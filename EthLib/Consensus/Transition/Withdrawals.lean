module

public import EthLib.Consensus.Credentials
public import EthLib.Consensus.Transition.BuilderRequests

/-!
# `Consensus.Transition.Withdrawals`

From Capella: the withdrawals of a block, and the change of BLS credentials to an address.

Each block pays balances out to the addresses that the credentials of validators name.

A sweep visits a bounded number of validators per block, from where the block before stopped.

A withdrawable validator gets its whole balance.

A validator at its largest effective balance gets the part above it.

From Electra, the queued partial withdrawals come first.

From Electra too, the largest effective balance depends on the credentials.

Before Gloas, the payload of the block must carry exactly the withdrawals that the state expects.

From Gloas the block carries no payload.

The state then records the withdrawals that the next payload must carry.

From Gloas too, the builders withdraw: their queued payments first, then a sweep of builders.

A block whose parent has no payload withdraws nothing.

A validator with BLS credentials may change them once to an address, signed by its BLS key.

[EIP-4895] adds the withdrawals to the payload, and [EIP-7251] the queue and the larger balances.

[EIP-7732] adds the withdrawals of builders.

[EIP-4895]: https://eips.ethereum.org/EIPS/eip-4895#new-field-in-the-execution-payload-withdrawals
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-! ## Withdrawable validators -/

/-- From Capella: whether the credentials of a validator name an address, for its withdrawals.

Before Electra only the execution address prefix names one. -/
def hasWithdrawalAddress (fork : Base.Fork) (validator : Validator) : Bool :=
  -- From Electra the prefix `0x01` or `0x02`, before it `0x01` only.
  if .pectra ≤ fork then hasExecutionWithdrawalCredential validator
  else hasEth1WithdrawalCredential validator

/-- From Capella: whether a validator may withdraw its whole balance at an epoch. -/
def isFullyWithdrawableValidator (fork : Base.Fork) (validator : Validator) (balance : Gwei)
    (epoch : Epoch) : Bool :=
  -- Its credentials name an address, it is withdrawable at the epoch, and its balance is positive.
  hasWithdrawalAddress fork validator && validator.withdrawableEpoch ≤ epoch && 0 < balance

/-- From Capella: whether a validator may withdraw the excess of its balance.

The excess is the part above its largest effective balance. -/
def isPartiallyWithdrawableValidator (preset : Preset) (fork : Base.Fork) (validator : Validator)
    (balance : Gwei) : Bool :=
  let largest := withdrawalMaxEffectiveBalance preset fork validator
  -- Its credentials name an address and its effective balance is the largest one, `m`.
  --
  -- Its balance exceeds `m`.
  hasWithdrawalAddress fork validator && validator.effectiveBalance == largest && largest < balance

/-- From Electra: whether a validator may take a queued partial withdrawal. -/
def isEligibleForPartialWithdrawals (preset : Preset) (validator : Validator) (balance : Gwei) :
    Bool :=
  -- It is not exiting, and its effective balance is at least `MIN_ACTIVATION_BALANCE`.
  --
  -- Its balance is above `MIN_ACTIVATION_BALANCE`.
  validator.exitEpoch == FAR_FUTURE_EPOCH &&
    preset.MIN_ACTIVATION_BALANCE ≤ validator.effectiveBalance &&
    preset.MIN_ACTIVATION_BALANCE < balance

/-- The balance of a validator less what some withdrawals already take from it.

A sum of 2^64 or more is an error, and so is a sum above the balance. -/
def getBalanceAfterWithdrawals (state : BeaconState preset fork) (index : ValidatorIndex)
    (withdrawals : Array Withdrawal) : Except AccessorError Gwei := do
  -- The balance less the sum of the amounts of the withdrawals of the validator.
  let balance ← getBalance state index
  let withdrawn ← withdrawals.foldlM (init := 0) fun sum withdrawal =>
    if withdrawal.validatorIndex = index then liftArith (addChecked sum withdrawal.amount)
    else pure sum
  liftArith (subChecked balance withdrawn)

/-! ## Expected withdrawals -/

/-- From Capella: the withdrawals that a state expects of the next payload.

It also counts the entries that each part of the computation read, each count a 64-bit integer.
-/
structure ExpectedWithdrawals where
  /-- The withdrawals, in their order. -/
  withdrawals : Array Withdrawal
  /-- From Gloas: the queued builder withdrawals that were read; zero before. -/
  processedBuilderWithdrawalsCount : UInt64
  /-- From Electra: the queued partial withdrawals that were read, paid or not. -/
  processedPartialWithdrawalsCount : UInt64
  /-- From Gloas: the builders that the sweep of builders visited; zero before. -/
  processedBuildersSweepCount : UInt64
  /-- The validators that the sweep visited. -/
  processedSweepWithdrawalsCount : UInt64
  deriving Repr

/-- The withdrawals with one more at their end, at the next withdrawal index, which then grows.

An index of 2^64 is an error. -/
def appendWithdrawal (withdrawals : Array Withdrawal) (withdrawalIndex : WithdrawalIndex)
    (index : ValidatorIndex) (address : ExecutionAddress) (amount : Gwei) :
    Except AccessorError (Array Withdrawal × WithdrawalIndex) := do
  -- The withdrawal takes the next withdrawal index `w`, which becomes `w + 1`.
  let next ← liftArith (addChecked withdrawalIndex 1)
  return (withdrawals.push ⟨withdrawalIndex, index, address, amount⟩, next)

/-- From Gloas: the queued builder withdrawals that the next payload pays, in their order.

The prior withdrawals must leave at least one place in the payload.

The result is the withdrawals, the next withdrawal index and the number of queued ones read. -/
def getBuilderWithdrawals (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  -- The limit is `MAX_WITHDRAWALS_PER_PAYLOAD - 1`, and the prior withdrawals stay within it.
  let limit ← liftAccessor (liftArith (subChecked preset.MAX_WITHDRAWALS_PER_PAYLOAD 1))
  ensure (prior.size ≤ limit.toNat) (.priorWithdrawalsAtLimit prior.size limit.toNat)
  let rec loop (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (withdrawalIndex : WithdrawalIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match queue with
    | [] => return (withdrawals, withdrawalIndex, processed)
    | pending :: rest =>
      -- The reading stops once the withdrawals reach the limit.
      if limit.toNat ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        -- Each pays its amount to its address, under the index that names its builder.
        let (withdrawals, withdrawalIndex) ← liftAccessor (appendWithdrawal withdrawals
          withdrawalIndex (convertBuilderIndexToValidatorIndex pending.builderIndex)
          pending.feeRecipient pending.amount)
        loop rest withdrawals withdrawalIndex (processed + 1)
  loop (state.builderPendingWithdrawals gloas).data.toList #[] withdrawalIndex 0

/-- From Gloas: the balance of a builder less what some withdrawals already take from it.

The result is zero when they take more.

A sum of 2^64 or more is an error. -/
def getBuilderBalanceAfterWithdrawals (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (index : BuilderIndex) (withdrawals : Array Withdrawal) :
    Except AccessorError Gwei := do
  -- The withdrawals of the builder carry the index that names it.
  let named := convertBuilderIndexToValidatorIndex index
  let withdrawn ← withdrawals.foldlM (init := 0) fun sum withdrawal =>
    if withdrawal.validatorIndex = named then liftArith (addChecked sum withdrawal.amount)
    else pure sum
  -- The balance less their sum, but not below 0.
  return saturatingSub (← getBuilder state gloas index).balance withdrawn

/-- From Gloas: the withdrawals of the sweep of builders, from the next builder of the state.

The prior withdrawals must leave at least one place in the payload.

The result is the withdrawals, the next withdrawal index and the number of builders visited. -/
def getBuildersSweepWithdrawals (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let epoch := getCurrentEpoch state
  let count := (state.builders gloas).data.size
  -- The limit is `MAX_WITHDRAWALS_PER_PAYLOAD - 1`, and the prior withdrawals stay within it.
  let limit ← liftAccessor (liftArith (subChecked preset.MAX_WITHDRAWALS_PER_PAYLOAD 1))
  ensure (prior.size ≤ limit.toNat) (.priorWithdrawalsAtLimit prior.size limit.toNat)
  let rec loop (visits : Nat) (withdrawals : Array Withdrawal) (withdrawalIndex : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match visits with
    | 0 => return (withdrawals, withdrawalIndex, processed)
    | visits + 1 =>
      -- The sweep stops once the withdrawals reach the limit.
      if limit.toNat ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        -- The balance left after the earlier withdrawals of the payload.
        let builder ← liftAccessor (getBuilder state gloas index)
        let balance ← liftAccessor
          (getBuilderBalanceAfterWithdrawals state gloas index (prior ++ withdrawals))
        -- A withdrawable builder with a positive balance left withdraws it to its address.
        let (withdrawals, withdrawalIndex) ←
          if builder.withdrawableEpoch ≤ epoch ∧ 0 < balance then
            liftAccessor (appendWithdrawal withdrawals withdrawalIndex
              (convertBuilderIndexToValidatorIndex index) builder.executionAddress balance)
          else pure (withdrawals, withdrawalIndex)
        -- The current builder is `i`, and the next is `(i + 1) mod n`, for `n` builders.
        let next ← liftAccessor (liftArith (addChecked index 1))
        loop visits withdrawals withdrawalIndex (next.toNat % count).toUInt64 (processed + 1)
  -- At most `min(n, MAX_BUILDERS_PER_WITHDRAWALS_SWEEP)` visits, from the next builder.
  loop (min count preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP.toNat) #[] withdrawalIndex
    (state.nextWithdrawalBuilderIndex gloas) 0

/-- From Electra: the queued partial withdrawals that the next payload pays, read in their order.

The prior withdrawals must stay within the limit, which leaves at least one place in the payload.

The result is the withdrawals, the next withdrawal index and the number of queued ones read. -/
def getPendingPartialWithdrawals (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let epoch := getCurrentEpoch state
  -- The limit is the prior count plus `MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP`.
  --
  -- It is at most `MAX_WITHDRAWALS_PER_PAYLOAD - 1`, and the prior withdrawals stay within it.
  let room ← liftAccessor (liftArith (subChecked preset.MAX_WITHDRAWALS_PER_PAYLOAD 1))
  let limit :=
    min (prior.size + preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat) room.toNat
  ensure (prior.size ≤ limit) (.priorWithdrawalsAtLimit prior.size limit)
  let rec loop (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (withdrawalIndex : WithdrawalIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match queue with
    | [] => return (withdrawals, withdrawalIndex, processed)
    | pending :: rest =>
      -- The reading stops at a withdrawal not yet withdrawable, or once at the limit.
      if epoch < pending.withdrawableEpoch ∨ limit ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        -- The balance `b` left after the earlier withdrawals of the payload.
        let index := pending.validatorIndex
        let validator ← liftAccessor (getValidator state index)
        let balance ←
          liftAccessor (getBalanceAfterWithdrawals state index (prior ++ withdrawals))
        -- An eligible validator withdraws `min(b - MIN_ACTIVATION_BALANCE, a)`, for the amount `a`.
        if isEligibleForPartialWithdrawals preset validator balance then
          let amount := min (balance - preset.MIN_ACTIVATION_BALANCE) pending.amount
          let (withdrawals, withdrawalIndex) ← liftAccessor (appendWithdrawal withdrawals
            withdrawalIndex index (credentialAddress validator.withdrawalCredentials) amount)
          loop rest withdrawals withdrawalIndex (processed + 1)
        -- Any other is read and dropped, with no withdrawal.
        else loop rest withdrawals withdrawalIndex (processed + 1)
  loop (state.pendingPartialWithdrawals electra).data.toList #[] withdrawalIndex 0

/-- From Capella: the withdrawals of the sweep, from the next validator of the state.

The prior withdrawals must leave a place.

The result is the withdrawals, the next withdrawal index and the number of validators visited. -/
def getValidatorsSweepWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let epoch := getCurrentEpoch state
  let count := state.validators.data.size
  -- The limit is `MAX_WITHDRAWALS_PER_PAYLOAD`, and the prior withdrawals leave a place.
  let limit := preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat
  ensure (prior.size < limit) (.priorWithdrawalsAtLimit prior.size limit)
  let rec loop (visits : Nat) (withdrawals : Array Withdrawal) (withdrawalIndex : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match visits with
    | 0 => return (withdrawals, withdrawalIndex, processed)
    | visits + 1 =>
      -- The sweep stops once the withdrawals reach the limit.
      if limit ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        -- The balance `b` left after the earlier withdrawals of the payload.
        let validator ← liftAccessor (getValidator state index)
        let balance ←
          liftAccessor (getBalanceAfterWithdrawals state index (prior ++ withdrawals))
        -- The address in the last 20 bytes of the credentials.
        let address := credentialAddress validator.withdrawalCredentials
        -- A fully withdrawable validator withdraws `b`.
        let (withdrawals, withdrawalIndex) ←
          if isFullyWithdrawableValidator fork validator balance epoch then
            liftAccessor (appendWithdrawal withdrawals withdrawalIndex index address balance)
          -- A partially withdrawable one withdraws `b - m`, for its largest effective balance `m`.
          else if isPartiallyWithdrawableValidator preset fork validator balance then
            liftAccessor (appendWithdrawal withdrawals withdrawalIndex index address
              (balance - withdrawalMaxEffectiveBalance preset fork validator))
          else pure (withdrawals, withdrawalIndex)
        -- The current validator is `i`, and the next is `(i + 1) mod n`, for `n` validators.
        let next ← liftAccessor (liftArith (addChecked index 1))
        loop visits withdrawals withdrawalIndex (next.toNat % count).toUInt64 (processed + 1)
  -- At most `min(n, MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)` visits, from the next validator.
  loop (min count preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP.toNat) #[] withdrawalIndex
    (state.nextWithdrawalValidatorIndex capella) 0

/-- From Capella: the withdrawals that the state expects of the next payload.

Each part continues the withdrawal indices of the part before it.

A part that a fork lacks reads nothing, with a count of 0.

A count of 2^64 or more is an error.
-/
def getExpectedWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork) :
    Except TransitionError ExpectedWithdrawals := do
  -- The withdrawal indices start at the next withdrawal index of the state.
  let start := state.nextWithdrawalIndex capella
  -- From Gloas the queued builder withdrawals come first, as EIP-7732 specifies.
  let (builders, withdrawalIndex, builderCount) ←
    (if gloas : .glamsterdam ≤ fork then getBuilderWithdrawals state gloas start #[]
    else pure (#[], start, 0))
  -- From Electra the queued partial withdrawals follow.
  let (partials, withdrawalIndex, partialCount) ←
    (if electra : .pectra ≤ fork then
      getPendingPartialWithdrawals state electra withdrawalIndex builders
    else pure (#[], withdrawalIndex, 0))
  -- The partial withdrawals follow the builder withdrawals.
  let prior := builders ++ partials
  -- From Gloas the sweep of builders follows.
  let (buildersSweep, withdrawalIndex, buildersSweepCount) ←
    (if gloas : .glamsterdam ≤ fork then
      getBuildersSweepWithdrawals state gloas withdrawalIndex prior
    else pure (#[], withdrawalIndex, 0))
  -- The withdrawals of the sweep of builders follow.
  let prior := prior ++ buildersSweep
  -- The sweep of validators always comes last.
  let (sweep, _, sweepCount) ←
    getValidatorsSweepWithdrawals state capella withdrawalIndex prior
  -- The parts count in naturals, and each count fails here if it reaches `2^64`.
  let builderCount ← liftAccessor (liftArith (Uint64.ofNatChecked builderCount))
  let partialCount ← liftAccessor (liftArith (Uint64.ofNatChecked partialCount))
  let buildersSweepCount ← liftAccessor (liftArith (Uint64.ofNatChecked buildersSweepCount))
  let sweepCount ← liftAccessor (liftArith (Uint64.ofNatChecked sweepCount))
  return ⟨prior ++ sweep, builderCount, partialCount, buildersSweepCount, sweepCount⟩

/-! ## Processing the withdrawals -/

/-- The state with the balance that a withdrawal names lowered by its amount, to at least zero.

From Gloas an index with the builder flag names the balance of a builder. -/
def applyWithdrawal (state : BeaconState preset fork) (withdrawal : Withdrawal) :
    Except AccessorError (BeaconState preset fork) :=
  -- From Gloas an index with the builder flag lowers the balance of its builder, but not below 0.
  if gloas : .glamsterdam ≤ fork ∧ isBuilderIndex withdrawal.validatorIndex = true then do
    let index := convertValidatorIndexToBuilderIndex withdrawal.validatorIndex
    let builder ← getBuilder state gloas.1 index
    state.setBuilder gloas.1 index
      { builder with balance := saturatingSub builder.balance withdrawal.amount }
  -- Any other lowers the balance of its validator, but not below 0.
  else decreaseBalance state withdrawal.validatorIndex withdrawal.amount

/-- The state with the balances lowered by the withdrawals, each to at least zero. -/
def applyWithdrawals (state : BeaconState preset fork) (withdrawals : Array Withdrawal) :
    Except AccessorError (BeaconState preset fork) :=
  withdrawals.foldlM applyWithdrawal state

/-- The state whose next withdrawal index follows the last withdrawal, if there is one.

An index of 2^64 is an error. -/
def updateNextWithdrawalIndex (state : BeaconState preset fork) (withdrawals : Array Withdrawal) :
    Except AccessorError (BeaconState preset fork) :=
  -- With a last withdrawal of index `w`, the next withdrawal index is `w + 1`.
  match withdrawals.back? with
  | some last => do
    let next ← liftArith (addChecked last.index 1)
    return { state with nextWithdrawalIndex := fun _ => next }
  | none => return state

/-- The index from which the next sweep starts, before it wraps around the registry.

A sum of 2^64 or more is an error. -/
def nextSweepStart (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (withdrawals : Array Withdrawal) : Except AccessorError ValidatorIndex :=
  match withdrawals.back? with
  | some last =>
    -- With `MAX_WITHDRAWALS_PER_PAYLOAD` withdrawals, the validator after that of the last one.
    if withdrawals.size = preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat then
      liftArith (addChecked last.validatorIndex 1)
    -- Else the start of this sweep plus `MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP`.
    else liftArith (addChecked (state.nextWithdrawalValidatorIndex capella)
      preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)
  | none => liftArith (addChecked (state.nextWithdrawalValidatorIndex capella)
      preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)

/-- The state whose next sweep starts where this one ends, wrapped around the registry.

An empty registry is an error. -/
def updateNextWithdrawalValidatorIndex (state : BeaconState preset fork)
    (capella : .shapella ≤ fork) (withdrawals : Array Withdrawal) :
    Except AccessorError (BeaconState preset fork) := do
  -- The start of the next sweep, modulo the number of validators.
  let next ← nextSweepStart state capella withdrawals
  let count := state.validators.data.size
  if count = 0 then throw (.arith .divisionByZero)
  return { state with nextWithdrawalValidatorIndex := fun _ => (next.toNat % count).toUInt64 }

/-- From Electra: the state without the queued partial withdrawals that were read. -/
def updatePendingPartialWithdrawals (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (count : UInt64) : BeaconState preset fork :=
  let queue := state.pendingPartialWithdrawals electra
  -- The queue without its first `count` entries, those that were read.
  let rest : PendingPartialWithdrawals preset fork :=
    ⟨queue.data.extract count.toNat queue.data.size, fun before => by
      have := queue.bound before
      simp only [Array.size_extract]
      omega⟩
  { state with pendingPartialWithdrawals := fun _ => rest }

/-- From Gloas: the state that records the withdrawals that the next payload must carry. -/
def updatePayloadExpectedWithdrawals (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (withdrawals : Array Withdrawal) : BeaconState preset fork :=
  -- The next payload must carry exactly these withdrawals, as EIP-7732 specifies.
  { state with
    payloadExpectedWithdrawals := fun _ =>
      ⟨withdrawals, fun before => absurd gloas (Nat.not_le_of_lt before)⟩ }

/-- From Gloas: the state without the queued builder withdrawals that were read. -/
def updateBuilderPendingWithdrawals (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (count : UInt64) : BeaconState preset fork :=
  let queue := (state.builderPendingWithdrawals gloas).data
  -- The queue without its first `count` entries, those that were read.
  let rest : BuilderPendingWithdrawals := ⟨queue.extract count.toNat queue.size⟩
  { state with builderPendingWithdrawals := fun _ => rest }

/-- From Gloas: the state whose next sweep of builders starts after the builders visited.

The index wraps around the registry, and stays when the registry is empty.

A sum of 2^64 or more is an error. -/
def updateNextWithdrawalBuilderIndex (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (count : UInt64) :
    Except AccessorError (BeaconState preset fork) := do
  let size := (state.builders gloas).data.size
  -- An empty registry of builders leaves the state as it is.
  if size = 0 then return state
  -- The next index grows by the number of builders visited; a sum of `2^64` or more is an error.
  let next ← liftArith (addChecked (state.nextWithdrawalBuilderIndex gloas) count)
  -- That sum modulo the number of builders becomes the next index.
  return { state with nextWithdrawalBuilderIndex := fun _ => (next.toNat % size).toUInt64 }

/-- From Gloas: whether the parent of the next block has its payload.

The latest payload then has the block hash of the latest bid. -/
def isParentBlockFull (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) : Bool :=
  -- The latest block hash is the block hash of the latest bid.
  state.latestBlockHash gloas == (state.latestExecutionPayloadBid gloas).blockHash

/-- The state after the withdrawals that the state expects, once they are known. -/
def applyExpectedWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (expected : ExpectedWithdrawals) : Except AccessorError (BeaconState preset fork) := do
  -- Each withdrawal lowers the balance of its validator, or from Gloas of its builder.
  let state ← applyWithdrawals state expected.withdrawals
  -- The next withdrawal index moves on.
  let state ← updateNextWithdrawalIndex state expected.withdrawals
  -- From Gloas the state records the withdrawals for the next payload.
  --
  -- The queued builder withdrawals that were read then leave the queue.
  let state := if gloas : .glamsterdam ≤ fork then
      updateBuilderPendingWithdrawals
        (updatePayloadExpectedWithdrawals state gloas expected.withdrawals) gloas
        expected.processedBuilderWithdrawalsCount
    else state
  -- From Electra, so do the queued partial withdrawals that were read.
  let state := if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals state electra expected.processedPartialWithdrawalsCount
    else state
  -- From Gloas the sweep of builders moves on.
  let state ← (if gloas : .glamsterdam ≤ fork then
      updateNextWithdrawalBuilderIndex state gloas expected.processedBuildersSweepCount
    else pure state)
  -- The sweep of validators moves on last.
  updateNextWithdrawalValidatorIndex state capella expected.withdrawals

/-- From Capella: the state after the withdrawals that the state expects.

From Gloas the block carries no payload, as [EIP-7732] specifies.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#state-transition
-/
def processWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (payload : Until .glamsterdam fork (ExecutionPayload preset fork)) :
    Except TransitionError (BeaconState preset fork) :=
  -- From Gloas a block whose parent has no payload changes nothing, as EIP-7732 specifies.
  if gloas : .glamsterdam ≤ fork then
    if isParentBlockFull state gloas then do
      let expected ← getExpectedWithdrawals state capella
      liftAccessor (applyExpectedWithdrawals state capella expected)
    else pure state
  else do
    -- Before Gloas the payload carries exactly the withdrawals that the state expects.
    let expected ← getExpectedWithdrawals state capella
    let carried := ((payload (Nat.lt_of_not_le gloas)).withdrawals capella).data
    ensure (carried = expected.withdrawals)
      (.wrongWithdrawals (firstDifference carried expected.withdrawals) carried.size
        expected.withdrawals.size)
    liftAccessor (applyExpectedWithdrawals state capella expected)

/-! ## Changes of BLS credentials -/

/-- From Capella: the credentials that name an address.

They hold the execution address prefix, 11 zero bytes and the address. -/
def executionCredentials (address : ExecutionAddress) : Bytes32 :=
  -- Byte 0 is `0x01`, bytes 1 to 11 are 0, and bytes 12 to 31 are the address.
  Vector.ofFn fun i =>
    if i.val = 0 then ETH1_ADDRESS_WITHDRAWAL_PREFIX[0]
    else if 12 ≤ i.val then address[i.val - 12]
    else 0

/-- From Capella: the state after a change of BLS credentials to an address. -/
def processBlsToExecutionChange (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBLSToExecutionChange) :
    Except TransitionError (BeaconState preset fork) := do
  let change := signed.message
  let index := change.validatorIndex
  -- The validator exists and has BLS credentials, with the prefix `0x00`.
  let validator ← liftAccessor (getValidator state index)
  let credentials := validator.withdrawalCredentials
  ensure (credentials[0] = BLS_WITHDRAWAL_PREFIX[0]) (.notBlsCredentials index)
  -- Bytes 1 to 31 of the credentials are those of the SHA-256 hash of the key of the change.
  let keyHash := Cryptography.Hash.Sha256.hash32 ⟨change.fromBlsPubkey.toArray⟩
  ensure (∀ i : Fin 31, credentials[i.val + 1] = keyHash[i.val + 1]) (.wrongBlsKey index)
  -- That key signs the change, under the genesis fork version and the genesis validators root.
  let domain ← liftSsz (computeDomain config DOMAIN_BLS_TO_EXECUTION_CHANGE
    (genesisValidatorsRoot := state.genesisValidatorsRoot))
  let signingRoot ← liftSsz (computeSigningRoot change domain)
  ensure (checks.verify change.fromBlsPubkey (packBytes signingRoot) signed.signature = true)
    (.invalidBlsChangeSignature index signingRoot)
  -- The validator gets the credentials that name the address of the change.
  liftAccessor (state.setValidator index
    { validator with withdrawalCredentials := executionCredentials change.toExecutionAddress })

end EthLib.Consensus

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
  if .pectra ≤ fork then hasExecutionWithdrawalCredential validator
  else hasEth1WithdrawalCredential validator

/-- From Capella: whether a validator may withdraw its whole balance at an epoch.

Its credentials must name an address, it must be withdrawable, and its balance must not be zero. -/
def isFullyWithdrawableValidator (fork : Base.Fork) (validator : Validator) (balance : Gwei)
    (epoch : Epoch) : Bool :=
  hasWithdrawalAddress fork validator && validator.withdrawableEpoch ≤ epoch && 0 < balance

/-- From Capella: whether a validator may withdraw the excess of its balance.

The excess is the part above its largest effective balance.

Its credentials must name an address, and its effective balance must be that largest one. -/
def isPartiallyWithdrawableValidator (preset : Preset) (fork : Base.Fork) (validator : Validator)
    (balance : Gwei) : Bool :=
  let largest := withdrawalMaxEffectiveBalance preset fork validator
  hasWithdrawalAddress fork validator && validator.effectiveBalance == largest && largest < balance

/-- From Electra: whether a validator may take a queued partial withdrawal.

It must not be exiting.

Its effective balance must be at least the activation balance.

Its balance must be above the activation balance. -/
def isEligibleForPartialWithdrawals (preset : Preset) (validator : Validator) (balance : Gwei) :
    Bool :=
  validator.exitEpoch == FAR_FUTURE_EPOCH &&
    preset.MIN_ACTIVATION_BALANCE ≤ validator.effectiveBalance &&
    preset.MIN_ACTIVATION_BALANCE < balance

/-- The balance of a validator less what some withdrawals already take from it.

A sum of 2^64 or more is an error, and so is a sum above the balance. -/
def getBalanceAfterWithdrawals (state : BeaconState preset fork) (index : ValidatorIndex)
    (withdrawals : Array Withdrawal) : Except AccessorError Gwei := do
  let balance ← getBalance state index
  let withdrawn ← withdrawals.foldlM (init := 0) fun sum withdrawal =>
    if withdrawal.validatorIndex = index then liftArith (addChecked sum withdrawal.amount)
    else pure sum
  liftArith (subChecked balance withdrawn)

/-! ## Expected withdrawals -/

/-- From Capella: the withdrawals that a state expects of the next payload.

It also counts the entries that each part of the computation read. -/
structure ExpectedWithdrawals where
  /-- The withdrawals, in their order. -/
  withdrawals : Array Withdrawal
  /-- From Gloas: the queued builder withdrawals that were read; zero before. -/
  processedBuilderWithdrawalsCount : Nat
  /-- From Electra: the queued partial withdrawals that were read, paid or not. -/
  processedPartialWithdrawalsCount : Nat
  /-- From Gloas: the builders that the sweep of builders visited; zero before. -/
  processedBuildersSweepCount : Nat
  /-- The validators that the sweep visited. -/
  processedSweepWithdrawalsCount : Nat
  deriving Repr

/-- The withdrawals with one more at their end, at the next withdrawal index, which then grows.

An index of 2^64 is an error. -/
def appendWithdrawal (withdrawals : Array Withdrawal) (withdrawalIndex : WithdrawalIndex)
    (index : ValidatorIndex) (address : ExecutionAddress) (amount : Gwei) :
    Except AccessorError (Array Withdrawal × WithdrawalIndex) := do
  let next ← liftArith (addChecked withdrawalIndex 1)
  return (withdrawals.push ⟨withdrawalIndex, index, address, amount⟩, next)

/-- From Gloas: the queued builder withdrawals that the next payload pays, in their order.

Each pays its amount to its address, under the index that names its builder.

The reading stops when the withdrawals leave only one place in the payload.

The prior withdrawals must leave that place.

The result is the withdrawals, the next withdrawal index and the number of queued ones read. -/
def getBuilderWithdrawals (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let limit ← liftAccessor (liftArith (subChecked preset.MAX_WITHDRAWALS_PER_PAYLOAD 1))
  ensure (prior.size ≤ limit.toNat) (.priorWithdrawalsAtLimit prior.size limit.toNat)
  let rec loop (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (withdrawalIndex : WithdrawalIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match queue with
    | [] => return (withdrawals, withdrawalIndex, processed)
    | pending :: rest =>
      if limit.toNat ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
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
  let named := convertBuilderIndexToValidatorIndex index
  let withdrawn ← withdrawals.foldlM (init := 0) fun sum withdrawal =>
    if withdrawal.validatorIndex = named then liftArith (addChecked sum withdrawal.amount)
    else pure sum
  return saturatingSub (← getBuilder state gloas index).balance withdrawn

/-- From Gloas: the withdrawals of the sweep of builders, from the next builder of the state.

The sweep visits at most the most builders per sweep, and at most the whole registry once.

It stops when the withdrawals leave only one place in the payload.

The prior withdrawals must leave that place.

A withdrawable builder with a balance left gives that balance to its address.

The balance is the one left after the earlier withdrawals of the payload.

The result is the withdrawals, the next withdrawal index and the number of builders visited. -/
def getBuildersSweepWithdrawals (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let epoch := getCurrentEpoch state
  let count := (state.builders gloas).data.size
  let limit ← liftAccessor (liftArith (subChecked preset.MAX_WITHDRAWALS_PER_PAYLOAD 1))
  ensure (prior.size ≤ limit.toNat) (.priorWithdrawalsAtLimit prior.size limit.toNat)
  let rec loop (visits : Nat) (withdrawals : Array Withdrawal) (withdrawalIndex : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match visits with
    | 0 => return (withdrawals, withdrawalIndex, processed)
    | visits + 1 =>
      if limit.toNat ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        let builder ← liftAccessor (getBuilder state gloas index)
        let balance ← liftAccessor
          (getBuilderBalanceAfterWithdrawals state gloas index (prior ++ withdrawals))
        let (withdrawals, withdrawalIndex) ←
          if builder.withdrawableEpoch ≤ epoch ∧ 0 < balance then
            liftAccessor (appendWithdrawal withdrawals withdrawalIndex
              (convertBuilderIndexToValidatorIndex index) builder.executionAddress balance)
          else pure (withdrawals, withdrawalIndex)
        let next ← liftAccessor (liftArith (addChecked index 1))
        loop visits withdrawals withdrawalIndex (next.toNat % count).toUInt64 (processed + 1)
  loop (min count preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP.toNat) #[] withdrawalIndex
    (state.nextWithdrawalBuilderIndex gloas) 0

/-- From Electra: the queued partial withdrawals that the next payload pays, read in their order.

The reading stops at the first one that is not yet withdrawable.

It also stops when the withdrawals reach their limit.

That limit is the prior withdrawals plus the most queued ones per sweep.

It also leaves at least one place in the payload.

A queued withdrawal is paid only if its validator is still eligible.

It then pays at most the balance above the activation balance.

The result is the withdrawals, the next withdrawal index and the number of queued ones read. -/
def getPendingPartialWithdrawals (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let epoch := getCurrentEpoch state
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
      if epoch < pending.withdrawableEpoch ∨ limit ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        let index := pending.validatorIndex
        let validator ← liftAccessor (getValidator state index)
        let balance ←
          liftAccessor (getBalanceAfterWithdrawals state index (prior ++ withdrawals))
        if isEligibleForPartialWithdrawals preset validator balance then
          let amount := min (balance - preset.MIN_ACTIVATION_BALANCE) pending.amount
          let (withdrawals, withdrawalIndex) ← liftAccessor (appendWithdrawal withdrawals
            withdrawalIndex index (credentialAddress validator.withdrawalCredentials) amount)
          loop rest withdrawals withdrawalIndex (processed + 1)
        else loop rest withdrawals withdrawalIndex (processed + 1)
  loop (state.pendingPartialWithdrawals electra).data.toList #[] withdrawalIndex 0

/-- From Capella: the withdrawals of the sweep, from the next validator of the state.

The sweep visits at most the most validators per sweep, and at most the whole registry once.

It stops when the withdrawals reach the most per payload.

The prior withdrawals must leave a place.

A fully withdrawable validator gives its balance.

A partially withdrawable one gives the part above its largest effective balance.

The balance is the one left after the earlier withdrawals of the payload.

The result is the withdrawals, the next withdrawal index and the number of validators visited. -/
def getValidatorsSweepWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (withdrawalIndex : WithdrawalIndex) (prior : Array Withdrawal) :
    Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) := do
  let epoch := getCurrentEpoch state
  let count := state.validators.data.size
  let limit := preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat
  ensure (prior.size < limit) (.priorWithdrawalsAtLimit prior.size limit)
  let rec loop (visits : Nat) (withdrawals : Array Withdrawal) (withdrawalIndex : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat) :
      Except TransitionError (Array Withdrawal × WithdrawalIndex × Nat) :=
    match visits with
    | 0 => return (withdrawals, withdrawalIndex, processed)
    | visits + 1 =>
      if limit ≤ prior.size + withdrawals.size then
        return (withdrawals, withdrawalIndex, processed)
      else do
        let validator ← liftAccessor (getValidator state index)
        let balance ←
          liftAccessor (getBalanceAfterWithdrawals state index (prior ++ withdrawals))
        let address := credentialAddress validator.withdrawalCredentials
        let (withdrawals, withdrawalIndex) ←
          if isFullyWithdrawableValidator fork validator balance epoch then
            liftAccessor (appendWithdrawal withdrawals withdrawalIndex index address balance)
          else if isPartiallyWithdrawableValidator preset fork validator balance then
            liftAccessor (appendWithdrawal withdrawals withdrawalIndex index address
              (balance - withdrawalMaxEffectiveBalance preset fork validator))
          else pure (withdrawals, withdrawalIndex)
        let next ← liftAccessor (liftArith (addChecked index 1))
        loop visits withdrawals withdrawalIndex (next.toNat % count).toUInt64 (processed + 1)
  loop (min count preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP.toNat) #[] withdrawalIndex
    (state.nextWithdrawalValidatorIndex capella) 0

/-- From Capella: the withdrawals that the state expects of the next payload.

From Gloas the queued builder withdrawals come first.

From Electra the queued partial withdrawals follow.

From Gloas the sweep of builders follows, and the sweep of validators always comes last.

Each part continues the withdrawal indices of the part before it. -/
def getExpectedWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork) :
    Except TransitionError ExpectedWithdrawals := do
  let start := state.nextWithdrawalIndex capella
  let (builders, withdrawalIndex, builderCount) ←
    (if gloas : .glamsterdam ≤ fork then getBuilderWithdrawals state gloas start #[]
    else pure (#[], start, 0))
  let (partials, withdrawalIndex, partialCount) ←
    (if electra : .pectra ≤ fork then
      getPendingPartialWithdrawals state electra withdrawalIndex builders
    else pure (#[], withdrawalIndex, 0))
  let prior := builders ++ partials
  let (buildersSweep, withdrawalIndex, buildersSweepCount) ←
    (if gloas : .glamsterdam ≤ fork then
      getBuildersSweepWithdrawals state gloas withdrawalIndex prior
    else pure (#[], withdrawalIndex, 0))
  let prior := prior ++ buildersSweep
  let (sweep, _, sweepCount) ←
    getValidatorsSweepWithdrawals state capella withdrawalIndex prior
  return ⟨prior ++ sweep, builderCount, partialCount, buildersSweepCount, sweepCount⟩

/-! ## Processing the withdrawals -/

/-- The state with the balance that a withdrawal names lowered by its amount, to at least zero.

From Gloas an index with the builder flag names the balance of a builder. -/
def applyWithdrawal (state : BeaconState preset fork) (withdrawal : Withdrawal) :
    Except AccessorError (BeaconState preset fork) :=
  if gloas : .glamsterdam ≤ fork ∧ isBuilderIndex withdrawal.validatorIndex = true then do
    let index := convertValidatorIndexToBuilderIndex withdrawal.validatorIndex
    let builder ← getBuilder state gloas.1 index
    return state.setBuilder index.toNat
      { builder with balance := saturatingSub builder.balance withdrawal.amount }
  else decreaseBalance state withdrawal.validatorIndex withdrawal.amount

/-- The state with the balances lowered by the withdrawals, each to at least zero. -/
def applyWithdrawals (state : BeaconState preset fork) (withdrawals : Array Withdrawal) :
    Except AccessorError (BeaconState preset fork) :=
  withdrawals.foldlM applyWithdrawal state

/-- The state whose next withdrawal index follows the last withdrawal, if there is one.

An index of 2^64 is an error. -/
def updateNextWithdrawalIndex (state : BeaconState preset fork) (withdrawals : Array Withdrawal) :
    Except AccessorError (BeaconState preset fork) :=
  match withdrawals.back? with
  | some last => do
    let next ← liftArith (addChecked last.index 1)
    return { state with nextWithdrawalIndex := fun _ => next }
  | none => return state

/-- The index from which the next sweep starts, before it wraps around the registry.

With the most withdrawals per payload, it is the validator after that of the last withdrawal.

Otherwise it is the start of this sweep plus the most validators per sweep.

A sum of 2^64 or more is an error. -/
def nextSweepStart (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (withdrawals : Array Withdrawal) : Except AccessorError ValidatorIndex :=
  match withdrawals.back? with
  | some last =>
    if withdrawals.size = preset.MAX_WITHDRAWALS_PER_PAYLOAD.toNat then
      liftArith (addChecked last.validatorIndex 1)
    else liftArith (addChecked (state.nextWithdrawalValidatorIndex capella)
      preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)
  | none => liftArith (addChecked (state.nextWithdrawalValidatorIndex capella)
      preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)

/-- The state whose next sweep starts where this one ends, wrapped around the registry.

An empty registry is an error. -/
def updateNextWithdrawalValidatorIndex (state : BeaconState preset fork)
    (capella : .shapella ≤ fork) (withdrawals : Array Withdrawal) :
    Except AccessorError (BeaconState preset fork) := do
  let next ← nextSweepStart state capella withdrawals
  let count := state.validators.data.size
  if count = 0 then throw (.arith .divisionByZero)
  return { state with nextWithdrawalValidatorIndex := fun _ => (next.toNat % count).toUInt64 }

/-- From Electra: the state without the queued partial withdrawals that were read. -/
def updatePendingPartialWithdrawals (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (count : Nat) : BeaconState preset fork :=
  let queue := state.pendingPartialWithdrawals electra
  { state with pendingPartialWithdrawals := fun _ =>
      ⟨queue.data.extract count queue.data.size, fun before => by
        have := queue.bound before
        simp only [Array.size_extract]
        omega⟩ }

/-- From Gloas: the state that records the withdrawals that the next payload must carry. -/
def updatePayloadExpectedWithdrawals (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (withdrawals : Array Withdrawal) : BeaconState preset fork :=
  { state with
    payloadExpectedWithdrawals := fun _ =>
      ⟨withdrawals, fun before => absurd gloas (Nat.not_le_of_lt before)⟩ }

/-- From Gloas: the state without the queued builder withdrawals that were read. -/
def updateBuilderPendingWithdrawals (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (count : Nat) : BeaconState preset fork :=
  let queue := (state.builderPendingWithdrawals gloas).data
  { state with builderPendingWithdrawals := fun _ => ⟨queue.extract count queue.size⟩ }

/-- From Gloas: the state whose next sweep of builders starts after the builders visited.

The index wraps around the registry, and stays when the registry is empty.

A sum of 2^64 or more is an error. -/
def updateNextWithdrawalBuilderIndex (state : BeaconState preset fork)
    (gloas : .glamsterdam ≤ fork) (count : Nat) :
    Except AccessorError (BeaconState preset fork) := do
  let size := (state.builders gloas).data.size
  if size = 0 then return state
  let next ← liftArith (addChecked (state.nextWithdrawalBuilderIndex gloas) count.toUInt64)
  return { state with nextWithdrawalBuilderIndex := fun _ => (next.toNat % size).toUInt64 }

/-- From Gloas: whether the parent of the next block has its payload.

The latest payload then has the block hash of the latest bid. -/
def isParentBlockFull (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) : Bool :=
  state.latestBlockHash gloas == (state.latestExecutionPayloadBid gloas).blockHash

/-- The state after the withdrawals that the state expects, once they are known.

Each withdrawal lowers the balance of its validator, or from Gloas of its builder.

The next withdrawal index and the start of the next sweep then move on.

From Gloas the state records the withdrawals for the next payload.

From Gloas too, the queued builder withdrawals that were read leave the queue.

From Electra, so do the queued partial withdrawals that were read.

From Gloas the sweep of builders moves on. -/
def applyExpectedWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (expected : ExpectedWithdrawals) : Except AccessorError (BeaconState preset fork) := do
  let state ← applyWithdrawals state expected.withdrawals
  let state ← updateNextWithdrawalIndex state expected.withdrawals
  let state := if gloas : .glamsterdam ≤ fork then
      updateBuilderPendingWithdrawals
        (updatePayloadExpectedWithdrawals state gloas expected.withdrawals) gloas
        expected.processedBuilderWithdrawalsCount
    else state
  let state := if electra : .pectra ≤ fork then
      updatePendingPartialWithdrawals state electra expected.processedPartialWithdrawalsCount
    else state
  let state ← (if gloas : .glamsterdam ≤ fork then
      updateNextWithdrawalBuilderIndex state gloas expected.processedBuildersSweepCount
    else pure state)
  updateNextWithdrawalValidatorIndex state capella expected.withdrawals

/-- From Capella: the state after the withdrawals that the state expects.

Before Gloas, the payload of the block must carry exactly those withdrawals.

From Gloas the block carries no payload.

A block whose parent has no payload then changes nothing. -/
def processWithdrawals (state : BeaconState preset fork) (capella : .shapella ≤ fork)
    (payload : Until .glamsterdam fork (ExecutionPayload preset fork)) :
    Except TransitionError (BeaconState preset fork) :=
  if gloas : .glamsterdam ≤ fork then
    if isParentBlockFull state gloas then do
      let expected ← getExpectedWithdrawals state capella
      liftAccessor (applyExpectedWithdrawals state capella expected)
    else pure state
  else do
    let expected ← getExpectedWithdrawals state capella
    ensure (((payload (Nat.lt_of_not_le gloas)).withdrawals capella).data = expected.withdrawals)
      .wrongWithdrawals
    liftAccessor (applyExpectedWithdrawals state capella expected)

/-! ## Changes of BLS credentials -/

/-- From Capella: the credentials that name an address.

They hold the execution address prefix, 11 zero bytes and the address. -/
def executionCredentials (address : ExecutionAddress) : Bytes32 :=
  Vector.ofFn fun i =>
    if i.val = 0 then ETH1_ADDRESS_WITHDRAWAL_PREFIX[0]
    else if 12 ≤ i.val then address[i.val - 12]
    else 0

/-- From Capella: the state after a change of BLS credentials to an address.

The validator must exist and have BLS credentials.

Bytes 1 to 31 of its credentials must be those of the SHA-256 hash of the key that the change names.

That key must sign the change, under the genesis fork version of the chain.

The validator then gets the credentials that name the address of the change. -/
def processBlsToExecutionChange (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (signed : SignedBLSToExecutionChange) :
    Except TransitionError (BeaconState preset fork) := do
  let change := signed.message
  let index := change.validatorIndex
  let validator ← liftAccessor (getValidator state index)
  let credentials := validator.withdrawalCredentials
  ensure (credentials[0] = BLS_WITHDRAWAL_PREFIX[0]) (.notBlsCredentials index)
  let keyHash := sha256Bytes32 ⟨change.fromBlsPubkey.toArray⟩
  ensure (∀ i : Fin 31, credentials[i.val + 1] = keyHash[i.val + 1]) (.wrongBlsKey index)
  let domain ← liftSsz (computeDomain config DOMAIN_BLS_TO_EXECUTION_CHANGE
    (genesisValidatorsRoot := state.genesisValidatorsRoot))
  let signingRoot ← liftSsz (computeSigningRoot change domain)
  ensure (checks.verify (packBytes change.fromBlsPubkey) (packBytes signingRoot)
    (packBytes signed.signature) = true) .invalidBlsChangeSignature
  return state.setValidator index.toNat
    { validator with withdrawalCredentials := executionCredentials change.toExecutionAddress }

end EthLib.Consensus

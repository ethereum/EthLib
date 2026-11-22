module

public import EthLib.Consensus.Churn

/-!
# `Consensus.Mutators`

Functions that change the balances and the validators of a beacon state.

A balance grows by a reward, and shrinks by a penalty down to zero at most.

A validator that exits joins the exit queue, which lets a limited number leave each epoch.

Before Electra the exit queue counts validators, and from Electra it counts balance.

From Electra, a validator that switches to compounding credentials keeps the activation balance.

The rest of its balance joins the queue of pending deposits.

A slashed validator exits, loses part of its balance, and pays a reward to whoever reported it.

A read past the end of a list, a full list, or a 64-bit overflow is an error.

From Gloas, a slashing also cancels the pending builder payments of some blocks.

Those are the blocks that the slashed validator proposed.

[EIP-7732] adds the builder payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The state with the balance at an index of the balances replaced. -/
def BeaconState.putBalance (state : BeaconState preset fork) (index : Nat)
    (inside : index < state.balances.data.size) (balance : Gwei) : BeaconState preset fork :=
  { state with balances := ⟨state.balances.data.set index balance inside, by
      simpa using state.balances.bound⟩ }

/-- The state with the balance of a validator replaced.

An index past the balances is an error. -/
def BeaconState.setBalance (state : BeaconState preset fork) (index : ValidatorIndex)
    (balance : Gwei) : Except AccessorError (BeaconState preset fork) :=
  if inside : index.toNat < state.balances.data.size then
    .ok (state.putBalance index.toNat inside balance)
  else .error (.indexOutOfRange index)

/-- The state with the validator at an index of the registry replaced. -/
def BeaconState.putValidator (state : BeaconState preset fork) (index : Nat)
    (inside : index < state.validators.data.size) (validator : Validator) :
    BeaconState preset fork :=
  { state with validators := state.validators.set index validator inside }

/-- The state with a validator of the registry replaced.

An index past the registry is an error. -/
def BeaconState.setValidator (state : BeaconState preset fork) (index : ValidatorIndex)
    (validator : Validator) : Except AccessorError (BeaconState preset fork) :=
  if inside : index.toNat < state.validators.data.size then
    .ok (state.putValidator index.toNat inside validator)
  else .error (.indexOutOfRange index)

/-- The balance of a validator. -/
def getBalance (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Gwei :=
  match state.balances.data[index.toNat]? with
  | some balance => .ok balance
  | none => .error (.indexOutOfRange index)

/-- A validator of the registry. -/
def getValidator (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Validator :=
  match state.validators.data[index.toNat]? with
  | some validator => .ok validator
  | none => .error (.indexOutOfRange index)

/-- The balance at a plain integer position.

A missing position is out of range, or an overflow at `2^64` or more. -/
def getBalanceAt (state : BeaconState preset fork) (position : Nat) : Except AccessorError Gwei :=
  match state.balances.data[position]? with
  | some balance => .ok balance
  | none => do
    let index ← liftArith (ofNatChecked position)
    throw (.indexOutOfRange index)

/-- The validator at a plain integer position.

A missing position is out of range, or an overflow at `2^64` or more. -/
def getValidatorAt (state : BeaconState preset fork) (position : Nat) :
    Except AccessorError Validator :=
  match state.validators.data[position]? with
  | some validator => .ok validator
  | none => do
    let index ← liftArith (ofNatChecked position)
    throw (.indexOutOfRange index)

/-- Replace the validator at a plain integer position, with an error outside the registry. -/
def BeaconState.setValidatorAt (state : BeaconState preset fork) (position : Nat)
    (validator : Validator) : Except AccessorError (BeaconState preset fork) :=
  if inside : position < state.validators.data.size then
    .ok (state.putValidator position inside validator)
  else do
    let index ← liftArith (ofNatChecked position)
    throw (.indexOutOfRange index)

/-- The state with a balance raised by an amount. -/
def increaseBalance (state : BeaconState preset fork) (index : ValidatorIndex) (delta : Gwei) :
    Except AccessorError (BeaconState preset fork) := do
  -- The balance `b` becomes `b + d`, for the amount `d`; `2^64` or more is an overflow.
  let balance ← liftArith (addChecked (← getBalance state index) delta)
  state.setBalance index balance

/-- The state with a balance lowered by an amount, or set to zero if the amount is larger. -/
def decreaseBalance (state : BeaconState preset fork) (index : ValidatorIndex) (delta : Gwei) :
    Except AccessorError (BeaconState preset fork) := do
  -- The balance `b` becomes `b - d` if `d ≤ b`, for the amount `d`, and else 0.
  state.setBalance index (saturatingSub (← getBalance state index) delta)

/-- The epoch at which a validator that starts to exit now leaves, before Electra. -/
def exitQueueEpoch (config : Config) (state : BeaconState preset fork) :
    Except AccessorError Epoch := do
  let validators := state.validators.data.toList
  -- The first epoch an exit may take, `e + 1 + MAX_SEED_LOOKAHEAD` for the current epoch `e`.
  let earliest ← liftArith (computeActivationExitEpoch preset (getCurrentEpoch state))
  -- The exit queue epoch `q`: the latest exit epoch of the registry, and at least that first one.
  let latest := (validators.filter (·.exitEpoch != FAR_FUTURE_EPOCH)).foldl
    (fun latest validator => max latest validator.exitEpoch) earliest
  -- The number of validators that exit at `q`.
  let churn := (validators.filter (·.exitEpoch == latest)).length
  -- If that number has reached the churn limit, the validator leaves at `q + 1`.
  if (getValidatorChurnLimit config state).toNat ≤ churn then liftArith (addChecked latest 1)
  else return latest

/-- The epoch at which an exit of a balance leaves, and the state with the exit queue updated.

Before Electra the queue counts validators, and the state stays the same.

From Electra the queue counts balance, as [EIP-7251] specifies, so the exit spends churn.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def exitQueue (config : Config) (state : BeaconState preset fork) (exitBalance : Gwei) :
    Except AccessorError (BeaconState preset fork × Epoch) :=
  -- From Electra the exit spends churn of balance.
  if electra : .pectra ≤ fork then computeExitEpochAndUpdateChurn config state electra exitBalance
  -- Before Electra the queue counts validators, and the state stays the same.
  else return (state, ← exitQueueEpoch config state)

/-- The state in which a validator starts to exit, unless it has already started. -/
def initiateValidatorExit (config : Config) (state : BeaconState preset fork)
    (index : ValidatorIndex) : Except AccessorError (BeaconState preset fork) := do
  let validator ← getValidator state index
  -- An exit epoch other than `FAR_FUTURE_EPOCH` means it has started, and nothing changes.
  if validator.exitEpoch != FAR_FUTURE_EPOCH then return state
  else
    -- It leaves at the epoch of the exit queue for its effective balance.
    let (state, exitEpoch) ← exitQueue config state validator.effectiveBalance
    -- It may withdraw `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` epochs after that.
    let withdrawableEpoch ←
      liftArith (addChecked exitEpoch config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY)
    state.setValidator index { validator with exitEpoch, withdrawableEpoch }

/-- A list of the state with one more element at its end.

Before the fork at which the list loses its limit, an append to a full list is an error. -/
def appendWithinLimit {switch : Base.Fork} {α : Type} {limit : Nat}
    (list : ForkList switch fork α limit) (item : α) :
    Except AccessorError (ForkList switch fork α limit) :=
  -- Before the fork at which the list loses its limit, the list stays within it.
  if fits : fork < switch → list.data.size + 1 ≤ limit then
    .ok ⟨list.data.push item, fun before => by simpa using fits before⟩
  else .error (.listFull limit)

/-- From Electra: the state with a deposit at the end of the pending deposits.

A queue at its limit is an error. -/
def addPendingDeposit (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (deposit : PendingDeposit) : Except AccessorError (BeaconState preset fork) := do
  let pending ← appendWithinLimit (state.pendingDeposits electra) deposit
  return { state with pendingDeposits := fun _ => pending }

/-- From Electra: the state in which the excess balance of a validator waits as a pending deposit.

The genesis slot of the deposit tells it apart from a deposit that comes as a request. -/
def queueExcessActiveBalance (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (index : ValidatorIndex) : Except AccessorError (BeaconState preset fork) := do
  let balance ← getBalance state index
  -- Only a balance `b` above `MIN_ACTIVATION_BALANCE` has an excess.
  if preset.MIN_ACTIVATION_BALANCE < balance then
    -- The deposit of `b - MIN_ACTIVATION_BALANCE`, with the key and credentials of the validator.
    --
    -- It carries the signature of the point at infinity and the slot `GENESIS_SLOT`.
    let validator ← getValidator state index
    let deposit : PendingDeposit := ⟨validator.pubkey, validator.withdrawalCredentials,
      balance - preset.MIN_ACTIVATION_BALANCE,
      Cryptography.Bls.Signatures.G2_POINT_AT_INFINITY, GENESIS_SLOT⟩
    let pending ← appendWithinLimit (state.pendingDeposits electra) deposit
    -- The balance becomes `MIN_ACTIVATION_BALANCE`.
    let state ← state.setBalance index preset.MIN_ACTIVATION_BALANCE
    return { state with pendingDeposits := fun _ => pending }
  else return state

/-- From Electra: the state in which a validator has compounding credentials. -/
def switchToCompoundingValidator (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (index : ValidatorIndex) : Except AccessorError (BeaconState preset fork) := do
  let validator ← getValidator state index
  -- Byte 0 of its credentials becomes `0x02`, the compounding prefix, and the rest stays.
  let withdrawalCredentials :=
    validator.withdrawalCredentials.set 0 COMPOUNDING_WITHDRAWAL_PREFIX[0]
  -- Its balance above `MIN_ACTIVATION_BALANCE` then waits as a pending deposit.
  queueExcessActiveBalance (← state.setValidator index { validator with withdrawalCredentials })
    electra index

/-- The share of the whistleblower reward that goes to the proposer. -/
def proposerShare (preset : Preset) (fork : Base.Fork) (whistleblowerReward : Gwei) :
    Except AccessorError Gwei :=
  -- From Altair `floor(w * PROPOSER_WEIGHT / WEIGHT_DENOMINATOR)`, for the reward `w`.
  if .altair ≤ fork then
    return (← liftArith (mulChecked whistleblowerReward PROPOSER_WEIGHT)) / WEIGHT_DENOMINATOR
  -- Before Altair `floor(w / PROPOSER_REWARD_QUOTIENT)`.
  else return whistleblowerReward / preset.PROPOSER_REWARD_QUOTIENT

/-- From Gloas: the state without the pending builder payments of the blocks of a proposer. -/
def cancelProposerPayments (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (proposer : ValidatorIndex) : BeaconState preset fork :=
  -- Each payment whose proposer is the validator becomes the payment of no bid.
  let cancel (payment : BuilderPendingPayment) :=
    if payment.proposerIndex = proposer then .empty else payment
  let payments := RootedVector.ofVector ((state.builderPendingPayments gloas).elements.map cancel)
  { state with builderPendingPayments := fun _ => payments }

/-- The state after a validator is slashed.

The proposer is the whistleblower by default. -/
def slashValidator (config : Config) (state : BeaconState preset fork)
    (slashedIndex : ValidatorIndex) (whistleblowerIndex : Option ValidatorIndex := none) :
    Except AccessorError (BeaconState preset fork) := do
  let epoch := getCurrentEpoch state
  -- The validator starts to exit.
  let state ← initiateValidatorExit config state slashedIndex
  -- It is slashed, and cannot withdraw before `e + EPOCHS_PER_SLASHINGS_VECTOR`, for the epoch `e`.
  let validator ← getValidator state slashedIndex
  let withdrawableEpoch := max validator.withdrawableEpoch
    (← liftArith (addChecked epoch preset.EPOCHS_PER_SLASHINGS_VECTOR))
  let state ← state.setValidator slashedIndex
    { validator with slashed := true, withdrawableEpoch }
  -- Its effective balance `b` joins the slashings, which set a later penalty.
  --
  -- It joins entry `e mod EPOCHS_PER_SLASHINGS_VECTOR`.
  let slashed ← readCircular state.slashings.elements epoch
  let slashed ← liftArith (addChecked slashed validator.effectiveBalance)
  let slashings ← writeCircularRooted state.slashings epoch slashed
  let state := { state with slashings }
  -- It pays `floor(b / MIN_SLASHING_PENALTY_QUOTIENT)` at once, by the quotient of the fork.
  let parameters := parameters preset fork
  let state ← decreaseBalance state slashedIndex
    (validator.effectiveBalance / parameters.MIN_SLASHING_PENALTY_QUOTIENT)
  -- The whistleblower is the proposer of the slot unless one is given.
  let proposerIndex ← getBeaconProposerIndex state
  let whistleblowerIndex := whistleblowerIndex.getD proposerIndex
  -- The whistleblower reward is `w = floor(b / WHISTLEBLOWER_REWARD_QUOTIENT)`, by the fork.
  let whistleblowerReward := validator.effectiveBalance / parameters.WHISTLEBLOWER_REWARD_QUOTIENT
  -- The proposer earns its share of `w`, and the whistleblower the rest.
  let proposerReward ← proposerShare preset fork whistleblowerReward
  let state ← increaseBalance state proposerIndex proposerReward
  let state ← increaseBalance state whistleblowerIndex (whistleblowerReward - proposerReward)
  -- From Gloas the pending builder payments of its blocks are cancelled, as EIP-7732 specifies.
  return if gloas : .glamsterdam ≤ fork then cancelProposerPayments state gloas slashedIndex
    else state

end EthLib.Consensus

module

public import EthLib.Consensus.Credentials
public import EthLib.Consensus.Transition.BuilderRequests

/-!
# `Consensus.Transition.Requests`

From Electra: the withdrawals and consolidations that the execution layer requests.

A withdrawal request comes from the withdrawal address of a validator, as [EIP-7002] specifies.

An amount of zero asks for a full exit, which starts only when no partial withdrawal waits.

Any other amount asks for a partial withdrawal from a validator with compounding credentials.

It takes only the balance above the activation balance.

A consolidation request moves the balance of a source validator to a target, as [EIP-7251] says.

The source exits, and its balance moves once it can withdraw.

A request with one key for both source and target switches that validator to compounding instead.

A request that fails a condition changes nothing.

A 64-bit overflow is an error, and so is a known key at a position of `2^64` or more.

[EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002#consensus-layer
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork}

/-- The position of the first validator with a key in the registry, if any. -/
def findValidatorByPubkey (state : BeaconState preset fork) (pubkey : BLSPubkey) :
    Option (Fin state.validators.data.size) :=
  state.validators.data.findFinIdx? (·.pubkey == pubkey)

/-- Whether a validator may send a request now.

It must be active, not exit, and have been active for long enough. -/
def canRequest (config : Config) (state : BeaconState preset fork) (validator : Validator) :
    Except TransitionError Bool := do
  let epoch := getCurrentEpoch state
  if !isActiveValidator validator epoch || validator.exitEpoch != FAR_FUTURE_EPOCH then
    return false
  let eligible ←
    liftAccessor (liftArith (addChecked validator.activationEpoch config.SHARD_COMMITTEE_PERIOD))
  return eligible ≤ epoch

/-- From Electra: the state after a request to withdraw part of a balance.

The validator must have compounding credentials.

Its effective balance must be at least the activation balance.

It keeps the activation balance and the withdrawals that already wait.

It withdraws the requested amount, but at most the rest of its balance.

The withdrawal waits in the exit churn, then a fixed delay. -/
def requestPartialWithdrawal (config : Config) (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (index : ValidatorIndex) (validator : Validator)
    (amount owed : Gwei) :
    Except TransitionError (BeaconState preset fork) := do
  let balance ← liftAccessor (getBalance state index)
  let kept ← liftAccessor (liftArith (addChecked preset.MIN_ACTIVATION_BALANCE owed))
  unless hasCompoundingWithdrawalCredential validator &&
      preset.MIN_ACTIVATION_BALANCE ≤ validator.effectiveBalance && kept < balance do
    return state
  let toWithdraw := min (balance - kept) amount
  let (state, exitEpoch) ←
    liftAccessor (computeExitEpochAndUpdateChurn config state electra toWithdraw)
  let withdrawableEpoch ←
    liftAccessor (liftArith (addChecked exitEpoch config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY))
  let pending ← liftAccessor (appendWithinLimit (state.pendingPartialWithdrawals electra)
    ⟨index, toWithdraw, withdrawableEpoch⟩)
  return { state with pendingPartialWithdrawals := fun _ => pending }

/-- From Electra: the state after a withdrawal request.

While the pending partial withdrawals are at their limit, only a full exit is taken.

The request must name a known key, from the address of its execution credentials.

The validator must be active, not exit, and have been active for long enough.

A full exit starts only when no partial withdrawal of the validator waits.

A known key at a position of `2^64` or more is an overflow. -/
def processWithdrawalRequest (config : Config) (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (request : WithdrawalRequest) :
    Except TransitionError (BeaconState preset fork) := do
  let fullExit := request.amount == FULL_EXIT_REQUEST_AMOUNT
  if (state.pendingPartialWithdrawals electra).data.size ==
      preset.PENDING_PARTIAL_WITHDRAWALS_LIMIT.toNat && !fullExit then
    return state
  let some position := findValidatorByPubkey state request.validatorPubkey | return state
  let index ← liftAccessor (liftArith (ofNatChecked position.val))
  let validator := state.validators.data[position]
  unless hasExecutionWithdrawalCredential validator &&
      credentialAddress validator.withdrawalCredentials == request.sourceAddress do
    return state
  unless ← canRequest config state validator do return state
  let owed ← liftAccessor (getPendingBalanceToWithdraw state electra index)
  if fullExit then
    if owed = 0 then liftAccessor (initiateValidatorExit config state index) else return state
  else requestPartialWithdrawal config state electra index validator request.amount owed

/-- From Electra: whether a validator may switch to compounding credentials on a request.

The request must come from the address of its credentials.

Those credentials must have the execution address prefix.

The validator must be active and not exit. -/
def isValidSwitchToCompoundingRequest (state : BeaconState preset fork)
    (request : ConsolidationRequest) (validator : Validator) : Bool :=
  credentialAddress validator.withdrawalCredentials == request.sourceAddress &&
    hasEth1WithdrawalCredential validator &&
    isActiveValidator validator (getCurrentEpoch state) &&
    validator.exitEpoch == FAR_FUTURE_EPOCH

/-- From Electra: the state in which a source validator exits to consolidate into a target.

It exits in the consolidation churn for its effective balance.

It may withdraw a fixed delay after that.

The consolidation then waits in the queue. -/
def queueConsolidation (config : Config) (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (sourceIndex : ValidatorIndex) (source : Validator)
    (targetIndex : ValidatorIndex) : Except TransitionError (BeaconState preset fork) := do
  let (state, exitEpoch) ← liftAccessor
    (computeConsolidationEpochAndUpdateChurn config state electra source.effectiveBalance)
  let withdrawableEpoch ←
    liftAccessor (liftArith (addChecked exitEpoch config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY))
  let state ← liftAccessor
    (state.setValidator sourceIndex { source with exitEpoch, withdrawableEpoch })
  let pending ← liftAccessor (appendWithinLimit (state.pendingConsolidations electra)
    ⟨sourceIndex, targetIndex⟩)
  return { state with pendingConsolidations := fun _ => pending }

/-- From Electra: the state after a consolidation request.

A request with one key for both source and target may only switch that validator to compounding.

Otherwise the request is ignored while the pending consolidations are at their limit.

It is also ignored while the churn of consolidations is at most the activation balance.

Both keys must be known.

The request must come from the address of the execution credentials of the source.

The target must have compounding credentials.

Both must be active and not exit.

The source must have been active for long enough, with no partial withdrawal waiting.

The source then exits to consolidate into the target.

A known key at a position of `2^64` or more is an overflow. -/
def processConsolidationRequest (config : Config) (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (request : ConsolidationRequest) :
    Except TransitionError (BeaconState preset fork) := do
  if request.sourcePubkey == request.targetPubkey then
    let some position := findValidatorByPubkey state request.sourcePubkey | return state
    let index ← liftAccessor (liftArith (ofNatChecked position.val))
    if isValidSwitchToCompoundingRequest state request state.validators.data[position] then
      liftAccessor (switchToCompoundingValidator state electra index)
    else return state
  else
    if (state.pendingConsolidations electra).data.size ==
        preset.PENDING_CONSOLIDATIONS_LIMIT.toNat then
      return state
    if (← liftAccessor (getConsolidationChurnLimit config state)) ≤ preset.MIN_ACTIVATION_BALANCE
    then return state
    let some sourcePosition := findValidatorByPubkey state request.sourcePubkey | return state
    let some targetPosition := findValidatorByPubkey state request.targetPubkey | return state
    let sourceIndex ← liftAccessor (liftArith (ofNatChecked sourcePosition.val))
    let targetIndex ← liftAccessor (liftArith (ofNatChecked targetPosition.val))
    let source := state.validators.data[sourcePosition]
    let target := state.validators.data[targetPosition]
    unless hasExecutionWithdrawalCredential source &&
        credentialAddress source.withdrawalCredentials == request.sourceAddress do
      return state
    unless hasCompoundingWithdrawalCredential target do return state
    let epoch := getCurrentEpoch state
    unless isActiveValidator source epoch && isActiveValidator target epoch do return state
    unless source.exitEpoch == FAR_FUTURE_EPOCH && target.exitEpoch == FAR_FUTURE_EPOCH do
      return state
    let eligible ←
      liftAccessor (liftArith (addChecked source.activationEpoch config.SHARD_COMMITTEE_PERIOD))
    if epoch < eligible then return state
    if 0 < (← liftAccessor (getPendingBalanceToWithdraw state electra sourceIndex)) then
      return state
    queueConsolidation config state electra sourceIndex source targetIndex

/-- From Electra: one pass over the pending consolidations from the front, and the number it read.

A consolidation from a slashed source is dropped.

The pass stops at the first source that cannot yet withdraw in the next epoch.

Otherwise the effective balance of the source, but at most its balance, moves to the target. -/
def passPendingConsolidations (nextEpoch : Epoch) (state : BeaconState preset fork) :
    List PendingConsolidation → Except TransitionError (BeaconState preset fork × Nat)
  | [] => return (state, 0)
  | consolidation :: rest => do
    let source ← liftAccessor (getValidator state consolidation.sourceIndex)
    if source.slashed then
      let (state, read) ← passPendingConsolidations nextEpoch state rest
      return (state, read + 1)
    if nextEpoch < source.withdrawableEpoch then return (state, 0)
    let balance ← liftAccessor (getBalance state consolidation.sourceIndex)
    let moved := min balance source.effectiveBalance
    let state ← liftAccessor (decreaseBalance state consolidation.sourceIndex moved)
    let state ← liftAccessor (increaseBalance state consolidation.targetIndex moved)
    let (state, read) ← passPendingConsolidations nextEpoch state rest
    return (state, read + 1)

/-- From Electra: the state after the pending consolidations of an epoch.

The queue keeps the consolidations that the pass did not read. -/
def processPendingConsolidations (state : BeaconState preset fork) (electra : .pectra ≤ fork) :
    Except TransitionError (BeaconState preset fork) := do
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  let queue := state.pendingConsolidations electra
  let (state, read) ← passPendingConsolidations nextEpoch state queue.data.toList
  let left : PendingConsolidations preset fork :=
    ⟨queue.data.extract read, fun before => by
      have bound := queue.bound before
      simp only [Array.size_extract]
      omega⟩
  return { state with pendingConsolidations := fun _ => left }

end EthLib.Consensus

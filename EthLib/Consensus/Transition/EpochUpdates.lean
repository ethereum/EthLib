module

public import EthLib.Consensus.Credentials
public import EthLib.Consensus.Transition.EpochRewards

/-!
# `Consensus.Transition.EpochUpdates`

The steps of the epoch transition after the rewards.

The registry queues new validators for activation, and activates some.

From Electra every queued validator whose place is finalized is activated, with no churn limit.

It ejects the validators whose balance fell too low.

Slashed validators pay a penalty that grows with the balance slashed around them.

The votes on the deposit contract restart with each voting period.

The effective balances follow the balances, with some hysteresis.

The circular buffers of slashings and RANDAO mixes move on to the next epoch.

Before Capella, the roots of each span of slots join the historical roots.

Before Altair, the pending attestations of the current epoch become those of the previous one.

A 64-bit overflow is an error.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Serialization.Ssz.SszType

variable {preset : Preset} {fork : Base.Fork}

/-! ## Registry updates -/

/-- A validator that joins the activation queue at the next epoch, if it is eligible for it. -/
def queueForActivation (state : BeaconState preset fork) (validator : Validator) :
    Except TransitionError Validator :=
  if isEligibleForActivationQueue preset fork validator then do
    let activationEligibilityEpoch ←
      liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
    return { validator with activationEligibilityEpoch }
  else pure validator

/-- The state after the first pass of the registry over one validator.

A validator eligible for the activation queue joins it at the next epoch.

An active validator whose effective balance is at most the ejection balance starts to exit. -/
def updateRegistryEntry (config : Config) (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index.toUInt64)
  let validator ← queueForActivation state validator
  let state ← liftAccessor (state.setValidator index.toUInt64 validator)
  if isActiveValidator validator (getCurrentEpoch state) &&
      validator.effectiveBalance ≤ config.EJECTION_BALANCE then
    liftAccessor (initiateValidatorExit config state index.toUInt64)
  else pure state

/-- The validators eligible for activation, in the order of their queue.

The queue orders them by the epoch at which they joined it, then by index. -/
def activationQueue (state : BeaconState preset fork) : List ValidatorIndex :=
  let eligible := state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isEligibleForActivation state validator then
      some (validator.activationEligibilityEpoch, index.toUInt64)
    else none
  (eligible.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)).map (·.2)

/-- The state with a validator activated, at the first epoch an activation may take. -/
def activateValidator (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index)
  let activationEpoch ←
    liftAccessor (liftArith (computeActivationExitEpoch preset (getCurrentEpoch state)))
  liftAccessor (state.setValidator index { validator with activationEpoch })

/-- From Electra: the state after the registry updates of one validator, as [EIP-7251] specifies.

A validator eligible for the activation queue joins it at the next epoch.

Otherwise an active validator at or below the ejection balance starts to exit.

Otherwise a validator eligible for activation is activated at the given epoch.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def updateRegistryEntryElectra (config : Config) (activationEpoch : Epoch)
    (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index.toUInt64)
  let currentEpoch := getCurrentEpoch state
  if isEligibleForActivationQueue preset fork validator then
    let activationEligibilityEpoch ← liftAccessor (liftArith (addChecked currentEpoch 1))
    liftAccessor (state.setValidator index.toUInt64 { validator with activationEligibilityEpoch })
  else if isActiveValidator validator currentEpoch &&
      validator.effectiveBalance ≤ config.EJECTION_BALANCE then
    liftAccessor (initiateValidatorExit config state index.toUInt64)
  else if isEligibleForActivation state validator then
    liftAccessor (state.setValidator index.toUInt64 { validator with activationEpoch })
  else return state

/-- The state after the registry updates.

Each validator in turn may join the activation queue, and may be ejected.

Then the first validators of the queue are activated, as many as the churn limit allows.

From Deneb the activations have their own limit, as [EIP-7514] specifies.

From Electra one pass over the validators also activates them, with no limit, as [EIP-7251] says.

They are activated at the first epoch an activation may take.

[EIP-7514]: https://eips.ethereum.org/EIPS/eip-7514#specification
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processRegistryUpdates (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if .pectra ≤ fork then do
    let activationEpoch ←
      liftAccessor (liftArith (computeActivationExitEpoch preset (getCurrentEpoch state)))
    (List.range state.validators.data.size).foldlM
      (updateRegistryEntryElectra config activationEpoch) state
  else do
    let state ← (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state
    let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config state
      else getValidatorChurnLimit config state
    let activated := (activationQueue state).take limit.toNat
    activated.foldlM activateValidator state

/-! ## Slashings -/

/-- The sum of the slashed balances of the recent epochs.

A sum that reaches `2^64` is an error. -/
def slashingsSum (state : BeaconState preset fork) : Except TransitionError Gwei :=
  liftAccessor (liftArith (state.slashings.toList.foldlM addChecked 0))

/-- The state after the slashing penalty of one validator, if it is due.

It is due for a slashed validator halfway through its time before it may withdraw.

The penalty is its share of the active balance, times the adjusted slashed balance.

The share is counted in increments, so that the product does not overflow. -/
def applySlashingPenalty (state : BeaconState preset fork)
    (totalBalance adjustedSlashingBalance : Gwei) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index.toUInt64)
  if validator.slashed then
    let due ← liftAccessor (liftArith
      (addChecked (getCurrentEpoch state) (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2)))
    if due = validator.withdrawableEpoch then
      let increment := preset.EFFECTIVE_BALANCE_INCREMENT
      let numerator ← liftAccessor (liftArith
        (mulChecked (validator.effectiveBalance / increment) adjustedSlashingBalance))
      let penalty ← liftAccessor (liftArith (mulChecked (numerator / totalBalance) increment))
      liftAccessor (decreaseBalance state index.toUInt64 penalty)
    else pure state
  else pure state

/-- From Electra: the state after the slashing penalty of one validator, if it is due.

It is due for a slashed validator halfway through its time before it may withdraw.

The penalty is a penalty per increment times the effective balance counted in increments. -/
def applySlashingPenaltyElectra (state : BeaconState preset fork) (perIncrement : Gwei)
    (index : Nat) : Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index.toUInt64)
  if validator.slashed then
    let due ← liftAccessor (liftArith
      (addChecked (getCurrentEpoch state) (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2)))
    if due = validator.withdrawableEpoch then
      let penalty ← liftAccessor (liftArith (mulChecked perIncrement
        (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT)))
      liftAccessor (decreaseBalance state index.toUInt64 penalty)
    else pure state
  else pure state

/-- The state after the slashing penalties of an epoch.

The slashed balance of the recent epochs is scaled by a multiplier of the fork.

It is capped by the active balance.

From Electra the penalty is counted per increment of balance, as [EIP-7251] specifies.

The penalty per increment divides the capped balance by the active balance counted in increments.

The active balance is at least one increment, so only a zero increment divides by zero.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processSlashings (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let total ← liftAccessor (getTotalActiveBalance state)
  let slashed ← liftAccessor (liftArith
    (mulChecked (← slashingsSum state) (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER))
  let indices := List.range state.validators.data.size
  if .pectra ≤ fork then
    let perIncrement ← liftAccessor (liftArith do
      divChecked (min slashed total) (← divChecked total preset.EFFECTIVE_BALANCE_INCREMENT))
    indices.foldlM (applySlashingPenaltyElectra · perIncrement ·) state
  else
    indices.foldlM (applySlashingPenalty · total (min slashed total) ·) state

/-! ## Resets and rotations -/

/-- The state after the reset of the votes on the deposit contract.

The votes restart when the next epoch starts a voting period.

The step exists only before Heze, which removes the votes. -/
def processEth1DataReset (_before : fork < .hegota) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  if nextEpoch % preset.EPOCHS_PER_ETH1_VOTING_PERIOD = 0 then
    return { state with eth1DataVotes := fun _ => ⟨#[], by simp⟩ }
  else return state

/-- Whether a balance leaves the band around an effective balance.

It leaves it below by more than the downward threshold, or above by more than the upward one.

The second sum is computed only when the first test fails. -/
def leavesBand (balance effectiveBalance downward upward : Gwei) : Except TransitionError Bool := do
  if (← liftAccessor (liftArith (addChecked balance downward))) < effectiveBalance then pure true
  else pure (decide ((← liftAccessor (liftArith (addChecked effectiveBalance upward))) < balance))

/-- The effective balance that a balance gives, with some hysteresis.

It changes only when the balance leaves a band around it.

The band reaches a fixed fraction of an increment below and above.

It then becomes the balance rounded down to an increment, and at most a largest value. -/
def updatedEffectiveBalance (preset : Preset) (largest balance effectiveBalance : Gwei) :
    Except TransitionError Gwei := do
  let hysteresis := preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT
  let downward ←
    liftAccessor (liftArith (mulChecked hysteresis preset.HYSTERESIS_DOWNWARD_MULTIPLIER))
  let upward ←
    liftAccessor (liftArith (mulChecked hysteresis preset.HYSTERESIS_UPWARD_MULTIPLIER))
  let leaves ← leavesBand balance effectiveBalance downward upward
  return if leaves then
      min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest
    else effectiveBalance

/-- The state with the effective balance of one validator updated from its balance.

Its largest effective balance is that of the fork, which from Electra depends on its credentials. -/
def updateEffectiveBalance (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index.toUInt64)
  let balance ← liftAccessor (getBalance state index.toUInt64)
  let effectiveBalance ← updatedEffectiveBalance preset
    (withdrawalMaxEffectiveBalance preset fork validator) balance validator.effectiveBalance
  liftAccessor (state.setValidator index.toUInt64 { validator with effectiveBalance })

/-- The state after the update of the effective balances.

From Electra the largest effective balance depends on the credentials, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processEffectiveBalanceUpdates (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  (List.range state.validators.data.size).foldlM updateEffectiveBalance state

/-- The state with the slashed balance of the next epoch cleared.

If the buffer of slashed balances has length zero, the reset fails, since it has no position. -/
def processSlashingsReset (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  let slashings ← liftAccessor (writeCircular state.slashings nextEpoch 0)
  return { state with slashings }

/-- The state with the RANDAO mix of the next epoch set to that of the current epoch.

If the buffer of mixes has length zero, the reset fails, since it has no position. -/
def processRandaoMixesReset (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let currentEpoch := getCurrentEpoch state
  let nextEpoch ← liftAccessor (liftArith (addChecked currentEpoch 1))
  let mix ← liftAccessor (getRandaoMix state currentEpoch)
  let randaoMixes ← liftAccessor (writeCircularRooted state.randaoMixes nextEpoch mix)
  return { state with randaoMixes }

/-- The historical roots with one more root, or an error when the list is full. -/
def appendHistoricalRoot (roots : SszList Root preset.HISTORICAL_ROOTS_LIMIT.toNat)
    (root : Root) : Except TransitionError (SszList Root preset.HISTORICAL_ROOTS_LIMIT.toNat) :=
  if fits : roots.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat then
    .ok ⟨roots.data.push root, by simp only [Array.size_push]; omega⟩
  else .error .historicalRootsFull

/-- The state after the historical roots update.

When the next epoch starts a span of slots, the span joins the history.

The root of its block roots and state roots joins the historical roots.

From Capella the summaries of the spans take its place. -/
def processHistoricalRootsUpdate (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if .shapella ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else do
    let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
    if nextEpoch % (preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH) = 0 then
      let batch : HistoricalBatch preset := ⟨state.blockRoots, state.stateRoots⟩
      let root ← liftSsz (hashTreeRoot batch)
      return { state with historicalRoots := ← appendHistoricalRoot state.historicalRoots root }
    else return state

/-- From Capella: the state after the historical summaries update.

When the next epoch starts a span of slots, the span joins the history.

The root of its block roots and the root of its state roots join the summaries, as one entry. -/
def processHistoricalSummariesUpdate (state : BeaconState preset fork)
    (capella : .shapella ≤ fork) : Except TransitionError (BeaconState preset fork) := do
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  if nextEpoch % (preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH) = 0 then
    let summary : HistoricalSummary :=
      ⟨← liftSsz (hashTreeRoot state.blockRoots), ← liftSsz (hashTreeRoot state.stateRoots)⟩
    let summaries := state.historicalSummaries capella
    if fits : summaries.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat then
      let summaries : SszList HistoricalSummary preset.HISTORICAL_ROOTS_LIMIT.toNat :=
        ⟨summaries.data.push summary, by simp only [Array.size_push]; omega⟩
      return { state with historicalSummaries := fun _ => summaries }
    else throw .historicalSummariesFull
  else return state

/-- The state after the rotation of the pending attestations.

Those of the current epoch become those of the previous epoch, and the current ones start empty.

From Altair the participation flags rotate instead, in their own step. -/
def processParticipationRecordUpdates (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else pure { state with
    previousEpochAttestations := state.currentEpochAttestations
    currentEpochAttestations := fun _ => ⟨#[], by simp⟩ }

end EthLib.Consensus

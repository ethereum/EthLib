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
  -- An eligible validator gets the activation eligibility epoch `e + 1`, for the current epoch `e`.
  if isEligibleForActivationQueue preset fork validator then do
    let activationEligibilityEpoch ←
      liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
    return { validator with activationEligibilityEpoch }
  else pure validator

/-- The state after the first pass of the registry over one validator. -/
def updateRegistryEntry (config : Config) (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  -- A validator eligible for the activation queue joins it at the next epoch.
  let validator ← liftAccessor (getValidatorAt state index)
  let validator ← queueForActivation state validator
  let state ← liftAccessor (state.setValidatorAt index validator)
  -- An active validator whose effective balance is at most `EJECTION_BALANCE` starts to exit.
  if isActiveValidator validator (getCurrentEpoch state) &&
      validator.effectiveBalance ≤ config.EJECTION_BALANCE then do
    let validatorIndex ← liftAccessor (liftArith (ofNatChecked index))
    liftAccessor (initiateValidatorExit config state validatorIndex)
  else pure state

/-- The validators eligible for activation, in the order of their queue.

The queue orders them by the epoch at which they joined it, then by index. -/
def activationQueue (state : BeaconState preset fork) : List ValidatorIndex :=
  -- The validators eligible for activation, with their activation eligibility epochs.
  let eligible := state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isEligibleForActivation state validator then
      some (validator.activationEligibilityEpoch, index.toUInt64)
    else none
  -- Sorted by activation eligibility epoch, then by index.
  (eligible.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)).map (·.2)

/-- The state with a validator activated, at the first epoch an activation may take. -/
def activateValidator (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidator state index)
  -- The activation epoch is `e + 1 + MAX_SEED_LOOKAHEAD`, for the current epoch `e`.
  let activationEpoch ←
    liftAccessor (liftArith (computeActivationExitEpoch preset (getCurrentEpoch state)))
  liftAccessor (state.setValidator index { validator with activationEpoch })

/-- From Electra: the state after the registry updates of one validator, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def updateRegistryEntryElectra (config : Config) (activationEpoch : Epoch)
    (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidatorAt state index)
  let currentEpoch := getCurrentEpoch state
  -- A validator eligible for the activation queue joins it at the next epoch.
  if isEligibleForActivationQueue preset fork validator then
    let activationEligibilityEpoch ← liftAccessor (liftArith (addChecked currentEpoch 1))
    liftAccessor (state.setValidatorAt index { validator with activationEligibilityEpoch })
  -- Otherwise an active validator at or below `EJECTION_BALANCE` starts to exit.
  else if isActiveValidator validator currentEpoch &&
      validator.effectiveBalance ≤ config.EJECTION_BALANCE then do
    let validatorIndex ← liftAccessor (liftArith (ofNatChecked index))
    liftAccessor (initiateValidatorExit config state validatorIndex)
  -- Otherwise a validator eligible for activation is activated at the given epoch.
  else if isEligibleForActivation state validator then
    liftAccessor (state.setValidatorAt index { validator with activationEpoch })
  else return state

/-- The state after the registry updates.

From Deneb the activations have their own limit, as [EIP-7514] specifies.

From Electra they have no limit, as [EIP-7251] specifies.

[EIP-7514]: https://eips.ethereum.org/EIPS/eip-7514#specification
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processRegistryUpdates (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  -- From Electra one pass over the validators also activates the eligible ones, with no limit.
  --
  -- That pass is the rule of EIP-7251.
  if .pectra ≤ fork then do
    -- They are activated at the first epoch an activation may take.
    let activationEpoch ←
      liftAccessor (liftArith (computeActivationExitEpoch preset (getCurrentEpoch state)))
    (List.range state.validators.data.size).foldlM
      (updateRegistryEntryElectra config activationEpoch) state
  else do
    -- Before Electra, each validator in turn may join the activation queue, and may be ejected.
    let state ← (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state
    -- Then the first validators of the queue are activated, as many as the churn limit allows.
    --
    -- From Deneb the activations have their own limit, as EIP-7514 specifies.
    let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config state
      else getValidatorChurnLimit config state
    let activated := (activationQueue state).take limit.toNat
    activated.foldlM activateValidator state

/-! ## Slashings -/

/-- The sum of the slashed balances of the recent epochs.

A sum that reaches `2^64` is an error. -/
def slashingsSum (state : BeaconState preset fork) : Except TransitionError Gwei :=
  -- The sum of the entries of the circular buffer of slashed balances.
  liftAccessor (liftArith (state.slashings.elements.toList.foldlM addChecked 0))

/-- The state after the slashing penalty of one validator, if it is due. -/
def applySlashingPenalty (state : BeaconState preset fork)
    (totalBalance adjustedSlashingBalance : Gwei) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidatorAt state index)
  -- Let `e` be the current epoch and `V` be `EPOCHS_PER_SLASHINGS_VECTOR`.
  --
  -- The penalty is due for a slashed validator with the withdrawable epoch `e + floor(V / 2)`.
  --
  -- That is halfway through its wait before it may withdraw.
  if validator.slashed then
    let due ← liftAccessor (liftArith
      (addChecked (getCurrentEpoch state) (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2)))
    if due = validator.withdrawableEpoch then
      -- `A` is the adjusted slashed balance and `T` the active balance.
      --
      -- `I` is the increment of balance and `b` the effective balance.
      --
      -- The penalty is `floor(floor(b / I) * A / T) * I`.
      --
      -- Counting `b` in increments keeps the product within 64 bits.
      let increment := preset.EFFECTIVE_BALANCE_INCREMENT
      let numerator ← liftAccessor (liftArith
        (mulChecked (validator.effectiveBalance / increment) adjustedSlashingBalance))
      let penalty ← liftAccessor (liftArith (mulChecked (numerator / totalBalance) increment))
      let validatorIndex ← liftAccessor (liftArith (ofNatChecked index))
      liftAccessor (decreaseBalance state validatorIndex penalty)
    else pure state
  else pure state

/-- From Electra: the state after the slashing penalty of one validator, if it is due. -/
def applySlashingPenaltyElectra (state : BeaconState preset fork) (perIncrement : Gwei)
    (index : Nat) : Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidatorAt state index)
  -- Let `e` be the current epoch and `V` be `EPOCHS_PER_SLASHINGS_VECTOR`.
  --
  -- The penalty is due for a slashed validator with the withdrawable epoch `e + floor(V / 2)`.
  if validator.slashed then
    let due ← liftAccessor (liftArith
      (addChecked (getCurrentEpoch state) (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2)))
    if due = validator.withdrawableEpoch then
      -- The penalty per increment, times `floor(b / I)`.
      --
      -- Here `b` is the effective balance and `I` the increment of balance.
      let penalty ← liftAccessor (liftArith (mulChecked perIncrement
        (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT)))
      let validatorIndex ← liftAccessor (liftArith (ofNatChecked index))
      liftAccessor (decreaseBalance state validatorIndex penalty)
    else pure state
  else pure state

/-- The state after the slashing penalties of an epoch.

From Electra the penalty is counted per increment of balance, as [EIP-7251] specifies.

The active balance is at least one increment, so only a zero increment divides by zero.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processSlashings (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let total ← liftAccessor (getTotalActiveBalance state)
  -- `S` is the slashed balance of the recent epochs, times the multiplier of the fork.
  let slashed ← liftAccessor (liftArith
    (mulChecked (← slashingsSum state) (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER))
  let indices := List.range state.validators.data.size
  -- From Electra the penalty is counted per increment of balance, as EIP-7251 specifies.
  if .pectra ≤ fork then
    -- `T` is the active balance and `I` is `EFFECTIVE_BALANCE_INCREMENT`.
    --
    -- The penalty per increment is `floor(min(S, T) / floor(T / I))`.
    let perIncrement ← liftAccessor (liftArith do
      divChecked (min slashed total) (← divChecked total preset.EFFECTIVE_BALANCE_INCREMENT))
    indices.foldlM (applySlashingPenaltyElectra · perIncrement ·) state
  -- Before Electra each validator's penalty reads `A = min(S, T)`: the scaled sum capped at `T`.
  else
    indices.foldlM (applySlashingPenalty · total (min slashed total) ·) state

/-! ## Resets and rotations -/

/-- The state after the reset of the votes on the deposit contract.

The step exists only before Heze, which removes the votes. -/
def processEth1DataReset (_before : fork < .hegota) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- The votes restart when `(e + 1) mod EPOCHS_PER_ETH1_VOTING_PERIOD = 0`, for the epoch `e`.
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  if nextEpoch % preset.EPOCHS_PER_ETH1_VOTING_PERIOD = 0 then
    return { state with eth1DataVotes := fun _ => ⟨#[], by simp⟩ }
  else return state

/-- Whether a balance leaves the band around an effective balance.

The second sum is computed only when the first test fails. -/
def leavesBand (balance effectiveBalance downward upward : Gwei) : Except TransitionError Bool := do
  -- Let `B` be the balance, `E` the effective balance, `D` the threshold below and `U` above.
  --
  -- The balance leaves the band below when `B + D < E`, and else above when `E + U < B`.
  if (← liftAccessor (liftArith (addChecked balance downward))) < effectiveBalance then pure true
  else pure (decide ((← liftAccessor (liftArith (addChecked effectiveBalance upward))) < balance))

/-- The effective balance that a balance gives, with some hysteresis. -/
def updatedEffectiveBalance (preset : Preset) (largest balance effectiveBalance : Gwei) :
    Except TransitionError Gwei := do
  -- The hysteresis step `h = floor(EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT)`.
  let hysteresis := preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT
  -- The band reaches `h * HYSTERESIS_DOWNWARD_MULTIPLIER` below the effective balance.
  --
  -- It reaches `h * HYSTERESIS_UPWARD_MULTIPLIER` above it.
  let downward ←
    liftAccessor (liftArith (mulChecked hysteresis preset.HYSTERESIS_DOWNWARD_MULTIPLIER))
  let upward ←
    liftAccessor (liftArith (mulChecked hysteresis preset.HYSTERESIS_UPWARD_MULTIPLIER))
  -- The effective balance changes only when the balance leaves the band.
  --
  -- It then becomes the balance rounded down to an increment, at most the largest value.
  let leaves ← leavesBand balance effectiveBalance downward upward
  return if leaves then
      min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest
    else effectiveBalance

/-- The state with the effective balance of one validator updated from its balance.

Its largest effective balance is that of the fork, which from Electra depends on its credentials. -/
def updateEffectiveBalance (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let validator ← liftAccessor (getValidatorAt state index)
  let balance ← liftAccessor (getBalanceAt state index)
  -- The largest effective balance is that of the fork and, from Electra, of the credentials.
  let effectiveBalance ← updatedEffectiveBalance preset
    (withdrawalMaxEffectiveBalance preset fork validator) balance validator.effectiveBalance
  liftAccessor (state.setValidatorAt index { validator with effectiveBalance })

/-- The state after the update of the effective balances.

From Electra the largest effective balance depends on the credentials, as [EIP-7251] specifies.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/
def processEffectiveBalanceUpdates (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  -- Each validator in order of index.
  (List.range state.validators.data.size).foldlM updateEffectiveBalance state

/-- The state with the slashed balance of the next epoch cleared.

If the buffer of slashed balances has length zero, the reset fails, since it has no position. -/
def processSlashingsReset (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  -- For the current epoch `e`, entry `(e + 1) mod EPOCHS_PER_SLASHINGS_VECTOR` becomes 0.
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  let slashings ← liftAccessor (writeCircularRooted state.slashings nextEpoch 0)
  return { state with slashings }

/-- The state with the RANDAO mix of the next epoch set to that of the current epoch.

If the buffer of mixes has length zero, the reset fails, since it has no position. -/
def processRandaoMixesReset (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) := do
  let currentEpoch := getCurrentEpoch state
  let nextEpoch ← liftAccessor (liftArith (addChecked currentEpoch 1))
  -- For the current epoch `e`, mix `(e + 1) mod EPOCHS_PER_HISTORICAL_VECTOR` becomes that of `e`.
  let mix ← liftAccessor (getRandaoMix state currentEpoch)
  let randaoMixes ← liftAccessor (writeCircularRooted state.randaoMixes nextEpoch mix)
  return { state with randaoMixes }

/-- The historical roots with one more root, or an error when the list is full. -/
def appendHistoricalRoot (roots : SszList Root preset.HISTORICAL_ROOTS_LIMIT.toNat)
    (root : Root) : Except TransitionError (SszList Root preset.HISTORICAL_ROOTS_LIMIT.toNat) :=
  -- The list holds at most `HISTORICAL_ROOTS_LIMIT` roots.
  if fits : roots.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat then
    .ok ⟨roots.data.push root, by simp only [Array.size_push]; omega⟩
  else .error (.historicalRootsFull preset.HISTORICAL_ROOTS_LIMIT.toNat)

/-- Before Capella: the state after the historical roots update.

From Capella the summaries of the spans take its place. -/
def processHistoricalRootsUpdate (state : BeaconState preset fork) (_before : fork < .shapella) :
    Except TransitionError (BeaconState preset fork) := do
  -- For the current epoch `e`, a span joins the history when `e + 1` is a multiple of its epochs.
  --
  -- A span has `floor(SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH)` epochs.
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  if nextEpoch % (preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH) = 0 then
    -- The root of the batch of its block roots and state roots joins the historical roots.
    let batch : HistoricalBatch preset := ⟨state.blockRoots, state.stateRoots⟩
    let root ← liftSsz (hashTreeRoot batch)
    return { state with historicalRoots := ← appendHistoricalRoot state.historicalRoots root }
  else return state

/-- From Capella: the state after the historical summaries update. -/
def processHistoricalSummariesUpdate (state : BeaconState preset fork)
    (capella : .shapella ≤ fork) : Except TransitionError (BeaconState preset fork) := do
  -- For the current epoch `e`, a span joins the history when `e + 1` is a multiple of its epochs.
  --
  -- A span has `floor(SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH)` epochs.
  let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
  if nextEpoch % (preset.SLOTS_PER_HISTORICAL_ROOT / preset.SLOTS_PER_EPOCH) = 0 then
    -- The root of its block roots and the root of its state roots join the summaries, as one entry.
    let summary : HistoricalSummary :=
      ⟨← liftSsz (hashTreeRoot state.blockRoots), ← liftSsz (hashTreeRoot state.stateRoots)⟩
    let summaries := state.historicalSummaries capella
    if fits : summaries.data.size < preset.HISTORICAL_ROOTS_LIMIT.toNat then
      let summaries : SszList HistoricalSummary preset.HISTORICAL_ROOTS_LIMIT.toNat :=
        ⟨summaries.data.push summary, by simp only [Array.size_push]; omega⟩
      return { state with historicalSummaries := fun _ => summaries }
    else throw (.historicalSummariesFull preset.HISTORICAL_ROOTS_LIMIT.toNat)
  else return state

/-- Before Altair: the state after the rotation of the pending attestations.

From Altair the participation flags rotate instead, in their own step. -/
def processParticipationRecordUpdates (state : BeaconState preset fork) (_before : fork < .altair) :
    Except TransitionError (BeaconState preset fork) :=
  -- The pending attestations of the current epoch become those of the previous epoch.
  --
  -- The current ones start empty.
  pure { state with
    previousEpochAttestations := state.currentEpochAttestations
    currentEpochAttestations := fun _ => ⟨#[], by simp⟩ }

end EthLib.Consensus

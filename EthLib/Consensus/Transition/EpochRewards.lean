module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Transition.EpochJustification

/-!
# `Consensus.Transition.EpochRewards`

The rewards and penalties of the attesters of the previous epoch.

Each eligible validator gets a base reward, which shrinks as the active balance grows.

It earns a share of it for each vote that matches: source, target and head.

It loses a whole base reward for each vote that does not match.

An attester also earns more the sooner its vote was included.

The proposer that included it earns a fixed share.

The chain leaks when it has not finalized for some epochs.

Then a matching vote earns the whole base reward.

Every eligible validator pays back four base rewards, less the proposer share.

A validator that missed the target also pays a penalty that grows with the delay of finality.

The first epoch has no rewards.

From Altair the state keeps participation flags instead of attestations.

Outside a leak, a flag earns its weight of the base reward, scaled by the balance that set it.

A validator that missed the source or the target pays its weight of the base reward.

A validator that missed the target also pays for its inactivity score.

A 64-bit overflow or underflow is an error, and so is a division by zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The share of a base reward that goes to the proposer that includes the vote. -/
def proposerReward (preset : Preset) (baseReward : Gwei) : Gwei :=
  baseReward / preset.PROPOSER_REWARD_QUOTIENT

/-- The number of epochs since the finalized epoch, counted from the previous epoch. -/
def getFinalityDelay (state : BeaconState preset fork) : Except TransitionError Epoch :=
  liftAccessor (liftArith (subChecked (getPreviousEpoch state) state.finalizedCheckpoint.epoch))

/-- Whether the chain leaks: it has not finalized for more than a fixed number of epochs. -/
def isInInactivityLeak (state : BeaconState preset fork) : Except TransitionError Bool := do
  return preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY < (← getFinalityDelay state)

/-- Whether a validator earns rewards and penalties for the previous epoch.

It must be active then, or slashed and not yet withdrawable in the epoch after it. -/
def isEligibleValidator (previousEpoch : Epoch) (validator : Validator) :
    Except TransitionError Bool :=
  if isActiveValidator validator previousEpoch then pure true
  else if validator.slashed then do
    return (← liftAccessor (liftArith (addChecked previousEpoch 1))) < validator.withdrawableEpoch
  else pure false

/-- The validators that earn rewards and penalties for the previous epoch, in increasing order. -/
def getEligibleValidatorIndices (state : BeaconState preset fork) :
    Except TransitionError (List ValidatorIndex) :=
  state.validators.data.toList.zipIdx.filterMapM fun (validator, index) => do
    return if ← isEligibleValidator (getPreviousEpoch state) validator then some index.toUInt64
      else none

/-- The deltas with an amount added at an index.

An index past the end is an error, and so is a 64-bit overflow. -/
def addDelta (deltas : Array Gwei) (index : ValidatorIndex) (amount : Gwei) :
    Except TransitionError (Array Gwei) :=
  if inside : index.toNat < deltas.size then do
    let sum ← liftAccessor (liftArith (addChecked deltas[index.toNat] amount))
    return deltas.set index.toNat sum inside
  else throw (.accessor (.indexOutOfRange index))

/-- The reward and the penalty of one eligible validator for one kind of vote.

A validator whose vote matches earns the base reward in a leak.

Otherwise it earns the base reward scaled by the share of the active balance that matched.

The balances are counted in increments, so that the product does not overflow.

A validator whose vote does not match pays the base reward.

The leak is read only for a vote that matches. -/
def componentDelta (state : BeaconState preset fork) (matched : Bool)
    (base attestingBalance totalActiveBalance : Gwei) : Except TransitionError (Gwei × Gwei) :=
  if matched then do
    let leak ← isInInactivityLeak state
    if leak then return (base, 0)
    else
      let increment := preset.EFFECTIVE_BALANCE_INCREMENT
      let numerator ← liftAccessor (liftArith (mulChecked base (attestingBalance / increment)))
      return (numerator / (totalActiveBalance / increment), 0)
  else pure (0, base)

/-- The rewards and penalties of each validator for one kind of vote.

The matching votes are those of some pending attestations. -/
def getAttestationComponentDeltas (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  let total ← liftAccessor (getTotalActiveBalance state)
  let attesters ← liftAccessor (getUnslashedAttestingIndices state attestations)
  let attestingBalance ← liftAccessor (getTotalBalance state attesters)
  let matched := markIndices size attesters
  let zeros : Array Gwei := Array.replicate size 0
  (← getEligibleValidatorIndices state).foldlM (init := (zeros, zeros))
    fun (rewards, penalties) index => do
      let base ← liftAccessor (getBaseReward state total index)
      let (reward, penalty) ←
        componentDelta state (matched.getD index.toNat false) base attestingBalance total
      return (← addDelta rewards index reward, ← addDelta penalties index penalty)

/-- Before Altair: the rewards and penalties of each validator for its source vote. -/
def getSourceDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  getAttestationComponentDeltas state
    (← getMatchingSourceAttestations state before (getPreviousEpoch state))

/-- Before Altair: the rewards and penalties of each validator for its target vote. -/
def getTargetDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  getAttestationComponentDeltas state
    (← getMatchingTargetAttestations state before (getPreviousEpoch state))

/-- Before Altair: the rewards and penalties of each validator for its head vote. -/
def getHeadDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  getAttestationComponentDeltas state
    (← getMatchingHeadAttestations state before (getPreviousEpoch state))

/-- The first included attestation with the least inclusion delay, for each signer.

An attestation replaces the one kept for a signer only with a strictly smaller delay. -/
def earliestInclusions (size : Nat)
    (signed : Array (PendingAttestation preset × List ValidatorIndex)) :
    Array (Option (PendingAttestation preset)) :=
  signed.foldl (init := Array.replicate size none) fun best (attestation, signers) =>
    signers.foldl (init := best) fun best index =>
      match best.getD index.toNat none with
      | some kept => if attestation.inclusionDelay < kept.inclusionDelay then
          best.setIfInBounds index.toNat (some attestation) else best
      | none => best.setIfInBounds index.toNat (some attestation)

/-- The inclusion rewards of one attester, under the attestation that first included its vote.

The proposer of that block earns the proposer share of the base reward of the attester.

The attester earns the rest of its base reward, divided by the inclusion delay.

A zero delay is an error. -/
def addInclusionReward (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (earliest : Array (Option (PendingAttestation preset))) (rewards : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) := do
  let some attestation := earliest.getD index.toNat none
    | throw (.accessor (.indexOutOfRange index))
  let base ← liftAccessor (getBaseReward state totalActiveBalance index)
  let rewards ← addDelta rewards attestation.proposerIndex (proposerReward preset base)
  let maxAttesterReward ← liftAccessor (liftArith (subChecked base (proposerReward preset base)))
  ensure (attestation.inclusionDelay ≠ 0) .zeroInclusionDelay
  addDelta rewards index (maxAttesterReward / attestation.inclusionDelay)

/-- Before Altair: the rewards of each validator for the inclusion of the previous epoch's votes.

There are no penalties. -/
def getInclusionDelayDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  let attestations ← getMatchingSourceAttestations state before (getPreviousEpoch state)
  let signers ← liftAccessor (attestations.toList.mapM (getPendingAttestingIndices state))
  let attesters ← liftAccessor (unslashedAmong state signers)
  let total ← liftAccessor (getTotalActiveBalance state)
  let earliest := earliestInclusions size (attestations.zip signers.toArray)
  let rewards ← attesters.foldlM (addInclusionReward state total earliest) (Array.replicate size 0)
  return (rewards, Array.replicate size 0)

/-- The inactivity penalty of one eligible validator in a leak.

It pays back four base rewards, what optimal votes earn, less the proposer share.

If it missed the target, it also pays its effective balance times the delay of finality.

That product is divided by a fixed quotient. -/
def addInactivityPenalty (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (finalityDelay : Epoch) (targetMatched : Array Bool) (penalties : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) := do
  let base ← liftAccessor (getBaseReward state totalActiveBalance index)
  let full ← liftAccessor (liftArith (mulChecked BASE_REWARDS_PER_EPOCH base))
  let paidBack ← liftAccessor (liftArith (subChecked full (proposerReward preset base)))
  let penalties ← addDelta penalties index paidBack
  if targetMatched.getD index.toNat false then pure penalties
  else do
    let validator ← liftAccessor (getValidator state index)
    let scaled ← liftAccessor (liftArith (mulChecked validator.effectiveBalance finalityDelay))
    addDelta penalties index (scaled / (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT)

/-- From Altair: the inactivity penalty of one eligible validator that missed the target.

It pays its effective balance times its inactivity score.

That product is divided by the score bias times a fixed quotient. -/
def addInactivityScorePenalty (config : Config) (state : BeaconState preset fork)
    (altair : .altair ≤ fork) (targetMatched : Array Bool) (penalties : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) :=
  if targetMatched.getD index.toNat false then pure penalties
  else do
    let validator ← liftAccessor (getValidator state index)
    let some score := (state.inactivityScores altair).data[index.toNat]?
      | throw (.accessor (.indexOutOfRange index))
    let numerator ← liftAccessor (liftArith (mulChecked validator.effectiveBalance score))
    let denominator ← liftAccessor (liftArith (mulChecked config.INACTIVITY_SCORE_BIAS
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT))
    addDelta penalties index (← liftAccessor (liftArith (divChecked numerator denominator)))

/-- The penalties of each validator for inactivity.

Before Altair only a leak has them, and they fall on the eligible validators.

From Altair they fall on the eligible validators that missed the target, in a leak or not.

There are no rewards. -/
def getInactivityPenaltyDeltas (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  if altair : .altair ≤ fork then
    let matching ← liftAccessor (getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch state))
    let penalties ← (← getEligibleValidatorIndices state).foldlM
      (addInactivityScorePenalty config state altair (markIndices size matching))
      (Array.replicate size 0)
    return (Array.replicate size 0, penalties)
  else
    let leak ← isInInactivityLeak state
    if leak then
      let attestations ← getMatchingTargetAttestations state (Nat.lt_of_not_le altair)
        (getPreviousEpoch state)
      let attesters ← liftAccessor (getUnslashedAttestingIndices state attestations)
      let targetMatched := markIndices size attesters
      let total ← liftAccessor (getTotalActiveBalance state)
      let delay ← getFinalityDelay state
      let penalties ← (← getEligibleValidatorIndices state).foldlM
        (addInactivityPenalty state total delay targetMatched) (Array.replicate size 0)
      return (Array.replicate size 0, penalties)
    else return (Array.replicate size 0, Array.replicate size 0)

/-- From Altair: the reward and the penalty of one eligible validator for one flag.

A validator that set the flag earns nothing in a leak.

Otherwise it earns the weight of the flag in its base reward, scaled by the share that set it.

That share is the balance that set the flag over the active balance, both in whole increments.

A validator that did not set the flag pays the weight of the flag in its base reward.

The head flag has no penalty.

The leak is read only for a validator that set the flag. -/
def addFlagDelta (state : BeaconState preset fork)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) (participated : Array Bool)
    (totalActiveBalance participatingIncrements activeIncrements : Gwei)
    (deltas : Array Gwei × Array Gwei) (index : ValidatorIndex) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let (rewards, penalties) := deltas
  let weight := PARTICIPATION_FLAG_WEIGHTS[flagIndex]
  let base ← liftAccessor (getBaseReward state totalActiveBalance index)
  if participated.getD index.toNat false then
    if ← isInInactivityLeak state then return (rewards, penalties)
    else
      let numerator ← liftAccessor (liftArith do
        mulChecked (← mulChecked base weight) participatingIncrements)
      let denominator ← liftAccessor (liftArith (mulChecked activeIncrements WEIGHT_DENOMINATOR))
      let reward ← liftAccessor (liftArith (divChecked numerator denominator))
      return (← addDelta rewards index reward, penalties)
  else if flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX then return (rewards, penalties)
  else
    let scaled ← liftAccessor (liftArith (mulChecked base weight))
    return (rewards, ← addDelta penalties index (scaled / WEIGHT_DENOMINATOR))

/-- From Altair: the rewards and penalties of each validator for one participation flag.

The flag is the one that the votes of the previous epoch set. -/
def getFlagIndexDeltas (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  let participating ← liftAccessor (getUnslashedParticipatingIndices state altair
    flagIndex.val.toUInt64 (getPreviousEpoch state))
  let participatingBalance ← liftAccessor (getTotalBalance state participating)
  let total ← liftAccessor (getTotalActiveBalance state)
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT
  let zeros : Array Gwei := Array.replicate size 0
  (← getEligibleValidatorIndices state).foldlM
    (addFlagDelta state flagIndex (markIndices size participating) total
      (participatingBalance / increment) (total / increment)) (zeros, zeros)

/-- The sums of four lists of deltas, index by index, from left to right. -/
def sumDeltas (first second third fourth : Array Gwei) : Except TransitionError (Array Gwei) :=
  (Array.range first.size).mapM fun i => liftAccessor (liftArith do
    addChecked (← addChecked (← addChecked (first.getD i 0) (second.getD i 0)) (third.getD i 0))
      (fourth.getD i 0))

/-- Before Altair: the rewards and the penalties of each validator for the previous epoch. -/
def getAttestationDeltas (config : Config) (state : BeaconState preset fork)
    (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let (sourceRewards, sourcePenalties) ← getSourceDeltas state before
  let (targetRewards, targetPenalties) ← getTargetDeltas state before
  let (headRewards, headPenalties) ← getHeadDeltas state before
  let (inclusionRewards, _) ← getInclusionDelayDeltas state before
  let (_, inactivityPenalties) ← getInactivityPenaltyDeltas config state
  let rewards ← sumDeltas sourceRewards targetRewards headRewards inclusionRewards
  let penalties ← sumDeltas sourcePenalties targetPenalties headPenalties inactivityPenalties
  return (rewards, penalties)

/-- The state with the reward and then the penalty of one validator applied. -/
def applyDeltas (rewards penalties : Array Gwei) (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let state ← liftAccessor (increaseBalance state index.toUInt64 (rewards.getD index 0))
  liftAccessor (decreaseBalance state index.toUInt64 (penalties.getD index 0))

/-- The state with the rewards and then the penalties of some deltas applied, index by index. -/
def applyAllDeltas (state : BeaconState preset fork) (deltas : Array Gwei × Array Gwei) :
    Except TransitionError (BeaconState preset fork) :=
  (List.range state.validators.data.size).foldlM (applyDeltas deltas.1 deltas.2) state

/-- The state after the rewards and penalties of the previous epoch.

The first epoch changes nothing.

Before Altair the deltas of each kind of vote are summed, then applied once.

From Altair the deltas of each flag, then those of inactivity, are applied in turn. -/
def processRewardsAndPenalties (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if getCurrentEpoch state = GENESIS_EPOCH then pure state
  else if altair : .altair ≤ fork then do
    let flagDeltas ← (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
      (getFlagIndexDeltas state altair)
    let inactivityDeltas ← getInactivityPenaltyDeltas config state
    (flagDeltas ++ [inactivityDeltas]).foldlM applyAllDeltas state
  else do applyAllDeltas state (← getAttestationDeltas config state (Nat.lt_of_not_le altair))

end EthLib.Consensus

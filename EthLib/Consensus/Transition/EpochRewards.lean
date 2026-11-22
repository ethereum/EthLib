module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Transition.EpochJustification

/-!
# `Consensus.Transition.EpochRewards`

The rewards and penalties of the attesters of the previous epoch.

Each eligible validator gets a base reward, which shrinks as the active balance grows.

Before Altair, a matching source, target or head vote earns a share of it.

Any other vote costs all of it.

In a leak a matching vote earns all of it.

Each eligible validator then pays back four base rewards, less the proposer share.

A missed target also adds a penalty that grows with the delay of finality.

An attester also earns more the sooner its vote was included, and its includer earns a fixed share.

From Altair the state keeps participation flags instead of attestations.

Outside a leak, a flag earns its weight of the base reward, scaled by the balance that set it.

A validator that missed the source or the target pays its weight of the base reward.

A missed target also costs a penalty that grows with the inactivity score.

A 64-bit overflow or underflow is an error, and so is a division by zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The share of a base reward that goes to the proposer that includes the vote. -/
def proposerReward (preset : Preset) (baseReward : Gwei) : Gwei :=
  -- `floor(b / PROPOSER_REWARD_QUOTIENT)` of the base reward `b`.
  baseReward / preset.PROPOSER_REWARD_QUOTIENT

/-- The number of epochs since the finalized epoch, counted from the previous epoch. -/
def getFinalityDelay (state : BeaconState preset fork) : Except TransitionError Epoch :=
  -- The previous epoch minus the finalized epoch.
  liftAccessor (liftArith (subChecked (getPreviousEpoch state) state.finalizedCheckpoint.epoch))

/-- Whether the chain leaks: it has not finalized for more than a fixed number of epochs. -/
def isInInactivityLeak (state : BeaconState preset fork) : Except TransitionError Bool := do
  -- The finality delay exceeds `MIN_EPOCHS_TO_INACTIVITY_PENALTY`.
  return preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY < (← getFinalityDelay state)

/-- Whether a validator earns rewards and penalties for the previous epoch. -/
def isEligibleValidator (previousEpoch : Epoch) (validator : Validator) :
    Except TransitionError Bool :=
  -- A validator active in the previous epoch `p` is eligible.
  if isActiveValidator validator previousEpoch then pure true
  -- So is a slashed one with `p + 1` below its withdrawable epoch.
  else if validator.slashed then do
    return (← liftAccessor (liftArith (addChecked previousEpoch 1))) < validator.withdrawableEpoch
  else pure false

/-- The validators that earn rewards and penalties for the previous epoch, in increasing order.

An eligible validator at a position of `2^64` or more has no validator index, an overflow. -/
def getEligibleValidatorIndices (state : BeaconState preset fork) :
    Except TransitionError (List ValidatorIndex) :=
  -- The positions of the eligible validators in the registry, in increasing order.
  state.validators.data.toList.zipIdx.filterMapM fun (validator, position) => do
    if ← isEligibleValidator (getPreviousEpoch state) validator then
      return some (← liftAccessor (liftArith (ofNatChecked position)))
    else return none

/-- The deltas with an amount added at an index.

An index past the end is an error, and so is a 64-bit overflow. -/
def addDelta (deltas : Array Gwei) (index : ValidatorIndex) (amount : Gwei) :
    Except TransitionError (Array Gwei) :=
  -- The entry at the index grows by the amount.
  if inside : index.toNat < deltas.size then do
    let sum ← liftAccessor (liftArith (addChecked deltas[index.toNat] amount))
    return deltas.set index.toNat sum inside
  else throw (.accessor (.indexOutOfRange index))

/-- The reward and the penalty of one eligible validator for one kind of vote.

The leak is read only for a vote that matches. -/
def componentDelta (state : BeaconState preset fork) (matched : Bool)
    (base attestingBalance totalActiveBalance : Gwei) : Except TransitionError (Gwei × Gwei) :=
  if matched then do
    -- In a leak a matching vote earns the whole base reward `b`.
    let leak ← isInInactivityLeak state
    if leak then return (base, 0)
    else
      -- Else it earns `floor(b * floor(A / I) / floor(T / I))`.
      --
      -- `A` is the attesting balance, `T` the total active one, `I` the increment of balance.
      --
      -- Counting in increments keeps the product within 64 bits.
      let increment := preset.EFFECTIVE_BALANCE_INCREMENT
      let numerator ← liftAccessor (liftArith (mulChecked base (attestingBalance / increment)))
      return (numerator / (totalActiveBalance / increment), 0)
  -- A vote that does not match costs `b`.
  else pure (0, base)

/-- The rewards and penalties of each validator for one kind of vote.

The matching votes are those of some pending attestations. -/
def getAttestationComponentDeltas (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  let total ← liftAccessor (getTotalActiveBalance state)
  -- The unslashed signers of the attestations match, with their total balance `A`.
  let attesters ← liftAccessor (getUnslashedAttestingIndices state attestations)
  let attestingBalance ← liftAccessor (getTotalBalance state attesters)
  let matched := markIndices size attesters
  let zeros : Array Gwei := Array.replicate size 0
  -- Each eligible validator gets its reward or its penalty, from its base reward.
  (← getEligibleValidatorIndices state).foldlM (init := (zeros, zeros))
    fun (rewards, penalties) index => do
      let base ← liftAccessor (getBaseReward state total index)
      let (reward, penalty) ←
        componentDelta state (matched.getD index.toNat false) base attestingBalance total
      return (← addDelta rewards index reward, ← addDelta penalties index penalty)

/-- Before Altair: the rewards and penalties of each validator for its source vote. -/
def getSourceDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  -- The matching votes are the source votes of the previous epoch.
  getAttestationComponentDeltas state
    (← getMatchingSourceAttestations state before (getPreviousEpoch state))

/-- Before Altair: the rewards and penalties of each validator for its target vote. -/
def getTargetDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  -- The matching votes are the target votes of the previous epoch.
  getAttestationComponentDeltas state
    (← getMatchingTargetAttestations state before (getPreviousEpoch state))

/-- Before Altair: the rewards and penalties of each validator for its head vote. -/
def getHeadDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  -- The matching votes are the head votes of the previous epoch.
  getAttestationComponentDeltas state
    (← getMatchingHeadAttestations state before (getPreviousEpoch state))

/-- The first included attestation with the least inclusion delay, for each signer. -/
def earliestInclusions (size : Nat)
    (signed : Array (PendingAttestation preset × List ValidatorIndex)) :
    Array (Option (PendingAttestation preset)) :=
  -- An attestation replaces the one kept for a signer only with a strictly smaller delay.
  --
  -- So among equal delays the first in the list stays, as the rule requires.
  signed.foldl (init := Array.replicate size none) fun best (attestation, signers) =>
    signers.foldl (init := best) fun best index =>
      match best.getD index.toNat none with
      | some kept => if attestation.inclusionDelay < kept.inclusionDelay then
          best.setIfInBounds index.toNat (some attestation) else best
      | none => best.setIfInBounds index.toNat (some attestation)

/-- The part of an inclusion reward that goes to the attester, for some base reward and delay.

A zero delay is an error. -/
def inclusionAttesterReward (preset : Preset) (base : Gwei) (inclusionDelay : Slot) :
    Except TransitionError Gwei := do
  -- The base reward less the proposer share.
  let maxAttesterReward ← liftAccessor (liftArith (subChecked base (proposerReward preset base)))
  -- Divided by the inclusion delay `d`, rounded down; `d = 0` is a division by zero.
  ensure (inclusionDelay ≠ 0) .zeroInclusionDelay
  return maxAttesterReward / inclusionDelay

/-- The inclusion rewards of one attester, under the attestation that first included its vote.

A zero delay is an error. -/
def addInclusionReward (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (earliest : Array (Option (PendingAttestation preset))) (rewards : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) := do
  -- The attestation with the least inclusion delay among those the attester signed.
  let some attestation := earliest.getD index.toNat none
    | throw (.accessor (.indexOutOfRange index))
  let base ← liftAccessor (getBaseReward state totalActiveBalance index)
  -- The proposer that included it earns the proposer share of the base reward of the attester.
  let rewards ← addDelta rewards attestation.proposerIndex (proposerReward preset base)
  -- The attester earns the rest, divided by the inclusion delay.
  addDelta rewards index (← inclusionAttesterReward preset base attestation.inclusionDelay)

/-- Before Altair: the rewards of each validator for the inclusion of the previous epoch's votes.
-/
def getInclusionDelayDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  -- The source votes of the previous epoch, and the signers of each.
  let attestations ← getMatchingSourceAttestations state before (getPreviousEpoch state)
  let signers ← liftAccessor (attestations.toList.mapM (getPendingAttestingIndices state))
  -- The unslashed signers, as a set in increasing order of index.
  let attesters ← liftAccessor (unslashedAmong state signers)
  let total ← liftAccessor (getTotalActiveBalance state)
  -- The signers of each vote are read once, and one pass keeps the earliest inclusion of each.
  --
  -- The source looks the signers up again for each attester, with the same result.
  let earliest := earliestInclusions size (attestations.zip signers.toArray)
  -- Each of them earns its inclusion reward, and its includer the proposer share.
  let rewards ← attesters.foldlM (addInclusionReward state total earliest) (Array.replicate size 0)
  -- There are no penalties.
  return (rewards, Array.replicate size 0)

/-- The inactivity penalty of one eligible validator in a leak. -/
def addInactivityPenalty (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (finalityDelay : Epoch) (targetMatched : Array Bool) (penalties : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) := do
  -- It pays back `BASE_REWARDS_PER_EPOCH * b` less the proposer share: what optimal votes earn.
  let base ← liftAccessor (getBaseReward state totalActiveBalance index)
  let full ← liftAccessor (liftArith (mulChecked BASE_REWARDS_PER_EPOCH base))
  let paidBack ← liftAccessor (liftArith (subChecked full (proposerReward preset base)))
  let penalties ← addDelta penalties index paidBack
  if targetMatched.getD index.toNat false then pure penalties
  else do
    -- One that missed the target also pays `floor(e * delay / INACTIVITY_PENALTY_QUOTIENT)`.
    --
    -- Here `e` is its effective balance and the delay is the finality delay.
    let validator ← liftAccessor (getValidator state index)
    let scaled ← liftAccessor (liftArith (mulChecked validator.effectiveBalance finalityDelay))
    addDelta penalties index (scaled / (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT)

/-- From Altair: the inactivity penalty of one eligible validator that missed the target. -/
def addInactivityScorePenalty (config : Config) (state : BeaconState preset fork)
    (altair : .altair ≤ fork) (targetMatched : Array Bool) (penalties : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) :=
  -- A validator that hit the target pays nothing.
  if targetMatched.getD index.toNat false then pure penalties
  else do
    -- It pays `floor(e * s / (INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT))`.
    --
    -- Here `e` is its effective balance and `s` its inactivity score.
    let validator ← liftAccessor (getValidator state index)
    let some score := (state.inactivityScores altair).data[index.toNat]?
      | throw (.accessor (.indexOutOfRange index))
    let numerator ← liftAccessor (liftArith (mulChecked validator.effectiveBalance score))
    let denominator ← liftAccessor (liftArith (mulChecked config.INACTIVITY_SCORE_BIAS
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT))
    addDelta penalties index (← liftAccessor (liftArith (divChecked numerator denominator)))

/-- The penalties of each validator for inactivity.

There are no rewards. -/
def getInactivityPenaltyDeltas (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  -- From Altair they fall on the eligible validators that missed the target, in a leak or not.
  --
  -- The target is hit by the unslashed validators with the timely target flag.
  if altair : .altair ≤ fork then
    let matching ← liftAccessor (getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch state))
    let penalties ← (← getEligibleValidatorIndices state).foldlM
      (addInactivityScorePenalty config state altair (markIndices size matching))
      (Array.replicate size 0)
    return (Array.replicate size 0, penalties)
  else
    -- Before Altair only a leak has them, and they fall on every eligible validator.
    let leak ← isInInactivityLeak state
    if leak then
      -- The target is hit by the unslashed signers of the target votes of the previous epoch.
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

The leak is read only for a validator that set the flag. -/
def addFlagDelta (state : BeaconState preset fork)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) (participated : Array Bool)
    (totalActiveBalance participatingIncrements activeIncrements : Gwei)
    (deltas : Array Gwei × Array Gwei) (index : ValidatorIndex) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let (rewards, penalties) := deltas
  -- The weight `w` of the flag and the base reward `b` of the validator.
  let weight := PARTICIPATION_FLAG_WEIGHTS[flagIndex]
  let base ← liftAccessor (getBaseReward state totalActiveBalance index)
  if participated.getD index.toNat false then
    -- A validator that set the flag earns nothing in a leak.
    if ← isInInactivityLeak state then return (rewards, penalties)
    else
      -- Else it earns `floor(b * w * P / (N * WEIGHT_DENOMINATOR))`.
      --
      -- `P` and `N` count whole increments of the balance that set the flag and of the active one.
      let numerator ← liftAccessor (liftArith do
        mulChecked (← mulChecked base weight) participatingIncrements)
      let denominator ← liftAccessor (liftArith (mulChecked activeIncrements WEIGHT_DENOMINATOR))
      let reward ← liftAccessor (liftArith (divChecked numerator denominator))
      return (← addDelta rewards index reward, penalties)
  -- A validator that did not set the head flag pays nothing.
  else if flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX then return (rewards, penalties)
  -- One that did not set another flag pays `floor(b * w / WEIGHT_DENOMINATOR)`.
  else
    let scaled ← liftAccessor (liftArith (mulChecked base weight))
    return (rewards, ← addDelta penalties index (scaled / WEIGHT_DENOMINATOR))

/-- From Altair: the rewards and penalties of each validator for one participation flag.

The flag is the one that the votes of the previous epoch set. -/
def getFlagIndexDeltas (state : BeaconState preset fork) (altair : .altair ≤ fork)
    (flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  -- The unslashed validators with the flag set in the previous epoch, and their balance.
  let participating ← liftAccessor (getUnslashedParticipatingIndices state altair
    flagIndex.val.toUInt64 (getPreviousEpoch state))
  let participatingBalance ← liftAccessor (getTotalBalance state participating)
  let total ← liftAccessor (getTotalActiveBalance state)
  let increment := preset.EFFECTIVE_BALANCE_INCREMENT
  let zeros : Array Gwei := Array.replicate size 0
  -- Each eligible validator gets its reward or its penalty, with balances in whole increments.
  (← getEligibleValidatorIndices state).foldlM
    (addFlagDelta state flagIndex (markIndices size participating) total
      (participatingBalance / increment) (total / increment)) (zeros, zeros)

/-- The sums of four lists of deltas, index by index, from left to right. -/
def sumDeltas (first second third fourth : Array Gwei) : Except TransitionError (Array Gwei) :=
  -- Entry `i` is the sum of entry `i` of each list, and a 64-bit overflow is an error.
  (Array.range first.size).mapM fun i => liftAccessor (liftArith do
    addChecked (← addChecked (← addChecked (first.getD i 0) (second.getD i 0)) (third.getD i 0))
      (fourth.getD i 0))

/-- Before Altair: the rewards and the penalties of each validator for the previous epoch. -/
def getAttestationDeltas (config : Config) (state : BeaconState preset fork)
    (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  -- The deltas of the source, target and head votes, of inclusion and of inactivity.
  let (sourceRewards, sourcePenalties) ← getSourceDeltas state before
  let (targetRewards, targetPenalties) ← getTargetDeltas state before
  let (headRewards, headPenalties) ← getHeadDeltas state before
  let (inclusionRewards, _) ← getInclusionDelayDeltas state before
  let (_, inactivityPenalties) ← getInactivityPenaltyDeltas config state
  -- The rewards and the penalties are summed apart.
  --
  -- Inclusion has no penalty and inactivity no reward, so their zero lists are left out.
  let rewards ← sumDeltas sourceRewards targetRewards headRewards inclusionRewards
  let penalties ← sumDeltas sourcePenalties targetPenalties headPenalties inactivityPenalties
  return (rewards, penalties)

/-- The state with the reward and then the penalty of the validator at a position applied.

A position of `2^64` or more has no validator index, an overflow. -/
def applyDeltas (rewards penalties : Array Gwei) (state : BeaconState preset fork)
    (position : Nat) : Except TransitionError (BeaconState preset fork) := liftAccessor do
  let index ← liftArith (ofNatChecked position)
  -- The balance grows by the reward, then shrinks by the penalty, but not below 0.
  let state ← increaseBalance state index (rewards.getD position 0)
  decreaseBalance state index (penalties.getD position 0)

/-- The state with the rewards, then the penalties, of some deltas applied in order of position. -/
def applyAllDeltas (state : BeaconState preset fork) (deltas : Array Gwei × Array Gwei) :
    Except TransitionError (BeaconState preset fork) :=
  -- Each validator of the registry, by increasing index.
  (List.range state.validators.data.size).foldlM (applyDeltas deltas.1 deltas.2) state

/-- The state after the rewards and penalties of the previous epoch.

The genesis epoch changes nothing. -/
def processRewardsAndPenalties (config : Config) (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  -- The genesis epoch has no previous epoch to reward, and changes nothing.
  if getCurrentEpoch state = GENESIS_EPOCH then pure state
  -- From Altair the deltas of each flag, then those of inactivity, are applied in turn.
  else if altair : .altair ≤ fork then do
    let flagDeltas ← (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
      (getFlagIndexDeltas state altair)
    let inactivityDeltas ← getInactivityPenaltyDeltas config state
    (flagDeltas ++ [inactivityDeltas]).foldlM applyAllDeltas state
  -- Before Altair the deltas of each kind of vote are summed, then applied once.
  else do applyAllDeltas state (← getAttestationDeltas config state (Nat.lt_of_not_le altair))

end EthLib.Consensus

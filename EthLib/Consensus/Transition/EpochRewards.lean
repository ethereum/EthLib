module

public import EthLib.Consensus.Transition.EpochJustification

/-!
# `Consensus.Transition.EpochRewards`

The rewards and penalties of the attesters of the previous epoch, before Altair.

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

A 64-bit overflow or underflow is an error.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- The base reward of an effective balance, under a total active balance.

The square root of the total divides it, so the issuance grows with the square root of the stake.
-/
def baseReward (preset : Preset) (totalActiveBalance effectiveBalance : Gwei) :
    Except TransitionError Gwei := do
  let scaled ← liftAccessor (liftArith (mulChecked effectiveBalance preset.BASE_REWARD_FACTOR))
  return scaled / integerSquareroot totalActiveBalance / BASE_REWARDS_PER_EPOCH

/-- Before Altair: the base reward of a validator.

The caller reads the total active balance of the state once, and passes it for every validator. -/
def baseRewardOf (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (index : ValidatorIndex) : Except TransitionError Gwei := do
  baseReward preset totalActiveBalance (← liftAccessor (getValidator state index)).effectiveBalance

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
  match deltas[index.toNat]? with
  | some old => do
    return deltas.set! index.toNat (← liftAccessor (liftArith (addChecked old amount)))
  | none => throw (.accessor (.indexOutOfRange index))

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
      let base ← baseRewardOf state total index
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
          best.set! index.toNat (some attestation) else best
      | none => best.set! index.toNat (some attestation)

/-- The inclusion rewards of one attester, under the attestation that first included its vote.

The proposer of that block earns the proposer share of the base reward of the attester.

The attester earns the rest of its base reward, divided by the inclusion delay.

A zero delay is an error. -/
def addInclusionReward (state : BeaconState preset fork) (totalActiveBalance : Gwei)
    (earliest : Array (Option (PendingAttestation preset))) (rewards : Array Gwei)
    (index : ValidatorIndex) : Except TransitionError (Array Gwei) := do
  let some attestation := earliest.getD index.toNat none
    | throw (.accessor (.indexOutOfRange index))
  let base ← baseRewardOf state totalActiveBalance index
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
  let base ← baseRewardOf state totalActiveBalance index
  let full ← liftAccessor (liftArith (mulChecked BASE_REWARDS_PER_EPOCH base))
  let paidBack ← liftAccessor (liftArith (subChecked full (proposerReward preset base)))
  let penalties ← addDelta penalties index paidBack
  if targetMatched.getD index.toNat false then pure penalties
  else do
    let validator ← liftAccessor (getValidator state index)
    let scaled ← liftAccessor (liftArith (mulChecked validator.effectiveBalance finalityDelay))
    addDelta penalties index (scaled / (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT)

/-- Before Altair: the penalties of each validator for inactivity.

Only a leak has them, and they fall on the eligible validators. -/
def getInactivityPenaltyDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let size := state.validators.data.size
  let leak ← isInInactivityLeak state
  if leak then
    let attestations ← getMatchingTargetAttestations state before (getPreviousEpoch state)
    let attesters ← liftAccessor (getUnslashedAttestingIndices state attestations)
    let targetMatched := markIndices size attesters
    let total ← liftAccessor (getTotalActiveBalance state)
    let delay ← getFinalityDelay state
    let penalties ← (← getEligibleValidatorIndices state).foldlM
      (addInactivityPenalty state total delay targetMatched) (Array.replicate size 0)
    return (Array.replicate size 0, penalties)
  else return (Array.replicate size 0, Array.replicate size 0)

/-- The sums of four lists of deltas, index by index, from left to right. -/
def sumDeltas (first second third fourth : Array Gwei) : Except TransitionError (Array Gwei) :=
  (Array.range first.size).mapM fun i => liftAccessor (liftArith do
    addChecked (← addChecked (← addChecked (first.getD i 0) (second.getD i 0)) (third.getD i 0))
      (fourth.getD i 0))

/-- Before Altair: the rewards and the penalties of each validator for the previous epoch. -/
def getAttestationDeltas (state : BeaconState preset fork) (before : fork < .altair) :
    Except TransitionError (Array Gwei × Array Gwei) := do
  let (sourceRewards, sourcePenalties) ← getSourceDeltas state before
  let (targetRewards, targetPenalties) ← getTargetDeltas state before
  let (headRewards, headPenalties) ← getHeadDeltas state before
  let (inclusionRewards, _) ← getInclusionDelayDeltas state before
  let (_, inactivityPenalties) ← getInactivityPenaltyDeltas state before
  let rewards ← sumDeltas sourceRewards targetRewards headRewards inclusionRewards
  let penalties ← sumDeltas sourcePenalties targetPenalties headPenalties inactivityPenalties
  return (rewards, penalties)

/-- The state with the reward and then the penalty of one validator applied. -/
def applyDeltas (rewards penalties : Array Gwei) (state : BeaconState preset fork) (index : Nat) :
    Except TransitionError (BeaconState preset fork) := do
  let state ← liftAccessor (increaseBalance state index.toUInt64 (rewards.getD index 0))
  liftAccessor (decreaseBalance state index.toUInt64 (penalties.getD index 0))

/-- The state after the rewards and penalties of the previous epoch.

The first epoch changes nothing.

Altair counts participation flags instead, which EthLib does not yet have. -/
def processRewardsAndPenalties (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else if getCurrentEpoch state = GENESIS_EPOCH then pure state
  else do
    let (rewards, penalties) ← getAttestationDeltas state (Nat.lt_of_not_le altair)
    (List.range state.validators.data.size).foldlM (applyDeltas rewards penalties) state

end EthLib.Consensus

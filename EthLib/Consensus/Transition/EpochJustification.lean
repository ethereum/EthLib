module

public import EthLib.Consensus.Participation
public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.Transition.EpochJustification`

The first step of the epoch transition: justification and finalization of Casper FFG.

Before Altair, the votes of an epoch are the pending attestations of its blocks.

Justification follows [Gasper], §4.4, Definitions 4.5 and 4.6.

Finalization is the four-case rule of Gasper §8.5: `k`-finality of Definition 4.9, `k` 1 or 2.

The rule looks only one to three epochs back, through four bits of justification.

The first two epochs keep the checkpoints of the genesis.

[Gasper]: https://arxiv.org/abs/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Before Altair: the pending attestations of the current or the previous epoch.

Their source matches, since inclusion checked it.

Any other epoch is an error. -/
def getMatchingSourceAttestations (state : BeaconState preset fork) (before : fork < .altair)
    (epoch : Epoch) : Except TransitionError (Array (PendingAttestation preset)) := do
  -- The epoch is the previous or the current epoch.
  ensure (epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state)
    (.accessor (.epochNotRecent epoch (getPreviousEpoch state) (getCurrentEpoch state)))
  -- The pending attestations that the state keeps for that epoch.
  return if epoch = getCurrentEpoch state then (state.currentEpochAttestations before).data
    else (state.previousEpochAttestations before).data

/-- Before Altair: the pending attestations of an epoch whose target is its first block.

The root of that block is read only when some attestation needs it. -/
def getMatchingTargetAttestations (state : BeaconState preset fork) (before : fork < .altair)
    (epoch : Epoch) : Except TransitionError (Array (PendingAttestation preset)) := do
  let attestations ← getMatchingSourceAttestations state before epoch
  -- With no attestation the root is not read, so its errors cannot arise.
  if attestations.isEmpty then return #[]
  else
    -- Those whose target root is the block root at the first slot of the epoch.
    let root ← liftAccessor (getBlockRoot state epoch)
    return attestations.filter (·.data.target.root == root)

/-- Before Altair: the pending attestations of an epoch whose target is its first block.

Their head must also be the block of their slot. -/
def getMatchingHeadAttestations (state : BeaconState preset fork) (before : fork < .altair)
    (epoch : Epoch) : Except TransitionError (Array (PendingAttestation preset)) := do
  -- Those of the matching target whose head root is the root of the block at their slot.
  (← getMatchingTargetAttestations state before epoch).filterM fun attestation => do
    return attestation.data.beaconBlockRoot ==
      (← liftAccessor (getBlockRootAtSlot state attestation.data.slot))

/-- The members of the committee of a pending attestation whose bit is set.

A committee with more members than bits is an error. -/
def getPendingAttestingIndices (state : BeaconState preset fork)
    (attestation : PendingAttestation preset) : Except AccessorError (List ValidatorIndex) := do
  -- The committee of the slot and index of the data.
  let committee ← getBeaconCommittee state attestation.data.slot attestation.data.index
  -- Member `i` signed when bit `i` of the aggregation bits is set.
  committeeAttesters attestation.aggregationBits.bits 0 committee

/-- The unslashed validators among lists of signers.

They form a set, in increasing order. -/
def unslashedAmong (state : BeaconState preset fork) (signers : List (List ValidatorIndex)) :
    Except AccessorError (List ValidatorIndex) :=
  -- The union of the lists, without the slashed validators.
  (sortedSet signers.flatten).filterM fun index => do
    return !(← getValidator state index).slashed

/-- The unslashed validators that some of a list of pending attestations show as signers.

They form a set, in increasing order. -/
def getUnslashedAttestingIndices (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) :
    Except AccessorError (List ValidatorIndex) := do
  -- The union of the signers of each attestation, without the slashed validators.
  unslashedAmong state (← attestations.toList.mapM (getPendingAttestingIndices state))

/-- The total effective balance of the unslashed signers of some pending attestations.

It is at least one increment, so that no division by it is by zero. -/
def getAttestingBalance (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) : Except AccessorError Gwei := do
  -- The total balance of those signers, at least `EFFECTIVE_BALANCE_INCREMENT`.
  getTotalBalance state (← getUnslashedAttestingIndices state attestations)

/-- The checkpoint of an epoch and the root of its first block, if the epoch is justified.

Otherwise the checkpoint stays as it is, and no root is read. -/
def justifyCheckpoint (state : BeaconState preset fork) (justified : Bool) (epoch : Epoch)
    (checkpoint : Checkpoint) : Except TransitionError Checkpoint :=
  -- A justified epoch `e` gives the checkpoint of `e` and the block root at its first slot.
  if justified then do return ⟨epoch, ← liftAccessor (getBlockRoot state epoch)⟩
  else pure checkpoint

/-- Whether a finalization rule applies.

Its epochs must be justified, and its source a fixed number of epochs before the current one.

The sum is computed only when the epochs are justified, and a 64-bit overflow is an error. -/
def finalizes (justified : Bool) (source gap currentEpoch : Epoch) :
    Except TransitionError Bool :=
  -- The epochs are justified, and the source epoch plus the gap is the current epoch.
  if justified then do
    return (← liftAccessor (liftArith (addChecked source gap))) == currentEpoch
  else pure false

/-- The bits of justification moved one epoch back.

The newest bit is cleared, and the oldest one is dropped. -/
def shiftJustificationBits (bits : Bitvector JUSTIFICATION_BITS_LENGTH.toNat) :
    Vector Bool JUSTIFICATION_BITS_LENGTH.toNat :=
  -- Bit `i` takes bit `i - 1` for `i ≥ 1`, and bit 0 is 0.
  Vector.ofFn fun i => if h : i.val = 0 then false else bits.bits[i.val - 1]

/-- The state after the votes of the previous and the current epoch are weighed.

A 64-bit overflow is an error. -/
def weighJustificationAndFinalization (state : BeaconState preset fork)
    (totalActiveBalance previousTargetBalance currentTargetBalance : Gwei) :
    Except TransitionError (BeaconState preset fork) := do
  let previousEpoch := getPreviousEpoch state
  let currentEpoch := getCurrentEpoch state
  -- The justified checkpoints before the update.
  let oldPrevious := state.previousJustifiedCheckpoint
  let oldCurrent := state.currentJustifiedCheckpoint
  -- The previous epoch is justified when its target balance is at least 2/3 of the active one.
  --
  -- That is the supermajority link of Gasper, Definition 4.5, compared as `3 * target ≥ 2 * total`.
  --
  -- Gasper asks for more than 2/3, and this rule also justifies at exactly 2/3.
  let previousWeight ← liftAccessor (liftArith (mulChecked previousTargetBalance 3))
  let threshold ← liftAccessor (liftArith (mulChecked totalActiveBalance 2))
  let previousJustified := decide (threshold ≤ previousWeight)
  let justified ← justifyCheckpoint state previousJustified previousEpoch oldCurrent
  -- Then the current epoch, by the same test, which wins if both are justified.
  let currentWeight ← liftAccessor (liftArith (mulChecked currentTargetBalance 3))
  let currentJustified := decide (threshold ≤ currentWeight)
  let justified ← justifyCheckpoint state currentJustified currentEpoch justified
  -- The bits move one epoch back: bit `i` now stands for the `(i + 1)`-th latest epoch.
  let shifted := shiftJustificationBits state.justificationBits
  -- Bit 1 is set for a justified previous epoch, and bit 0 for a justified current epoch.
  let bits := (shifted.set 1 (previousJustified || shifted[1]) (by decide)).set 0 currentJustified
    (by decide)
  -- Gasper §8.5 names the epoch boundary blocks of the four latest epochs `B_1` to `B_4`.
  --
  -- `B_4` is that of the current epoch, so bits 3 to 0 stand for `B_1` to `B_4`.
  --
  -- Case 1: `B_1`, `B_2`, `B_3` justified, `B_3` with source `B_1`, finalizes `B_1` (`k = 2`).
  --
  -- The source is the old previous justified checkpoint, of epoch `e - 3`.
  let byOldPrevious3 ← finalizes (bits[1] && bits[2] && bits[3]) oldPrevious.epoch 3 currentEpoch
  -- Case 2: `B_2`, `B_3` justified, `B_3` with source `B_2`, finalizes `B_2` (`k = 1`).
  let byOldPrevious2 ← finalizes (bits[1] && bits[2]) oldPrevious.epoch 2 currentEpoch
  -- Case 3: `B_2`, `B_3`, `B_4` justified, `B_4` with source `B_2`, finalizes `B_2` (`k = 2`).
  --
  -- The source is now the old current justified checkpoint.
  let byOldCurrent2 ← finalizes (bits[0] && bits[1] && bits[2]) oldCurrent.epoch 2 currentEpoch
  -- Case 4: `B_3`, `B_4` justified, `B_4` with source `B_3`, finalizes `B_3` (`k = 1`).
  let byOldCurrent1 ← finalizes (bits[0] && bits[1]) oldCurrent.epoch 1 currentEpoch
  -- The rules apply in that order, so a rule on the old current checkpoint wins.
  let finalized :=
    if byOldCurrent2 || byOldCurrent1 then oldCurrent
    else if byOldPrevious3 || byOldPrevious2 then oldPrevious
    else state.finalizedCheckpoint
  -- The old current justified checkpoint becomes the previous one.
  return { state with
    previousJustifiedCheckpoint := oldCurrent, currentJustifiedCheckpoint := justified,
    justificationBits := ⟨bits⟩, finalizedCheckpoint := finalized }

/-- From Altair: the state after justification and finalization. -/
def processJustificationAndFinalizationAltair (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : Except TransitionError (BeaconState preset fork) :=
  -- The first two epochs change nothing.
  if getCurrentEpoch state ≤ GENESIS_EPOCH + 1 then pure state
  else do
    -- The target balances are those of the unslashed validators with the timely target flag.
    let previous ← liftAccessor (getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getPreviousEpoch state))
    let current ← liftAccessor (getUnslashedParticipatingIndices state altair
      TIMELY_TARGET_FLAG_INDEX (getCurrentEpoch state))
    let total ← liftAccessor (getTotalActiveBalance state)
    let previousBalance ← liftAccessor (getTotalBalance state previous)
    let currentBalance ← liftAccessor (getTotalBalance state current)
    weighJustificationAndFinalization state total previousBalance currentBalance

/-- The state after justification and finalization. -/
def processJustificationAndFinalization (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  -- From Altair the participation flags give the target balances.
  if altair : .altair ≤ fork then processJustificationAndFinalizationAltair state altair
  -- The first two epochs change nothing.
  else if getCurrentEpoch state ≤ GENESIS_EPOCH + 1 then pure state
  else do
    have before : fork < .altair := Nat.lt_of_not_le altair
    -- Before Altair, the target balances are those of the matching pending attestations.
    let previous ← getMatchingTargetAttestations state before (getPreviousEpoch state)
    let current ← getMatchingTargetAttestations state before (getCurrentEpoch state)
    let total ← liftAccessor (getTotalActiveBalance state)
    let previousBalance ← liftAccessor (getAttestingBalance state previous)
    let currentBalance ← liftAccessor (getAttestingBalance state current)
    weighJustificationAndFinalization state total previousBalance currentBalance

end EthLib.Consensus

module

public import EthLib.Consensus.Transition.Basic

/-!
# `Consensus.Transition.EpochJustification`

The first step of the epoch transition: justification and finalization of Casper FFG.

Before Altair, the votes of an epoch are the pending attestations of its blocks.

An epoch is justified when at least two thirds of the active balance vote for its first block.

A justified checkpoint is finalized when the epochs after it are justified too.

The last of those epochs must use it as source.

The rule looks only one to three epochs back, through four bits of justification.

The first two epochs keep the checkpoints of the genesis.
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
  ensure (epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state)
    (.accessor (.epochNotRecent epoch (getPreviousEpoch state) (getCurrentEpoch state)))
  return if epoch = getCurrentEpoch state then (state.currentEpochAttestations before).data
    else (state.previousEpochAttestations before).data

/-- Before Altair: the pending attestations of an epoch whose target is its first block.

The root of that block is read only when some attestation needs it. -/
def getMatchingTargetAttestations (state : BeaconState preset fork) (before : fork < .altair)
    (epoch : Epoch) : Except TransitionError (Array (PendingAttestation preset)) := do
  let attestations ← getMatchingSourceAttestations state before epoch
  if attestations.isEmpty then return #[]
  else
    let root ← liftAccessor (getBlockRoot state epoch)
    return attestations.filter (·.data.target.root == root)

/-- Before Altair: the pending attestations of an epoch whose target is its first block.

Their head must also be the block of their slot. -/
def getMatchingHeadAttestations (state : BeaconState preset fork) (before : fork < .altair)
    (epoch : Epoch) : Except TransitionError (Array (PendingAttestation preset)) := do
  (← getMatchingTargetAttestations state before epoch).filterM fun attestation => do
    return attestation.data.beaconBlockRoot ==
      (← liftAccessor (getBlockRootAtSlot state attestation.data.slot))

/-- The members of the committee of a pending attestation whose bit is set.

A committee with more members than bits is an error. -/
def getPendingAttestingIndices (state : BeaconState preset fork)
    (attestation : PendingAttestation preset) : Except AccessorError (List ValidatorIndex) := do
  let committee ← getBeaconCommittee state attestation.data.slot attestation.data.index
  committeeAttesters attestation.aggregationBits.bits 0 committee

/-- The unslashed validators among lists of signers.

They form a set, in increasing order. -/
def unslashedAmong (state : BeaconState preset fork) (signers : List (List ValidatorIndex)) :
    Except AccessorError (List ValidatorIndex) :=
  (sortedSet signers.flatten).filterM fun index => do
    return !(← getValidator state index).slashed

/-- The unslashed validators that some of a list of pending attestations show as signers.

They form a set, in increasing order. -/
def getUnslashedAttestingIndices (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) :
    Except AccessorError (List ValidatorIndex) := do
  unslashedAmong state (← attestations.toList.mapM (getPendingAttestingIndices state))

/-- The total effective balance of the unslashed signers of some pending attestations.

It is at least one increment, so that no division by it is by zero. -/
def getAttestingBalance (state : BeaconState preset fork)
    (attestations : Array (PendingAttestation preset)) : Except AccessorError Gwei := do
  getTotalBalance state (← getUnslashedAttestingIndices state attestations)

/-- The checkpoint of an epoch and the root of its first block, if the epoch is justified.

Otherwise the checkpoint stays as it is, and no root is read. -/
def justifyCheckpoint (state : BeaconState preset fork) (justified : Bool) (epoch : Epoch)
    (checkpoint : Checkpoint) : Except TransitionError Checkpoint :=
  if justified then do return ⟨epoch, ← liftAccessor (getBlockRoot state epoch)⟩
  else pure checkpoint

/-- Whether a finalization rule applies.

Its epochs must be justified, and its source a fixed number of epochs before the current one.

The sum is computed only when the epochs are justified, and a 64-bit overflow is an error. -/
def finalizes (justified : Bool) (source gap currentEpoch : Epoch) :
    Except TransitionError Bool :=
  if justified then do
    return (← liftAccessor (liftArith (addChecked source gap))) == currentEpoch
  else pure false

/-- The bits of justification moved one epoch back.

The newest bit is cleared, and the oldest one is dropped. -/
def shiftJustificationBits (bits : Bitvector JUSTIFICATION_BITS_LENGTH.toNat) :
    Vector Bool JUSTIFICATION_BITS_LENGTH.toNat :=
  Vector.ofFn fun i => if h : i.val = 0 then false else bits.bits[i.val - 1]

/-- The state after the votes of the previous and the current epoch are weighed.

The current justified checkpoint becomes the previous one, and the bits move one epoch back.

An epoch whose target balance, times three, reaches twice the active balance is justified.

The previous epoch is weighed first, then the current one, which wins if both are justified.

Then a rule may finalize the old previous justified checkpoint, three or two epochs back.

It needs the second to fourth, or the second and third, latest epochs justified.

A later rule may finalize the old current justified checkpoint, two or one epochs back.

It needs the first to third, or the first and second, latest epochs justified.

The later rule wins.

A 64-bit overflow is an error. -/
def weighJustificationAndFinalization (state : BeaconState preset fork)
    (totalActiveBalance previousTargetBalance currentTargetBalance : Gwei) :
    Except TransitionError (BeaconState preset fork) := do
  let previousEpoch := getPreviousEpoch state
  let currentEpoch := getCurrentEpoch state
  let oldPrevious := state.previousJustifiedCheckpoint
  let oldCurrent := state.currentJustifiedCheckpoint
  let previousWeight ← liftAccessor (liftArith (mulChecked previousTargetBalance 3))
  let threshold ← liftAccessor (liftArith (mulChecked totalActiveBalance 2))
  let previousJustified := decide (threshold ≤ previousWeight)
  let justified ← justifyCheckpoint state previousJustified previousEpoch oldCurrent
  let currentWeight ← liftAccessor (liftArith (mulChecked currentTargetBalance 3))
  let currentJustified := decide (threshold ≤ currentWeight)
  let justified ← justifyCheckpoint state currentJustified currentEpoch justified
  let shifted := shiftJustificationBits state.justificationBits
  let bits := (shifted.set 1 (previousJustified || shifted[1]) (by decide)).set 0 currentJustified
    (by decide)
  let byOldPrevious3 ← finalizes (bits[1] && bits[2] && bits[3]) oldPrevious.epoch 3 currentEpoch
  let byOldPrevious2 ← finalizes (bits[1] && bits[2]) oldPrevious.epoch 2 currentEpoch
  let byOldCurrent2 ← finalizes (bits[0] && bits[1] && bits[2]) oldCurrent.epoch 2 currentEpoch
  let byOldCurrent1 ← finalizes (bits[0] && bits[1]) oldCurrent.epoch 1 currentEpoch
  let finalized :=
    if byOldCurrent2 || byOldCurrent1 then oldCurrent
    else if byOldPrevious3 || byOldPrevious2 then oldPrevious
    else state.finalizedCheckpoint
  return { state with
    previousJustifiedCheckpoint := oldCurrent, currentJustifiedCheckpoint := justified,
    justificationBits := ⟨bits⟩, finalizedCheckpoint := finalized }

/-- The state after justification and finalization.

The first two epochs change nothing.

Before Altair, the target balances are those of the matching pending attestations.

Altair counts participation flags instead, which EthLib does not yet have. -/
def processJustificationAndFinalization (state : BeaconState preset fork) :
    Except TransitionError (BeaconState preset fork) :=
  if altair : .altair ≤ fork then throw (.accessor (.forkNotYetSpecified fork))
  else if getCurrentEpoch state ≤ GENESIS_EPOCH + 1 then pure state
  else do
    have before : fork < .altair := Nat.lt_of_not_le altair
    let previous ← getMatchingTargetAttestations state before (getPreviousEpoch state)
    let current ← getMatchingTargetAttestations state before (getCurrentEpoch state)
    let total ← liftAccessor (getTotalActiveBalance state)
    let previousBalance ← liftAccessor (getAttestingBalance state previous)
    let currentBalance ← liftAccessor (getAttestingBalance state current)
    weighJustificationAndFinalization state total previousBalance currentBalance

end EthLib.Consensus

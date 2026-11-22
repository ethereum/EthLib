module

public import EthLib.Consensus.ForkChoice.Handlers

/-!
# `Consensus.ForkChoice.ProposerHead`

The head on which a proposer builds: the head of the fork choice, or its parent.

A proposer may skip a late and weak head, and build on its parent instead.

Its own block then takes the boost and outweighs the late block.

Every condition must hold, so that the skip is safe and cheap:

- the head arrived after the attestations were due, and its slot is the one before;
- its parent is one slot before it, and holds more weight than a share of a committee;
- the head holds less weight than a smaller share, counting its equivocating voters;
- the head brings no better justification than its parent;
- finality is recent, and the proposer is early in its slot;
- before Fulu, the slot does not start an epoch, where the proposer shuffling could change.

A weak head of the previous slot, from a proposer that proposed twice in it, is also skipped.

From Gloas the parent keeps the payload status that the head builds on.

The late test reads the attestation deadline, and the strong test weighs the pending parent node.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- Whether the proposer shuffling of a slot is already fixed: the slot does not start an epoch. -/
def isShufflingStable (preset : Preset) (slot : Slot) : Except ForkChoiceError Bool :=
  if preset.SLOTS_PER_EPOCH = 0 then throw (.arith .divisionByZero)
  -- `s mod SLOTS_PER_EPOCH` is not 0, for the slot `s`.
  else return slot % preset.SLOTS_PER_EPOCH ≠ 0

/-- Whether the shuffling test lets a re-org happen at a slot.

From Fulu the proposers of an epoch are fixed one epoch ahead, so the test always passes. -/
def shufflingAllowsReorg (preset : Preset) (fork : Fork) (slot : Slot) :
    Except ForkChoiceError Bool :=
  -- From Fulu the test always passes, and before Fulu the slot does not start an epoch.
  if .fusaka ≤ fork then pure true else isShufflingStable preset slot

namespace Store

variable (config : Config) (store : Store preset fork)

/-- Whether a block arrived after the attestations of its slot were due. -/
def isHeadLate (headRoot : Root) : Except ForkChoiceError Bool :=
  -- The block is late when the store did not record it as timely.
  match store.blockTimeliness[headRoot]? with
  | some timely => return !timely
  | none => throw (.unknownBlockTimeliness headRoot)

/-- The unrealized justified checkpoint of a block, or an error when the store holds none. -/
def unrealizedJustification (root : Root) : Except ForkChoiceError Checkpoint :=
  match store.unrealizedJustifications[root]? with
  | some checkpoint => return checkpoint
  | none => throw (.unknownUnrealizedJustification root)

/-- Whether a head and its parent reach the same justified checkpoint at the end of the epoch. -/
def isFfgCompetitive (headRoot parentRoot : Root) : Except ForkChoiceError Bool := do
  -- The unrealized justified checkpoints of the head and of the parent are equal.
  return (← store.unrealizedJustification headRoot) == (← store.unrealizedJustification parentRoot)

/-- Whether the finalized epoch is at most a few epochs behind the epoch of a slot. -/
def isFinalizationOk (slot : Slot) : Except ForkChoiceError Bool := do
  -- Let `e` be the epoch of the slot and `f` the finalized epoch.
  --
  -- The test is `e - f ≤ REORG_MAX_EPOCHS_SINCE_FINALIZATION`, and `e < f` is an underflow.
  let epochsSinceFinalization ← (subChecked (computeEpochAtSlot preset slot)
    store.finalizedCheckpoint.epoch).mapError .arith
  return epochsSinceFinalization ≤ config.REORG_MAX_EPOCHS_SINCE_FINALIZATION

/-- Whether the clock of the store is before the cutoff of re-orgs in its slot. -/
def isProposingOnTime : Except ForkChoiceError Bool := do
  -- The time into the slot is at most the cutoff of re-orgs, both in milliseconds.
  return (← store.getTimeIntoSlotMs config) ≤
    (← (getProposerReorgCutoffMs config).mapError .arith)

/-- Whether the parent of a block holds more weight than a share of a committee.

The weight is that of the pending node of the parent, whatever its payload. -/
def isParentStrong (root : Root) : Except ForkChoiceError Bool := do
  -- The threshold is `REORG_PARENT_WEIGHT_THRESHOLD` percent of the weight of a committee.
  let justifiedState ← store.checkpointState store.justifiedCheckpoint
  let parentThreshold ←
    calculateCommitteeFraction justifiedState config.REORG_PARENT_WEIGHT_THRESHOLD
  let parentRoot := (← store.block root).parentRoot
  -- The weight of the pending node of the parent exceeds the threshold.
  let parentWeight ← store.getAttestationScore ⟨parentRoot, .pending⟩ justifiedState
  return parentThreshold < parentWeight

/-- Whether the proposer of a block proposed another known block in the same slot. -/
def isProposerEquivocation (root : Root) : Except ForkChoiceError Bool := do
  let block ← store.block root
  -- More than one known block has the proposer and the slot of the block.
  let matching := store.blocks.toList.filter fun (_, other) =>
    other.proposerIndex = block.proposerIndex ∧ other.slot = block.slot
  return 1 < matching.length

/-- The node on which a proposer of a slot builds: the head, or its parent.

The parent replaces a late and weak head, or a weak head whose proposer equivocated.

The parent node has the payload status that the head builds on: pending before Gloas.

The boost must have worn off the head. -/
def getProposerHead (headNode : ForkChoiceNode) (slot : Slot) :
    Except ForkChoiceError ForkChoiceNode := do
  let headBlock ← store.block headNode.root
  let parentRoot := headBlock.parentRoot
  let parentBlock ← store.block parentRoot
  -- The parent node keeps the payload status that the head builds on, pending before Gloas.
  let parentNode : ForkChoiceNode := ⟨parentRoot, parentPayloadStatus headBlock parentBlock⟩
  -- The head arrived after the attestations of its slot were due.
  let headLate ← store.isHeadLate headNode.root
  -- Before Fulu the slot does not start an epoch, where the proposer shuffling could change.
  --
  -- From Fulu this test passes.
  let shufflingStable ← shufflingAllowsReorg preset fork slot
  -- The head brings no better justification than its parent.
  let ffgCompetitive ← store.isFfgCompetitive headNode.root parentRoot
  -- Finality is recent, and the proposer is before the cutoff of its slot.
  let finalizationOk ← store.isFinalizationOk config slot
  let proposingOnTime ← store.isProposingOnTime config
  -- Let `h` be the slot of the head.
  --
  -- A single-slot re-org: the parent is at slot `h - 1` and the slot is `h + 1`.
  let parentSlotOk := (← (addChecked parentBlock.slot 1).mapError .arith) = headBlock.slot
  let currentTimeOk := (← (addChecked headBlock.slot 1).mapError .arith) = slot
  let singleSlotReorg := parentSlotOk ∧ currentTimeOk
  -- The boost has worn off the head.
  if store.proposerBoostRoot = headNode.root then throw (.boostNotWornOff headNode.root) else do
  -- The head is weak, with the equivocators of the committees of its slot counted for it.
  --
  -- The parent is strong.
  let headWeak ← store.isHeadWeak config headNode.root
  let parentStrong ← store.isParentStrong config headNode.root
  -- The proposer of the head proposed another block in its slot.
  let proposerEquivocation ← store.isProposerEquivocation headNode.root
  -- All the tests hold: the parent node.
  return if headLate ∧ shufflingStable ∧ ffgCompetitive ∧ finalizationOk ∧ proposingOnTime ∧
      singleSlotReorg ∧ headWeak ∧ parentStrong then parentNode
    -- Else a weak head of the previous slot from an equivocating proposer: the parent node.
    else if headWeak ∧ currentTimeOk ∧ proposerEquivocation then parentNode
    -- Else the head.
    else headNode

end Store

end EthLib.Consensus

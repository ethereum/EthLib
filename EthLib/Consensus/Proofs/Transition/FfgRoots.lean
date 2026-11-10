module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.FfgSlack
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Proofs: the justified roots of a chain come before the roots it records later

A state records the root of the latest block at each recent slot.

At two consecutive slots it records the same root, or a block and its child.

So the pairs of roots at consecutive slots order the roots by ancestry.

Each step of a chain keeps each justified checkpoint below the roots recorded from its epoch on.

The order is that of any map from roots to blocks that keeps each such pair in order.

The genesis checkpoints have the zero root, which comes before the root recorded at slot zero.

Justification then compares the block of each justified checkpoint with the block of a recent epoch.

Gasper §4.4, Definition 4.5, asks the source of a link to be an ancestor of its target.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {β : Type*} [Preorder β]
  {block : Root → β}

/-- The justified checkpoint of the current epoch, or else of the previous one. -/
def recentJustified {fork : Fork} (state : BeaconState preset fork) (current : Bool) :
    Checkpoint :=
  if current then state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint

/-- The pairs of roots that a state records at two consecutive slots.

The zero root also comes before the root that the state records at slot zero. -/
def rootLinks {fork : Fork} (state : BeaconState preset fork) : Set (Root × Root) :=
  {link | (∃ slot : Slot, getBlockRootAtSlot state slot = .ok link.1 ∧
      getBlockRootAtSlot state (slot + 1) = .ok link.2) ∨
    (link.1 = Vector.replicate 32 0 ∧ getBlockRootAtSlot state 0 = .ok link.2)}

/-- Each justified checkpoint of a state is below the roots that it records from its epoch on.

The order is that of the blocks of a map from roots.

The epoch of the checkpoint is at most its recent epoch.

Its first slot is below the slot of the state, unless it is the genesis checkpoint. -/
structure RootsAbove {fork : Fork} (block : Root → β) (state : BeaconState preset fork) :
    Prop where
  /-- The epoch of each justified checkpoint is at most its recent epoch. -/
  epoch : ∀ current : Bool, (recentJustified state current).epoch ≤
    (if current then getCurrentEpoch state else getPreviousEpoch state)
  /-- The first slot of each justified checkpoint is below the slot of the state.

  The genesis checkpoint, of epoch zero and of the zero root, is the exception. -/
  started : ∀ current : Bool,
    (recentJustified state current).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat ∨
      ((recentJustified state current).epoch = 0 ∧
        (recentJustified state current).root = Vector.replicate 32 0)
  /-- The block of each justified checkpoint is below that of each root recorded from its epoch. -/
  below : ∀ (current : Bool) (slot : Slot) (root : Root),
    (recentJustified state current).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat →
      getBlockRootAtSlot state slot = .ok root →
        block (recentJustified state current).root ≤ block root

/-- The block of each justified checkpoint is below the block of its recent epoch. -/
theorem RootsAbove.le_of_getBlockRoot {fork : Fork} {state : BeaconState preset fork}
    (holds : RootsAbove block state) (current : Bool) (root : Root)
    (read : getBlockRoot state
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok root) :
    block (if current then state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint).root ≤ block root := by
  sorry

/-- The genesis state built from deposits has each justified checkpoint below its later roots. -/
theorem RootsAbove.of_initializeBeaconStateFromEth1 {fork : Fork}
    {state : BeaconState preset fork} {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok state) :
    RootsAbove block state := by
  sorry

/-- One step of a chain keeps each justified checkpoint below the roots recorded from its epoch on.

The map from roots to blocks must keep in order the links of the state after the step.

An epoch must have at least one slot, and the buffer of roots must cover two epochs. -/
theorem RootsAbove.of_chainStep (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {forked after : ForkedBeaconState preset} (holds : RootsAbove block forked.state)
    (links : ∀ link ∈ rootLinks after.state, block link.1 ≤ block link.2)
    (step : ChainStep config checks forked after) :
    RootsAbove block after.state := by
  sorry

end EthLib.Consensus

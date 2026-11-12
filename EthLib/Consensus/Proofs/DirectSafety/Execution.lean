module

public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Transition.Genesis
public import Mathlib.Data.Finset.Basic

/-!
# Concrete executions for the direct safety statement

Blocks are the actual inputs of successful transitions, with result validation enabled.

No relation over all reachable paths stands in for the selected execution.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base Serialization.Ssz.SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The conditions on the preset that the direct safety proof uses.

An epoch has a slot, and the buffer of block roots covers four epochs.

There are more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes, to recompute committees.

The mainnet and minimal presets meet them. -/
structure Parameters (preset : Preset) : Prop where
  slots : 1 ≤ preset.SLOTS_PER_EPOCH.toNat
  roots : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat

/-- The header of a block, with the state root that the block supplies. -/
def blockHeader {fork : Fork} (block : BeaconBlock preset fork) : Option BeaconBlockHeader := do
  let bodyRoot ← (hashTreeRoot block.body).toOption
  pure ⟨block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, bodyRoot⟩

/-- The header of the block of a step, with its supplied state root; none for a slot. -/
def _root_.EthLib.Consensus.Step.headers {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : List BeaconBlockHeader :=
  match step with
  | .slot _ => []
  | .block _ signed _ _ => (blockHeader signed.message).toList

/-- The headers of the blocks of a run, in order. -/
def _root_.EthLib.Consensus.Run.headers {first last : ForkedBeaconState preset}
    (run : Run config checks first last) : List BeaconBlockHeader :=
  match run with
  | .nil => []
  | .snoc pre step => pre.headers ++ step.headers

/-- The headers of the blocks of a run up to the first slot of an epoch. -/
def _root_.EthLib.Consensus.Run.checkpointPath {first last : ForkedBeaconState preset}
    (run : Run config checks first last) (epoch : Epoch) : List BeaconBlockHeader :=
  run.headers.filter fun h => h.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat

/-- The headers of a run up to an epoch are those up to a later epoch, cut at the first one. -/
theorem _root_.EthLib.Consensus.Run.checkpointPath_restrict {g a : ForkedBeaconState preset}
    (run : Run config checks g a) (early late : Epoch) (ordered : early ≤ late) :
    run.checkpointPath early = (run.checkpointPath late).filter
      (fun h => h.slot.toNat ≤ early.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
  unfold Run.checkpointPath
  rw [List.filter_filter]
  congr 1
  funext h
  have bound := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat
    (UInt64.le_iff_toNat_le.mp ordered)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun small => ⟨small, Nat.le_trans small bound⟩, And.left⟩

/-- Two checkpoints conflict on two runs when the block headers of the runs differ.

The headers are compared up to the first slot of the earlier of the two epochs. -/
def Conflict {g a b : ForkedBeaconState preset} (left : Run config checks g a)
    (right : Run config checks g b) (f j : Checkpoint) : Prop :=
  left.checkpointPath (min f.epoch j.epoch) ≠ right.checkpointPath (min f.epoch j.epoch)

end EthLib.Consensus.DirectSafety

module

public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: a block keeps the slot of the state

No step of a block moves the slot of the state, at any fork.

A valid block runs on the state advanced to its slot, which is later than the slot before.

So the state after a valid block sits at the slot of the block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- No block moves the slot of the state that it runs on. -/
theorem processBlock_slot {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    after.slot = state.slot :=
  (frame_processBlock computed).slot

/-- A valid block runs on a state at an earlier slot, and leaves the state at its own slot. -/
theorem stateTransition_slot {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    state.slot < signed.message.slot ∧ after.slot = signed.message.slot := by
  obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok computed
  refine ⟨?_, (processBlock_slot blockOk).trans advancedSlot⟩
  unfold processSlots at slotsOk
  simp only [bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, later, _⟩ := slotsOk
  exact later

end EthLib.Consensus

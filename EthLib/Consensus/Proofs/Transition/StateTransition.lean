module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.StateTransition

/-!
# Proofs: the beacon state transition

The caching of a slot keeps the slot, and each slot step moves it on by exactly one.

Advancing to a slot fails when the slot is not after that of the state.

When it succeeds, the state ends exactly at that slot.

A valid block ran on the state at its slot.

When the result is validated, it carries its proposer's signature.

It then also commits to the root of the state after it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The caching of a slot succeeds only before Gloas, and keeps the slot. -/
theorem processSlot_slot (computed : processSlot state = .ok after) :
    fork < .glamsterdam ∧ after.slot = state.slot := by
  unfold processSlot at computed
  split at computed
  · cases computed
  rename_i gloas
  simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact ⟨Nat.lt_of_not_le gloas, rfl⟩

/-- One slot step moves the slot on by exactly one. -/
theorem advanceSlot_slot (computed : advanceSlot config state = .ok after) :
    after.slot.toNat = state.slot.toNat + 1 := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, _, _, _, _, rfl⟩ := computed
  exact sum

/-- Some count of slot steps moves the slot on by exactly that count. -/
theorem advanceSlots_slot :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config count state = .ok after → after.slot.toNat = state.slot.toNat + count
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    rw [computed]
    rfl
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    rw [advanceSlots_slot count rest, advanceSlot_slot first]
    omega

/-- Advancing to a slot that is not after the slot of the state fails. -/
theorem processSlots_of_le {slot : Slot} (notAfter : slot ≤ state.slot) :
    processSlots config state slot = .error (.slotNotAfter slot state.slot) := by
  have : ¬state.slot < slot := UInt64.not_lt.mpr notAfter
  simp [processSlots, ensure, this, bind, Except.bind]

/-- Advancing to a slot succeeds only when the slot is after that of the state.

The state then ends exactly at that slot. -/
theorem processSlots_slot {slot : Slot} (computed : processSlots config state slot = .ok after) :
    state.slot < slot ∧ after.slot = slot := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, later, advanced⟩ := computed
  refine ⟨later, UInt64.toNat_inj.mp ?_⟩
  rw [advanceSlots_slot _ advanced]
  have := UInt64.lt_iff_toNat_lt.mp later
  omega

/-- A valid signed block ran on the state advanced to its slot.

When the result is validated, the block carries its proposer's signature on that state.

Its state root is then the root of the state after it. -/
theorem stateTransition_ok {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    ∃ advanced, processSlots config state signed.message.slot = .ok advanced ∧
      advanced.slot = signed.message.slot ∧
      (validateResult = true → verifyBlockSignature config checks advanced signed = .ok true) ∧
      processBlock config checks engine advanced signed.message = .ok after ∧
      (validateResult = true → hashTreeRoot after = .ok signed.message.stateRoot) := by
  simp only [stateTransition, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨advanced, slotsOk, _, signatureOk, processed, blockOk, _, rootOk, rfl⟩ := computed
  refine ⟨advanced, slotsOk, (processSlots_slot slotsOk).2, fun validate => ?_, blockOk,
    fun validate => ?_⟩
  · simp only [checkBlockSignature, validate, ↓reduceIte, bind_ok_iff, ensure_ok_iff]
      at signatureOk
    obtain ⟨verified, verifiedOk, _, rfl, _⟩ := signatureOk
    exact verifiedOk
  · simp only [checkStateRoot, validate, ↓reduceIte, bind_ok_iff, ensure_ok_iff, liftSsz_ok]
      at rootOk
    obtain ⟨root, rootOk, same⟩ := rootOk
    rw [rootOk, same]

end EthLib.Consensus

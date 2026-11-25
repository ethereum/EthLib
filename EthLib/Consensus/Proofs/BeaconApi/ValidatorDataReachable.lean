module

public import EthLib.Consensus.Proofs.BeaconApi.ValidatorData
public import EthLib.Consensus.Proofs.ForkChoice.BlockStates
public import EthLib.Consensus.Proofs.ForkChoice.ForwardClock
import EthLib.Consensus.Proofs.ForkChoice.Ghost
import EthLib.Consensus.Proofs.HonestAggregation
import EthLib.Consensus.Proofs.Time

/-!
# Proofs: the attestation data answers on a reachable store

A store that the handlers build never answers the attestation data with code 500.

Nor does it answer the payload attestation data with code 500.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {config : Config}

namespace Store

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A store that the handlers build holds the state after its head block. -/
theorem Reachable.blockState_of_getHead
    (reachable : Reachable config anchorState anchorBlock store) {head : ForkChoiceNode}
    (found : store.getHead config = .ok head) :
    ∃ state, store.blockStates[head.root]? = some state := by
  obtain ⟨block, held⟩ := getHead_known found
  obtain ⟨state, stateHeld, -⟩ := reachable.blockStatesFromParents held
  exact ⟨state, stateHeld⟩

end Store

namespace BeaconApi

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- A forward store with a head never answers the attestation data with code 500.

That holds for every request.

It assumes the one step it does not prove: the empty slots from the state of the head. -/
theorem produceAttestationData_ne_internal_of_forwardReachable
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    -- A slot lasts a positive time.
    (positive : 0 < config.SLOT_DURATION_MS)
    -- An epoch has a slot, and at most as many as the recorded block roots.
    (epochPositive : 0 < preset.SLOTS_PER_EPOCH)
    (covered : preset.SLOTS_PER_EPOCH ≤ preset.SLOTS_PER_HISTORICAL_ROOT)
    -- Every slot that a clock reaches, plus the number of recorded block roots, fits in 64 bits.
    (room : (2 ^ 64 - 1) / config.SLOT_DURATION_MS.toNat +
      preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    {optimistic : OptimisticStore preset fork} {slot : Slot} {committeeIndex : CommitteeIndex}
    {head : ForkChoiceNode} (found : store.getHead config = .ok head)
    -- The empty slots from the state of the head up to the slot succeed, when there are any.
    (advances : ∀ headState, store.blockStates[head.root]? = some headState →
      headState.slot < slot → ∃ after, processSlots config .bls headState slot = .ok after) :
    ¬ ∃ error, produceAttestationData config store optimistic slot committeeIndex =
      .error error ∧ error.code = 500 := by
  intro refused
  -- The store holds the head block and its state, and has a current slot.
  obtain ⟨block, held⟩ := Store.getHead_known found
  obtain ⟨headState, stateHeld⟩ := forward.reachable.blockState_of_getHead found
  obtain ⟨current, currentOk⟩ := forward.exists_getCurrentSlot positive
  -- Each cause of code 500 contradicts one of these facts.
  rcases produceAttestationData_internal_iff.mp refused with ⟨fault, noHead⟩ | ⟨found', got, rest⟩
  · rw [found] at noHead
    cases noHead
  rw [found, Except.ok.injEq] at got
  subst got
  rcases rest with noBlock | noState | ⟨-, headState', -, held', -, rest⟩
  · simp [held] at noBlock
  · simp [stateHeld] at noState
  rw [stateHeld, Option.some.injEq] at held'
  subst held'
  rcases rest with ⟨fault, noSlot⟩ |
    ⟨current', currentOk', early, ⟨later, fault, stuck⟩ | ⟨state, atSlot, fault, noRoot⟩⟩
  · rw [currentOk] at noSlot
    cases noSlot
  -- The empty slots succeed by hypothesis.
  · obtain ⟨after, advanced⟩ := advances headState stateHeld later
    rw [advanced] at stuck
    cases stuck
  -- The slot is at most the current slot, which the clock bounds, so it leaves room for the roots.
  · have bounded := computeSlotAtTimeMs_le (mapError_ok_iff.mp currentOk')
    have notAfter := UInt64.le_iff_toNat_le.mp early
    -- The state at the slot sits at the slot, so the root of its target has a value.
    obtain ⟨root, rooted⟩ := getEpochBoundaryBlockRoot_ok (state := state)
      (headRoot := head.root) epochPositive covered
      (by rw [stateAtSlot_slot atSlot]; omega)
    rw [rooted] at noRoot
    cases noRoot

/-- A store with a head never answers the payload attestation data with code 500. -/
theorem producePayloadAttestationData_ne_internal_of_getHead {slot : Slot}
    {payloadPresent blobDataAvailable : Bool} {head : ForkChoiceNode}
    (found : store.getHead config = .ok head) :
    ¬ ∃ error, producePayloadAttestationData config store slot payloadPresent
      blobDataAvailable = .error error ∧ error.code = 500 := by
  rw [producePayloadAttestationData_internal_iff, found]
  simp

end BeaconApi

end EthLib.Consensus

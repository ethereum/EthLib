module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the slots keep the root of the latest block

Each slot step writes the root of the latest block header into the buffer of block roots.

It fills the state root of the header when that root is zero.

So it writes the root of the new header.

The epoch transition changes neither the buffer of block roots nor the latest block header.

So after the slots up to a later slot, the root at the slot before it is the root of the header.

The block handler uses this to show which parent a block it accepts names.

The block, and from Gloas its bid, names that root as its parent.

From Gloas the slots and the epoch transition also keep the latest block hash and the latest bid.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- One slot step runs the caching, then keeps the buffer of block roots and the latest header.

From Gloas it also keeps the latest block hash and the latest bid.

It moves to the next slot. -/
private theorem advanceSlot_cachedRoots
    (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, processSlot state = .ok cached ∧ after.blockRoots = cached.blockRoots ∧
      after.latestBlockHeader = cached.latestBlockHeader ∧
      after.latestBlockHash = cached.latestBlockHash ∧
      after.latestExecutionPayloadBid = cached.latestExecutionPayloadBid ∧
      after.slot.toNat = state.slot.toNat + 1 := by
  have sum := advanceSlot_slot computed
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, -, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  refine ⟨cached, cachedOk, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨_, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    obtain ⟨-, roots, header, hash, bid⟩ := processJustificationAndFinalization_keeps justifiedOk
    exact ⟨frame.blockRoots.trans roots, frame.latestBlockHeader.trans header,
      frame.latestBlockHash.trans hash, frame.latestExecutionPayloadBid.trans bid,
      sum⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, rfl, rfl, sum⟩

/-- After one slot, the root at the slot before the new one is that of the header. -/
private theorem advanceSlot_latestBlockRoot
    (computed : advanceSlot config checks state = .ok after) :
    ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
      readCircular after.blockRoots.elements (after.slot - 1) = .ok root := by
  obtain ⟨cached, cachedOk, roots, header, -, -, slot⟩ := advanceSlot_cachedRoots computed
  obtain ⟨root, hashed, written⟩ := processSlot_blockRoots cachedOk
  have previous : after.slot - 1 = state.slot := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), slot]
    simp
  rw [header, roots, previous]
  exact ⟨root, hashed, readCircular_writeCircular written⟩

/-- After one slot or more, the root at the slot before the last one is that of the header. -/
private theorem advanceSlots_latestBlockRoot :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks (count + 1) state = .ok after →
      ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
        readCircular after.blockRoots.elements (after.slot - 1) = .ok root
  | 0, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, first, rfl⟩ := computed
    exact advanceSlot_latestBlockRoot first
  | count + 1, _, _, computed => by
    rw [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, _, rest⟩ := computed
    exact advanceSlots_latestBlockRoot count rest

/-- After the slots up to a later slot, the root at the slot before it is that of the header.

That root is the root of the latest block header of the result. -/
theorem processSlots_latestBlockRoot {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
      readCircular after.blockRoots.elements (slot - 1) = .ok root := by
  obtain ⟨lt, reached⟩ := processSlots_slot computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advanced⟩ := computed
  have lt' := UInt64.lt_iff_toNat_lt.mp lt
  obtain ⟨count, counted⟩ : ∃ count, slot.toNat - state.slot.toNat = count + 1 :=
    ⟨slot.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  rw [← reached]
  exact advanceSlots_latestBlockRoot count advanced

/-- The slots keep the latest block hash and the latest bid, for any count. -/
private theorem advanceSlots_latestBid :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      after.latestBlockHash = state.latestBlockHash ∧
        after.latestExecutionPayloadBid = state.latestExecutionPayloadBid
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl⟩
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, first, rest⟩ := computed
    obtain ⟨_, cachedOk, -, -, hashKept, bidKept, -⟩ := advanceSlot_cachedRoots first
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    obtain ⟨hash, bid⟩ := advanceSlots_latestBid count rest
    exact ⟨hash.trans hashKept, bid.trans bidKept⟩

/-- The slots keep the latest block hash and the latest bid. -/
theorem processSlots_latestBid {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.latestBlockHash = state.latestBlockHash ∧
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact advanceSlots_latestBid _ advanced

end EthLib.Consensus

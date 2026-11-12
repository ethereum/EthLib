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

A root that is readable after one slot was readable before it, or is the root of the new header.

The new header is the one before it, with its state root filled by the root of the state before.

The block handler uses this to show which parent a block it accepts names.

The block, and from Gloas its bid, names that root as its parent.

From Gloas the slots and the epoch transition also keep the latest block hash and the latest bid.

The slots and the transition keep the genesis time.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- One slot step runs the caching, then keeps the buffer of block roots and the latest header.

It keeps the genesis time.

From Gloas it also keeps the latest block hash and the latest bid.

It moves to the next slot. -/
theorem advanceSlot_cachedRoots
    (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, processSlot state = .ok cached ∧ after.genesisTime = cached.genesisTime ∧
      after.blockRoots = cached.blockRoots ∧
      after.latestBlockHeader = cached.latestBlockHeader ∧
      after.latestBlockHash = cached.latestBlockHash ∧
      after.latestExecutionPayloadBid = cached.latestExecutionPayloadBid ∧
      after.slot.toNat = state.slot.toNat + 1 := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  refine ⟨cached, cachedOk, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨_, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    obtain ⟨genesis, roots, header, hash, bid, -⟩ :=
      processJustificationAndFinalization_keeps justifiedOk
    exact ⟨frame.genesisTime.trans genesis, frame.blockRoots.trans roots,
      frame.latestBlockHeader.trans header, frame.latestBlockHash.trans hash,
      frame.latestExecutionPayloadBid.trans bid, sum⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, rfl, rfl, rfl, sum⟩

/-- A slot below another, by less than the length of the buffer of roots, has another position. -/
private theorem slot_mod_ne {low high : Slot} (lt : low.toNat < high.toNat)
    (close : high.toNat - low.toNat < preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    high % preset.SLOTS_PER_HISTORICAL_ROOT ≠ low % preset.SLOTS_PER_HISTORICAL_ROOT := by
  intro same
  have same' := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
  exact Nat.mod_ne_of_sub_lt lt close same'

/-- One slot keeps the root recorded at a slot while that slot stays in the buffer of roots. -/
theorem getBlockRootAtSlot_advanceSlot {slot : Slot} {root : Root}
    (computed : advanceSlot config checks state = .ok after)
    (read : getBlockRootAtSlot state slot = .ok root)
    (recent : state.slot.toNat < slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRootAtSlot after slot = .ok root := by
  obtain ⟨cached, cachedOk, -, roots, -, -, -, afterSlot⟩ := advanceSlot_cachedRoots computed
  obtain ⟨_, -, written⟩ := processSlot_blockRoots cachedOk
  obtain ⟨before, readOk⟩ := getBlockRootAtSlot_read read
  have before' := UInt64.lt_iff_toNat_lt.mp before
  have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
      slot % preset.SLOTS_PER_HISTORICAL_ROOT := slot_mod_ne before' (by omega)
  unfold getBlockRootAtSlot at read
  simp only [before, ↓reduceIte, bind_ok_iff, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at read
  obtain ⟨bound, ⟨fits, boundEq⟩, -⟩ := read
  unfold getBlockRootAtSlot
  have later : slot < after.slot := UInt64.lt_iff_toNat_lt.mpr (by omega)
  simp only [later, ↓reduceIte, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
  refine ⟨bound, ⟨fits, boundEq⟩, ?_⟩
  have within : after.slot ≤ bound := UInt64.le_iff_toNat_le.mpr (by omega)
  simp only [within, ↓reduceIte, roots]
  rw [readCircular_writeCircular_of_ne written other]
  exact readOk

/-- After one slot, the latest block header is the one before, with its state root filled if zero.

The root that fills it is the root of the state before the slot. -/
theorem advanceSlot_latestBlockHeader (computed : advanceSlot config checks state = .ok after) :
    ∃ root, SszType.hashTreeRoot state = .ok root ∧
      after.latestBlockHeader =
        if state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
          { state.latestBlockHeader with stateRoot := root } else state.latestBlockHeader := by
  obtain ⟨cached, cachedOk, -, -, header, -⟩ := advanceSlot_cachedRoots computed
  rw [header]
  unfold processSlot at cachedOk
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at cachedOk
  obtain ⟨root, hashed, _, _, _, _, _, _, cachedOk⟩ := cachedOk
  refine ⟨root, hashed, ?_⟩
  split at cachedOk
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp cachedOk)
    rfl
  · cases cachedOk
    rfl

/-- A root that one slot makes readable was readable before, or is the root of the new header.

The root of the new header is at the slot of the state before the slot step. -/
theorem getBlockRootAtSlot_advanceSlot_cases {slot : Slot} {root : Root}
    (computed : advanceSlot config checks state = .ok after)
    (read : getBlockRootAtSlot after slot = .ok root) :
    (slot < state.slot ∧ getBlockRootAtSlot state slot = .ok root) ∨
      (slot = state.slot ∧ SszType.hashTreeRoot after.latestBlockHeader = .ok root) := by
  obtain ⟨cached, cachedOk, -, roots, header, -, -, afterSlot⟩ := advanceSlot_cachedRoots computed
  obtain ⟨lt, fits, recent, read⟩ := getBlockRootAtSlot_ok_iff.mp read
  obtain ⟨_, hashed, written⟩ := processSlot_blockRoots cachedOk
  rw [roots] at read
  by_cases same : slot = state.slot
  · subst same
    -- The slot step writes the root of the new header at the slot of the state.
    rw [readCircular_writeCircular written] at read
    cases read
    exact .inr ⟨rfl, by rw [header]; exact hashed⟩
  · -- Any other slot in the buffer keeps its root, as the write is at another position.
    have different : slot.toNat ≠ state.slot.toNat := fun eq => same (UInt64.toNat_inj.mp eq)
    have earlier : slot.toNat < state.slot.toNat := by omega
    have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
        slot % preset.SLOTS_PER_HISTORICAL_ROOT := slot_mod_ne earlier (by omega)
    rw [readCircular_writeCircular_of_ne written other] at read
    exact .inl ⟨UInt64.lt_iff_toNat_lt.mpr earlier,
      getBlockRootAtSlot_ok_iff.mpr ⟨earlier, fits, by omega, read⟩⟩

/-- One slot keeps the root of the block at the first slot of an epoch.

That slot must stay in the buffer of roots at the next slot. -/
theorem getBlockRoot_advanceSlot {epoch : Epoch} {root : Root}
    (computed : advanceSlot config checks state = .ok after)
    (read : getBlockRoot state epoch = .ok root)
    (recent : state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRoot after epoch = .ok root := by
  unfold getBlockRoot at read ⊢
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at read ⊢
  obtain ⟨start, startOk, read⟩ := read
  refine ⟨start, startOk, getBlockRootAtSlot_advanceSlot computed read ?_⟩
  rw [(mulChecked_ok_iff.mp startOk).2]
  exact recent

/-- A state one slot later with the same roots reads the same root of an epoch.

The first slot of the epoch must be before the slot of the earlier state and stay in the buffer. -/
theorem getBlockRoot_succ_iff {other : BeaconState preset fork}
    (roots : other.blockRoots = state.blockRoots) (slot : other.slot.toNat = state.slot.toNat + 1)
    {epoch : Epoch} {root : Root}
    (before : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < state.slot.toNat)
    (recent : state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRoot other epoch = .ok root ↔ getBlockRoot state epoch = .ok root := by
  rw [getBlockRoot_ok_iff, getBlockRoot_ok_iff]
  refine exists_congr fun start => and_congr_right fun startOk => ?_
  have startEq := (mulChecked_ok_iff.mp startOk).2
  rw [getBlockRootAtSlot_ok_iff, getBlockRootAtSlot_ok_iff, roots, slot]
  constructor
  · rintro ⟨-, fits, -, read⟩
    exact ⟨by omega, fits, by omega, read⟩
  · rintro ⟨-, fits, -, read⟩
    exact ⟨by omega, fits, by omega, read⟩

/-- The caching of a slot keeps the root recorded at a slot while that slot stays in the buffer.

It writes the entry of the current slot only. -/
theorem getBlockRootAtSlot_processSlot {cached : BeaconState preset fork} {slot : Slot}
    (computed : processSlot state = .ok cached)
    (recent : state.slot.toNat < slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRootAtSlot cached slot = getBlockRootAtSlot state slot := by
  obtain ⟨_, -, written⟩ := processSlot_blockRoots computed
  unfold getBlockRootAtSlot
  rw [processSlot_slot computed]
  by_cases lt : slot < state.slot
  · simp only [lt, ↓reduceIte]
    rcases sum : addChecked slot preset.SLOTS_PER_HISTORICAL_ROOT with _ | bound
    · rfl
    · by_cases within : state.slot ≤ bound
      · simp only [liftArith, Except.mapError, within, ↓reduceIte, bind, Except.bind]
        have lt' := UInt64.lt_iff_toNat_lt.mp lt
        exact readCircular_writeCircular_of_ne written (slot_mod_ne lt' (by omega))
      · simp only [liftArith, Except.mapError, within, ↓reduceIte, bind, Except.bind]
        rfl
  · simp only [lt, ↓reduceIte]
    rfl

/-- The caching of a slot keeps the root of the block at the first slot of an epoch.

That slot must stay in the buffer of roots. -/
theorem getBlockRoot_processSlot {cached : BeaconState preset fork} {epoch : Epoch}
    (computed : processSlot state = .ok cached)
    (recent : state.slot.toNat <
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRoot cached epoch = getBlockRoot state epoch := by
  unfold getBlockRoot
  rcases start : computeStartSlotAtEpoch preset epoch with _ | first
  · rfl
  · simp only [liftArith, Except.mapError, bind, Except.bind]
    refine getBlockRootAtSlot_processSlot computed ?_
    rw [(mulChecked_ok_iff.mp start).2]
    exact recent

/-- After one slot, the root at the slot before the new one is that of the header. -/
theorem advanceSlot_latestBlockRoot
    (computed : advanceSlot config checks state = .ok after) :
    ∃ root, SszType.hashTreeRoot after.latestBlockHeader = .ok root ∧
      readCircular after.blockRoots.elements (after.slot - 1) = .ok root := by
  obtain ⟨cached, cachedOk, -, roots, header, -, -, slot⟩ := advanceSlot_cachedRoots computed
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

/-- The slots keep the genesis time, the latest block hash and the latest bid, for any count. -/
private theorem advanceSlots_keeps :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      after.genesisTime = state.genesisTime ∧ after.latestBlockHash = state.latestBlockHash ∧
        after.latestExecutionPayloadBid = state.latestExecutionPayloadBid
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl⟩
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨_, first, rest⟩ := computed
    obtain ⟨_, cachedOk, genesisKept, -, -, hashKept, bidKept, -⟩ := advanceSlot_cachedRoots first
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    obtain ⟨genesis, hash, bid⟩ := advanceSlots_keeps count rest
    exact ⟨genesis.trans genesisKept, hash.trans hashKept, bid.trans bidKept⟩

/-- The slots keep the latest block hash and the latest bid. -/
theorem processSlots_latestBid {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.latestBlockHash = state.latestBlockHash ∧
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact (advanceSlots_keeps _ advanced).2

/-- The slots keep the genesis time. -/
theorem processSlots_genesisTime {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    after.genesisTime = state.genesisTime := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact (advanceSlots_keeps _ advanced).1

/-- The transition of a block keeps the genesis time. -/
theorem stateTransition_genesisTime {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    after.genesisTime = state.genesisTime := by
  obtain ⟨_, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  exact (frame_processBlock blockOk).genesisTime.trans (processSlots_genesisTime slotsOk)

end EthLib.Consensus

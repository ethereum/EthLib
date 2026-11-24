module

public import EthLib.Consensus.Proofs.ForkChoice.HeadTotality
public import EthLib.Consensus.Proofs.ForkChoice.HonestDuties
import EthLib.Consensus.Proofs.ForkChoice.BlockStates
import EthLib.Consensus.Proofs.ForkChoice.StoreEntries
import EthLib.Consensus.Proofs.Time

/-!
# Proofs: an honest proposal is timely and boosted

The duty of an honest proposer, and what a store records of a block of its current slot.

The network model is §2 of [arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config}

namespace Store

variable {store : Store preset fork}

/-- An update of the boost keeps a boost that a block already holds. -/
theorem updateProposerBoostRoot_of_ne_zero {head root : Root} {after : Store preset fork}
    (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (updated : store.updateProposerBoostRoot config head root = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  -- The block is not the first of its slot, so it does not take the boost.
  split at updated
  · rename_i taken
    exact absurd taken.2.1 boosted
  · simp only [pure, Except.pure, Except.ok.injEq] at updated
    subst updated
    rfl

/-- A new block keeps a boost that another block already holds. -/
theorem addBlock_proposerBoostRoot_of_ne_zero {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {blockRoot : Root} {after : Store preset fork}
    (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (added : store.addBlock config checks sources signed blockRoot = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨_, _, _, _, voted, vote, recorded, record, _, boost, added⟩ := added
  obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
  have kept := recordBlockTimeliness_boost record
  rw [computePulledUpTip_boost added, updateCheckpoints_boost,
    updateProposerBoostRoot_of_ne_zero (kept ▸ boosted) boost, kept]

/-- A block keeps a boost that another block already holds. -/
theorem onBlock_proposerBoostRoot_of_ne_zero {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    {after : Store preset fork} (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (added : store.onBlock config checks sources signed = .ok after) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e => simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      rfl
    simp only [onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    exact addBlock_proposerBoostRoot_of_ne_zero boosted added

/-- The dependent slot of the epoch of a slot is before that slot, when the slot is not 0. -/
private theorem dependentSlot_lt {slot dependent : Slot} (positive : 0 < slot)
    (computed : computeShufflingDependentSlot preset (computeEpochAtSlot preset slot) =
      .ok dependent) : dependent < slot := by
  simp only [computeShufflingDependentSlot, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨start, startOk, rfl⟩ := computed
  -- The lookahead starts at the first slot of an epoch no later than that of the slot.
  have le : start ≤ slot := by
    refine computeStartSlotAtEpoch_le_of_epoch_le startOk ?_
    simp only [Uint64.saturatingSub]
    split
    · rename_i lt
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
      omega
    · simp
  have le := UInt64.le_iff_toNat_le.mp le
  have positive := UInt64.lt_iff_toNat_lt.mp positive
  simp only [Uint64.saturatingSub]
  split
  · rename_i lt
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    simp only [UInt64.toNat_one] at *
    omega
  · exact UInt64.lt_iff_toNat_lt.mpr (by simpa using positive)

/-- A new timely block takes the boost when no block holds it and the block builds on the head.

It is timely when the clock is in its slot, before the attestations are due.

The store must hold its parent, at an earlier slot. -/
theorem addBlock_proposerBoostRoot {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} {blockRoot : Root} {after : Store preset fork}
    {head : ForkChoiceNode} {parent : BeaconBlock preset fork} {time due : UInt64}
    (unboosted : store.proposerBoostRoot = Vector.replicate 32 0)
    (current : store.getCurrentSlot config = .ok signed.message.slot)
    (into : store.getTimeIntoSlotMs config = .ok time)
    (dueOk : getAttestationDueMs config fork = .ok due) (early : time < due)
    (headOk : store.getHead config = .ok head) (onHead : head.root = signed.message.parentRoot)
    (parentFound : store.blocks[signed.message.parentRoot]? = some parent)
    (lower : parent.slot < signed.message.slot)
    (added : store.addBlock config checks sources signed blockRoot = .ok after) :
    after.proposerBoostRoot = blockRoot := by
  unfold addBlock at added
  simp only [bind_ok_iff] at added
  obtain ⟨_, _, read, readOk, voted, vote, recorded, record, boosted, boost, added⟩ := added
  rw [headOk, Except.ok.injEq] at readOk
  subst readOk
  rw [computePulledUpTip_boost added, updateCheckpoints_boost]
  obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
  -- The record finds the block timely, and keeps the boost, the blocks and the clock.
  obtain ⟨block, now, elapsed, limit, found, nowOk, elapsedOk, limitOk, timely⟩ :=
    recordBlockTimeliness_blockTimeliness record
  have kept := recordBlockTimeliness_boost record
  obtain ⟨-, blocks, -, clock, -⟩ := Store.recordBlockTimeliness_frame record
  simp only [getElem?_insert_root, ↓reduceIte, Option.some.injEq] at found
  subst found
  have sameNow : now = signed.message.slot := Except.ok.inj (nowOk.symm.trans current)
  have sameElapsed : elapsed = time := Except.ok.inj (elapsedOk.symm.trans into)
  have sameLimit : limit = due := Except.ok.inj (limitOk.symm.trans dueOk)
  subst sameNow sameElapsed sameLimit
  -- The update of the boost reads the epoch of the slot, and the two dependent roots.
  unfold updateProposerBoostRoot at boost
  rw [timely] at boost
  simp only [bind_ok_iff, pure_bind] at boost
  obtain ⟨epoch, epochOk, headRoot, headRootOk, blockDependent, blockDependentOk, boost⟩ := boost
  have epochEq : epoch = computeEpochAtSlot preset signed.message.slot := by
    rw [getCurrentStoreEpoch, (Store.SameClock.getCurrentSlot clock), nowOk] at epochOk
    exact (Except.ok.inj epochOk).symm
  subst epochEq
  -- Both roots are those of one walk, so the block takes the boost.
  have same : headRoot = blockDependent := by
    unfold getShufflingDependentRoot at headRootOk blockDependentOk
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at headRootOk blockDependentOk
    obtain ⟨dependent, dependentOk, headNode, headWalk, rfl⟩ := headRootOk
    obtain ⟨dependent', dependentOk', blockNode, blockWalk, rfl⟩ := blockDependentOk
    rw [dependentOk, Except.ok.injEq] at dependentOk'
    subst dependentOk'
    have before := dependentSlot_lt
      (UInt64.lt_of_le_of_lt (UInt64.zero_le (a := parent.slot)) lower)
      (mapError_ok_iff.mp dependentOk)
    rw [onHead] at headWalk
    by_cases loop : blockRoot = signed.message.parentRoot
    · rw [loop, headWalk, Except.ok.injEq] at blockWalk
      rw [blockWalk]
    · have step := getAncestor_step (store := recorded) (node := ⟨blockRoot, .pending⟩)
        (slot := dependent)
        (by rw [blocks]; simp)
        (UInt64.not_le.mpr before)
        (by rw [blocks, getElem?_insert_root]; simp [loop, parentFound])
        lower
      have roots := getAncestor_root (store := recorded)
        ⟨signed.message.parentRoot, parentPayloadStatus signed.message parent⟩ .pending dependent
      rw [← step, blockWalk, headWalk] at roots
      simpa using roots.symm
  simp only [unboosted, kept, same, early, decide_true, and_self, ↓reduceIte, pure,
    Except.pure, Except.ok.injEq] at boost
  rw [← boost]

/-- No held block builds on a held block of the current slot, in a store with a forward clock.

Each held block is at or before the current slot, and each child is after its parent. -/
theorem ForwardReachable.not_parentRoot_of_current {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (forward : ForwardReachable config anchorState anchorBlock store)
    (positive : 0 < config.SLOT_DURATION_MS) (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (lower : store.ParentsBelow) {root : Root} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (current : store.getCurrentSlot config = .ok block.slot) :
    ∀ (child : Root) (other : BeaconBlock preset fork), store.blocks[child]? = some other →
      other.parentRoot ≠ root := by
  intro child other childFound builds
  obtain ⟨now, nowOk, blocksLe, -⟩ := forward.slots_le_current positive anchorSlot
  rw [current, Except.ok.injEq] at nowOk
  subst nowOk
  -- A child sits after its parent, so after the current slot.
  have below := lower child other block childFound (builds ▸ found)
  exact absurd (blocksLe child other childFound) (UInt64.not_le.mpr below)

end Store

namespace Models.Network

variable (config) {checks : SignatureChecks} {sources : BlockSources preset fork}
  {time : ℕ} {view : Set (Message preset fork)} {store after : Store preset fork}

/-- A move of the store keeps the timeliness of each block that the store holds. -/
theorem Handles.blockTimeliness_of_contains
    (handles : Handles config checks sources time view store after) {root : Root}
    (held : store.blocks.contains root) :
    after.blockTimeliness[root]? = store.blockTimeliness[root]? := by
  cases handles with
  | tick _ _ step => rw [Store.onTick_blockTimeliness step]
  | block _ step => exact Store.onBlock_blockTimeliness_of_contains step held
  | blockAttestation _ _ _ _ step => rw [Store.onAttestation_blockTimeliness step]
  | blockAttesterSlashing _ _ _ _ step => rw [Store.onAttesterSlashing_blockTimeliness step]
  | attestation _ step => rw [Store.onAttestation_blockTimeliness step]
  | attesterSlashing _ step => rw [Store.onAttesterSlashing_blockTimeliness step]
  | payloadAttestation _ step => rw [Store.onPayloadAttestationMessage_blockTimeliness step]
  | envelope _ step => rw [Store.onExecutionPayloadEnvelope_blockTimeliness step]
  | inclusionList _ step => rw [Store.onInclusionList_blockTimeliness step]

variable {config}

/-- A move of the store keeps its time of genesis, and never sets its clock back. -/
private theorem Handles.clock (handles : Handles config checks sources time view store after) :
    after.genesisTimeMs = store.genesisTimeMs ∧ store.timeMs ≤ after.timeMs ∧
      ∀ slot, store.getCurrentSlot config = .ok slot →
        ∃ later, after.getCurrentSlot config = .ok later ∧ slot ≤ later := by
  have same (clock : Store.SameClock store after) :
      after.genesisTimeMs = store.genesisTimeMs ∧ store.timeMs ≤ after.timeMs ∧
        ∀ slot, store.getCurrentSlot config = .ok slot →
          ∃ later, after.getCurrentSlot config = .ok later ∧ slot ≤ later := by
    refine ⟨clock.2, clock.1 ▸ UInt64.le_refl _, fun slot slotOk => ⟨slot, ?_, UInt64.le_refl _⟩⟩
    rw [clock.getCurrentSlot, slotOk]
  cases handles with
  | tick le fits step =>
    have forward : store.timeMs ≤ time.toUInt64 := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' fits]
      exact le
    refine ⟨?_, (Store.onTick_frame step).1 ▸ forward, fun slot slotOk =>
      Store.exists_getCurrentSlot_onTick_ge forward step slotOk⟩
    unfold Store.onTick at step
    simp only [bind_ok_iff] at step
    obtain ⟨_, _, _, caught, ticked⟩ := step
    exact (Store.onTickPerSlot_frame ticked).2.1.trans (Store.catchUp_frame caught).1
  | block _ step => exact same (Store.onBlock_sameClock step)
  | blockAttestation _ _ _ _ step => exact same (Store.onAttestation_sameClock step)
  | blockAttesterSlashing _ _ _ _ step => exact same (Store.onAttesterSlashing_sameClock step)
  | attestation _ step => exact same (Store.onAttestation_sameClock step)
  | attesterSlashing _ step => exact same (Store.onAttesterSlashing_sameClock step)
  | payloadAttestation _ step => exact same (Store.onPayloadAttestationMessage_sameClock step)
  | envelope _ step => exact same (Store.onExecutionPayloadEnvelope_sameClock step)
  | inclusionList _ step => exact same (Store.onInclusionList_sameClock step)

/-- A move of the store that keeps it in one slot keeps a boost that a block holds. -/
theorem Handles.proposerBoostRoot_of_ne_zero
    (handles : Handles config checks sources time view store after) {slot : Slot}
    (boosted : store.proposerBoostRoot ≠ Vector.replicate 32 0)
    (current : store.getCurrentSlot config = .ok slot)
    (stays : after.getCurrentSlot config = .ok slot) :
    after.proposerBoostRoot = store.proposerBoostRoot := by
  cases handles with
  | tick _ _ step =>
    -- A tick inside the slot only sets the time.
    have slotted : computeSlotAtTimeMs config store.genesisTimeMs time.toUInt64 = .ok slot := by
      rw [Store.getCurrentSlot_onTick step] at stays
      cases computed : computeSlotAtTimeMs config store.genesisTimeMs time.toUInt64 with
      | error e => simp [computed, Except.mapError] at stays
      | ok s => simpa [computed, Except.mapError] using stays
    rw [onTick_sameSlot current slotted, Except.ok.injEq] at step
    rw [← step]
  | block _ step => exact Store.onBlock_proposerBoostRoot_of_ne_zero boosted step
  | blockAttestation _ _ _ _ step => exact Store.onAttestation_boost step
  | blockAttesterSlashing _ _ _ _ step => exact Store.onAttesterSlashing_boost step
  | attestation _ step => exact Store.onAttestation_boost step
  | attesterSlashing _ step => exact Store.onAttesterSlashing_boost step
  | payloadAttestation _ step =>
    obtain ⟨_, _, rfl⟩ := Store.onPayloadAttestationMessage_onlyPtcVotes step
    rfl
  | envelope _ step =>
    obtain ⟨_, _, _, _, _, record, rfl⟩ := Store.onExecutionPayloadEnvelope_ok step
    obtain ⟨_, rfl⟩ := Store.recordEnvelope_frame record
    rfl
  | inclusionList _ step =>
    obtain ⟨_, _, rfl⟩ := Store.onInclusionList_ok ‹_› step
    rfl

/-- A move of the store keeps its blocks, or is a block that the block handler accepts. -/
private theorem Handles.blocks_or_onBlock
    (handles : Handles config checks sources time view store after) :
    after.blocks = store.blocks ∨
      ∃ signed, store.onBlock config checks sources signed = .ok after := by
  cases handles with
  | tick _ _ step => exact .inl (Store.onTick_frame step).2.2.1
  | block _ step => exact .inr ⟨_, step⟩
  | blockAttestation _ _ _ _ step => exact .inl (Store.onAttestation_frame step).2.1
  | blockAttesterSlashing _ _ _ _ step => exact .inl (Store.onAttesterSlashing_frame step).2.1
  | attestation _ step => exact .inl (Store.onAttestation_frame step).2.1
  | attesterSlashing _ step => exact .inl (Store.onAttesterSlashing_frame step).2.1
  | payloadAttestation _ step =>
    exact .inl (Store.onPayloadAttestationMessage_onlyPtcVotes step).frame.2.1
  | envelope _ step => exact .inl (Store.onExecutionPayloadEnvelope_frame step).2.1
  | inclusionList _ step => exact .inl (Store.onInclusionList_frame step).2.1

/-- A move of the store keeps each block that the store holds. -/
private theorem Handles.blocks_of_found
    (handles : Handles config checks sources time view store after) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    after.blocks[root]? = some block := by
  rcases handles.blocks_or_onBlock with same | ⟨_, step⟩
  · rw [same]
    exact found
  · exact Store.onBlock_blocks_of_found step found

/-- Of two clocks with one time of genesis in one slot, the later one is further into the slot. -/
private theorem getTimeIntoSlotMs_le {later : Store preset fork} {slot : Slot}
    {elapsed elapsedLater : UInt64} (genesis : later.genesisTimeMs = store.genesisTimeMs)
    (forward : store.timeMs ≤ later.timeMs) (current : store.getCurrentSlot config = .ok slot)
    (stays : later.getCurrentSlot config = .ok slot)
    (into : store.getTimeIntoSlotMs config = .ok elapsed)
    (intoLater : later.getTimeIntoSlotMs config = .ok elapsedLater) : elapsed ≤ elapsedLater := by
  unfold Store.getTimeIntoSlotMs at into intoLater
  rw [current] at into
  rw [stays, genesis] at intoLater
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, mapError_ok_iff] at into intoLater
  obtain ⟨_, rfl, start, startOk, rfl⟩ := into
  obtain ⟨_, rfl, start', startOk', rfl⟩ := intoLater
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  -- The slot starts by the earlier clock.
  have read := mapError_ok_iff.mp current
  obtain ⟨start', startOk', began⟩ := slotStart_le_of_slotAtTime read (UInt64.le_refl slot)
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  have forward := UInt64.le_iff_toNat_le.mp forward
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr began),
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
  omega

/-- Two stores with one clock are equally far into their slot. -/
private theorem getTimeIntoSlotMs_of_sameClock (clock : Store.SameClock store after) :
    after.getTimeIntoSlotMs config = store.getTimeIntoSlotMs config := by
  unfold Store.getTimeIntoSlotMs
  rw [clock.getCurrentSlot, clock.1, clock.2]

variable {ν κ : Type*} [DecidableEq ν] {signed : Message preset fork → Set (ν × κ)}
  {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
  {J : Set ν}

/-- What a store has recorded of each block that it did not hold at the start.

The block is at or before the current slot.

The block is timely when the clock is still in its slot, before the attestations are due. -/
private def RecordsTimely (initial store : Store preset fork) : Prop :=
  ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
    initial.blocks[root]? = none →
    (∃ current, store.getCurrentSlot config = .ok current ∧ block.slot ≤ current) ∧
    ∀ time due, store.getCurrentSlot config = .ok block.slot →
      store.getTimeIntoSlotMs config = .ok time → getAttestationDueMs config fork = .ok due →
      time < due → store.blockTimeliness[root]? = some true

/-- A move keeps the record of timely blocks. -/
private theorem Handles.recordsTimely {initial : Store preset fork}
    (handles : Handles config checks sources time view store after)
    (records : RecordsTimely (config := config) initial store) :
    RecordsTimely (config := config) initial after := by
  intro root block held fresh
  obtain ⟨genesis, forward, slots⟩ := handles.clock
  by_cases old : store.blocks.contains root
  · -- The store held the block, which stays, so its record carries over.
    obtain ⟨heldBefore, foundBefore⟩ := Option.isSome_iff_exists.mp
      (Std.TreeMap.contains_eq_isSome_getElem?.symm.trans old)
    have keep := handles.blocks_of_found foundBefore
    rw [keep, Option.some.injEq] at held
    subst held
    obtain ⟨⟨current, currentOk, inSlot⟩, timely⟩ := records root heldBefore foundBefore fresh
    obtain ⟨later, laterOk, grows⟩ := slots current currentOk
    refine ⟨⟨later, laterOk, UInt64.le_trans inSlot grows⟩, fun elapsed due stays into dueOk
      early => ?_⟩
    rw [laterOk, Except.ok.injEq] at stays
    subst stays
    -- The earlier clock was in the slot of the block too, and less far into it.
    have same : current = heldBefore.slot := UInt64.le_antisymm grows inSlot
    subst same
    obtain ⟨start, startOk⟩ : ∃ start,
        computeTimeAtSlotMs config store.genesisTimeMs heldBefore.slot = .ok start := by
      unfold Store.getTimeIntoSlotMs at into
      rw [laterOk, genesis] at into
      simp only [bind_ok_iff, mapError_ok_iff] at into
      obtain ⟨_, same, start, startOk, -⟩ := into
      obtain rfl := Except.ok.inj same
      exact ⟨start, startOk⟩
    have intoBefore : store.getTimeIntoSlotMs config = .ok (store.timeMs - start) := by
      simp [Store.getTimeIntoSlotMs, currentOk, startOk, Except.mapError, bind, Except.bind,
        pure, Except.pure]
    have le := getTimeIntoSlotMs_le genesis forward currentOk laterOk intoBefore into
    rw [handles.blockTimeliness_of_contains config old]
    exact timely _ due currentOk intoBefore dueOk (UInt64.lt_of_le_of_lt le early)
  · -- The move took the block: it is a block that its handler adds with the clock of the store.
    rcases handles.blocks_or_onBlock with same | ⟨_, step⟩
    · rw [same] at held
      exact absurd (Std.TreeMap.contains_eq_isSome_getElem?.trans (by simp [held])) old
    rcases Store.onBlock_same_or_insert step with same | ⟨blockRoot, hashed, new, blocks, -⟩
    · subst same
      exact absurd (Std.TreeMap.contains_eq_isSome_getElem?.trans (by simp [held])) old
    rw [blocks, getElem?_insert_root] at held
    split at held
    · rename_i same
      subst same
      rw [Option.some.injEq] at held
      subst held
      have fresh' : ¬ store.blocks.contains blockRoot := by simpa using new
      have clock := Store.onBlock_sameClock step
      obtain ⟨current, currentOk, notFuture⟩ := (Store.onBlock_checks hashed fresh' step).1
      refine ⟨⟨current, clock.getCurrentSlot ▸ currentOk, notFuture⟩,
        fun elapsed due stays into dueOk early => ?_⟩
      simp only [Store.onBlock, hashed, fresh', bind, Except.bind, Except.mapError, ↓reduceIte,
        Bool.false_eq_true] at step
      obtain ⟨now, elapsed', due', nowOk, elapsedOk, dueOk', timely⟩ :=
        Store.addBlock_blockTimeliness step
      rw [clock.getCurrentSlot, nowOk, Except.ok.injEq] at stays
      rw [getTimeIntoSlotMs_of_sameClock clock, elapsedOk, Except.ok.injEq] at into
      rw [dueOk', Except.ok.injEq] at dueOk
      subst stays into dueOk
      rw [timely]
      simp [early]
    · exact absurd (Std.TreeMap.contains_eq_isSome_getElem?.trans (by simp [held])) old

/-- A store records as timely each held block of the slot of its clock, before the deadline.

The deadline is the time into the slot at which the attestations are due.

The store must not hold the block at the start of the execution. -/
theorem Execution.blockTimeliness_eq_true
    (e : Execution (forkChoice config checks sources signed sends) J) {u : ν} {n : ℕ}
    {root : Root} {block : BeaconBlock preset fork} {elapsed due : UInt64}
    (fresh : (e.start u).blocks[root]? = none)
    (held : ((e.world n).state u).blocks[root]? = some block)
    (current : ((e.world n).state u).getCurrentSlot config = .ok block.slot)
    (into : ((e.world n).state u).getTimeIntoSlotMs config = .ok elapsed)
    (dueOk : getAttestationDueMs config fork = .ok due) (early : elapsed < due) :
    ((e.world n).state u).blockTimeliness[root]? = some true := by
  -- The block entered the store at an earlier event, since the store did not hold it at the start.
  --
  -- No handler accepts a block from a later slot, so the clock was then in the slot of the block.
  --
  -- The clock never goes back, so the deadline had not passed then either.
  --
  -- Every move keeps that record, and the start holds no block that it speaks of.
  have records : ∀ n, RecordsTimely (config := config) (e.start u) ((e.world n).state u) := by
    intro n
    induction n with
    | zero =>
      intro root block found fresh
      change (e.start u).blocks[root]? = some block at found
      rw [found] at fresh
      cases fresh
    | succ n ih =>
      rcases e.state_succ n u with same | ⟨-, moved⟩
      · rw [same]
        exact ih
      · exact Handles.recordsTimely moved ih
  exact (records n root block held fresh).2 elapsed due current into dueOk early

/-- The boost of a store stays with its block while the clock of the store stays in one slot.

The boosted root must not be 32 zero bytes, the value that means no boost. -/
theorem Execution.proposerBoostRoot_of_le
    (e : Execution (forkChoice config checks sources signed sends) J) {u : ν} {k n : ℕ}
    (later : k ≤ n) {slot : Slot}
    (boosted : ((e.world k).state u).proposerBoostRoot ≠ Vector.replicate 32 0)
    (start : ((e.world k).state u).getCurrentSlot config = .ok slot)
    (stays : ((e.world n).state u).getCurrentSlot config = .ok slot) :
    ((e.world n).state u).proposerBoostRoot = ((e.world k).state u).proposerBoostRoot := by
  -- From `k` on the slot never falls, and while it is the slot of `k` the boost stays.
  suffices holds : ∀ j, k ≤ j →
      (∃ now, ((e.world j).state u).getCurrentSlot config = .ok now ∧ slot ≤ now) ∧
      (((e.world j).state u).getCurrentSlot config = .ok slot →
        ((e.world j).state u).proposerBoostRoot = ((e.world k).state u).proposerBoostRoot) from
    (holds n later).2 stays
  intro j le
  induction j, le using Nat.le_induction with
  | base => exact ⟨⟨slot, start, UInt64.le_refl _⟩, fun _ => rfl⟩
  | succ j _ ih =>
    obtain ⟨⟨now, nowOk, after⟩, keep⟩ := ih
    rcases e.state_succ j u with same | ⟨-, moved⟩
    · rw [same]
      exact ⟨⟨now, nowOk, after⟩, keep⟩
    obtain ⟨-, -, slots⟩ := Handles.clock moved
    obtain ⟨next, nextOk, grows⟩ := slots now nowOk
    refine ⟨⟨next, nextOk, UInt64.le_trans after grows⟩, fun inSlot => ?_⟩
    rw [nextOk, Except.ok.injEq] at inSlot
    subst inSlot
    -- The slot did not move, so the move kept the boost.
    have same : now = next := UInt64.le_antisymm grows after
    subst same
    rw [Handles.proposerBoostRoot_of_ne_zero moved (keep nowOk ▸ boosted) nowOk nextOk,
      keep nowOk]

/-- An up-to-date store holds each block of its view that its block handler accepts. -/
theorem UpToDate.contains_of_onBlock {store : Store preset fork}
    (upToDate : UpToDate config checks sources time view store)
    {signed : SignedBeaconBlock preset fork} (member : .block signed ∈ view)
    {after : Store preset fork} (accepted : store.onBlock config checks sources signed = .ok after)
    {root : Root} (hashed : SszType.hashTreeRoot signed.message = .ok root) :
    store.blocks.contains root := by
  -- The accepted block is a move, which leaves an up-to-date store as it is.
  have same := upToDate.2 after (.block member accepted)
  by_contra new
  have found := (Store.onBlock_new hashed new accepted).2.1
  rw [same] at found
  exact new (Std.TreeMap.contains_eq_isSome_getElem?.trans (by simp [found]))

section Duty

variable (config checks) in
/-- A store names a validator as the proposer of a slot, when its head is older than the slot.

The state of the head goes through the empty slots up to the slot, and names the validator. -/
def IsProposer (store : Store preset fork) (slot : Slot) (v : ValidatorIndex) : Prop :=
  ∃ head block headState state, store.getHead config = .ok head ∧
    store.blocks[head.root]? = some block ∧ block.slot < slot ∧
    store.blockState head.root = .ok headState ∧
    lookaheadState config checks headState slot = .ok state ∧
    getBeaconProposerIndex state = .ok v

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64}

/-- A proposal of an honest validator, as its duty asks, at the `n`-th event of an execution.

The event sends a new block of the slot at its start, on the head of the up-to-date store.

The parent is the head, not the parent of a late head that a proposer may build on instead. -/
structure ProposalAt {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) (v : ValidatorIndex) (slot : Slot) (time n : ℕ)
    (signed : SignedBeaconBlock preset fork) : Prop where
  sends : e.events n = .send v (.block signed)
  atTime : (e.world n).time = time
  -- The time is the start of the slot.
  atStart : ∃ start, computeTimeAtSlotMs config genesisTimeMs slot = .ok start ∧
    time = start.toNat
  inSlot : signed.message.slot = slot
  proposer : signed.message.proposerIndex = v
  genesis : ((e.world n).state v).genesisTimeMs = genesisTimeMs
  upToDate : UpToDate config checks sources time ((e.world n).view v) ((e.world n).state v)
  -- The store names the validator as the proposer of the slot.
  names : IsProposer config checks ((e.world n).state v) slot v
  -- The block builds on the head node, with the payload status of the head from Gloas.
  onHead : ∃ head parent, ((e.world n).state v).getHead config = .ok head ∧
    head.root = signed.message.parentRoot ∧
    ((e.world n).state v).blocks[signed.message.parentRoot]? = some parent ∧
    Store.parentPayloadStatus signed.message parent = head.payloadStatus
  -- The store does not hold the block yet, and its block handler accepts it.
  fresh : ∀ root, SszType.hashTreeRoot signed.message = .ok root →
    ((e.world n).state v).blocks.contains root = false
  accepted : ∃ after, ((e.world n).state v).onBlock config checks sources signed = .ok after

/-- The duty to propose, on an execution with honest validators `J`, in the slots `[first, last)`.

At the start of each slot from the start of the execution, each honest store is up to date once.

It follows the time of genesis, and the validator proposes at the first such event when named.

An honest validator sends a block only as its duty asks, at most one in every slot. -/
def Proposes {J : Set ValidatorIndex} (first last : Slot)
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  (∀ v ∈ J, ∀ slot start, first ≤ slot → slot < last →
    computeTimeAtSlotMs config genesisTimeMs slot = .ok start → e.startTime ≤ start.toNat →
    ∃ n, (e.world n).time = start.toNat ∧ ((e.world n).state v).genesisTimeMs = genesisTimeMs ∧
      UpToDate config checks sources start.toNat ((e.world n).view v) ((e.world n).state v) ∧
      (∀ k < n, (e.world k).time = start.toNat →
        ¬ UpToDate config checks sources start.toNat ((e.world k).view v) ((e.world k).state v)) ∧
      (IsProposer config checks ((e.world n).state v) slot v →
        ∃ signed, ProposalAt e v slot start.toNat n signed)) ∧
  (∀ v ∈ J, ∀ n m (signed other : SignedBeaconBlock preset fork),
    e.events n = .send v (.block signed) → e.events m = .send v (.block other) →
    signed.message.slot = other.message.slot → signed = other) ∧
  ∀ v ∈ J, ∀ n (signed : SignedBeaconBlock preset fork),
    e.events n = .send v (.block signed) → ∃ slot time, ProposalAt e v slot time n signed

/-- Only its proposer first sends a block that names an honest validator as proposer.

Any validator may send such a block again once it was sent.

It is an assumption on the adversary, in place of the signature of the proposer. -/
def UnforgedProposals {J : Set ValidatorIndex}
    (e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J) : Prop :=
  ∀ v n (signed : SignedBeaconBlock preset fork), e.events n = .send v (.block signed) →
    signed.message.proposerIndex ∈ J →
    signed.message.proposerIndex = v ∨ .block signed ∈ (e.world n).sent

/-- Under synchrony with delay `Δ`, a proposal reaches every honest validator `Δ` later. -/
theorem ProposalAt.mem_view {J : Set ValidatorIndex}
    {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
      genesisTimeMs) J} {Δ : ℕ} (sync : e.Synchronous Δ) {v u : ValidatorIndex}
    (honest : v ∈ J) (receiver : u ∈ J) {slot : Slot} {time n : ℕ}
    {signed : SignedBeaconBlock preset fork} (proposal : ProposalAt e v slot time n signed)
    {k : ℕ} (late : time + Δ ≤ (e.world k).time) : .block signed ∈ (e.world k).view u := by
  refine e.mem_view_of_send sync proposal.sends honest receiver ?_
  rw [proposal.atTime, Nat.max_zero]
  exact late

end Duty

end Models.Network

end EthLib.Consensus

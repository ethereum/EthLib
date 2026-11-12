module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.History.Era
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.E2store
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# Proofs: the indices and the name of an era file

In an accepted file, each group holds the index of its state where the group says.

That index has one entry, which finds the record of the state.

The record decompresses and decodes to the state of the group, at the slot where its era ends.

Each block of a group is found the same way, through the entry of its slot in the index of blocks.

Its root is the one that the state holds for its slot, and its fork is the fork of that slot.

A group of era 0 has no block, and a later group has an index entry for each slot of its era.

Each entry that is not 0 finds a block, and each later entry of 0 repeats the root before it.

So a reader can go straight to any block or state through the indices.

Two errors of an era file with one code come from one constructor.

A file name joins the configuration, the lowest era on at least five digits, and a short root.

The short root comes from the state of the last group of the highest era.

Era 0 is named by the root of the validators at genesis.

A later era is named by a historical root while the state holds one for it.

From Capella, past the historical roots, it is named by the root of a historical summary.
-/

@[expose] public section

namespace EthLib.Consensus.History

open EthLib.Base
open EthLib.Serialization

/-- Two errors with one code come from one constructor. -/
theorem EraError.code_injective (e₁ e₂ : EraError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EraError.code] at h; exact absurd h (by decide))

/-- Each record of a group is a record of the file. -/
private theorem mem_of_mem_groupsOf {records : List Located} {g : List Located}
    (hg : g ∈ groupsOf records) {x : Located} (hx : x ∈ g) : x ∈ records := by
  fun_induction groupsOf records with
  | case1 => simp at hg
  | case2 first rest ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact List.mem_cons_of_mem _ ((List.takeWhile_prefix _).subset hx)
    · exact List.mem_cons_of_mem _ ((List.dropWhile_suffix _).subset (ih hg))

/-- The indices that split off are records of the group, and SlotIndex records. -/
private theorem splitIndices_spec {records : List Located} {others : List Located}
    {blockIndexAt : Option Located} {stateIndexAt : Located}
    (h : splitIndices records = some (others, blockIndexAt, stateIndexAt)) :
    stateIndexAt ∈ records ∧ stateIndexAt.2.type = SLOT_INDEX ∧
      ∀ b, blockIndexAt = some b → b ∈ records ∧ b.2.type = SLOT_INDEX := by
  have hm : ∀ x, x ∈ records.reverse → x ∈ records := fun x => List.mem_reverse.mp
  unfold splitIndices at h
  split at h <;> rename_i heq
  · split at h
    · cases h
    split at h
    · cases h
      exact ⟨hm _ (heq ▸ List.mem_cons_self), by simp_all, fun b hb => by
        cases hb
        exact ⟨hm _ (heq ▸ List.mem_cons_of_mem _ List.mem_cons_self), by assumption⟩⟩
    · cases h
      exact ⟨hm _ (heq ▸ List.mem_cons_self), by simp_all, fun b hb => by cases hb⟩
  · split at h
    · cases h
    · cases h
      exact ⟨hm _ (heq ▸ List.mem_cons_self), by simp_all, fun b hb => by cases hb⟩
  · cases h

/-- Each slot that an index gives a block has a nonzero entry, and points where it says. -/
private theorem mem_indexedSlots {indexAt : Nat} {index : E2store.Index} {slot : Nat} {pos : Int}
    (h : (slot, pos) ∈ indexedSlots indexAt index) :
    ∃ (i : Nat) (hi : i < index.offsets.length), index.offsets[i] ≠ 0 ∧
      slot = index.start + i ∧ pos = indexAt + index.offsets[i] := by
  obtain ⟨⟨offset, i⟩, hm, he⟩ := List.mem_filterMap.mp h
  rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hm
  obtain ⟨hi, hoff⟩ := hm
  dsimp only at he
  split at he
  · cases he
  · cases he
    exact ⟨i, hi, hoff ▸ by assumption, rfl, by rw [hoff]⟩

/-- Each nonzero entry of an index gives its slot a block, at the position it points at. -/
private theorem mem_indexedSlots_of_ne {indexAt : Nat} {index : E2store.Index} {i : Nat}
    (hi : i < index.offsets.length) (hne : index.offsets[i] ≠ 0) :
    (index.start + i, (indexAt : Int) + index.offsets[i]) ∈ indexedSlots indexAt index := by
  refine List.mem_filterMap.mpr ⟨(index.offsets[i], i), ?_, ?_⟩
  · rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hi]
  · simp [hne]

/-- The matched blocks keep the slots of the index, in order. -/
private theorem matchBlocks_map_fst {slots : List (Nat × Int)} {records : List Located}
    {out : List (Nat × E2store.Record)} (h : matchBlocks slots records = .ok out) :
    out.map Prod.fst = slots.map Prod.fst := by
  induction slots generalizing records out with
  | nil =>
    cases records with
    | nil => cases h; rfl
    | cons r rs => cases h
  | cons s ss ih =>
    obtain ⟨slot, pos⟩ := s
    cases records with
    | nil => cases h
    | cons r rs =>
      obtain ⟨start, record⟩ := r
      rw [matchBlocks] at h
      split at h
      · cases hrest : matchBlocks ss rs with
        | error e => rw [hrest] at h; cases h
        | ok rest =>
          rw [hrest] at h
          cases h
          simp [ih hrest]
      · cases h

/-- A passed check of the slots without a block finds one root for such a slot and the one before.

It holds for each such slot but the first of the index. -/
private theorem checkEmptySlots_root {fork : Fork} {preset : Preset}
    {state : BeaconState preset fork} {index : E2store.Index}
    (h : checkEmptySlots state index = .ok ()) {i : Nat} (hlt : i < index.offsets.length)
    (hz : index.offsets[i] = 0) (h0 : i ≠ 0) :
    ∃ root, getBlockRootAtSlot state (UInt64.ofNat (index.start + i - 1)) = .ok root ∧
      getBlockRootAtSlot state (UInt64.ofNat (index.start + i)) = .ok root := by
  unfold checkEmptySlots at h
  have hstep := forM_ok_iff.mp h (0, i) (by
    rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hlt, hz])
  dsimp only at hstep
  rw [ite_eq_left ⟨rfl, h0⟩] at hstep
  rcases hb : getBlockRootAtSlot state (UInt64.ofNat (index.start + i - 1)) with e | before
  · simp only [hb, Except.mapError, bind, Except.bind] at hstep
    cases hstep
  rcases hr : getBlockRootAtSlot state (UInt64.ofNat (index.start + i)) with e | root
  · simp only [hb, hr, Except.mapError, bind, Except.bind] at hstep
    cases hstep
  simp only [hb, hr, Except.mapError, bind, Except.bind] at hstep
  split at hstep
  · rename_i hsame
    exact ⟨root, hsame ▸ rfl, rfl⟩
  · cases hstep

/-- Each matched block comes from a slot of the index and a record at the position it points at. -/
private theorem matchBlocks_mem {slots : List (Nat × Int)} {records : List Located}
    {out : List (Nat × E2store.Record)} (h : matchBlocks slots records = .ok out)
    {p : Nat × E2store.Record} (hp : p ∈ out) :
    ∃ start : Nat, (p.1, (start : Int)) ∈ slots ∧ (start, p.2) ∈ records := by
  induction slots generalizing records out with
  | nil =>
    cases records with
    | nil => cases h; simp at hp
    | cons r rs => cases h
  | cons s ss ih =>
    obtain ⟨slot, pos⟩ := s
    cases records with
    | nil => cases h
    | cons r rs =>
      obtain ⟨start, record⟩ := r
      rw [matchBlocks] at h
      split at h
      · rename_i hpos
        cases hrest : matchBlocks ss rs with
        | error e => rw [hrest] at h; cases h
        | ok rest =>
          rw [hrest] at h
          cases h
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨start, hpos ▸ List.mem_cons_self, List.mem_cons_self⟩
          · obtain ⟨st, h1, h2⟩ := ih hrest hp
            exact ⟨st, List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      · cases h

/-- A block that reads from its record decodes from it, at the fork of its slot, and checks out. -/
private theorem readBlock_facts {preset : Preset} {config : Config} {fork : Fork}
    {state : BeaconState preset fork} {slot : Nat} {record : E2store.Record}
    {block : EraBlock preset} (h : readBlock preset config state slot record = .ok block) :
    ∃ ssz, Networking.Snappy.decodeFrames record.data = .ok ssz ∧
      block.fork = forkAtSlot preset config slot ∧
      Ssz.SszType.deserialize (SignedBeaconBlock preset block.fork) ssz = .ok block.block ∧
      block.slot = block.block.message.slot ∧ block.slot.toNat = slot ∧
      Ssz.SszType.hashTreeRoot block.block.message = .ok block.root ∧
      getBlockRootAtSlot state block.slot = .ok block.root := by
  unfold readBlock at h
  cases hd : Networking.Snappy.decodeFrames record.data with
  | error e => simp [hd, bind, Except.bind, Except.mapError] at h
  | ok ssz =>
  cases hs : Ssz.SszType.deserialize
      (SignedBeaconBlock preset (forkAtSlot preset config slot)) ssz with
  | error e => simp [hd, hs, bind, Except.bind, Except.mapError] at h
  | ok b =>
  cases hr : Ssz.SszType.hashTreeRoot b.message with
  | error e =>
    simp [hd, hs, hr, bind, Except.bind, Except.mapError, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h <;> cases h
  | ok root =>
  cases hg : getBlockRootAtSlot state b.message.slot with
  | error e =>
    simp [hd, hs, hr, hg, bind, Except.bind, Except.mapError, throw, throwThe,
      MonadExceptOf.throw] at h
    split at h <;> cases h
  | ok expected =>
  simp [hd, hs, hr, hg, bind, Except.bind, Except.mapError, throw, throwThe,
    MonadExceptOf.throw, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
      rename_i h1 h2
      exact ⟨ssz, rfl, rfl, hs, rfl, h1, hr, h2 ▸ hg⟩
    · cases h
  · cases h

/-- What the blocks of an accepted group after era 0 passed, through its index of blocks. -/
private structure BlocksRead (preset : Preset) (config : Config) (g : List Located)
    (group : EraGroup preset) (blockIndexAt : Located) (blockIndex : E2store.Index)
    (slots : List (Nat × E2store.Record)) : Prop where
  mem : blockIndexAt ∈ g
  type : blockIndexAt.2.type = SLOT_INDEX
  found : group.blockIndex = some (blockIndexAt.1, blockIndex)
  read : E2store.readIndex blockIndexAt.2.data = .ok blockIndex
  range : blockIndex.start + preset.SLOTS_PER_HISTORICAL_ROOT.toNat = group.stateIndex.2.start
  length : blockIndex.offsets.length = preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  matched : matchBlocks (indexedSlots blockIndexAt.1 blockIndex)
    (g.takeWhile (·.2.type == COMPRESSED_SIGNED_BEACON_BLOCK)) = .ok slots
  blocks : slots.mapM (fun p => readBlock preset config group.state p.1 p.2) = .ok group.blocks
  empty : checkEmptySlots group.state blockIndex = .ok ()

/-- What an accepted group passed on its way: its state, its indices and its blocks. -/
private theorem readGroup_facts {preset : Preset} {config : Config} {g : List Located}
    {group : EraGroup preset} (h : readGroup preset config g = .ok group) :
    (∃ (stateAt stateIndexAt : Located) (ssz : ByteArray),
      stateAt ∈ g ∧ stateAt.2.type = COMPRESSED_BEACON_STATE ∧
      stateIndexAt ∈ g ∧ stateIndexAt.2.type = SLOT_INDEX ∧
      group.stateIndex.1 = stateIndexAt.1 ∧
      E2store.readIndex stateIndexAt.2.data = .ok group.stateIndex.2 ∧
      group.stateIndex.2.offsets.map ((stateIndexAt.1 : Int) + ·) = [(stateAt.1 : Int)] ∧
      Networking.Snappy.decodeFrames stateAt.2.data = .ok ssz ∧
      Ssz.SszType.deserialize (BeaconState preset group.fork) ssz = .ok group.state ∧
      group.fork = forkAtSlot preset config group.stateIndex.2.start ∧
      group.state.slot.toNat = group.stateIndex.2.start ∧
      group.stateIndex.2.start % preset.SLOTS_PER_HISTORICAL_ROOT.toNat = 0 ∧
      group.era = group.stateIndex.2.start / preset.SLOTS_PER_HISTORICAL_ROOT.toNat) ∧
    (group.era = 0 ∧ group.blocks = [] ∧ group.blockIndex = none ∨
      group.era ≠ 0 ∧ ∃ (blockIndexAt : Located) (blockIndex : E2store.Index)
        (slots : List (Nat × E2store.Record)),
        BlocksRead preset config g group blockIndexAt blockIndex slots) := by
  unfold readGroup at h
  dsimp only at h
  split at h
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i stateAt tail hdrop
  have hstate : stateAt ∈ g :=
    (List.dropWhile_suffix _).subset (hdrop ▸ List.mem_cons_self)
  have htail : ∀ x ∈ tail, x ∈ g := fun x hx =>
    (List.dropWhile_suffix _).subset (hdrop ▸ List.mem_cons_of_mem _ hx)
  by_cases htype : stateAt.2.type = COMPRESSED_BEACON_STATE
  rotate_left
  · simp [htype, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  rcases hsplit : splitIndices tail with _ | ⟨others, blockIndexAt, stateIndexAt⟩
  · simp [htype, hsplit, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨hsi, hsitype, hbi⟩ := splitIndices_spec hsplit
  rcases hidx : E2store.readIndex stateIndexAt.2.data with e | stateIndex
  · simp [htype, hsplit, hidx, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      Except.mapError] at h
    split at h <;> cases h
  simp [htype, hsplit, hidx, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      Except.mapError] at h
  split at h
  · cases h
  by_cases hoff : stateIndex.offsets.map ((stateIndexAt.1 : Int) + ·) = [(stateAt.1 : Int)]
  rotate_left
  · rw [ite_eq_right hoff] at h; cases h
  rw [ite_eq_left hoff] at h
  rcases hd : Networking.Snappy.decodeFrames stateAt.2.data with e | ssz
  · simp [hd] at h
  simp only [hd] at h
  rcases hs : Ssz.SszType.deserialize
      (BeaconState preset (forkAtSlot preset config stateIndex.start)) ssz with e | state
  · simp [hs] at h
  simp only [hs] at h
  by_cases hslot : state.slot.toNat = stateIndex.start ∧
      stateIndex.start % preset.SLOTS_PER_HISTORICAL_ROOT.toNat = 0
  rotate_left
  · rw [ite_eq_right hslot] at h; cases h
  rw [ite_eq_left hslot] at h
  split at h
  rotate_left
  · cases h
  by_cases hera : preset.SLOTS_PER_HISTORICAL_ROOT.toNat = 0 ∨
      stateIndex.start < preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  · rw [ite_eq_left hera] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨⟨stateAt, stateIndexAt, ssz, hstate, htype, htail _ hsi, hsitype, rfl, hidx, hoff,
        hd, hs, rfl, hslot.1, hslot.2, (Nat.div_eq_zero_iff.mpr hera).symm⟩,
        Or.inl ⟨rfl, rfl, rfl⟩⟩
    · cases h
  rw [ite_eq_right hera] at h
  rcases blockIndexAt with _ | bi
  · cases h
  obtain ⟨hbim, hbit⟩ := hbi bi rfl
  rcases hbidx : E2store.readIndex bi.2.data with e | blockIndex
  · simp [hbidx] at h
  simp only [hbidx] at h
  split at h
  rotate_left
  · cases h
  rename_i hrange
  rcases hm : matchBlocks (indexedSlots bi.1 blockIndex)
      (g.takeWhile (·.2.type == COMPRESSED_SIGNED_BEACON_BLOCK)) with e | slots
  · simp [hm] at h
  simp only [hm] at h
  rcases hb : slots.mapM (fun p => readBlock preset config state p.1 p.2) with e | blocks
  · simp [hb] at h
  simp only [hb] at h
  split at h
  · cases h
  · rename_i hempty
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨⟨stateAt, stateIndexAt, ssz, hstate, htype, htail _ hsi, hsitype, rfl, hidx, hoff, hd,
      hs, rfl, hslot.1, hslot.2, rfl⟩,
      Or.inr ⟨fun h0 => hera (Nat.div_eq_zero_iff.mp h0), bi, blockIndex, slots,
        ⟨htail _ hbim, hbit, rfl, hbidx, hrange.1, hrange.2, hm, hb, hempty⟩⟩⟩

/-- Each group of an accepted file reads from a group of the records of the decoded bytes. -/
private theorem decodeEra_group {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) :
    ∃ (records : List E2store.Record) (g : List Located), E2store.decode bytes = .ok records ∧
      g ∈ groupsOf ((E2store.recordStarts 0 records).zip records) ∧
      readGroup preset config g = .ok group := by
  unfold decodeEra at h
  rcases hf : E2store.decodeFile bytes with e | records
  · simp [hf, Except.mapError, bind, Except.bind] at h
  simp only [hf, Except.mapError, bind, Except.bind] at h
  obtain ⟨g, hgm, hrg⟩ := mapM_ok_mem h group hg
  exact ⟨records, g, (E2store.decodeFile_eq_ok_iff.mp hf).1, hgm, hrg⟩

/-- A group of an accepted file with an index of blocks read its blocks through that index. -/
private theorem decodeEra_blocksRead {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) {indexAt : Nat} {index : E2store.Index}
    (hi : group.blockIndex = some (indexAt, index)) :
    ∃ (g : List Located) (blockIndexAt : Located) (slots : List (Nat × E2store.Record)),
      blockIndexAt.1 = indexAt ∧ BlocksRead preset config g group blockIndexAt index slots := by
  obtain ⟨-, g, -, -, hrg⟩ := decodeEra_group h hg
  rcases (readGroup_facts hrg).2 with ⟨-, -, hnone⟩ | ⟨-, bi, blockIndex, slots, hread⟩
  · rw [hnone] at hi
    cases hi
  have hsame := hread.found.symm.trans hi
  simp only [Option.some.injEq, Prod.mk.injEq] at hsame
  obtain ⟨hat, rfl⟩ := hsame
  exact ⟨g, bi, slots, hat, hread⟩

/-- Each block of a group of an accepted file reads from a block record that the index points at. -/
private theorem decodeEra_block_facts {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) {block : EraBlock preset}
    (hb : block ∈ group.blocks) :
    ∃ (records : List E2store.Record) (indexAt : Located) (index : E2store.Index) (slot : Nat)
      (start : Nat) (record : E2store.Record), E2store.decode bytes = .ok records ∧
      indexAt ∈ (E2store.recordStarts 0 records).zip records ∧
      indexAt.2.type = SLOT_INDEX ∧ group.blockIndex = some (indexAt.1, index) ∧
      E2store.readIndex indexAt.2.data = .ok index ∧
      (slot, (start : Int)) ∈ indexedSlots indexAt.1 index ∧
      (start, record) ∈ (E2store.recordStarts 0 records).zip records ∧
      record.type = COMPRESSED_SIGNED_BEACON_BLOCK ∧
      readBlock preset config group.state slot record = .ok block := by
  obtain ⟨records, g, hdec, hgm, hrg⟩ := decodeEra_group h hg
  rcases (readGroup_facts hrg).2 with ⟨-, hnil, -⟩ | ⟨-, bi, blockIndex, slots, hread⟩
  · rw [hnil] at hb
    cases hb
  obtain ⟨⟨slot, record⟩, hsm, hrb⟩ := mapM_ok_mem hread.blocks block hb
  obtain ⟨start, hsl, hrec⟩ := matchBlocks_mem hread.matched hsm
  exact ⟨records, bi, blockIndex, slot, start, record, hdec, mem_of_mem_groupsOf hgm hread.mem,
    hread.type, hread.found, hread.read, hsl,
    mem_of_mem_groupsOf hgm ((List.takeWhile_prefix _).subset hrec),
    by simpa using List.all_eq_true.mp List.all_takeWhile _ hrec, hrb⟩

/-- In an accepted file, the index of the state of each group finds the state.

The index record sits where the group says, and has a single entry.

The entry counts from the start of the index record, and finds the record of the state.

That record decompresses and decodes, at the fork of the group, to the state of the group.

The state is at the first slot of the index, where the era of the group ends. -/
theorem decodeEra_state {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) :
    (∃ length, E2store.readHeader bytes group.stateIndex.1 = .ok ⟨SLOT_INDEX, length⟩ ∧
      E2store.readIndex (bytes.extract (group.stateIndex.1 + 8) (group.stateIndex.1 + 8 + length)) =
        .ok group.stateIndex.2) ∧
    ∃ (offset : Int) (pos length : Nat) (ssz : ByteArray),
      group.stateIndex.2.offsets = [offset] ∧
      (pos : Int) = group.stateIndex.1 + offset ∧
      E2store.readHeader bytes pos = .ok ⟨COMPRESSED_BEACON_STATE, length⟩ ∧
      Networking.Snappy.decodeFrames (bytes.extract (pos + 8) (pos + 8 + length)) = .ok ssz ∧
      Ssz.SszType.deserialize (BeaconState preset group.fork) ssz = .ok group.state ∧
      group.fork = forkAtSlot preset config group.stateIndex.2.start ∧
      group.state.slot.toNat = group.stateIndex.2.start ∧
      group.era * preset.SLOTS_PER_HISTORICAL_ROOT.toNat = group.stateIndex.2.start := by
  obtain ⟨records, g, hdec, hgm, hrg⟩ := decodeEra_group h hg
  obtain ⟨stateAt, stateIndexAt, ssz, hstate, htype, hsi, hsitype, hpos, hidx, hoff, hd, hs, hfork,
    hslot, hmod, hera⟩ := (readGroup_facts hrg).1
  have hat := fun x (hx : x ∈ g) =>
    E2store.record_at_mem hdec (mem_of_mem_groupsOf hgm hx)
  obtain ⟨hsh, hsx⟩ := hat _ hsi
  obtain ⟨hh, hx⟩ := hat _ hstate
  obtain ⟨offset, hone, hoffset⟩ := List.map_eq_singleton_iff.mp hoff
  refine ⟨⟨stateIndexAt.2.data.size, ?_, ?_⟩, offset, stateAt.1, stateAt.2.data.size, ssz, hone,
    ?_, ?_, ?_, hs, hfork, hslot, ?_⟩
  · rw [hpos, hsh, hsitype]
  · rw [hpos, hsx, hidx]
  · rw [hpos, ← hoffset]
  · rw [hh, htype]
  · rw [hx, hd]
  · rw [hera, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)]

/-- In an accepted file, the index of blocks finds each block of a group.

The group has an index of blocks, whose record sits where the group says.

The entry of the slot of the block is not 0, and counts from the start of the index record.

It finds a block record, which decompresses and decodes, at the fork of the block, to the block. -/
theorem decodeEra_block {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) {block : EraBlock preset}
    (hb : block ∈ group.blocks) :
    ∃ (indexAt : Nat) (index : E2store.Index), group.blockIndex = some (indexAt, index) ∧
      (∃ length, E2store.readHeader bytes indexAt = .ok ⟨SLOT_INDEX, length⟩ ∧
        E2store.readIndex (bytes.extract (indexAt + 8) (indexAt + 8 + length)) = .ok index) ∧
      ∃ (i : Nat) (hi : i < index.offsets.length), index.start + i = block.slot.toNat ∧
        index.offsets[i] ≠ 0 ∧
        ∃ (pos length : Nat) (ssz : ByteArray), (pos : Int) = indexAt + index.offsets[i] ∧
          E2store.readHeader bytes pos = .ok ⟨COMPRESSED_SIGNED_BEACON_BLOCK, length⟩ ∧
          Networking.Snappy.decodeFrames (bytes.extract (pos + 8) (pos + 8 + length)) = .ok ssz ∧
          Ssz.SszType.deserialize (SignedBeaconBlock preset block.fork) ssz = .ok block.block := by
  obtain ⟨records, indexAt, index, slot, start, record, hdec, hbim, hbit, hbig, hbidx, hsl, hrec,
    hrt, hrb⟩ := decodeEra_block_facts h hg hb
  obtain ⟨i, hi, hne, hslot, hstart⟩ := mem_indexedSlots hsl
  obtain ⟨ssz, hd, -, hs, -, hbs, -, -⟩ := readBlock_facts hrb
  obtain ⟨hih, hix⟩ := E2store.record_at_mem hdec hbim
  obtain ⟨hh, hx⟩ := E2store.record_at_mem hdec hrec
  refine ⟨indexAt.1, index, hbig, ⟨indexAt.2.data.size, ?_, ?_⟩, i, hi, ?_, hne, start,
    record.data.size, ssz, hstart, ?_, ?_, hs⟩
  · rw [hih, hbit]
  · rw [hix, hbidx]
  · rw [hbs, hslot]
  · rw [hh, hrt]
  · rw [hx, hd]

/-- In an accepted file, each block of a group has the root that the state holds for its slot.

The block has the slot of its message, and the fork of that slot.

Its root is the root of its message. -/
theorem decodeEra_blockRoot {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) {block : EraBlock preset}
    (hb : block ∈ group.blocks) :
    block.slot = block.block.message.slot ∧
      block.fork = forkAtSlot preset config block.slot.toNat ∧
      Ssz.SszType.hashTreeRoot block.block.message = .ok block.root ∧
      getBlockRootAtSlot group.state block.slot = .ok block.root := by
  obtain ⟨_, _, _, slot, _, _, -, -, -, -, -, -, -, -, hrb⟩ := decodeEra_block_facts h hg hb
  obtain ⟨-, -, hfork, -, hms, hbs, hroot, hget⟩ := readBlock_facts hrb
  exact ⟨hms, hbs ▸ hfork, hroot, hget⟩

/-- In an accepted file, a group of era 0 has no block and no index of blocks.

A group of a later era has an index of blocks with one entry per slot of the era.

Its first slot is that many slots before the slot of the state. -/
theorem decodeEra_blockIndex {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) :
    (group.era = 0 → group.blocks = [] ∧ group.blockIndex = none) ∧
      (group.era ≠ 0 → ∃ (indexAt : Nat) (index : E2store.Index),
        group.blockIndex = some (indexAt, index) ∧
        index.start + preset.SLOTS_PER_HISTORICAL_ROOT.toNat = group.stateIndex.2.start ∧
        index.offsets.length = preset.SLOTS_PER_HISTORICAL_ROOT.toNat) := by
  obtain ⟨-, g, -, -, hrg⟩ := decodeEra_group h hg
  rcases (readGroup_facts hrg).2 with ⟨h0, hnil, hnone⟩ | ⟨hne, bi, blockIndex, slots, hread⟩
  · exact ⟨fun _ => ⟨hnil, hnone⟩, fun hne => absurd h0 hne⟩
  · exact ⟨fun h0 => absurd h0 hne,
      fun _ => ⟨bi.1, blockIndex, hread.found, hread.range, hread.length⟩⟩

/-- In an accepted file, each entry of an index of blocks that is not 0 has its block.

The group holds a block at the slot of the entry.

The index finds that block, as the theorem on the blocks of a group says.

So a reader that follows any entry of the index lands on a block of the group. -/
theorem decodeEra_entry {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) {indexAt : Nat} {index : E2store.Index}
    (hi : group.blockIndex = some (indexAt, index)) (i : Nat) (hlt : i < index.offsets.length)
    (hne : index.offsets[i] ≠ 0) :
    ∃ block ∈ group.blocks, block.slot.toNat = index.start + i := by
  obtain ⟨g, bi, slots, rfl, hread⟩ := decodeEra_blocksRead h hg hi
  have hslots := matchBlocks_map_fst hread.matched
  have hblocks : group.blocks.map (·.slot.toNat) = slots.map Prod.fst :=
    map_of_mapM_ok (fun _ _ hrb => by
      obtain ⟨-, -, -, -, -, hslot, -⟩ := readBlock_facts hrb
      exact hslot) hread.blocks
  have hmem : index.start + i ∈ group.blocks.map (·.slot.toNat) := by
    rw [hblocks, hslots]
    exact List.mem_map_of_mem (f := Prod.fst) (mem_indexedSlots_of_ne hlt hne)
  obtain ⟨block, hb, hslot⟩ := List.mem_map.mp hmem
  exact ⟨block, hb, hslot⟩

/-- In an accepted file, each entry of 0 in an index of blocks, but the first, is an empty slot.

The state holds the same block root for its slot as for the slot before. -/
theorem decodeEra_emptySlot {preset : Preset} {config : Config} {bytes : ByteArray}
    {groups : List (EraGroup preset)} (h : decodeEra preset config bytes = .ok groups)
    {group : EraGroup preset} (hg : group ∈ groups) {indexAt : Nat} {index : E2store.Index}
    (hi : group.blockIndex = some (indexAt, index)) (i : Nat) (hlt : i < index.offsets.length)
    (hz : index.offsets[i] = 0) (h0 : i ≠ 0) :
    ∃ root, getBlockRootAtSlot group.state (UInt64.ofNat (index.start + i - 1)) = .ok root ∧
      getBlockRootAtSlot group.state (UInt64.ofNat (index.start + i)) = .ok root := by
  obtain ⟨_, _, _, _, hread⟩ := decodeEra_blocksRead h hg hi
  exact checkEmptySlots_root hread.empty hlt hz h0

/-! ## The name of a file -/

/-- The root that a state gives for an era is one of three roots, and only these.

Era 0 is named by the root of the validators at genesis.

Era `n + 1` is named by the historical root at index `n`, when the state holds one there.

Past the historical roots, a state from Capella names it by the root of a summary.

That summary sits at index `n` less the number of historical roots. -/
theorem eraRoot_eq_ok_iff {preset : Preset} {fork : Fork} {state : BeaconState preset fork}
    {era : Nat} {root : Root} :
    eraRoot state era = .ok root ↔
      (era = 0 ∧ root = state.genesisValidatorsRoot) ∨
      (∃ n, era = n + 1 ∧ state.historicalRoots.data[n]? = some root) ∨
      (∃ n, era = n + 1 ∧ state.historicalRoots.data.size ≤ n ∧
        ∃ (capella : .shapella ≤ fork) (summary : HistoricalSummary),
          (state.historicalSummaries capella).data[n - state.historicalRoots.data.size]? =
            some summary ∧
          Ssz.SszType.hashTreeRoot summary = .ok root) := by
  cases era with
  | zero => simp [eraRoot, pure, Except.pure, eq_comm]
  | succ n =>
    simp only [eraRoot, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    by_cases hr : n < state.historicalRoots.data.size
    · simp only [hr, dite_true, pure, Except.pure]
      simp [hr]
      omega
    · simp only [hr, dite_false]
      by_cases capella : .shapella ≤ fork
      · simp only [capella, dite_true]
        by_cases hs :
            n - state.historicalRoots.data.size < (state.historicalSummaries capella).data.size
        · obtain ⟨r, hroot⟩ := Ssz.SszType.hashTreeRoot_total
            (state.historicalSummaries capella).data[n - state.historicalRoots.data.size]
          simp [hs, hroot, hr, Except.mapError]
          omega
        · simp [hs, hr, throw, throwThe, MonadExceptOf.throw]
      · simp [capella, hr, throw, throwThe, MonadExceptOf.throw]

/-- The root of an era fails exactly when the state holds no root for it.

The error then carries the era, since hashing a summary never fails.

So era 0 never fails, and neither does an era within the historical roots.

A later era fails before Capella, and from Capella when it is past the summaries too. -/
theorem eraRoot_eq_error_iff {preset : Preset} {fork : Fork} {state : BeaconState preset fork}
    {era : Nat} {e : EraError} :
    eraRoot state era = .error e ↔
      e = .eraRoot era ∧ state.historicalRoots.data.size < era ∧
        ∀ capella : .shapella ≤ fork,
          state.historicalRoots.data.size + (state.historicalSummaries capella).data.size <
            era := by
  cases era with
  | zero => simp [eraRoot, pure, Except.pure]
  | succ n =>
    simp only [eraRoot, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    by_cases hr : n < state.historicalRoots.data.size
    · simp only [hr, dite_true, pure, Except.pure]
      simp
      omega
    · simp only [hr, dite_false]
      by_cases capella : .shapella ≤ fork
      · simp only [capella, dite_true]
        by_cases hs :
            n - state.historicalRoots.data.size < (state.historicalSummaries capella).data.size
        · obtain ⟨r, hroot⟩ := Ssz.SszType.hashTreeRoot_total
            (state.historicalSummaries capella).data[n - state.historicalRoots.data.size]
          simp [hs, hroot, Except.mapError]
          omega
        · simp only [hs, dite_false, throw, throwThe, MonadExceptOf.throw, Except.error.injEq]
          exact ⟨fun h => ⟨h.symm, by omega, fun _ => by omega⟩, fun h => h.1.symm⟩
      · simp only [capella, dite_false, throw, throwThe, MonadExceptOf.throw, Except.error.injEq]
        exact ⟨fun h => ⟨h.symm, by omega, fun c => c.elim⟩, fun h => h.1.symm⟩

/-- Let a number fit in `k` decimal places.

Its decimal digits, after zeros up to `k` places, are its digits by place. -/
private theorem leftpad_toDigits (n k : Nat) (hk : (Nat.toDigits 10 n).length ≤ k) :
    (Nat.toDigits 10 n).leftpad k '0' =
      List.ofFn fun i : Fin k => Nat.digitChar (n / 10 ^ (k - 1 - i) % 10) := by
  induction n using Nat.strongRecOn generalizing k with
  | _ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by
      have := Nat.length_toDigits_pos (b := 10) (n := n); omega⟩
    rw [List.ofFn_succ_last]
    by_cases hn : n < 10
    · rw [Nat.toDigits_of_lt_base hn]
      have hlast : n / 10 ^ (m + 1 - 1 - m) % 10 = n := by simp [Nat.mod_eq_of_lt hn]
      simp only [List.leftpad, List.length_singleton, Fin.val_last, hlast]
      congr 1
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.length_replicate] at h1
      have hdiv : n / 10 ^ (m - j) = 0 := by
        apply Nat.div_eq_of_lt
        calc n < 10 := hn
          _ = 10 ^ 1 := by simp
          _ ≤ 10 ^ (m - j) := Nat.pow_le_pow_right (by decide) (by omega)
      simp [hdiv]
    · rw [Nat.toDigits_of_base_le (by decide) (by omega)] at hk ⊢
      simp only [List.length_append, List.length_singleton] at hk
      have hpad : (Nat.toDigits 10 (n / 10) ++ [Nat.digitChar (n % 10)]).leftpad (m + 1) '0' =
          (Nat.toDigits 10 (n / 10)).leftpad m '0' ++ [Nat.digitChar (n % 10)] := by
        simp only [List.leftpad, List.length_append, List.length_singleton, List.append_assoc]
        congr 2
        omega
      rw [hpad, ih (n / 10) (by omega) m (by omega)]
      congr 1
      · apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [List.length_ofFn] at h1
        have hj : n / 10 ^ (m - j) = n / 10 / 10 ^ (m - 1 - j) := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
          congr 2
          omega
        simp [hj]
      · simp

/-- The digits of an era are its decimal digits by place, with zeros in front up to five places.

The last digit is the units.

An era of more than five digits keeps all its digits. -/
theorem eraDigits_toList (era : Nat) :
    (eraDigits era).toList =
      List.ofFn fun i : Fin (max 5 (Nat.toDigits 10 era).length) =>
        Nat.digitChar (era / 10 ^ (max 5 (Nat.toDigits 10 era).length - 1 - i) % 10) := by
  rw [eraDigits, String.toList_ofList, ← leftpad_toDigits era _ (Nat.le_max_right _ _)]
  simp only [List.leftpad]
  congr 2
  omega

/-- Below `10 ^ 5`, the digits of an era are its five decimal digits by place. -/
theorem eraDigits_toList_of_lt {era : Nat} (h : era < 10 ^ 5) :
    (eraDigits era).toList =
      List.ofFn fun i : Fin 5 => Nat.digitChar (era / 10 ^ (4 - i.val) % 10) := by
  have hlen : max 5 (Nat.toDigits 10 era).length = 5 :=
    Nat.max_eq_left ((Nat.length_toDigits_le_iff (by decide) (by decide)).mpr h)
  rw [eraDigits_toList, hlen]

/-- Folding by the higher era, the later on a tie, gives the last group of the highest era. -/
private theorem foldl_highest {preset : Preset} (highest : EraGroup preset) :
    ∀ (top : EraGroup preset) (groups before after : List (EraGroup preset)),
      top :: groups = before ++ highest :: after → (∀ g ∈ before, g.era ≤ highest.era) →
      (∀ g ∈ after, g.era < highest.era) →
      groups.foldl (fun top group => if top.era ≤ group.era then group else top) top = highest := by
  intro top groups
  induction groups generalizing top with
  | nil =>
    intro before after h _ _
    cases before with
    | nil => simp at h; exact h.1
    | cons b bs => simp at h
  | cons g gs ih =>
    intro before after h hbefore hafter
    simp only [List.foldl_cons]
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlt := hafter g (by simp)
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      exact ih top [] gs (by simp) (by simp) (fun x hx => hafter x (by simp [hx]))
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have htop := hbefore top (by simp)
      cases bs with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ite_eq_left_iff.mpr (fun h => absurd htop h)]
        exact ih g [] gs (by simp) (by simp) hafter
      | cons c cs =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        have hg := hbefore g (by simp)
        apply ih _ (_ :: cs) after (by rw [h]; rfl) _ hafter
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · split <;> assumption
        · exact hbefore x (by simp [hx])

/-- The name of a file of groups.

It is the name of the configuration, the digits of the lowest era, and a short root.

Dashes separate them, and `.era` ends the name.

The short root is the first 4 bytes of the root of the highest era, as lowercase hex.

That root comes from the last group of the highest era.

The statement splits the groups at that group.

No group before it has a higher era, and every group after it has a lower era.

The name fails exactly when that root fails, with the same error. -/
theorem eraFileName_eq {preset : Preset} {config : Config} {first : EraGroup preset}
    {rest before after : List (EraGroup preset)} {highest : EraGroup preset} {lowest : Nat}
    (hsplit : first :: rest = before ++ highest :: after)
    (hbefore : ∀ g ∈ before, g.era ≤ highest.era) (hafter : ∀ g ∈ after, g.era < highest.era)
    (hlowest : ∃ g ∈ first :: rest, g.era = lowest)
    (hle : ∀ g ∈ first :: rest, lowest ≤ g.era) :
    eraFileName config first rest = (eraRoot highest.state highest.era).map fun root =>
      config.CONFIG_NAME ++ "-" ++ eraDigits lowest ++ "-" ++
        String.ofList ((root.toList.take 4).flatMap byteHexDigits) ++ ".era" := by
  have hlow : rest.foldl (fun era group => min era group.era) first.era = lowest := by
    have h : ((first :: rest).map (·.era)).min? = some lowest :=
      List.min?_eq_some_iff.mpr ⟨by simpa [eq_comm] using hlowest, by simpa using hle⟩
    rwa [List.map_cons, List.min?_cons', List.foldl_map, Option.some.injEq] at h
  have hhigh := foldl_highest highest first rest before after hsplit hbefore hafter
  rw [eraFileName]
  simp only [hlow]
  rw [hhigh]
  cases eraRoot highest.state highest.era <;> rfl

end EthLib.Consensus.History

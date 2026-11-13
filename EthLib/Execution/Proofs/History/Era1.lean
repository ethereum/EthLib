module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.History.Era1
public import EthLib.Serialization.Proofs.E2store

/-!
# Proofs: the block index and the chain of an era1 file

An accepted file has one offset per block.

The offset of a block, from the start of the BlockIndex record, finds its header record.

That record decompresses to the header of the block.

So a reader can go straight to any block through the index.

The blocks of an accepted file form a chain.

Their headers carry the numbers from the first number of the index on.

Each block after the first names the hash of the header before as its parent.

Each total difficulty after the first is the one before plus the difficulty of the block.

In a file whose first number is 0, the first total difficulty is the difficulty of that block.

An accepted file holds at most 8192 blocks.

The accumulator is the SSZ root of the list of the hash and total difficulty of each block.

Two errors of an era1 file with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Execution.History

open EthLib.Serialization

/-- Two errors with one code come from one constructor. -/
theorem Era1Error.code_injective (e₁ e₂ : Era1Error) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [Era1Error.code] at h; exact absurd h (by decide))

/-- The front records split into the four records of each block, then the records after them. -/
private theorem takeBlocks_spec (rs : List E2store.Record) :
    rs.drop (4 * (takeBlocks rs).1.length) = (takeBlocks rs).2 ∧
      ∀ i (hi : i < (takeBlocks rs).1.length), ∃ hk : 4 * i < rs.length,
        rs[4 * i] = ((takeBlocks rs).1[i]).1 ∧
          ((takeBlocks rs).1[i]).1.type = COMPRESSED_HEADER := by
  match rs with
  | h :: b :: r :: t :: rest =>
    obtain ⟨ihd, ihi⟩ := takeBlocks_spec rest
    by_cases hc : h.type = COMPRESSED_HEADER ∧ b.type = COMPRESSED_BODY ∧
        r.type = COMPRESSED_RECEIPTS ∧ t.type = TOTAL_DIFFICULTY
    · have e : takeBlocks (h :: b :: r :: t :: rest) =
          ((h, b, r, t) :: (takeBlocks rest).1, (takeBlocks rest).2) := by
        rw [takeBlocks.eq_1, ite_eq_left hc]
      rw [e]
      refine ⟨?_, fun i hi => ?_⟩
      · simpa [Nat.mul_add] using ihd
      · cases i with
        | zero => exact ⟨by simp, rfl, hc.1⟩
        | succ i =>
          obtain ⟨hk, h1, h2⟩ := ihi i (by simpa using hi)
          refine ⟨by simp; omega, ?_, h2⟩
          simpa [Nat.mul_add] using h1
    · rw [takeBlocks.eq_1, ite_eq_right hc]
      exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | [] | [_] | [_, _] | [_, _, _] =>
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

/-- A block read from its four records has the decompressed header record as header. -/
private theorem readBlock_header {start i : Nat}
    {records : E2store.Record × E2store.Record × E2store.Record × E2store.Record}
    {result : Era1Block × Nat × Base.Hash32} (h : readBlock start i records = .ok result) :
    Networking.Snappy.decodeFrames records.1.data = .ok result.1.header := by
  obtain ⟨hr, b, r, t⟩ := records
  unfold readBlock decompressRecord at h
  cases hd : Networking.Snappy.decodeFrames hr.data with
  | error e => simp [hd, bind, Except.bind, Except.mapError] at h
  | ok header =>
    simp [hd, bind, Except.bind, Except.mapError] at h
    repeat' split at h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
      | cases h

/-- A read block has a header that decodes to one RLP item, with the number its place asks.

The difficulty and the parent hash that come back are those of that item. -/
private theorem readBlock_item {start i : Nat}
    {records : E2store.Record × E2store.Record × E2store.Record × E2store.Record}
    {block : Era1Block} {difficulty : Nat} {parent : Base.Hash32}
    (h : readBlock start i records = .ok (block, difficulty, parent)) :
    ∃ item, Rlp.decode block.header = .ok item ∧
      Execution.Network.headerNumber item = .ok (start + i) ∧
      Execution.Network.headerDifficulty item = .ok difficulty ∧
      Execution.Network.headerParent item = .ok parent := by
  obtain ⟨hr, b, r, t⟩ := records
  unfold readBlock decompressRecord rlpItem at h
  simp only [bind, Except.bind, Except.mapError, pure, Except.pure] at h
  repeat (first | (split at h <;> try cases h))
  rename_i _ item hi _ _ _ _ _ _ _ n hn hnum _ _ _ _ _ hd hp
  exact ⟨item, Base.mapError_ok_iff.mp hi, hnum ▸ Base.mapError_ok_iff.mp hn,
    Base.mapError_ok_iff.mp hd, Base.mapError_ok_iff.mp hp⟩

/-- Reading blocks reads the first block, checks it against the block before, then reads on.

A first block numbered from 0 with no block before has its difficulty as total difficulty. -/
private theorem readBlocks_link {start i : Nat} {before : Option (Base.Hash32 × Nat)}
    {r : E2store.Record × E2store.Record × E2store.Record × E2store.Record}
    {rest : List (E2store.Record × E2store.Record × E2store.Record × E2store.Record)}
    {blocks : List Era1Block} (h : readBlocks start i before (r :: rest) = .ok blocks) :
    ∃ block difficulty parent bs, readBlock start i r = .ok (block, difficulty, parent) ∧
      (∀ hash tdBefore, before = some (hash, tdBefore) →
        parent = hash ∧ block.totalDifficulty.toNat = tdBefore + difficulty) ∧
      (before = none → start = 0 → block.totalDifficulty.toNat = difficulty) ∧
      readBlocks start (i + 1)
        (some (Cryptography.Hash.Keccak.keccak256 block.header, block.totalDifficulty.toNat))
        rest = .ok bs ∧
      blocks = block :: bs := by
  rw [readBlocks] at h
  rcases hr : readBlock start i r with e | ⟨block, difficulty, parent⟩
  · simp [hr, bind, Except.bind] at h
  simp only [hr, bind, Except.bind] at h
  rcases hb : readBlocks start (i + 1)
      (some (Cryptography.Hash.Keccak.keccak256 block.header, block.totalDifficulty.toNat))
      rest with e | bs
  · rcases before with _ | ⟨hash, tdBefore⟩ <;> simp [hb] at h <;>
      repeat' split at h <;> simp_all
  · refine ⟨block, difficulty, parent, bs, rfl, ?_, ?_, hb, ?_⟩ <;>
      rcases before with _ | ⟨hash, tdBefore⟩ <;> simp [hb] at h <;>
      repeat' split at h <;> simp_all [pure, Except.pure]

/-- Reading blocks gives one block per tuple, whose header decompresses from its record. -/
private theorem readBlocks_spec {start i : Nat} {before : Option (Base.Hash32 × Nat)}
    {ts : List (E2store.Record × E2store.Record × E2store.Record × E2store.Record)}
    {blocks : List Era1Block} (h : readBlocks start i before ts = .ok blocks) :
    blocks.length = ts.length ∧ ∀ k (hk : k < blocks.length) (hk' : k < ts.length),
      Networking.Snappy.decodeFrames (ts[k]).1.data = .ok blocks[k].header := by
  induction ts generalizing i before blocks with
  | nil =>
    rw [readBlocks] at h
    cases h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | cons r rest ih =>
    obtain ⟨block, _, _, bs, hr, -, -, hbs, rfl⟩ := readBlocks_link h
    obtain ⟨hl, hk⟩ := ih hbs
    refine ⟨by simp [hl], fun k hk1 hk2 => ?_⟩
    cases k with
    | zero => exact readBlock_header hr
    | succ k => exact hk k (by simpa using hk1) (by simpa using hk2)

/-- Read blocks form a chain from the block before them.

The header of each decodes to one RLP item, with the number its place asks.

After a block before, the first names its hash as parent.

Its total difficulty is the one before plus its difficulty.

With no block before and a numbering that starts at 0, the first total difficulty is its difficulty.

Each later block names the Keccak-256 hash of the header before as its parent.

Its total difficulty is the one before plus its difficulty. -/
private theorem readBlocks_chain {start i : Nat} {before : Option (Base.Hash32 × Nat)}
    {ts : List (E2store.Record × E2store.Record × E2store.Record × E2store.Record)}
    {blocks : List Era1Block} (h : readBlocks start i before ts = .ok blocks)
    {k : Nat} (hk : k < blocks.length) :
    ∃ item difficulty, Rlp.decode blocks[k].header = .ok item ∧
      Execution.Network.headerNumber item = .ok (start + (i + k)) ∧
      Execution.Network.headerDifficulty item = .ok difficulty ∧
      (k = 0 →
        (∀ hash tdBefore, before = some (hash, tdBefore) →
          Execution.Network.headerParent item = .ok hash ∧
            blocks[k].totalDifficulty.toNat = tdBefore + difficulty) ∧
        (before = none → start = 0 → blocks[k].totalDifficulty.toNat = difficulty)) ∧
      ∀ j (hj : k = j + 1),
        Execution.Network.headerParent item =
            .ok (Cryptography.Hash.Keccak.keccak256 (blocks[j]'(by omega)).header) ∧
          blocks[k].totalDifficulty.toNat =
            (blocks[j]'(by omega)).totalDifficulty.toNat + difficulty := by
  induction ts generalizing i before blocks k with
  | nil =>
    rw [readBlocks] at h
    cases h
    exact absurd hk (Nat.not_lt_zero _)
  | cons r rest ih =>
    obtain ⟨block, difficulty, parent, bs, hr, hs, hn, hbs, rfl⟩ := readBlocks_link h
    cases k with
    | zero =>
      obtain ⟨item, hi, hnum, hd, hp⟩ := readBlock_item hr
      refine ⟨item, difficulty, hi, by simpa using hnum, hd, fun _ => ⟨fun hash tdBefore hb => ?_,
        hn⟩, fun j hj => absurd hj (by omega)⟩
      obtain ⟨rfl, htd⟩ := hs hash tdBefore hb
      exact ⟨hp, htd⟩
    | succ k =>
      obtain ⟨item, d, hi, hnum, hd, h0, hj⟩ := ih hbs (k := k) (by simpa using hk)
      refine ⟨item, d, hi, ?_, hd, fun h => absurd h (by omega), fun j hj' => ?_⟩
      · rw [hnum]
        congr 2
        omega
      cases j with
      | zero => exact (h0 (by omega)).1 _ _ rfl
      | succ j => exact hj j (by omega)

/-- What an accepted file passed on its way: its records, its index, blocks and accumulator. -/
private theorem decodeEra1_facts {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) :
    ∃ (records : List E2store.Record) (idx : E2store.Record) (index : E2store.Index),
      E2store.decode bytes = .ok records ∧
      E2store.readIndex idx.data = .ok index ∧
      index.offsets.length = (takeBlocks (records.drop 1)).1.length ∧
      (∀ i < (takeBlocks (records.drop 1)).1.length,
        ((bytes.size - 8 - idx.data.size : Nat) : Int) + index.offsets.getD i 0 =
          ((E2store.recordStarts 0 records).getD (1 + 4 * i) 0 : Nat)) ∧
      readBlocks index.start 0 none (takeBlocks (records.drop 1)).1 = .ok era1.blocks ∧
      era1.offsets = index.offsets ∧ era1.startingNumber = index.start ∧
      accumulatorRoot era1.blocks = .ok era1.accumulator := by
  unfold decodeEra1 at h
  rcases hf : E2store.decodeFile bytes with e | records
  · simp [hf, Except.mapError, bind, Except.bind] at h
  rcases ht : takeBlocks records.tail with ⟨tuples, after⟩
  rcases hs : splitLastTwo after with _ | ⟨others, acc, idx⟩
  · simp [hf, ht, hs, Except.mapError, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h
  rcases hi : E2store.readIndex idx.data with e | index
  · simp [hf, ht, hs, hi, Except.mapError, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' split at h
    all_goals cases h
  simp [hf, ht, hs, hi, Except.mapError, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at h
  by_cases htr : acc.type = ACCUMULATOR ∧ idx.type = BLOCK_INDEX
  rotate_left
  · rw [ite_eq_right htr] at h; cases h
  rw [ite_eq_left htr] at h
  split at h
  · cases h
  by_cases hmax : tuples.length ≤ MAX_ERA1_BLOCKS
  rotate_left
  · rw [ite_eq_right hmax] at h; cases h
  rw [ite_eq_left hmax] at h
  by_cases hlen : index.offsets.length = tuples.length
  rotate_left
  · rw [ite_eq_right hlen] at h; cases h
  rw [ite_eq_left hlen] at h
  split at h
  · cases h
  rename_i hmis
  rcases hrb : readBlocks index.start 0 none tuples with e | blocks
  · rw [hrb] at h; cases h
  rw [hrb] at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · rename_i hroot hsame
    cases h
    have hnone := Option.eq_none_iff_forall_ne_some.mpr hmis
    rw [List.find?_eq_none] at hnone
    refine ⟨records, idx, index, (E2store.decodeFile_eq_ok_iff.mp hf).1, hi, ?_, ?_, ?_, rfl, rfl,
      ?_⟩
    · rw [List.drop_one, ht]; exact hlen
    · intro i hi'
      rw [List.drop_one, ht] at hi'
      have := hnone i (List.mem_range.mpr hi')
      simpa [List.getD_eq_getElem?_getD] using this
    · rw [List.drop_one, ht]; exact hrb
    · exact hroot.trans (congrArg _ hsame)
  · cases h

/-- An accepted file has one offset per block. -/
theorem decodeEra1_offsets_length {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) : era1.offsets.length = era1.blocks.length := by
  obtain ⟨_, _, _, -, -, hlen, -, hrb, hoff, -⟩ := decodeEra1_facts h
  rw [hoff, hlen, (readBlocks_spec hrb).1]

/-- In an accepted file, the offset of each block finds its header record.

The offset counts from 24 bytes plus 8 bytes per block before the end of the file.

The decoder reads the BlockIndex record, the last one, from there.

The data of the header record decompresses to the header of the block. -/
theorem decodeEra1_offset {bytes : ByteArray} {era1 : Era1} (h : decodeEra1 bytes = .ok era1)
    {i : Nat} (hi : i < era1.blocks.length) :
    ∃ pos length : Nat,
      (pos : Int) = ((bytes.size - (24 + 8 * era1.offsets.length) : Nat) : Int) +
        era1.offsets.getD i 0 ∧
      E2store.readHeader bytes pos = .ok ⟨COMPRESSED_HEADER, length⟩ ∧
      Networking.Snappy.decodeFrames (bytes.extract (pos + 8) (pos + 8 + length)) =
        .ok era1.blocks[i].header := by
  obtain ⟨records, idx, index, hd, hidx, -, hpos, hrb, hoff, -⟩ := decodeEra1_facts h
  obtain ⟨hbl, hhd⟩ := readBlocks_spec hrb
  have hit : i < (takeBlocks (records.drop 1)).1.length := hbl ▸ hi
  obtain ⟨hk, hrec, htype⟩ := (takeBlocks_spec (records.drop 1)).2 i hit
  have hk' : 1 + 4 * i < records.length := by
    rw [List.length_drop] at hk
    omega
  have hrec' : records[1 + 4 * i] = ((takeBlocks (records.drop 1)).1[i]).1 := by
    rw [← hrec, List.getElem_drop]
  obtain ⟨hh, hx⟩ := E2store.record_at hd hk'
  have hsz := E2store.readIndex_size hidx
  refine ⟨(E2store.recordStarts 0 records).getD (1 + 4 * i) 0,
    ((takeBlocks (records.drop 1)).1[i]).1.data.size, ?_, ?_, ?_⟩
  · rw [← hpos i hit, hoff, hsz]
    congr 2
    omega
  · rw [hh, hrec', htype]
  · rw [hrec'] at hx
    rw [hx]
    exact hhd i hi hit

/-- The header of each block of an accepted file decodes to one RLP item.

That item has a difficulty. -/
theorem decodeEra1_header {bytes : ByteArray} {era1 : Era1} (h : decodeEra1 bytes = .ok era1)
    {k : Nat} (hk : k < era1.blocks.length) :
    ∃ item difficulty, Rlp.decode era1.blocks[k].header = .ok item ∧
      Execution.Network.headerDifficulty item = .ok difficulty := by
  obtain ⟨_, _, _, -, -, -, -, hrb, -, -, -⟩ := decodeEra1_facts h
  obtain ⟨item, d, hi, -, hd, -⟩ := readBlocks_chain hrb hk
  exact ⟨item, d, hi, hd⟩

/-- In an accepted file, the header of each block carries the first number plus its place. -/
theorem decodeEra1_number {bytes : ByteArray} {era1 : Era1} (h : decodeEra1 bytes = .ok era1)
    {k : Nat} (hk : k < era1.blocks.length) {item : Rlp.Item}
    (hi : Rlp.decode era1.blocks[k].header = .ok item) :
    Execution.Network.headerNumber item = .ok (era1.startingNumber + k) := by
  obtain ⟨_, _, _, -, -, -, -, hrb, -, hstart, -⟩ := decodeEra1_facts h
  obtain ⟨item', _, hi', hnum, -⟩ := readBlocks_chain hrb hk
  cases hi.symm.trans hi'
  rw [hnum, hstart, Nat.zero_add]

/-- In an accepted file, each block after the first names the hash of the header before. -/
theorem decodeEra1_parent {bytes : ByteArray} {era1 : Era1} (h : decodeEra1 bytes = .ok era1)
    {k : Nat} (hk : k + 1 < era1.blocks.length) {item : Rlp.Item}
    (hi : Rlp.decode era1.blocks[k + 1].header = .ok item) :
    Execution.Network.headerParent item =
      .ok (Cryptography.Hash.Keccak.keccak256 era1.blocks[k].header) := by
  obtain ⟨_, _, _, -, -, -, -, hrb, -, -, -⟩ := decodeEra1_facts h
  obtain ⟨item', _, hi', -, -, -, hj⟩ := readBlocks_chain hrb hk
  cases hi.symm.trans hi'
  exact (hj k rfl).1

/-- In an accepted file, each block after the first adds its difficulty to the total before. -/
theorem decodeEra1_totalDifficulty {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) {k : Nat} (hk : k + 1 < era1.blocks.length)
    {item : Rlp.Item} {difficulty : Nat} (hi : Rlp.decode era1.blocks[k + 1].header = .ok item)
    (hd : Execution.Network.headerDifficulty item = .ok difficulty) :
    era1.blocks[k + 1].totalDifficulty.toNat =
      era1.blocks[k].totalDifficulty.toNat + difficulty := by
  obtain ⟨_, _, _, -, -, -, -, hrb, -, -, -⟩ := decodeEra1_facts h
  obtain ⟨item', d, hi', -, hd', -, hj⟩ := readBlocks_chain hrb hk
  cases hi.symm.trans hi'
  cases hd.symm.trans hd'
  exact (hj k rfl).2

/-- In an accepted file whose first number is 0, the first total difficulty is its difficulty. -/
theorem decodeEra1_totalDifficulty_zero {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) (hs : era1.startingNumber = 0)
    (hk : 0 < era1.blocks.length) {item : Rlp.Item} {difficulty : Nat}
    (hi : Rlp.decode era1.blocks[0].header = .ok item)
    (hd : Execution.Network.headerDifficulty item = .ok difficulty) :
    era1.blocks[0].totalDifficulty.toNat = difficulty := by
  obtain ⟨_, _, _, -, -, -, -, hrb, -, hstart, -⟩ := decodeEra1_facts h
  obtain ⟨item', d, hi', -, hd', h0, -⟩ := readBlocks_chain hrb hk
  cases hi.symm.trans hi'
  cases hd.symm.trans hd'
  exact (h0 rfl).2 rfl (hstart ▸ hs)

/-- An accepted file holds at most 8192 blocks. -/
theorem decodeEra1_blocks_length_le {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) : era1.blocks.length ≤ MAX_ERA1_BLOCKS := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, hacc⟩ := decodeEra1_facts h
  unfold accumulatorRoot at hacc
  dsimp only at hacc
  split at hacc
  · rename_i bound
    simpa using bound
  · cases hacc

/-- The accumulator of an accepted file is the SSZ root of a list with one entry per block.

The entry of a block is the Keccak-256 hash of its header and its total difficulty. -/
theorem decodeEra1_accumulator {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) : accumulatorRoot era1.blocks = .ok era1.accumulator := by
  obtain ⟨_, _, _, -, -, -, -, -, -, -, hacc⟩ := decodeEra1_facts h
  exact hacc

end EthLib.Execution.History

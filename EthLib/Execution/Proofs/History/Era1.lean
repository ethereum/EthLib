module

public import EthLib.Execution.History.Era1
public import EthLib.Serialization.Proofs.E2store

/-!
# Proofs: the block index of an era1 file

An accepted file has one offset per block.

The offset of a block, from the start of the BlockIndex record, finds its header record.

That record decompresses to the header of the block.

So a reader can go straight to any block through the index.

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
  unfold readBlock decompress at h
  cases hd : Networking.Snappy.decodeFrames hr.data with
  | error e => simp [hd, bind, Except.bind, Except.mapError] at h
  | ok header =>
    simp [hd, bind, Except.bind, Except.mapError] at h
    repeat' split at h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
      | cases h

/-- Reading blocks reads the first block, then the others after it. -/
private theorem readBlocks_cons {start i : Nat} {before : Option (Base.Hash32 × Nat)}
    {r : E2store.Record × E2store.Record × E2store.Record × E2store.Record}
    {rest : List (E2store.Record × E2store.Record × E2store.Record × E2store.Record)}
    {blocks : List Era1Block} (h : readBlocks start i before (r :: rest) = .ok blocks) :
    ∃ result bs after, readBlock start i r = .ok result ∧
      readBlocks start (i + 1) after rest = .ok bs ∧ blocks = result.1 :: bs := by
  rw [readBlocks] at h
  cases hr : readBlock start i r with
  | error e => simp [hr, bind, Except.bind] at h
  | ok result =>
    simp [hr, bind, Except.bind] at h
    cases hb : readBlocks start (i + 1)
        (some (Cryptography.Hash.Keccak.keccak256 result.1.header,
          result.1.totalDifficulty.toNat)) rest with
    | error e =>
      repeat' split at h
      all_goals cases h <;> simp_all
    | ok bs =>
      refine ⟨result, bs, _, rfl, hb, ?_⟩
      repeat' split at h
      all_goals cases h <;> simp_all

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
    obtain ⟨result, bs, after, hr, hbs, rfl⟩ := readBlocks_cons h
    obtain ⟨hl, hk⟩ := ih hbs
    refine ⟨by simp [hl], fun k hk1 hk2 => ?_⟩
    cases k with
    | zero => exact readBlock_header hr
    | succ k => exact hk k (by simpa using hk1) (by simpa using hk2)

/-- What an accepted file passed on its way: its records, its block index and its blocks. -/
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
      era1.offsets = index.offsets := by
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
  · cases h
    have hnone := Option.eq_none_iff_forall_ne_some.mpr hmis
    rw [List.find?_eq_none] at hnone
    refine ⟨records, idx, index, (E2store.decodeFile_eq_ok_iff.mp hf).1, hi, ?_, ?_, ?_, rfl⟩
    · rw [List.drop_one, ht]; exact hlen
    · intro i hi'
      rw [List.drop_one, ht] at hi'
      have := hnone i (List.mem_range.mpr hi')
      simpa [List.getD_eq_getElem?_getD] using this
    · rw [List.drop_one, ht]; exact hrb
  · cases h

/-- An accepted file has one offset per block. -/
theorem decodeEra1_offsets_length {bytes : ByteArray} {era1 : Era1}
    (h : decodeEra1 bytes = .ok era1) : era1.offsets.length = era1.blocks.length := by
  obtain ⟨_, _, _, -, -, hlen, -, hrb, hoff⟩ := decodeEra1_facts h
  rw [hoff, hlen, (readBlocks_spec hrb).1]

/-- In an accepted file, the offset of each block finds its header record.

The offset counts from the start of the BlockIndex record, the last record of the file.

That record has 24 bytes plus 8 bytes per block.

The data of the header record decompresses to the header of the block. -/
theorem decodeEra1_offset {bytes : ByteArray} {era1 : Era1} (h : decodeEra1 bytes = .ok era1)
    {i : Nat} (hi : i < era1.blocks.length) :
    ∃ pos length : Nat,
      (pos : Int) = ((bytes.size - (24 + 8 * era1.offsets.length) : Nat) : Int) +
        era1.offsets.getD i 0 ∧
      E2store.readHeader bytes pos = .ok ⟨COMPRESSED_HEADER, length⟩ ∧
      Networking.Snappy.decodeFrames (bytes.extract (pos + 8) (pos + 8 + length)) =
        .ok era1.blocks[i].header := by
  obtain ⟨records, idx, index, hd, hidx, -, hpos, hrb, hoff⟩ := decodeEra1_facts h
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

end EthLib.Execution.History

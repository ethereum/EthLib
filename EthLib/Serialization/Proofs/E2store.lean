module

public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Base.Proofs.Bytes
public import EthLib.Serialization.E2store
import EthLib.Serialization.Proofs.Ssz.Codec.CanonicalTable
import EthLib.Serialization.Proofs.Ssz.Codec.DecodeFits

/-!
# Proofs: the e2store records read back

The encoding is a bijection onto the bytes that decode.

Its domain is the record lists whose data each have fewer than `2^32` bytes.

This module also states which files decode, and where each record sits in the bytes.
-/

@[expose] public section

namespace EthLib.Serialization.E2store

open EthLib.Base

/-! ### Headers -/

/-- A header is eight bytes. -/
@[simp] theorem size_encodeHeader (type : UInt16) (length : Nat) :
    (encodeHeader type length).size = 8 := by
  simp [encodeHeader, ByteArray.size]

/-- The header at the start of eight bytes, read from their values. -/
private theorem readHeader_mk (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    readHeader ⟨#[b0, b1, b2, b3, b4, b5, b6, b7]⟩ 0 =
      if b6 ≠ 0 ∨ b7 ≠ 0 then .error (.reservedNotZero b6 b7)
      else .ok ⟨UInt16.ofNat (ByteOrder.ofBE [b0, b1]), ByteOrder.ofLE #v[b2, b3, b4, b5]⟩ :=
  rfl

/-- Eight bytes are the array of their values. -/
private theorem eq_mk_of_size (x : ByteArray) (h : x.size = 8) :
    x = ⟨#[byteAtOrZero x 0, byteAtOrZero x 1, byteAtOrZero x 2, byteAtOrZero x 3, byteAtOrZero x 4, byteAtOrZero x 5, byteAtOrZero x 6,
      byteAtOrZero x 7]⟩ := by
  refine eq_of_byteAtOrZero h fun i => ?_
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | i + 8 => rw [byteAtOrZero_of_size_le (by omega), byteAtOrZero_of_size_le (Nat.le_add_left 8 i)]

/-- The header at a position is the header at the start of the eight bytes there. -/
private theorem readHeader_extract (bytes : ByteArray) (offset : Nat)
    (h : offset + 8 ≤ bytes.size) :
    readHeader (bytes.extract offset (offset + 8)) 0 = readHeader bytes offset := by
  -- Byte `i` of the eight extracted bytes is byte `offset + i` of the buffer.
  simp only [readHeader, ByteArray.size_extract, ByteArray.getElem_extract, Nat.zero_add,
    dite_eq_right (show ¬bytes.size < offset + 8 by omega),
    dite_eq_right (show ¬min (offset + 8) bytes.size - offset < 0 + 8 by omega)]

/-- The header of a type and a length that fits reads back as that type and length. -/
private theorem readHeader_encodeHeader (type : UInt16) (length : Nat) (h : length < 2 ^ 32) :
    readHeader (encodeHeader type length) 0 = .ok ⟨type, length⟩ := by
  have ht : ByteOrder.ofBE (ByteOrder.toBE 2 type.toNat).toList = type.toNat :=
    ByteOrder.ofBE_toBE_of_lt type.toNat_lt
  have hl : ByteOrder.ofLE (ByteOrder.toLE 4 length) = length := by
    rw [ByteOrder.ofLE_toLE, Nat.mod_eq_of_lt h]
  obtain ⟨a, b, hab⟩ : ∃ a b, (ByteOrder.toBE 2 type.toNat).toList = [a, b] :=
    match (ByteOrder.toBE 2 type.toNat).toList, ByteOrder.length_toList_toBE 2 type.toNat with
    | [a, b], _ => ⟨a, b, rfl⟩
  generalize hv : ByteOrder.toLE 4 length = v at hl
  rw [vector_four v] at hv hl
  have he : encodeHeader type length = ⟨#[a, b, v[0], v[1], v[2], v[3], 0, 0]⟩ := by
    rw [encodeHeader, hab, hv]
    rfl
  rw [he, readHeader_mk, hl, ← hab, ht, UInt16.ofNat_toNat]
  rfl

/-- Eight bytes that read as a header are the header of the type and length they hold. -/
private theorem eq_encodeHeader_of_readHeader {b0 b1 b2 b3 b4 b5 b6 b7 : UInt8} {header : Header}
    (h : readHeader ⟨#[b0, b1, b2, b3, b4, b5, b6, b7]⟩ 0 = .ok header) :
    header.length < 2 ^ 32 ∧
      (⟨#[b0, b1, b2, b3, b4, b5, b6, b7]⟩ : ByteArray) =
        encodeHeader header.type header.length := by
  rw [readHeader_mk] at h
  by_cases hr : b6 ≠ 0 ∨ b7 ≠ 0
  · rw [ite_eq_left hr] at h
    cases h
  rw [ite_eq_right hr] at h
  cases h
  obtain ⟨h6, h7⟩ := not_or.mp hr
  rw [Decidable.not_not] at h6 h7
  subst h6 h7
  have h01 : ByteOrder.ofBE [b0, b1] % 2 ^ 16 = ByteOrder.ofBE [b0, b1] := by
    have := ByteOrder.ofBE_lt [b0, b1]
    rw [List.length_cons, List.length_cons, List.length_nil] at this
    exact Nat.mod_eq_of_lt (by omega)
  have hn : (ByteOrder.toBE 2 (ByteOrder.ofBE [b0, b1])).toList = [b0, b1] :=
    ByteOrder.toList_toBE_ofBE [b0, b1]
  have hl := ByteOrder.ofLE_lt #v[b2, b3, b4, b5]
  refine ⟨by omega, ?_⟩
  rw [encodeHeader]
  dsimp only
  rw [UInt16.toNat_ofNat', h01, hn, ByteOrder.toLE_ofLE]
  rfl

/-- The header at the start of a record is its type and the length of its data.

The record may sit anywhere in the bytes, after any prefix. -/
theorem readHeader_append_encodeHeader (pre rest : ByteArray) (type : UInt16) (length : Nat)
    (h : length < 2 ^ 32) :
    readHeader (pre ++ encodeHeader type length ++ rest) pre.size = .ok ⟨type, length⟩ := by
  have hx := @ByteArray.extract_append_size_add pre (encodeHeader type length ++ rest) 0 8
  rw [Nat.add_zero, ByteArray.extract_append_eq_left (size_encodeHeader type length).symm,
    ← ByteArray.append_assoc] at hx
  rw [← readHeader_extract _ _ (by simp only [ByteArray.size_append, size_encodeHeader]; omega),
    hx, readHeader_encodeHeader type length h]

/-- A header that reads holds eight bytes in range, and they encode its type and length.

Its length is below `2^32`. -/
theorem readHeader_eq_ok {bytes : ByteArray} {offset : Nat} {header : Header}
    (h : readHeader bytes offset = .ok header) :
    offset + 8 ≤ bytes.size ∧ header.length < 2 ^ 32 ∧
      bytes.extract offset (offset + 8) = encodeHeader header.type header.length := by
  have hs : offset + 8 ≤ bytes.size := Nat.le_of_not_lt fun hc => by
    rw [readHeader, dite_eq_left hc] at h
    cases h
  rw [← readHeader_extract _ _ hs] at h
  have hx : (bytes.extract offset (offset + 8)).size = 8 := by
    rw [ByteArray.size_extract]
    omega
  rw [eq_mk_of_size _ hx] at h ⊢
  exact ⟨hs, eq_encodeHeader_of_readHeader h⟩

/-! ### Encoding -/

/-- The fold of the encoding from any output succeeds when every data fits, and appends. -/
private theorem foldlM_encode_eq_ok (records : List Record) (out bytes : ByteArray) :
    records.foldlM (fun out record =>
        if record.data.size < 2 ^ 32 then
          (Except.ok (out ++ encodeHeader record.type record.data.size ++ record.data) :
            Except E2storeError ByteArray)
        else Except.error (E2storeError.dataTooLong record.data.size)) out = .ok bytes ↔
      (∀ record ∈ records, record.data.size < 2 ^ 32) ∧
        bytes = out ++ records.foldr (fun record out =>
          encodeHeader record.type record.data.size ++ record.data ++ out) .empty := by
  induction records generalizing out with
  | nil =>
    rw [List.foldlM_nil, List.foldr_nil, ByteArray.append_empty]
    exact ⟨fun h => by cases h; exact ⟨nofun, rfl⟩, fun ⟨_, h⟩ => by rw [h]; rfl⟩
  | cons r rs ih =>
    rw [List.foldlM_cons, List.foldr_cons, List.forall_mem_cons]
    by_cases hr : r.data.size < 2 ^ 32
    · rw [ite_eq_left hr]
      refine (ih _).trans ?_
      simp only [hr, true_and, ByteArray.append_assoc]
    · rw [ite_eq_right hr]
      exact ⟨fun h => (nomatch h), fun ⟨⟨h, _⟩, _⟩ => absurd h hr⟩

/-- The encoding succeeds exactly when every data has fewer than `2^32` bytes.

It then gives each record's header and data, one record after the other. -/
theorem encode_eq_ok_iff {records : List Record} {bytes : ByteArray} :
    encode records = .ok bytes ↔ (∀ record ∈ records, record.data.size < 2 ^ 32) ∧
      bytes = records.foldr (fun record out =>
        encodeHeader record.type record.data.size ++ record.data ++ out) .empty := by
  rw [encode, foldlM_encode_eq_ok, ByteArray.empty_append]

/-! ### Decoding -/

/-- A record after a prefix has its header at the end of the prefix, and its data after it. -/
private theorem record_after (pre post : ByteArray) (r : Record) (h : r.data.size < 2 ^ 32) :
    readHeader (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)) pre.size =
        .ok ⟨r.type, r.data.size⟩ ∧
      (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)).extract
        (pre.size + 8) (pre.size + 8 + r.data.size) = r.data := by
  refine ⟨?_, ?_⟩
  · rw [ByteArray.append_assoc, ← ByteArray.append_assoc]
    exact readHeader_append_encodeHeader _ _ _ _ h
  · have hd := @ByteArray.extract_append_size_add' (encodeHeader r.type r.data.size)
      (r.data ++ post) 0 r.data.size 8 (size_encodeHeader _ _).symm
    rw [Nat.add_zero, ByteArray.extract_append_eq_left rfl, ← ByteArray.append_assoc] at hd
    rw [Nat.add_assoc, ByteArray.extract_append_size_add, hd]

/-- Decoding at the header of a record reads the record, then goes on after its data. -/
private theorem decodeFrom_record (pre post : ByteArray) (r : Record) (acc : Array Record)
    (h : r.data.size < 2 ^ 32) :
    decodeFrom (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)) pre.size acc =
      decodeFrom (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post))
        (pre.size + 8 + r.data.size) (acc.push r) := by
  obtain ⟨hr, he⟩ := record_after pre post r h
  have hs : (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)).size =
      pre.size + 8 + r.data.size + post.size := by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, size_encodeHeader]
    omega
  rw [decodeFrom.eq_1 _ pre.size, ite_eq_left (by omega), hr]
  dsimp only
  rw [ite_eq_right (by omega), he]

/-- Decoding the bytes of records after a prefix reads them back. -/
private theorem decodeFrom_foldr (records : List Record) (pre : ByteArray) (acc : Array Record)
    (h : ∀ record ∈ records, record.data.size < 2 ^ 32) :
    decodeFrom (pre ++ records.foldr (fun record out =>
        encodeHeader record.type record.data.size ++ record.data ++ out) .empty) pre.size acc =
      .ok (acc.toList ++ records) := by
  induction records generalizing pre acc with
  | nil =>
    rw [List.foldr_nil, ByteArray.append_empty, decodeFrom.eq_1, ite_eq_right (Nat.lt_irrefl _),
      List.append_nil]
  | cons r rs ih =>
    have hr := h r List.mem_cons_self
    have := ih (pre ++ encodeHeader r.type r.data.size ++ r.data) (acc.push r)
      fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    rw [ByteArray.size_append, ByteArray.size_append, size_encodeHeader, ByteArray.append_assoc,
      ByteArray.append_assoc, Array.toList_push, List.append_assoc, List.singleton_append] at this
    rw [List.foldr_cons, decodeFrom_record _ _ _ _ hr, ByteArray.append_assoc]
    exact this

/-- In the bytes of records after a prefix, each record sits at its position. -/
private theorem record_at_foldr (records : List Record) (pre : ByteArray)
    (h : ∀ record ∈ records, record.data.size < 2 ^ 32) (k : Nat) (hk : k < records.length) :
    readHeader (pre ++ records.foldr (fun record out =>
        encodeHeader record.type record.data.size ++ record.data ++ out) .empty)
        ((recordStarts pre.size records).getD k 0) =
        .ok ⟨records[k].type, records[k].data.size⟩ ∧
      (pre ++ records.foldr (fun record out =>
        encodeHeader record.type record.data.size ++ record.data ++ out) .empty).extract
        ((recordStarts pre.size records).getD k 0 + 8)
        ((recordStarts pre.size records).getD k 0 + 8 + records[k].data.size) =
        records[k].data := by
  induction records generalizing pre k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons r rs ih =>
    cases k with
    | zero =>
      rw [List.foldr_cons]
      exact record_after pre _ r (h r List.mem_cons_self)
    | succ k =>
      have := ih (pre ++ encodeHeader r.type r.data.size ++ r.data)
        (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) k (by simpa using hk)
      rw [ByteArray.size_append, ByteArray.size_append, size_encodeHeader, ByteArray.append_assoc,
        ByteArray.append_assoc] at this
      rw [List.foldr_cons, recordStarts, List.getD_cons_succ, List.getElem_cons_succ,
        ByteArray.append_assoc]
      exact this

/-- Bytes that decode from a position hold the bytes of the records read from there. -/
private theorem decodeFrom_eq_ok (bytes : ByteArray) (offset : Nat) (acc : Array Record)
    (records : List Record) (h : decodeFrom bytes offset acc = .ok records) :
    ∃ rs, records = acc.toList ++ rs ∧ (∀ r ∈ rs, r.data.size < 2 ^ 32) ∧
      bytes.extract offset bytes.size = rs.foldr (fun record out =>
        encodeHeader record.type record.data.size ++ record.data ++ out) .empty := by
  revert h
  fun_induction decodeFrom bytes offset acc with
  | case1 | case2 => intro h; cases h
  | case4 offset acc hlt =>
    intro h
    cases h
    exact ⟨[], (List.append_nil _).symm, nofun, ByteArray.extract_eq_empty_iff.mpr (by omega)⟩
  | case3 offset acc hlt header hheader hdata data ih =>
    intro h
    obtain ⟨rs, rfl, hs, he⟩ := ih h
    obtain ⟨h8, hl, hx⟩ := readHeader_eq_ok hheader
    have hsize : data.size = header.length := by
      show (bytes.extract _ _).size = _
      rw [ByteArray.size_extract]
      omega
    refine ⟨⟨header.type, data⟩ :: rs, ?_, ?_, ?_⟩
    · rw [Array.toList_push, List.append_assoc, List.singleton_append]
    · rw [List.forall_mem_cons, hsize]
      exact ⟨hl, hs⟩
    · rw [ByteArray.extract_eq_extract_append_extract (offset + 8) (by omega) (by omega),
        ByteArray.extract_eq_extract_append_extract (i := offset + 8)
          (offset + 8 + header.length) (by omega) (by omega),
        he, hx, List.foldr_cons]
      dsimp only
      rw [hsize, ByteArray.append_assoc]

/-- Records read back from the bytes they encode to. -/
theorem decode_encode {records : List Record} {bytes : ByteArray}
    (h : encode records = .ok bytes) : decode bytes = .ok records := by
  obtain ⟨hs, rfl⟩ := encode_eq_ok_iff.mp h
  have := decodeFrom_foldr records .empty #[] hs
  rw [ByteArray.empty_append, ByteArray.size_empty, Array.toList_empty, List.nil_append] at this
  exact this

/-- Bytes that decode are the encoding of their records. -/
theorem encode_decode {records : List Record} {bytes : ByteArray}
    (h : decode bytes = .ok records) : encode records = .ok bytes := by
  obtain ⟨rs, rfl, hs, he⟩ := decodeFrom_eq_ok bytes 0 #[] records h
  rw [ByteArray.extract_zero_size] at he
  exact encode_eq_ok_iff.mpr ⟨hs, he⟩

/-- A file decodes exactly when its records start with a Version record.

Every Version record must also have no data. -/
theorem decodeFile_eq_ok_iff {bytes : ByteArray} {records : List Record} :
    decodeFile bytes = .ok records ↔
      decode bytes = .ok records ∧ records.head?.map (·.type) = some VERSION ∧
        ∀ record ∈ records, record.type = VERSION → record.data.size = 0 := by
  unfold decodeFile
  cases h : decode bytes with
  | error e => simp [bind, Except.bind]
  | ok rs =>
    have hall : rs.all (fun record => record.type != VERSION || record.data.size == 0) = true ↔
        ∀ record ∈ rs, record.type = VERSION → record.data.size = 0 := by
      simp only [List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact forall₂_congr fun r _ => by by_cases a : r.type = VERSION <;> simp [a]
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
    by_cases hv : rs.head?.map (·.type) = some VERSION <;>
      by_cases ha : rs.all (fun record => record.type != VERSION || record.data.size == 0) = true
    · simp only [hv, ha, ite_true]
      constructor
      · intro h1
        cases h1
        exact ⟨rfl, hv, hall.mp ha⟩
      · rintro ⟨h2, -⟩
        exact h2
    all_goals
      constructor
      · intro h1
        simp [hv, ha] at h1
      · rintro ⟨h2, h3, h4⟩
        cases h2
        simp_all

/-- In bytes that decode, each record sits at its position.

That position is where the sizes of the records before it put it.

Its header reads there, and its data follows the header. -/
theorem record_at {bytes : ByteArray} {records : List Record} (h : decode bytes = .ok records)
    {k : Nat} (hk : k < records.length) :
    readHeader bytes ((recordStarts 0 records).getD k 0) =
        .ok ⟨records[k].type, records[k].data.size⟩ ∧
      bytes.extract ((recordStarts 0 records).getD k 0 + 8)
        ((recordStarts 0 records).getD k 0 + 8 + records[k].data.size) = records[k].data := by
  obtain ⟨hs, he⟩ := encode_eq_ok_iff.mp (encode_decode h)
  have := record_at_foldr records .empty hs k hk
  rw [ByteArray.empty_append, ByteArray.size_empty] at this
  rw [he]
  exact this

/-- There is one position for each record. -/
@[simp] theorem length_recordStarts (pos : Nat) (records : List Record) :
    (recordStarts pos records).length = records.length := by
  induction records generalizing pos with
  | nil => rfl
  | cons r rs ih => simp [recordStarts, ih]

/-- In bytes that decode, a record paired with its position sits there.

Its header reads at the position, and its data follows the header. -/
theorem record_at_mem {bytes : ByteArray} {records : List Record}
    (h : decode bytes = .ok records) {pos : Nat} {r : Record}
    (hm : (pos, r) ∈ (recordStarts 0 records).zip records) :
    readHeader bytes pos = .ok ⟨r.type, r.data.size⟩ ∧
      bytes.extract (pos + 8) (pos + 8 + r.data.size) = r.data := by
  obtain ⟨k, hk, he⟩ := List.getElem_of_mem hm
  rw [List.getElem_zip, Prod.mk.injEq] at he
  obtain ⟨hp, hr⟩ := he
  have hk' : k < records.length := by simpa using hk
  have := record_at h hk'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hk'),
    Option.getD_some, hp] at this
  rw [← hr]
  exact this

/-! ### Index records -/

/-- The data of an index that reads has 16 bytes plus 8 bytes per offset. -/
theorem readIndex_size {data : ByteArray} {index : Index}
    (h : readIndex data = .ok index) : data.size = 16 + 8 * index.offsets.length := by
  unfold readIndex at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · nomatch h
  rename_i hs
  obtain rfl := Except.ok.inj h
  simp only [List.length_map, List.length_range]
  exact Decidable.of_not_not hs

/-- An offset read from 8 bytes lies in `[-2^63, 2^63)`. -/
private theorem readInt64_bounds (data : ByteArray) (pos : Nat) :
    -2 ^ 63 ≤ readInt64 data pos ∧ readInt64 data pos < 2 ^ 63 :=
  ⟨by simpa [readInt64] using BitVec.le_toInt (BitVec.ofNat 64 (Ssz.readUint data pos 8)),
    by simpa [readInt64] using
      BitVec.toInt_lt (x := BitVec.ofNat 64 (Ssz.readUint data pos 8))⟩

/-- An offset read from 8 bytes, modulo `2^64`, is the same bytes read unsigned. -/
private theorem readInt64_emod (data : ByteArray) (pos : Nat) :
    (readInt64 data pos % 2 ^ 64).toNat = Ssz.readUint data pos 8 := by
  have fits := Ssz.readUint_lt data pos 8
  unfold readInt64
  rw [BitVec.toInt_emod_two_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, Int.toNat_natCast]

/-- An unsigned read of 8 bytes is below `2^64`. -/
private theorem readUint_eight_lt (data : ByteArray) (pos : Nat) :
    Ssz.readUint data pos 8 < 2 ^ 64 := by
  simpa using Ssz.readUint_lt data pos 8

/-- The `count` words of 8 bytes from `pos`, each written back from its unsigned read. -/
private theorem extract_eq_flatMap (data : ByteArray) (pos : Nat) :
    ∀ count, pos + 8 * count ≤ data.size →
      (data.extract pos (pos + 8 * count)).data.toList =
        (List.range count).flatMap fun i =>
          (ByteOrder.toLE 8 (Ssz.readUint data (pos + 8 * i) 8)).toList
  | 0, _ => by simp
  | count + 1, h => by
    have ih := extract_eq_flatMap data pos count (by omega)
    have slice := Ssz.uintBytes_readUint_slice data (pos + 8 * count) 8 (by omega)
    rw [List.range_succ, List.flatMap_append, ← ih, List.flatMap_singleton,
      show pos + 8 * (count + 1) = pos + 8 * count + 8 by omega,
      ← Ssz.extract_join data (middle := pos + 8 * count) (by omega) (by omega),
      ByteArray.data_append, Array.toList_append, ← slice]
    rfl

/-- Data of `16 + 8 count` bytes is its first number, its offsets and its count, written back. -/
private theorem toList_of_size {data : ByteArray} {count : Nat} (h : data.size = 16 + 8 * count) :
    data.data.toList = (ByteOrder.toLE 8 (Ssz.readUint data 0 8)).toList ++
      ((List.range count).map fun i => readInt64 data (8 + 8 * i)).flatMap
        (fun offset => (ByteOrder.toLE 8 (offset % 2 ^ 64).toNat).toList) ++
      (ByteOrder.toLE 8 (Ssz.readUint data (8 + 8 * count) 8)).toList := by
  have first := Ssz.uintBytes_readUint_slice data 0 8 (by omega)
  have last := Ssz.uintBytes_readUint_slice data (8 + 8 * count) 8 (by omega)
  have middle := extract_eq_flatMap data 8 count (by omega)
  simp only [List.flatMap_map, readInt64_emod]
  rw [← middle]
  have whole : data = data.extract 0 8 ++ data.extract 8 (8 + 8 * count) ++
      data.extract (8 + 8 * count) (8 + 8 * count + 8) := by
    rw [Ssz.extract_join data (by omega) (by omega),
      Ssz.extract_join data (by omega) (by omega),
      show 8 + 8 * count + 8 = data.size by omega, ByteArray.extract_zero_size]
  conv => lhs; rw [whole]
  rw [Nat.zero_add] at first
  rw [ByteArray.data_append, ByteArray.data_append, Array.toList_append, Array.toList_append,
    ← first, ← last]
  rfl

/-- Two lists of offsets in range, whose 8-byte writings agree, are the same list. -/
private theorem offsets_inj {xs ys : List Int}
    (hx : ∀ x ∈ xs, -2 ^ 63 ≤ x ∧ x < 2 ^ 63) (hy : ∀ y ∈ ys, -2 ^ 63 ≤ y ∧ y < 2 ^ 63)
    (h : xs.flatMap (fun offset => (ByteOrder.toLE 8 (offset % 2 ^ 64).toNat).toList) =
      ys.flatMap (fun offset => (ByteOrder.toLE 8 (offset % 2 ^ 64).toNat).toList)) :
    xs = ys := by
  -- On offsets in range, the 8-byte writing is injective.
  --
  -- So the lemma on joined pieces applies to the lists with their range attached.
  have joined := EthLib.Base.flatMap_inj_of_length
    (f := fun x : {x : Int // -2 ^ 63 ≤ x ∧ x < 2 ^ 63} =>
      (ByteOrder.toLE 8 (x.1 % 2 ^ 64).toNat).toList)
    (n := 8) (by decide) (fun _ => by simp)
    (fun x y hxy => Subtype.ext (by
      have := ByteOrder.toLE_inj (k := 8) (by have := x.2; simp; omega)
        (by have := y.2; simp; omega) (Vector.toList_inj.mp hxy)
      have := x.2
      have := y.2
      omega))
    (l := xs.attachWith _ hx) (l' := ys.attachWith _ hy) (by simpa using h)
  simpa using congrArg List.unattach joined

/-- The data of an index record reads as an index exactly when it holds its numbers, 8 bytes each.

The first number and the count are below `2^64`, and each offset lies in `[-2^63, 2^63)`. -/
theorem readIndex_eq_ok_iff {data : ByteArray} {index : Index} :
    readIndex data = .ok index ↔
      index.start < 2 ^ 64 ∧ index.offsets.length < 2 ^ 64 ∧
        (∀ offset ∈ index.offsets, -2 ^ 63 ≤ offset ∧ offset < 2 ^ 63) ∧
        -- Each number takes 8 little-endian bytes: the first number, the offsets, then the count.
        --
        -- The offsets come in order, each as its two's complement, its value modulo `2^64`.
        data.data.toList = (ByteOrder.toLE 8 index.start).toList ++
          index.offsets.flatMap (fun offset => (ByteOrder.toLE 8 (offset % 2 ^ 64).toNat).toList) ++
          (ByteOrder.toLE 8 index.offsets.length).toList := by
  constructor
  · intro h
    unfold readIndex at h
    split at h
    · cases h
    dsimp only at h
    split at h
    · nomatch h
    rename_i hs
    obtain rfl := Except.ok.inj h
    have hc : data.size = 16 + 8 * Ssz.readUint data (data.size - 8) 8 :=
      Decidable.of_not_not hs
    have hl := readUint_eight_lt data (data.size - 8)
    dsimp only
    refine ⟨readUint_eight_lt data 0, ?_, ?_, ?_⟩
    · simp only [List.length_map, List.length_range]
      exact hl
    · intro offset ho
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ho
      exact readInt64_bounds data _
    · rw [toList_of_size hc]
      simp only [List.length_map, List.length_range]
      rw [show 8 + 8 * Ssz.readUint data (data.size - 8) 8 = data.size - 8 by omega]
  · rintro ⟨hstart, hlen, hrange, hbytes⟩
    have hsize : data.size = 16 + 8 * index.offsets.length := by
      have := congrArg List.length hbytes
      simp only [Array.length_toList, List.length_append, Vector.length_toList,
        List.length_flatMap] at this
      simp [List.map_const'] at this
      omega
    have hread := toList_of_size hsize
    rw [hbytes] at hread
    obtain ⟨front, hlast⟩ := List.append_inj' hread (by simp)
    obtain ⟨hfirst, hmiddle⟩ := List.append_inj front (by simp)
    have hs := ByteOrder.toLE_inj (k := 8) (by simpa using hstart)
      (by simpa using readUint_eight_lt data 0) (Vector.toList_inj.mp hfirst)
    have hc := ByteOrder.toLE_inj (k := 8) (by simpa using hlen)
      (by simpa using readUint_eight_lt data _) (Vector.toList_inj.mp hlast)
    have ho := offsets_inj hrange
      (fun offset ho => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp ho
        exact readInt64_bounds data _) hmiddle
    have hcount : Ssz.readUint data (data.size - 8) 8 = index.offsets.length := by
      rw [show data.size - 8 = 8 + 8 * index.offsets.length by omega]
      exact hc.symm
    have h16 : ¬data.size < 16 := by omega
    have hfit : ¬data.size ≠ 16 + 8 * index.offsets.length := by omega
    unfold readIndex
    simp only [h16, hcount, hfit, ↓reduceIte, ← hs, ← ho]

end EthLib.Serialization.E2store

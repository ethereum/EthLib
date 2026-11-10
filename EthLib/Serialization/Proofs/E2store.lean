module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Serialization.E2store

/-!
# `Serialization.Proofs.E2store`

The e2store records read back.

Writing records and reading the bytes back gives the same records.

Reading bytes and writing the records back gives the same bytes.

So the encoding is a bijection onto the bytes that decode.

Its domain is the record lists whose data each have fewer than `2^32` bytes.

A file decodes exactly when its records start with a Version record, and no Version record has data.
-/

@[expose] public section

namespace EthLib.Serialization.E2store

open EthLib.Base

/-! ### Headers -/

/-- A header is eight bytes. -/
@[simp] theorem size_encodeHeader (type : UInt16) (length : Nat) :
    (encodeHeader type length).size = 8 := by
  simp [encodeHeader, ByteArray.size, natToBytes_length]

/-- The header at the start of eight bytes, read from their values. -/
private theorem readHeader_mk (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    readHeader ⟨#[b0, b1, b2, b3, b4, b5, b6, b7]⟩ 0 =
      if b6 ≠ 0 ∨ b7 ≠ 0 then .error .reservedNotZero
      else .ok ⟨UInt16.ofNat (bytesToNat [b0, b1]), bytesToUint #v[b2, b3, b4, b5]⟩ :=
  rfl

/-- Eight bytes are the array of their values. -/
private theorem eq_mk_of_size (x : ByteArray) (h : x.size = 8) :
    x = ⟨#[byteAt x 0, byteAt x 1, byteAt x 2, byteAt x 3, byteAt x 4, byteAt x 5, byteAt x 6,
      byteAt x 7]⟩ := by
  refine eq_of_byteAt h fun i => ?_
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | i + 8 => rw [byteAt_of_size_le (by omega), byteAt_of_size_le (Nat.le_add_left 8 i)]

/-- The header at a position is the header at the start of the eight bytes there. -/
private theorem readHeader_extract (bytes : ByteArray) (offset : Nat)
    (h : offset + 8 ≤ bytes.size) :
    readHeader (bytes.extract offset (offset + 8)) 0 = readHeader bytes offset := by
  have hb (i : Nat) (hi : i < 8) :
      byteAt (bytes.extract offset (offset + 8)) (0 + i) = byteAt bytes (offset + i) := by
    rw [Nat.zero_add, byteAt_extract, ite_eq_left (by omega)]
  simp only [readHeader, ByteArray.size_extract, hb 0 (by omega), hb 1 (by omega),
    hb 2 (by omega), hb 3 (by omega), hb 4 (by omega), hb 5 (by omega), hb 6 (by omega),
    hb 7 (by omega)]
  rw [ite_eq_right (show ¬bytes.size < offset + 8 by omega),
    ite_eq_right (show ¬min (offset + 8) bytes.size - offset < 0 + 8 by omega)]

/-- A vector of four bytes is the vector of its four entries. -/
private theorem vector_four (v : Vector UInt8 4) : v = #v[v[0], v[1], v[2], v[3]] := by
  ext i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl

/-- The header of a type and a length that fits reads back as that type and length. -/
private theorem readHeader_encodeHeader (type : UInt16) (length : Nat) (h : length < 2 ^ 32) :
    readHeader (encodeHeader type length) 0 = .ok ⟨type, length⟩ := by
  have ht : bytesToNat (natToBytes 2 type.toNat) = type.toNat :=
    bytesToNat_natToBytes_of_lt type.toNat_lt
  have hl : bytesToUint (uintToBytes 4 length) = length := by
    rw [bytesToUint_uintToBytes, Nat.mod_eq_of_lt h]
  obtain ⟨a, b, hab⟩ : ∃ a b, natToBytes 2 type.toNat = [a, b] :=
    match natToBytes 2 type.toNat, natToBytes_length 2 type.toNat with
    | [a, b], _ => ⟨a, b, rfl⟩
  generalize hv : uintToBytes 4 length = v at hl
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
  have h01 : bytesToNat [b0, b1] % 2 ^ 16 = bytesToNat [b0, b1] := by
    have := bytesToNat_lt [b0, b1]
    rw [List.length_cons, List.length_cons, List.length_nil] at this
    exact Nat.mod_eq_of_lt (by omega)
  have hn : natToBytes 2 (bytesToNat [b0, b1]) = [b0, b1] := natToBytes_bytesToNat [b0, b1]
  have hl := bytesToUint_lt #v[b2, b3, b4, b5]
  refine ⟨by omega, ?_⟩
  rw [encodeHeader]
  dsimp only
  rw [UInt16.toNat_ofNat', h01, hn, uintToBytes_bytesToUint]
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
    rw [readHeader, ite_eq_left hc] at h
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
        else Except.error E2storeError.dataTooLong) out = .ok bytes ↔
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

/-- Decoding at the header of a record reads the record, then goes on after its data. -/
private theorem decodeFrom_record (pre post : ByteArray) (r : Record) (acc : Array Record)
    (h : r.data.size < 2 ^ 32) :
    decodeFrom (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)) pre.size acc =
      decodeFrom (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post))
        (pre.size + 8 + r.data.size) (acc.push r) := by
  have hr : readHeader (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)) pre.size =
      .ok ⟨r.type, r.data.size⟩ := by
    rw [ByteArray.append_assoc, ← ByteArray.append_assoc]
    exact readHeader_append_encodeHeader _ _ _ _ h
  have hs : (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)).size =
      pre.size + 8 + r.data.size + post.size := by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, size_encodeHeader]
    omega
  have hd := @ByteArray.extract_append_size_add' (encodeHeader r.type r.data.size)
    (r.data ++ post) 0 r.data.size 8 (size_encodeHeader _ _).symm
  rw [Nat.add_zero, ByteArray.extract_append_eq_left rfl, ← ByteArray.append_assoc] at hd
  have he : (pre ++ (encodeHeader r.type r.data.size ++ r.data ++ post)).extract
      (pre.size + 8) (pre.size + 8 + r.data.size) = r.data := by
    rw [Nat.add_assoc, ByteArray.extract_append_size_add, hd]
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

end EthLib.Serialization.E2store

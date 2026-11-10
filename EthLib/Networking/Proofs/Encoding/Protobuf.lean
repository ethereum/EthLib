module

public import EthLib.Networking.Encoding.Protobuf
public import EthLib.Networking.Proofs.Encoding.Varint

/-!
# Proofs: the protobuf wire format

- Reading a varint, a key or a record back from its encoding returns it, whatever bytes follow.
- Reading the records of an encoded sequence returns the sequence.
- The key needs a field number in range; a record also needs a value shorter than `2^64` bytes.
- Reading a serialized message returns its records, for fields in range and under `2^64` bytes.
- The values of one field follow the order of the records.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Encoding.Protobuf

open EthLib.Networking.Encoding.Protobuf
open EthLib.Networking.Encoding

/-- Reading a varint back from its encoding returns it, and the bytes after it. -/
theorem readVarint_encode (v : UInt64) (rest : List UInt8) :
    readVarint (Varint.encode v ++ rest) = .ok (v, rest) := by
  have hlt : v.toNat < Varint.groupSize ^ Varint.maxLength := by
    have := v.toNat_lt_size
    simp only [UInt64.size, Varint.groupSize, Varint.payloadBits, Varint.maxLength] at *
    omega
  have hg : Varint.groups Varint.maxLength (Varint.encode v) = .ok (Varint.encode v) :=
    Proofs.Encoding.Varint.groups_encodeAux (by decide) hlt
  have hv : Varint.valueOf (Varint.encode v) = v.toNat :=
    Proofs.Encoding.Varint.valueOf_encodeAux hlt
  have hs : ¬ 2 ^ 64 ≤ v.toNat := by have := v.toNat_lt_size; simp [UInt64.size] at this; omega
  simp [readVarint, Proofs.Encoding.Varint.split_encode, hg, hv, hs, Except.mapError, bind,
    Except.bind, pure, Except.pure]

/-- Reading a key back from its encoding returns its field number and its wire type below 8. -/
theorem readKey_encodeKey {field wire : Nat} (h0 : 0 < field) (hmax : field ≤ maxField)
    (hw : wire < 8) (rest : List UInt8) :
    readKey (encodeKey field wire ++ rest) = .ok (field, wire, rest) := by
  have hk : (UInt64.ofNat (field * 8 + wire)).toNat = field * 8 + wire := by
    rw [UInt64.toNat_ofNat_of_lt']
    simp only [maxField] at hmax
    simp only [UInt64.size]
    omega
  have hf : (field * 8 + wire) / 8 = field := by omega
  have hm : (field * 8 + wire) % 8 = wire := by omega
  have hc : ¬ (field = 0 ∨ maxField < field) := by omega
  simp only [readKey, encodeKey, readVarint_encode, bind, Except.bind, hk, hf, hm]
  simp only [hc, ↓reduceIte]
  rfl

/-- Reading `n` bytes from `n` bytes and more returns them, and the bytes after them. -/
theorem readFixed_append {n : Nat} (bytes : Vector UInt8 n) (rest : List UInt8) :
    readFixed n (bytes.toList ++ rest) = .ok (bytes, rest) := by
  have hl : bytes.toList.length = n := bytes.length_toList
  have hle : n ≤ (bytes.toList ++ rest).length := by simp [hl]
  simp only [readFixed, dite_eq_left_of_eq_true (eq_true hle)]
  congr 2
  · apply Vector.ext
    intro i hi
    simp [Vector.getElem_toList, hl]
  · simp [hl]

/-- Reading a length-delimited value back from its encoding returns it. -/
theorem readLen_encodeValue {field : Nat} {bytes : ByteArray} (h : bytes.size < 2 ^ 64)
    (rest : List UInt8) : readLen (encodeValue field (.len bytes) ++ rest) = .ok (bytes, rest) := by
  have hn : (UInt64.ofNat bytes.size).toNat = bytes.size := by
    rw [UInt64.toNat_ofNat_of_lt']
    simpa [UInt64.size] using h
  have hle : bytes.size ≤ (bytes.data.toList ++ rest).length := by simp
  simp only [encodeValue, List.append_assoc, readLen, readVarint_encode, bind, Except.bind, hn,
    readFixed, dite_eq_left_of_eq_true (eq_true hle)]
  simp [pure, Except.pure]

/-- A key takes at least one byte. -/
theorem encodeKey_ne_nil (field wire : Nat) : encodeKey field wire ≠ [] :=
  Proofs.Encoding.Varint.encodeAux_ne_nil (by decide)

/-- Reading a well-formed record back from its encoding returns it. -/
theorem readRecord_encodeRecord {r : Record} (h : r.WellFormed) (rest : List UInt8) :
    readRecord (encodeRecord r ++ rest) = .ok (r, rest) := by
  obtain ⟨field, value⟩ := r
  obtain ⟨h0, hmax, hv⟩ := h
  cases value with
  | varint v =>
    simp [readRecord, encodeRecord, encodeValue, Value.wireType, List.append_assoc,
      readKey_encodeKey h0 hmax, readScalar, readVarint_encode, bind, Except.bind, pure,
      Except.pure, Except.map]
  | i64 bytes =>
    simp [readRecord, encodeRecord, encodeValue, Value.wireType, List.append_assoc,
      readKey_encodeKey h0 hmax, readScalar, readFixed_append, bind, Except.bind, pure,
      Except.pure, Except.map]
  | len bytes =>
    simp only [readRecord, encodeRecord, Value.wireType, List.append_assoc]
    rw [readKey_encodeKey h0 hmax (by decide)]
    simp [readScalar, readLen_encodeValue hv, bind, Except.bind, pure, Except.pure, Except.map]
  | group =>
    have hk := List.length_pos_iff.mpr (encodeKey_ne_nil field 4)
    obtain ⟨k, hk'⟩ : ∃ k, (encodeKey field 4 ++ rest).length = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by simp; omega)).symm⟩
    simp only [readRecord, encodeRecord, encodeValue, Value.wireType, List.append_assoc]
    rw [readKey_encodeKey h0 hmax (by decide)]
    simp only [bind, Except.bind, ite_true, hk', skipGroup]
    rw [readKey_encodeKey h0 hmax (by decide)]
    simp [pure, Except.pure]
  | i32 bytes =>
    simp [readRecord, encodeRecord, encodeValue, Value.wireType, List.append_assoc,
      readKey_encodeKey h0 hmax, readScalar, readFixed_append, bind, Except.bind, pure,
      Except.pure, Except.map]

/-- A record takes at least two bytes: its key, and a value or an end key. -/
theorem two_le_length_encodeRecord (r : Record) : 2 ≤ (encodeRecord r).length := by
  obtain ⟨field, value⟩ := r
  have hk := List.length_pos_iff.mpr (encodeKey_ne_nil field value.wireType)
  have hvar (v : UInt64) : 0 < (Varint.encode v).length := List.length_pos_iff.mpr
    (Proofs.Encoding.Varint.encodeAux_ne_nil (n := v.toNat) (fuel := Varint.maxLength) (by decide))
  simp only [encodeRecord, List.length_append]
  cases value with
  | varint v => have := hvar v; simp only [encodeValue]; exact Nat.add_le_add hk this
  | i64 bytes => simp only [encodeValue, Vector.length_toList]; omega
  | len bytes =>
    have := hvar (UInt64.ofNat bytes.size)
    simp only [encodeValue, List.length_append]
    exact Nat.le_trans (Nat.add_le_add hk this) (by omega)
  | group =>
    have := List.length_pos_iff.mpr (encodeKey_ne_nil field 4)
    simp only [encodeValue]; omega
  | i32 bytes => simp only [encodeValue, Vector.length_toList]; omega

/-- The loop reads back well-formed records from their encoding, given one step per input byte. -/
theorem records_go_encodeRecords {rs : List Record} (h : ∀ r ∈ rs, r.WellFormed)
    (fuel : Nat) (hfuel : (encodeRecords rs).length ≤ fuel) (acc : List Record) :
    records.go fuel (encodeRecords rs) acc = .ok (acc.reverse ++ rs) := by
  induction rs generalizing fuel acc with
  | nil => simp [encodeRecords, records.go]
  | cons r rs ih =>
    have hr := h r (by simp)
    have h2 := two_le_length_encodeRecord r
    have he : encodeRecords (r :: rs) = encodeRecord r ++ encodeRecords rs := by
      simp [encodeRecords]
    rw [he, List.length_append] at hfuel
    obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hne : encodeRecord r ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil hne
    rw [he, hb]
    simp only [List.cons_append, records.go]
    rw [← List.cons_append, ← hb, readRecord_encodeRecord hr]
    simp only [bind, Except.bind]
    rw [ih (fun r' hr' => h r' (by simp [hr'])) fuel (by omega)]
    simp

/-- Reading the records of an encoded sequence of well-formed records returns the sequence. -/
theorem records_encodeRecords {rs : List Record} (h : ∀ r ∈ rs, r.WellFormed) :
    records (encodeRecords rs) = .ok rs := by
  have := records_go_encodeRecords h _ (Nat.le_refl _) []
  simpa [records] using this

/-- The bytes of a serialized message are the encoding of its records. -/
theorem toList_serialize (rs : List Record) :
    (serialize rs).data.toList = encodeRecords rs := by
  simp [serialize]

/-- A serialized message is as long as the encoding of its records. -/
theorem size_serialize (rs : List Record) :
    (serialize rs).size = (encodeRecords rs).length := by
  simp [serialize, ByteArray.size]

/-- A length-delimited value is no longer than the encoding of a sequence that holds it. -/
theorem size_le_of_mem {rs : List Record} {n : Nat} {b : ByteArray} (h : lenRecord n b ∈ rs) :
    b.size ≤ (encodeRecords rs).length := by
  induction rs with
  | nil => simp at h
  | cons r rs ih =>
    simp only [encodeRecords, List.flatMap_cons, List.length_append] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · simp only [lenRecord, encodeRecord, encodeValue, List.length_append, Array.length_toList]
      have : b.data.size = b.size := rfl
      omega
    · have := ih h; omega

/-- A length-delimited value in a message shorter than `2^64` bytes is shorter too. -/
theorem size_lt_of_mem {rs : List Record} {n : Nat} {b : ByteArray} (hm : lenRecord n b ∈ rs)
    (h : (serialize rs).size < 2 ^ 64) : b.size < 2 ^ 64 := by
  have := size_le_of_mem hm
  rw [size_serialize] at h
  omega

/-- Reading the records of a serialized message returns them.

Every field number must be in range, and the message shorter than `2^64` bytes. -/
theorem records_serialize {rs : List Record}
    (hf : ∀ r ∈ rs, 0 < r.field ∧ r.field ≤ maxField) (h : (serialize rs).size < 2 ^ 64) :
    records (serialize rs).data.toList = .ok rs := by
  have hw : ∀ r ∈ rs, r.WellFormed := by
    intro ⟨n, v⟩ hr
    refine ⟨(hf _ hr).1, (hf _ hr).2, ?_⟩
    cases v with
    | len b => exact size_lt_of_mem hr h
    | _ => trivial
  rw [toList_serialize, records_encodeRecords hw]

/-- No record holds a value of any field. -/
theorem valuesOf_nil (field : Nat) : valuesOf [] field = [] := rfl

/-- A record of the field puts its value first; a record of another field adds nothing. -/
theorem valuesOf_cons (r : Record) (rs : List Record) (field : Nat) :
    valuesOf (r :: rs) field =
      if r.field = field then r.value :: valuesOf rs field else valuesOf rs field := by
  by_cases h : r.field = field <;> simp [valuesOf, h]

/-- The values of two sequences of records follow one another. -/
theorem valuesOf_append (rs rs' : List Record) (field : Nat) :
    valuesOf (rs ++ rs') field = valuesOf rs field ++ valuesOf rs' field := by
  simp [valuesOf]

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Encoding.Protobuf.ProtobufError.code_injective
    (e₁ e₂ : ProtobufError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ProtobufError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Encoding.Protobuf

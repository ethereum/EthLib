module

public import EthLib.Networking.Encoding.Protobuf
public import EthLib.Networking.Proofs.Encoding.Varint

/-!
# Proofs: the protobuf wire format

- Reading a varint, a key or a record back from its encoding returns it, whatever bytes follow.
- Reading the records of an encoded sequence returns the sequence.
- Each holds for a well-formed record: a field number in range, and a short enough value.
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

/-- Reading a key back from its encoding returns its field number and wire type. -/
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

/-- The loop reads back well-formed records from their encoding, given a budget per byte. -/
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

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Encoding.Protobuf.ProtobufError.code_injective
    (e₁ e₂ : ProtobufError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ProtobufError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Encoding.Protobuf

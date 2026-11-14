module

public import EthLib.Networking.Quic.Tls.Wire
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: TLS wire fields

The readers recover written fields and preserve arbitrary trailing bytes.

Vector encoders reject lengths that do not fit, rather than reducing them modulo the field width.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Wire

open EthLib.Base (bind_ok_iff)

@[simp] theorem bytes_append (data rest : List UInt8) :
    bytes data.length (data ++ rest) = .ok (data, rest) := by
  simp [bytes]

@[simp] theorem uint_encode (width value : Nat) (rest : List UInt8) :
    uint width (Base.natToBytes width value ++ rest) =
      .ok (value % 256 ^ width, rest) := by
  simp [uint, bytes, Base.natToBytes_length, Base.bytesToNat_natToBytes,
    StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure]

@[simp] theorem uint_byte (value : UInt8) (rest : List UInt8) :
    uint 1 (value :: rest) = .ok (value.toNat, rest) := by
  simp [uint, bytes, Base.bytesToNat, StateT.bind, StateT.pure,
    bind, Except.bind, pure, Except.pure]

@[simp] theorem require_true (condition : Prop) [Decidable condition]
    (h : condition) (error : Error) (rest : List UInt8) :
    require condition error rest = .ok ((), rest) := by
  simp [require, h]

/-- Reading a bounded vector recovers all its bytes and leaves the following bytes. -/
theorem blob_encode (width minimum maximum : Nat) (data rest : List UInt8)
    (lower : minimum ≤ data.length) (upper : data.length ≤ maximum)
    (capacity : data.length < 256 ^ width) :
    blob width minimum maximum (Base.natToBytes width data.length ++ (data ++ rest)) =
      .ok (data, rest) := by
  simp [blob, Nat.mod_eq_of_lt capacity, lower, upper,
    StateT.bind, bind, Except.bind]

/-- A successful vector encoder writes its exact length followed by its exact content. -/
theorem encodeBlob_eq_ok_iff (width minimum maximum : Nat) (data encoded : List UInt8) :
    encodeBlob width minimum maximum data = .ok encoded ↔
      minimum ≤ data.length ∧ data.length ≤ maximum ∧ data.length < 256 ^ width ∧
      encoded = Base.natToBytes width data.length ++ data := by
  simp only [encodeBlob]
  split <;> simp_all [eq_comm] <;> omega

/-- An overlong vector is rejected even when its low length bytes would fit. -/
theorem encodeBlob_length_overflow (width minimum maximum : Nat) (data : List UInt8)
    (overflow : 256 ^ width ≤ data.length) :
    encodeBlob width minimum maximum data = .error .length := by
  simp [encodeBlob, Nat.not_lt.mpr overflow]

/-- Two-byte identifiers round trip, including values unknown to the protocol implementation. -/
@[simp] theorem codePoint_encode (value : CodePoint) (rest : List UInt8) :
    codePoint (Base.natToBytes 2 value.val ++ rest) = .ok (value, rest) := by
  have bound : value.val < 256 ^ 2 := value.isLt
  simp [codePoint, Nat.mod_eq_of_lt bound, value.isLt,
    StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure]

/-- Reading a fixed-size vector recovers the same vector. -/
@[simp] theorem vector_encode (n : Nat) (value : Vector UInt8 n) (rest : List UInt8) :
    vector n (value.toList ++ rest) = .ok (value, rest) := by
  have length : value.toList.length = n := by simp
  simp only [vector, ← length, bytes_append, bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure, ↓reduceDIte]
  simp only [Vector.toArray_toList, Vector.mk_toArray]

/-- Reading any successful vector encoding recovers its data and the following bytes. -/
theorem blob_encode_of_encode {width minimum maximum : Nat} {data encoded : List UInt8}
    (written : encodeBlob width minimum maximum data = .ok encoded) (rest : List UInt8) :
    blob width minimum maximum (encoded ++ rest) = .ok (data, rest) := by
  obtain ⟨lower, upper, capacity, rfl⟩ := (encodeBlob_eq_ok_iff ..).mp written
  simpa only [List.append_assoc] using
    blob_encode width minimum maximum data rest lower upper capacity

/-- A successful vector encoding adds exactly its length-field width. -/
theorem length_encodeBlob {width minimum maximum : Nat} {data encoded : List UInt8}
    (written : encodeBlob width minimum maximum data = .ok encoded) :
    encoded.length = width + data.length := by
  obtain ⟨_, _, _, rfl⟩ := (encodeBlob_eq_ok_iff ..).mp written
  simp [Base.natToBytes_length]

/-- Lists of nonempty entry encodings fit the parser's fuel and recover each entry in order. -/
theorem many_encodeEntries (encoder : α → Except Error (List UInt8)) (reader : Reader α)
    (reads : ∀ value data rest, encoder value = .ok data →
      reader (data ++ rest) = .ok (value, rest))
    (positive : ∀ value data, encoder value = .ok data → 0 < data.length)
    (values : List α) (data : List UInt8) (written : encodeEntries encoder values = .ok data) :
    values.length ≤ data.length ∧
      ∀ fuel, values.length ≤ fuel → many reader fuel data = .ok values := by
  induction values generalizing data with
  | nil =>
    simp only [encodeEntries, Except.ok.injEq] at written
    subst data
    exact ⟨by simp, fun fuel _ => by cases fuel <;> rfl⟩
  | cons value values ih =>
    simp only [encodeEntries, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨first, hf, tail, ht, rfl⟩ := written
    obtain ⟨bound, parsed⟩ := ih tail ht
    have nonempty := positive value first hf
    constructor
    · simp only [List.length_cons, List.length_append]
      omega
    · intro fuel enough
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
        have enoughTail : values.length ≤ fuel := by simpa using enough
        cases first with
        | nil => simp at nonempty
        | cons byte rest =>
          have recovered := reads value (byte :: rest) tail hf
          simp only [List.cons_append] at recovered
          simp only [List.cons_append, many, recovered, bind, Except.bind,
            pure, Except.pure, parsed fuel enoughTail]

/-- An isolated vector of entries recovers every successfully encoded entry. -/
theorem entries_encodeEntries (encoder : α → Except Error (List UInt8)) (reader : Reader α)
    (reads : ∀ value data rest, encoder value = .ok data →
      reader (data ++ rest) = .ok (value, rest))
    (positive : ∀ value data, encoder value = .ok data → 0 < data.length)
    (values : List α) (data : List UInt8) (written : encodeEntries encoder values = .ok data) :
    entries reader data = .ok values := by
  obtain ⟨bound, parsed⟩ := many_encodeEntries encoder reader reads positive values data written
  exact parsed data.length bound

/-- A vector of entries round trips with arbitrary trailing bytes after its length boundary. -/
theorem items_encodeItems (encoder : α → Except Error (List UInt8)) (reader : Reader α)
    (reads : ∀ value data rest, encoder value = .ok data →
      reader (data ++ rest) = .ok (value, rest))
    (positive : ∀ value data, encoder value = .ok data → 0 < data.length)
    {width minimum maximum : Nat} {values : List α} {encoded : List UInt8}
    (written : encodeItems width minimum maximum encoder values = .ok encoded)
    (rest : List UInt8) :
    items width minimum maximum reader (encoded ++ rest) = .ok (values, rest) := by
  simp only [encodeItems, bind_ok_iff] at written
  obtain ⟨data, hd, he⟩ := written
  simp [items, blob_encode_of_encode he rest,
    entries_encodeEntries encoder reader reads positive values data hd,
    StateT.bind, StateT.lift, bind, Except.bind, pure, Except.pure]

end EthLib.Networking.Quic.Tls.Wire

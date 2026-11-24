module

public import EthLib.Networking.Quic.Tls.Wire
public import EthLib.Base.Proofs.Bytes
public import EthLib.Base.Proofs.ByteOrder
public import EthLib.Networking.Proofs.Encoding.ByteReader

/-!
# Proofs: TLS wire fields

The readers recover written fields and preserve arbitrary trailing bytes.

A successful length-prefixed field re-encodes to its exact consumed prefix.

Vector encoders reject lengths that do not fit, rather than reducing them modulo the field width.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Wire

open EthLib.Base (bind_ok_iff)
open EthLib.Networking.Encoding.ByteReader (bytes_append uint_encode require_true)

/-- A one-byte integer is the value of that byte. -/
@[simp] theorem uint_byte (value : UInt8) (rest : List UInt8) :
    uint 1 (value :: rest) = .ok (value.toNat, rest) := by
  simp [uint, Encoding.ByteReader.uint, Encoding.ByteReader.bytes, Base.ByteOrder.ofBE, StateT.bind,
    StateT.pure, bind, Except.bind, pure, Except.pure]

/-- Reading a bounded vector recovers all its bytes and leaves the following bytes. -/
theorem blob_encode (width minimum maximum : Nat) (data rest : List UInt8)
    (lower : minimum ≤ data.length) (upper : data.length ≤ maximum)
    (capacity : data.length < 256 ^ width) :
    blob width minimum maximum ((Base.ByteOrder.toBE width data.length).toList ++ (data ++ rest)) =
      .ok (data, rest) := by
  simp [blob, Nat.mod_eq_of_lt capacity, lower, upper,
    StateT.bind, bind, Except.bind]

/-- A successful vector encoder writes its exact length followed by its exact content. -/
theorem encodeBlob_eq_ok_iff (width minimum maximum : Nat) (data encoded : List UInt8) :
    encodeBlob width minimum maximum data = .ok encoded ↔
      minimum ≤ data.length ∧ data.length ≤ maximum ∧ data.length < 256 ^ width ∧
      encoded = (Base.ByteOrder.toBE width data.length).toList ++ data := by
  simp only [encodeBlob]
  split <;> simp_all [eq_comm] <;> omega

/-- An overlong vector is rejected even when its low length bytes would fit. -/
theorem encodeBlob_length_overflow (width minimum maximum : Nat) (data : List UInt8)
    (overflow : 256 ^ width ≤ data.length) :
    encodeBlob width minimum maximum data = .error .length := by
  simp [encodeBlob, Nat.not_lt.mpr overflow]

/-- Two-byte identifiers round trip, including values that no registry assigns. -/
@[simp] theorem codePoint_encode (value : CodePoint) (rest : List UInt8) :
    codePoint ((Base.ByteOrder.toBE 2 value.val).toList ++ rest) = .ok (value, rest) := by
  have bound : value.val < 256 ^ 2 := value.isLt
  simp [codePoint, Nat.mod_eq_of_lt bound, value.isLt,
    StateT.bind, StateT.pure, bind, Except.bind, pure, Except.pure]

/-- Reading a fixed-size vector recovers the same vector. -/
@[simp] theorem vector_encode (n : Nat) (value : Vector UInt8 n) (rest : List UInt8) :
    vector n (value.toList ++ rest) = .ok (value, rest) :=
  Encoding.ByteReader.vector_append _ value rest

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
  simp

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

/-- An isolated reader succeeds exactly when it consumes the whole input. -/
theorem exact_eq_ok_iff (reader : Reader α) (input : List UInt8) (value : α) :
    exact reader input = .ok value ↔ reader input = .ok (value, []) := by
  simp only [exact, bind_ok_iff]
  constructor
  · rintro ⟨⟨result, rest⟩, parsed, checked⟩
    by_cases empty : rest = []
    · have same : result = value := by
        simpa [empty, pure, Except.pure] using checked
      simpa only [same, empty] using parsed
    · simp [empty, throw, throwThe, MonadExceptOf.throw] at checked
  · intro parsed
    exact ⟨(value, []), parsed, rfl⟩

/-- Every accepted entry list is exactly the concatenation of its entries' encodings. -/
theorem encodeEntries_of_many (encoder : α → Except Error (List UInt8)) (reader : Reader α)
    (reconstructs : ∀ input value rest, reader input = .ok (value, rest) →
      ∃ encoded, encoder value = .ok encoded ∧ input = encoded ++ rest)
    {fuel : Nat} {input : List UInt8} {values : List α}
    (parsed : many reader fuel input = .ok values) :
    encodeEntries encoder values = .ok input := by
  induction fuel generalizing input values with
  | zero =>
    cases input with
    | nil => cases parsed; rfl
    | cons byte rest => cases parsed
  | succ fuel ih =>
    cases input with
    | nil => cases parsed; rfl
    | cons byte rest =>
      simp only [many, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at parsed
      obtain ⟨⟨value, suffix⟩, headRead, tail, tailRead, rfl⟩ := parsed
      obtain ⟨encoded, headWritten, same⟩ := reconstructs _ _ _ headRead
      simp [encodeEntries, headWritten, ih tailRead, same, bind, Except.bind,
        pure, Except.pure]

/-- Parsing an isolated entry list leaves exactly the encodings of the returned entries. -/
theorem encodeEntries_of_entries (encoder : α → Except Error (List UInt8)) (reader : Reader α)
    (reconstructs : ∀ input value rest, reader input = .ok (value, rest) →
      ∃ encoded, encoder value = .ok encoded ∧ input = encoded ++ rest)
    {input : List UInt8} {values : List α} (parsed : entries reader input = .ok values) :
    encodeEntries encoder values = .ok input :=
  encodeEntries_of_many encoder reader reconstructs parsed

/-- An accepted identifier occupies exactly its two-byte big-endian encoding. -/
theorem eq_toBE_of_codePoint {input rest : List UInt8} {value : CodePoint}
    (parsed : codePoint input = .ok (value, rest)) :
    input = (Base.ByteOrder.toBE 2 value.val).toList ++ rest := by
  cases numberRead : uint 2 input with
  | error error => simp [codePoint, numberRead, bind, StateT.bind, Except.bind] at parsed
  | ok result =>
    obtain ⟨number, suffix⟩ := result
    by_cases bound : number < 2 ^ 16
    · have checked : (⟨number, bound⟩ : CodePoint) = value ∧ suffix = rest := by
        simpa [codePoint, numberRead, bound, bind, StateT.bind, Except.bind,
          pure, StateT.pure, Except.pure] using parsed
      obtain ⟨rfl, rfl⟩ := checked
      exact (Encoding.ByteReader.uint_ok_iff ..).mp numberRead |>.2
    · simp [codePoint, numberRead, bound, bind, StateT.bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, StateT.lift] at parsed

/-- A fixed-size vector retains every consumed byte and the exact remaining suffix. -/
theorem eq_toList_append_of_vector {n : Nat} {input rest : List UInt8}
    {value : Vector UInt8 n} (parsed : vector n input = .ok (value, rest)) :
    input = value.toList ++ rest :=
  (Encoding.ByteReader.vector_ok_iff _ input rest value).mp parsed

/-- Every accepted length-prefixed byte vector is the encoding of the returned data. -/
theorem encodeBlob_of_blob {width minimum maximum : Nat} {input data rest : List UInt8}
    (parsed : blob width minimum maximum input = .ok (data, rest)) :
    ∃ encoded, encodeBlob width minimum maximum data = .ok encoded ∧ input = encoded ++ rest := by
  change (uint width input >>= fun (size, afterLength) =>
    require (minimum ≤ size ∧ size ≤ maximum) .length afterLength >>= fun (_, afterCheck) =>
      bytes size afterCheck) = .ok (data, rest) at parsed
  simp only [bind_ok_iff] at parsed
  obtain ⟨⟨size, afterLength⟩, sizeRead, ⟨u, afterCheck⟩, checked, dataRead⟩ := parsed
  obtain ⟨bounds, same⟩ := (Encoding.ByteReader.require_ok_iff ..).mp checked
  obtain ⟨length, suffix⟩ := (Encoding.ByteReader.bytes_ok_iff ..).mp dataRead
  obtain ⟨capacity, before⟩ := (Encoding.ByteReader.uint_ok_iff ..).mp sizeRead
  refine ⟨(Base.ByteOrder.toBE width data.length).toList ++ data, ?_, ?_⟩
  · apply (encodeBlob_eq_ok_iff ..).mpr
    exact ⟨by omega, by omega, by omega, rfl⟩
  · have after : afterLength = data ++ rest := same.trans suffix
    rw [after] at before
    simpa only [length, List.append_assoc] using before

/-- Every accepted vector of entries re-encodes to its exact consumed prefix. -/
theorem encodeItems_of_items (encoder : α → Except Error (List UInt8)) (reader : Reader α)
    (reconstructs : ∀ input value rest, reader input = .ok (value, rest) →
      ∃ encoded, encoder value = .ok encoded ∧ input = encoded ++ rest)
    {width minimum maximum : Nat} {input rest : List UInt8} {values : List α}
    (parsed : items width minimum maximum reader input = .ok (values, rest)) :
    ∃ encoded, encodeItems width minimum maximum encoder values = .ok encoded ∧
      input = encoded ++ rest := by
  change (blob width minimum maximum input >>= fun (data, suffix) =>
    entries reader data >>= fun decoded => .ok (decoded, suffix)) = .ok (values, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨data, suffix⟩, dataRead, decoded, entriesRead, rfl, rfl⟩ := parsed
  obtain ⟨encoded, written, same⟩ := encodeBlob_of_blob dataRead
  refine ⟨encoded, ?_, same⟩
  simp [encodeItems, encodeEntries_of_entries encoder reader reconstructs entriesRead,
    written, bind, Except.bind]

end EthLib.Networking.Quic.Tls.Wire

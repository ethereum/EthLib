module

public import EthLib.Serialization.Ssz.Codec.Json

/-!
# Proofs: the loops of the SSZ codec

The serializer and the byte-run reader loop over their lists, carrying what they have built so far.

The theorems below give back the plain recursion on the first element, which the other proofs use.

The two smallest cases of the hex reader are here too.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-! ## The composite arms of the encoder -/

/-- A vector of its length encodes its elements as a sequence. -/
theorem serialize_vector_seq (element : Desc) (length : Nat) (elements : List Value) :
    serialize (.vector element length) (.seq elements) =
      if elements.length == length then serializeSequence element elements
      else .error (.scope length elements.length) :=
  rfl

/-- A list within its limit encodes its elements as a sequence. -/
theorem serialize_list_seq (element : Desc) (limit : Nat) (elements : List Value) :
    serialize (.list element limit) (.seq elements) =
      if elements.length ≤ limit then serializeSequence element elements
      else .error (.overLimit limit elements.length) :=
  rfl

/-- A progressive list within its bound encodes its elements as a sequence. -/
theorem serialize_progressiveList_seq (element : Desc) (limit : Option Nat)
    (elements : List Value) :
    serialize (.progressiveList element limit) (.seq elements) = (do
      boundCheck limit elements.length
      serializeSequence element elements) :=
  rfl

/-- A container encodes its values as a struct. -/
theorem serialize_container_seq (names : List String) (fields : List Desc)
    (values : List Value) :
    serialize (.container names fields) (.seq values) = serializeStruct fields values :=
  rfl

/-- A progressive container encodes its values as a struct of its declared fields. -/
theorem serialize_progressiveContainer_seq (active : List Bool) (names : List String)
    (fields : List Desc) (values : List Value) :
    serialize (.progressiveContainer active names fields) (.seq values) =
      serializeStruct fields values :=
  rfl

/-! ## Widths -/

/-- The width loop from some width adds that width to the width from none. -/
theorem headWidthFrom_eq (parts : List (Bool × Bytes)) (width : Nat) :
    headWidthFrom parts width = width + headWidth parts := by
  induction parts generalizing width with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨isInline, part⟩ := p
    rw [headWidth, headWidthFrom, headWidthFrom, ih, ih]
    omega

/-- No parts take no fixed bytes. -/
theorem headWidth_nil : headWidth [] = 0 := rfl

/-- The fixed width of the first part, then that of the rest. -/
theorem headWidth_cons (isInline : Bool) (part : Bytes) (rest : List (Bool × Bytes)) :
    headWidth ((isInline, part) :: rest) =
      (if isInline then part.size else bytesPerOffset) + headWidth rest := by
  rw [headWidth, headWidthFrom, headWidthFrom_eq]
  omega

/-- The body loop from some width adds that width to the width from none. -/
theorem bodyWidthFrom_eq (parts : List (Bool × Bytes)) (width : Nat) :
    bodyWidthFrom parts width = width + bodyWidth parts := by
  induction parts generalizing width with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨isInline, part⟩ := p
    cases isInline
    · rw [bodyWidth, bodyWidthFrom, bodyWidthFrom, ih, ih]
      omega
    · rw [bodyWidth, bodyWidthFrom, bodyWidthFrom, ih, ih]
      omega

/-- No parts take no body bytes. -/
theorem bodyWidth_nil : bodyWidth [] = 0 := rfl

/-- An inline part has no body. -/
theorem bodyWidth_cons_inline (part : Bytes) (rest : List (Bool × Bytes)) :
    bodyWidth ((true, part) :: rest) = bodyWidth rest := rfl

/-- A part not in place adds its whole size to the bodies. -/
theorem bodyWidth_cons_variable (part : Bytes) (rest : List (Bool × Bytes)) :
    bodyWidth ((false, part) :: rest) = part.size + bodyWidth rest := by
  rw [bodyWidth, bodyWidthFrom, bodyWidthFrom_eq]
  omega

/-! ## Layout -/

/-- The fixed-part loop from some bytes is the loop from none, after them. -/
theorem headOfFrom_eq (start : Nat) (parts : List (Bool × Bytes)) (out : Bytes) :
    headOfFrom start parts out = out ++ headOf start parts := by
  induction parts generalizing start out with
  | nil => rw [headOf, headOfFrom, headOfFrom, Array.append_empty]
  | cons p rest ih =>
    obtain ⟨isInline, part⟩ := p
    cases isInline <;>
      rw [headOf, headOfFrom, headOfFrom, ih, ih, Array.empty_append, Array.append_assoc]

/-- No parts have no fixed part. -/
theorem headOf_nil (start : Nat) : headOf start [] = #[] := rfl

/-- An inline part sits in the fixed part in full. -/
theorem headOf_cons_inline (start : Nat) (part : Bytes) (rest : List (Bool × Bytes)) :
    headOf start ((true, part) :: rest) = part ++ headOf start rest := by
  rw [headOf, headOfFrom, headOfFrom_eq, Array.empty_append]

/-- A part not in place leaves its offset, and the next body begins past its end. -/
theorem headOf_cons_variable (start : Nat) (part : Bytes) (rest : List (Bool × Bytes)) :
    headOf start ((false, part) :: rest) =
      uintBytes bytesPerOffset start ++ headOf (start + part.size) rest := by
  rw [headOf, headOfFrom, headOfFrom_eq, Array.empty_append]

/-- The body loop from some bytes is the loop from none, after them. -/
theorem bodiesOfFrom_eq (parts : List (Bool × Bytes)) (out : Bytes) :
    bodiesOfFrom parts out = out ++ bodiesOf parts := by
  induction parts generalizing out with
  | nil => rw [bodiesOf, bodiesOfFrom, bodiesOfFrom, Array.append_empty]
  | cons p rest ih =>
    obtain ⟨isInline, part⟩ := p
    cases isInline
    · rw [bodiesOf, bodiesOfFrom, bodiesOfFrom, ih, ih, Array.empty_append, Array.append_assoc]
    · rw [bodiesOf, bodiesOfFrom, bodiesOfFrom, ih, ih, Array.empty_append]

/-- No parts have no bodies. -/
theorem bodiesOf_nil : bodiesOf [] = #[] := rfl

/-- An inline part has no body. -/
theorem bodiesOf_cons_inline (part : Bytes) (rest : List (Bool × Bytes)) :
    bodiesOf ((true, part) :: rest) = bodiesOf rest := rfl

/-- A part not in place puts its bytes first among the bodies that follow. -/
theorem bodiesOf_cons_variable (part : Bytes) (rest : List (Bool × Bytes)) :
    bodiesOf ((false, part) :: rest) = part ++ bodiesOf rest := by
  rw [bodiesOf, bodiesOfFrom, bodiesOfFrom_eq, Array.empty_append]

/-! ## Elements and fields -/

/-- The element loop from some encodings is the loop from none, after them. -/
theorem serializeEachFrom_eq (element : Desc) (values : List Value) (done : List Bytes) :
    serializeEachFrom element values done =
      (serializeEachFrom element values []).map (done.reverse ++ ·) := by
  induction values generalizing done with
  | nil => simp [serializeEachFrom, Except.map]
  | cons value rest ih =>
    simp only [serializeEachFrom]
    cases serialize element value with
    | error e => rfl
    | ok head =>
      show serializeEachFrom element rest (head :: done) =
        (serializeEachFrom element rest [head]).map _
      rw [ih, ih [head]]
      cases serializeEachFrom element rest [] <;> simp [Except.map]

/-- The elements of a sequence are the element loop from none. -/
theorem serializeEach_eq (element : Desc) (values : List Value) :
    serializeEach element values = serializeEachFrom element values [] := by
  cases values with
  | nil => simp [serializeEach, serializeEachFrom]
  | cons value rest => simp only [serializeEach, serializeEachFrom]

/-- No elements encode to no parts. -/
theorem serializeEach_nil (element : Desc) : serializeEach element [] = .ok [] := by
  simp [serializeEach]

/-- The elements of a sequence: the first encoded, then the rest. -/
theorem serializeEach_cons (element : Desc) (value : Value) (rest : List Value) :
    serializeEach element (value :: rest) = do
      let head ← serialize element value
      let tail ← serializeEach element rest
      return head :: tail := by
  simp only [serializeEach]
  cases serialize element value with
  | error e => rfl
  | ok head =>
    show serializeEachFrom element rest [head] = _
    rw [serializeEachFrom_eq, ← serializeEach_eq]
    cases serializeEach element rest <;> rfl

/-- The field loop from some encodings is the loop from none, after them. -/
theorem serializeFieldsFrom_eq (fields : List Desc) (values : List Value) (done : List Bytes) :
    serializeFieldsFrom fields values done =
      (serializeFieldsFrom fields values []).map (done.reverse ++ ·) := by
  induction fields generalizing values done with
  | nil => cases values <;> simp [serializeFieldsFrom, Except.map]
  | cons field fields ih =>
    cases values with
    | nil => simp [serializeFieldsFrom, Except.map]
    | cons value values =>
      simp only [serializeFieldsFrom]
      cases serialize field value with
      | error e => rfl
      | ok head =>
        show serializeFieldsFrom fields values (head :: done) =
          (serializeFieldsFrom fields values [head]).map _
        rw [ih, ih values [head]]
        cases serializeFieldsFrom fields values [] <;> simp [Except.map]

/-- The fields of a struct are the field loop from none. -/
theorem serializeFields_eq (fields : List Desc) (values : List Value) :
    serializeFields fields values = serializeFieldsFrom fields values [] := by
  cases fields <;> cases values <;> simp [serializeFields, serializeFieldsFrom]

/-- No fields encode to no parts. -/
theorem serializeFields_nil : serializeFields [] [] = .ok [] := by
  simp [serializeFields]

/-- More values than fields fit no struct. -/
theorem serializeFields_nil_cons (value : Value) (values : List Value) :
    serializeFields [] (value :: values) = .error .typeMismatch := by
  simp [serializeFields]

/-- More fields than values fit no struct. -/
theorem serializeFields_cons_nil (field : Desc) (fields : List Desc) :
    serializeFields (field :: fields) [] = .error .typeMismatch := by
  simp [serializeFields]

/-- The fields of a struct: the first encoded, then the rest. -/
theorem serializeFields_cons (field : Desc) (fields : List Desc) (value : Value)
    (values : List Value) :
    serializeFields (field :: fields) (value :: values) = do
      let head ← serialize field value
      let tail ← serializeFields fields values
      return head :: tail := by
  simp only [serializeFields]
  cases serialize field value with
  | error e => rfl
  | ok head =>
    show serializeFieldsFrom fields values [head] = _
    rw [serializeFieldsFrom_eq, ← serializeFields_eq]
    cases serializeFields fields values <;> rfl

/-! ## Hex and byte runs -/

/-- No digits hold no bytes. -/
theorem hexBytes_nil : hexBytes [] = .ok #[] := rfl

/-- One digit alone holds no byte. -/
theorem hexBytes_single (c : Char) : hexBytes [c] = .error .hexDigits := rfl

/-- The byte-run loop from some bytes is the loop from none, after them. -/
theorem byteRunFrom_eq : ∀ (values : List Value) (out : Bytes),
    byteRunFrom values out = (byteRunFrom values #[]).map (out ++ ·)
  | [], out => by simp [byteRunFrom, Except.map]
  | .uint n :: rest, out => by
    simp only [byteRunFrom]
    by_cases wide : n ≥ 256
    · simp [wide]; rfl
    · simp only [wide]
      show byteRunFrom rest (out.push _) = (byteRunFrom rest (#[].push _)).map _
      rw [byteRunFrom_eq rest (out.push _), byteRunFrom_eq rest (#[].push _)]
      cases byteRunFrom rest #[] <;>
        simp only [Except.map, Array.push_eq_append, Array.empty_append, Array.append_assoc]
  | .bool _ :: _, _ | .bytes _ :: _, _ | .bits _ :: _, _ | .seq _ :: _, _ | .union _ _ :: _, _ =>
    rfl

/-- No values hold no bytes. -/
theorem byteRun_nil : byteRun [] = .ok #[] := rfl

/-- The first value is the first byte, and the rest are the bytes after it. -/
theorem byteRun_uint (n : Nat) (rest : List Value) :
    byteRun (.uint n :: rest) = do
      if n ≥ 256 then throw (.uintRange 256 n)
      return #[UInt8.ofNat n] ++ (← byteRun rest) := by
  simp only [byteRun, byteRunFrom]
  by_cases wide : n ≥ 256
  · simp [wide]; rfl
  · simp only [wide]
    show byteRunFrom rest (#[].push _) = _
    rw [byteRunFrom_eq]
    cases byteRunFrom rest #[] <;> rfl

/-! ## Layout and slices, by `zip` -/

/-- The layout pairs each part with its flag, as `zip` does. -/
theorem assemble_eq (inline : List Bool) (parts : List Bytes) :
    assemble inline parts = (do
      let slots := inline.zip parts
      let leading := headWidth slots
      let total := leading + bodyWidth slots
      if total ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow total)
      return headOf leading slots ++ bodiesOf slots) := by
  rw [assemble, List.zip_eq_zipWith]

/-- Cutting each offset's span out of the data is a map over the offsets zipped with their spans.

Proofs about the slicers rewrite their last step into this form. -/
theorem zipWith_extract_eq (data : Bytes) (offsets spans : List Nat) :
    List.zipWith (fun start span => data.extract start (start + span)) offsets spans =
      (offsets.zip spans).map fun (start, span) => data.extract start (start + span) := by
  rw [List.map_zip_eq_zipWith]
  rfl

/-! ## Offsets -/

/-- The span loop from some spans is the loop from none, after them. -/
theorem offsetSpansFrom_eq : ∀ (offsets : List Nat) (scope : Nat) (done : List Nat),
    offsetSpansFrom offsets scope done =
      (offsetSpansFrom offsets scope []).map (done.reverse ++ ·)
  | [], _, done => by simp [offsetSpansFrom, Except.map]
  | [start], scope, done => by
    simp only [offsetSpansFrom]
    split <;> simp [Except.map]
  | start :: next :: rest, scope, done => by
    simp only [offsetSpansFrom]
    split
    · rfl
    · rw [offsetSpansFrom_eq (next :: rest) scope ((next - start) :: done),
        offsetSpansFrom_eq (next :: rest) scope [next - start]]
      cases offsetSpansFrom (next :: rest) scope [] <;> simp [Except.map]

/-- No offsets give no spans. -/
theorem offsetSpans_nil (scope : Nat) : offsetSpans [] scope = .ok [] := rfl

/-- The last body is closed by the budget. -/
theorem offsetSpans_single (start scope : Nat) :
    offsetSpans [start] scope =
      if scope < start then .error (.offsetPastScope start scope) else .ok [scope - start] := by
  simp only [offsetSpans, offsetSpansFrom]
  split <;> rfl

/-- Every other body ends where the next one begins. -/
theorem offsetSpans_cons_cons (start next : Nat) (rest : List Nat) (scope : Nat) :
    offsetSpans (start :: next :: rest) scope =
      if next < start then .error (.offsetUnordered start next)
      else do return (next - start) :: (← offsetSpans (next :: rest) scope) := by
  simp only [offsetSpans, offsetSpansFrom]
  split
  · rfl
  · rw [offsetSpansFrom_eq]
    cases offsetSpansFrom (next :: rest) scope [] <;> rfl

/-! ## Decoding each element -/

/-- The element loop from some values is the loop from none, after them. -/
theorem deserializeEachFrom_eq (element : Desc) (slices : List Bytes) (done : List Value) :
    deserializeEachFrom element slices done =
      (deserializeEachFrom element slices []).map (done.reverse ++ ·) := by
  induction slices generalizing done with
  | nil => simp [deserializeEachFrom, Except.map]
  | cons slice rest ih =>
    rw [deserializeEachFrom, deserializeEachFrom]
    cases deserialize element slice with
    | error e => rfl
    | ok head =>
      show deserializeEachFrom element rest (head :: done) =
        (deserializeEachFrom element rest [head]).map _
      rw [ih, ih [head]]
      cases deserializeEachFrom element rest [] <;> simp [Except.map]

/-- No slices decode to no values. -/
theorem deserializeEach_nil (element : Desc) : deserializeEach element [] = .ok [] := by
  rw [deserializeEach, deserializeEachFrom]
  rfl

/-- The elements of a sequence: the first decoded, then the rest. -/
theorem deserializeEach_cons (element : Desc) (slice : Bytes) (rest : List Bytes) :
    deserializeEach element (slice :: rest) = do
      let head ← deserialize element slice
      let tail ← deserializeEach element rest
      return head :: tail := by
  rw [deserializeEach, deserializeEachFrom]
  cases deserialize element slice with
  | error e => rfl
  | ok head =>
    show deserializeEachFrom element rest [head] = _
    rw [deserializeEachFrom_eq, deserializeEach]
    cases deserializeEachFrom element rest [] <;> rfl

end EthLib.Serialization.Ssz

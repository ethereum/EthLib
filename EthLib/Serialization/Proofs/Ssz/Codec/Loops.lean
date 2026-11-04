module

public import EthLib.Serialization.Ssz.Codec.Json

/-!
# Proofs: the loops of the SSZ codec

The serializer and the hex reader run their lists in loops that carry what they have built so far.

The theorems below give back the plain recursion on the first element, which the other proofs use.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

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

/-- The hex loop from some bytes is the loop from none, after them. -/
theorem hexBytesFrom_eq : ∀ (digits : List Char) (out : Bytes),
    hexBytesFrom digits out = (hexBytesFrom digits #[]).map (out ++ ·)
  | [], out => by simp [hexBytesFrom, Except.map]
  | [_], _ => rfl
  | high :: low :: rest, out => by
    simp only [hexBytesFrom]
    cases hexDigit high with
    | error e => rfl
    | ok h =>
      cases hexDigit low with
      | error e => rfl
      | ok l =>
        show hexBytesFrom rest (out.push _) = (hexBytesFrom rest (#[].push _)).map _
        rw [hexBytesFrom_eq rest (out.push _), hexBytesFrom_eq rest (#[].push _)]
        cases hexBytesFrom rest #[] <;>
          simp only [Except.map, Array.push_eq_append, Array.empty_append, Array.append_assoc]

/-- No digits hold no bytes. -/
theorem hexBytes_nil : hexBytes [] = .ok #[] := rfl

/-- One digit alone holds no byte. -/
theorem hexBytes_single (c : Char) : hexBytes [c] = .error .hexDigits := rfl

/-- The first two digits hold the first byte, and the rest hold the bytes after it. -/
theorem hexBytes_cons (high low : Char) (rest : List Char) :
    hexBytes (high :: low :: rest) = do
      let byte := 16 * (← hexDigit high) + (← hexDigit low)
      return #[UInt8.ofNat byte] ++ (← hexBytes rest) := by
  simp only [hexBytes, hexBytesFrom]
  cases hexDigit high with
  | error e => rfl
  | ok h =>
    cases hexDigit low with
    | error e => rfl
    | ok l =>
      show hexBytesFrom rest (#[].push _) = _
      rw [hexBytesFrom_eq]
      cases hexBytesFrom rest #[] <;> rfl

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

end EthLib.Serialization.Ssz

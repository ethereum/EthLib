module

public import EthLib.Base.BigEndian

/-!
# Distinguished Encoding Rules reader

Clause numbers follow [ITU-T X.690 (02/2021)][x690].

DER lengths are definite and in their shortest form (X.690 §10.1).

The reader keeps each value's complete encoding, so a certificate signature can be checked.

[x690]: https://www.itu.int/rec/T-REC-X.690-202102-I/en
-/

@[expose] public section

namespace EthLib.Serialization.Der

/-- A malformed DER tag, length, value or trailing input. -/
inductive Error where
  | truncated
  | tag
  | length
  | value
  | trailing
  deriving Repr, DecidableEq

/-- One low-tag-number DER value, including its original tag and length bytes. -/
structure Value where
  tag : UInt8
  content : ByteArray
  encoded : ByteArray

/-- Read one low-tag-number tag, length and value (X.690 §§8.1.2, 8.1.3 and 10.1). -/
def read (input : ByteArray) : Except Error (Value × ByteArray) := do
  match input.data.toList with
  | tag :: first :: rest =>
    if tag.toNat % 32 = 31 ∨ tag = 0 then throw .tag
    let (length, header) ←
      if first.toNat < 128 then pure (first.toNat, 2)
      else do
        let count := first.toNat - 128
        if count = 0 ∨ count = 127 then throw .length
        if rest.length < count then throw .truncated
        let bytes := rest.take count
        match bytes with
        | [] => throw .length
        | head :: _ =>
          if head = 0 then throw .length
          let length := EthLib.Base.bytesToNat bytes
          if length < 128 then throw .length
          pure (length, 2 + count)
    if input.size < header + length then throw .truncated
    return (⟨tag, input.extract header (header + length),
      input.extract 0 (header + length)⟩, input.extract (header + length) input.size)
  | _ => throw .truncated

/-- Read one value of the expected tag. -/
def readTag (tag : UInt8) (input : ByteArray) : Except Error (Value × ByteArray) := do
  let (value, rest) ← read input
  if value.tag = tag then return (value, rest) else throw .tag

/-- Read exactly one value, without trailing bytes. -/
def exact (tag : UInt8) (input : ByteArray) : Except Error Value := do
  let (value, rest) ← readTag tag input
  if rest.isEmpty then return value else throw .trailing

/-- Read siblings, with at most one value per input byte. -/
def children (input : ByteArray) : Except Error (List Value) := go input.size input
where
  go : Nat → ByteArray → Except Error (List Value)
    | 0, input => if input.isEmpty then .ok [] else .error .truncated
    | fuel + 1, input => do
      if input.isEmpty then return []
      let (value, rest) ← read input
      return value :: (← go fuel rest)

/-- A DER INTEGER, rejecting redundant sign octets (X.690 §8.3). -/
def integer (value : Value) : Except Error Int := do
  if value.tag != 2 then throw .tag
  match value.content.data.toList with
  | [] => throw .value
  | first :: rest =>
    match rest with
    | next :: _ =>
      if (first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat) then
        throw .value
    | [] => pure ()
    let n := EthLib.Base.bytesToNat value.content.data.toList
    return if first.toNat < 128 then Int.ofNat n
      else Int.ofNat n - Int.ofNat (256 ^ value.content.size)

/-- A nonnegative DER INTEGER. -/
def natural (value : Value) : Except Error Nat := do
  let n ← integer value
  if n < 0 then throw .value else return n.toNat

/-- DER BOOLEAN uses one byte, 00 or FF (X.690 §11.1). -/
def boolean (value : Value) : Except Error Bool := do
  if value.tag != 1 then throw .tag
  match value.content.data.toList with
  | [0] => return false
  | [255] => return true
  | _ => throw .value

/-- An octet-aligned BIT STRING, used for certificate keys and signatures (RFC 5280 §4.1). -/
def bitString (value : Value) : Except Error ByteArray := do
  if value.tag != 3 then throw .tag
  match value.content.data.toList with
  | 0 :: bytes => return ⟨bytes.toArray⟩
  | _ => throw .value

/-- Validate minimal base-128 OBJECT IDENTIFIER components (X.690 §8.19). -/
def oid (value : Value) : Except Error ByteArray := do
  if value.tag != 6 then throw .tag
  if value.content.isEmpty then throw .value
  -- A component starts after a byte with the top bit clear, and may not start with 0x80.
  let atStart ← value.content.data.toList.foldlM
    (fun (atStart : Bool) byte => do
      if atStart ∧ byte = 128 then throw .value
      return byte.toNat < 128) true
  if atStart then return value.content else throw .value

/-- Validate BIT STRING unused bits, also of an implicitly tagged value (X.690 §§8.6.2, 11.2.1). -/
def validBits (content : ByteArray) : Except Error Unit := do
  match content.data.toList with
  | [] => throw .value
  | unused :: bytes =>
    if 7 < unused.toNat then throw .value
    match bytes.getLast? with
    | none => if unused = 0 then pure () else throw .value
    | some last =>
      if last.toNat % (2 ^ unused.toNat) = 0 then pure () else throw .value

/-- Validate a Unicode scalar in a fixed-width ASN.1 character string. -/
def unicodeScalar (n : Nat) : Bool :=
  n ≤ 0x10ffff && !(0xd800 ≤ n && n ≤ 0xdfff)

/-- Validate BMPString or UniversalString code units (X.690 §8.23). -/
def fixedString (width : Nat) (bytes : List UInt8) : Bool :=
  let state := bytes.foldl (fun (state : Nat × Nat × Bool) byte =>
    let n := state.2.1 * 256 + byte.toNat
    if state.1 + 1 = width then (0, 0, state.2.2 && unicodeScalar n)
    else (state.1 + 1, n, state.2.2)) (0, 0, true)
  state.1 == 0 && state.2.2

/-- Validate the certificate subset of DER values, including values inside a Name.

Every other tag, primitive or constructed, is rejected.

X.690 §§8.2–8.12, 8.19, 8.23 and 11 fix these encodings. -/
def validate (value : Value) : Except Error Unit := go (value.encoded.size + 1) value
where
  go : Nat → Value → Except Error Unit
    | 0, _ => .error .value
    | fuel + 1, value => do
      match value.tag.toNat with
      | 1 => let _ ← boolean value; pure ()
      | 2 => let _ ← integer value; pure ()
      | 3 => validBits value.content
      | 4 => pure ()
      | 5 => if value.content.isEmpty then pure () else throw .value
      | 6 => let _ ← oid value; pure ()
      | 12 => if (String.fromUTF8? value.content).isSome then pure () else throw .value
      | 19 =>
        if value.content.data.toList.all (fun byte =>
          (48 ≤ byte.toNat && byte.toNat ≤ 57) ||
          (65 ≤ byte.toNat && byte.toNat ≤ 90) ||
          (97 ≤ byte.toNat && byte.toNat ≤ 122) ||
          ([32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63] : List UInt8).contains byte)
        then pure () else throw .value
      | 22 =>
        if value.content.data.toList.all (fun b => b.toNat < 128) then pure ()
        else throw .value
      | 28 => if fixedString 4 value.content.data.toList then pure () else throw .value
      | 30 => if fixedString 2 value.content.data.toList then pure () else throw .value
      | 48 | 49 =>
        let values ← children value.content
        if value.tag = 49 then
          if (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·) then pure ()
          else throw .value
        values.forM (go fuel)
      | _ => throw .tag

end EthLib.Serialization.Der

module

public import EthLib.Base.BigEndian

/-!
# Distinguished Encoding Rules reader

Clause numbers follow [ITU-T X.690 (02/2021)][x690].

The character sets of the strings follow [ITU-T X.680 (02/2021)][x680].

DER lengths are definite and in their shortest form (X.690 §10.1).

The reader keeps each value's complete encoding, so a certificate signature can be checked.

The module also writes and reads the ECDSA signature value, the SEQUENCE of r and s.

[x690]: https://www.itu.int/rec/T-REC-X.690-202102-I/en
[x680]: https://www.itu.int/rec/T-REC-X.680-202102-I/en
-/

@[expose] public section

namespace EthLib.Serialization.Der

/-- A malformed DER tag, length, value or trailing input.

A count of bytes is relative to the input of the read that failed. -/
inductive Error where
  /-- The input has `available` bytes, where the value needs at least `needed`. -/
  | truncated (needed available : Nat)
  /-- The tag `actual` is not allowed here.

  With `expected`, it is not that tag.

  Without, it is a high-number or zero tag, or outside the subset that validation reads. -/
  | tag (expected : Option UInt8) (actual : UInt8)
  /-- The length octets, which start with `first`, are not in the minimal definite form. -/
  | length (first : UInt8)
  /-- The content of a value is not a valid encoding of its type. -/
  | value
  /-- `count` bytes are left after the value. -/
  | trailing (count : Nat)
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
    -- §8.1.2.2: one identifier octet, with the tag number from 0 to 30 in bits 5 to 1.
    --
    -- §8.1.2.4.1: bits 5 to 1 set to `11111` start a high tag number, which this reader rejects.
    --
    -- The octet 0x00 starts the end-of-contents octets of §8.1.5, never a value of DER.
    if tag.toNat % 32 = 31 ∨ tag = 0 then throw (.tag none tag)
    let (length, header) ←
      -- §8.1.3.4, short form: bit 8 is zero, and bits 7 to 1 give the length.
      if first.toNat < 128 then pure (first.toNat, 2)
      else do
        -- §8.1.3.5 b, long form: bits 7 to 1 of the initial octet count the subsequent octets.
        let count := first.toNat - 128
        -- §10.1: DER uses the definite form, so the indefinite form 0x80 of §8.1.3.6.1 is rejected.
        --
        -- §8.1.3.5 c: the initial octet 0xFF shall not be used.
        if count = 0 ∨ count = 127 then throw (.length first)
        if rest.length < count then throw (.truncated (2 + count) input.size)
        -- §8.1.3.5: the subsequent octets give the length, unsigned, most significant octet first.
        let bytes := rest.take count
        match bytes with
        -- Unreachable: the count is at least 1, and the input holds that many octets after it.
        | [] => throw (.length first)
        | head :: _ =>
          -- §10.1: the length takes the minimum number of octets, so no leading zero octet.
          if head = 0 then throw (.length first)
          let length := EthLib.Base.bytesToNat bytes
          -- §10.1 again: a length below 128 takes the short form.
          if length < 128 then throw (.length first)
          pure (length, 2 + count)
    -- §8.1.1.1 and §8.1.3.3: the contents octets follow the length octets, as many as it gives.
    if input.size < header + length then throw (.truncated (header + length) input.size)
    -- The value keeps its contents and its whole encoding, then the input after it.
    return (⟨tag, input.extract header (header + length),
      input.extract 0 (header + length)⟩, input.extract (header + length) input.size)
  -- §8.1.1.1: an encoding has at least one identifier octet and one length octet.
  | _ => throw (.truncated 2 input.size)

/-- Read one value of the expected tag. -/
def readTag (tag : UInt8) (input : ByteArray) : Except Error (Value × ByteArray) := do
  let (value, rest) ← read input
  -- The identifier octet must be the expected one.
  if value.tag = tag then return (value, rest) else throw (.tag (some tag) value.tag)

/-- Read exactly one value, without trailing bytes. -/
def exact (tag : UInt8) (input : ByteArray) : Except Error Value := do
  let (value, rest) ← readTag tag input
  -- No octet may follow the value.
  if rest.isEmpty then return value else throw (.trailing rest.size)

/-- Read siblings, with at most one value per input byte. -/
def children (input : ByteArray) : Except Error (List Value) := go input.size input
where
  go : Nat → ByteArray → Except Error (List Value)
    -- Unreachable: each read takes two bytes or more, so the fuel never runs out first.
    | 0, input => if input.isEmpty then .ok [] else .error (.truncated 2 input.size)
    | fuel + 1, input => do
      -- §8.9.2, §8.10.2, §8.11.2 and §8.12.2: the contents are complete encodings, in turn.
      if input.isEmpty then return []
      let (value, rest) ← read input
      return value :: (← go fuel rest)

/-- A DER INTEGER, rejecting redundant sign octets (X.690 §8.3). -/
def integer (value : Value) : Except Error Int := do
  -- The universal tag 2, primitive, as §8.3.1 asks.
  if value.tag != 2 then throw (.tag (some 2) value.tag)
  match value.content.data.toList with
  -- §8.3.1: one or more contents octets.
  | [] => throw .value
  | first :: rest =>
    match rest with
    -- §8.3.2: the bits of the first octet and bit 8 of the second are not all zero, nor all ones.
    | next :: _ =>
      if (first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat) then
        throw .value
    | [] => pure ()
    -- §8.3.3: two's complement, so the unsigned value minus `256^k` for `k` octets.
    --
    -- That holds when bit 8 of the first octet is 1.
    let n := EthLib.Base.bytesToNat value.content.data.toList
    return if first.toNat < 128 then Int.ofNat n
      else Int.ofNat n - Int.ofNat (256 ^ value.content.size)

/-- A nonnegative DER INTEGER. -/
def natural (value : Value) : Except Error Nat := do
  let n ← integer value
  -- EthLib's restriction, not X.690's: the INTEGER is not negative.
  if n < 0 then throw .value else return n.toNat

/-- DER BOOLEAN uses one byte, 00 or FF (X.690 §11.1). -/
def boolean (value : Value) : Except Error Bool := do
  -- §8.2.1: the universal tag 1, primitive, with a single contents octet.
  if value.tag != 1 then throw (.tag (some 1) value.tag)
  match value.content.data.toList with
  -- §8.2.2: FALSE is the octet zero.
  | [0] => return false
  -- §11.1: TRUE has all eight bits set to one.
  | [255] => return true
  | _ => throw .value

/-- An octet-aligned BIT STRING, used for certificate keys and signatures (RFC 5280 §4.1). -/
def bitString (value : Value) : Except Error ByteArray := do
  -- The universal tag 3, primitive, as §10.2 asks of DER.
  if value.tag != 3 then throw (.tag (some 3) value.tag)
  match value.content.data.toList with
  -- §8.6.2.2: the initial octet counts the unused bits of the last octet.
  --
  -- EthLib reads only whole octets, so that count must be 0.
  | 0 :: bytes => return ⟨bytes.toArray⟩
  | _ => throw .value

/-- Validate minimal base-128 OBJECT IDENTIFIER components (X.690 §8.19). -/
def oid (value : Value) : Except Error ByteArray := do
  -- §8.19.1: the universal tag 6, primitive.
  if value.tag != 6 then throw (.tag (some 6) value.tag)
  -- §8.19.3: at least one subidentifier, one less than the two or more components.
  if value.content.isEmpty then throw .value
  -- §8.19.2: bit 8 is zero on the last octet of a subidentifier, and one on each octet before.
  --
  -- §8.19.2: the fewest octets, so the leading octet of a subidentifier is never 0x80.
  let atStart ← value.content.data.toList.foldlM
    (fun (atStart : Bool) byte => do
      if atStart ∧ byte = 128 then throw .value
      return byte.toNat < 128) true
  -- The last octet ends a subidentifier.
  if atStart then return value.content else throw .value

/-- Validate BIT STRING unused bits, also of an implicitly tagged value (X.690 §§8.6.2, 11.2.1). -/
def validBits (content : ByteArray) : Except Error Unit := do
  match content.data.toList with
  -- §8.6.2: the contents start with an initial octet.
  | [] => throw .value
  | unused :: bytes =>
    -- §8.6.2.2: the initial octet counts the unused bits of the last octet, from zero to seven.
    if 7 < unused.toNat then throw .value
    match bytes.getLast? with
    -- §8.6.2.3: an empty bitstring has no subsequent octets, and an initial octet of zero.
    | none => if unused = 0 then pure () else throw .value
    -- §11.2.1: each unused bit of the last octet is zero, so the octet is a multiple of `2^unused`.
    | some last =>
      if last.toNat % (2 ^ unused.toNat) = 0 then pure () else throw .value

/-- Validate a Unicode scalar in a fixed-width ASN.1 character string. -/
def unicodeScalar (n : Nat) : Bool :=
  -- At most 0x10FFFF, and outside the surrogates 0xD800 to 0xDFFF.
  n ≤ 0x10ffff && !(0xd800 ≤ n && n ≤ 0xdfff)

/-- Validate BMPString or UniversalString code units (X.690 §8.23). -/
def fixedString (width : Nat) (bytes : List UInt8) : Bool :=
  -- §8.23.7 and §8.23.8: each character takes `width` octets, 4 or 2, read most significant first.
  let state := bytes.foldl (fun (state : Nat × Nat × Bool) byte =>
    let n := state.2.1 * 256 + byte.toNat
    if state.1 + 1 = width then (0, 0, state.2.2 && unicodeScalar n)
    else (state.1 + 1, n, state.2.2)) (0, 0, true)
  -- The octets form whole characters, and each character is a Unicode scalar.
  state.1 == 0 && state.2.2

/-- Validate the certificate subset of DER values, including values inside a Name.

Every other tag, primitive or constructed, is rejected.

X.690 §§8.2–8.12, 8.19, 8.23 and 11 fix these encodings. -/
def validate (value : Value) : Except Error Unit := go (value.encoded.size + 1) value
where
  go : Nat → Value → Except Error Unit
    -- Unreachable: each level of nesting is at least two octets shorter than the one above it.
    | 0, _ => .error .value
    | fuel + 1, value => do
      match value.tag.toNat with
      -- BOOLEAN, §8.2 and §11.1.
      | 1 => let _ ← boolean value; pure ()
      -- INTEGER, §8.3.
      | 2 => let _ ← integer value; pure ()
      -- BIT STRING, §8.6.2 and §11.2.1, primitive as §10.2 asks.
      | 3 => validBits value.content
      -- OCTET STRING, §8.7.2: any contents octets, primitive as §10.2 asks.
      | 4 => pure ()
      -- NULL, §8.8.2: no contents octets.
      | 5 => if value.content.isEmpty then pure () else throw .value
      -- OBJECT IDENTIFIER, §8.19.
      | 6 => let _ ← oid value; pure ()
      -- UTF8String, §8.23.10: the UTF-8 octets of ISO/IEC 10646, Annex D.
      | 12 => if (String.fromUTF8? value.content).isSome then pure () else throw .value
      -- PrintableString: the letters, the digits, the space and `' ( ) + , - . / : = ?`.
      --
      -- X.680 §41.4, Table 10, lists those characters.
      | 19 =>
        if value.content.data.toList.all (fun byte =>
          (48 ≤ byte.toNat && byte.toNat ≤ 57) ||
          (65 ≤ byte.toNat && byte.toNat ≤ 90) ||
          (97 ≤ byte.toNat && byte.toNat ≤ 122) ||
          ([32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63] : List UInt8).contains byte)
        then pure () else throw .value
      -- IA5String: X.680 Table 8 gives registers 1 and 6, SPACE and DELETE, so octets below 0x80.
      | 22 =>
        if value.content.data.toList.all (fun b => b.toNat < 128) then pure ()
        else throw .value
      -- UniversalString, §8.23.7: four octets per character.
      | 28 => if fixedString 4 value.content.data.toList then pure () else throw .value
      -- BMPString, §8.23.8: two octets per character.
      | 30 => if fixedString 2 value.content.data.toList then pure () else throw .value
      -- SEQUENCE, SEQUENCE OF, SET and SET OF, constructed (§8.9.1, §8.10.1, §8.11.1, §8.12.1).
      | 48 | 49 =>
        let values ← children value.content
        -- §11.6: the components of a SET OF appear in ascending order, compared as octet strings.
        --
        -- No encoding is a proper prefix of another, so the zero padding of §11.6 never decides.
        --
        -- The tag 0x31 also marks a SET, whose components §10.3 orders by their tags instead.
        --
        -- EthLib asks the order of §11.6 of every value of that tag.
        if value.tag = 49 then
          if (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·) then pure ()
          else throw .value
        -- Each component is valid in turn.
        values.forM (go fuel)
      -- Every other tag is rejected, among them the constructed strings that §10.2 forbids.
      | _ => throw (.tag none value.tag)

/-! ## ECDSA signatures

An ECDSA signature value is the SEQUENCE of the INTEGERs r and s ([RFC 3279 §2.2.3][rfc3279]).

[rfc3279]: https://www.rfc-editor.org/rfc/rfc3279#section-2.2.3
-/

/-- The DER INTEGER of a number below `2 ^ 256`, on the fewest content bytes (X.690 §8.3.2). -/
def ecdsaInteger (n : Nat) : List UInt8 :=
  -- §8.3.2: the fewest octets, so the leading zero octets of the 32-octet form go.
  let bytes := (EthLib.Base.natToBytes 32 n).dropWhile (· == 0)
  let bytes := match bytes with
    -- §8.3.1: zero is one contents octet, 0x00.
    | [] => [0]
    -- §8.3.3: two's complement, so a set bit 8 needs a 0x00 octet first to stay positive.
    | b :: _ => if b.toNat ≥ 128 then 0 :: bytes else bytes
  -- The identifier 0x02, then the short form length (§8.1.3.4), since there are at most 33 octets.
  [0x02, UInt8.ofNat bytes.length] ++ bytes

/-- The DER SEQUENCE of the two ECDSA scalars r and s. -/
def encodeEcdsaSignature (r s : Nat) : ByteArray :=
  -- RFC 3279 §2.2.3: `Ecdsa-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }`.
  let integers := ecdsaInteger r ++ ecdsaInteger s
  -- The identifier 0x30, then the short form length, since the two INTEGERs take at most 70 octets.
  ⟨([0x30, UInt8.ofNat integers.length] ++ integers).toArray⟩

/-- The two positive scalars below `2 ^ 256` of a strict DER ECDSA signature.

It serves every curve whose group order is at most `2 ^ 256`.

Each curve checks its own scalar ranges after this read. -/
def decodeEcdsaScalars (signature : ByteArray) : Option (Nat × Nat) :=
  match signature.data.toList with
  -- RFC 3279 §2.2.3: a SEQUENCE (0x30) whose first component is the INTEGER r (0x02).
  | 0x30 :: total :: 0x02 :: rLength :: rest =>
    -- The SEQUENCE spans the whole input, so no octet trails it.
    if total.toNat + 2 != signature.size then none
    else
      -- After the contents of r, the INTEGER s ends the SEQUENCE.
      match rest.drop rLength.toNat with
      | 0x02 :: sLength :: sBytes =>
        if sLength.toNat != sBytes.length then none
        else
          -- The contents read as unsigned numbers; the encoding below rejects any other reading.
          let r := EthLib.Base.bytesToNat (rest.take rLength.toNat)
          let s := EthLib.Base.bytesToNat sBytes
          -- EthLib's checks: `0 < r, s < 2^256`, as no ECDSA scalar is zero.
          --
          -- The input must be the DER encoding of `(r, s)`.
          --
          -- So a long form length, a redundant octet and a negative INTEGER are rejected.
          if 0 < r ∧ r < 2 ^ 256 ∧ 0 < s ∧ s < 2 ^ 256 ∧ encodeEcdsaSignature r s = signature then
            some (r, s)
          else none
      | _ => none
  | _ => none

end EthLib.Serialization.Der

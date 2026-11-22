module

public import EthLib.Networking.Quic.Varint
public import EthLib.Networking.Encoding.ByteReader
public import EthLib.Base.Bytes

/-!
# QUIC wire fields

The readers consume one field and return the bytes after it.

[RFC 9000 §16][rfc] defines the integer encoding.

Headers (§17) and frames (§19) use it to prefix byte strings with their length.

[rfc]: https://www.rfc-editor.org/rfc/rfc9000#section-16
-/

@[expose] public section

namespace EthLib.Networking.Quic.Wire

/-- Reasons to reject a QUIC header or frame. -/
inductive Error where
  /-- A field needs `needed` bytes, and only `available` are left.

  Before the first byte of an integer, `needed` is 1, the byte that selects its length. -/
  | truncated (needed available : Nat)
  /-- A connection ID has `length` bytes, more than `maximum` (§§17.2, 17.3.1).

  A long header carries the length; a short header takes it from the connection. -/
  | connectionIdLength (length maximum : Nat)
  /-- The fixed bit of the first byte `first` is 0 (§§17.2, 17.3.1). -/
  | fixedBit (first : UInt8)
  /-- The long header carries the version `version`, which is neither 0 nor 1 (§17.2). -/
  | version (version : Nat)
  /-- A reserved bit of the first byte `first` is set (§§17.2, 17.3.1). -/
  | reservedBits (first : UInt8)
  /-- A header length is too small for its fields, or an encoded header breaks a field bound. -/
  | packetLength
  /-- A truncated packet number cannot be expanded (Appendix A.3).

  The fields hold the truncated number, its width in bytes and the expected next number. -/
  | packetNumber (truncated width expected : Nat)
  /-- A frame breaks the format of its type, or a length is `2^62` or more (§§19, 20.1). -/
  | frameEncoding
  /-- A frame of type `type` is not allowed in its packet type (§12.4, Table 3). -/
  | protocolViolation (type : Nat)
  deriving Repr, DecidableEq

/-- Stable local error codes, independent of transport error codes. -/
def Error.code : Error → UInt32
  | .truncated .. => 1
  | .connectionIdLength .. => 2
  | .fixedBit _ => 3
  | .version _ => 4
  | .reservedBits _ => 5
  | .packetLength => 6
  | .packetNumber .. => 7
  | .frameEncoding => 8
  | .protocolViolation _ => 9

/-- A field reader carries the bytes still to be read. -/
abbrev Reader (α : Type) := Encoding.ByteReader.Reader Error α

/-- Read exactly the requested bytes, without padding a truncated field. -/
abbrev bytes (n : Nat) : Reader (List UInt8) := fun input =>
  Encoding.ByteReader.bytes (.truncated n input.length) n input

/-- Read a fixed-length byte vector without defaulting or padding. -/
abbrev vector (n : Nat) : Reader (Vector UInt8 n) := fun input =>
  Encoding.ByteReader.vector (.truncated n input.length) n input

/-- Read a big-endian integer of the given byte width. -/
abbrev uint (n : Nat) : Reader Nat := fun input =>
  Encoding.ByteReader.uint (.truncated n input.length) n input

/-- Read one byte. -/
def byte : Reader UInt8 := fun input =>
  match input with
  -- No byte is left: the field is truncated.
  | [] => .error (.truncated 1 0)
  -- The first byte, and the bytes after it.
  | head :: tail => .ok (head, tail)

/-- Read a QUIC integer, accepting the nonminimal forms permitted by RFC 9000 §16. -/
def varint : Reader Varint := fun input =>
  -- A variable-length integer of §16, whose truncation is the truncation of the field.
  (Varint.decodeList input).mapError fun
    | .truncated needed available => .truncated needed available

/-- Reject a field that does not meet its format constraint. -/
abbrev require (condition : Prop) [Decidable condition] (error : Error) : Reader Unit :=
  Encoding.ByteReader.require condition error

/-- Read every remaining byte of a packet. -/
def remainder : Reader (List UInt8) := fun input =>
  -- Every byte left, and none after it.
  .ok (input, [])

/-- Convert a length to a QUIC integer, rejecting `2^62` or more. -/
def checkedVarint (n : Nat) : Except Error Varint :=
  -- §16: a variable-length integer holds at most 62 bits, so a length of `2^62` or more fails.
  if h : n < 2 ^ 62 then .ok ⟨n, h⟩ else .error .frameEncoding

/-- Read a byte string prefixed by its length as a QUIC integer. -/
def blob : Reader (List UInt8) := do
  -- A length, as a variable-length integer (§16), such as Token Length (i) of §17.2.2.
  let n ← varint
  -- Then exactly that many bytes, such as Token (..).
  bytes n.val

/-- Encode a byte string whose length fits a QUIC integer. -/
def encodeBlob (data : List UInt8) : Except Error (List UInt8) := do
  -- The length of the string, as a variable-length integer (§16).
  let n ← checkedVarint data.length
  -- The length in its shortest form, then the bytes of the string.
  return Varint.encodeList n ++ data

end EthLib.Networking.Quic.Wire

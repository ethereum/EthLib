module

public import EthLib.Networking.Quic.Varint

/-!
# QUIC wire fields

The readers consume one field and return the bytes after it.

RFC 9000 §16 defines the integer encoding.

Headers (§17) and frames (§19) use it to prefix byte strings with their length.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Wire

/-- Reasons to reject a QUIC header or frame. -/
inductive Error where
  | truncated
  | connectionIdLength
  | fixedBit
  | version
  | reservedBits
  | packetLength
  | packetNumber
  | frameEncoding
  | protocolViolation
  deriving Repr, DecidableEq

/-- Stable local error codes, independent of transport error codes. -/
def Error.code : Error → UInt32
  | .truncated => 1
  | .connectionIdLength => 2
  | .fixedBit => 3
  | .version => 4
  | .reservedBits => 5
  | .packetLength => 6
  | .packetNumber => 7
  | .frameEncoding => 8
  | .protocolViolation => 9

/-- A field reader carries the bytes still to be read. -/
abbrev Reader (α : Type) := StateT (List UInt8) (Except Error) α

/-- Read exactly the requested bytes, without padding a truncated field. -/
def bytes (n : Nat) : Reader (List UInt8) := fun input =>
  let field := input.take n
  if field.length = n then .ok (field, input.drop n) else .error .truncated

/-- Read a big-endian integer of the given byte width. -/
def uint (n : Nat) : Reader Nat := do
  return Base.bytesToNat (← bytes n)

/-- Read one byte. -/
def byte : Reader UInt8 := fun input =>
  match input with
  | [] => .error .truncated
  | head :: tail => .ok (head, tail)

/-- Read a QUIC integer, accepting the nonminimal forms permitted by RFC 9000 §16. -/
def varint : Reader Varint := fun input =>
  (Varint.decode input).mapError fun _ => .truncated

/-- Reject a field that does not meet its format constraint. -/
def require (condition : Prop) [Decidable condition] (error : Error) : Reader Unit :=
  fun input => if condition then .ok ((), input) else .error error

/-- Read every remaining byte of a packet. -/
def remainder : Reader (List UInt8) := fun input => .ok (input, [])

/-- Convert a length to a QUIC integer, rejecting `2^62` or more. -/
def checkedVarint (n : Nat) : Except Error Varint :=
  if h : n < 2 ^ 62 then .ok ⟨n, h⟩ else .error .frameEncoding

/-- Read a byte string prefixed by its length as a QUIC integer. -/
def blob : Reader (List UInt8) := do
  let n ← varint
  bytes n.val

/-- Encode a byte string whose length fits a QUIC integer. -/
def encodeBlob (data : List UInt8) : Except Error (List UInt8) := do
  let n ← checkedVarint data.length
  return Varint.encode n ++ data

end EthLib.Networking.Quic.Wire

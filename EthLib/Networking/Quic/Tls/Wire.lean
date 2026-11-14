module

public import EthLib.Base.BigEndian
public import EthLib.Base.Except

/-!
# TLS presentation-language fields

[RFC 8446 §§3.3 and 3.4][fields] use big-endian integers and length-prefixed vectors.

Readers return the bytes after a field and reject truncated or out-of-range lengths.

The errors are local codec errors, rather than TLS alerts or QUIC connection errors.

[fields]: https://www.rfc-editor.org/rfc/rfc8446#section-3.3
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Wire

/-- A malformed wire field, an unsupported message, or a misplaced transcript retry. -/
inductive Error where
  | truncated
  | length
  | trailing
  | constant
  | duplicateExtension
  | messageType
  | retry
  deriving Repr, DecidableEq

/-- Stable local codes, independent of the TLS alert numbers. -/
def Error.code : Error → UInt32
  | .truncated => 1
  | .length => 2
  | .trailing => 3
  | .constant => 4
  | .duplicateExtension => 5
  | .messageType => 6
  | .retry => 7

/-- A reader consumes a prefix of a byte list. -/
abbrev Reader (α : Type) := StateT (List UInt8) (Except Error) α

/-- Require a format condition without consuming input. -/
def require (condition : Prop) [Decidable condition] (error : Error) : Reader Unit :=
  fun input => if condition then .ok ((), input) else .error error

/-- Read exactly `n` bytes, without padding an incomplete field. -/
def bytes (n : Nat) : Reader (List UInt8) := fun input =>
  if n ≤ input.length then .ok (input.take n, input.drop n) else .error .truncated

/-- Read a big-endian integer of the given width, RFC 8446 §3.3. -/
def uint (width : Nat) : Reader Nat := do
  return Base.bytesToNat (← bytes width)

/-- A two-byte protocol identifier, without an algorithm-selection policy. -/
abbrev CodePoint := Fin (2 ^ 16)

/-- Read a two-byte identifier, preserving unrecognized values. -/
def codePoint : Reader CodePoint := do
  let n ← uint 2
  if h : n < 2 ^ 16 then return ⟨n, h⟩ else throw .length

/-- Read a fixed-size byte vector. -/
def vector (n : Nat) : Reader (Vector UInt8 n) := do
  let data ← bytes n
  if h : data.length = n then return ⟨data.toArray, by simpa using h⟩
  else throw .truncated

/-- Read a vector whose encoded byte length lies between the inclusive bounds (§3.4). -/
def blob (width minimum maximum : Nat) : Reader (List UInt8) := do
  let size ← uint width
  require (minimum ≤ size ∧ size ≤ maximum) .length
  bytes size

/-- Encode a vector after checking both its bounds and its length-field capacity (§3.4). -/
def encodeBlob (width minimum maximum : Nat) (data : List UInt8) :
    Except Error (List UInt8) :=
  if minimum ≤ data.length ∧ data.length ≤ maximum ∧ data.length < 256 ^ width then
    .ok (Base.natToBytes width data.length ++ data)
  else .error .length

/-- Parse an isolated field and reject any bytes its reader leaves. -/
def exact (reader : Reader α) (input : List UInt8) : Except Error α := do
  let (value, rest) ← reader input
  if rest = [] then return value else throw .trailing

/-- Read consecutive entries until the isolated vector ends.

The fuel is the vector's byte length; every entry reader used here consumes at least one byte. -/
def many (reader : Reader α) : Nat → List UInt8 → Except Error (List α)
  | _, [] => .ok []
  | 0, _ :: _ => .error .length
  | fuel + 1, input@(_ :: _) => do
    let (value, rest) ← reader input
    return value :: (← many reader fuel rest)

/-- Parse each entry of an isolated vector. -/
def entries (reader : Reader α) (input : List UInt8) : Except Error (List α) :=
  many reader input.length input

/-- Encode entries in order, stopping at the first malformed field. -/
def encodeEntries (encoder : α → Except Error (List UInt8)) :
    List α → Except Error (List UInt8)
  | [] => .ok []
  | value :: rest => do
    return (← encoder value) ++ (← encodeEntries encoder rest)

/-- Read a length-prefixed vector of entries, with no trailing partial entry (§3.4). -/
def items (width minimum maximum : Nat) (reader : Reader α) : Reader (List α) := do
  let data ← blob width minimum maximum
  StateT.lift (entries reader data)

/-- Encode entries and prefix their byte length (§3.4). -/
def encodeItems (width minimum maximum : Nat) (encoder : α → Except Error (List UInt8))
    (values : List α) : Except Error (List UInt8) := do
  encodeBlob width minimum maximum (← encodeEntries encoder values)

end EthLib.Networking.Quic.Tls.Wire

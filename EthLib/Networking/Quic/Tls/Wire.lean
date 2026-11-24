module

public import EthLib.Base.ByteOrder
public import EthLib.Base.Except
public import EthLib.Networking.Encoding.ByteReader
public import EthLib.Base.Bytes

/-!
# TLS presentation-language fields

[RFC 9846 §3.3][numbers] and [§3.4][vectors] use big-endian integers and length-prefixed vectors.

Readers return the bytes after a field and reject truncated or out-of-range lengths.

The errors are local codec errors, rather than TLS alerts or QUIC connection errors.

[numbers]: https://www.rfc-editor.org/rfc/rfc9846#section-3.3
[vectors]: https://www.rfc-editor.org/rfc/rfc9846#section-3.4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls.Wire

/-- A malformed wire field, an unsupported message, or a misplaced transcript retry.

A fixed field with another value, or an extension of the wrong type, is a constant error.

The legacy version of a hello has its own error, since its alert differs. -/
inductive Error where
  /-- A field needs `needed` bytes, and only `available` are left. -/
  | truncated (needed available : Nat)
  /-- A length is outside the bounds of its field, or does not fit its length field (§3.4). -/
  | length
  /-- A field that must fill its input leaves `count` bytes after it. -/
  | trailing (count : Nat)
  /-- A fixed field has another value, or an extension has the wrong type. -/
  | constant
  /-- The extension type `type` occurs twice in one block (§4.3). -/
  | duplicateExtension (type : Fin (2 ^ 16))
  /-- The handshake type `type` is not one this codec reads (§4). -/
  | messageType (type : UInt8)
  /-- The transcript cannot take a retry here: it has already retried, or has more messages. -/
  | retry
  /-- A hello's legacy version is not `0x0303` (RFC 9846 §§4.2.2 to 4.2.4). -/
  | legacyVersion
  deriving Repr, DecidableEq

/-- Stable local codes, independent of the TLS alert numbers. -/
def Error.code : Error → UInt32
  | .truncated .. => 1
  | .length => 2
  | .trailing _ => 3
  | .constant => 4
  | .duplicateExtension _ => 5
  | .messageType _ => 6
  | .retry => 7
  | .legacyVersion => 8

/-- A reader consumes a prefix of a byte list. -/
abbrev Reader (α : Type) := Encoding.ByteReader.Reader Error α

/-- Require a format condition without consuming input. -/
abbrev require (condition : Prop) [Decidable condition] (error : Error) : Reader Unit :=
  Encoding.ByteReader.require condition error

/-- Read exactly `n` bytes, without padding an incomplete field. -/
abbrev bytes (n : Nat) : Reader (List UInt8) := fun input =>
  Encoding.ByteReader.bytes (.truncated n input.length) n input

/-- Read a big-endian integer of the given width, RFC 9846 §3.3. -/
abbrev uint (width : Nat) : Reader Nat := fun input =>
  -- §3.3: the given number of bytes, in network byte (big-endian) order.
  Encoding.ByteReader.uint (.truncated width input.length) width input

/-- A two-byte protocol identifier, without an algorithm-selection policy. -/
abbrev CodePoint := Fin (2 ^ 16)

/-- Read a two-byte identifier, preserving unrecognized values. -/
def codePoint : Reader CodePoint := do
  -- A `uint16` (§3.3), as `ExtensionType`, `NamedGroup` and the like are.
  let n ← uint 2
  -- Two bytes always hold a value below `2^16`, so the length error is never reached.
  if h : n < 2 ^ 16 then return ⟨n, h⟩ else throw .length

/-- Read a fixed-size byte vector. -/
abbrev vector (n : Nat) : Reader (Vector UInt8 n) := fun input =>
  Encoding.ByteReader.vector (.truncated n input.length) n input

/-- Read a vector whose encoded byte length lies between the inclusive bounds (§3.4). -/
def blob (width minimum maximum : Nat) : Reader (List UInt8) := do
  -- §3.4: `T T'<floor..ceiling>`: the actual length precedes the vector's contents.
  --
  -- It takes as many bytes as the ceiling needs, and the caller gives that width.
  let size ← uint width
  -- §3.4: the legal lengths lie in `floor..ceiling`, inclusively, counted in bytes.
  require (minimum ≤ size ∧ size ≤ maximum) .length
  -- Then the contents: exactly `size` bytes.
  bytes size

/-- Encode a vector after checking both its bounds and its length-field capacity (§3.4). -/
def encodeBlob (width minimum maximum : Nat) (data : List UInt8) :
    Except Error (List UInt8) :=
  -- §3.4: the length lies in `floor..ceiling`, and it fits in its length field.
  if minimum ≤ data.length ∧ data.length ≤ maximum ∧ data.length < 256 ^ width then
    -- The actual length, big-endian (§3.3), then the contents.
    .ok ((Base.ByteOrder.toBE width data.length).toList ++ data)
  else .error .length

/-- Parse an isolated field and reject any bytes its reader leaves. -/
def exact (reader : Reader α) (input : List UInt8) : Except Error α := do
  let (value, rest) ← reader input
  if rest = [] then return value else throw (.trailing rest.length)

/-- Read consecutive entries until the isolated vector ends.

The fuel is the vector's byte length; every entry reader used here consumes at least one byte. -/
def many (reader : Reader α) : Nat → List UInt8 → Except Error (List α)
  -- The vector ends exactly where its last entry ends.
  | _, [] => .ok []
  -- Out of fuel with bytes left, which an entry reader of at least one byte never reaches.
  | 0, _ :: _ => .error .length
  -- §3.4: the vector holds whole entries, so a partial last entry fails in its reader.
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
  -- §3.4: the length declares the number of bytes, not the number of elements.
  let data ← blob width minimum maximum
  -- Those bytes hold whole entries only: a 17-byte vector of `uint16` is illegal (§3.4).
  StateT.lift (entries reader data)

/-- Encode entries and prefix their byte length (§3.4). -/
def encodeItems (width minimum maximum : Nat) (encoder : α → Except Error (List UInt8))
    (values : List α) : Except Error (List UInt8) := do
  -- §3.4: the byte length of the entries, within the bounds, then the entries in order.
  encodeBlob width minimum maximum (← encodeEntries encoder values)

end EthLib.Networking.Quic.Tls.Wire

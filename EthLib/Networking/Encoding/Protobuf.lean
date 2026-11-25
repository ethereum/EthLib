module

public import EthLib.Networking.Encoding.Varint
public import EthLib.Networking.Encoding.ByteReader

/-!
# The protobuf wire format

The binary records of protocol buffers, from the [encoding guide][encoding].

A message is a sequence of records, as the section Message Structure of the guide says.

A record is a key, then a value.

The wire type in the key says how long the value is, so a reader can skip a field it does not know.

A reader rejects field numbers outside 1 to `2^29 - 1`, the range of [the proto2 guide][fields].

[encoding]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/encoding.md
[fields]: https://github.com/protocolbuffers/protocolbuffers.github.io/blob/bc2f346991e20631ed0a884e345110738228bfae/content/programming-guides/proto2.md#assigning-field-numbers-assigning
-/

@[expose] public section

namespace EthLib.Networking.Encoding.Protobuf

open EthLib.Networking.Encoding.Varint (VarintError)

/-- The largest field number. -/
def maxField : Nat := 2 ^ 29 - 1

/-- Every way reading records can fail. -/
inductive ProtobufError where
  /-- A key, a length or a varint value ends early, runs past ten bytes, or is at least `2^64`. -/
  | varint (error : VarintError)
  /-- A key holds the field number 0, or one above `2^29 - 1`. -/
  | fieldNumber (field : Nat)
  /-- A key holds the wire type 6 or 7, or a group end outside any group. -/
  | wireType (wire : Nat)
  /-- The input ends inside a value or inside a group.

  A value needs `needed` bytes and only `available` remain.

  Input that ends inside a group usually fails on the next key, as a varint error.

  This error comes instead, with one byte needed, when the group reader runs out of steps. -/
  | truncated (needed available : Nat)
  /-- A group ends with the number of another field. -/
  | groupEnd (field : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def ProtobufError.code : ProtobufError → UInt32
  | .varint _ => 1
  | .fieldNumber _ => 2
  | .wireType _ => 3
  | .truncated .. => 4
  | .groupEnd _ => 5

/-- The value of a record, by wire type.

A group keeps no content: a reader skips it, after checking that it is well nested. -/
inductive Value where
  /-- Wire type 0, a varint. -/
  | varint (value : UInt64)
  /-- Wire type 1, eight bytes. -/
  | i64 (bytes : Vector UInt8 8)
  /-- Wire type 2, a varint length and that many bytes. -/
  | len (bytes : ByteArray)
  /-- Wire types 3 and 4, the start and the end of a group. -/
  | group
  /-- Wire type 5, four bytes. -/
  | i32 (bytes : Vector UInt8 4)
  deriving DecidableEq

/-- The wire type of a value; a group is written with its start type. -/
def Value.wireType : Value → Nat
  | .varint _ => 0
  | .i64 _ => 1
  | .len _ => 2
  | .group => 3
  | .i32 _ => 5

/-- One record: a field number and its value. -/
structure Record where
  field : Nat
  value : Value
  deriving DecidableEq

/-- A record that the encoding can carry: its field number is in range.

A length-delimited value must also be shorter than `2^64` bytes, so that its length is a varint. -/
def Record.WellFormed (r : Record) : Prop :=
  0 < r.field ∧ r.field ≤ maxField ∧
    match r.value with
    | .len bytes => bytes.size < 2 ^ 64
    | _ => True

/-! ## Reading -/

/-- The varint at the start of the input, and the bytes after it.

It may run to ten bytes, and its value must be below `2^64`. -/
def readVarint (bytes : List UInt8) : Except ProtobufError (UInt64 × List UInt8) := do
  -- Base 128 Varints: the varint ends at the first byte whose MSB, the continuation bit, is clear.
  let (head, rest) := Varint.split bytes
  -- Base 128 Varints: one to ten bytes, each with its MSB set but the last.
  --
  -- The section asks for no shortest form, so no minimality check is made here.
  let groups ← (Varint.groups Varint.maxLength head).mapError .varint
  -- Base 128 Varints: the 7-bit payloads, little-endian, are an unsigned 64-bit integer.
  --
  -- The guide leaves a sum of `2^64` or more unspecified, and this reader rejects it.
  if 2 ^ 64 ≤ Varint.valueOf groups then throw (.varint (.overflow (Varint.valueOf groups)))
  return (UInt64.ofNat (Varint.valueOf groups), rest)

/-- The field number and the wire type of the key at the start of the input. -/
def readKey (bytes : List UInt8) : Except ProtobufError (Nat × Nat × List UInt8) := do
  -- Message Structure: the tag is the varint `(f << 3) | t`, for field number `f`, wire type `t`.
  --
  -- The guide's card encodes it as a uint32 varint, and this reader takes any 64-bit varint.
  --
  -- A tag of `2^32` or more has a field number above `2^29 - 1`, so the next check rejects it.
  let (key, rest) ← readVarint bytes
  -- Message Structure: the rest of the integer, after the low 3 bits, is the field number.
  let field := key.toNat / 8
  -- The proto2 guide: field numbers run from 1 to `2^29 - 1`.
  if field = 0 ∨ maxField < field then throw (.fieldNumber field)
  -- Message Structure: the low 3 bits are the wire type.
  return (field, key.toNat % 8, rest)

/-- The first `n` bytes of the input, and the bytes after them. -/
def readFixed (n : Nat) (bytes : List UInt8) : Except ProtobufError (Vector UInt8 n × List UInt8) :=
  -- The next `n` bytes, all in the input.
  --
  -- They are a lump of Non-varint Numbers, or the payload of a length-delimited record.
  Encoding.ByteReader.vector (.truncated n) n bytes

/-- A length-delimited value: a varint length, then that many bytes. -/
def readLen (bytes : List UInt8) : Except ProtobufError (ByteArray × List UInt8) := do
  -- Length-Delimited Records: the length is a varint immediately after the tag.
  --
  -- The guide encodes it as an int32 varint, for at most 2 GB.
  --
  -- This reader takes any 64-bit length, and a length past the end of the input fails.
  let (size, rest) ← readVarint bytes
  -- Length-Delimited Records: the payload of that many bytes follows.
  let (value, rest) ← readFixed size.toNat rest
  return (⟨value.toArray⟩, rest)

/-- The value of a wire type other than a group, and the bytes after it. -/
def readScalar (wire : Nat) (bytes : List UInt8) : Except ProtobufError (Value × List UInt8) :=
  match wire with
  -- Message Structure: wire type 0, `VARINT`, is a varint.
  | 0 => (readVarint bytes).map fun (v, rest) => (.varint v, rest)
  -- Non-varint Numbers: wire type 1, `I64`, is a fixed eight-byte lump.
  | 1 => (readFixed 8 bytes).map fun (b, rest) => (.i64 b, rest)
  -- Length-Delimited Records: wire type 2, `LEN`, is a length, then that many bytes.
  | 2 => (readLen bytes).map fun (b, rest) => (.len b, rest)
  -- Non-varint Numbers: wire type 5, `I32`, is a fixed four-byte lump.
  | 5 => (readFixed 4 bytes).map fun (b, rest) => (.i32 b, rest)
  -- Message Structure lists the six wire types 0 to 5, so this reader rejects 6 and 7.
  --
  -- Type 3, `SGROUP`, never reaches this point: the record and group readers take it first.
  --
  -- Type 4, `EGROUP`, reaches it only outside any group, where it is malformed.
  | _ => .error (.wireType wire)

/-- The bytes after every open group, checking that each end matches its start.

The list holds the field numbers of the open groups, innermost first.

Each step reads a key, so a budget of one step per input byte never runs out. -/
def skipGroup : Nat → List Nat → List UInt8 → Except ProtobufError (List UInt8)
  -- Every group is closed: the bytes after the last end tag remain.
  | _, [], bytes => .ok bytes
  -- Out of steps inside a group: one more byte is needed, for an end key.
  | 0, _ :: _, bytes => .error (.truncated 1 bytes.length)
  | fuel + 1, expected :: outer, bytes => do
    -- Groups: the next key is a field of the group, a nested start, or the end tag that closes it.
    let (field, wire, rest) ← readKey bytes
    match wire with
    -- Groups: an `SGROUP` tag with no payload starts a group, here nested in the open one.
    | 3 => skipGroup fuel (field :: expected :: outer) rest
    -- Groups: an `EGROUP` tag with no payload ends a group, and its field number must match.
    --
    -- `7:EGROUP` where `8:EGROUP` is expected makes the message malformed.
    | 4 => if field = expected then skipGroup fuel outer rest else throw (.groupEnd field)
    -- Any other record of the group is read and dropped, as a group keeps no content here.
    | _ => skipGroup fuel (expected :: outer) (← readScalar wire rest).2

/-- The record at the start of the input, and the bytes after it. -/
def readRecord (bytes : List UInt8) : Except ProtobufError (Record × List UInt8) := do
  -- Message Structure: a record is a tag, then the payload its wire type describes.
  let (field, wire, rest) ← readKey bytes
  -- Groups: an `SGROUP` tag starts a group, read up to its matching `EGROUP` tag.
  if wire = 3 then
    return (⟨field, .group⟩, ← skipGroup rest.length [field] rest)
  let (value, rest) ← readScalar wire rest
  return (⟨field, value⟩, rest)

/-- The records of a message, in the order of the input. -/
def records (bytes : List UInt8) : Except ProtobufError (List Record) :=
  go bytes.length bytes []
where
  /-- Each record takes at least one byte, so a budget of the input length never runs out. -/
  go : Nat → List UInt8 → List Record → Except ProtobufError (List Record)
    -- Condensed Reference Card: a message is `(tag value)*`, so it may end after any record.
    | _, [], acc => .ok acc.reverse
    -- Out of fuel: unreachable, so the fields are arbitrary.
    | 0, bytes@(_ :: _), _ => .error (.truncated 1 bytes.length)
    -- Otherwise the next record starts here.
    | fuel + 1, bytes@(_ :: _), acc => do
      let (record, rest) ← readRecord bytes
      go fuel rest (record :: acc)

/-- The values of one field, in the order of the records. -/
def valuesOf (rs : List Record) (field : Nat) : List Value :=
  -- Repeated Elements: records of one field may interleave with others, and keep their order.
  --
  -- A packed payload stays one `LEN` value here, since only the field's type can split it.
  rs.filterMap fun r => if r.field = field then some r.value else none

/-! ## Writing -/

/-- A length-delimited record. -/
def lenRecord (field : Nat) (bytes : ByteArray) : Record := ⟨field, .len bytes⟩

/-- A string record, in UTF-8. -/
def stringRecord (field : Nat) (s : String) : Record := lenRecord field s.toUTF8

/-- The key of a field number and a wire type. -/
def encodeKey (field wire : Nat) : List UInt8 :=
  -- Message Structure: the varint `(f << 3) | t`, written `8 f + t`, as each caller passes `t < 8`.
  --
  -- A field number in range keeps the tag below `2^32`, so it fits the 64-bit varint.
  Varint.encode (UInt64.ofNat (field * 8 + wire))

/-- The bytes of a value after its key; a group writes only its end key. -/
def encodeValue (field : Nat) : Value → List UInt8
  -- `VARINT`: the value as a varint.
  | .varint v => Varint.encode v
  -- `I64` and `I32`: the eight or four bytes as they are.
  | .i64 bytes => bytes.toList
  | .i32 bytes => bytes.toList
  -- Length-Delimited Records: the length as a varint, then the payload.
  --
  -- The guide caps the length at 2 GB, and this writer takes any length below `2^64`.
  | .len bytes => Varint.encode (UInt64.ofNat bytes.size) ++ bytes.data.toList
  -- Groups: the start tag has an empty payload, and the end tag of the same field closes it.
  --
  -- A group keeps no content, so nothing is written between the two tags.
  | .group => encodeKey field 4

/-- The bytes of a record. -/
def encodeRecord (r : Record) : List UInt8 :=
  -- Message Structure: the tag, then the payload.
  encodeKey r.field r.value.wireType ++ encodeValue r.field r.value

/-- The bytes of a sequence of records. -/
def encodeRecords (rs : List Record) : List UInt8 :=
  -- Condensed Reference Card: a message is `(tag value)*`, its records one after the other.
  rs.flatMap encodeRecord

/-- The bytes of a message made of a sequence of records. -/
def serialize (rs : List Record) : ByteArray :=
  ⟨(encodeRecords rs).toArray⟩

end EthLib.Networking.Encoding.Protobuf

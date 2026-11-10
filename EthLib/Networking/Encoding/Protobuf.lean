module

public import EthLib.Networking.Encoding.Varint

/-!
# The protobuf wire format

The binary records of protocol buffers, from the [encoding guide][encoding].

A message is a sequence of records, as "Message Structure" says.

A record is a key, then a value.

The key is a varint: the field number times eight, plus the wire type.

The wire type says how long the value is, so a reader can skip a field it does not know.

The guide's "Base 128 Varints" asks for no shortest form.

So a reader accepts a varint longer than its value needs.

A reader skips a group, and checks that its end matches its start, as "Groups" says.

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
  /-- The input ends inside a value or inside a group. -/
  | truncated
  /-- A group ends with the number of another field. -/
  | groupEnd (field : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor. -/
def ProtobufError.code : ProtobufError → UInt32
  | .varint _ => 1
  | .fieldNumber _ => 2
  | .wireType _ => 3
  | .truncated => 4
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
  let (head, rest) := Varint.split bytes
  let groups ← (Varint.groups Varint.maxLength head).mapError .varint
  if 2 ^ 64 ≤ Varint.valueOf groups then throw (.varint .overflow)
  return (UInt64.ofNat (Varint.valueOf groups), rest)

/-- The field number and the wire type of the key at the start of the input. -/
def readKey (bytes : List UInt8) : Except ProtobufError (Nat × Nat × List UInt8) := do
  let (key, rest) ← readVarint bytes
  let field := key.toNat / 8
  if field = 0 ∨ maxField < field then throw (.fieldNumber field)
  return (field, key.toNat % 8, rest)

/-- The first `n` bytes of the input, and the bytes after them. -/
def readFixed (n : Nat) (bytes : List UInt8) : Except ProtobufError (Vector UInt8 n × List UInt8) :=
  if h : n ≤ bytes.length then
    .ok (⟨(bytes.take n).toArray, by simp [Nat.min_eq_left h]⟩, bytes.drop n)
  else .error .truncated

/-- A length-delimited value: a varint length, then that many bytes. -/
def readLen (bytes : List UInt8) : Except ProtobufError (ByteArray × List UInt8) := do
  let (size, rest) ← readVarint bytes
  let (value, rest) ← readFixed size.toNat rest
  return (⟨value.toArray⟩, rest)

/-- The value of a wire type other than a group, and the bytes after it. -/
def readScalar (wire : Nat) (bytes : List UInt8) : Except ProtobufError (Value × List UInt8) :=
  match wire with
  | 0 => (readVarint bytes).map fun (v, rest) => (.varint v, rest)
  | 1 => (readFixed 8 bytes).map fun (b, rest) => (.i64 b, rest)
  | 2 => (readLen bytes).map fun (b, rest) => (.len b, rest)
  | 5 => (readFixed 4 bytes).map fun (b, rest) => (.i32 b, rest)
  | _ => .error (.wireType wire)

/-- The bytes after every open group, checking that each end matches its start.

The list holds the field numbers of the open groups, innermost first.

Each step reads a key, so a budget of one step per input byte never runs out. -/
def skipGroup : Nat → List Nat → List UInt8 → Except ProtobufError (List UInt8)
  | _, [], bytes => .ok bytes
  | 0, _ :: _, _ => .error .truncated
  | fuel + 1, expected :: outer, bytes => do
    let (field, wire, rest) ← readKey bytes
    match wire with
    | 3 => skipGroup fuel (field :: expected :: outer) rest
    | 4 => if field = expected then skipGroup fuel outer rest else throw (.groupEnd field)
    | _ => skipGroup fuel (expected :: outer) (← readScalar wire rest).2

/-- The record at the start of the input, and the bytes after it. -/
def readRecord (bytes : List UInt8) : Except ProtobufError (Record × List UInt8) := do
  let (field, wire, rest) ← readKey bytes
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
    | _, [], acc => .ok acc.reverse
    | 0, _ :: _, _ => .error .truncated
    | fuel + 1, bytes@(_ :: _), acc => do
      let (record, rest) ← readRecord bytes
      go fuel rest (record :: acc)

/-- The values of one field, in the order of the records. -/
def valuesOf (rs : List Record) (field : Nat) : List Value :=
  rs.filterMap fun r => if r.field = field then some r.value else none

/-! ## Writing -/

/-- A length-delimited record. -/
def lenRecord (field : Nat) (bytes : ByteArray) : Record := ⟨field, .len bytes⟩

/-- A string record, in UTF-8. -/
def stringRecord (field : Nat) (s : String) : Record := lenRecord field s.toUTF8

/-- The key of a field number and a wire type. -/
def encodeKey (field wire : Nat) : List UInt8 :=
  Varint.encode (UInt64.ofNat (field * 8 + wire))

/-- The bytes of a value after its key; a group writes only its end key. -/
def encodeValue (field : Nat) : Value → List UInt8
  | .varint v => Varint.encode v
  | .i64 bytes => bytes.toList
  | .i32 bytes => bytes.toList
  | .len bytes => Varint.encode (UInt64.ofNat bytes.size) ++ bytes.data.toList
  | .group => encodeKey field 4

/-- The bytes of a record. -/
def encodeRecord (r : Record) : List UInt8 :=
  encodeKey r.field r.value.wireType ++ encodeValue r.field r.value

/-- The bytes of a sequence of records. -/
def encodeRecords (rs : List Record) : List UInt8 :=
  rs.flatMap encodeRecord

/-- The bytes of a message made of a sequence of records. -/
def serialize (rs : List Record) : ByteArray :=
  ⟨(encodeRecords rs).toArray⟩

end EthLib.Networking.Encoding.Protobuf

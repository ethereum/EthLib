module

public import EthLib.Base.BigEndian
public import EthLib.Base.Bytes
public import EthLib.Base.LittleEndian
public import EthLib.Serialization.Ssz.Codec.Deserialize

/-!
# `Serialization.E2store`

The e2store container: a file of typed records, one after the other.

The history files of Ethereum, era1 and era, are e2store files.

The [format documents][formats] build on it, and name each record type in their [type list][types].

[formats]: https://github.com/eth-clients/e2store-format-specs/tree/31cf6b577123bf1703eb3713f0b242f65fea806a
[types]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/types/README.md
[version]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/types/0x6532.md
[slotindex]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/types/0x6932.md

A record is an 8-byte header, then its data.

The header holds the type in 2 bytes, the length of the data in 4 bytes, then 2 reserved bytes.

The length is little-endian, and the reserved bytes are zero.

The documents of the [Version][version] and [SlotIndex][slotindex] types give the header 8 bytes.

The documents do not lay out those 8 bytes, so EthLib states the layout as its own definition.

A type is written as its two bytes in order, so the Version type `0x6532` is `e2` in ASCII.

The Version record must come first, as [its document][version] says.

Every Version record has no data, as that document also says.

A later Version record applies to the records after it, as when two files are concatenated.

An index record gives the position of each entry of a file, as an offset from the record.
-/

@[expose] public section

namespace EthLib.Serialization.E2store

open EthLib.Base

/-- A record: its type, as its two bytes read in order, and its data. -/
structure Record where
  /-- The type, as its two bytes read in order: `0x6532` is the bytes `0x65 0x32`. -/
  type : UInt16
  /-- The data, which must have fewer than `2^32` bytes to be written. -/
  data : ByteArray

/-- The type of the Version record, `e2` in ASCII. -/
def VERSION : UInt16 := 0x6532

/-- Why bytes are not an e2store file, or records cannot be written. -/
inductive E2storeError where
  /-- The bytes end inside the header of a record. -/
  | truncatedHeader
  /-- The bytes end inside the data of a record. -/
  | truncatedData
  /-- A reserved byte of a header is not zero. -/
  | reservedNotZero
  /-- The data of a record has `2^32` bytes or more, which its length cannot write.

  Only the encoder raises it. -/
  | dataTooLong
  /-- The first record is not a Version record. -/
  | noVersion
  /-- A Version record has data. -/
  | versionData
  /-- The data of an index record is not 16 bytes plus 8 bytes for each entry it counts. -/
  | indexSize
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def E2storeError.code : E2storeError → UInt32
  | .truncatedHeader => 1
  | .truncatedData => 2
  | .reservedNotZero => 3
  | .dataTooLong => 4
  | .noVersion => 5
  | .versionData => 6
  | .indexSize => 7

/-- The header of a record of the type `type` whose data has `length` bytes.

The type is big-endian, so its bytes come in the order the type list writes them.

A length of `2^32` or more keeps only its value modulo `2^32`, so the encoder rejects it first. -/
def encodeHeader (type : UInt16) (length : Nat) : ByteArray :=
  ⟨(natToBytes 2 type.toNat ++ (uintToBytes 4 length).toList ++ [0, 0]).toArray⟩

/-- The bytes of the records, one after the other.

Each record goes straight onto the output, so its data is copied once. -/
def encode (records : List Record) : Except E2storeError ByteArray :=
  records.foldlM (init := .empty) fun out record =>
    if record.data.size < 2 ^ 32 then
      .ok (out ++ encodeHeader record.type record.data.size ++ record.data)
    else
      .error .dataTooLong

/-- What a header says: the type of its record and the length of its data. -/
structure Header where
  /-- The type of the record. -/
  type : UInt16
  /-- The number of bytes of data after the header. -/
  length : Nat
  deriving Repr, DecidableEq

/-- The header at the position `offset` of `bytes`.

An index of an era1 or era file points at such a position. -/
def readHeader (bytes : ByteArray) (offset : Nat) : Except E2storeError Header :=
  if bytes.size < offset + 8 then
    .error .truncatedHeader
  else
    let byte (i : Nat) := byteAt bytes (offset + i)
    if byte 6 ≠ 0 ∨ byte 7 ≠ 0 then
      .error .reservedNotZero
    else
      .ok ⟨UInt16.ofNat (bytesToNat [byte 0, byte 1]),
        bytesToUint #v[byte 2, byte 3, byte 4, byte 5]⟩

/-- The records of `bytes` from the position `offset`, after the records `acc`. -/
def decodeFrom (bytes : ByteArray) (offset : Nat) (acc : Array Record) :
    Except E2storeError (List Record) :=
  if offset < bytes.size then
    match readHeader bytes offset with
    | .error e => .error e
    | .ok header =>
      if bytes.size < offset + 8 + header.length then
        .error .truncatedData
      else
        let data := bytes.extract (offset + 8) (offset + 8 + header.length)
        decodeFrom bytes (offset + 8 + header.length) (acc.push ⟨header.type, data⟩)
  else
    .ok acc.toList
termination_by bytes.size - offset

/-- The records of `bytes`, one after the other. -/
def decode (bytes : ByteArray) : Except E2storeError (List Record) :=
  decodeFrom bytes 0 #[]

/-- The records of an e2store file, which must start with a Version record.

Every Version record must have no data. -/
def decodeFile (bytes : ByteArray) : Except E2storeError (List Record) := do
  let records ← decode bytes
  unless (records.head?.map (·.type)) = some VERSION do throw .noVersion
  unless records.all (fun record => record.type != VERSION || record.data.size == 0) do
    throw .versionData
  return records

/-- The position of each record in the bytes that encode the records, from the position `pos`. -/
def recordStarts (pos : Nat) : List Record → List Nat
  | [] => []
  | record :: rest => pos :: recordStarts (pos + 8 + record.data.size) rest

/-! ### Index records -/

/-- An index record: the number of its first entry, then the offset of each entry.

An offset counts bytes from the start of the index record, so it may be negative. -/
structure Index where
  /-- The number of the first entry, such as a block number or a slot. -/
  start : Nat
  /-- The offset of each entry from the start of the index record, in order. -/
  offsets : List Int
  deriving Repr, DecidableEq

/-- The 8 little-endian bytes at the position `pos` of `data`, as a signed integer.

The integer is in two's complement, so a top bit of 1 makes it negative. -/
def readInt64 (data : ByteArray) (pos : Nat) : Int :=
  (BitVec.ofNat 64 (Ssz.readUint data.data pos 8)).toInt

/-- The index that the data of an index record holds.

The data is the first number, one offset per entry, then the count of entries.

Each is 8 bytes, little-endian, and each offset is signed.

The [SlotIndex][slotindex] document gives this layout.

So the data has 16 bytes plus 8 bytes for each entry it counts.

[slotindex]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/types/0x6932.md
-/
def readIndex (data : ByteArray) : Except E2storeError Index :=
  if data.size < 16 then
    .error .indexSize
  else
    let count := Ssz.readUint data.data (data.size - 8) 8
    if data.size ≠ 16 + 8 * count then
      .error .indexSize
    else
      .ok ⟨Ssz.readUint data.data 0 8, (List.range count).map fun i => readInt64 data (8 + 8 * i)⟩

end EthLib.Serialization.E2store

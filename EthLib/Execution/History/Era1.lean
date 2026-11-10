module

public import EthLib.Base.U256
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Network.Blocks
public import EthLib.Networking.Snappy.Frame
public import EthLib.Serialization.E2store
public import EthLib.Serialization.Rlp.Decode
public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# `Execution.History.Era1`

Era1 files: the execution blocks of up to 8192 numbers in a row, before the Merge.

The [era1 document][era1] defines them on top of e2store records.

A file is a Version record, four records per block, other records, an Accumulator and an index.

The four records of a block are its header, its body, its receipts and its total difficulty.

The first three are RLP, each compressed with the Snappy framing format.

The accumulator is the SSZ root of the list of each block's hash and total difficulty.

The block index gives the first block number and where the header of each block starts.

[era1]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/formats/era1.md
-/

@[expose] public section

namespace EthLib.Execution.History

open EthLib.Base
open EthLib.Serialization
open EthLib.Serialization.E2store (Record)

/-- The type of a CompressedHeader record. -/
def COMPRESSED_HEADER : UInt16 := 0x0300

/-- The type of a CompressedBody record. -/
def COMPRESSED_BODY : UInt16 := 0x0400

/-- The type of a CompressedReceipts record. -/
def COMPRESSED_RECEIPTS : UInt16 := 0x0500

/-- The type of a TotalDifficulty record. -/
def TOTAL_DIFFICULTY : UInt16 := 0x0600

/-- The type of an Accumulator record. -/
def ACCUMULATOR : UInt16 := 0x0700

/-- The type of a BlockIndex record, `f2` in ASCII. -/
def BLOCK_INDEX : UInt16 := 0x6632

/-- The record types of the era1 document, which no other record of a file may take. -/
def ERA1_TYPES : List UInt16 :=
  [E2store.VERSION, COMPRESSED_HEADER, COMPRESSED_BODY, COMPRESSED_RECEIPTS, TOTAL_DIFFICULTY,
    ACCUMULATOR, BLOCK_INDEX]

/-- The most blocks a file holds, the limit of the list under the accumulator. -/
def MAX_ERA1_BLOCKS : Nat := 8192

/-- What the accumulator holds for one block. -/
structure HeaderRecord where
  /-- The hash of the block, the Keccak-256 hash of the RLP of its header. -/
  blockHash : Hash32
  /-- The total difficulty of the chain up to and including the block. -/
  totalDifficulty : U256
  deriving DecidableEq, Repr

instance : Ssz.SszType HeaderRecord :=
  .container ["block_hash", "total_difficulty"]
    (fun r => (r.blockHash, r.totalDifficulty))
    (fun (blockHash, totalDifficulty) => ⟨blockHash, totalDifficulty⟩)

/-- One block of a file: its header, body and receipts as RLP, and its total difficulty. -/
structure Era1Block where
  /-- The RLP of the header. -/
  header : ByteArray
  /-- The RLP of the body. -/
  body : ByteArray
  /-- The RLP of the receipts. -/
  receipts : ByteArray
  /-- The total difficulty of the chain up to and including the block. -/
  totalDifficulty : U256

/-- What an era1 file holds. -/
structure Era1 where
  /-- The number of the first block. -/
  startingNumber : Nat
  /-- Where the header of each block starts, from the start of the BlockIndex record. -/
  offsets : List Int
  /-- The blocks, by number. -/
  blocks : List Era1Block
  /-- The records between the blocks and the accumulator, of types the document leaves open. -/
  others : List Record
  /-- The root of the list of each block's hash and total difficulty. -/
  accumulator : Bytes32

/-- Why bytes are not an era1 file. -/
inductive Era1Error where
  /-- The bytes are not an e2store file, or the block index does not read. -/
  | e2store (e : E2store.E2storeError)
  /-- The last two records are not an Accumulator and a BlockIndex. -/
  | noTrailer
  /-- A record between the blocks and the accumulator has a type of the era1 document.

  So a block is cut short, out of order, or after another record. -/
  | misplacedRecord (type : UInt16)
  /-- The file holds more than 8192 blocks. -/
  | tooManyBlocks (count : Nat)
  /-- A TotalDifficulty or Accumulator record does not hold 32 bytes. -/
  | wrongSize (type : UInt16) (size : Nat)
  /-- The block index counts another number of blocks than the file holds. -/
  | blockCount (counted held : Nat)
  /-- The block index points the block `i` elsewhere than at its header. -/
  | blockOffset (i : Nat)
  /-- A compressed record of the block `i` is not a valid Snappy framed stream. -/
  | frame (i : Nat) (e : Networking.Snappy.FrameError)
  /-- A record of the block `i` is not one RLP item, or its header lacks a field. -/
  | rlp (i : Nat) (e : Rlp.RlpError)
  /-- The header of the block `i` has another number than the index gives it. -/
  | blockNumber (i : Nat)
  /-- The header of the block `i` does not name the hash of the block before as its parent. -/
  | parentHash (i : Nat)
  /-- The total difficulty of the block `i` is not the one before plus its difficulty.

  For the genesis block, it is not its difficulty. -/
  | totalDifficulty (i : Nat)
  /-- The SSZ root of the header records fails. -/
  | ssz (e : Ssz.Err)
  /-- The accumulator is not the root of the header records of the blocks. -/
  | accumulator
  deriving Repr

/-- The stable code of an error, one per constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Era1Error.code : Era1Error → UInt32
  | .e2store _ => 1
  | .noTrailer => 2
  | .misplacedRecord _ => 3
  | .tooManyBlocks _ => 4
  | .wrongSize _ _ => 5
  | .blockCount _ _ => 6
  | .blockOffset _ => 7
  | .frame _ _ => 8
  | .rlp _ _ => 9
  | .blockNumber _ => 10
  | .parentHash _ => 11
  | .totalDifficulty _ => 12
  | .ssz _ => 13
  | .accumulator => 14

/-- The blocks at the front of the records, four records each, and the records after them.

A block is a header, a body, receipts and a total difficulty, in that order. -/
def takeBlocks : List Record → List (Record × Record × Record × Record) × List Record
  | h :: b :: r :: t :: rest =>
    if h.type = COMPRESSED_HEADER ∧ b.type = COMPRESSED_BODY ∧
        r.type = COMPRESSED_RECEIPTS ∧ t.type = TOTAL_DIFFICULTY then
      let (blocks, after) := takeBlocks rest
      ((h, b, r, t) :: blocks, after)
    else
      ([], h :: b :: r :: t :: rest)
  | rest => ([], rest)

/-- The records before the last two, and the last two, if there are two. -/
def splitLastTwo : List Record → Option (List Record × Record × Record)
  | [] | [_] => none
  | [a, b] => some ([], a, b)
  | r :: rest => (splitLastTwo rest).map fun (front, a, b) => (r :: front, a, b)

/-- The 32 bytes of a TotalDifficulty or Accumulator record. -/
def bytes32Of (record : Record) : Except Era1Error Bytes32 :=
  if h : record.data.size = 32 then .ok ⟨record.data.data, h⟩
  else .error (.wrongSize record.type record.data.size)

/-- The data of the compressed record of the block `i`. -/
def decompress (i : Nat) (record : Record) : Except Era1Error ByteArray :=
  (Networking.Snappy.decodeFrames record.data).mapError (.frame i)

/-- The one RLP item of the bytes of a record of the block `i`. -/
def rlpItem (i : Nat) (bytes : ByteArray) : Except Era1Error Rlp.Item :=
  (Rlp.decode bytes).mapError (.rlp i)

/-- The index of the difficulty in a header, the eighth field at every fork. -/
def HEADER_DIFFICULTY_INDEX : Nat := 7

/-- The difficulty of a header of the block `i`, its eighth field. -/
def headerDifficulty (i : Nat) (header : Rlp.Item) : Except Era1Error Nat :=
  Except.mapError (.rlp i) do
    let fields ← header.toItems
    match fields[HEADER_DIFFICULTY_INDEX]? with
    | some d => Rlp.Codec.ofItem d
    | none => throw (.wrongFieldCount (HEADER_DIFFICULTY_INDEX + 1) fields.length)

/-- The block `i` of a file whose first block has the number `start`, checked alone.

Each compressed record must decompress to one RLP item.

The header must carry the number of its place.

The result also gives the difficulty and the parent hash of the header. -/
def readBlock (start i : Nat) (records : Record × Record × Record × Record) :
    Except Era1Error (Era1Block × Nat × Hash32) := do
  let (h, b, r, t) := records
  let header ← decompress i h
  let body ← decompress i b
  let receipts ← decompress i r
  let item ← rlpItem i header
  discard <| rlpItem i body
  discard <| rlpItem i receipts
  let number ← (Execution.Network.headerNumber item).mapError (.rlp i)
  unless number = start + i do throw (.blockNumber i)
  let difficulty ← headerDifficulty i item
  let parent ← (Execution.Network.headerParent item).mapError (.rlp i)
  let td := BitVec.ofNat 256 (Base.bytesToUint (← bytes32Of t))
  return (⟨header, body, receipts, td⟩, difficulty, parent)

/-- The blocks of a file, from the block `i` on, after the block before them.

The block before is its hash and total difficulty, or none at the first block.

Each block must name the hash of the block before as its parent.

Its total difficulty must be the one before plus its difficulty.

A first block numbered 0 is the genesis block, whose total difficulty is its difficulty. -/
def readBlocks (start : Nat) :
    Nat → Option (Hash32 × Nat) → List (Record × Record × Record × Record) →
      Except Era1Error (List Era1Block)
  | _, _, [] => .ok []
  | i, before, records :: rest => do
    let (block, difficulty, parent) ← readBlock start i records
    let td := block.totalDifficulty.toNat
    match before with
    | some (hash, tdBefore) =>
      unless parent = hash do throw (.parentHash i)
      unless td = tdBefore + difficulty do throw (.totalDifficulty i)
    | none =>
      if start = 0 ∧ td ≠ difficulty then throw (.totalDifficulty i)
    let hash := Cryptography.Hash.Keccak.keccak256 block.header
    return block :: (← readBlocks start (i + 1) (some (hash, td)) rest)

/-- The root of the list of each block's hash and total difficulty.

The list holds at most 8192 records. -/
def accumulatorRoot (blocks : List Era1Block) : Except Era1Error Bytes32 := do
  let records := blocks.toArray.map fun block =>
    (⟨Cryptography.Hash.Keccak.keccak256 block.header, block.totalDifficulty⟩ : HeaderRecord)
  if bound : records.size ≤ MAX_ERA1_BLOCKS then
    let list : Ssz.SszList HeaderRecord MAX_ERA1_BLOCKS := ⟨records, bound⟩
    (Ssz.SszType.hashTreeRoot list).mapError .ssz
  else
    throw (.tooManyBlocks records.size)

/-- The era1 file that the bytes hold, or why they hold none.

The records must follow the order of the era1 document.

The block index must count the blocks and point at the header of each.

Each offset counts from the start of the BlockIndex record.

Its layout is that of a SlotIndex record, which the era1 document leaves unstated.

The blocks must form a chain from the first number of the index, with their total difficulties.

The total difficulty is a 256-bit little-endian integer, as SSZ writes it.

The accumulator must be the root of the hashes and total difficulties of the blocks. -/
def decodeEra1 (bytes : ByteArray) : Except Era1Error Era1 := do
  let records ← (E2store.decodeFile bytes).mapError .e2store
  let starts := (E2store.recordStarts 0 records).toArray
  -- The Version record comes first, as decoding the file checks.
  let (tuples, after) := takeBlocks (records.drop 1)
  let some (others, acc, idx) := splitLastTwo after | throw .noTrailer
  unless acc.type = ACCUMULATOR ∧ idx.type = BLOCK_INDEX do throw .noTrailer
  if let some other := others.find? (ERA1_TYPES.contains ·.type) then
    throw (.misplacedRecord other.type)
  unless tuples.length ≤ MAX_ERA1_BLOCKS do throw (.tooManyBlocks tuples.length)
  let index ← (E2store.readIndex idx.data).mapError .e2store
  unless index.offsets.length = tuples.length do
    throw (.blockCount index.offsets.length tuples.length)
  -- The BlockIndex record is the last one, and the header of the block `i` the record `1 + 4 i`.
  let indexStart := bytes.size - 8 - idx.data.size
  let misplaced := (List.range tuples.length).find? fun i =>
    (indexStart : Int) + index.offsets.getD i 0 ≠ starts.getD (1 + 4 * i) 0
  if let some i := misplaced then throw (.blockOffset i)
  let blocks ← readBlocks index.start 0 none tuples
  let accumulator ← bytes32Of acc
  unless (← accumulatorRoot blocks) = accumulator do throw .accumulator
  return ⟨index.start, index.offsets, blocks, others, accumulator⟩

end EthLib.Execution.History

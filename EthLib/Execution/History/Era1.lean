module

public import EthLib.Base.U256
public import EthLib.Execution.ErrorFormat
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

[era1]: https://github.com/eth-clients/e2store-format-specs/blob/923b1522f8970e9ebe939057d2a573aaf71b7f22/formats/era1.md
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

/-- The record types of the era1 document.

EthLib reads its grammar so that no other record of a file takes one of them.

So a second Version record, as in two files put together, is not an era1 file. -/
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
  /-- The header of the block `i` has the number `actual`, not `expected`, the one of the index. -/
  | blockNumber (i expected actual : Nat)
  /-- The header of the block `i` names the parent `actual`, not `expected`, the block before. -/
  | parentHash (i : Nat) (expected actual : Hash32)
  /-- The total difficulty `actual` of the block `i` is not `expected`.

  It is the one before plus the difficulty of the block, or for the genesis block its difficulty.
  -/
  | totalDifficulty (i expected actual : Nat)
  /-- The SSZ root of the header records fails. -/
  | ssz (e : Ssz.Err)
  /-- The accumulator `actual` of the file is not `expected`, the root of its header records. -/
  | accumulator (expected actual : Bytes32)

/-- A constructor of the error, named in full, applied to its arguments. -/
def era1ErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.History.Era1Error." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named and each hash in hex. -/
def Era1Error.reprPrec : Era1Error → Nat → Std.Format
  | .e2store e, p => era1ErrorFormat "e2store" [reprArg e] p
  | .noTrailer, p => era1ErrorFormat "noTrailer" [] p
  | .misplacedRecord type, p => era1ErrorFormat "misplacedRecord" [namedArg "type" type] p
  | .tooManyBlocks count, p => era1ErrorFormat "tooManyBlocks" [namedArg "count" count] p
  | .wrongSize type size, p =>
    era1ErrorFormat "wrongSize" [namedArg "type" type, namedArg "size" size] p
  | .blockCount counted held, p =>
    era1ErrorFormat "blockCount" [namedArg "counted" counted, namedArg "held" held] p
  | .blockOffset i, p => era1ErrorFormat "blockOffset" [namedArg "i" i] p
  | .frame i e, p => era1ErrorFormat "frame" [namedArg "i" i, reprArg e] p
  | .rlp i e, p => era1ErrorFormat "rlp" [namedArg "i" i, reprArg e] p
  | .blockNumber i expected actual, p =>
    era1ErrorFormat "blockNumber"
      [namedArg "i" i, namedArg "expected" expected, namedArg "actual" actual] p
  | .parentHash i expected actual, p =>
    era1ErrorFormat "parentHash"
      [namedArg "i" i, namedArg "expected" expected, namedArg "actual" actual] p
  | .totalDifficulty i expected actual, p =>
    era1ErrorFormat "totalDifficulty"
      [namedArg "i" i, namedArg "expected" expected, namedArg "actual" actual] p
  | .ssz e, p => era1ErrorFormat "ssz" [reprArg e] p
  | .accumulator expected actual, p =>
    era1ErrorFormat "accumulator" [namedArg "expected" expected, namedArg "actual" actual] p

instance : Repr Era1Error := ⟨Era1Error.reprPrec⟩

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
  | .blockNumber .. => 10
  | .parentHash .. => 11
  | .totalDifficulty .. => 12
  | .ssz _ => 13
  | .accumulator .. => 14

/-- The blocks at the front of the records, four records each, and the records after them.

A block is a header, a body, receipts and a total difficulty, in that order. -/
def takeBlocks : List Record → List (Record × Record × Record × Record) × List Record
  -- `block-tuple := CompressedHeader | CompressedBody | CompressedReceipts | TotalDifficulty`.
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
  exactBytes 32 record.data (.wrongSize record.type)

/-- The data of the compressed record of the block `i`. -/
def decompressRecord (i : Nat) (record : Record) : Except Era1Error ByteArray :=
  (Networking.Snappy.decodeFrames record.data).mapError (.frame i)

/-- The one RLP item of the bytes of a record of the block `i`. -/
def rlpItem (i : Nat) (bytes : ByteArray) : Except Era1Error Rlp.Item :=
  (Rlp.decode bytes).mapError (.rlp i)

/-- The block `i` of a file whose first block has the number `start`, checked alone.

Each compressed record must decompress to one RLP item.

The header must carry the number of its place.

The result also gives the difficulty and the parent hash of the header. -/
def readBlock (start i : Nat) (records : Record × Record × Record × Record) :
    Except Era1Error (Era1Block × Nat × Hash32) := do
  let (h, b, r, t) := records
  -- Each compressed record holds the RLP of its part, in the framing format of Snappy.
  let header ← decompressRecord i h
  let body ← decompressRecord i b
  let receipts ← decompressRecord i r
  -- Each part must be one RLP item; only the header is read further.
  let item ← rlpItem i header
  discard <| rlpItem i body
  discard <| rlpItem i receipts
  -- EthLib's check: block `i` of the file has the number `starting-number + i`.
  let number ← (Execution.Network.headerNumber item).mapError (.rlp i)
  unless number = start + i do throw (.blockNumber i (start + i) number)
  -- The difficulty and the parent hash of the header, for the chain checks.
  let difficulty ← (Execution.Network.headerDifficulty item).mapError (.rlp i)
  let parent ← (Execution.Network.headerParent item).mapError (.rlp i)
  -- The document gives the total difficulty as an unsigned 256-bit integer, with no byte order.
  --
  -- EthLib reads it little-endian, as SSZ and the accumulator do.
  let td := BitVec.ofNat 256 (Base.ByteOrder.ofLE (← bytes32Of t))
  return (⟨header, body, receipts, td⟩, difficulty, parent)

/-- The blocks of a file, from the block `i` on, after the block before them.

The block before is its hash and total difficulty, or none at the first block.

The blocks must form a chain. -/
def readBlocks (start : Nat) :
    Nat → Option (Hash32 × Nat) → List (Record × Record × Record × Record) →
      Except Era1Error (List Era1Block)
  | _, _, [] => .ok []
  | i, before, records :: rest => do
    let (block, difficulty, parent) ← readBlock start i records
    let td := block.totalDifficulty.toNat
    -- The era1 document asks none of the checks below, which EthLib adds for the chain.
    match before with
    -- EthLib's check after a block: the parent hash is the hash of the block before.
    --
    -- And the total difficulty is the one before plus the difficulty of this block.
    | some (hash, tdBefore) =>
      unless parent = hash do throw (.parentHash i hash parent)
      unless td = tdBefore + difficulty do throw (.totalDifficulty i (tdBefore + difficulty) td)
    -- EthLib's check at the genesis block: its total difficulty is its difficulty.
    --
    -- A first block numbered 0 is the genesis block.
    --
    -- A first block with another number has no block before it in the file, so it is not checked.
    | none =>
      if start = 0 ∧ td ≠ difficulty then throw (.totalDifficulty i difficulty td)
    -- The hash of the block, the Keccak-256 hash of the RLP of its header.
    let hash := Cryptography.Hash.Keccak.keccak256 block.header
    return block :: (← readBlocks start (i + 1) (some (hash, td)) rest)

/-- The root of the list of each block's hash and total difficulty.

The list holds at most 8192 records. -/
def accumulatorRoot (blocks : List Era1Block) : Except Era1Error Bytes32 := do
  -- `header-record := { block-hash: Bytes32, total-difficulty: Uint256 }`, for each block.
  let records := blocks.toArray.map fun block =>
    (⟨Cryptography.Hash.Keccak.keccak256 block.header, block.totalDifficulty⟩ : HeaderRecord)
  -- The hash tree root of the list of header records, at most 8192 long.
  if bound : records.size ≤ MAX_ERA1_BLOCKS then
    let list : Ssz.SszList HeaderRecord MAX_ERA1_BLOCKS := ⟨records, bound⟩
    (Ssz.SszType.hashTreeRoot list).mapError .ssz
  else
    throw (.tooManyBlocks records.size)

/-- The era1 file that the bytes hold, or why they hold none.

The records must follow the order of the era1 document, and the blocks must form a chain. -/
def decodeEra1 (bytes : ByteArray) : Except Era1Error Era1 := do
  let records ← (E2store.decodeFile bytes).mapError .e2store
  let starts := (E2store.recordStarts 0 records).toArray
  -- `era1 := Version | block-tuple* | other-entries* | Accumulator | BlockIndex`.
  --
  -- A file is a Version record, four records per block, other records, the Accumulator, the index.
  --
  -- The Version record comes first, as decoding the file checks.
  let (tuples, after) := takeBlocks (records.drop 1)
  -- The last two records are the Accumulator and the BlockIndex.
  let some (others, acc, idx) := splitLastTwo after | throw .noTrailer
  unless acc.type = ACCUMULATOR ∧ idx.type = BLOCK_INDEX do throw .noTrailer
  -- EthLib's reading: no other entry takes a type of the era1 document.
  if let some other := others.find? (ERA1_TYPES.contains ·.type) then
    throw (.misplacedRecord other.type)
  -- At most 8192 blocks, the limit of the accumulator.
  unless tuples.length ≤ MAX_ERA1_BLOCKS do throw (.tooManyBlocks tuples.length)
  -- `block-index := starting-number | index | index | index ... | count`.
  --
  -- The block index gives the first block number and where the header of each block starts.
  --
  -- The era1 document gives the order of its fields, but not their width or sign.
  --
  -- EthLib takes the layout of a SlotIndex record: 8 bytes each, little-endian, offsets signed.
  let index ← (E2store.readIndex idx.data).mapError .e2store
  -- The count is the number of blocks.
  unless index.offsets.length = tuples.length do
    throw (.blockCount index.offsets.length tuples.length)
  -- The era1 document gives where the offsets count from only loosely.
  --
  -- EthLib's reading: each index counts from the start of the BlockIndex record, the last record.
  --
  -- Index `i` must point at the CompressedHeader record of block `i`, the record `1 + 4 i`.
  let indexStart := bytes.size - 8 - idx.data.size
  let offsets := index.offsets.toArray
  let misplaced := (List.range tuples.length).find? fun i =>
    (indexStart : Int) + offsets.getD i 0 ≠ starts.getD (1 + 4 * i) 0
  if let some i := misplaced then throw (.blockOffset i)
  -- The blocks, numbered from `starting-number`, each checked against the one before by EthLib.
  --
  -- They must form a chain from the first number of the index, with their total difficulties.
  let blocks ← readBlocks index.start 0 none tuples
  -- The Accumulator record is the root of the header records of the blocks.
  --
  -- That is the SSZ root of the list of each block's hash and total difficulty.
  let accumulator ← bytes32Of acc
  let root ← accumulatorRoot blocks
  unless root = accumulator do throw (.accumulator root accumulator)
  return ⟨index.start, index.offsets, blocks, others, accumulator⟩

end EthLib.Execution.History

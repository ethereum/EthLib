module

public import EthLib.Base.Hex
public import EthLib.Consensus.Accessors
public import EthLib.Consensus.ForkSchedule
public import EthLib.Networking.Snappy.Frame
public import EthLib.Serialization.E2store

/-!
# `Consensus.History.Era`

Era files: the beacon blocks and states of the chain, one group of records per era.

The [era document][era] defines them on top of e2store records.

An era spans as many slots as a state holds block roots for, and is numbered by when it ends.

Era 0 ends at genesis.

The era `e` ends at the slot `e` times that span, and holds the blocks of the span before it.

A group starts with a Version record, the blocks of the era, and the state where the era ends.

Other records follow, then one or two SlotIndex records.

The first index points at the block of each slot, and is absent for era 0.

The second index points at the state, and its first slot is the slot of the state.

A file is one or more groups, one after the other.

Each block and the state are SSZ, compressed with the Snappy framing format.

Their fork is the fork of their slot.

The documents of the [block][block] and [state][state] types say so.

[era]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/formats/era.md
[block]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/types/0x0100.md
[state]: https://github.com/eth-clients/e2store-format-specs/blob/31cf6b577123bf1703eb3713f0b242f65fea806a/types/0x0200.md
-/

@[expose] public section

namespace EthLib.Consensus.History

open EthLib.Base
open EthLib.Serialization
open EthLib.Serialization.E2store (Record Index)

/-- The type of a CompressedSignedBeaconBlock record. -/
def COMPRESSED_SIGNED_BEACON_BLOCK : UInt16 := 0x0100

/-- The type of a CompressedBeaconState record. -/
def COMPRESSED_BEACON_STATE : UInt16 := 0x0200

/-- The type of a SlotIndex record, `i2` in ASCII. -/
def SLOT_INDEX : UInt16 := 0x6932

/-- The record types of the era document.

EthLib reads its grammar so that no other record of a group takes one of them. -/
def ERA_TYPES : List UInt16 :=
  [E2store.VERSION, COMPRESSED_SIGNED_BEACON_BLOCK, COMPRESSED_BEACON_STATE, SLOT_INDEX]

/-- A record of a file, after the position in the file at which its header starts. -/
abbrev Located := Nat × Record

/-- One block of a group, at the fork of its slot. -/
structure EraBlock (preset : Preset) where
  /-- The slot of the block. -/
  slot : Slot
  /-- The fork of the slot. -/
  fork : Fork
  /-- The block, with the signature of its proposer. -/
  block : SignedBeaconBlock preset fork
  /-- The root of the block, which the state holds for its slot. -/
  root : Root

/-- What one group of an era file holds. -/
structure EraGroup (preset : Preset) where
  /-- The era of the group: the slot of its state, over the length of the buffer of block roots. -/
  era : Nat
  /-- The blocks of the era, by slot. -/
  blocks : List (EraBlock preset)
  /-- The fork of the slot of the state. -/
  fork : Fork
  /-- The state at the slot where the era ends. -/
  state : BeaconState preset fork
  /-- The records between the state and the indices, of types the document leaves open. -/
  others : List Record
  /-- The position of the index of the blocks in the file, and the index, except in era 0. -/
  blockIndex : Option (Nat × Index)
  /-- The position of the index of the state in the file, and the index. -/
  stateIndex : Nat × Index

/-- Why bytes are not an era file. -/
inductive EraError where
  /-- The bytes are not an e2store file, or an index does not read. -/
  | e2store (e : E2store.E2storeError)
  /-- A group has no CompressedBeaconState record after its blocks. -/
  | noState
  /-- The last record of a group is not a SlotIndex record. -/
  | noStateIndex
  /-- A record between the state and the indices has a type of the era document. -/
  | misplacedRecord (type : UInt16)
  /-- The index of the state does not have one entry, or it does not point at the state. -/
  | stateIndex
  /-- The record of the slot is not a valid Snappy framed stream. -/
  | frame (slot : Nat) (e : Networking.Snappy.FrameError)
  /-- The record of the slot does not decode, or a root fails. -/
  | ssz (slot : Nat) (e : Ssz.Err)
  /-- The state is not at the slot of its index, or not at a slot where an era ends. -/
  | stateSlot (slot : Nat)
  /-- The current version of the state is not that of its fork in the configuration. -/
  | forkVersion (slot : Nat)
  /-- The group of era 0 holds a block or an index of blocks. -/
  | genesisBlocks
  /-- A group after era 0 has no index of blocks. -/
  | noBlockIndex
  /-- The index of the blocks does not cover the slots of the era. -/
  | blockIndexRange
  /-- The index points the slot elsewhere than at the next block record. -/
  | blockOffset (slot : Nat)
  /-- The block record at the position is not pointed at by the index. -/
  | unindexedBlock (position : Nat)
  /-- The block that the index points at for the slot has another slot. -/
  | blockSlot (slot : Nat)
  /-- The root of the block of the slot is not the one the state holds for it. -/
  | blockRoot (slot : Nat)
  /-- The slot has no block, but the state holds another root for it than for the slot before. -/
  | emptySlot (slot : Nat)
  /-- The state holds no block root for a slot of the era. -/
  | accessor (e : AccessorError)
  /-- The state of the era holds no root to name the file by.

  Only the name of a file raises it, never the decoder. -/
  | eraRoot (era : Nat)
  deriving Repr

/-- The stable code of an error, one per constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def EraError.code : EraError → UInt32
  | .e2store _ => 1
  | .noState => 2
  | .noStateIndex => 3
  | .misplacedRecord _ => 4
  | .stateIndex => 5
  | .frame _ _ => 6
  | .ssz _ _ => 7
  | .stateSlot _ => 8
  | .forkVersion _ => 9
  | .genesisBlocks => 10
  | .noBlockIndex => 11
  | .blockIndexRange => 12
  | .blockOffset _ => 13
  | .unindexedBlock _ => 14
  | .blockSlot _ => 15
  | .blockRoot _ => 16
  | .emptySlot _ => 17
  | .accessor _ => 18
  | .eraRoot _ => 19

/-- The groups of the records of a file, each without its Version record.

A group starts at a Version record, and runs until the next one. -/
def groupsOf : List Located → List (List Located)
  | [] => []
  | _ :: rest =>
    rest.takeWhile (·.2.type != E2store.VERSION) ::
      groupsOf (rest.dropWhile (·.2.type != E2store.VERSION))
termination_by records => records.length
decreasing_by exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le

/-- The records before the indices of a group, then the index of the blocks, then that of the state.

A group without an index of blocks has none.

The last record must be a SlotIndex record, the index of the state.

A SlotIndex record just before it is the index of the blocks. -/
def splitIndices (records : List Located) :
    Option (List Located × Option Located × Located) :=
  match records.reverse with
  | last :: before :: rest =>
    if last.2.type ≠ SLOT_INDEX then none
    else if before.2.type = SLOT_INDEX then some (rest.reverse, some before, last)
    else some ((before :: rest).reverse, none, last)
  | [last] => if last.2.type ≠ SLOT_INDEX then none else some ([], none, last)
  | [] => none

/-- The slots that an index at the position `indexAt` gives a block, with where each points.

An offset of 0 marks a slot without a block. -/
def indexedSlots (indexAt : Nat) (index : Index) : List (Nat × Int) :=
  index.offsets.zipIdx.filterMap fun (offset, i) =>
    if offset = 0 then none else some (index.start + i, (indexAt : Int) + offset)

/-- The block records with their slots, if the index points each slot at the next block record.

Each slot that has a block must point at the next record, in order, and no record is left. -/
def matchBlocks : List (Nat × Int) → List Located → Except EraError (List (Nat × Record))
  | [], [] => .ok []
  | (slot, pos) :: slots, (start, record) :: records =>
    if pos = (start : Int) then
      (matchBlocks slots records).map ((slot, record) :: ·)
    else
      .error (.blockOffset slot)
  | (slot, _) :: _, [] => .error (.blockOffset slot)
  | [], (start, _) :: _ => .error (.unindexedBlock start)

/-- The fork of a slot in a configuration. -/
def forkAtSlot (preset : Preset) (config : Config) (slot : Nat) : Fork :=
  config.forkAtEpoch (computeEpochAtSlot preset (UInt64.ofNat slot))

/-- The block of a record that the index gives the slot, checked against the state.

The block must decompress, then decode at the fork of its slot.

It must have that slot, and its root must be the one the state holds for the slot. -/
def readBlock {fork : Fork} (preset : Preset) (config : Config) (state : BeaconState preset fork)
    (slot : Nat) (record : Record) : Except EraError (EraBlock preset) := do
  let blockFork := forkAtSlot preset config slot
  let bytes ← (Networking.Snappy.decodeFrames record.data).mapError (.frame slot)
  let block ← (Ssz.SszType.deserialize (SignedBeaconBlock preset blockFork) bytes).mapError
    (.ssz slot)
  unless block.message.slot.toNat = slot do throw (.blockSlot slot)
  let root ← (Ssz.SszType.hashTreeRoot block.message).mapError (.ssz slot)
  let expected ← (getBlockRootAtSlot state block.message.slot).mapError .accessor
  unless root = expected do throw (.blockRoot slot)
  return ⟨block.message.slot, blockFork, block, root⟩

/-- Check each slot without a block against the state, except the first slot of the era.

The state must hold the same root for the slot as for the slot before.

The era document says to check the first slot against the era before, which a group lacks. -/
def checkEmptySlots {fork : Fork} {preset : Preset} (state : BeaconState preset fork)
    (index : Index) : Except EraError Unit :=
  index.offsets.zipIdx.forM fun (offset, i) => do
    if offset = 0 ∧ i ≠ 0 then
      let slot := index.start + i
      let before ← (getBlockRootAtSlot state (UInt64.ofNat (slot - 1))).mapError .accessor
      let root ← (getBlockRootAtSlot state (UInt64.ofNat slot)).mapError .accessor
      unless before = root do throw (.emptySlot slot)

/-- The group that the records hold, after its Version record, or why they hold none.

The records must follow the order of the era document.

The index of the state must have one entry, which points at the state.

Its first slot is the slot of the state, which must be a slot where an era ends.

The state must be consistent with the configuration: its current version is that of its fork.

EthLib reads that requirement of the era document so, and checks no other field.

The group of era 0 has no block and no index of blocks.

Any later group has an index of blocks, with one entry for each slot of the era.

It points each slot with a block at its record, in order, and each other slot at 0.

Each offset counts from the start of the index record.

Each block must have the root that the state holds for its slot.

Each slot without a block, but the first, must have the root of the slot before in the state.

The signatures of the blocks are not checked, since they need the keys of the validators. -/
def readGroup (preset : Preset) (config : Config) (group : List Located) :
    Except EraError (EraGroup preset) := do
  let isBlock (record : Located) := record.2.type == COMPRESSED_SIGNED_BEACON_BLOCK
  let blockRecords := group.takeWhile isBlock
  let stateAt :: tail := group.dropWhile isBlock | throw .noState
  unless stateAt.2.type = COMPRESSED_BEACON_STATE do throw .noState
  let some (others, blockIndexAt, stateIndexAt) := splitIndices tail | throw .noStateIndex
  if let some other := others.find? (ERA_TYPES.contains ·.2.type) then
    throw (.misplacedRecord other.2.type)
  let stateIndex ← (E2store.readIndex stateIndexAt.2.data).mapError .e2store
  unless stateIndex.offsets.map ((stateIndexAt.1 : Int) + ·) = [(stateAt.1 : Int)] do
    throw .stateIndex
  let slot := stateIndex.start
  let fork := forkAtSlot preset config slot
  let bytes ← (Networking.Snappy.decodeFrames stateAt.2.data).mapError (.frame slot)
  let state ← (Ssz.SszType.deserialize (BeaconState preset fork) bytes).mapError (.ssz slot)
  let slotsPerEra := preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  unless state.slot.toNat = slot ∧ slot % slotsPerEra = 0 do throw (.stateSlot slot)
  unless state.forkVersions.currentVersion = config.forkVersion fork do throw (.forkVersion slot)
  let era := slot / slotsPerEra
  let others := others.map (·.2)
  let stateIndex := (stateIndexAt.1, stateIndex)
  if era = 0 then
    unless blockRecords.isEmpty ∧ blockIndexAt.isNone do throw .genesisBlocks
    return ⟨0, [], fork, state, others, none, stateIndex⟩
  let some blockIndexAt := blockIndexAt | throw .noBlockIndex
  let blockIndex ← (E2store.readIndex blockIndexAt.2.data).mapError .e2store
  unless blockIndex.start + slotsPerEra = slot ∧ blockIndex.offsets.length = slotsPerEra do
    throw .blockIndexRange
  let slots ← matchBlocks (indexedSlots blockIndexAt.1 blockIndex) blockRecords
  let blocks ← slots.mapM fun (slot, record) => readBlock preset config state slot record
  checkEmptySlots state blockIndex
  return ⟨era, blocks, fork, state, others, some (blockIndexAt.1, blockIndex), stateIndex⟩

/-- The groups of an era file, or why the bytes are not one.

Each group must be valid on its own, since groups can be split and combined freely.

The era document leaves the order of the groups open, so EthLib asks none. -/
def decodeEra (preset : Preset) (config : Config) (bytes : ByteArray) :
    Except EraError (List (EraGroup preset)) := do
  let records ← (E2store.decodeFile bytes).mapError .e2store
  (groupsOf ((E2store.recordStarts 0 records).zip records)).mapM (readGroup preset config)

/-! ### The name of a file -/

/-- The root that names a file whose last era is `era`, from the state at the end of that era.

For era 0 it is the root of the validators at genesis.

For a later era it is the root of the historical batch of the slots of the era.

Before Capella, that root is in the historical roots.

From Capella, historical summaries follow them, each with the root of its batch.

The era document picks between the two by the fork of the state.

EthLib picks by the number of historical roots, which agrees wherever the document's index exists.

So a state of Capella whose historical roots run up to the era is named by the last of them. -/
def eraRoot {preset : Preset} {fork : Fork} (state : BeaconState preset fork) (era : Nat) :
    Except EraError Root := do
  if era = 0 then return state.genesisValidatorsRoot
  let roots := state.historicalRoots.data
  if h : era - 1 < roots.size then return roots[era - 1]
  if capella : .shapella ≤ fork then
    let summaries := (state.historicalSummaries capella).data
    if h : era - 1 - roots.size < summaries.size then
      return ← (Ssz.SszType.hashTreeRoot summaries[era - 1 - roots.size]).mapError
        (.ssz state.slot.toNat)
  throw (.eraRoot era)

/-- The decimal digits of a number, after zeros up to five digits. -/
def eraDigits (era : Nat) : String :=
  String.ofList ((Nat.toDigits 10 era).leftpad 5 '0')

/-- The name of a file of groups: the configuration, the first era, and a short root.

The first era is the lowest era of the groups, on at least five digits.

The short root is the first 4 bytes, in lowercase hex, of the root of the highest era.

Of two groups with the highest era, the later one names the file. -/
def eraFileName {preset : Preset} (config : Config) (first : EraGroup preset)
    (rest : List (EraGroup preset)) : Except EraError String := do
  let lowest := rest.foldl (fun era group => min era group.era) first.era
  let highest := rest.foldl (fun top group => if top.era ≤ group.era then group else top) first
  let root ← eraRoot highest.state highest.era
  let short := String.ofList ((root.toList.take 4).flatMap byteHexDigits)
  return s!"{config.CONFIG_NAME}-{eraDigits lowest}-{short}.era"

end EthLib.Consensus.History

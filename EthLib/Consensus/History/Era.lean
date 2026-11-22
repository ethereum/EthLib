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

The section Structure of the era document gives the grammar of a file, with one group per era.

In it, `|` separates records that follow one another, not alternatives.

`era := group+`

`group := Version | block* | era-state | other-entries* | slot-index(block)? | slot-index(state)`

`block := CompressedSignedBeaconBlock`

`era-state := CompressedBeaconState`

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
  /-- A group has no CompressedBeaconState record after its blocks.

  The error gives the type of the record after the blocks, or none when the group ends there. -/
  | noState (found : Option UInt16)
  /-- The last record of a group is not a SlotIndex record.

  The error gives the type of the last record, or none when the state is the last record. -/
  | noStateIndex (found : Option UInt16)
  /-- A record between the state and the indices has a type of the era document. -/
  | misplacedRecord (type : UInt16)
  /-- The index of the state does not have one entry, or it does not point at the state.

  The error gives the number of entries and the position that the first one points at, if any.

  It then gives the position of the state record. -/
  | stateIndex (entries : Nat) (pointed : Option Int) (statePosition : Nat)
  /-- The record of the slot is not a valid Snappy framed stream. -/
  | frame (slot : Nat) (e : Networking.Snappy.FrameError)
  /-- The record of the slot does not decode, or a root fails. -/
  | ssz (slot : Nat) (e : Ssz.Err)
  /-- The state is not at the slot of its index, or not at a slot where an era ends. -/
  | stateSlot (slot : Nat)
  /-- The current version of the state is not that of its fork in the configuration. -/
  | forkVersion (slot : Nat)
  /-- The group of era 0 holds a block or an index of blocks.

  The error gives the number of block records and whether an index of blocks is present. -/
  | genesisBlocks (blocks : Nat) (hasBlockIndex : Bool)
  /-- A group after era 0, whose era the error gives, has no index of blocks. -/
  | noBlockIndex (era : Nat)
  /-- The index of the blocks does not cover the slots of the era.

  The error gives the first slot and the number of entries of the index.

  It then gives the first slot and the number of slots of the era. -/
  | blockIndexRange (start entries expectedStart expectedEntries : Nat)
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
  | .noState _ => 2
  | .noStateIndex _ => 3
  | .misplacedRecord _ => 4
  | .stateIndex .. => 5
  | .frame _ _ => 6
  | .ssz _ _ => 7
  | .stateSlot _ => 8
  | .forkVersion _ => 9
  | .genesisBlocks .. => 10
  | .noBlockIndex _ => 11
  | .blockIndexRange .. => 12
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
  -- `era := group+`, and `group := Version | ...`: each Version record starts a group.
  | _ :: rest =>
    rest.takeWhile (·.2.type != E2store.VERSION) ::
      groupsOf (rest.dropWhile (·.2.type != E2store.VERSION))
termination_by records => records.length
decreasing_by exact Nat.lt_succ_of_le (List.dropWhile_suffix _).length_le

/-- The records before the indices of a group, then the index of the blocks, then that of the state.

A group without an index of blocks has none. -/
def splitIndices (records : List Located) :
    Option (List Located × Option Located × Located) :=
  -- `... | other-entries* | slot-index(block)? | slot-index(state)`, read from the back.
  match records.reverse with
  -- The last record is `slot-index(state)`; a SlotIndex record before it is `slot-index(block)`.
  | last :: before :: rest =>
    if last.2.type ≠ SLOT_INDEX then none
    else if before.2.type = SLOT_INDEX then some (rest.reverse, some before, last)
    else some ((before :: rest).reverse, none, last)
  -- A lone `slot-index(state)`.
  | [last] => if last.2.type ≠ SLOT_INDEX then none else some ([], none, last)
  | [] => none

/-- The slots that an index at the position `indexAt` gives a block, with where each points. -/
def indexedSlots (indexAt : Nat) (index : Index) : List (Nat × Int) :=
  -- SlotIndex: entry `i` is for the slot `starting-slot + i`.
  --
  -- An offset of 0 indicates that no data is present for the slot.
  --
  -- Another offset counts bytes from the beginning of the index record.
  index.offsets.zipIdx.filterMap fun (offset, i) =>
    if offset = 0 then none else some (index.start + i, (indexAt : Int) + offset)

/-- The block records with their slots, if the index points each slot at the next block record. -/
def matchBlocks : List (Nat × Int) → List Located → Except EraError (List (Nat × Record))
  -- Every slot with a block and every block record are matched.
  | [], [] => .ok []
  -- The blocks are in slot order and empty slots are skipped.
  --
  -- So the slot points at the start of the next block record.
  | (slot, pos) :: slots, (start, record) :: records =>
    if pos = (start : Int) then
      (matchBlocks slots records).map ((slot, record) :: ·)
    else
      .error (.blockOffset slot)
  -- A slot with a block, but no block record left.
  | (slot, _) :: _, [] => .error (.blockOffset slot)
  -- A block record that no slot points at.
  | [], (start, _) :: _ => .error (.unindexedBlock start)

/-- The fork of a slot in a configuration. -/
def forkAtSlot (preset : Preset) (config : Config) (slot : Nat) : Fork :=
  -- The fork that the configuration schedules at the epoch of the slot.
  config.forkAtEpoch (computeEpochAtSlot preset (UInt64.ofNat slot))

/-- The block of a record that the index gives the slot, checked against the state. -/
def readBlock {fork : Fork} (preset : Preset) (config : Config) (state : BeaconState preset fork)
    (slot : Nat) (record : Record) : Except EraError (EraBlock preset) := do
  -- CompressedSignedBeaconBlock: the fork, and so the format of the block, is that of its slot.
  let blockFork := forkAtSlot preset config slot
  -- CompressedSignedBeaconBlock: `data: snappyFramed(ssz(SignedBeaconBlock))`.
  let bytes ← (Networking.Snappy.decodeFrames record.data).mapError (.frame slot)
  let block ← (Ssz.SszType.deserialize (SignedBeaconBlock preset blockFork) bytes).mapError
    (.ssz slot)
  -- EthLib's check: the block is at the slot that the index gives it.
  unless block.message.slot.toNat = slot do throw (.blockSlot slot)
  -- The root of each block matches the block root that the state holds for its slot.
  let root ← (Ssz.SszType.hashTreeRoot block.message).mapError (.ssz slot)
  let expected ← (getBlockRootAtSlot state block.message.slot).mapError .accessor
  unless root = expected do throw (.blockRoot slot)
  return ⟨block.message.slot, blockFork, block, root⟩

/-- Check each slot without a block against the state, except the first slot of the era. -/
def checkEmptySlots {fork : Fork} {preset : Preset} (state : BeaconState preset fork)
    (index : Index) : Except EraError Unit :=
  index.offsets.zipIdx.forM fun (offset, i) => do
    -- An empty slot has the offset 0 in the index of the blocks.
    --
    -- The document asks to verify the first slot of the era against the era before, if possible.
    --
    -- A group holds no era before, so EthLib skips that slot.
    if offset = 0 ∧ i ≠ 0 then
      let slot := index.start + i
      -- The state holds the same block root for the empty slot as for the slot before it.
      let before ← (getBlockRootAtSlot state (UInt64.ofNat (slot - 1))).mapError .accessor
      let root ← (getBlockRootAtSlot state (UInt64.ofNat slot)).mapError .accessor
      unless before = root do throw (.emptySlot slot)

/-- The group that the records hold, after its Version record, or why they hold none.

The signatures of the blocks are not checked, since they need the keys of the validators. -/
def readGroup (preset : Preset) (config : Config) (group : List Located) :
    Except EraError (EraGroup preset) := do
  -- The grammar of a group, in order: after the Version record, `block*`.
  let isBlock (record : Located) := record.2.type == COMPRESSED_SIGNED_BEACON_BLOCK
  let blockRecords := group.takeWhile isBlock
  -- Then `era-state`.
  let stateAt :: tail := group.dropWhile isBlock | throw (.noState none)
  unless stateAt.2.type = COMPRESSED_BEACON_STATE do throw (.noState (some stateAt.2.type))
  -- Then `other-entries* | slot-index(block)? | slot-index(state)`, which ends the group.
  let some (others, blockIndexAt, stateIndexAt) := splitIndices tail
    | throw (.noStateIndex (tail.getLast?.map (·.2.type)))
  -- EthLib's reading: no other entry takes a type of the era document.
  if let some other := others.find? (ERA_TYPES.contains ·.2.type) then
    throw (.misplacedRecord other.2.type)
  -- `slot-index(state)` has `count = 1`, and points out the offset where the state entry begins.
  --
  -- Each offset counts from the beginning of the index record.
  let stateIndex ← (E2store.readIndex stateIndexAt.2.data).mapError .e2store
  unless stateIndex.offsets.map ((stateIndexAt.1 : Int) + ·) = [(stateAt.1 : Int)] do
    throw (.stateIndex stateIndex.offsets.length
      (stateIndex.offsets.head?.map ((stateIndexAt.1 : Int) + ·)) stateAt.1)
  -- The start slot field of the state slot index identifies the era of the group.
  let slot := stateIndex.start
  -- CompressedBeaconState: the fork, and so the format of the state, is that of its slot.
  let fork := forkAtSlot preset config slot
  -- CompressedBeaconState: `data: snappyFramed(ssz(BeaconState))`.
  let bytes ← (Networking.Snappy.decodeFrames stateAt.2.data).mapError (.frame slot)
  let state ← (Ssz.SszType.deserialize (BeaconState preset fork) bytes).mapError (.ssz slot)
  -- The state is in the era transition slot, a multiple of the slots per historical root.
  --
  -- EthLib's check: the state is at the slot of its index.
  let slotsPerEra := preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  unless state.slot.toNat = slot ∧ slot % slotsPerEra = 0 do throw (.stateSlot slot)
  -- The state is consistent with the given runtime configuration.
  --
  -- EthLib's reading: its current version is that of its fork, and no other field is checked.
  unless state.forkVersions.currentVersion = config.forkVersion fork do throw (.forkVersion slot)
  -- The era is identified by when it ends.
  let era := slot / slotsPerEra
  let others := others.map (·.2)
  let stateIndex := (stateIndexAt.1, stateIndex)
  -- The genesis group contains only the genesis state, and `slot-index(block)` is omitted.
  if era = 0 then
    unless blockRecords.isEmpty ∧ blockIndexAt.isNone do
      throw (.genesisBlocks blockRecords.length blockIndexAt.isSome)
    return ⟨0, [], fork, state, others, none, stateIndex⟩
  -- Any later group has `slot-index(block)`, with one entry per slot of the era.
  --
  -- EthLib's reading: its first slot is the first slot of the era, one era before the state.
  let some blockIndexAt := blockIndexAt | throw (.noBlockIndex era)
  let blockIndex ← (E2store.readIndex blockIndexAt.2.data).mapError .e2store
  unless blockIndex.start + slotsPerEra = slot ∧ blockIndex.offsets.length = slotsPerEra do
    throw (.blockIndexRange blockIndex.start blockIndex.offsets.length (slot - slotsPerEra)
      slotsPerEra)
  -- Offsets within indices point to entries of the correct kind, here each block record in turn.
  let slots ← matchBlocks (indexedSlots blockIndexAt.1 blockIndex) blockRecords
  -- Each block decompresses, deserializes, and has the root that the state holds for its slot.
  let blocks ← slots.mapM fun (slot, record) => readBlock preset config state slot record
  -- Each empty slot but the first has the block root of the slot before it in the state.
  checkEmptySlots state blockIndex
  return ⟨era, blocks, fork, state, others, some (blockIndexAt.1, blockIndex), stateIndex⟩

/-- The groups of an era file, or why the bytes are not one.

The era document leaves the order of the groups open, so EthLib asks none. -/
def decodeEra (preset : Preset) (config : Config) (bytes : ByteArray) :
    Except EraError (List (EraGroup preset)) := do
  -- An era file is an e2store file, so it starts with a Version record.
  let records ← (E2store.decodeFile bytes).mapError .e2store
  -- Each group is a full, independent era file, since groups can freely be split and combined.
  --
  -- So each group is read and checked on its own.
  (groupsOf ((E2store.recordStarts 0 records).zip records)).mapM (readGroup preset config)

/-! ### The name of a file -/

/-- The root that names a file whose last era is `era`, from the state at the end of that era.

For a later era than 0, it is the root of the historical batch of the slots of the era. -/
def eraRoot {preset : Preset} {fork : Fork} (state : BeaconState preset fork) (era : Nat) :
    Except EraError Root := do
  -- For the genesis era, the genesis validators root of the genesis state.
  if era = 0 then return state.genesisValidatorsRoot
  -- The document, before Capella: the last historical root of the state, at index `era - 1`.
  --
  -- The document picks by the fork of the state; EthLib picks by the number of historical roots.
  --
  -- The two agree wherever the index of the document exists.
  --
  -- So a state of Capella whose historical roots run up to the era is named by the last of them.
  let roots := state.historicalRoots.data
  if h : era - 1 < roots.size then return roots[era - 1]
  -- The document, from Capella: the last historical summary, at `era - 1` minus the root count.
  --
  -- EthLib takes its hash tree root, which is the root of the historical batch of the era.
  if capella : .shapella ≤ fork then
    let summaries := (state.historicalSummaries capella).data
    if h : era - 1 - roots.size < summaries.size then
      return ← (Ssz.SszType.hashTreeRoot summaries[era - 1 - roots.size]).mapError
        (.ssz state.slot.toNat)
  -- The state holds no root for the era.
  throw (.eraRoot era)

/-- The decimal digits of a number, after zeros up to five digits. -/
def eraDigits (era : Nat) : String :=
  -- `era-number`: a 5-digit 0-filled decimal integer.
  --
  -- EthLib's choice, where the document is silent: an era above 99999 keeps all its digits.
  String.ofList ((Nat.toDigits 10 era).leftpad 5 '0')

/-- The name of a file of groups: the configuration, the first era, and a short root. -/
def eraFileName {preset : Preset} (config : Config) (first : EraGroup preset)
    (rest : List (EraGroup preset)) : Except EraError String := do
  -- Era files with multiple eras use the era number of the lowest era stored in the file.
  let lowest := rest.foldl (fun era group => min era group.era) first.era
  -- And the root of the highest era; of two groups of that era, EthLib takes the later one.
  let highest := rest.foldl (fun top group => if top.era ≤ group.era then group else top) first
  let root ← eraRoot highest.state highest.era
  -- `short-era-root`: the first 4 bytes of the root, lower-case hex-encoded (8 characters).
  let short := String.ofList ((root.toList.take 4).flatMap byteHexDigits)
  -- `<config-name>-<era-number>-<short-era-root>.era`, with the name of the configuration.
  return s!"{config.CONFIG_NAME}-{eraDigits lowest}-{short}.era"

end EthLib.Consensus.History

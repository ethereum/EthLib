module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.ReqResp.Messages

/-!
# `Consensus.ReqResp.Validity`

When the response of a request and response protocol is valid for its request.

Each check reads only the request and the items of the response.

So the rules that need the chain of the responder stay out, such as sending the first block it has.

## Blocks by range

The request names the slots from its start slot, for its count of slots.

- The response has at most as many blocks as the count, and at most the request limit of the fork.
- Each block lies in the requested slots.
- Each block has a higher slot than the one before it.
- When the step is 1, each block names the one before it as its parent.

The step must be 1; for any other step, the range of slots stays the same.

## Blocks by root

The request names blocks by the roots of their messages.

- The response has at most as many blocks as the request has roots.
- The root of each block is one of the requested roots.

## Sidecars by range

From Deneb, a request names the blob sidecars of a range of slots.

From Fulu, a request names the column sidecars of a range of slots, for some columns.

Each check assumes a fork at which its protocol exists.

- The response has at most the count times the most sidecars of one block.
- It has at most the request limit, which is the most sidecars of the most blocks.
- Each sidecar lies in the requested slots.
- The sidecars are in increasing order of slot, then of index.
- The sidecars of one slot name the same block.
- For blobs, the indices of the sidecars of one block are 0, 1, 2 and so on.
- For blobs, each index is below the most blobs of one block.
- For columns, each block has each requested column once, and no other.
- For columns, each index is below the number of columns.

A response holds every sidecar of each block it serves, but a blob check cannot see how many.

So the last block of a blob response may lack its last blobs.

## Sidecars by root

The request names sidecars by the root of their block and their index.

- The response has at most as many sidecars as the request names.
- Each sidecar is one that the request names.

The text does not forbid a sidecar twice in one response, so these checks allow it.

[EIP-4844] adds the blob protocols, and [EIP-7594] the column protocols.

[EIP-4844]: https://eips.ethereum.org/EIPS/eip-4844#networking
[EIP-7594]: https://eips.ethereum.org/EIPS/eip-7594#networking
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- What a response check reads from a block: its slot, the root of its parent and its own root.

The blocks of one response can belong to several forks, and this form is the same for each. -/
structure ResponseBlock where
  /-- The slot of the block. -/
  slot : Slot
  /-- The root of the parent block. -/
  parentRoot : Root
  /-- The root of the block, without its signature. -/
  root : Root
  deriving DecidableEq, Repr

/-- What a response check reads from a signed block.

It fails when the root of the block cannot be computed. -/
def ResponseBlock.ofSigned {preset : Preset} {fork : Fork} (block : SignedBeaconBlock preset fork) :
    Except Err ResponseBlock := do
  let root ← SszType.hashTreeRoot block.message
  return { slot := block.message.slot, parentRoot := block.message.parentRoot, root }

/-- Whether each block of a list has a higher slot than the block before it. -/
def ResponseBlock.slotsAscending : List ResponseBlock → Bool
  | a :: b :: rest => a.slot < b.slot && slotsAscending (b :: rest)
  | _ => true

/-- Whether each block of a list names the block before it as its parent. -/
def ResponseBlock.parentsLinked : List ResponseBlock → Bool
  | a :: b :: rest => b.parentRoot == a.root && parentsLinked (b :: rest)
  | _ => true

/-- Whether a slot lies in the range of a count of slots from a start slot.

The bound is computed without overflow, so a range past the largest slot stops there. -/
def slotInRange (startSlot : Slot) (count : UInt64) (slot : Slot) : Bool :=
  startSlot ≤ slot && slot.toNat < startSlot.toNat + count.toNat

/-- Whether a slot is one that a request for blocks by range names. -/
def BeaconBlocksByRangeRequest.containsSlot (request : BeaconBlocksByRangeRequest)
    (slot : Slot) : Bool :=
  slotInRange request.startSlot request.count slot

/-- Whether the blocks of a response are valid for a request for blocks by range.

The fork is the one in effect when the request is served; it sets the request limit. -/
def isValidBlocksByRangeResponse (config : Config) (fork : Fork)
    (request : BeaconBlocksByRangeRequest) (blocks : List ResponseBlock) : Bool :=
  blocks.length ≤ request.count.toNat &&
    blocks.length ≤ (config.maxRequestBlocks fork).toNat &&
    blocks.all (fun block => request.containsSlot block.slot) &&
    ResponseBlock.slotsAscending blocks &&
    (request.step != 1 || ResponseBlock.parentsLinked blocks)

/-- Whether the blocks of a response are valid for a request for blocks by root. -/
def isValidBlocksByRootResponse {config : Config} {fork : Fork}
    (request : BeaconBlocksByRootRequest config fork) (blocks : List ResponseBlock) : Bool :=
  blocks.length ≤ request.data.size && blocks.all (fun block => request.data.contains block.root)

/-- What a response check reads from a sidecar: the slot and root of its block, and its index.

The index is the index of the blob for a blob sidecar, and of the column for a column sidecar. -/
structure ResponseSidecar where
  /-- The slot of the block. -/
  slot : Slot
  /-- The root of the block, without its signature. -/
  blockRoot : Root
  /-- The index of the sidecar in its block. -/
  index : UInt64
  deriving DecidableEq, Repr

/-- What a response check reads from a blob sidecar.

It fails when the root of the header cannot be computed. -/
def ResponseSidecar.ofBlob {preset : Preset} (sidecar : BlobSidecar preset) :
    Except Err ResponseSidecar := do
  let header := sidecar.signedBlockHeader.message
  let blockRoot ← SszType.hashTreeRoot header
  return { slot := header.slot, blockRoot, index := sidecar.index }

/-- What a response check reads from a column sidecar.

Before Gloas, the slot and root come from the header; it fails when that root cannot be computed.

From Gloas, the sidecar carries the slot and root of its block. -/
def ResponseSidecar.ofColumn {preset : Preset} {fork : Fork}
    (sidecar : DataColumnSidecar preset fork) : Except Err ResponseSidecar :=
  if gloas : .glamsterdam ≤ fork then
    return ⟨sidecar.slot gloas, sidecar.beaconBlockRoot gloas, sidecar.index⟩
  else do
    let header := (sidecar.signedBlockHeader (Nat.lt_of_not_le gloas)).message
    let blockRoot ← SszType.hashTreeRoot header
    return { slot := header.slot, blockRoot, index := sidecar.index }

/-- Whether a relation holds between each item of a list and the item after it. -/
def allAdjacent {α : Type} (r : α → α → Bool) : List α → Bool
  | a :: b :: rest => r a b && allAdjacent r (b :: rest)
  | _ => true

/-- Whether a blob sidecar may follow another in a response by range.

It is the next blob of the same block, or the first blob of a block at a later slot. -/
def ResponseSidecar.nextBlob (a b : ResponseSidecar) : Bool :=
  if a.slot = b.slot then b.blockRoot == a.blockRoot && b.index.toNat == a.index.toNat + 1
  else a.slot < b.slot && b.index == 0

/-- Whether a column sidecar may follow another in a response by range.

It is a later column of the same block, or it belongs to a block at a later slot. -/
def ResponseSidecar.nextColumn (a b : ResponseSidecar) : Bool :=
  if a.slot = b.slot then b.blockRoot == a.blockRoot && a.index < b.index else a.slot < b.slot

/-- Whether the sidecars of a response are valid for a request for blob sidecars by range.

The fork is the one in effect when the request is served; it sets the limits.

A block served under Electra may have the Electra count of blobs, even at an older slot.

From Fulu no new blob sidecars exist, so the Electra count stays the limit. -/
def isValidBlobSidecarsByRangeResponse (config : Config) (fork : Fork)
    (request : BlobSidecarsByRangeRequest) (sidecars : List ResponseSidecar) : Bool :=
  sidecars.length ≤ request.count.toNat * (config.maxRequestBlobsPerBlock fork).toNat &&
    sidecars.length ≤ (computeMaxRequestBlobSidecars config fork).toNat &&
    sidecars.all (fun sidecar => slotInRange request.startSlot request.count sidecar.slot &&
      sidecar.index.toNat < (config.maxRequestBlobsPerBlock fork).toNat) &&
    sidecars.head?.all (fun first => first.index == 0) &&
    allAdjacent ResponseSidecar.nextBlob sidecars

/-- Whether the sidecars of a response are valid for a request for blob sidecars by root. -/
def isValidBlobSidecarsByRootResponse {config : Config} {fork : Fork}
    (request : BlobSidecarsByRootRequest config fork) (sidecars : List ResponseSidecar) : Bool :=
  sidecars.length ≤ request.data.size &&
    sidecars.all (fun sidecar => request.data.contains ⟨sidecar.blockRoot, sidecar.index⟩)

/-- The sidecars of a response grouped by slot: each group is a longest run with one slot. -/
def ResponseSidecar.groupBySlot (sidecars : List ResponseSidecar) : List (List ResponseSidecar) :=
  sidecars.splitBy (fun a b => a.slot == b.slot)

/-- Whether the sidecars of a response are valid for a request for column sidecars by range.

Each block of the response has every requested column. -/
def isValidDataColumnSidecarsByRangeResponse (preset : Preset) (config : Config)
    (request : DataColumnSidecarsByRangeRequest preset) (sidecars : List ResponseSidecar) : Bool :=
  sidecars.length ≤ request.count.toNat * preset.NUMBER_OF_COLUMNS.toNat &&
    sidecars.length ≤ (computeMaxRequestDataColumnSidecars preset config).toNat &&
    sidecars.all (fun sidecar => slotInRange request.startSlot request.count sidecar.slot &&
      sidecar.index < preset.NUMBER_OF_COLUMNS && request.columns.data.contains sidecar.index) &&
    allAdjacent ResponseSidecar.nextColumn sidecars &&
    (ResponseSidecar.groupBySlot sidecars).all (fun block =>
      request.columns.data.all (fun column => block.any (·.index == column)))

/-- The number of column sidecars that a request by root names. -/
def DataColumnSidecarsByRootRequest.columnCount {preset : Preset} {config : Config}
    (request : DataColumnSidecarsByRootRequest preset config) : Nat :=
  request.data.foldl (fun total identifier => total + identifier.columns.data.size) 0

/-- Whether the sidecars of a response are valid for a request for column sidecars by root. -/
def isValidDataColumnSidecarsByRootResponse {preset : Preset} {config : Config}
    (request : DataColumnSidecarsByRootRequest preset config)
    (sidecars : List ResponseSidecar) : Bool :=
  sidecars.length ≤ request.columnCount &&
    sidecars.all (fun sidecar => request.data.any (fun identifier =>
      identifier.blockRoot == sidecar.blockRoot && identifier.columns.data.contains sidecar.index))

end EthLib.Consensus

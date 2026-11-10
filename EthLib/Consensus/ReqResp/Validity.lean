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

/-- Whether a slot is one that a request for blocks by range names.

The bound is computed without overflow, so a range past the largest slot stops there. -/
def BeaconBlocksByRangeRequest.containsSlot (request : BeaconBlocksByRangeRequest)
    (slot : Slot) : Bool :=
  request.startSlot ≤ slot && slot.toNat < request.startSlot.toNat + request.count.toNat

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

end EthLib.Consensus

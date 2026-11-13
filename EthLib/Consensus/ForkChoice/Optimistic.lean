module

public import EthLib.Consensus.ForkChoice.Store
public import EthLib.Consensus.Transition.Execution

/-!
# `Consensus.ForkChoice.Optimistic`

A node may import a block before the execution layer has judged its payload.

The execution layer may later find that payload invalid.

It then names the latest valid payload of the chain, if it knows one.

The first invalid block is the child of the block with that payload, on the chain.

That block and every block that descends from it leave the store.

Their votes and their boost do not count, and no new block can build on them.

So the head falls back to the blocks that the execution layer has not found invalid.

From Gloas a payload arrives apart from its block, so an invalid payload leaves its block valid.

The blocks built on that payload leave the store, and the block stays without it.

A valid payload never turns invalid, unless the execution layer is faulty.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Whether a hash names the payload of a block as the latest valid one.

The zero hash names a block with the empty payload.

A block before Bellatrix has no payload, so the zero hash names it too. -/
def marksLatestValid (latestValidHash : Hash32) (block : BeaconBlock preset fork) : Bool :=
  if range : .bellatrix ≤ fork ∧ fork < .glamsterdam then
    let payload := block.body.executionPayload range
    if latestValidHash = Vector.replicate 32 0 then payload == .empty preset fork
    else payload != .empty preset fork && payload.blockHash == latestValidHash
  else latestValidHash = Vector.replicate 32 0

namespace Store

variable (store : Store preset fork)

/-- The first invalid block of a chain, from a known block and its child on the chain.

The walk climbs from the block until the hash names a payload as the latest valid one.

The result is the child of that block on the chain.

It is none when the walk leaves the store first. -/
def firstInvalidBlock (latestValidHash : Hash32) (child root : Root) :
    Except ForkChoiceError (Option Root) :=
  match _found : store.blocks[root]? with
  | none => pure none
  | some block =>
    if marksLatestValid latestValidHash block then pure (some child)
    else
      match _parentFound : store.blocks[block.parentRoot]? with
      | none => pure none
      | some parent =>
        if _lower : parent.slot < block.slot then
          firstInvalidBlock latestValidHash root block.parentRoot
        else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- The store without the blocks of the given roots.

The votes for those blocks and their boost are dropped too.

So is every record kept by block root, such as the payloads and the votes of the payload committee.

The inclusion lists, kept by slot, stay. -/
def removeBlocks (roots : List Root) : Store preset fork :=
  let kept (root : Root) := !roots.contains root
  { store with
    blocks := store.blocks.filter fun root _ => kept root
    blockStates := store.blockStates.filter fun root _ => kept root
    blockTimeliness := store.blockTimeliness.filter fun root _ => kept root
    ptcTimeliness := fun gloas => (store.ptcTimeliness gloas).filter fun root _ => kept root
    unrealizedJustifications := store.unrealizedJustifications.filter fun root _ => kept root
    latestMessages := store.latestMessages.filter fun _ message => kept message.root
    proposerBoostRoot :=
      if kept store.proposerBoostRoot then store.proposerBoostRoot else Vector.replicate 32 0
    payloads := fun gloas => (store.payloads gloas).filter fun root _ => kept root
    payloadTimelinessVote := fun gloas =>
      (store.payloadTimelinessVote gloas).filter fun root _ => kept root
    payloadDataAvailabilityVote := fun gloas =>
      (store.payloadDataAvailabilityVote gloas).filter fun root _ => kept root
    payloadInclusionListSatisfaction := fun heze =>
      (store.payloadInclusionListSatisfaction heze).filter fun root _ => kept root }

/-- The store without a known block and every known block that descends from it.

An unknown root removes nothing. -/
def removeDescendants (first : Root) : Except ForkChoiceError (Store preset fork) := do
  if !store.blocks.contains first then return store
  let removed ← store.blocks.keys.filterMapM fun known => do
    return if ← store.isAncestor ⟨known, .pending⟩ ⟨first, .pending⟩ then some known else none
  return store.removeBlocks removed

/-- From Gloas: the first block of a chain whose payload is invalid, from a block on the chain.

A candidate holds the earliest block found so far whose payload is invalid.

The result is the first invalid block only when the hash names a payload on the chain.

The execution layer promises that it does.

Each block names, in its bid, the hash of the payload on which it builds.

When that hash is the latest valid one, the candidate is the first invalid block.

Otherwise the walk climbs to the parent of the block.

When the block builds on the payload of its parent, that payload is invalid too.

The parent then becomes the candidate.

When the block builds on its parent without the payload, that payload is not on the chain.

The result is none when the walk leaves the store first. -/
def firstInvalidPayload (gloas : .glamsterdam ≤ fork) (latestValidHash : Hash32)
    (candidate : Root) (child : BeaconBlock preset fork) :
    Except ForkChoiceError (Option Root) :=
  if (child.body.signedExecutionPayloadBid gloas).message.parentBlockHash = latestValidHash then
    pure (some candidate)
  else
    match _parentFound : store.blocks[child.parentRoot]? with
    | none => pure none
    | some parent =>
      if _lower : parent.slot < child.slot then
        if parentPayloadStatus child parent = .full then
          firstInvalidPayload gloas latestValidHash child.parentRoot parent
        else firstInvalidPayload gloas latestValidHash candidate parent
      else throw (.parentSlotNotLower child.parentRoot)
termination_by child.slot.toNat
decreasing_by
  all_goals exact UInt64.lt_iff_toNat_lt.mp _lower

/-- From Gloas: the store without the payload of a block and every block built on that payload.

A block built on it is a known block whose bid builds on that payload.

Those blocks, and every block that descends from one of them, leave the store with their records.

The votes for the block with its payload are dropped, so their weight reaches no ancestor.

The block itself stays, without its payload, since its state does not depend on it.

From Heze its record of the inclusion lists stays, but it is read only with its payload.

An unknown root removes nothing. -/
def removeFullDescendants (gloas : .glamsterdam ≤ fork) (first : Root) :
    Except ForkChoiceError (Store preset fork) := do
  if !store.blocks.contains first then return store
  let removed ← store.blocks.keys.filterMapM fun known => do
    return if ← store.isAncestor ⟨known, .pending⟩ ⟨first, .full⟩ then some known else none
  let kept := store.removeBlocks removed
  return { kept with
    latestMessages := kept.latestMessages.filter fun _ message =>
      !(message.root == first && message.payloadPresent gloas)
    payloads := fun _ => (kept.payloads gloas).filter fun root _ => root != first }

/-- The store after the execution layer finds the payload of a block invalid.

The block may be known or new, and the latest valid hash may be absent.

Before Gloas the first invalid block is the child, on the chain, of the block with that payload.

Without a hash, or when no known block of the chain has that payload, it is the block itself.

So a hash that names a descendant of the block, or no block at all, counts as absent.

The zero hash names the empty payload, so the first block of the chain with a payload is invalid.

On a store anchored above the merge block, no known block has the empty payload.

EthLib then takes the block itself as the first invalid block, a choice of its own.

When the hash names the payload of the block itself, no block is invalid.

That block and every known block that descends from it leave the store.

If the justified block leaves, the head fails, since no chain is left to follow.

From Gloas a payload arrives apart from its block, and the latest valid hash names a payload.

The walk from the block then gives the first invalid block, or none when it leaves the store.

When the hash names the payload of the block itself, nothing is removed.

Without a hash, or with none from the walk, the first invalid block is the block itself.

Its payload, every block built on that payload and their descendants leave the store.

The votes for that block with its payload are dropped, so their weight reaches no ancestor.

The block itself and its node without the payload stay, as do the blocks built on that node.

No published source defines this rule from Gloas, so it is a choice of EthLib. -/
def onInvalidPayload (block : BeaconBlock preset fork) (latestValidHash : Option Hash32) :
    Except ForkChoiceError (Store preset fork) := do
  let root ← (SszType.hashTreeRoot block).mapError .ssz
  if gloas : .glamsterdam ≤ fork then
    let first ← match latestValidHash with
      | none => pure (some root)
      | some hash =>
        if (block.body.signedExecutionPayloadBid gloas).message.blockHash = hash then pure none
        else pure (some ((← store.firstInvalidPayload gloas hash root block).getD root))
    return ← match first with
      | none => pure store
      | some first => store.removeFullDescendants gloas first
  let first ← match latestValidHash with
    | none => pure (some root)
    | some hash =>
      if marksLatestValid hash block then pure none
      else pure (some ((← store.firstInvalidBlock hash root block.parentRoot).getD root))
  match first with
  | none => return store
  | some first => store.removeDescendants first

end Store

end EthLib.Consensus

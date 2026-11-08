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

The votes for those blocks and their boost are dropped too. -/
def removeBlocks (roots : List Root) : Store preset fork :=
  let kept (root : Root) := !roots.contains root
  { store with
    blocks := store.blocks.filter fun root _ => kept root
    blockStates := store.blockStates.filter fun root _ => kept root
    blockTimeliness := store.blockTimeliness.filter fun root _ => kept root
    unrealizedJustifications := store.unrealizedJustifications.filter fun root _ => kept root
    latestMessages := store.latestMessages.filter fun _ message => kept message.root
    proposerBoostRoot :=
      if kept store.proposerBoostRoot then store.proposerBoostRoot else Vector.replicate 32 0 }

/-- The store without a known block and every known block that descends from it.

An unknown root removes nothing. -/
def removeDescendants (first : Root) : Except ForkChoiceError (Store preset fork) := do
  if !store.blocks.contains first then return store
  let removed ← store.blocks.keys.filterMapM fun known => do
    return if ← store.isAncestor ⟨known, .pending⟩ ⟨first, .pending⟩ then some known else none
  return store.removeBlocks removed

/-- The store after the execution layer finds the payload of a block invalid.

The block may be known or new, and the latest valid hash may be absent.

The first invalid block is the child of the block whose payload the hash names, on the chain.

Without a hash, or when no known block of the chain has that payload, it is the block itself.

That covers a hash that names a descendant of the block, or no block at all.

The optimistic sync guide says a node should then act as if the hash were absent.

The zero hash names the empty payload, so the first block of the chain with a payload is invalid.

On a store anchored above the merge block, no known block has the empty payload.

The zero hash then makes the block itself the first invalid block.

When the hash names the payload of the block itself, no block is invalid.

That block and every known block that descends from it leave the store.

If the justified block leaves, the head fails, since no chain is left to follow.

From Gloas the rule is not yet specified here. -/
def onInvalidPayload (block : BeaconBlock preset fork) (latestValidHash : Option Hash32) :
    Except ForkChoiceError (Store preset fork) := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let root ← (SszType.hashTreeRoot block).mapError .ssz
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

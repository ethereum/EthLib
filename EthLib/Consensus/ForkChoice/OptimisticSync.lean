module

public import EthLib.Consensus.ForkChoice.Head
public import EthLib.Consensus.ForkChoice.Optimistic

/-!
# `Consensus.ForkChoice.OptimisticSync`

From Bellatrix, a node may import a block before the execution layer has judged its payload.

Such a block is optimistic until the execution layer answers that its payload is valid or invalid.

The node keeps the roots of the optimistic blocks beside its blocks, in an optimistic store.

A block may be imported optimistically when its parent carries a payload.

It may also be imported once the clock is far enough past the slot of the block.

That distance protects a node from a chain that builds on a payload nobody can check.

A valid payload makes the block and its known ancestors leave the optimistic set.

An invalid one makes the first invalid block and its known descendants leave it.

The rule of the latest valid hash names that first block.

The store of the fork choice removes those blocks, and the optimistic store keeps them.

A node is optimistic when its head is optimistic.

From Gloas the head is a block with or without its payload, which decides the payload it reads.

It is also optimistic when invalid payloads left its block tree with no viable branch.

That needs a block dropped at or above the justified block, and no viable leaf left.

The validators of an optimistic node sign none of these:

- A block, under the proposer domain.
- An attestation, a selection proof or an aggregate and proof.
- A sync committee message, a sync selection proof or a contribution and proof.

The re-run of the checks of the merge block, once its payload is valid, is not defined here.

Neither is the answer to an execution layer that fails to respond.

From Gloas a block carries a bid, and its payload arrives later in an envelope.

The block itself is then checked in full, and only its payload may be optimistic.

The [optimistic sync guide] has no text for Gloas, so EthLib reads it there, a choice of its own.

From Gloas a root of the optimistic set names a block whose payload is not yet judged.

The gossip rules of Gloas key the status of a payload by the root of its block the same way.

From Gloas the ancestors of a payload are the payloads that it builds on, not every ancestor block.

A bid builds on the payload whose block hash it names as its parent block hash.

The [fork choice of Gloas] reads a full parent by the same test.

A block whose payload a child skipped, by building on that block alone, is not one of them.

So a valid payload clears itself and only the payloads that it builds on.

An invalid one clears itself and only the payloads that build on it.

From Gloas the rule of the latest valid hash is not defined, so the caller names the first block.

From Gloas the latest verified ancestor of a node reads only the payloads that the node holds.

So a block without its payload is never its own verified ancestor.

From Gloas the store may lack the payload that a block builds on.

A node without its own payload is then neither optimistic nor not, and the rules fail.

That happens at an empty first block of Gloas, which builds on a payload of Fulu.

It happens too at an empty anchor of a store started from a checkpoint.

From Gloas the status of a node is trusted: a full node must name a payload that the store holds.

From Gloas the second case of an optimistic node is not yet specified here.

It needs the removal of an invalid payload from the store of the fork choice.

The store holds the blocks of one fork, so a payload chain never crosses into Fulu.

The [Heze guide] also records whether a payload satisfies the inclusion lists; it is not modelled.

[optimistic sync guide]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/bellatrix/optimistic-sync.md
[fork choice of Gloas]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/gloas/fork-choice.md#new-get_parent_payload_status
[Heze guide]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/heze/optimistic-sync.md
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The optimistic blocks of a node, beside the blocks it imported, by root.

The guide keeps the states of the blocks there too, which no rule here reads. -/
structure OptimisticStore (preset : Preset) (fork : Fork) where
  /-- The roots of the blocks imported optimistically whose payload is not yet judged.

  From Gloas, the roots of the blocks whose payload was imported optimistically, not yet judged. -/
  optimisticRoots : List Root
  /-- The head of the fork choice: the root of a block and the status of its payload.

  Before Gloas only the root is read. -/
  head : ForkChoiceNode
  /-- The blocks that the node imported, fully or optimistically. -/
  blocks : Std.TreeMap Root (BeaconBlock preset fork)

/-- From Bellatrix: whether a block carries a payload, the empty payload aside.

A block before Bellatrix carries none.

From Gloas a block carries a bid, and the answer is whether the bid names a nonzero block hash.

The zero block hash stands for the empty payload there, a choice of EthLib. -/
def isExecutionBlock (block : BeaconBlock preset fork) : Bool :=
  if gloas : .glamsterdam ≤ fork then
    (block.body.signedExecutionPayloadBid gloas).message.blockHash != Vector.replicate 32 0
  else if range : .bellatrix ≤ fork then
    block.body.executionPayload ⟨range, Nat.lt_of_not_le gloas⟩ != .empty preset fork
  else false

/-- From Bellatrix: whether a block may be imported optimistically at a slot of the clock.

Its parent must be known.

The parent carries a payload, or the slot of the block plus a count is at most the clock's slot.

The count is `SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY` unless the user sets another.

It fails when the parent is not known, and when the slot plus the count overflows 64 bits.

The sum is computed only when the parent carries no payload. -/
def OptimisticStore.isOptimisticCandidateBlock (store : OptimisticStore preset fork)
    (currentSlot : Slot) (block : BeaconBlock preset fork)
    (safeSlots : Slot := SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY) : Except ForkChoiceError Bool := do
  let some parent := store.blocks[block.parentRoot]? | throw (.unknownBlock block.parentRoot)
  if isExecutionBlock parent then return true
  let enough ← (Uint64.addChecked block.slot safeSlots).mapError .arith
  return enough ≤ currentSlot

namespace OptimisticStore

variable (store : OptimisticStore preset fork)

/-- Whether a block, by its root, is optimistic. -/
def isOptimistic (root : Root) : Bool :=
  store.optimisticRoots.contains root

/-- The roots of a known block and of its known ancestors, from the block up.

The walk stops at a parent that the store does not know, such as the parent of the genesis.

It fails when the block is not known, or when a parent is not at a lower slot. -/
def chain (root : Root) : Except ForkChoiceError (List Root) :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block =>
    match _parentFound : store.blocks[block.parentRoot]? with
    | none => pure [root]
    | some parent =>
      if _lower : parent.slot < block.slot then
        return root :: (← chain block.parentRoot)
      else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- From Gloas: whether a root names a known block whose bid names a block hash. -/
def namesBlockHash (gloas : .glamsterdam ≤ fork) (hash : Hash32) (root : Root) : Bool :=
  (store.blocks[root]?).any fun block =>
    (block.body.signedExecutionPayloadBid gloas).message.blockHash == hash

/-- From Gloas: the roots of a chain whose payloads a payload chain holds, in their order.

The hash is the block hash that the next payload of the chain must have, none at the start.

A root is kept when its bid names that hash, and the chain then expects its parent block hash.

A root whose bid names another hash was built on without its payload, and is skipped.

A root of no known block is skipped too, which never happens on the chain of a block. -/
def payloadsOnChain (gloas : .glamsterdam ≤ fork) (expected : Option Hash32) :
    List Root → List Root
  | [] => []
  | root :: rest =>
    match store.blocks[root]? with
    | none => payloadsOnChain gloas expected rest
    | some block =>
      let bid := (block.body.signedExecutionPayloadBid gloas).message
      if expected.all (· == bid.blockHash) then
        root :: payloadsOnChain gloas (some bid.parentBlockHash) rest
      else payloadsOnChain gloas expected rest

/-- The roots of a known block and of the known blocks whose payloads its payload builds on.

The block comes first, then those ancestors, from the block up.

Before Gloas every block carries its payload, so the payload chain is the chain itself.

From Gloas it keeps the blocks of the chain that the bids link by their block hashes.

It fails as the chain of the block does. -/
def payloadChain (root : Root) : Except ForkChoiceError (List Root) := do
  let roots ← store.chain root
  if gloas : .glamsterdam ≤ fork then return store.payloadsOnChain gloas none roots
  else return roots

/-- From Gloas: whether a known block builds on an optimistic payload.

That payload is the second root of the payload chain of the block.

It fails as the payload chain of the block does.

It also fails when the chain has no second root, since the store then lacks that payload.

That happens at the first block of Gloas, which builds on a payload of Fulu. -/
def buildsOnOptimistic (root : Root) : Except ForkChoiceError Bool := do
  let some parent := (← store.payloadChain root)[1]? | throw (.payloadNotVerified root)
  return store.isOptimistic parent

/-- Whether the head of the node is optimistic, the first case of an optimistic node.

Before Gloas it is whether the head block is optimistic.

From Gloas a full head reads the payload of its block.

An empty head reads the payload that its block builds on.

A pending head stands for both: it reads the payload of its block, then the one it builds on.

The search of the head never stops at a pending node, and that reading is a choice of EthLib.

From Gloas an empty head fails as the read of the payload its block builds on does.

A pending head fails that way only when the payload of its block is not optimistic. -/
def isHeadOptimistic : Except ForkChoiceError Bool :=
  if .glamsterdam ≤ fork then
    match store.head.payloadStatus with
    | .full => return store.isOptimistic store.head.root
    | .empty => store.buildsOnOptimistic store.head.root
    | .pending =>
      if store.isOptimistic store.head.root then return true
      else store.buildsOnOptimistic store.head.root
  else return store.isOptimistic store.head.root

/-- Two known blocks, by root, where the bid of the first builds on the payload of the second.

The parent block hash of the first bid is the block hash of the second bid.

The second block need not be the parent of the first; the fork choice would see it as full.

Only a bid builds on a payload, so this holds only from Gloas. -/
def PayloadLink (child parent : Root) : Prop :=
  ∃ childBlock parentBlock, store.blocks[child]? = some childBlock ∧
    store.blocks[parent]? = some parentBlock ∧
    Store.parentPayloadStatus childBlock parentBlock = .full

/-- Before Gloas: the latest block of the chain of a known block that is not optimistic, by root.

The guide assumes that the execution layer never found the block itself invalid.

The walk follows parent roots, and also stops at the genesis block, whose parent root is zero.

It fails when an optimistic block on the way has a parent that is not known.

It also fails when the block is not known, or when a parent is not at a lower slot. -/
def latestVerifiedBlock (root : Root) : Except ForkChoiceError Root :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block =>
    if !store.isOptimistic root || block.parentRoot == Vector.replicate 32 0 then pure root
    else
      match _parentFound : store.blocks[block.parentRoot]? with
      | none => throw (.unknownBlock block.parentRoot)
      | some parent =>
        if _lower : parent.slot < block.slot then latestVerifiedBlock block.parentRoot
        else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- From Gloas: the roots of a payload chain whose payloads a node of its block holds.

A full node holds the payload of its block, so all of them; the caller vouches for that status.

An empty or pending node holds only the payloads that its block builds on: all but the first. -/
def _root_.EthLib.Consensus.ForkChoiceNode.heldPayloads (node : ForkChoiceNode)
    (roots : List Root) : List Root :=
  if node.payloadStatus = .full then roots else roots.tail

/-- The latest block of the chain of a node whose payload is not optimistic, by root.

Before Gloas it reads only the block of the node, and walks its chain.

From Gloas it is the first root not optimistic among the payloads that the node holds.

A full node must name a payload that the store holds, which the rule does not check.

A pending node stands for its block whatever its payload, so it reads as empty.

That reading is a choice of EthLib.

From Gloas it fails when every payload that the node holds is optimistic, or when it holds none.

The error then names the last root of those payloads, or the block of the node.

It also fails as the payload chain of the block does. -/
def latestVerifiedAncestor (node : ForkChoiceNode) : Except ForkChoiceError Root :=
  if .glamsterdam ≤ fork then do
    let held := node.heldPayloads (← store.payloadChain node.root)
    let some ancestor := held.find? (!store.isOptimistic ·)
      | throw (.payloadNotVerified (held.getLastD node.root))
    return ancestor
  else store.latestVerifiedBlock node.root

/-- The optimistic roots after the payload of a known block is found valid.

The roots of its payload chain leave the set.

Those are the block and the ancestors whose payloads it builds on.

Every other root stays.

Before Gloas those are all its known ancestors.

It fails as the chain of the block does. -/
def onValidPayload (root : Root) : Except ForkChoiceError (OptimisticStore preset fork) := do
  let ancestors ← store.payloadChain root
  return { store with
    optimisticRoots := store.optimisticRoots.filter fun optimistic =>
      !ancestors.contains optimistic }

/-- The optimistic roots after the execution layer finds a block to be the first invalid one.

The rule of the latest valid hash names that block.

It leaves the set, with each known descendant whose payload chain holds it.

Before Gloas those are all its known descendants.

From Gloas the rule of the latest valid hash is not defined, and the caller names the block.

Every other root stays.

It fails when an optimistic root is not a known block, or as the chain of one fails. -/
def onInvalidatedPayload (first : Root) : Except ForkChoiceError (OptimisticStore preset fork) := do
  let kept ← store.optimisticRoots.filterMapM fun optimistic => do
    return if (← store.payloadChain optimistic).contains first then none else some optimistic
  return { store with optimisticRoots := kept }

end OptimisticStore

namespace Store

variable (config : Config) (store : Store preset fork)

/-- Whether the block tree has no viable branch above the justified block.

The case holds when the justified block is not in the store, a choice of EthLib.

Otherwise it holds when no leaf above the justified block agrees with the checkpoints.

It fails as the filter of the tree does. -/
def hasNoViableBranch : Except ForkChoiceError Bool :=
  if store.blocks.contains store.justifiedCheckpoint.root then
    return (← store.getFilteredNodeTree config).isEmpty
  else pure true

end Store

/-- Whether a block that the fork choice dropped is the justified block or descends from it.

The optimistic store keeps the blocks that the fork choice drops for an invalid payload.

It fails as the chain of such a block does. -/
def OptimisticStore.invalidatedAbove (optimistic : OptimisticStore preset fork)
    (store : Store preset fork) : Except ForkChoiceError Bool :=
  optimistic.blocks.keys.anyM fun root => do
    if store.blocks.contains root then return false
    return (← optimistic.chain root).contains store.justifiedCheckpoint.root

/-- Whether a node is optimistic: its head is optimistic, or its tree lost every viable branch.

The second case is read only when the first does not hold.

The second case needs a dropped block at or above the justified block.

It also needs no viable branch left.

The optimistic store must hold only blocks that the fork choice accepted, so dropped means invalid.

So a tree that empties with nothing invalidated, as in a long stall, does not count.

The guide asks that every viable branch was invalidated, which needs history the store drops.

This rule approximates it: one invalidated block above the justified block is enough.

From Gloas the second case is not yet specified, and the rule fails when the head is not optimistic.

It also fails as the optimism of the head does. -/
def isOptimisticNode (config : Config) (optimistic : OptimisticStore preset fork)
    (store : Store preset fork) : Except ForkChoiceError Bool := do
  if ← optimistic.isHeadOptimistic then return true
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  if !(← optimistic.invalidatedAbove store) then return false
  store.hasNoViableBranch config

/-- Whether an optimistic validator may not sign under a domain type.

These are the domains of a block, of an attestation and its aggregation, and of a sync committee. -/
def isOptimisticRestrictedDomain (domainType : DomainType) : Bool :=
  [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_SELECTION_PROOF,
    DOMAIN_AGGREGATE_AND_PROOF, DOMAIN_SYNC_COMMITTEE, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF,
    DOMAIN_CONTRIBUTION_AND_PROOF].contains domainType

end EthLib.Consensus

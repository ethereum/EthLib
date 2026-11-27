module

public import EthLib.Consensus.ForkChoice.Handlers
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

From Gloas a builder of an optimistic node submits no bid.

The answer of the execution layer decides whether a block, or from Gloas an envelope, is imported.

The re-run of the checks of the merge block, once its payload is valid, is not defined here.

From Gloas a block carries a bid, and its payload arrives later in an envelope.

The block itself is then checked in full, and only its payload may be optimistic.

From Gloas EthLib keeps the optimistic set by block root, where the guide keeps payload hashes.

The lines below state each choice and each difference.

From Gloas a root of the optimistic set names a block whose payload is not yet judged.

From Gloas the status of a payload is keyed by the root of its block, in gossip too.

The head reads that set through the block hashes that the bids name.

From Gloas the ancestors of a payload are the payloads that it builds on, not every ancestor block.

A bid builds on the payload whose block hash it names as its parent block hash.

A full parent is read by the same test.

A block whose payload a child skipped, by building on that block alone, is not one of them.

So a valid payload clears itself and only the payloads that it builds on.

An invalid one clears itself and only the payloads that build on it.

From Gloas the first invalid block is the block of the earliest invalid payload.

The removal from the store of the fork choice finds it.

From Gloas the latest verified ancestor of a node is a node of the fork choice.

It stops at the genesis block, whose node is the last one of the walk.

From Gloas the store may lack the payload that a block builds on.

A node without its own payload is then neither optimistic nor not, and the rules fail.

That happens at an empty first block of Gloas, which builds on a payload of Fulu.

It happens too at an empty anchor of a store started from a checkpoint.

From Gloas the status of a node is trusted: a full node must name a payload that the store holds.

From Gloas an invalid payload drops only the blocks built on it and their descendants.

The block of that payload stays, so its node without the payload can keep a branch viable.

The store holds the blocks of one fork, so a payload chain never crosses into Fulu.

From Heze the node also records whether a payload satisfies the inclusion lists of the slot before.

A payload not yet validated counts as satisfying them, until the execution layer judges it.

-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The optimistic blocks of a node, beside the blocks it imported, by root.

No rule here reads the states of the blocks, so the store keeps none. -/
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
  -- From Gloas, the bid names a block hash other than zero.
  if gloas : .glamsterdam ≤ fork then
    (block.body.signedExecutionPayloadBid gloas).message.blockHash != Vector.replicate 32 0
  -- From Bellatrix to Fulu, the payload of the block is not the empty payload.
  else if range : .bellatrix ≤ fork then
    block.body.executionPayload ⟨range, Nat.lt_of_not_le gloas⟩ != .empty preset fork
  -- Before Bellatrix, no block carries a payload.
  else false

/-- From Bellatrix: whether a block may be imported optimistically at a slot of the clock.

The count of safe slots is `SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY` unless the user sets another.

It fails when the parent is not known.

It also fails when the slot of the block plus that count overflows 64 bits.

That sum is computed only when the parent carries no payload. -/
def OptimisticStore.isOptimisticCandidateBlock (store : OptimisticStore preset fork)
    (currentSlot : Slot) (block : BeaconBlock preset fork)
    (safeSlots : Slot := SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY) : Except ForkChoiceError Bool := do
  -- The parent of the block is known.
  let some parent := store.blocks[block.parentRoot]? | throw (.unknownBlock block.parentRoot)
  -- A parent that carries a payload makes the block a candidate.
  if isExecutionBlock parent then return true
  -- Else `s + k` is at most the slot of the clock, for the slot `s` of the block and the count `k`.
  let enough ← (Uint64.addChecked block.slot safeSlots).mapError .arith
  return enough ≤ currentSlot

namespace OptimisticStore

variable (store : OptimisticStore preset fork)

/-- Whether a block, by its root, is optimistic. -/
def isOptimistic (root : Root) : Bool :=
  -- The root is among the optimistic roots.
  store.optimisticRoots.contains root

/-- The roots of a known block and of its known ancestors, from the block up.

The walk stops at a parent that the store does not know, such as the parent of the genesis.

It fails when the block is not known, or when a parent is not at a lower slot. -/
def chain (root : Root) : Except ForkChoiceError (List Root) :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block =>
    match _parentFound : store.blocks[block.parentRoot]? with
    -- An unknown parent ends the chain at the block.
    | none => pure [root]
    | some parent =>
      -- Else the block, then the chain of its parent, whose slot is lower.
      if _lower : parent.slot < block.slot then
        return root :: (← chain block.parentRoot)
      else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- From Gloas: whether a root names a known block whose bid names a block hash. -/
def namesBlockHash (gloas : .glamsterdam ≤ fork) (hash : Hash32) (root : Root) : Bool :=
  -- The block is known and the block hash of its bid is the hash.
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
      -- A root whose bid names the expected hash, or any at the start, is kept.
      --
      -- The chain then expects the parent block hash of that bid.
      if expected.all (· == bid.blockHash) then
        root :: payloadsOnChain gloas (some bid.parentBlockHash) rest
      -- A root whose bid names another hash is skipped.
      else payloadsOnChain gloas expected rest

/-- The roots of a known block and of the known blocks whose payloads its payload builds on.

The block comes first, then those ancestors, from the block up.

Before Gloas every block carries its payload, so the payload chain is the chain itself.

From Gloas it keeps the blocks of the chain that the bids link by their block hashes.

It fails as the chain of the block does. -/
def payloadChain (root : Root) : Except ForkChoiceError (List Root) := do
  -- The chain of the block, filtered from Gloas by the block hashes that the bids link.
  let roots ← store.chain root
  if gloas : .glamsterdam ≤ fork then return store.payloadsOnChain gloas none roots
  else return roots

/-- From Gloas: whether a payload, by its block hash, is optimistic.

It is when an optimistic root names a block whose bid names that hash. -/
def isOptimisticPayload (gloas : .glamsterdam ≤ fork) (hash : Hash32) : Bool :=
  store.optimisticRoots.any (store.namesBlockHash gloas hash)

/-- From Gloas: whether a known block names a payload, by its block hash. -/
def knowsPayload (gloas : .glamsterdam ≤ fork) (hash : Hash32) : Bool :=
  store.blocks.keys.any (store.namesBlockHash gloas hash)

/-- From Gloas: whether a node of the fork choice is optimistic.

A full node reads the payload of its block, by the block hash of its bid.

An empty or pending node reads the payload that its block builds on, by the parent block hash.

It fails when the store does not know the block of the node.

It also fails when no known block names the payload that the node builds on, a choice of EthLib. -/
def isNodeOptimistic (gloas : .glamsterdam ≤ fork) (node : ForkChoiceNode) :
    Except ForkChoiceError Bool := do
  let some block := store.blocks[node.root]? | throw (.unknownBlock node.root)
  let bid := (block.body.signedExecutionPayloadBid gloas).message
  match node.payloadStatus with
  -- A full node reads the payload of its block.
  | .full => return store.isOptimisticPayload gloas bid.blockHash
  -- An empty or pending node reads the payload that its block builds on.
  | .empty | .pending =>
    -- The store must know a block that names that payload, else it cannot tell its status.
    unless store.knowsPayload gloas bid.parentBlockHash do
      throw (.payloadNotVerified node.root)
    return store.isOptimisticPayload gloas bid.parentBlockHash

/-- Whether the head of the node is optimistic, the first case of an optimistic node.

Before Gloas it is whether the head block is optimistic.

From Gloas it is whether the head, a node of the fork choice, is optimistic. -/
def isHeadOptimistic : Except ForkChoiceError Bool :=
  if gloas : .glamsterdam ≤ fork then store.isNodeOptimistic gloas store.head
  -- Before Gloas, whether the head block is optimistic.
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

It assumes that the execution layer never found the block itself invalid.

The walk follows parent roots, and also stops at the genesis block, whose parent root is zero.

It fails when an optimistic block on the way has a parent that is not known.

It also fails when the block is not known, or when a parent is not at a lower slot. -/
def latestVerifiedBlock (root : Root) : Except ForkChoiceError Root :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block =>
    -- A block that is not optimistic, or the genesis block with a zero parent root, ends the walk.
    if !store.isOptimistic root || block.parentRoot == Vector.replicate 32 0 then pure root
    -- Else the walk climbs to the parent, which is known and at a lower slot.
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

/-- From Gloas: the latest node at or above a node of the fork choice that is not optimistic.

An optimistic node reads next as the pending node of its block.

An optimistic pending node climbs to its parent, full when it builds on the payload of the parent.

The walk stops at a node that is not optimistic, or at a node of the genesis block.

Away from genesis it fails as the optimism of a node on the way does.

It also fails when a parent is not known, or not at a lower slot. -/
def latestVerifiedNode (gloas : .glamsterdam ≤ fork) (node : ForkChoiceNode) :
    Except ForkChoiceError ForkChoiceNode :=
  match _found : store.blocks[node.root]? with
  | none => throw (.unknownBlock node.root)
  | some block =>
    let bid := (block.body.signedExecutionPayloadBid gloas).message
    -- A full node whose payload is not optimistic ends the walk.
    if node.payloadStatus = .full ∧ !store.isOptimisticPayload gloas bid.blockHash then pure node
    else
      -- Else the node reads as a node of its block without its own payload.
      let current : ForkChoiceNode :=
        if node.payloadStatus = .full then ⟨node.root, .pending⟩ else node
      -- A node of the genesis block, whose parent root is zero, ends the walk.
      --
      -- It is the node itself when it builds on a payload that is not optimistic.
      --
      -- Else it is the pending node of its block.
      if block.parentRoot = Vector.replicate 32 0 then
        pure (if node.payloadStatus ≠ .full ∧ !store.isOptimisticPayload gloas bid.parentBlockHash
          then node else ⟨node.root, .pending⟩)
      -- The store must know a block that names the payload that the node builds on.
      else if !store.knowsPayload gloas bid.parentBlockHash then
        throw (.payloadNotVerified node.root)
      -- A node that builds on a payload that is not optimistic ends the walk.
      else if !store.isOptimisticPayload gloas bid.parentBlockHash then pure current
      -- Else the walk climbs to the node of the parent, which is known and at a lower slot.
      else
        match _parentFound : store.blocks[block.parentRoot]? with
        | none => throw (.unknownBlock block.parentRoot)
        | some parent =>
          if _lower : parent.slot < block.slot then
            latestVerifiedNode gloas ⟨block.parentRoot, Store.parentPayloadStatus block parent⟩
          else throw (.parentSlotNotLower node.root)
termination_by (store.blocks[node.root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- The latest node at or above a node of the fork choice that is not optimistic.

Before Gloas it walks the chain of the block of the node, and keeps the status of the node.

From Gloas it walks the nodes of the fork choice. -/
def latestVerifiedAncestor (node : ForkChoiceNode) : Except ForkChoiceError ForkChoiceNode :=
  if gloas : .glamsterdam ≤ fork then store.latestVerifiedNode gloas node
  -- Before Gloas, the walk of the chain of the block.
  else return ⟨← store.latestVerifiedBlock node.root, node.payloadStatus⟩

/-- The optimistic roots after the payload of a known block is found valid.

The roots of its payload chain leave the set.

Those are the block and the ancestors whose payloads it builds on.

Every other root stays.

Before Gloas those are all its known ancestors.

It fails as the chain of the block does. -/
def onValidPayload (root : Root) : Except ForkChoiceError (OptimisticStore preset fork) := do
  -- The roots of the payload chain of the block leave the set, and every other root stays.
  let ancestors ← store.payloadChain root
  return { store with
    optimisticRoots := store.optimisticRoots.filter fun optimistic =>
      !ancestors.contains optimistic }

/-- The optimistic roots after the execution layer finds a block to be the first invalid one.

The rule of the latest valid hash names that block.

It leaves the set, with each known descendant whose payload chain holds it.

Before Gloas those are all its known descendants.

From Gloas it is the block of the earliest invalid payload.

The removal from the store of the fork choice finds it.

Every other root stays.

It fails when an optimistic root is not a known block, or as the chain of one fails. -/
def onInvalidatedPayload (first : Root) : Except ForkChoiceError (OptimisticStore preset fork) := do
  -- An optimistic root stays unless its payload chain holds the first invalid block.
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
  -- With the justified block in the store, the filtered tree is empty.
  if store.blocks.contains store.justifiedCheckpoint.root then
    return (← store.getFilteredNodeTree config).isEmpty
  -- Without it, no branch counts as viable, a choice of EthLib.
  else pure true

/-- From Heze: the store once the payload of a block moves from not validated to valid.

The execution layer then answers whether that payload satisfies its inclusion lists.

The answer is recorded for that block only, whose payload the store must keep.

The answers for the other blocks, its ancestors among them, stay as they were.

The store does not keep the status of a payload, so the caller must check that it was optimistic.

It fails when the store keeps no payload for the block. -/
def recordValidatedInclusionListSatisfaction (heze : .hegota ≤ fork) (root : Root)
    (satisfied : Bool) : Except ForkChoiceError (Store preset fork) := do
  -- The store keeps the payload of the block.
  unless store.isPayloadVerified (Nat.le_trans (by decide) heze) root do
    throw (.payloadNotVerified root)
  -- The answer is recorded for that block only.
  let satisfaction := (store.payloadInclusionListSatisfaction heze).insert root satisfied
  return { store with payloadInclusionListSatisfaction := fun _ => satisfaction }

end Store

/-- From Bellatrix: the sources of a block whose payload the execution layer gave a status.

A payload not yet validated passes the checks of the execution layer.

From Heze it also counts as satisfying its inclusion lists.

An invalidated payload fails those checks, and counts as not satisfying its lists.

A valid payload keeps the sources as they are.

Any other status counts as invalidated, a choice of EthLib. -/
def BlockSources.withPayloadStatus (sources : BlockSources preset fork)
    (status : PayloadValidationStatus) : BlockSources preset fork :=
  -- A valid payload keeps the sources.
  if status = PAYLOAD_STATUS_VALID then sources
  else
    -- A payload not yet validated is accepted, and any other status is not.
    let accepted := decide (status = PAYLOAD_STATUS_NOT_VALIDATED)
    { sources with engine := .constant accepted, inclusionListSatisfied := fun _ _ => accepted }

/-- From Heze: both stores once the payload of a block moves from not validated to valid.

The payload must be optimistic.

It then leaves the optimistic set, with the payloads that it builds on.

The store of the fork choice records the answer of the execution layer for that block only.

It fails when the payload is not optimistic, and as each of the two updates does. -/
def OptimisticStore.onValidatedPayload (optimistic : OptimisticStore preset fork)
    (store : Store preset fork) (heze : .hegota ≤ fork) (root : Root) (satisfied : Bool) :
    Except ForkChoiceError (OptimisticStore preset fork × Store preset fork) := do
  -- The payload is optimistic.
  unless optimistic.isOptimistic root do throw (.payloadNotOptimistic root)
  -- The store of the fork choice records the answer, and the payload chain leaves the set.
  let recorded ← store.recordValidatedInclusionListSatisfaction heze root satisfied
  return (← optimistic.onValidPayload root, recorded)

/-- Whether a block that the fork choice dropped is the justified block or descends from it.

The optimistic store keeps the blocks that the fork choice drops for an invalid payload.

It fails as the chain of such a block does. -/
def OptimisticStore.invalidatedAbove (optimistic : OptimisticStore preset fork)
    (store : Store preset fork) : Except ForkChoiceError Bool :=
  -- Some block that the fork choice dropped has the justified block on its chain.
  optimistic.blocks.keys.anyM fun root => do
    if store.blocks.contains root then return false
    return (← optimistic.chain root).contains store.justifiedCheckpoint.root

/-- Whether a node is optimistic: its head is optimistic, or its tree lost every viable branch.

The second case is read only when the first does not hold.

The second case needs a dropped block at or above the justified block.

It also needs no viable branch left.

The optimistic store must hold only blocks that the fork choice accepted, so dropped means invalid.

So a tree that empties with nothing invalidated, as in a long stall, does not count.

A rule that every viable branch was invalidated would need history that the store drops.

This rule approximates it: one invalidated block above the justified block is enough.

From Gloas a dropped block is one built on an invalid payload, or a descendant of one.

A block whose own payload is invalid stays, so its node without the payload can stay viable.

It fails as the optimism of the head, the chains of the dropped blocks or the filter does. -/
def isOptimisticNode (config : Config) (optimistic : OptimisticStore preset fork)
    (store : Store preset fork) : Except ForkChoiceError Bool := do
  -- The head is optimistic.
  if ← optimistic.isHeadOptimistic then return true
  -- Else a dropped block sits at or above the justified block, and no viable branch is left.
  if !(← optimistic.invalidatedAbove store) then return false
  store.hasNoViableBranch config

/-- From Gloas: whether the optimism of its node lets a builder submit a bid.

It fails as the optimism of the node does. -/
def mayBuilderSubmitBid (config : Config) (optimistic : OptimisticStore preset fork)
    (store : Store preset fork) (_gloas : .glamsterdam ≤ fork) : Except ForkChoiceError Bool := do
  -- The source: an optimistic builder signs no bid under the builder domain.
  return !(← isOptimisticNode config optimistic store)

/-! ## The answer of the execution layer -/

/-- The answer of the execution layer to a payload that a node imports. -/
inductive PayloadAnswer where
  /-- A status, and the latest valid hash that comes with it, if any. -/
  | status (status : PayloadValidationStatus) (latestValidHash : Option Hash32)
  /-- An error, or no answer at all. -/
  | failure
  deriving DecidableEq, Repr

/-- What a node does with the unit that it imports: a block, or from Gloas an envelope. -/
inductive ImportAction where
  /-- The answer lets the unit be imported, as optimistic when its payload is not yet validated.

  The conditions of an optimistic import are checked apart. -/
  | accept
  /-- Reject the unit only, and invalidate nothing else. -/
  | reject
  /-- Reject the unit, then remove what an invalid payload removes for the latest valid hash. -/
  | invalidate (latestValidHash : Hash32)
  /-- Neither import nor reject the unit, nor apply it to the fork choice. -/
  | defer
  deriving DecidableEq, Repr

/-- What a node does with the unit that it imports, for an answer of the execution layer. -/
def importAction : PayloadAnswer → ImportAction
  -- The source: on an error the unit is neither imported nor applied, and may be queued.
  | .failure => .defer
  | .status status latestValidHash =>
    -- The source: a valid or a not validated payload lets the unit be imported.
    if status = PAYLOAD_STATUS_VALID ∨ status = PAYLOAD_STATUS_NOT_VALIDATED then .accept
    -- The source: an invalidated payload rejects it, and invalidates from the latest valid hash.
    else if status = PAYLOAD_STATUS_INVALIDATED then
      match latestValidHash with
      | some hash => .invalidate hash
      -- Without a latest valid hash only the unit is rejected.
      --
      -- From Gloas the source says so, since the verdict may come from the bid of the envelope.
      --
      -- Before Gloas the unit is then the first invalid block, which the store does not hold.
      | none => .reject
    -- EthLib's choice: a status outside the three is no answer, so it counts as an error.
    else .defer

/-- Whether an optimistic validator may not sign under a domain type.

These are the domains of a block, of an attestation and its aggregation, and of a sync committee. -/
def isOptimisticRestrictedDomain (domainType : DomainType) : Bool :=
  -- The seven domains of proposal, attestation, aggregation and sync committee signing.
  [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_SELECTION_PROOF,
    DOMAIN_AGGREGATE_AND_PROOF, DOMAIN_SYNC_COMMITTEE, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF,
    DOMAIN_CONTRIBUTION_AND_PROOF].contains domainType

end EthLib.Consensus

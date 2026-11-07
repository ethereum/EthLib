module

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

A node whose head is optimistic is an optimistic node, and its validators sign none of these:

- A block, under the proposer domain.
- An attestation, a selection proof or an aggregate and proof.
- A sync committee message, a sync selection proof or a contribution and proof.

The guide also calls a node optimistic when every viable branch of its block tree is invalid.

That case is not defined here.

The re-run of the checks of the merge block, once its payload is valid, is not defined here.

Neither is the answer to an execution layer that fails to respond.

From Gloas the block carries a bid and not a payload, and these rules are not specified there.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The optimistic blocks of a node, beside the blocks it imported, by root.

The guide keeps the states of the blocks there too, which no rule here reads. -/
structure OptimisticStore (preset : Preset) (fork : Fork) where
  /-- The roots of the blocks imported optimistically whose payload is not yet judged. -/
  optimisticRoots : List Root
  /-- The root of the head block. -/
  headBlockRoot : Root
  /-- The blocks that the node imported, fully or optimistically. -/
  blocks : Std.TreeMap Root (BeaconBlock preset fork)

/-- From Bellatrix: whether a block carries a payload, the empty payload aside.

A block before Bellatrix carries none.

From Gloas a block carries a bid and not a payload, so the answer is false. -/
def isExecutionBlock (block : BeaconBlock preset fork) : Bool :=
  if range : .bellatrix ≤ fork ∧ fork < .glamsterdam then
    block.body.executionPayload range != .empty preset fork
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

/-- Whether the head of the node is optimistic, the first case of an optimistic node. -/
def isOptimisticNode : Bool :=
  store.isOptimistic store.headBlockRoot

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

/-- The latest block of the chain of a known block that is not optimistic, by root.

The walk also stops at a block whose parent root is zero, the genesis block.

The guide assumes that the execution layer never found the block itself invalid.

It fails when an optimistic block on the way has a parent that is not known.

It also fails when the block is not known, or when a parent is not at a lower slot. -/
def latestVerifiedAncestor (root : Root) : Except ForkChoiceError Root :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block =>
    if !store.isOptimistic root || block.parentRoot == Vector.replicate 32 0 then pure root
    else
      match _parentFound : store.blocks[block.parentRoot]? with
      | none => throw (.unknownBlock block.parentRoot)
      | some parent =>
        if _lower : parent.slot < block.slot then latestVerifiedAncestor block.parentRoot
        else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- The optimistic roots after the payload of a known block is found valid.

The block and its known ancestors leave the set, and every other root stays.

It fails as the chain of the block does. -/
def onValidPayload (root : Root) : Except ForkChoiceError (OptimisticStore preset fork) := do
  let ancestors ← store.chain root
  return { store with
    optimisticRoots := store.optimisticRoots.filter fun optimistic =>
      !ancestors.contains optimistic }

/-- The optimistic roots after the execution layer finds a block to be the first invalid one.

The rule of the latest valid hash names that block.

It and its known descendants leave the set, and every other root stays.

It fails when an optimistic root is not a known block, or as the chain of one fails. -/
def onInvalidatedPayload (first : Root) : Except ForkChoiceError (OptimisticStore preset fork) := do
  let kept ← store.optimisticRoots.filterMapM fun optimistic => do
    return if (← store.chain optimistic).contains first then none else some optimistic
  return { store with optimisticRoots := kept }

end OptimisticStore

/-- Whether an optimistic validator may not sign under a domain type.

These are the domains of a block, of an attestation and its aggregation, and of a sync committee. -/
def isOptimisticRestrictedDomain (domainType : DomainType) : Bool :=
  [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_SELECTION_PROOF,
    DOMAIN_AGGREGATE_AND_PROOF, DOMAIN_SYNC_COMMITTEE, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF,
    DOMAIN_CONTRIBUTION_AND_PROOF].contains domainType

end EthLib.Consensus

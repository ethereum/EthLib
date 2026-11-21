module

public import EthLib.Engine.Node
public import EthLib.Execution.Rpc.View

/-!
# `Engine.Node.View`

The chain view of an execution node: what its JSON-RPC API reads.

The view holds the valid blocks that the node knows, each with the state after it.

The canonical chain is the chain of the head of the node, from its lowest valid block.

The other valid blocks are off the canonical chain.

The safe and the finalized blocks are those of the last update that applied a head.

The receipts and the logs of a block come from running its body again on its parent.

A block whose parent the node does not hold as valid, such as the first block, has none.

Such a block must have no transaction, or the node gives no view.

The view has no pending block, and no fork ID context beyond a first block of number zero.
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Rpc (BlockRecord ChainView)

namespace Node

/-- The record of a known valid block, with the state after it, its receipts and its logs.

A block on a known valid parent runs its body again on the chain of that parent.

A block on any other parent must have no transaction, and has no receipt and no log.

There is no record for a block that the node does not know as valid, or whose body fails. -/
def validRecord (node : Node) (hash : Hash32) : Option BlockRecord :=
  match node.blocks.lookup hash with
  | some ⟨⟨fork, block⟩, _, .valid post⟩ =>
    let parent := block.header.parentHash
    match node.validState parent with
    | some before => (BlockRecord.ofRun (node.chainAt parent before) block hash post).toOption
    | none => if block.transactions.isEmpty then some ⟨fork, block, hash, post, [], [], none⟩
      else none
  | _ => none

/-- The hashes of the valid blocks that the node knows, each once. -/
def validHashes (node : Node) : List Hash32 :=
  (node.blocks.map (·.1)).eraseDups.filter fun hash => (node.validState hash).isSome

/-- The hashes of the blocks of the chain of the head, oldest first. -/
def canonicalHashes (node : Node) : List Hash32 :=
  (chainOf node.tree node.forkchoice.headBlockHash).reverse

/-- The chain view of the node, under a network ID and a KZG trusted setup.

The canonical blocks are the blocks of the chain of the head, oldest first.

The other valid blocks are off the canonical chain.

A zero safe or finalized hash names no block.

There is no view when a block of that chain is not valid, or when a record fails. -/
def view (node : Node) (networkId : Nat) (setup : TrustedSetup) : Option ChainView := do
  let chain := node.canonicalHashes
  let canonical ← chain.mapM node.validRecord
  let side ← (node.validHashes.filter (· ∉ chain)).mapM node.validRecord
  let named := fun (hash : Hash32) => if hash = ZERO_HASH then none else some hash
  if h : canonical = [] then none
  else
    let lowest := canonical.head h
    some {
      config := node.config
      canonical
      nonempty := h
      side
      safe := named node.forkchoice.safeBlockHash
      finalized := named node.forkchoice.finalizedBlockHash
      networkId
      genesis := if lowest.block.header.number = 0 then
          some (lowest.hash, lowest.block.header.timestamp.toNat)
        else none
      setup }

end Node

end EthLib.Engine

module

public import EthLib.Engine.Node
public import EthLib.Execution.Rpc.View

/-!
# `Engine.Node.View`

The chain view of an execution node: what its JSON-RPC API reads.

The view holds the valid blocks that the node knows, each with the state after it.

It has no pending block.
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Rpc (BlockRecord ChainView namedBlock)

namespace Node

/-- The record of a known valid block, with the state after it, its receipts and its logs.

There is no record for a block that the node does not know as valid, or whose body fails. -/
def validRecord (node : Node) (hash : Hash32) : Option BlockRecord :=
  match node.blocks.lookup hash with
  | some ⟨⟨fork, block⟩, _, .valid post⟩ =>
    let parent := block.header.parentHash
    match node.validState parent with
    -- The receipts and the logs come from running the body again on the chain of the parent.
    | some before => (BlockRecord.ofRun (node.chainAt parent before) block hash post).toOption
    -- A block whose parent the node does not hold as valid, such as the first block, has none.
    --
    -- Such a block must have no transaction, or it has no record.
    | none => if block.transactions.isEmpty then some ⟨fork, block, hash, post, [], [], none⟩
      else none
  | _ => none

/-- The hashes of the valid blocks that the node knows, each once. -/
def validHashes (node : Node) : List Hash32 :=
  (node.blocks.map (·.1)).eraseDups.filter fun hash => (node.validState hash).isSome

/-- The hashes of the blocks of the chain of the head, oldest first. -/
def canonicalHashes (node : Node) : List Hash32 :=
  -- The canonical chain is the chain of the head, back to the lowest block that the node knows.
  (chainOf node.tree node.forkchoice.headBlockHash).reverse

/-- The chain view of the node, under a network ID and a KZG trusted setup. -/
def view (node : Node) (networkId : Nat) (setup : TrustedSetup) : Option ChainView := do
  let chain := node.canonicalHashes
  -- The canonical blocks are the blocks of the chain of the head, oldest first.
  --
  -- There is no view when a block of that chain is not valid, or when a record fails.
  let canonical ← chain.mapM node.validRecord
  -- The other valid blocks are off the canonical chain.
  let side ← (node.validHashes.filter (· ∉ chain)).mapM node.validRecord
  if h : canonical = [] then none
  else
    some {
      config := node.config
      canonical
      nonempty := h
      side
      -- The safe and the finalized blocks are those of the last update that applied a head.
      --
      -- A zero safe or finalized hash names no block.
      safe := namedBlock node.forkchoice.safeBlockHash
      finalized := namedBlock node.forkchoice.finalizedBlockHash
      networkId
      -- The fork ID context comes only from a first canonical block of number zero.
      genesis := (canonical.head h).genesis
      setup }

end Node

end EthLib.Engine

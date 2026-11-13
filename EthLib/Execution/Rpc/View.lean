module

public import EthLib.Execution.Blocks.Transition
public import EthLib.Execution.Rpc.BlockParam
public import EthLib.Execution.Rpc.Errors

/-!
# `Execution.Rpc.View`

The chain view of a node: the blocks that it holds when it answers a query, with their states.

A query of the execution JSON-RPC API names a block, and its answer reads that block.

The canonical chain runs from the lowest block that the node holds to its head.

The node may also hold other blocks, which only a hash can name.

The consensus layer names the safe and the finalized blocks by their hashes.

The node may also offer a sample next block, which the tag `pending` names.

The tags are those of [`block.yaml`][block].

A valid view follows the state transition from its lowest block on.

[EIP-1898][eip1898] lets a query by hash require that the block be canonical.

It says that the node SHOULD answer a block that it does not find with an error, code `-32001`.

With the flag set, it SHOULD also answer a block off the canonical chain with code `-32000`.

The view follows the second recommendation.

A block that it does not find resolves to no block, and each method says what it answers then.

[block]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block.yaml
[eip1898]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-1898.md#specification
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.State (State stateRoot)
open EthLib.Execution.Transactions (Transaction)
open EthLib.Cryptography.Hash.Keccak (keccak256)
open EthLib.Serialization.JsonRpc (RpcError)

/-- A block that a node holds, with its hash, the state after it, its receipts and its logs. -/
structure BlockRecord where
  /-- The fork of the block. -/
  fork : Fork
  /-- The block. -/
  block : Block fork Transaction
  /-- The hash of its header. -/
  hash : Hash32
  /-- The state after the block. -/
  state : State
  /-- The receipts of its transactions, in order, each with the type of its transaction. -/
  receipts : List (UInt8 × Receipt fork)
  /-- The logs of its transactions, in order. -/
  logs : List Log
  /-- The retained block access list, or none when it is unavailable or pruned. -/
  accessList : Option BlockAccessList := none

/-- The block as a recent block of a chain: its fork, its header and its ommers. -/
def BlockRecord.recent (r : BlockRecord) : RecentBlock :=
  ⟨r.fork, r.block.header, r.block.ommers⟩

/-- What a node holds when it answers a query. -/
structure ChainView where
  /-- The configuration of the chain. -/
  config : ChainConfig
  /-- The blocks before the lowest canonical block that its first transitions read, oldest first.

  The node holds neither their bodies nor their states, and takes them as given. -/
  history : List RecentBlock := []
  /-- The canonical chain, from the lowest block that the node holds to its head. -/
  canonical : List BlockRecord
  /-- The node holds at least one block. -/
  nonempty : canonical ≠ []
  /-- Other blocks that the node holds, off the canonical chain. -/
  side : List BlockRecord := []
  /-- The hash of the block that the consensus layer last named safe. -/
  safe : Option Hash32 := none
  /-- The hash of the block that the consensus layer last named finalized. -/
  finalized : Option Hash32 := none
  /-- A sample next block that the node built on top of the head, with contents of its choice. -/
  pending : Option BlockRecord := none
  /-- The network ID of the node. -/
  networkId : Nat
  /-- The genesis hash and timestamp, when the node has that fork-ID context. -/
  genesis : Option (Hash32 × Nat) := none
  /-- `FORK_NEXT_VALUE` of EIP-3675, the block that stands for Paris in the fork ID, if set. -/
  mergeForkBlock : Option Nat := none

namespace ChainView

/-- The head: the last canonical block. -/
def head (v : ChainView) : BlockRecord :=
  v.canonical.getLast v.nonempty

/-- The lowest block that the node holds: the first canonical block. -/
def lowest (v : ChainView) : BlockRecord :=
  v.canonical.head v.nonempty

/-- The chain after the canonical block at index `i`, which the block after it runs on.

Its recent blocks are the blocks of the history, then the canonical blocks up to index `i`. -/
def chainAt (v : ChainView) (i : Nat) (h : i < v.canonical.length) : BlockChain where
  config := v.config
  state := v.canonical[i].state
  recent := v.history ++ (v.canonical.take (i + 1)).map BlockRecord.recent

/-- A record that the state transition gives: its block, run on a chain, gives its state.

The body gives its receipts, its logs and any retained block access list.

When the seal is not checked, the proof of work is left out. -/
def Follows (chain : BlockChain) (checkSeal : Bool) (r : BlockRecord) : Prop :=
  stateTransition chain r.block checkSeal = .ok r.state ∧
    ∃ result, runBody chain r.block = .ok result ∧
      result.output.receipts = r.receipts ∧ result.output.logs = r.logs ∧
      ∀ bal, r.accessList = some bal → bal = result.output.body.builder.build

/-- A view that the state transition gives, from its lowest block on.

The hash of each block is the hash of its header.

The state of the lowest block is an input, and its root is the state root of its header.

The blocks before it are an input too, and the last of them is its parent.

The lowest block and each block off the canonical chain are at the active fork of their header.

Each other canonical block follows the one before it by the state transition.

When the seal is not checked, the proof of work is left out.

A block off the canonical chain is checked for its hash and its fork only.

The pending block is built on top of the head, and its contents are the node's own choice. -/
structure Valid (v : ChainView) (checkSeal : Bool) : Prop where
  /-- The hash of each block is the hash of its header. -/
  hash : ∀ r ∈ v.canonical ++ v.side, r.block.header.hash = .ok r.hash
  /-- The lowest block and each block off the canonical chain are at their active fork. -/
  fork : ∀ r ∈ v.lowest :: v.side,
    v.config.activeFork r.block.header.number r.block.header.timestamp.toNat = some r.fork
  /-- The last block of the history is the parent of the lowest block. -/
  history : ∀ b ∈ v.history.getLast?, b.header.hash = .ok v.lowest.block.header.parentHash
  /-- The state of the lowest block has the state root of its header. -/
  lowest : stateRoot keccak256 v.lowest.state = .ok v.lowest.block.header.stateRoot
  /-- Each other canonical block follows the block before it. -/
  follows : ∀ i (h : i + 1 < v.canonical.length),
    Follows (v.chainAt i (by omega)) checkSeal v.canonical[i + 1]
  /-- The pending block has the hash of its header, the head as parent, and its active fork. -/
  pending : ∀ p, v.pending = some p →
    p.block.header.hash = .ok p.hash ∧ p.block.header.parentHash = v.head.hash ∧
      p.block.header.number = v.head.block.header.number + 1 ∧
      v.config.activeFork p.block.header.number p.block.header.timestamp.toNat = some p.fork

/-- The canonical block of a number, if the node holds one. -/
def byNumber (v : ChainView) (n : Nat) : Option BlockRecord :=
  v.canonical.find? (·.block.header.number == n)

/-- The canonical block of a hash, if the node holds one. -/
def canonicalByHash (v : ChainView) (h : Hash32) : Option BlockRecord :=
  v.canonical.find? (·.hash == h)

/-- The block of a hash, canonical or not, if the node holds one. -/
def byHash (v : ChainView) (h : Hash32) : Option BlockRecord :=
  (v.canonical ++ v.side).find? (·.hash == h)

/-- The block that a tag names, if any.

A safe or finalized hash that names no canonical block resolves to no block. -/
def byTag (v : ChainView) : BlockTag → Option BlockRecord
  | .latest => some v.head
  | .earliest => some v.lowest
  | .safe => v.safe.bind v.canonicalByHash
  | .finalized => v.finalized.bind v.canonicalByHash
  | .pending => v.pending

/-- The error of a query by hash that requires a canonical block, when the block found is not. -/
def notCanonical : RpcError :=
  invalidInput.toRpcError (some (.str "block is not canonical"))

/-- The block that a block parameter names, or no block when the node holds none.

A query by hash that requires a canonical block fails when the block it finds is not one. -/
def resolve (v : ChainView) : BlockParam → Except RpcError (Option BlockRecord)
  | .number n => .ok (v.byNumber n)
  | .tag t => .ok (v.byTag t)
  | .hash h requireCanonical =>
    match v.byHash h with
    | none => .ok none
    | some r =>
      if requireCanonical && (v.canonicalByHash h).isNone then .error notCanonical
      else .ok (some r)

end ChainView

end EthLib.Execution.Rpc

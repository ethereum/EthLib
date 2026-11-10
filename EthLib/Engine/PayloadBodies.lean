module

public import EthLib.Engine.Json

/-!
# `Engine.PayloadBodies`

The methods `engine_getPayloadBodiesByHash` and `engine_getPayloadBodiesByRange`.

Each has versions 1 and 2, and returns the bodies of past payloads.

A body holds the transactions and the withdrawals of a block.

Version 2 adds the block access list of EIP-7928.

The store of the execution layer is an input, with the body of each block that it holds.

It finds a block by its hash, and a block of the canonical chain by its number.

That chain is the one that the latest forkchoice update selected.

The store also gives the number of the latest known block.

EthLib reads that block as one whose body the node holds, as the examples of the source do.

The model does not tie the two lookups together, since the source lets a node skip some blocks.

A node may decline to serve finalized blocks by hash, and a syncing node may serve none by hash.

By range, a syncing node may answer `null` for every block below its latest known block.

The withdrawals of a body are `null` for a block before Shapella.

Its block access list is `null` for a block before Glamsterdam, or when the node pruned it.

The Engine API calls the execution side of Glamsterdam by the name Amsterdam.

A block before the fork that adds a field has no such field, so the store holds nothing for it.

By hash, the answer holds one entry per requested hash, in order, and `null` for a missing block.

By range, the answer holds the canonical blocks from `start`, at most `count` of them.

It holds `null` for a missing block below the latest known block.

It stops at the latest known block, so it holds no trailing `null` past it.

A request with `start` or `count` below 1 is invalid, with JSON-RPC code `-32602`.

A node must take every request of up to 32 bodies, and may refuse a larger one as too large.

A request above the node's limit is too large, with JSON-RPC code `-38004`.

The source sets this minimum for each of the four methods, and EthLib takes one limit for all four.

The parameters are an array of 32-byte block hashes, or `start` and `count` as 64-bit numbers.

Any other parameters are invalid, with code `-32602`.

The source orders no two checks.

EthLib decodes the parameters first, then checks `start` and `count`, then the request size.

The source sets no fork rule for these methods, so EthLib answers both versions at every fork.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`ExecutionPayloadBodyV1`][body-v1] and [`ExecutionPayloadBodyV2`][body-v2]
- [`engine_getPayloadBodiesByHashV1`][hash-v1] and [`engine_getPayloadBodiesByRangeV1`][range-v1]
- [`engine_getPayloadBodiesByHashV2`][hash-v2] and [`engine_getPayloadBodiesByRangeV2`][range-v2]

[body-v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#executionpayloadbodyv1
[body-v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#executionpayloadbodyv2
[hash-v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadbodiesbyhashv1
[range-v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadbodiesbyrangev1
[hash-v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadbodiesbyhashv2
[range-v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadbodiesbyrangev2
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Engine.Json

/-- The fewest bodies that every node must take in one request. -/
def MIN_BODIES_REQUEST_LIMIT : Nat := 32

/-- The body of a block that the store holds, with the fields of the block's fork. -/
structure StoredBody where
  /-- The fork of the block. -/
  fork : Fork
  /-- The bytes of each transaction, in the order that they run. -/
  transactions : List ByteArray
  /-- The withdrawals, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)
  /-- The RLP form of the block access list from Glamsterdam, or `none` if the node pruned it. -/
  blockAccessList : Since .glamsterdam fork (Option ByteArray)

/-- The bodies that an execution layer holds, as the methods read them. -/
structure BodyStore where
  /-- The body of the block with a hash, if the node serves it. -/
  byHash : Hash32 → Option StoredBody
  /-- The body of the canonical block with a number, if the node holds it. -/
  canonical : Nat → Option StoredBody
  /-- The number of the latest known block of the canonical chain. -/
  latest : Nat
  /-- The node holds the body of its latest known block, as EthLib reads the source. -/
  latest_held : (canonical latest).isSome
  /-- The most bodies that one request may ask for. -/
  maxRequest : Nat
  /-- The source requires that a node take every request of up to 32 bodies. -/
  le_maxRequest : MIN_BODIES_REQUEST_LIMIT ≤ maxRequest

/-- The body of a payload, as version 1 answers it. -/
structure ExecutionPayloadBodyV1 where
  /-- The bytes of each transaction, in the order that they run. -/
  transactions : List ByteArray
  /-- The withdrawals, or `none` for a block before Shapella. -/
  withdrawals : Option (List Withdrawal)

/-- The body of a payload, as version 2 answers it. -/
structure ExecutionPayloadBodyV2 extends ExecutionPayloadBodyV1 where
  /-- The RLP form of the block access list.

  It is `none` for a block before Glamsterdam, or if the node pruned it. -/
  blockAccessList : Option ByteArray

namespace StoredBody

/-- The body as version 1 answers it. -/
def toV1 (b : StoredBody) : ExecutionPayloadBodyV1 :=
  ⟨b.transactions, sinceValue b.withdrawals⟩

/-- The body as version 2 answers it. -/
def toV2 (b : StoredBody) : ExecutionPayloadBodyV2 :=
  { b.toV1 with blockAccessList := (sinceValue b.blockAccessList).join }

end StoredBody

/-- The stored body of each requested hash, in order, or `none` for a block that the node lacks.
-/
def bodiesByHash (store : BodyStore) (hashes : List Hash32) :
    Except EngineError (List (Option StoredBody)) := do
  checkRequestSize store.maxRequest hashes.length
  return hashes.map store.byHash

/-- The number of entries of a range: at most `count`, and none past the latest known block. -/
def rangeLength (store : BodyStore) (start count : Nat) : Nat :=
  min count (store.latest + 1 - start)

/-- The stored body of each canonical block from `start`, in order, or `none` where it is missing.

The answer stops at the latest known block. -/
def bodiesByRange (store : BodyStore) (start count : UInt64) :
    Except EngineError (List (Option StoredBody)) := do
  if start = 0 then throw (.invalidParams "start: below 1")
  if count = 0 then throw (.invalidParams "count: below 1")
  checkRequestSize store.maxRequest count.toNat
  return (List.range (rangeLength store start.toNat count.toNat)).map fun i =>
    store.canonical (start.toNat + i)

/-- Version 1 by hash: the body of each requested block, or `none` where the node lacks it. -/
def getPayloadBodiesByHashV1 (store : BodyStore) (hashes : List Hash32) :
    Except EngineError (List (Option ExecutionPayloadBodyV1)) :=
  (·.map (·.map StoredBody.toV1)) <$> bodiesByHash store hashes

/-- Version 2 by hash: the body of each requested block with its block access list, or `none`. -/
def getPayloadBodiesByHashV2 (store : BodyStore) (hashes : List Hash32) :
    Except EngineError (List (Option ExecutionPayloadBodyV2)) :=
  (·.map (·.map StoredBody.toV2)) <$> bodiesByHash store hashes

/-- Version 1 by range: the body of each canonical block from `start`, or `none`. -/
def getPayloadBodiesByRangeV1 (store : BodyStore) (start count : UInt64) :
    Except EngineError (List (Option ExecutionPayloadBodyV1)) :=
  (·.map (·.map StoredBody.toV1)) <$> bodiesByRange store start count

/-- Version 2 by range: the body of each canonical block from `start`, with its access list. -/
def getPayloadBodiesByRangeV2 (store : BodyStore) (start count : UInt64) :
    Except EngineError (List (Option ExecutionPayloadBodyV2)) :=
  (·.map (·.map StoredBody.toV2)) <$> bodiesByRange store start count

/-- The parameters of a request by hash: one array of 32-byte block hashes. -/
def bodiesByHashParams (params : Json) : Decode (List Hash32) := do
  let params ← match params with
    | .arr items => pure items.toList
    | _ => invalid "params: not an array"
  match params with
  | [hashes] => array "hashes" (fixed "block hash" 32) hashes
  | _ => invalid s!"params: got {params.length}, expected 1"

/-- The parameters of a request by range: `start` and `count`, two 64-bit numbers. -/
def bodiesByRangeParams (params : Json) : Decode (UInt64 × UInt64) := do
  let params ← match params with
    | .arr items => pure items.toList
    | _ => invalid "params: not an array"
  match params with
  | [start, count] => return (← uint64 "start" start, ← uint64 "count" count)
  | _ => invalid s!"params: got {params.length}, expected 2"

end EthLib.Engine

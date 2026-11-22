module

public import EthLib.Engine.Json

/-!
# `Engine.PayloadBodies`

The methods `engine_getPayloadBodiesByHash` and `engine_getPayloadBodiesByRange`.

Each has versions 1 and 2, and returns the bodies of past payloads.

A body holds the transactions and the withdrawals of a block.

Version 2 adds the block access list of EIP-7928.

A step comment names the method and its version, as in by range, version 1, step 3.

Version 2 follows version 1 with two numbered additions, as in version 2, addition 1.

The Engine API calls the execution side of Glamsterdam by the name Amsterdam.

The store of the execution layer is an input, with the body of each block that it holds.

The consensus layer also writes the parameters of both requests as JSON.

The source orders no two checks.

EthLib decodes the parameters first, then checks `start` and `count`, then the request size.

The source sets no fork rule for these methods, so EthLib answers both versions at every fork.

The answer is also written as JSON, and read back as a consensus node reads it.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`ExecutionPayloadBodyV1`][body-v1] and [`ExecutionPayloadBodyV2`][body-v2]
- [`engine_getPayloadBodiesByHashV1`][hash-v1] and [`engine_getPayloadBodiesByRangeV1`][range-v1]
- [`engine_getPayloadBodiesByHashV2`][hash-v2] and [`engine_getPayloadBodiesByRangeV2`][range-v2]
- the table of [errors][errors] in `common.md`

[body-v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#executionpayloadbodyv1
[body-v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#executionpayloadbodyv2
[hash-v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadbodiesbyhashv1
[range-v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadbodiesbyrangev1
[hash-v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadbodiesbyhashv2
[range-v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_getpayloadbodiesbyrangev2
[errors]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/common.md#errors
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Rpc (withdrawal withdrawalJson)

/-- The fewest bodies that every node must take in one request. -/
def MIN_BODIES_REQUEST_LIMIT : Nat := 32

/-- The body of a block that the store holds, with the fields of the block's fork. -/
structure StoredBody where
  /-- The fork of the block. -/
  fork : Fork
  /-- The bytes of each transaction, in the order that they run. -/
  transactions : List ByteArray
  -- A block before the fork that adds a field has no such field, so the store holds nothing for it.
  /-- The withdrawals, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)
  /-- The RLP form of the block access list from Glamsterdam, or `none` if the node pruned it. -/
  blockAccessList : Since .glamsterdam fork (Option ByteArray)

/-- The bodies that an execution layer holds, as the methods read them. -/
structure BodyStore where
  -- By hash, version 1, step 4: a node may decline to serve finalized blocks by hash.
  --
  -- Step 7: a syncing node may serve no body at all.
  /-- The body of the block with a hash, if the node serves it. -/
  byHash : Hash32 → Option StoredBody
  -- By range, version 1, step 1: the canonical chain that the latest forkchoice update selected.
  --
  -- Step 9: a syncing node may serve no body, so by step 4 each is `null` below the latest one.
  --
  -- EthLib does not tie this lookup to the one by hash, since the source lets a node skip blocks.
  /-- The body of the canonical block with a number, if the node holds it. -/
  canonical : Nat → Option StoredBody
  /-- The number of the latest known block of the canonical chain. -/
  latest : Nat
  -- By range, version 1, step 4 places `null` only below the latest known block.
  --
  -- The source does not say what a node answers when it lacks that block itself.
  --
  -- EthLib reads that block as one whose body the node holds, as the examples of step 4 do.
  /-- The node holds the body of its latest known block, as EthLib reads the source. -/
  latest_held : (canonical latest).isSome
  /-- The most bodies that one request may ask for. -/
  maxRequest : Nat
  -- By hash, version 1, step 3, and by range, version 1, step 2: at least 32 bodies.
  --
  -- The source sets this minimum for each of the four methods, and EthLib takes one limit for all.
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
  -- By hash, version 1, step 5, and by range, version 1, step 5.
  --
  -- The withdrawals are `null` for a block before Shanghai, here Shapella.
  ⟨b.transactions, sinceValue b.withdrawals⟩

/-- The body as version 2 answers it. -/
def toV2 (b : StoredBody) : ExecutionPayloadBodyV2 :=
  -- Version 2, addition 1: the block access list is `null` for a block before Amsterdam.
  --
  -- Addition 2: it is `null` too when the node pruned it.
  { b.toV1 with blockAccessList := (sinceValue b.blockAccessList).join }

end StoredBody

/-- The stored body of each requested hash, in order, or `none` for a block that the node lacks.
-/
def bodiesByHash (store : BodyStore) (hashes : List Hash32) :
    Except EngineError (List (Option StoredBody)) := do
  -- By hash, version 1, step 3: more hashes than the node takes is `-38004`, too large request.
  checkRequestSize store.maxRequest hashes.length
  -- Steps 1 and 2: the body of each hash, in the order of the request, `null` for a missing block.
  return hashes.map store.byHash

/-- The number of entries of a range: at most `count`, and none past the latest known block. -/
def rangeLength (store : BodyStore) (start count : Nat) : Nat :=
  -- By range, version 1, step 4: no trailing `null` past the latest known block `L`.
  --
  -- So the answer has `min(count, L + 1 - start)` entries, and none when `start > L`.
  min count (store.latest + 1 - start)

/-- The stored body of each canonical block from `start`, in order, or `none` where it is missing.

The answer stops at the latest known block. -/
def bodiesByRange (store : BodyStore) (start count : UInt64) :
    Except EngineError (List (Option StoredBody)) := do
  -- By range, version 1, step 3: `start` or `count` below `1` is `-32602`, invalid params.
  if start = 0 then throw (.invalidParams "start: below 1")
  if count = 0 then throw (.invalidParams "count: below 1")
  -- Step 2: a `count` above what the node takes is `-38004`, too large request.
  checkRequestSize store.maxRequest count.toNat
  -- Step 1: the canonical blocks `start, start + 1, ...`, in the order of the chain.
  --
  -- Step 4: `null` for a missing block below the latest known block.
  return (List.range (rangeLength store start.toNat count.toNat)).map fun i =>
    store.canonical (start.toNat + i)

/-- Version 1 by hash: the body of each requested block, or `none` where the node lacks it. -/
def getPayloadBodiesByHashV1 (store : BodyStore) (hashes : List Hash32) :
    Except EngineError (List (Option ExecutionPayloadBodyV1)) :=
  (·.map (·.map StoredBody.toV1)) <$> bodiesByHash store hashes

/-- Version 2 by hash: the body of each requested block with its block access list, or `none`. -/
def getPayloadBodiesByHashV2 (store : BodyStore) (hashes : List Hash32) :
    Except EngineError (List (Option ExecutionPayloadBodyV2)) :=
  -- Version 2 follows version 1 by hash, with the bodies of version 2.
  (·.map (·.map StoredBody.toV2)) <$> bodiesByHash store hashes

/-- Version 1 by range: the body of each canonical block from `start`, or `none`. -/
def getPayloadBodiesByRangeV1 (store : BodyStore) (start count : UInt64) :
    Except EngineError (List (Option ExecutionPayloadBodyV1)) :=
  (·.map (·.map StoredBody.toV1)) <$> bodiesByRange store start count

/-- Version 2 by range: the body of each canonical block from `start`, with its access list. -/
def getPayloadBodiesByRangeV2 (store : BodyStore) (start count : UInt64) :
    Except EngineError (List (Option ExecutionPayloadBodyV2)) :=
  -- Version 2 follows version 1 by range, with the bodies of version 2.
  (·.map (·.map StoredBody.toV2)) <$> bodiesByRange store start count

/-- The parameters of a request by hash: one array of 32-byte block hashes. -/
def bodiesByHashParams (params : Json) : Decode (List Hash32) := do
  let params ← paramsArray params
  match params with
  -- By hash, request: one parameter, an `Array of DATA` of 32 bytes each.
  | [hashes] => array "hashes" (fixed "block hash" 32) hashes
  -- Any other parameters are `-32602`, invalid params, by the table of errors.
  | _ => invalid s!"params: got {params.length}, expected 1"

/-- The parameters of a request by hash as JSON: one array of block hashes. -/
def bodiesByHashParamsJson (hashes : List Hash32) : Json :=
  -- By hash, request: the array of block hashes as its one parameter.
  .arr #[listJson (dataJson ·.toList) hashes]

/-- The parameters of a request by range: `start` and `count`, two 64-bit numbers. -/
def bodiesByRangeParams (params : Json) : Decode (UInt64 × UInt64) := do
  let params ← paramsArray params
  match params with
  -- By range, request: `start` and `count`, each a `QUANTITY` of 64 bits.
  | [start, count] => return (← uint64 "start" start, ← uint64 "count" count)
  -- Any other parameters are `-32602`, invalid params, by the table of errors.
  | _ => invalid s!"params: got {params.length}, expected 2"

/-- The parameters of a request by range as JSON: `start` and `count`, as quantities. -/
def bodiesByRangeParamsJson (start count : UInt64) : Json :=
  -- By range, request: `start`, then `count`.
  .arr #[quantityJson start.toNat, quantityJson count.toNat]

/-! ## The answer as JSON -/

/-- A body of version 1 as JSON, with `null` for absent withdrawals. -/
def bodyV1Json (b : ExecutionPayloadBodyV1) : Json :=
  Json.mkObj [
    -- `ExecutionPayloadBodyV1`: `transactions`, an `Array of DATA` of EIP-2718 transactions.
    ("transactions", listJson (dataJson ·.data.toList) b.transactions),
    -- `withdrawals`, an `Array of WithdrawalV1`, or `null` before Shanghai, by step 5 of version 1.
    ("withdrawals", optionJson (listJson withdrawalJson) b.withdrawals)]

/-- A body of version 2 as JSON: version 1, then the block access list or `null`. -/
def bodyV2Json (b : ExecutionPayloadBodyV2) : Json :=
  -- `ExecutionPayloadBodyV2`: the fields of version 1, then `blockAccessList`.
  Json.mkObj [
    ("transactions", listJson (dataJson ·.data.toList) b.transactions),
    ("withdrawals", optionJson (listJson withdrawalJson) b.withdrawals),
    -- `blockAccessList`, `DATA|null`: the RLP form of the list of EIP-7928.
    ("blockAccessList", optionJson (dataJson ·.data.toList) b.blockAccessList)]

/-- The fields of a body of version 1. -/
def bodyFieldsV1 : List String := ["transactions", "withdrawals"]

/-- The fields of a body of version 2: version 1 and the block access list. -/
def bodyFieldsV2 : List String := bodyFieldsV1 ++ ["blockAccessList"]

/-- A body of version 1: transactions, and withdrawals that may be `null` or absent.

No other field with a value other than `null` is allowed. -/
def bodyV1OfJson (j : Json) : Read ExecutionPayloadBodyV1 := do
  -- The reader drops a field whose value is `null`, so a missing and a `null` field read the same.
  let fs ← fields "body" j
  -- Not in the source: EthLib rejects any other field.
  --
  -- So a field that the structure does not list is never dropped in silence.
  unless hasOnly fs bodyFieldsV1 do reject "body: a field of no body of version 1"
  return {
    transactions := ← array "transactions" (bytes "transaction") (← field "body" fs "transactions")
    -- Version 1, step 5, by hash and by range: `null` withdrawals, for a block before Shanghai.
    withdrawals := ← (fs.lookup "withdrawals").mapM (array "withdrawals" withdrawal) }

/-- A body of version 2: version 1, and a block access list that may be `null` or absent.

No other field with a value other than `null` is allowed. -/
def bodyV2OfJson (j : Json) : Read ExecutionPayloadBodyV2 := do
  -- The reader drops a field whose value is `null`, so a missing and a `null` field read the same.
  let fs ← fields "body" j
  -- Not in the source: EthLib rejects any other field.
  --
  -- So a field that the structure does not list is never dropped in silence.
  unless hasOnly fs bodyFieldsV2 do reject "body: a field of no body of version 2"
  return {
    transactions := ← array "transactions" (bytes "transaction") (← field "body" fs "transactions")
    withdrawals := ← (fs.lookup "withdrawals").mapM (array "withdrawals" withdrawal)
    -- Version 2, additions 1 and 2: a `null` block access list, before Amsterdam or once pruned.
    blockAccessList := ← (fs.lookup "blockAccessList").mapM (bytes "blockAccessList") }

/-- The answer of version 1, by hash or by range, as JSON: a body or `null` for each entry. -/
def payloadBodiesV1Json (bodies : List (Option ExecutionPayloadBodyV1)) : Json :=
  -- Response: an `Array of ExecutionPayloadBodyV1`.
  --
  -- It holds `null` for a missing block, by step 2 by hash and step 4 by range.
  listJson (optionJson bodyV1Json) bodies

/-- The answer of version 2, by hash or by range, as JSON: a body or `null` for each entry. -/
def payloadBodiesV2Json (bodies : List (Option ExecutionPayloadBodyV2)) : Json :=
  -- Response: an `Array of ExecutionPayloadBodyV2`, or `null` for blocks that are unavailable.
  listJson (optionJson bodyV2Json) bodies

/-- The answer of version 1, by hash or by range: an array of bodies, with `null` entries. -/
def payloadBodiesV1OfJson (j : Json) : Decode (List (Option ExecutionPayloadBodyV1)) :=
  -- Response: an array whose entries are bodies of version 1 or `null`.
  lift (array "result" (nullable bodyV1OfJson) j)

/-- The answer of version 2, by hash or by range: an array of bodies, with `null` entries. -/
def payloadBodiesV2OfJson (j : Json) : Decode (List (Option ExecutionPayloadBodyV2)) :=
  -- Response: an array whose entries are bodies of version 2 or `null`.
  lift (array "result" (nullable bodyV2OfJson) j)

end EthLib.Engine

module

public import EthLib.Execution.Rpc.Receipt

/-!
# `Execution.Rpc.Filter`

The log filters of the execution JSON-RPC API, and the method `eth_getLogs`.

A filter is the object `Filter` of [`filter.yaml`][filter].

It names either one block by its hash, or a range of canonical blocks by its two bounds.

It then asks for logs from some addresses, with some topics at each position.

- An address of `null` takes any address, and a list takes each address in it.
- A topic list of `null` takes any topics.
- At each position of the list, `null` takes any topic, and a list takes each topic in it.

A log matches when its address is taken, and it has a topic at each position of the list.

That topic must be taken at its position.

The source leaves several cases open, and each choice here follows the fixtures where they decide:

- An empty list at a position takes any topic, as `topic-wildcard.io` expects.
- An empty list of addresses takes any address, as an empty list of topics does.
- A log with fewer topics than the list has positions does not match.
  This holds even when each extra position takes any topic.
  No fixture filter ends with a position that takes any topic.
  No text of the source decides the case.
- A list of more than four positions is no error.
  It takes no log of the EVM, which has at most four topics.
- A filter with a block hash and a bound is invalid, though the schema allows it.
  The fixture `filter-error-invalid-blockHash-and-range.io` expects that.
- An omitted bound is the head.
- The logs come in the order of their blocks, then of their position in the block.

The [method][method] resolves the bounds against the head.

A bound above the head, or a first bound above the last, is an invalid parameter, `-32602`.

The method MUST NOT clamp the range to the head or return part of the logs.

Here a number below the lowest block that the node holds gets `4444`, for pruned history.

The method lists that code without saying when it applies.

A `safe` or `finalized` tag can name no block.

For that case, [`block.yaml`][block] points to the answer for an unknown block.

The method defines no such answer.

Here an unknown block hash, and a tag that names no block, get `-32001`, "Resource not found".

[filter]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/filter.yaml
[method]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/filter.yaml
[block]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (Log)

/-- The blocks that a filter reads: one block by its hash, or a range by its optional bounds. -/
inductive FilterBlocks where
  /-- The block of this hash. -/
  | hash (h : Hash32)
  /-- The canonical blocks from the first bound to the last, the head for an omitted bound. -/
  | range (fromBlock toBlock : Option BlockParam)
  deriving DecidableEq, Repr

/-- A log filter. -/
structure Filter where
  /-- The blocks that the filter reads. -/
  blocks : FilterBlocks
  /-- The addresses that the filter takes, or none for any address. -/
  address : Option (List Address)
  /-- What the filter takes at each position of the topics, none for any topic. -/
  topics : List (Option (List Hash32))
  deriving DecidableEq, Repr

namespace Filter

/-- Whether a position of the topic list takes a topic. -/
def takesTopic : Option (List Hash32) → Hash32 → Bool
  | none, _ => true
  | some ts, t => ts.isEmpty || ts.contains t

/-- Whether a filter selects a log, by its address and its topic at each position of the list.

The log needs a topic at each position of the list. -/
def selects (f : Filter) (log : Log) : Bool :=
  (match f.address with
    | none => true
    | some addresses => addresses.isEmpty || addresses.contains log.address) &&
  decide (f.topics.length ≤ log.topics.length) &&
  (f.topics.zip log.topics).all fun (taken, t) => takesTopic taken t

end Filter

/-- The addresses of a filter: `null` for any, one address, or a list of addresses. -/
def filterAddress (j : Json) : Read (Option (List Address)) :=
  match j with
  | .null => pure none
  | .arr _ => some <$> array "address" (address "address") j
  | _ => (some [·]) <$> address "address" j

/-- What a position of the topic list takes: `null` for any, one topic, or a list of topics. -/
def filterTopic (j : Json) : Read (Option (List Hash32)) :=
  match j with
  | .null => pure none
  | .arr _ => some <$> array "topic" (hash32 "topic") j
  | _ => (some [·]) <$> hash32 "topic" j

/-- A filter, from the object `Filter`.

A field whose value is `null` counts as absent.

A field that the schema does not name is ignored. -/
def filterOfJson (j : Json) : Read Filter := do
  let fs ← fields "filter" j
  let address ← match fs.lookup "address" with
    | some a => filterAddress a
    | none => pure none
  let topics ← match fs.lookup "topics" with
    | some t => array "topics" filterTopic t
    | none => pure []
  let fromBlock ← (fs.lookup "fromBlock").mapM (blockNumberOrTagForRange "fromBlock")
  let toBlock ← (fs.lookup "toBlock").mapM (blockNumberOrTagForRange "toBlock")
  let blocks ← match fs.lookup "blockHash", fromBlock, toBlock with
    | some h, none, none => FilterBlocks.hash <$> hash32 "blockHash" h
    | some _, _, _ => reject "filter: a block hash with a bound"
    | none, _, _ => pure (FilterBlocks.range fromBlock toBlock)
  return { blocks, address, topics }

namespace ChainView

/-- The error of a range that reaches past the head, or whose bounds are out of order. -/
def invalidRange (reason : String) : RpcError :=
  RpcError.invalidParams s!"block range: {reason}"

/-- Whether a bound of a range is a number above the head. -/
def aboveHead (v : ChainView) : Option BlockParam → Bool
  | some (.number n) => v.head.block.header.number < n
  | _ => false

/-- The number of the block that a bound of a range names, the head for an omitted bound.

A tag that names no block is an unknown block. -/
def boundNumber (v : ChainView) : Option BlockParam → Except RpcError Nat
  | none => .ok v.head.block.header.number
  | some (.number n) => .ok n
  | some p => do
    match ← v.resolve p with
    | some r => return r.block.header.number
    | none => throw (unknown "block")

/-- The blocks that a filter reads, in order.

For a range, they are the canonical blocks from its first bound to its last.

A number bound above the head is an invalid range, before any tag resolves.

A bound that resolves above the head, or a first bound above the last, is an invalid range too.

Those checks come before the check for pruned blocks. -/
def filterBlocks (v : ChainView) : FilterBlocks → Except RpcError (List BlockRecord)
  | .hash h =>
    match v.byHash h with
    | some r => .ok [r]
    | none => .error (unknown "block")
  | .range fromBlock toBlock => do
    if v.aboveHead fromBlock || v.aboveHead toBlock then throw (invalidRange "beyond the head")
    let first ← v.boundNumber fromBlock
    let last ← v.boundNumber toBlock
    if v.head.block.header.number < last then throw (invalidRange "beyond the head")
    if last < first then throw (invalidRange "the first bound is above the last")
    if first < v.lowest.block.header.number then
      throw (prunedHistoryUnavailable.toRpcError (some (.str s!"block {first}")))
    return v.canonical.filter fun r =>
      first ≤ r.block.header.number && r.block.header.number ≤ last

/-- The logs of some blocks that match a filter, in the order of the blocks, then of the logs. -/
def matchingLogs (v : ChainView) (f : Filter) (blocks : List BlockRecord) :
    Except RpcError (List LogInfo) := do
  let infos ← blocks.mapM (·.receiptInfos v.config)
  return (infos.flatten.flatMap (·.logs)).filter (f.selects ·.log)

/-- The logs that a filter selects, as `eth_getLogs` returns them. -/
def getLogs (v : ChainView) (f : Filter) : Except RpcError (List LogInfo) := do
  v.matchingLogs f (← v.filterBlocks f.blocks)

end ChainView

end EthLib.Execution.Rpc

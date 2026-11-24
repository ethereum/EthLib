module

public import EthLib.Execution.Rpc.Receipt

/-!
# `Execution.Rpc.Filter`

The log filters of the execution JSON-RPC API, and the method `eth_getLogs`.

The source leaves several cases open, and EthLib follows the fixtures where they decide.

Sources, at commit `1ca0818` of execution-apis:

- the object `Filter` of [`filter.yaml`][filter]: the fields of a filter
- the [method][method]: bounds resolved against the head, with no clamping and no partial answer
- [`block.yaml`][block]: the answer for a tag that names no block

[filter]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/filter.yaml
[method]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/eth/filter.yaml
[block]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/block.yaml
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

/-- A log filter.

It names one block by its hash, or a range of canonical blocks by two bounds.

Then it takes logs by their address and by their topic at each position. -/
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
  -- Null takes any topic.
  | none, _ => true
  -- A list takes each topic in it, and an empty list any topic, as `topic-wildcard.io` expects.
  | some ts, t => ts.isEmpty || ts.contains t

/-- Whether a filter selects a log, by its address and its topic at each position of the list. -/
def selects (f : Filter) (log : Log) : Bool :=
  -- Null takes any address, and a list each address in it.
  --
  -- An empty list takes any address, as an empty list of topics does, EthLib's choice.
  (match f.address with
    | none => true
    | some addresses => addresses.isEmpty || addresses.contains log.address) &&
  -- EthLib's choice: the log has a topic at each position, even one that takes any topic.
  --
  -- No fixture and no text of the source decides a filter that ends with such a position.
  --
  -- So a list of more than four positions is no error, but takes no log.
  --
  -- A log has at most four topics.
  decide (f.topics.length ≤ log.topics.length) &&
  -- The topic at each position is taken there.
  (f.topics.zip log.topics).all fun (taken, t) => takesTopic taken t

end Filter

/-- The addresses of a filter: `null` for any, one address, or a list of addresses. -/
def filterAddress (j : Json) : Read (Option (List Address)) :=
  -- The three forms of the schema.
  match j with
  | .null => pure none
  | .arr _ => some <$> array "address" (address "address") j
  | _ => (some [·]) <$> address "address" j

/-- What a position of the topic list takes: `null` for any, one topic, or a list of topics. -/
def filterTopic (j : Json) : Read (Option (List Hash32)) :=
  -- The three forms of the schema.
  match j with
  | .null => pure none
  | .arr _ => some <$> array "topic" (hash32 "topic") j
  | _ => (some [·]) <$> hash32 "topic" j

/-- A filter, from the object `Filter`.

A field whose value is `null` counts as absent.

A field that the schema does not name is ignored. -/
def filterOfJson (j : Json) : Read Filter := do
  let fs ← fields "filter" j
  -- The addresses, any address when absent.
  let address ← match fs.lookup "address" with
    | some a => filterAddress a
    | none => pure none
  -- The topics, no position when absent, so any topics.
  let topics ← match fs.lookup "topics" with
    | some t => array "topics" filterTopic t
    | none => pure []
  -- The two bounds, each a number or a tag of a range.
  let fromBlock ← (fs.lookup "fromBlock").mapM (blockNumberOrTagForRange "fromBlock")
  let toBlock ← (fs.lookup "toBlock").mapM (blockNumberOrTagForRange "toBlock")
  -- A block hash or a range.
  --
  -- A block hash with a bound is invalid, as `filter-error-invalid-blockHash-and-range.io` expects.
  --
  -- The schema allows it.
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

/-- The number of the block that a bound of a range names. -/
def boundNumber (v : ChainView) : Option BlockParam → Except RpcError Nat
  -- An omitted bound is the head, EthLib's choice.
  | none => .ok v.head.block.header.number
  | some (.number n) => .ok n
  -- The method: a tag resolves against the head.
  | some p => do
    match ← v.resolve p with
    | some r => return r.block.header.number
    -- A `safe` or `finalized` tag that names no block takes the answer for an unknown block.
    --
    -- That is what `block.yaml` says, and the method defines no such answer.
    --
    -- A tag that names no block is an unknown block: code -32001, EthLib's choice.
    | none => throw (unknown "block")

/-- The blocks that a filter reads, in order. -/
def filterBlocks (v : ChainView) : FilterBlocks → Except RpcError (List BlockRecord)
  -- The block of the hash, else code -32001, EthLib's choice.
  | .hash h =>
    match v.byHash h with
    | some r => .ok [r]
    | none => .error (unknown "block")
  | .range fromBlock toBlock => do
    -- The method: a number bound above the head, code -32602, checked before any tag resolves.
    if v.aboveHead fromBlock || v.aboveHead toBlock then throw (invalidRange "beyond the head")
    let first ← v.boundNumber fromBlock
    let last ← v.boundNumber toBlock
    -- The method: a bound that resolves above the head, code -32602, with no clamping.
    if v.head.block.header.number < last then throw (invalidRange "beyond the head")
    -- The method: a first bound above the last, code -32602.
    if last < first then throw (invalidRange "the first bound is above the last")
    -- A first bound below the lowest block of the node: code 4444, which the method lists.
    --
    -- EthLib's choice of when it applies, since the method does not say.
    if first < v.lowest.block.header.number then
      throw (prunedHistoryUnavailable.toRpcError (some (.str s!"block {first}")))
    -- The canonical blocks from the first bound to the last, both included.
    return v.canonical.filter fun r =>
      first ≤ r.block.header.number && r.block.header.number ≤ last

/-- The logs of some blocks that match a filter, in the order of the blocks, then of the logs. -/
def matchingLogs (v : ChainView) (f : Filter) (blocks : List BlockRecord) :
    Except RpcError (List LogInfo) := do
  -- The logs of the blocks in order, each block's in their order, that the filter selects.
  let infos ← blocks.mapM (·.receiptInfos v.config)
  return (infos.flatten.flatMap (·.logs)).filter (f.selects ·.log)

/-- The logs that a filter selects, as `eth_getLogs` returns them.

The method MUST NOT clamp the range, and MUST NOT return part of the logs either. -/
def getLogs (v : ChainView) (f : Filter) : Except RpcError (List LogInfo) := do
  v.matchingLogs f (← v.filterBlocks f.blocks)

end ChainView

end EthLib.Execution.Rpc

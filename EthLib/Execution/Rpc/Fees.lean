module

public import EthLib.Execution.Rpc.Receipt

/-!
# `Execution.Rpc.Fees`

The methods `eth_feeHistory` and `eth_baseFee` of [`fee_market.yaml`][fees].

The fee history of a range of blocks that ends at a newest block gives, for each block:

- its base fee per gas, or 0 before London;
- its base fee per blob gas, or 0 before Dencun;
- the ratio of its gas used to its gas limit;
- the ratio of its blob gas used to the most blob gas of a block, or 0 before Dencun;
- the effective tip per gas at each requested percentile of its transactions.

The tip of a transaction is the price per gas that it pays, minus the base fee of its block.

Before London that base fee is 0, so the tip is the whole gas price.

The two lists of base fees end with the base fees of the block after the newest one.

The descriptions of both lists say that this value "can be derived from the newest block".

It is the base fee that the header rule gives to a child of the newest block.

The time of that child is unknown, but it is at least one second after the newest block.

So the fork of the child, and its blob schedule, are taken at that earliest time.

That is exact for a fork that activates at a block number, as London does.

A fork or a blob schedule that activates later than that earliest time is not seen.

`eth_baseFee` gives the base fee of the block after the head, by the same rule.

The source leaves some points open, and the method decides them as follows.

A percentile is a JSON number from 0 to 100, and the list must strictly increase.

Otherwise the request has invalid parameters, code `-32602`.

The range holds the blocks that the node has among the `blockCount` numbers that end at the newest.

It is shorter when the node holds fewer blocks, as the source allows.

A count of 0 gives an empty range, whose oldest block is the one after the newest.

A newest block that the node does not hold gives the error `-32001`.

The newest block is canonical or pending, since the request names it by number or by tag.

The transactions of a block are sorted by ascending tip.

The tip at a percentile is that of the first one at which the gas used so far reaches that share.

The share is of the gas that the receipts of the block record, and the comparison is exact.

A ratio is written with at most 18 decimal places, rounded down.

The rewards are left out when no percentile is requested.

[fees]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/fee_market.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Fees.BlobBaseFee (chainBlobSchedule getBaseFeePerBlobGas)
open EthLib.Execution.Transactions (effectiveGasPrice maxBlobGasPerBlock)
open EthLib.Serialization.JsonRpc

/-- A reward percentile as a decimal: its digits and its number of decimal places.

The reader of the request keeps it from 0 to 100. -/
structure Percentile where
  /-- The digits of the number. -/
  num : Nat
  /-- The number of its decimal places. -/
  exponent : Nat
  deriving DecidableEq, Repr

/-- One percentile is below another. -/
def Percentile.lt (p q : Percentile) : Bool :=
  p.num * 10 ^ q.exponent < q.num * 10 ^ p.exponent

/-- A reward percentile: a JSON number from 0 to 100. -/
def percentile : Json → Read Percentile
  | .num ⟨m, e⟩ =>
    if m < 0 then reject "rewardPercentile: below 0"
    else if 100 * 10 ^ e < m.toNat then reject "rewardPercentile: above 100"
    else pure ⟨m.toNat, e⟩
  | _ => reject "rewardPercentile: not a number"

/-- Whether each percentile of a list is below the next one. -/
def percentilesIncreasing : List Percentile → Bool
  | p :: q :: rest => p.lt q && percentilesIncreasing (q :: rest)
  | _ => true

/-- The tip at a percentile of transactions sorted by tip, each with the gas that it used.

It is the tip of the first transaction at which the gas used so far reaches the percentile.

The percentile is of `total`, the gas used by all of them, and `before` is the gas before these.

The last transaction gives its tip when none before it does, and no transaction gives 0. -/
def tipAt (p : Percentile) (total : Nat) : Nat → List (Nat × Nat) → Nat
  | _, [] => 0
  | _, [(tip, _)] => tip
  | before, (tip, gas) :: rest =>
    if p.num * total ≤ (before + gas) * 100 * 10 ^ p.exponent then tip
    else tipAt p total (before + gas) rest

/-- The fee history of a range of blocks, before it is written as JSON.

Each ratio is a numerator and a denominator. -/
structure FeeHistory where
  /-- The number of the lowest block of the range. -/
  oldestBlock : Nat
  /-- The base fee per gas of each block, then that of the block after the newest. -/
  baseFeePerGas : List Nat
  /-- The base fee per blob gas of each block, then that of the block after the newest. -/
  baseFeePerBlobGas : List Nat
  /-- The gas used and the gas limit of each block. -/
  gasUsedRatio : List (Nat × Nat)
  /-- The blob gas used and the most blob gas of each block. -/
  blobGasUsedRatio : List (Nat × Nat)
  /-- The tips of each block at the requested percentiles, or none when none is requested. -/
  reward : Option (List (List Nat))
  deriving DecidableEq, Repr

namespace BlockRecord

/-- The gas that each transaction of a block used: the growth of the cumulative gas of receipts. -/
def gasUsedList (r : BlockRecord) : List Nat :=
  let cumulative := r.receipts.map (·.2.cumulativeGasUsed)
  List.zipWith (· - ·) cumulative (0 :: cumulative)

/-- The effective tip per gas of each transaction of a block, with the gas that it used.

The tip is the price per gas that the transaction pays, minus the base fee of the block.

The list stops at the shorter of the transactions and the receipts. -/
def tips (r : BlockRecord) : List (Nat × Nat) :=
  (r.block.transactions.map fun tx => effectiveGasPrice r.baseFee tx - r.baseFee).zip
    r.gasUsedList

/-- The tips of a block in ascending order, each with its gas. -/
def sortedTips (r : BlockRecord) : List (Nat × Nat) :=
  r.tips.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- The tip of a block at each percentile, weighted by gas used, or 0 for an empty block. -/
def rewards (r : BlockRecord) (ps : List Percentile) : List Nat :=
  ps.map fun p => tipAt p (r.sortedTips.map (·.2)).sum 0 r.sortedTips

/-- The fork of the block after a block, at the next number and one second after the block.

It is never before the fork of the block itself. -/
def nextFork (r : BlockRecord) (config : ChainConfig) : Fork :=
  match config.activeFork (r.block.header.number + 1) (r.block.header.timestamp.toNat + 1) with
  | some fork => if r.fork ≤ fork then fork else r.fork
  | none => r.fork

/-- The base fee per gas that the header rule gives to the block after a block, or 0 before London.

The rule gives the initial base fee to the first London block. -/
def nextBaseFee (r : BlockRecord) (config : ChainConfig) : Nat :=
  if .london ≤ r.nextFork config then expectedBaseFeeAcross r.block.header else 0

/-- The base fee per blob gas of the block after a block, or 0 before Dencun.

It is that of the excess blob gas that the header rule gives to that block.

The blob schedule is that of the chain at the next number and one second after the block. -/
def nextBlobBaseFee (r : BlockRecord) (config : ChainConfig) : Nat :=
  let fork := r.nextFork config
  let schedule := chainBlobSchedule config fork (r.block.header.number + 1)
    (r.block.header.timestamp.toNat + 1)
  if h : .dencun ≤ fork then
    if hLondon : .london ≤ r.fork then
      getBaseFeePerBlobGas (schedule h) (expectedExcessBlobGas hLondon h r.block.header schedule)
    else 0
  else 0

/-- The blob gas used of a block and the most blob gas of a block, both 0 before Dencun. -/
def blobGasRatio (r : BlockRecord) (config : ChainConfig) : Nat × Nat :=
  (parentBlobGasUsed r.block.header, maxBlobGasPerBlock (blockEnvironment config [] r.block.header))

end BlockRecord

namespace ChainView

/-- The blocks of a fee history that ends at a block: those of the node among `count` numbers.

The numbers end at the number of that block.

The blocks are canonical blocks and the pending block, in order.

A block off the canonical chain is never in the range, so it should not be the newest block. -/
def feeHistoryBlocks (v : ChainView) (count : Nat) (newest : BlockRecord) : List BlockRecord :=
  (v.canonical ++ v.pending.toList).filter fun r =>
    r.block.header.number ≤ newest.block.header.number &&
      newest.block.header.number < r.block.header.number + count

/-- The fee history of up to `count` blocks that end at a block, at some percentiles.

The percentiles must strictly increase, and the node must hold the newest block. -/
def feeHistory (v : ChainView) (count : Nat) (newest : BlockParam) (ps : List Percentile) :
    Except RpcError FeeHistory := do
  unless percentilesIncreasing ps do
    throw (RpcError.invalidParams "rewardPercentiles: not strictly increasing")
  match ← v.resolve newest with
  | none => throw (resourceNotFound.toRpcError (some (.str "newest block not found")))
  | some last =>
    let blocks := v.feeHistoryBlocks count last
    return {
      oldestBlock := (blocks.head?.map (·.block.header.number)).getD
        (last.block.header.number + 1)
      baseFeePerGas := blocks.map (·.baseFee) ++ [last.nextBaseFee v.config]
      baseFeePerBlobGas := blocks.map (·.blobGasPrice v.config) ++ [last.nextBlobBaseFee v.config]
      gasUsedRatio := blocks.map fun r => (r.block.header.gasUsed, r.block.header.gasLimit)
      blobGasUsedRatio := blocks.map (·.blobGasRatio v.config)
      reward := if ps.isEmpty then none else some (blocks.map (·.rewards ps)) }

/-- The base fee per gas of the block after the head, as `eth_baseFee` returns it. -/
def baseFee (v : ChainView) : Nat :=
  v.head.nextBaseFee v.config

end ChainView

/-- A ratio as JSON, with at most 18 decimal places, rounded down. -/
def feeRatioJson (ratio : Nat × Nat) : Json :=
  ratioJson 18 ratio.1 ratio.2

/-- The fee history as the JSON object of the method. -/
def feeHistoryJson (h : FeeHistory) : Json :=
  Json.mkObj ([("oldestBlock", quantityJson h.oldestBlock),
    ("baseFeePerGas", listJson quantityJson h.baseFeePerGas),
    ("baseFeePerBlobGas", listJson quantityJson h.baseFeePerBlobGas),
    ("gasUsedRatio", listJson feeRatioJson h.gasUsedRatio),
    ("blobGasUsedRatio", listJson feeRatioJson h.blobGasUsedRatio)] ++
    match h.reward with
    | some reward => [("reward", listJson (listJson quantityJson) reward)]
    | none => [])

end EthLib.Execution.Rpc

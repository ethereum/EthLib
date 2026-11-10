module

public import EthLib.Base.GasLimit
public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Execution.Blocks.Transition

/-!
# `Engine.BuildPayload`

The payload that the execution layer builds from payload attributes, on the last block of its chain.

The attributes fix the timestamp and the RANDAO mix.

The withdrawals join them from Shapella, the parent beacon block root from Dencun.

The slot and the target gas limit join them from Glamsterdam.

The builder chooses the fee recipient, the extra data and the transactions.

The attributes only suggest a fee recipient, and step 1 of the source lets the builder take another.

The source leaves the choice of the transactions to the builder, so they are an input here.

The parent fixes the number, the base fee and the excess blob gas.

The excess blob gas follows the blob schedule of the chain at the number and the timestamp.

The gas limit moves from the parent's toward a target, by one step of the header check at most.

From Glamsterdam the target is the target gas limit of the attributes, as the source asks.

Before Glamsterdam the builder chooses the target.

A target below 5000, the smallest gas limit, counts as 5000.

The source does not say how far one block moves toward the target; that step is a choice here.

From Glamsterdam a bid of Gloas must take the same step, so the choice matches it.

Only a parent near 5000 with a target below 5000 can make the two disagree, by the floor above.

The block then runs on the state of the chain.

Its roots, gas used, blob gas used, logs Bloom and hashes are those that its body gives.

The body reads none of those fields, so it runs on the header before they are filled.

Last, the build checks its block as the state transition does, so it gives no block that fails it.

The header holds what the body gave, so those checks guard against a value that does not fit.

The checks against the parent can fail, for instance on a timestamp not above the parent's.

They also fail on extra data of more than 32 bytes, or on a block above the size limit of EIP-7934.

The build gives the block, the state after it, its requests and its value to the fee recipient.

The value is the sum of the priority fees, which [`engine_getPayloadV2`][v2] recommends.

Before Paris it always fails, since its header has a difficulty of 0.

The source states the build in [Payload building][build], at commit `3284ee8` of execution-apis.

[`engine_forkchoiceUpdatedV4`][v4] adds the target gas limit.

[build]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-building
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadv2
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Fees.GasLimit (LIMIT_MINIMUM parentGasLimitForCheck)
open EthLib.Execution.Transactions (Transaction effectiveGasPrice)

variable {fork : Fork}

/-- What the builder of a payload chooses. -/
structure BuildChoices where
  /-- The account that receives the fees of the block. -/
  feeRecipient : Address
  /-- The extra data of the block; the build fails on more than 32 bytes. -/
  extraData : ByteArray
  /-- The target gas limit, which counts only before Glamsterdam. -/
  targetGasLimit : UInt64

/-- The target gas limit: that of the attributes from Glamsterdam, else the builder's.

A target below the smallest gas limit, 5000, counts as 5000. -/
def gasTarget (attributes : PayloadAttributes fork) (choices : BuildChoices) : Nat :=
  max LIMIT_MINIMUM
    (if h : .glamsterdam ≤ fork then (attributes.targetGasLimit h).toNat
    else choices.targetGasLimit.toNat)

/-- The header of a built block before its body runs, on a parent.

The fields that the body gives are zero. -/
def buildHeader (config : ChainConfig) (parent : RecentBlock) (parentHash : Hash32)
    (attributes : PayloadAttributes fork) (choices : BuildChoices) : Header fork :=
  let number := parent.header.number + 1
  let timestamp := attributes.timestamp.toNat
  let schedule := Execution.Fees.BlobBaseFee.chainBlobSchedule config fork number timestamp
  { parentHash
    ommersHash := EMPTY_OMMER_HASH
    coinbase := choices.feeRecipient
    stateRoot := 0
    transactionsRoot := 0
    receiptRoot := 0
    bloom := Vector.replicate 256 0
    difficulty := 0
    number
    gasLimit := gasLimitToward (parentGasLimitForCheck parent.fork fork parent.header.gasLimit)
      (gasTarget attributes choices)
    gasUsed := 0
    timestamp := BitVec.ofNat 256 timestamp
    extraData := choices.extraData
    prevRandao := attributes.prevRandao
    nonce := Vector.replicate 8 0
    baseFeePerGas := fun _ => expectedBaseFeeAcross parent.header
    withdrawalsRoot := fun _ => 0
    blobGasUsed := fun _ => 0
    excessBlobGas := fun h =>
      if hLondon : .london ≤ parent.fork then
        (expectedExcessBlobGas hLondon h parent.header schedule).toUInt64
      else 0
    parentBeaconBlockRoot := attributes.parentBeaconBlockRoot
    requestsHash := fun _ => 0
    blockAccessListHash := fun _ => 0
    slotNumber := attributes.slotNumber }

/-- The header of a built block, with the fields that its body gives. -/
def fillHeader (header : Header fork) (output : BlockOutput fork) (roots : OutputRoots) :
    Header fork :=
  { header with
    stateRoot := roots.state
    transactionsRoot := roots.transactions
    receiptRoot := roots.receipts
    bloom := logsBloom output.logs
    gasUsed := output.gas.gasUsed
    withdrawalsRoot := fun _ => roots.withdrawals.getD 0
    blobGasUsed := fun _ => output.gas.blob.toUInt64
    requestsHash := fun _ => requestsHash output.requests
    blockAccessListHash := fun _ => output.accessListHash.getD 0 }

/-- The priority fees that transactions pay to the fee recipient of their block, in wei.

Each transaction pays its gas used times its gas price above the base fee `baseFee`.

The gas used of a transaction is the step of the cumulative gas used of its receipt. -/
def priorityFees (baseFee : Nat) (transactions : List Transaction)
    (receipts : List (UInt8 × Receipt fork)) : Nat :=
  let cumulative := receipts.map (·.2.cumulativeGasUsed)
  let used := List.zipWith (· - ·) cumulative (0 :: cumulative)
  (List.zipWith (fun tx gas => gas * (effectiveGasPrice baseFee tx - baseFee)) transactions
    used).sum

/-- A payload that the execution layer built, with what `engine_getPayload` returns beside it. -/
structure BuiltPayload (fork : Fork) where
  /-- The block of the payload. -/
  block : Block fork Transaction
  /-- The state after the block. -/
  state : Execution.State.State
  /-- The requests of the block, each list with its type byte first; none before Pectra. -/
  requests : List ByteArray
  /-- The value of the block to its fee recipient, in wei: the sum of its priority fees. -/
  blockValue : Nat

/-- Build a payload at `fork` from payload attributes and transactions, on the last block of a chain.

The fork must be the active fork at the number after the parent and at the timestamp.

The result is the block, the state after it, its requests and its value.

It fails when the block cannot be built, or when it would fail the state transition. -/
def buildPayload (chain : BlockChain) (attributes : PayloadAttributes fork)
    (choices : BuildChoices) (transactions : List Transaction) :
    Except BlockError (BuiltPayload fork) := do
  if .hegota ≤ fork then throw (.aborted (.forkNotYetSpecified fork))
  let some parent := chain.recent.getLast? | throw .noParent
  let number := parent.header.number + 1
  unless chain.config.activeFork number attributes.timestamp.toNat = some fork do
    throw .wrongFork
  let parentHash ← parent.header.hash.mapError .encoding
  let header := buildHeader chain.config parent parentHash attributes choices
  let result ← runBody chain ⟨header, transactions, [], attributes.withdrawals⟩
  let block : Block fork Transaction :=
    ⟨fillHeader header result.output result.roots, transactions, [], attributes.withdrawals⟩
  checkBlock chain.config false chain.recent block
  firstFailure (outputChecks block.header result.output result.roots)
  let baseFee := if h : .london ≤ fork then header.baseFeePerGas h else 0
  return { block, state := result.post, requests := result.output.requests
           blockValue := priorityFees baseFee transactions result.output.receipts }

end EthLib.Engine

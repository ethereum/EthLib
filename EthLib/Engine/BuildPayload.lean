module

public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Execution.Blocks.Transition

/-!
# `Engine.BuildPayload`

The block that the execution layer builds from payload attributes, on the last block of its chain.

The attributes fix the timestamp and the RANDAO mix.

From their forks on, they fix the withdrawals, the parent beacon block root and the slot.

The builder chooses the fee recipient, the extra data and the transactions.

The attributes only suggest a fee recipient, and step 1 of the source lets the builder take another.

The source leaves the choice of the transactions to the builder, so they are an input here.

The parent fixes the number, the base fee and the excess blob gas.

The gas limit moves from the parent's toward a target, as far as the header check allows.

That check keeps it strictly within a 1024th of the parent's, and at least 5000.

So each step moves it by at most a 1024th of the parent's, minus one.

From Glamsterdam the target is the target gas limit of the attributes, as the source asks.

Before Glamsterdam the builder chooses the target.

The source does not say how far one block moves toward the target; that step is a choice here.

The block then runs on the state of the chain.

Its roots, gas used, blob gas used, logs Bloom and hashes are those that its body gives.

The body reads none of those fields, so it runs on the header before they are filled.

Last, the build checks its block as the state transition does, so it gives no block that fails it.

The header holds what the body gave, so those checks guard against a value that does not fit.

The checks against the parent can fail, for instance on a timestamp not above the parent's.

They also fail on extra data of more than 32 bytes, or on a block above the size limit of EIP-7934.

The build gives the block and the state after it, not the response of `engine_getPayload`.

Before Paris it always fails, since its header has a difficulty of 0.

The source states the build in [Payload building][build], at commit `3284ee8` of execution-apis.

[`engine_forkchoiceUpdatedV4`][v4] adds the target gas limit.

[build]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-building
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Fees.GasLimit (LIMIT_ADJUSTMENT_FACTOR LIMIT_MINIMUM parentGasLimitForCheck)
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-- The gas limit after a parent's that moves toward a target as far as the header check allows.

The target is at least the smallest gas limit, 5000.

The step is a 1024th of the parent's gas limit, minus one, since the check's bounds are strict. -/
def gasLimitToward (parentGasLimit target : Nat) : Nat :=
  let step := parentGasLimit / LIMIT_ADJUSTMENT_FACTOR - 1
  let target := max target LIMIT_MINIMUM
  if parentGasLimit < target then min (parentGasLimit + step) target
  else max (parentGasLimit - step) target

/-- What the builder of a payload chooses. -/
structure BuildChoices where
  /-- The account that receives the fees of the block. -/
  feeRecipient : Address
  /-- The extra data of the block; the build fails on more than 32 bytes. -/
  extraData : ByteArray
  /-- The target of the gas limit, which counts only before Glamsterdam. -/
  gasLimitTarget : Nat

/-- The target of the gas limit: that of the attributes from Glamsterdam, else the builder's. -/
def gasTarget (attributes : PayloadAttributes fork) (choices : BuildChoices) : Nat :=
  if h : .glamsterdam ≤ fork then (attributes.targetGasLimit h).toNat else choices.gasLimitTarget

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

/-- Build a block at `fork` from payload attributes and transactions, on the last block of a chain.

The fork must be the active fork at the number after the parent and at the timestamp.

The result is the block and the state after it.

It fails when the block cannot be built, or when it would fail the state transition. -/
def buildBlock (chain : BlockChain) (attributes : PayloadAttributes fork) (choices : BuildChoices)
    (transactions : List Transaction) :
    Except BlockError (Block fork Transaction × Execution.State.State) := do
  if .hegota ≤ fork then throw (.aborted (.forkNotYetSpecified fork))
  let some parent := chain.recent.getLast? | throw .noParent
  let number := parent.header.number + 1
  unless chain.config.activeFork number attributes.timestamp.toNat = some fork do
    throw .wrongFork
  let parentHash ← parent.header.hash.mapError .encoding
  let header := buildHeader chain.config parent parentHash attributes choices
  let hashes ← recentHashes chain.recent
  let env := blockEnvironment chain.config hashes header
  let output ← applyBody chain.config env ⟨header, transactions, [], attributes.withdrawals⟩
    ⟨chain.state, ∅, ∅, ∅, ∅⟩
  let post := output.block.applyChanges
  let roots ← outputRoots transactions attributes.withdrawals output post
  let block : Block fork Transaction :=
    ⟨fillHeader header output roots, transactions, [], attributes.withdrawals⟩
  checkBlock chain.config false chain.recent block
  firstFailure (outputChecks block.header output roots)
  return (block, post)

end EthLib.Engine

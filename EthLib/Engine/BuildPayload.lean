module

public import EthLib.Base.GasLimit
public import EthLib.Engine.Block
public import EthLib.Engine.ForkchoiceUpdated
public import EthLib.Execution.Blocks.Transition

/-!
# `Engine.BuildPayload`

The payload that the execution layer builds from payload attributes, on the last block of its chain.

The build gives the block, the state after it, its requests and its value to the fee recipient.

The source states the build in [Payload building][build], at commit `3284ee8` of execution-apis.

A step comment without a method names a step of that section.

Step 5, an ID for each new build, is the ID of the forkchoice update.

Step 6 does not apply here, since EthLib keeps no build between calls.

[`engine_forkchoiceUpdatedV4`][v4] adds the target gas limit.

[`engine_getPayloadV2`][v2] adds the value.

[build]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-building
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_getpayloadv2
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_forkchoiceupdatedv4
-/

@[expose] public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Fees.GasLimit (LIMIT_MINIMUM parentGasLimitForCheck)
open EthLib.Execution.Transactions (Transaction priorityFeeOf)

variable {fork : Fork}

/-- What the builder of a payload chooses. -/
structure BuildChoices where
  /-- The account that receives the fees of the block. -/
  feeRecipient : Address
  /-- The extra data of the block; the build fails on more than 32 bytes. -/
  extraData : ByteArray
  /-- The target gas limit, which counts only before Glamsterdam. -/
  targetGasLimit : UInt64

/-- The target gas limit: that of the attributes from Glamsterdam, else the builder's. -/
def gasTarget (attributes : PayloadAttributes fork) (choices : BuildChoices) : Nat :=
  -- A target below the smallest gas limit, 5000, counts as 5000.
  --
  -- A bid of Gloas takes the same step toward its target, without this floor.
  --
  -- So the build and the bid can differ only on a parent of at most 5002 and a target below 5000.
  max LIMIT_MINIMUM
    -- `engine_forkchoiceUpdatedV4`, step 2: the target gas limit of the attributes.
    (if h : .glamsterdam ≤ fork then (attributes.targetGasLimit h).toNat
    -- Before Glamsterdam the attributes hold no target, and the builder chooses it.
    else choices.targetGasLimit.toNat)

/-- The excess blob gas that a parent gives to the block built on it, from Dencun.

It is 0 before Dencun, where a header has no excess, and on a parent before London. -/
def builtExcessBlobGas (config : ChainConfig) (parent : RecentBlock)
    (attributes : PayloadAttributes fork) : Nat :=
  childExcessBlobGas config fork parent.header (parent.header.number + 1)
    attributes.timestamp.toNat

/-- The header of a built block before its body runs, on a parent.

The fields that the body gives are zero.

The build checks first that the excess blob gas is below `2^64`, so the header holds it exactly. -/
def buildHeader (config : ChainConfig) (parent : RecentBlock) (parentHash : Hash32)
    (attributes : PayloadAttributes fork) (choices : BuildChoices) : Header fork :=
  -- The parent fixes the number.
  let number := parent.header.number + 1
  -- Step 1: the timestamp of the attributes.
  let timestamp := attributes.timestamp.toNat
  { parentHash
    -- EIP-3675: the hash of the RLP of an empty list of ommers.
    ommersHash := EMPTY_OMMER_HASH
    -- Step 1: the attributes only suggest a fee recipient, and the builder may take another.
    coinbase := choices.feeRecipient
    stateRoot := 0
    transactionsRoot := 0
    receiptRoot := 0
    bloom := Vector.replicate 256 0
    -- EIP-3675: a difficulty of 0.
    difficulty := 0
    number
    -- The gas limit moves from the parent's toward the target, by one step at most.
    --
    -- The source does not say how far one block moves.
    --
    -- EthLib takes the step of the header check.
    --
    -- From Glamsterdam a bid of Gloas must take the same step, so the choice matches it.
    gasLimit := gasLimitToward (parentGasLimitForCheck parent.fork fork parent.header.gasLimit)
      (gasTarget attributes choices)
    gasUsed := 0
    timestamp := BitVec.ofNat 256 timestamp
    -- The builder chooses the extra data.
    extraData := choices.extraData
    -- Step 1: the RANDAO mix of the attributes.
    prevRandao := attributes.prevRandao
    -- EIP-3675: a nonce of 8 zero bytes.
    nonce := Vector.replicate 8 0
    -- From London, the parent fixes the base fee.
    baseFeePerGas := fun _ => expectedBaseFeeAcross parent.header
    withdrawalsRoot := fun _ => 0
    blobGasUsed := fun _ => 0
    -- From Dencun, the parent fixes the excess blob gas.
    excessBlobGas := fun _ => UInt64.ofNat (builtExcessBlobGas config parent attributes)
    -- Step 1, from Dencun: the root of the parent beacon block of the attributes.
    parentBeaconBlockRoot := attributes.parentBeaconBlockRoot
    requestsHash := fun _ => 0
    blockAccessListHash := fun _ => 0
    -- Step 1, from Glamsterdam: the slot number of the attributes.
    slotNumber := attributes.slotNumber }

/-- The priority fees that transactions pay to the fee recipient of their block, in wei. -/
def priorityFees (baseFee : Nat) (transactions : List Transaction)
    (receipts : List (UInt8 × Receipt fork)) : Nat :=
  let cumulative := receipts.map (·.2.cumulativeGasUsed)
  -- The gas used of a transaction is its receipt's cumulative gas used minus the one before.
  let used := List.zipWith (· - ·) cumulative (0 :: cumulative)
  -- Each transaction pays its gas used times its gas price above the base fee.
  (List.zipWith (fun tx gas => priorityFeeOf baseFee gas tx) transactions used).sum

/-- A payload that the execution layer built, with what `engine_getPayload` returns beside it. -/
structure BuiltPayload (fork : Fork) where
  /-- The block of the payload. -/
  block : Block fork Transaction
  /-- The state after the block. -/
  state : Execution.State.State
  /-- The requests of the block, each list with its type byte first; none before Pectra. -/
  requests : List ByteArray
  /-- The value of the block, in wei.

  It sums the gas used of each receipt times its price above the base fee. -/
  blockValue : Nat
  /-- The block access list from Glamsterdam, in RLP form, whose hash the header holds. -/
  blockAccessList : Since .glamsterdam fork ByteArray

/-- Build a payload at `fork` from attributes and transactions, on the last block of a chain.

The fork must be the active fork at the number after the parent and at the timestamp.

The result is the block, the state after it, its requests and its value.

From Glamsterdam it also holds the block access list that the run of the body records.

It fails when the block cannot be built, or when it would fail the state transition.

From Fusaka that covers the block size limit of [EIP-7934][eip-7934].

[eip-7934]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7934.md#specification
-/
def buildPayload (chain : BlockChain) (attributes : PayloadAttributes fork)
    (choices : BuildChoices) (transactions : List Transaction) :
    Except BlockError (BuiltPayload fork) := do
  -- From Hegotá the build fails, since the rules of that fork are not here yet.
  if .hegota ≤ fork then throw (.aborted (.forkNotYetSpecified fork))
  -- The parent is the last block of the chain.
  let some parent := chain.recent.getLast? | throw .noParent
  let number := parent.header.number + 1
  -- The fork is the active fork at the number after the parent and at the timestamp.
  let active := chain.config.activeFork number attributes.timestamp.toNat
  unless active = some fork do throw (.wrongFork active fork)
  -- From Dencun the header holds the excess blob gas in 64 bits, so a larger excess fails here.
  let excess := builtExcessBlobGas chain.config parent attributes
  ensure (excess < 2 ^ 64) (.excessBlobGasOverflow excess)
  let parentHash ← parent.header.hash.mapError .encoding
  -- Step 1: the header takes the fields of the attributes, except the fee recipient.
  let header := buildHeader chain.config parent parentHash attributes choices
  -- Steps 2 to 4: a first build with no transaction, then updates until a stop.
  --
  -- The source leaves the choice of the transactions to the client, so they are an input here.
  --
  -- EthLib builds once, with the transactions it is given.
  --
  -- Step 1, from Shapella: the withdrawals of the attributes.
  let result ← runBody chain ⟨header, transactions, [], attributes.withdrawals⟩
  -- The header then takes the fields that the body gives.
  let block : Block fork Transaction :=
    ⟨fillHeader header result.output result.roots, transactions, [], attributes.withdrawals⟩
  -- The build checks its block as the state transition does, so it gives no block that fails.
  --
  -- The checks against the parent can fail, for instance on a timestamp not above the parent's.
  --
  -- They also fail on extra data of more than 32 bytes.
  --
  -- EIP-7934, block creation, from Fusaka: its RLP has at most `MAX_RLP_BLOCK_SIZE` bytes.
  --
  -- Before Paris the build always fails, since its header has a difficulty of 0.
  checkBlock chain.config false chain.recent block
  -- The fields of the header that the body gives match what it gave.
  firstFailure (outputChecks block.header result.output result.roots)
  let baseFee := if h : .london ≤ fork then header.baseFeePerGas h else 0
  -- The list that the body recorded, whose hash the header already holds.
  let blockAccessList ← sinceM fun _ =>
    (Serialization.Rlp.Codec.encode result.output.body.builder.build).mapError .encoding
  -- `engine_getPayloadV2`: the sum of the priority fees of the block, or any other rule.
  --
  -- EthLib takes the sum.
  return { block, state := result.post, requests := result.output.requests
           blockValue := priorityFees baseFee transactions result.output.receipts
           blockAccessList }

/-- Why a build on a chain fails: its attributes, a transaction that does not decode, or its block.
-/
inductive BuildError where
  /-- The attributes fail the checks of the forkchoice update, with that error. -/
  | attributes (e : EngineError)
  /-- A transaction does not decode at the fork of the attributes. -/
  | transaction (e : PayloadError)
  /-- The build fails, with the error of its block. -/
  | block (e : BlockError)
  deriving Repr

/-- The code of a build error: that of the error it holds. -/
def BuildError.code : BuildError → UInt32
  | .attributes e => e.code
  | .transaction e => e.code
  | .block e => e.code

/-- Build a payload on a chain from attributes as a forkchoice update of a version decodes them.

The last recent block is the head that the update applies.

So the attributes must pass the checks of that version against it, which fix their fork.

The transactions are in the form of an execution payload, and decode at that fork. -/
def buildPayloadOnChain (chain : BlockChain) (version : Nat) (attributes : Σ f, PayloadAttributes f)
    (choices : BuildChoices) (transactions : List ByteArray) :
    Except BuildError (Σ fork, BuiltPayload fork) := do
  let some parent := chain.recent.getLast? | throw (.block .noParent)
  -- The checks of the attributes read only the number and the time of the head.
  let head : KnownPayload := ⟨parent.header.parentHash, true,
    parent.header.number, parent.header.timestamp.toNat, none⟩
  let ⟨fork, attributes⟩ ←
    (checkAttributes chain.config version head attributes).mapError .attributes
  let transactions ← (decodeTransactions fork 0 transactions).mapError .transaction
  let built ← (buildPayload chain attributes choices transactions).mapError .block
  return ⟨fork, built⟩

end EthLib.Engine

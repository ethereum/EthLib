module

public import EthLib.Execution.Rpc.Simulate
public import EthLib.Execution.Rpc.Block
public import EthLib.Execution.Rpc.Receipt
public import EthLib.Execution.Rpc.Submit

/-!
# `Execution.Rpc.Simulate.Blocks`

The blocks of `eth_simulateV1`, and the answer of the method.

A simulated block runs through the body of a real block, with the changes of the [notes][notes]:

- its header takes the default values of the notes, then the overrides of the request;
- without validation, its base fee and its base fee per blob gas are 0;
- each call runs as a transaction from its given sender, with no signature;
- the cap at `2^32 - 1` on the gas limit never applies;
- without validation, a call skips the nonce check and the caps at `2^24` of EIP-8037;
- without validation, a call with a fee cap of 0 pays nothing for its gas, as a fixture shows;
- without validation, the block access list need not fit the gas limit, as a fixture shows;
- code that the overrides set at a precompile address replaces it, by the [schema][schema].

Its roots, its gas used, its hash and its size are computed as for a real block.

[notes]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/docs-api/docs/ethsimulatev1-notes.mdx
[schema]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/execute.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.Evm.GasCosts (TX_MAX_GAS_LIMIT)
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions

/-! ## The codes -/

namespace SimulateCode

/-- The code of a nonce below the nonce of the sender. -/
def nonceTooLow : ErrorCode := ⟨-38010, "Transactions nonce is too low"⟩

/-- The code of a nonce above the nonce of the sender. -/
def nonceTooHigh : ErrorCode := ⟨-38011, "Transactions nonce is too high"⟩

/-- The code of a fee cap below the base fee of the block. -/
def baseFeeTooLow : ErrorCode := ⟨-38012, "Transactions baseFeePerGas is too low"⟩

/-- The code of a gas limit below the intrinsic gas. -/
def intrinsicGas : ErrorCode :=
  ⟨-38013, "Not enough gas provided to pay for intrinsic gas for a transaction"⟩

/-- The code of a sender that cannot pay the fees and the value. -/
def insufficientFunds : ErrorCode :=
  ⟨-38014, "Insufficient funds to pay for gas fees and value for a transaction"⟩

/-- The code of a call that does not fit in what its block has left. -/
def blockGasLimit : ErrorCode := ⟨-38015, "Block gas limit exceeded by the block's transactions"⟩

/-- The code of init code above the limit. -/
def initCodeTooLarge : ErrorCode := ⟨-38025, "Max init code size exceeded"⟩

end SimulateCode

/-- The error of a call that cannot enter its simulated block. -/
def simulateInclusionError (e : InclusionError) : RpcError :=
  let data := some (.str (inclusionErrorText e))
  match e with
  | .nonceTooLow .. => SimulateCode.nonceTooLow.toRpcError data
  | .nonceTooHigh .. => SimulateCode.nonceTooHigh.toRpcError data
  | .insufficientMaxFeePerGas .. => SimulateCode.baseFeeTooLow.toRpcError data
  | .transaction (.insufficientGas ..) => SimulateCode.intrinsicGas.toRpcError data
  | .insufficientBalance .. => SimulateCode.insufficientFunds.toRpcError data
  | .gasAllowanceExceeded .. | .blobGasLimitExceeded .. =>
    SimulateCode.blockGasLimit.toRpcError data
  | .transaction (.initCodeTooLarge _) => SimulateCode.initCodeTooLarge.toRpcError data
  -- A nonce at the limit of EIP-2681 gives an internal error, as the fixtures show.
  --
  -- A simulation gives the sender of each call, so the rule on the code of the sender never runs.
  --
  -- That error cannot occur, and EthLib maps it to an internal error.
  | .transaction (.nonceOverflow _) | .missingCode _ | .senderNotEoa _ =>
    internalError.toRpcError data
  -- The source gives no code to the other rules, so EthLib reads them as invalid parameters.
  | _ => RpcError.invalidParams (inclusionErrorText e)

/-- The error of a simulated block whose body fails: that of its call, else an internal error. -/
def simulateBlockError : BlockError → RpcError
  | .invalidTransaction _ e => simulateInclusionError e
  | _ => internalError.toRpcError (some (.str "simulated block: the block is invalid"))

/-! ## The defaults of a block -/

/-- The header of a simulated block at `fork`, before its body runs.

It follows the block `parent`, whose hash is `parentHash`, and takes the overrides `o`.

The other fields take the default values of the notes, and those that the body gives are 0. -/
def simulatedHeader (config : ChainConfig) (fork : Fork) (base parent : RecentBlock)
    (parentHash : Hash32) (number time : Nat) (o : BlockOverrides) (validation : Bool) :
    Header fork :=
  { parentHash
    ommersHash := EMPTY_OMMER_HASH
    -- The fee recipient of the overrides, else that of the block before, as the notes say.
    --
    -- So the first simulated block takes the fee recipient of the base block.
    coinbase := o.feeRecipient.getD parent.header.coinbase
    stateRoot := 0
    transactionsRoot := 0
    receiptRoot := 0
    bloom := Vector.replicate 256 0
    -- From Paris 0, before it the difficulty of the base block, as the notes say.
    difficulty := if fork ≥ .paris then 0 else base.header.difficulty
    number
    -- The gas limit of the overrides, else that of the block before, as the notes say.
    --
    -- So the first simulated block takes the gas limit of the base block.
    gasLimit := o.gasLimit.getD parent.header.gasLimit
    gasUsed := 0
    timestamp := BitVec.ofNat 256 time
    -- Empty, as the notes say.
    extraData := .empty
    prevRandao := o.prevRandao.getD 0
    nonce := Vector.replicate 8 0
    -- The base fee of the overrides, else the one of EIP-1559 with validation, else 0.
    --
    -- With validation, the base fee follows the parent.
    baseFeePerGas := fun _ =>
      match o.baseFeePerGas with
      | some fee => fee.toNat
      | none => if validation then expectedBaseFeeAcross parent.header else 0
    withdrawalsRoot := fun _ => 0
    blobGasUsed := fun _ => 0
    -- The excess blob gas of EIP-4844 after the parent, on which the notes are silent.
    --
    -- The caller has checked that it is below `2^64`, so the header holds it exactly.
    excessBlobGas := fun _ =>
      UInt64.ofNat (childExcessBlobGas config fork parent.header number time)
    -- The notes give no root of the parent beacon block.
    --
    -- EthLib takes a zero root, as the fixtures do.
    parentBeaconBlockRoot := fun _ => 0
    requestsHash := fun _ => 0
    blockAccessListHash := fun _ => 0
    -- The slot after that of the parent, as the notes say.
    --
    -- After a block without a slot, the notes omit it, and EthLib takes 0.
    slotNumber := fun _ =>
      if h : .glamsterdam ≤ parent.fork then parent.header.slotNumber h + 1 else 0 }

/-- The base fee per blob gas that a simulated block sets: its override, else 0 without validation.

With validation and no override, the excess blob gas gives it. -/
def simulatedBlobGasPrice (o : BlockOverrides) (validation : Bool) : Option Nat :=
  match o.blobBaseFee with
  -- The blob base fee of the overrides.
  | some price => some price
  -- Else none with validation, so that the excess blob gas gives it, and 0 without.
  | none => if validation then none else some 0

/-- The state after the overrides of a block at `fork`.

From Spurious Dragon, an override creates no account that it leaves empty, as the fixtures show.

An account is empty when it has no nonce, no balance, no code and no storage. -/
def overrideState (fork : Fork) (before : State) (overrides : List (Address × AccountOverride)) :
    State :=
  let s := applyOverrides before overrides
  -- EthLib's choice: before Spurious Dragon, which brings EIP-161, an override may leave it empty.
  if fork < .spuriousDragon then s
  -- From it, an account that the override created and left empty is removed, as the fixtures show.
  else overrides.foldl (init := s) fun s (a, _) =>
    match before.accounts[a]?, s.accounts[a]? with
    | none, some account =>
      if account.nonce = 0 ∧ account.balance = 0 ∧ account.codeHash = State.EMPTY_CODE_HASH ∧
          (s.storage.getD a ∅).isEmpty then
        { s with accounts := s.accounts.erase a, storage := s.storage.erase a }
      else s
    | _, _ => s

/-- The precompile that a call to each address runs, after the moves of a block.

A moved precompile runs at its new address, and its old address runs none. -/
def movedPrecompiles (moves : List (Address × Address)) (a : Address) : Option Address :=
  match moves.find? (·.2 == a) with
  -- A new address runs the precompile that moved there, the first one if two did, EthLib's choice.
  | some (from_, _) => some from_
  -- An address that a precompile left runs none; any other runs its own.
  | none => if moves.any (·.1 == a) then none else some a

/-- The precompile that a call to each address runs, after the overrides of a block.

The [state override schema][schema] says that such code replaces the precompile.

It also says that a move comes before the code.

So, by EthLib's reading, code at the address that a precompile moved to replaces it too.

[schema]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/execute.yaml -/
def simulatedPrecompiles (overrides : List (Address × AccountOverride)) (a : Address) :
    Option Address :=
  -- The moves of precompiles in the overrides apply first.
  --
  -- Then an address whose code the overrides set runs that code and no precompile.
  if overrides.any fun (b, o) => b == a && o.code.isSome then none
  -- Any other address runs the precompile that the moves leave at it, if any.
  else movedPrecompiles (precompileMoves overrides) a

/-- The rules that a simulation lifts.

The cap at `2^32 - 1` on the gas limit never applies.

Without validation, the nonce check and the caps at `2^24` of EIP-8037 do not apply either.

Without validation, a call with a fee cap of 0 also pays nothing for its gas at any base fee. -/
def simulateLifted (validation : Bool) : LiftedRules :=
  { nonce := !validation, gasCap := !validation, totalGasCap := true, zeroFee := !validation }

/-! ## The defaults of a call -/

/-- The gas limit of a call that names none, after the gas `used` of the earlier calls of its block.

It is at most the gas `budget` that the simulation has left. -/
def defaultCallGas (fork : Fork) (validation : Bool) (gasLimit : Nat) (used : BlockGas)
    (budget : Nat) : Nat :=
  let left :=
    -- From Glamsterdam with validation: the largest gas limit that the block can still include.
    if fork ≥ .glamsterdam ∧ validation then
      let execution := gasLimit - used.execution
      let state := gasLimit - used.state
      -- That gas limit is:
      --
      -- - the state gas left, when the execution gas left is at least `2^24`;
      -- - else the smaller of the two.
      if TX_MAX_GAS_LIMIT ≤ execution then state else min execution state
    -- From Fusaka to BPO5, EthLib's choice: at most `2^24`, the cap of EIP-7825, in both modes.
    --
    -- The notes are silent on it.
    else if fork ≥ .fusaka ∧ fork < .glamsterdam then min TX_MAX_GAS_LIMIT (gasLimit - used.gasUsed)
    -- Else the gas limit of the block minus the gas that the block has used.
    else gasLimit - used.gasUsed
  -- Never above the budget that the simulation has left.
  min left budget

/-- The calls of a block filled with their defaults, as unsigned transactions with their senders.

The gas that each call uses comes off the `budget` of the simulation, which is returned.

`body` is the block after its first system calls. -/
def fillCalls {fork : Fork} (env : BlockEnvironment fork) (validation : Bool)
    (precompiles : Address → Option Address) (body : BodyState) (budget : Nat)
    (calls : List GenericTransaction) :
    Except RpcError (List (Transaction × Address) × Nat) := do
  let lifted := simulateLifted validation
  let step := fun (acc : BodyOutput fork × List (Transaction × Address) × Nat)
      (call : GenericTransaction × Nat) => do
    let (before, filled, budget) := acc
    let (call, index) := call
    let sender := call.sender.getD (Vector.replicate 20 0)
    -- Before London a call without a type or a fee cap is legacy, or type 1 with an access list.
    let call := if fork < .london ∧ call.type.isNone ∧ call.simulateType = 2 ∧
        call.maxFeePerGas.isNone ∧ call.maxPriorityFeePerGas.isNone then
        { call with type := some (if fork ≥ .berlin ∧ call.accessList.isSome then 1 else 0) }
      else call
    -- The nonce of the sender after the earlier calls, and the default gas of the call.
    let nonce := ((TransactionState.ofBlock before.block).getAccount sender).nonce
    let gas := defaultCallGas fork validation env.gasLimit before.gas budget
    let call := call.withDefaults nonce gas
    -- A blob fee cap on a call without blobs is dropped, as the fixtures show.
    let call := if call.simulateType = 3 then call else { call with maxFeePerBlobGas := none }
    let tx ← call.toTransaction env.chainId (call.nonce.getD nonce) (call.gas.getD gas)
      (call.maxFeePerGas.getD 0)
    -- The call runs as a transaction from its given sender, with no signature.
    let after ← (applyTransaction env index before tx
      { senders := fun _ => some sender, precompiles, lifted }).mapError simulateBlockError
    -- The gas that the call used comes off the global budget, as the notes say.
    --
    -- A call that uses more than the budget left fails with code -38026.
    let used := after.cumulativeGasUsed - before.cumulativeGasUsed
    ensure (used ≤ budget) (clientLimitExceeded.toRpcError (some (.str "gas budget exceeded")))
    return (after, filled ++ [(tx, sender)], budget - used)
  let (_, filled, budget) ← calls.zipIdx.foldlM step (⟨body, .zero, 0, [], [], []⟩, [], budget)
  return (filled, budget)

/-! ## The blocks -/

/-- A simulated block, with the sender and the result of each of its transactions. -/
structure SimulatedBlock where
  /-- The block, its hash, the state after it, its receipts and its logs. -/
  record : BlockRecord
  /-- The sender of each transaction, in order. -/
  senders : List Address
  /-- The result of each transaction, in order. -/
  results : List TransactionResult

/-- Simulate a block at `fork` with its number, its time and its request, on a chain.

The block `base` is the base block of the simulation, and `budget` the gas that it has left.

It returns the chain after the block, the gas left, and the block. -/
def simulateBlock (chain : BlockChain) (base : RecentBlock) (fork : Fork) (number time : Nat)
    (request : BlockStateCall) (validation : Bool) (budget : Nat) :
    Except RpcError (BlockChain × Nat × SimulatedBlock) := do
  let some parent := chain.recent.getLast? | throw (callInternalError "no parent block")
  -- The header holds the excess blob gas in 64 bits, so a larger excess builds no block.
  let excess := childExcessBlobGas chain.config fork parent.header number time
  ensure (excess < 2 ^ 64) (callInternalError "the excess blob gas is 2^64 or more")
  let parentHash ← parent.header.hash.mapError fun _ => BlockRecord.encodingError "parent hash"
  let o := request.blockOverrides
  let header : Header fork :=
    simulatedHeader chain.config fork base parent parentHash number time o validation
  -- The overrides of the accounts change the state before the block.
  --
  -- So they are not in its access list.
  let chain := { chain with state := overrideState fork chain.state request.stateOverrides }
  let blobGasPrice := simulatedBlobGasPrice o validation
  let precompiles := simulatedPrecompiles request.stateOverrides
  let hashes ← (recentHashes chain.recent).mapError simulateBlockError
  let env := blockEnvironment chain.config hashes header blobGasPrice
  let start ← (daoTransfer chain.config fork number ⟨chain.state, ∅, ∅, ∅, ∅⟩).mapError
    simulateBlockError
  let body ← (startSystemCalls env parentHash (.init start)).mapError fun _ =>
    callInternalError "the system calls aborted"
  -- The calls with their defaults, then the body of a real block with the overrides.
  let (filled, budget) ← fillCalls env validation precompiles body budget request.calls
  let senders := filled.map (·.2)
  -- Without validation, the block access list need not fit the gas limit, as a fixture shows.
  let overrides : BodyOverrides :=
    { senders := (senders[·]?), precompiles, lifted := simulateLifted validation
      itemCap := validation }
  let block : Block fork Transaction :=
    ⟨header, filled.map (·.1), [], fun _ => o.withdrawals.getD []⟩
  let result ← (runBody chain block overrides blobGasPrice).mapError simulateBlockError
  -- The header takes the fields that the run of the body gives.
  let block := { block with header := fillHeader header result.output result.roots }
  let hash ← block.header.hash.mapError fun _ => BlockRecord.encodingError "block hash"
  let record : BlockRecord :=
    { fork, block, hash, state := result.post, receipts := result.output.receipts
      logs := result.output.logs }
  return (chain.addBlock block result.post, budget, ⟨record, senders, result.output.results⟩)

/-- A simulated block with other transactions in place of its calls, with their root.

Such transactions can be the signed form of the calls, which a real block needs. -/
def SimulatedBlock.withTransactions (b : SimulatedBlock) (txs : List Transaction)
    (root : Hash32) : Block b.record.fork Transaction :=
  { b.record.block with
    header := { b.record.block.header with transactionsRoot := root }
    transactions := txs }

/-- What a simulation carries from one block to the next. -/
structure SimulateStep where
  /-- The chain after the last block. -/
  chain : BlockChain
  /-- The gas that the simulation has left. -/
  budget : Nat
  /-- The number of the last block. -/
  number : Nat
  /-- The time of the last block. -/
  time : Nat
  /-- The blocks so far, gap blocks included. -/
  blocks : List SimulatedBlock

/-- Simulate a block of the request after the empty blocks that fill the gap before it. -/
def SimulateStep.next (config : ChainConfig) (base : RecentBlock) (validation : Bool)
    (blockTime : Nat) (s : SimulateStep) (planned : PlannedBlock × Fork) :
    Except RpcError SimulateStep := do
  let (b, fork) := planned
  -- The empty blocks of the gap first, a block time apart, each at its own fork.
  let gaps := (List.range b.gap).map fun k => (s.number + 1 + k, s.time + blockTime * (k + 1))
  let s ← gaps.foldlM (init := s) fun s (number, time) => do
    let some fork := config.activeFork number time
      | throw (callInternalError "no fork for the block")
    let (chain, budget, block) ← simulateBlock s.chain base fork number time {} validation s.budget
    return { chain, budget, number, time, blocks := s.blocks ++ [block] }
  let (chain, budget, block) ←
    simulateBlock s.chain base fork b.number b.time b.request validation s.budget
  return { chain, budget, number := b.number, time := b.time, blocks := s.blocks ++ [block] }

/-- The blocks of a simulation on top of the block that `p` names, gap blocks included.

The base block must be canonical, so that the hashes before each block are those of its chain. -/
def ChainView.simulateBlocks (v : ChainView) (payload : SimulatePayload) (p : BlockParam)
    (choices : SimulateChoices) : Except RpcError (List SimulatedBlock) := do
  let plan ← v.planSimulate payload p choices
  let some i := v.canonical.findFinIdx? (·.hash == plan.base.hash)
    | throw (invalidInput.toRpcError (some (.str "base block not canonical")))
  let start : SimulateStep :=
    { chain := v.chainAt i i.2, budget := choices.gasCap
      number := plan.base.block.header.number, time := plan.base.block.header.timestamp.toNat
      blocks := [] }
  let s ← plan.blocks.foldlM
    (SimulateStep.next v.config plan.base.recent payload.validation choices.blockTime) start
  return s.blocks

/-! ## The call results -/

namespace SimulateCode

/-- The code of a call that fails for a reason other than a revert. -/
def callFailed : ErrorCode := ⟨-32015, "Execution error"⟩

end SimulateCode

/-- The error of a call that failed with `e`, with `output` the output of its message.

A revert has the code 3, with that output as its data.

Any other error has the code `-32015`, whose message the source leaves to the client. -/
def callResultError (e : Evm.EvmError) (output : ByteArray) : RpcError :=
  match e with
  | .revert => revertError output
  | _ => SimulateCode.callFailed.toRpcError

/-- The result of a call as JSON, from its result, its gas used and its logs. -/
def callResultJson (result : TransactionResult) (gasUsed : Nat) (logs : List LogInfo) : Json :=
  -- The gas before the refund is the `maxUsedGas` of the source.
  let common := [("logs", listJson logInfoJson logs), ("gasUsed", quantityJson gasUsed),
    ("maxUsedGas", quantityJson result.gasBeforeRefund)]
  -- The status follows the error, at every fork.
  match result.error with
  -- A call that succeeds has the status `0x1` and returns the output of its message.
  | none =>
    Json.mkObj ([("returnData", dataJson result.output.toList)] ++ common ++
      [("status", quantityJson 1)])
  -- A call that fails has the status `0x0`, no return data, no logs, and its error.
  | some e =>
    Json.mkObj ([("returnData", dataJson [])] ++ common ++
      [("status", quantityJson 0), ("error", rpcErrorJson (callResultError e result.output))])

/-- The logs that a call reports, from its receipt and its result.

With transfers traced, they are the logs that a simulation reports.

Without traced transfers, they are the logs of the receipt. -/
def callLogs {fork : Fork} (trace : Bool) (receipt : Receipt fork) (result : TransactionResult) :
    List Log :=
  -- Before Glamsterdam, traced transfers add a log from `0xee…ee` for each move of ether.
  --
  -- A move of 0 wei, or from an account to itself, adds none.
  if trace then result.simulatedLogs else receipt.logs

/-- The number of logs that the calls before `index` report, with transfers traced or not. -/
def SimulatedBlock.firstLog (b : SimulatedBlock) (trace : Bool) (index : Nat) : Nat :=
  (((b.record.receipts.zip b.results).take index).map fun (receipt, result) =>
    (callLogs trace receipt.2 result).length).sum

/-- The log objects that the call at `index` reports, with the hash `hash` of its transaction. -/
def SimulatedBlock.callLogInfos (b : SimulatedBlock) (trace : Bool) (index : Nat) (hash : Hash32)
    (receipt : Receipt b.record.fork) (result : TransactionResult) : List LogInfo :=
  b.record.logInfos index (b.firstLog trace index) hash (callLogs trace receipt result)

/-- The results of the calls of a simulated block as JSON, in order.

The logs of a call are numbered among all the logs that the calls of the block report.

With transfers traced, before Glamsterdam, each move of ether adds a log.

The body gives one result per receipt, so no call is left out. -/
def SimulatedBlock.callsJson (b : SimulatedBlock) (trace : Bool := false) :
    Except RpcError Json := do
  let r := b.record
  let calls := (r.block.transactions.zip (r.receipts.zip b.results)).zipIdx
  let items ← calls.mapM fun ((tx, (_, receipt), result), index) => do
    let hash ← (transactionHash tx).mapError fun _ => BlockRecord.encodingError "transaction hash"
    let logs := b.callLogInfos trace index hash receipt result
    return callResultJson result (receipt.cumulativeGasUsed - r.gasBefore index) logs
  return .arr items.toArray

/-- A simulated block as a block object, with the objects of its transactions when asked for.

Without validation, a call with a fee cap of 0 reports a gas price of 0, which it paid.

It also holds the results of its calls, with traced transfers when asked for. -/
def SimulatedBlock.json (b : SimulatedBlock) (full validation : Bool) (trace : Bool := false) :
    Except RpcError Json := do
  let r := b.record
  let size ← r.size
  let transactions ← if full then
      listJson transactionInfoJson <$> (r.block.transactions.zip b.senders).zipIdx.mapM
        fun ((tx, sender), index) => do
          let hash ← (transactionHash tx).mapError fun _ =>
            BlockRecord.encodingError "transaction hash"
          return { blockHash := r.hash, blockNumber := r.block.header.number
                   blockTimestamp := r.block.header.timestamp.toNat, index, sender, hash
                   gasPrice := effectiveGasPrice
                     (if !validation && tx.maxFeePerGas == 0 then 0 else r.baseFee) tx, tx }
    else listJson hash32Json <$> r.transactionHashes
  let calls ← b.callsJson trace
  return Json.mkObj (headerFields r.hash r.block.header ++
    blockFields size [] transactions r.block.withdrawals ++ [("calls", calls)])

/-- The answer of `eth_simulateV1`: the simulated blocks, gap blocks included. -/
def ChainView.simulate (v : ChainView) (payload : SimulatePayload) (p : BlockParam)
    (choices : SimulateChoices) : Except RpcError Json := do
  let blocks ← v.simulateBlocks payload p choices
  let full := payload.returnFullTransactions
  return .arr (← blocks.mapM (·.json full payload.validation payload.traceTransfers)).toArray

end EthLib.Execution.Rpc

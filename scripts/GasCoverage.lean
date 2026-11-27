module

import EvmGasCoverage
import EthLib.Execution.Exports.Transition

/-!
# Gas coverage of execution fixtures

The runner accepts one JSON request per line and counts gas rules during replay.

A block must pass the state transition and reproduce its roots in the observed run.
-/

namespace EthLib.Coverage

open Lean (FromJson Json toJson)
open EthLib.Base
open EthLib.Exports (Result forkUpTo toResult)
open EthLib.Execution
open EthLib.Execution.Blocks
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState stateRoot)
open EthLib.Execution.Transactions
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

abbrev Counts := Std.HashMap String Nat

def addRules (counts : Counts) (rules : Array String) : Counts :=
  rules.foldl (fun counts rule => counts.insert rule (counts.getD rule 0 + 1)) counts

/-- The transaction gas rules that a run can distinguish at `fork`. -/
def transactionGasInventory (fork : Fork) : Array String := Id.run do
  let mut rules := #["transaction.data.zero-byte", "transaction.data.nonzero-byte",
    "transaction.refund.none", "transaction.refund.below-cap", "transaction.refund.at-cap"]
  if fork ≥ .glamsterdam then
    rules := rules ++ #["transaction.base.creation", "transaction.base.self",
      "transaction.base.other-no-value", "transaction.base.other-value",
      "transaction.access-list.data"]
  else
    rules := rules.push "transaction.base.fixed"
    if fork ≥ .homestead then rules := rules.push "transaction.creation.base"
  if fork ≥ .shapella then rules := rules.push "transaction.creation.initcode"
  if fork ≥ .berlin then
    rules := rules ++ #["transaction.access-list.address", "transaction.access-list.storage-key"]
  if fork ≥ .pectra then
    rules := rules ++ #["transaction.authorizations", "transaction.calldata-floor.at-floor",
      "transaction.calldata-floor.above-floor"]
  return rules

/-- Record the intrinsic gas terms and the outcomes that settlement exposes. -/
def transactionGasRules (fork : Fork) (included : Included) (tx : Transaction)
    (output : TransactionOutput) : Array String := Id.run do
  let mut rules := if fork < .glamsterdam then #["transaction.base.fixed"]
    else #[match tx.to with
      | none => "transaction.base.creation"
      | some to => if to = included.sender then "transaction.base.self"
        else if tx.value = 0 then "transaction.base.other-no-value"
        else "transaction.base.other-value"]
  let zeros := zeroBytes tx.data
  if zeros > 0 then rules := rules.push "transaction.data.zero-byte"
  if zeros < tx.data.size then rules := rules.push "transaction.data.nonzero-byte"
  if tx.to.isNone then
    if .homestead ≤ fork ∧ fork < .glamsterdam then
      rules := rules.push "transaction.creation.base"
    if .shapella ≤ fork ∧ tx.data.size > 0 then
      rules := rules.push "transaction.creation.initcode"
  if fork ≥ .berlin && !tx.accesses.isEmpty then
    rules := rules.push "transaction.access-list.address"
    if tx.accesses.any (fun access => !access.slots.isEmpty) then
      rules := rules.push "transaction.access-list.storage-key"
    if fork ≥ .glamsterdam then rules := rules.push "transaction.access-list.data"
  if fork ≥ .pectra && !tx.authorizations.isEmpty then
    rules := rules.push "transaction.authorizations"
  if fork ≥ .pectra then
    -- At the floor of EIP-7623, the settled gas can hide a refund.
    if output.gasUsed = calldataFloor fork included.sender tx then
      return rules.push "transaction.calldata-floor.at-floor"
    rules := rules.push "transaction.calldata-floor.above-floor"
  let refund := output.gasBeforeRefund - output.gasUsed
  return rules.push <| if refund = 0 then "transaction.refund.none"
    else if refund = output.gasBeforeRefund / maxRefundQuotient fork then
      "transaction.refund.at-cap"
    else "transaction.refund.below-cap"

def observeStep {fork : Fork} {Meter : Type} [GasMeter Meter] :
    StepObserver (StateT Counts (Except EvmError)) fork Meter :=
  fun evm result => do
    if let .ok step := result then
      unless evm.code.isEmpty do modify (addRules · (stepGasRules evm step))

/-- Run a transaction with a counter as its step observer. -/
def observeTransaction {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) (counts : Counts := {}) :
    Except EvmError (TransactionOutput × Counts) := do
  let (output, counts) ← (processTransactionWith observeStep env block included tx).run counts
  return (output, addRules counts (transactionGasRules fork included tx output))

/-- Count an accepted block's system call and join its writes into the body. -/
def observeSystemCall {fork : Fork} (env : BlockEnvironment fork) (target : Address)
    (data : ByteArray) (before : BodyState × Counts) :
    Except BlockError (BodyState × Counts) := do
  let (body, counts) := before
  let message := systemMessage env target data
  let state := Execution.State.TransactionState.ofBlock body.block
  let substate := systemSubstate env target
  let run := if fork ≥ .glamsterdam then
      processMessageCallWith (Meter := StateGasMeter) observeStep env.chainId.toNat
        message state substate
    else processMessageCallWith (Meter := Nat) observeStep env.chainId.toNat message state substate
  let (output, counts) ← (run.run counts).mapError .aborted
  let body ← (body.join output.state).mapError .state
  return (body, counts)

structure BodyReplay where
  body : BodyState
  counts : Counts
  blockGas : BlockGas := .zero
  cumulativeGasUsed : Nat := 0
  receiptsRev : List ByteArray := []

def observeBodyTransaction {fork : Fork} (env : BlockEnvironment fork) (before : BodyReplay)
    (entry : Transaction × Nat) : Except BlockError BodyReplay := do
  let (tx, index) := entry
  let included ← (checkInclusion env.chainId env before.blockGas (.ofBlock before.body.block)
    tx).mapError (.invalidTransaction index)
  let (output, counts) ←
    (observeTransaction env before.body.block included tx before.counts).mapError .aborted
  let body ← ((before.body.beginIndex (index + 1)).join output.state).mapError .state
  let cumulativeGasUsed := before.cumulativeGasUsed + output.gasUsed
  let outcome : Outcome fork ← if h : .byzantium ≤ fork then pure (.status h output.error.isNone)
    else .postState (Nat.lt_of_not_le h) <$>
      (stateRoot keccak256 body.block.applyChanges).mapError .trie
  let receipt ← (encodeReceipt tx.type (makeReceipt outcome cumulativeGasUsed output.logs.toList))
    |>.mapError (.trie ∘ .rlp)
  return {
    body
    counts
    blockGas := before.blockGas.add output.blockGas
    cumulativeGasUsed
    receiptsRev := receipt :: before.receiptsRev }

/-- Observe an accepted block and check the state and receipt roots of the replay. -/
def observeBlock {fork : Fork} (chain : BlockChain) (block : Block fork Transaction) :
    Except BlockError (Counts × List ByteArray) := do
  let hashes ← recentHashes chain.recent
  let env := blockEnvironment chain.config hashes block.header
  let start ← daoTransfer chain.config fork block.header.number ⟨chain.state, ∅, ∅, ∅, ∅⟩
  let start := (BodyState.init start, ({} : Counts))
  let start ← if h : BEACON_ROOTS_CONTRACT.since ≤ fork then
      observeSystemCall env BEACON_ROOTS_CONTRACT.address
        ⟨(env.parentBeaconBlockRoot h).toArray⟩ start
    else pure start
  let (body, counts) ← if HISTORY_STORAGE_CONTRACT.since ≤ fork then
      observeSystemCall env HISTORY_STORAGE_CONTRACT.address ⟨block.header.parentHash.toArray⟩ start
    else pure start
  let replay ← block.transactions.zipIdx.foldlM (observeBodyTransaction env) { body, counts }
  let body := replay.body.beginIndex (block.transactions.length + 1)
  let body ← if h : .shapella ≤ fork then do
      let state ← (withdrawalState fork body.block (block.withdrawals h)).mapError .state
      (body.join state).mapError .state
    else pure body
  let (body, counts) ← (requestContracts fork).foldlM
    (fun before (_, target) => observeSystemCall env target .empty before) (body, replay.counts)
  let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
  let state ← onBlock body.block fun tx =>
    payRewards fork tx block.header.coinbase block.header.number ommers
  let root ← (stateRoot keccak256 state.applyChanges).mapError .trie
  unless root = block.header.stateRoot do throw (.wrongStateRoot block.header.stateRoot root)
  let receipts := replay.receiptsRev.reverse
  let receiptRoot ← (indexedRoot receipts).mapError .trie
  unless receiptRoot = block.header.receiptRoot do
    throw (.wrongReceiptRoot block.header.receiptRoot receiptRoot)
  return (counts, receipts)

def countsJson (counts : Counts) : Json :=
  Json.mkObj (counts.toList.map fun (rule, n) => (rule, toJson n))

def asResult {α : Type} (value : Except String α) : Result α :=
  value.mapError (0, ·)

def field {α : Type} [FromJson α] (request : Json) (name : String) : Result α :=
  asResult ((request.getObjValAs? α name).mapError fun error => s!"{name}: {error}")

def decodeHex (value : String) : Result ByteArray :=
  match hexBytes? value.toList with
  | some bytes => pure bytes
  | none => throw (0, "expected an even number of hex digits")

def fromHexField (request : Json) (name : String) : Result ByteArray :=
  field request name >>= decodeHex

def encodeHex (bytes : ByteArray) : Json :=
  toJson ((hexString bytes.data.toList).drop 2).toString

def stateRequest (request : Json) (forkName : String) : Result Json := do
  let chainId : Nat ← field request "chainId"
  let some chainId := Uint64.ofNat? chainId | throw (0, "chain ID is not below 2^64")
  let (fork, tx) ← Transactions.Exports.decodeAt .glamsterdam forkName.toUTF8
    (← fromHexField request "tx")
  let pre ← toResult none (Execution.State.Exports.ofInput (← fromHexField request "state"))
  let env ← toResult "block environment rejected"
    (decode (← fromHexField request "env") >>= Transactions.Exports.ofEnvironmentItem fork chainId)
  let block : BlockState := ⟨pre, ∅, ∅, ∅, ∅⟩
  let included ← toResult none (checkInclusion chainId env .zero (.ofBlock block) tx)
  let (output, counts) ← toResult none (observeTransaction env block included tx)
  let root ← toResult none
    ((stateRoot keccak256 output.block.applyChanges).mapError BlockError.trie)
  let logs ← toResult "logs" (encode (Codec.toItem output.logs.toList))
  let succeeded := output.error.isNone
  let receipt := makeReceipt (Outcome.make fork succeeded (fun _ => root))
    output.gasUsed output.logs.toList
  let receipt ← toResult "receipt" (encodeReceipt tx.type receipt)
  return Json.mkObj [("gasRules", countsJson counts), ("stateRoot", encodeHex ⟨root.toArray⟩),
    ("logsHash", encodeHex ⟨(keccak256 logs).toArray⟩), ("gasUsed", toJson output.gasUsed),
    ("succeeded", toJson succeeded), ("receipt", encodeHex receipt)]

def recentBlock (config : ChainConfig) (entry : Array Json) : Result RecentBlock := do
  let #[fork, header, ommers] := entry | throw (0, "expected a recent block with three entries")
  let fork ← asResult fork.getStr?
  let header ← decodeHex (← asResult header.getStr?)
  let ommers : List String ← asResult (Lean.fromJson? ommers)
  Blocks.Exports.recentOf config (fork, header, ← ommers.mapM decodeHex)

def blockRequest (request : Json) (forkName : String) : Result Json := do
  let config ← ChainConfig.Exports.configOfJson (← asResult (request.getObjVal? "config"))
  let pre ← toResult none (Execution.State.Exports.ofInput (← fromHexField request "state"))
  let recent : List (Array Json) ← field request "recent"
  let chain : BlockChain := ⟨config, pre, ← recent.mapM (recentBlock config)⟩
  let ⟨_, block⟩ ← Blocks.Exports.blockOf config forkName (← fromHexField request "block")
  let checkSeal : Bool ← field request "checkSeal"
  let post ← toResult none (stateTransition chain block checkSeal)
  let (counts, receipts) ← toResult "observed block" (observeBlock chain block)
  let accounts ← toResult none (Blocks.Exports.accountsItem post)
  let state ← toResult "accounts" (encode accounts)
  return Json.mkObj [("gasRules", countsJson counts), ("state", encodeHex state),
    ("receipts", Json.arr (receipts.toArray.map encodeHex))]

def request (value : Json) : Result Json := do
  let name : String ← field value "fork"
  match ← field value "kind" with
  | "inventory" =>
    let fork ← forkUpTo .glamsterdam name.toUTF8
    return Json.mkObj [("forkIndex", toJson fork.ctorIdx),
      ("gasRules", toJson (gasRuleInventory fork ++ transactionGasInventory fork))]
  | "state" => stateRequest value name
  | "block" => blockRequest value name
  | _ => throw (0, "unknown coverage request")

def response (line : String) : String :=
  let value := match asResult (Json.parse line) >>= request with
    | .ok result => result
    | .error (code, message) => Json.mkObj [("error", Json.mkObj [
        ("code", toJson code.toNat), ("message", toJson message)])]
  value.compress

end EthLib.Coverage

public def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (EthLib.Coverage.response line)
    stdout.flush

module

import EvmGasCoverage
import EthLib.Execution.Exports.Transition

/-!
# Gas coverage of execution fixtures

The runner accepts one JSON request per line and counts gas rules during replay.

A block must pass the state transition before the runner observes its body.
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

/-- The number of recorded occurrences of each gas rule. -/
abbrev Counts := Std.HashMap String Nat

/-- Add one occurrence for each label in the list. -/
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

/-- Record the gas rules of a completed opcode step. -/
def observeStep {fork : Fork} {Meter : Type} [GasMeter Meter] :
    StepObserver (StateT Counts (Except EvmError)) fork Meter :=
  fun evm result => do
    if let .ok step := result then
      unless evm.code.isEmpty do modify (addRules · (stepGasRules evm step))

/-- Run a transaction and count the gas rules that it uses. -/
def observeTransaction {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) :
    Except EvmError (TransactionOutput × Counts) := do
  let (output, counts) ← (processTransactionWith observeStep env block included tx).run {}
  return (output, addRules counts (transactionGasRules fork included tx output))

/-- Encode the counts as a JSON object keyed by gas-rule label. -/
def countsJson (counts : Counts) : Json :=
  Json.mkObj (counts.toList.map fun (rule, n) => (rule, toJson n))

/-- Give a request error code 0. -/
def asResult {α : Type} (value : Except String α) : Result α :=
  value.mapError (0, ·)

/-- Read a typed field from a JSON request. -/
def field {α : Type} [FromJson α] (request : Json) (name : String) : Result α :=
  asResult ((request.getObjValAs? α name).mapError fun error => s!"{name}: {error}")

/-- Read bytes from pairs of hexadecimal digits. -/
def decodeHex (value : String) : Result ByteArray :=
  match hexBytes? value.toList with
  | some bytes => pure bytes
  | none => throw (0, "expected an even number of hex digits")

/-- Read a request field that holds hexadecimal bytes. -/
def fromHexField (request : Json) (name : String) : Result ByteArray :=
  field request name >>= decodeHex

/-- Write bytes as a JSON string of hexadecimal digits. -/
def encodeHex (bytes : ByteArray) : Json :=
  toJson ((hexString bytes.data.toList).drop 2).toString

/-- Replay a state test and give its gas counts, state root and receipt data. -/
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

/-- Read a recent block from its fork name, encoded header and encoded ommers. -/
def recentBlock (config : ChainConfig) (entry : Array Json) : Result RecentBlock := do
  let #[fork, header, ommers] := entry | throw (0, "expected a recent block with three entries")
  let fork ← asResult fork.getStr?
  let header ← decodeHex (← asResult header.getStr?)
  let ommers : List String ← asResult (Lean.fromJson? ommers)
  Blocks.Exports.recentOf config (fork, header, ← ommers.mapM decodeHex)

/-- Check a block and give its post-state, gas counts and encoded receipts. -/
def blockRequest (request : Json) (forkName : String) : Result Json := do
  let config ← ChainConfig.Exports.configOfJson (← asResult (request.getObjVal? "config"))
  let pre ← toResult none (Execution.State.Exports.ofInput (← fromHexField request "state"))
  let recent : List (Array Json) ← field request "recent"
  let chain : BlockChain := ⟨config, pre, ← recent.mapM (recentBlock config)⟩
  let ⟨fork, block⟩ ← Blocks.Exports.blockOf config forkName (← fromHexField request "block")
  let checkSeal : Bool ← field request "checkSeal"
  -- The state transition checks the active fork and the roots before the observed run.
  let post ← toResult none (stateTransition chain block checkSeal)
  let hashes ← toResult none (recentHashes chain.recent)
  let env := blockEnvironment chain.config hashes block.header
  let observer : BodyObserver (StateT Counts (Except EvmError))
      (StateT Counts (Except BlockError)) fork :=
    BodyObserver.ofSteps observeStep
      (fun run counts => (run.run counts).mapError .aborted)
      (fun _ included tx output =>
        modify (addRules · (transactionGasRules fork included tx output)))
  let (output, counts) ← toResult "observed block"
    ((applyBodyWith observer chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩).run {})
  let receipts ← toResult "receipts" (output.receipts.mapM fun (type, receipt) =>
    encodeReceipt type receipt)
  let accounts ← toResult none (Blocks.Exports.accountsItem post)
  let state ← toResult "accounts" (encode accounts)
  return Json.mkObj [("gasRules", countsJson counts), ("state", encodeHex state),
    ("receipts", Json.arr (receipts.toArray.map encodeHex))]

/-- Serve one request for a gas inventory or a fixture replay. -/
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

/-- Encode the result of one JSON request on one line. -/
def response (line : String) : String :=
  let value := match asResult (Json.parse line) >>= request with
    | .ok result => result
    | .error (code, message) => Json.mkObj [("error", Json.mkObj [
        ("code", toJson code.toNat), ("message", toJson message)])]
  value.compress

end EthLib.Coverage

/-- Read requests from standard input and write responses to standard output. -/
public def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (EthLib.Coverage.response line)
    stdout.flush

module

public import EthLib.Base.Exports.Result
public import EthLib.Base.Hex
public import EthLib.Execution.Blocks.Validate

/-!
# `Exports.Errors`

The code and the message of the transaction, inclusion, EVM abort and block errors.

An error reaches Python with its code, and its message names the rule that failed.

The block, transaction, transition, JSON-RPC and Engine API exports reach them through imports.

So a block error has one code and one message in every export.
-/

public section

namespace EthLib.Execution.Transactions.Exports

open EthLib.Exports (ExportError oneLine)

open EthLib.Serialization.Rlp

/-- An RLP error, with the index of each structure field on the way to it. -/
def rlpMessage : RlpError → String
  | .inField index error => s!"field {index}: {rlpMessage error}"
  | error => (oneLine error).replace "EthLib.Serialization.Rlp.RlpError." ""

/-- A message for a rejection, phrased for someone reading a Python traceback. -/
def message : TransactionError → String
  | .decoding error => s!"decoding: {rlpMessage error}"
  | .encoding error => s!"encoding: {rlpMessage error}"
  | error => (oneLine error).replace "EthLib.Execution.Transactions.TransactionError." ""

/-- A rejection reaches Python with its code, and its message names the rule that failed. -/
instance : ExportError TransactionError where
  code := TransactionError.code
  message := message

/-- A message for a rejection by the block, phrased for a Python traceback. -/
def inclusionMessage : InclusionError → String
  | .transaction e => message e
  | error => (oneLine error).replace "EthLib.Execution.Transactions.InclusionError." ""

/-- A rejection by the block reaches Python with its code, and its message names the rule. -/
instance : ExportError InclusionError where
  code := InclusionError.code
  message := inclusionMessage

/-- A message for an error that aborts a run, phrased for a Python traceback. -/
def abortMessage (error : Evm.EvmError) : String :=
  s!"the run aborted: {(oneLine error).replace "EthLib.Execution.Evm.EvmError." ""}"

/-- An error that aborts a run reaches Python with a code and its message.

An error of the state keeps its own code.

Any other abort has code 0, since no error type of the specification gives it a code. -/
instance : ExportError Evm.EvmError where
  code
    | .state s => s.code
    | _ => 0
  message := abortMessage

end EthLib.Execution.Transactions.Exports

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (ExportError oneLine)
open EthLib.Base (hexString)
open EthLib.Execution.Transactions.Exports (abortMessage inclusionMessage message)

/-- A message for a block error, phrased for a Python traceback. -/
def blockErrorMessage : BlockError → String
  | .invalidTransaction index e => s!"transaction {index} rejected: {inclusionMessage e}"
  | .undecodableTransaction index e => s!"transaction {index} does not decode: {message e}"
  | .aborted e => abortMessage e
  | .systemCallFailed address e => s!"system call to {hexString address.toList} failed: {oneLine e}"
  | e => s!"block invalid: {(oneLine e).replace "EthLib.Execution.Blocks.BlockError." ""}"

/-- A block error reaches Python with its code, and its message names the rule that failed. -/
instance : ExportError BlockError where
  code := BlockError.code
  message := blockErrorMessage

end EthLib.Execution.Blocks.Exports

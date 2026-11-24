module

public import EthLib.Serialization.JsonRpc

/-!
# `Execution.Rpc.Errors`

The error codes of the execution JSON-RPC API.

Source: the [error groups][groups], at commit `1ca0818` of execution-apis.

They give each group, its codes with their messages, and its range.

[groups]: https://github.com/ethereum/execution-apis/tree/1ca0818569467cff85b7f41372f22e728d5daa14/src/error-groups
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Serialization.JsonRpc (RpcError)

/-- An error code with the message that its group gives it.

Only the code of an error is fixed: the official fixtures show messages other than these. -/
structure ErrorCode where
  /-- The code. -/
  code : Int
  /-- The message of the group. -/
  message : String
  deriving DecidableEq, Repr

/-- A group of error codes, with the range that it declares, if any.

Each group lists codes with a message, and four groups declare a range that holds their codes. -/
structure ErrorGroup where
  /-- The name of the group in the source. -/
  name : String
  /-- The least and the greatest code that the group may use. -/
  range : Option (Int × Int)
  /-- The codes of the group. -/
  errors : List ErrorCode
  deriving DecidableEq, Repr

/-- The code of a request that is not valid JSON. -/
def parseError : ErrorCode := ⟨-32700, "Parse error"⟩

/-- The code of a request whose method the node does not serve. -/
def methodNotFound : ErrorCode := ⟨-32601, "Method not found"⟩

/-- The code of a failure of the node, such as a transaction whose sender it cannot recover. -/
def internalError : ErrorCode := ⟨-32603, "Internal error"⟩

/-- The codes of JSON-RPC 2.0 itself. -/
def rpcStandardErrors : ErrorGroup where
  name := "JSONRPCStandardErrors"
  -- The file declares no range, and the README of the groups gives `-32768` to `-32000`.
  range := none
  errors := [parseError, ⟨-32600, "Invalid request"⟩, methodNotFound,
    ⟨-32602, "Invalid params"⟩, internalError]

/-- The code of an input that the method rejects, such as a block that is not canonical. -/
def invalidInput : ErrorCode := ⟨-32000, "Invalid input"⟩

/-- The code of a resource that the node does not find, such as an unknown block.

Some methods list this code beside those of their groups, and it is already in this group. -/
def resourceNotFound : ErrorCode := ⟨-32001, "Resource not found"⟩

/-- The code of a transaction that the node rejects for a reason that no other code names. -/
def transactionRejected : ErrorCode := ⟨-32003, "Transaction rejected"⟩

/-- The code of a method that the node does not support, or not for the request's state. -/
def methodNotSupported : ErrorCode := ⟨-32004, "Method not supported"⟩

/-- The codes that JSON-RPC 2.0 leaves to servers, as the execution API uses them. -/
def rpcNonStandardErrors : ErrorGroup where
  name := "JSONRPCNonStandardErrors"
  -- The file declares no range, and the README of the groups gives `-32099` to `-32000`.
  range := none
  errors := [invalidInput, resourceNotFound,
    ⟨-32002, "Resource unavailable"⟩, transactionRejected,
    methodNotSupported, ⟨-32005, "Limit exceeded"⟩,
    ⟨-32006, "JSON-RPC version not supported"⟩]

/-- The code of a nonce below that of the sender. -/
def nonceTooLow : ErrorCode := ⟨1, "Nonce too low"⟩

/-- The code of a nonce above that of the sender. -/
def nonceTooHigh : ErrorCode := ⟨2, "Nonce too high"⟩

/-- The code of an execution that ends with REVERT. -/
def executionReverted : ErrorCode := ⟨3, "Execution reverted"⟩

/-- The code of an execution that meets an invalid opcode. -/
def invalidOpcode : ErrorCode := ⟨4, "Invalid opcode"⟩

/-- The codes of a failed execution. -/
def executionErrors : ErrorGroup where
  name := "ExecutionErrors"
  range := some (1, 199)
  errors := [nonceTooLow, nonceTooHigh, executionReverted, invalidOpcode]

/-- The code of a gas limit below the intrinsic gas of its transaction. -/
def intrinsicGasTooLow : ErrorCode :=
  ⟨800, "Intrinsic gas too low / Intrinsic gas exceeds gas limit"⟩

/-- The code of an execution that runs out of gas. -/
def ranOutOfGas : ErrorCode := ⟨801, "Transaction ran out of gas"⟩

/-- The code of a gas limit of a transaction above the gas limit of its block. -/
def gasLimitAboveBlock : ErrorCode := ⟨803, "Tx gas limit exceeds max block gas limit"⟩

/-- The code of a priority fee above the fee cap. -/
def priorityFeeAboveCap : ErrorCode := ⟨804, "Max priority fee per gas higher than max fee per gas"⟩

/-- The code of a fee cap below the base fee of the block. -/
def feeCapBelowBaseFee : ErrorCode := ⟨806, "Max fee per gas less than block base fee"⟩

/-- The code of a sender whose balance does not cover the fee and the value. -/
def insufficientFunds : ErrorCode := ⟨809, "Insufficient funds for gas * price + value"⟩

/-- The codes of gas and fee faults. -/
def gasErrors : ErrorGroup where
  name := "GasErrors"
  range := some (800, 999)
  errors := [intrinsicGasTooLow, ranOutOfGas,
    ⟨802, "Gas price too low / Gas price below configured minimum"⟩,
    gasLimitAboveBlock, priorityFeeAboveCap,
    ⟨805, "Gas uint64 overflow"⟩, feeCapBelowBaseFee,
    ⟨807, "Max priority fee per gas higher than 2^256-1"⟩,
    ⟨808, "Max fee per gas higher than 2^256-1"⟩, insufficientFunds]

/-- The code of a transaction whose signature names no sender. -/
def invalidSender : ErrorCode := ⟨1001, "Invalid sender"⟩

/-- The codes of the transaction pool. -/
def txPoolErrors : ErrorGroup where
  name := "TxPoolErrors"
  range := some (1000, 1199)
  errors := [⟨1000, "Already known transaction"⟩, invalidSender]

/-- The codes of execution in a zero-knowledge prover. -/
def zkExecutionErrors : ErrorGroup where
  name := "ZkExecutionErrors"
  range := some (2000, 2199)
  errors := [⟨2000, "Out of counters"⟩]

/-- Every group of the source. -/
def errorGroups : List ErrorGroup :=
  [rpcStandardErrors, rpcNonStandardErrors, executionErrors, gasErrors, txPoolErrors,
    zkExecutionErrors]

/-- The code of history that the node pruned.

Many methods that read blocks, transactions, receipts, logs or traces list it.

No group holds it: the methods list it beside the codes of the groups. -/
def prunedHistoryUnavailable : ErrorCode := ⟨4444, "Pruned history unavailable"⟩

/-- The error object of a code, with its message and the given data. -/
def ErrorCode.toRpcError (e : ErrorCode) (data : Option Lean.Json := none) : RpcError :=
  { code := e.code, message := e.message, data }

end EthLib.Execution.Rpc

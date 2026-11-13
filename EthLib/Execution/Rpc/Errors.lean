module

public import EthLib.Serialization.JsonRpc

/-!
# `Execution.Rpc.Errors`

The error codes of the execution JSON-RPC API, in the groups of its [error groups][groups].

Each group lists codes with a message, and four groups declare a range that holds their codes.

The two groups of JSON-RPC itself declare no range in their files.

The README of the groups gives them `-32768` to `-32000` and `-32099` to `-32000`.

Some methods list two more codes: `4444` for history that the node pruned, and `-32001`.

The code `-32001` is already in the group of non-standard errors.

Only the code of an error is fixed: the official fixtures show messages other than these.

[groups]: https://github.com/ethereum/execution-apis/tree/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/error-groups
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Serialization.JsonRpc (RpcError)

/-- An error code with the message that its group gives it. -/
structure ErrorCode where
  /-- The code. -/
  code : Int
  /-- The message of the group. -/
  message : String
  deriving DecidableEq, Repr

/-- A group of error codes, with the range that it declares, if any. -/
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
  range := none
  errors := [parseError, ⟨-32600, "Invalid request"⟩, methodNotFound,
    ⟨-32602, "Invalid params"⟩, internalError]

/-- The code of an input that the method rejects, such as a block that is not canonical. -/
def invalidInput : ErrorCode := ⟨-32000, "Invalid input"⟩

/-- The code of a resource that the node does not find, such as an unknown block. -/
def resourceNotFound : ErrorCode := ⟨-32001, "Resource not found"⟩

/-- The code of a transaction that the node rejects for a reason that no other code names. -/
def transactionRejected : ErrorCode := ⟨-32003, "Transaction rejected"⟩

/-- The code of a method that the node does not support, or not for the request's state. -/
def methodNotSupported : ErrorCode := ⟨-32004, "Method not supported"⟩

/-- The codes that JSON-RPC 2.0 leaves to servers, as the execution API uses them. -/
def rpcNonStandardErrors : ErrorGroup where
  name := "JSONRPCNonStandardErrors"
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

Many methods that read blocks, transactions, receipts, logs or traces list it. -/
def prunedHistoryUnavailable : ErrorCode := ⟨4444, "Pruned history unavailable"⟩

/-- The error object of a code, with its message and the given data. -/
def ErrorCode.toRpcError (e : ErrorCode) (data : Option Lean.Json := none) : RpcError :=
  { code := e.code, message := e.message, data }

end EthLib.Execution.Rpc

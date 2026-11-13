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

/-- The codes of JSON-RPC 2.0 itself. -/
def rpcStandardErrors : ErrorGroup where
  name := "JSONRPCStandardErrors"
  range := none
  errors := [⟨-32700, "Parse error"⟩, ⟨-32600, "Invalid request"⟩, ⟨-32601, "Method not found"⟩,
    ⟨-32602, "Invalid params"⟩, ⟨-32603, "Internal error"⟩]

/-- The codes that JSON-RPC 2.0 leaves to servers, as the execution API uses them. -/
def rpcNonStandardErrors : ErrorGroup where
  name := "JSONRPCNonStandardErrors"
  range := none
  errors := [⟨-32000, "Invalid input"⟩, ⟨-32001, "Resource not found"⟩,
    ⟨-32002, "Resource unavailable"⟩, ⟨-32003, "Transaction rejected"⟩,
    ⟨-32004, "Method not supported"⟩, ⟨-32005, "Limit exceeded"⟩,
    ⟨-32006, "JSON-RPC version not supported"⟩]

/-- The codes of a failed execution. -/
def executionErrors : ErrorGroup where
  name := "ExecutionErrors"
  range := some (1, 199)
  errors := [⟨1, "Nonce too low"⟩, ⟨2, "Nonce too high"⟩, ⟨3, "Execution reverted"⟩,
    ⟨4, "Invalid opcode"⟩]

/-- The codes of gas and fee faults. -/
def gasErrors : ErrorGroup where
  name := "GasErrors"
  range := some (800, 999)
  errors := [⟨800, "Intrinsic gas too low / Intrinsic gas exceeds gas limit"⟩,
    ⟨801, "Transaction ran out of gas"⟩,
    ⟨802, "Gas price too low / Gas price below configured minimum"⟩,
    ⟨803, "Tx gas limit exceeds max block gas limit"⟩,
    ⟨804, "Max priority fee per gas higher than max fee per gas"⟩,
    ⟨805, "Gas uint64 overflow"⟩, ⟨806, "Max fee per gas less than block base fee"⟩,
    ⟨807, "Max priority fee per gas higher than 2^256-1"⟩,
    ⟨808, "Max fee per gas higher than 2^256-1"⟩,
    ⟨809, "Insufficient funds for gas * price + value"⟩]

/-- The codes of the transaction pool. -/
def txPoolErrors : ErrorGroup where
  name := "TxPoolErrors"
  range := some (1000, 1199)
  errors := [⟨1000, "Already known transaction"⟩, ⟨1001, "Invalid sender"⟩]

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

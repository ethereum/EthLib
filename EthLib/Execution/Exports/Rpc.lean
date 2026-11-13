module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Execution.Rpc.BlockParam
public import EthLib.Execution.Rpc.Errors

/-!
# `Exports.Rpc`

The C exports of the parameter readers of the execution JSON-RPC API, and of its error codes.

A parameter crosses as the typed value of its JSON, with the name of its schema.

The names are those of [`base-types.yaml`][types] and [`block.yaml`][block].

A number reads as an `int`, and a byte string, an address or a hash as `bytes`.

A storage slot of type `bytesMax32` reads as its 32 bytes.

A block parameter reads as a tuple: its kind, then its number, its tag, or its hash and flag.

A value that its schema rejects has the code of invalid parameters, without its sign.

An unknown schema, or an argument that Lean cannot read, has code 0.

An error code may be negative, but a Python `int` crosses only when it is not.

So a code crosses as a pair: whether it is negative, then its absolute value.

[types]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/base-types.yaml
[block]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue ToPy toPy pyExport)
open EthLib.Serialization.JsonRpc (Read RpcError address bytes uint uint64)

derive_py BlockTag
derive_py_laws BlockTag
derive_py BlockParam
derive_py_laws BlockParam

/-- An error code crosses as whether it is negative, then its absolute value. -/
local instance : ToPy Int := ⟨fun i => toPy (decide (i < 0), i.natAbs)⟩

/-- A reading as a Python value.

A rejection has the code of invalid parameters, without its sign, and the reason as message. -/
def readingOf {α : Type} [ToPy α] : Read α → Result PyValue
  | .ok a => .ok (toPy a)
  | .error reason => .error ((RpcError.invalidParams reason).code.natAbs.toUInt32, reason)

/-- The value of a parameter under the schema of the given name, or why the schema rejects it. -/
def readParamOf (args : String × PyValue) : Result PyValue :=
  let (schema, value) := args
  let j := value.toJson
  match schema with
  | "byte" => readingOf (byte schema j)
  | "uint" => readingOf (uint schema j)
  | "uint32" => readingOf (uint32 schema j)
  | "uint64" => readingOf (uint64 schema j)
  | "uint256" => readingOf (uint256 schema j)
  | "uintDecimal" => readingOf (uintDecimal schema j)
  | "bytes" => readingOf (bytes schema j)
  | "bytesMax32" => readingOf (bytesMax32 schema j)
  | "bytes4" => readingOf (bytes4 schema j)
  | "bytes8" => readingOf (bytes8 schema j)
  | "bytes16" => readingOf (bytes16 schema j)
  | "bytes32" => readingOf (bytes32 schema j)
  | "bytes48" => readingOf (bytes48 schema j)
  | "bytes65" => readingOf (bytes65 schema j)
  | "bytes96" => readingOf (bytes96 schema j)
  | "bytes256" => readingOf (bytes256 schema j)
  | "hash32" => readingOf (hash32 schema j)
  | "address" => readingOf (address schema j)
  | "BlockNumberOrTag" => readingOf (blockNumberOrTag schema j)
  | "BlockNumberOrTagForRange" => readingOf (blockNumberOrTagForRange schema j)
  | "BlockNumberOrTagOrHash" => readingOf (blockNumberOrTagOrHash schema j)
  | _ => .error (0, s!"unknown schema: {schema}")

/-- Read a parameter of the execution JSON-RPC API under the schema of the given name.

The arguments are the name of a base type or a block schema, and the JSON value of the parameter.

A number is an `int`, and a byte string, an address, a hash or a storage slot is `bytes`.

A block parameter is a tuple of its kind and its number, its tag, or its hash and flag.

A value that the schema rejects has code 32602, the code of invalid parameters without its sign.

An unknown schema has code 0. -/
@[export eth_rpc_read_param]
def readParamExport (args : PyValue) : Result PyValue :=
  pyExport readParamOf args

/-- The groups of error codes of the execution JSON-RPC API, in the order of the source.

Each group is its name, its range if it declares one, and its codes, each with its message.

Each code and each bound is a pair: whether it is negative, then its absolute value. -/
@[export eth_rpc_error_groups]
def errorGroupsExport : PyValue → Result PyValue
  | .tuple #[] => .ok (toPy (errorGroups.map fun g =>
    (g.name, g.range, g.errors.map fun e => (e.code, e.message))))
  | _ => .error (0, "expected no argument")

/-- The code of history that the node pruned, with its message.

The code is a pair: whether it is negative, then its absolute value. -/
@[export eth_rpc_pruned_history_unavailable]
def prunedHistoryUnavailableExport : PyValue → Result PyValue
  | .tuple #[] => .ok (toPy (prunedHistoryUnavailable.code, prunedHistoryUnavailable.message))
  | _ => .error (0, "expected no argument")

end EthLib.Execution.Rpc.Exports

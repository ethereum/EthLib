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

A number or a `byte` reads as an `int`, and a byte string, an address or a hash as `bytes`.

A `bytes` value has an even number of digits, though the pattern of the source admits an odd one.

A value that holds Python `bytes` at any depth has no JSON form, so every schema rejects it.

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
open EthLib.Serialization.JsonRpc (Read RpcError address bytes reject uint uint64)

derive_py BlockTag
derive_py_laws BlockTag
derive_py BlockParam
derive_py_laws BlockParam

/-- An error code crosses as whether it is negative, then its absolute value. -/
local instance : ToPy Int := ⟨fun i => toPy (decide (i < 0), i.natAbs)⟩

mutual

/-- Whether a value holds Python `bytes` at any depth, which have no JSON form. -/
def containsBytes : PyValue → Bool
  | .bytes _ => true
  | .list ⟨items⟩ | .tuple ⟨items⟩ => containsBytesList items
  | .dict ⟨entries⟩ => containsBytesEntries entries
  | _ => false
termination_by structural v => v

/-- Whether one of some values holds Python `bytes` at any depth. -/
def containsBytesList : List PyValue → Bool
  | [] => false
  | v :: vs => containsBytes v || containsBytesList vs

/-- Whether the value of one of some entries holds Python `bytes` at any depth. -/
def containsBytesEntries : List (String × PyValue) → Bool
  | [] => false
  | (_, v) :: rest => containsBytes v || containsBytesEntries rest

end

/-- A value read by a reader of a schema, as a Python value.

A value that holds Python `bytes` is no JSON value, so the schema rejects it.

A rejection has the code of invalid parameters, without its sign, and the reason as message. -/
def readingOf {α : Type} [ToPy α] (schema : String) (value : PyValue)
    (reader : String → Json → Read α) : Result PyValue :=
  let reading :=
    if containsBytes value then reject s!"{schema}: not a JSON value"
    else reader schema value.toJson
  match reading with
  | .ok a => .ok (toPy a)
  | .error reason => .error ((RpcError.invalidParams reason).code.natAbs.toUInt32, reason)

/-- The value of a parameter under the schema of the given name, or why the schema rejects it. -/
def readParamOf (args : String × PyValue) : Result PyValue :=
  let (schema, value) := args
  match schema with
  | "byte" => readingOf schema value byte
  | "uint" => readingOf schema value uint
  | "uint32" => readingOf schema value uint32
  | "uint64" => readingOf schema value uint64
  | "uint256" => readingOf schema value uint256
  | "uintDecimal" => readingOf schema value uintDecimal
  | "bytes" => readingOf schema value bytes
  | "bytesMax32" => readingOf schema value bytesMax32
  | "bytes4" => readingOf schema value bytes4
  | "bytes8" => readingOf schema value bytes8
  | "bytes16" => readingOf schema value bytes16
  | "bytes32" => readingOf schema value bytes32
  | "bytes48" => readingOf schema value bytes48
  | "bytes65" => readingOf schema value bytes65
  | "bytes96" => readingOf schema value bytes96
  | "bytes256" => readingOf schema value bytes256
  | "hash32" => readingOf schema value hash32
  | "address" => readingOf schema value address
  | "BlockNumberOrTag" => readingOf schema value blockNumberOrTag
  | "BlockNumberOrTagForRange" => readingOf schema value blockNumberOrTagForRange
  | "BlockNumberOrTagOrHash" => readingOf schema value blockNumberOrTagOrHash
  | _ => .error (0, s!"unknown schema: {schema}")

/-- Read a parameter of the execution JSON-RPC API under the schema of the given name.

The arguments are the name of a base type or a block schema, and the JSON value of the parameter.

A number or a `byte` is an `int`, and a byte string, an address, a hash or a slot is `bytes`.

A `bytes` value has an even number of digits, though the pattern of the source admits an odd one.

A value that holds Python `bytes` at any depth has no JSON form, so every schema rejects it.

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

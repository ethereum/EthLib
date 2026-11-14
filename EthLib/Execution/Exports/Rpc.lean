module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Execution.Rpc.BlockParam
public import EthLib.Execution.Rpc.Errors
public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Rpc.Simulate
public import EthLib.Execution.Exports.Transition

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

A chain view crosses as the inputs that build it, and answers a list of requests at once.

Its blocks are the lowest block and the blocks after it, each with the name of its fork.

Each block after the lowest runs through the state transition, as a valid view asks.

A chain view reads the embedded KZG trusted setup, which the KZG exports decode once.

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

/-! ## The chain view -/

open EthLib.Base (ChainConfig Fork Hash32)
open EthLib.Execution.Blocks (Block BlockChain BlockError Log Receipt runBody stateTransition)
open EthLib.Execution.Blocks.Exports (blockErrorMessage blockOf)
open EthLib.Execution.State (stateRoot)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The record of a block, with its hash, from the state after it and the body that it ran. -/
def recordOf {fork : Fork} (block : Block fork Execution.Transactions.Transaction)
    (state : Execution.State.State) (receipts : List (UInt8 × Receipt fork))
    (logs : List Log) (accessList : Option Blocks.BlockAccessList := none) :
    Result BlockRecord := do
  let hash ← block.header.hash.mapError fun e => (0, s!"block hash: {reprStr e}")
  return ⟨fork, block, hash, state, receipts, logs, accessList⟩

/-- The record of a block after the last record of a chain, by the state transition. -/
def nextRecord (config : ChainConfig) (checkSeal : Bool) (records : List BlockRecord)
    (prev : BlockRecord) (block : String × ByteArray) : Result BlockRecord := do
  let ⟨_, block⟩ ← blockOf config block.1 block.2
  let chain : BlockChain := ⟨config, prev.state, records.map BlockRecord.recent⟩
  let failed := fun (e : BlockError) =>
    (e.code, s!"block {block.header.number}: {blockErrorMessage e}")
  let state ← (stateTransition chain block checkSeal).mapError failed
  let result ← (runBody chain block).mapError failed
  let accessList := result.output.accessListHash.map fun _ => result.output.body.builder.build
  recordOf block state result.output.receipts result.output.logs accessList

/-- The hash of thirty-two zero bytes, which a forkchoice state gives for no block. -/
def zeroHash : Hash32 := Vector.replicate 32 (0 : UInt8)

/-- The inputs of a chain view: the configuration, the state of the lowest block, and the blocks.

Then come the head, safe and finalized hashes, the network ID and whether to check the seal. -/
abbrev ViewInputs :=
  PyValue × ByteArray × List (String × ByteArray) × (Hash32 × Hash32 × Hash32) × Nat × Bool

/-- An optional numeric field of the chain configuration, below 2^64 as EIP-6122 requires. -/
def configNat (j : Json) (name : String) : Result (Option Nat) := do
  match j.getObjVal? name with
  | .error _ => return none
  | .ok value =>
    let some n := value.getNat?.toOption | throw (0, s!"config: {name} is not a number")
    unless n < 2 ^ 64 do throw (0, s!"config: {name} is not below 2^64")
    return some n

/-- Explicit genesis context for a pruned view, or none when neither field is given.

The hash and timestamp must be given together; a partial or malformed context is rejected. -/
def configGenesis (j : Json) : Result (Option (Hash32 × Nat)) := do
  let time ← configNat j "genesisTime"
  match j.getObjVal? "genesisHash", time with
  | .error _, none => return none
  | .ok hash, some time =>
    let hash ← (hash32 "genesisHash" hash).mapError fun reason => (0, reason)
    return some (hash, time)
  | _, _ => throw (0, "config: genesisHash and genesisTime must be given together")

/-- The chain view that its inputs build, or why they build none.

The lowest block is taken with its state, whose root must be the state root of its header.

It must be at the active fork of its header.

It must hold no transaction, since its receipts are not given.

Each block after it runs on the chain before it, without the history before the lowest block.

The head must be the last block, and a zero safe or finalized hash names no block.

When the lowest block is block zero, any given genesis hash and timestamp must match it. -/
def viewOf (inputs : ViewInputs) : Result ChainView := do
  let (config, state, blocks, (head, safeHash, finalizedHash), networkId, checkSeal) := inputs
  let configJson := config.toJson
  let genesis ← configGenesis configJson
  let mergeForkBlock ← configNat configJson "mergeForkBlock"
  let config ← ChainConfig.Exports.configOfJson configJson
  let setup ← Cryptography.Kzg.Exports.runKzg (Cryptography.Kzg.Exports.embeddedSetup ())
  let state ← (State.Exports.ofInput state).mapError fun e => (0, e.message)
  let (first, rest) ← match blocks with
    | [] => .error (0, "no block")
    | first :: rest => pure (first, rest)
  let ⟨fork, lowest⟩ ← blockOf config first.1 first.2
  unless config.activeFork lowest.header.number lowest.header.timestamp.toNat = some fork do
    .error (0, "the lowest block is not at its active fork")
  let root ← (stateRoot keccak256 state).mapError fun e => (0, s!"state root: {reprStr e}")
  unless root = lowest.header.stateRoot do
    .error (0, "the state is not the state of the lowest block")
  unless lowest.transactions.isEmpty do
    .error (0, "the lowest block has transactions, whose receipts are not given")
  let lowest ← recordOf lowest state [] []
  let genesis ← if lowest.block.header.number = 0 then do
      let actual := (lowest.hash, lowest.block.header.timestamp.toNat)
      match genesis with
      | some given =>
        unless given = actual do throw (0, "config: genesis context disagrees with block zero")
        pure (some actual)
      | none => pure (some actual)
    else pure genesis
  let records ← rest.foldlM (init := [lowest]) fun records block => do
    let prev := records.getLast?.getD lowest
    return records ++ [← nextRecord config checkSeal records prev block]
  if h : records = [] then .error (0, "no block")
  else
    unless (records.getLast h).hash = head do .error (0, "the head is not the last block")
    let named := fun (hash : Hash32) => if hash = zeroHash then none else some hash
    let view : ChainView := {
      config := config
      canonical := records
      nonempty := h
      safe := named safeHash
      finalized := named finalizedHash
      networkId := networkId
      genesis := genesis
      mergeForkBlock := mergeForkBlock
      setup := setup }
    return view

/-- The responses of the chain view that its inputs build, to the texts of requests, as text.

The access lists of the named block numbers are pruned first.

A notification, or a batch of notifications, gets none. -/
def serveOf (args : ViewInputs × List Nat × List String) : Result (List (Option String)) := do
  let view := (← viewOf args.1).pruneAccessLists args.2.1
  return args.2.2.map fun text => (view.serve (Json.parse text)).map (·.compress)

/-- Answer requests of the execution JSON-RPC API from the chain that the arguments build.

The arguments are the configuration, the state of the lowest block, and the blocks.

Each block is the name of its fork and its RLP form, the lowest block first.

Then come the head, safe and finalized hashes, the network ID, and whether to check the seal.

Next come the block numbers whose access lists are pruned, while their blocks remain available.

From Glamsterdam, the access-list methods report code 4444 for a pruned list.

The last argument is the list of the texts of the requests.

The configuration may give `mergeForkBlock`, the `FORK_NEXT_VALUE` of EIP-3675.

When the lowest block is not block zero, `eth_config` needs `genesisHash` and `genesisTime` there.

When it is block zero, both are read from it, and any given values must match.

It returns the text of the response to each request, in order, or none for a notification.

A block that does not decode or fails its transition has the code of its block error.

Any other bad input has code 0. -/
@[export eth_rpc_serve]
def serveExport (args : PyValue) : Result PyValue :=
  pyExport serveOf args

/-- Encode a JSON access list with the same reader and RLP codec as the query methods. -/
def encodeBlockAccessListOf (value : PyValue) : Result ByteArray := do
  let bal ← (if containsBytes value then reject "block access list: not a JSON value"
    else blockAccessListOfJson value.toJson).mapError fun reason =>
      ((RpcError.invalidParams reason).code.natAbs.toUInt32, reason)
  (Serialization.Rlp.Codec.encode bal).mapError fun _ =>
    (internalError.code.natAbs.toUInt32, "cannot encode block access list")

/-- Encode a block access-list JSON value as its EIP-7928 RLP bytes.

The argument is the JSON value returned by `eth_getBlockAccessList`.

The empty list encodes as `0xc0`.

The order of the list is not checked, so the bytes match a header hash only for a canonical order.

A value outside the JSON schema has code 32602, and an encoding failure has code 32603. -/
@[export eth_rpc_encode_block_access_list]
def encodeBlockAccessListExport (args : PyValue) : Result PyValue :=
  pyExport encodeBlockAccessListOf args

/-- The state root after the account overrides of a block, or why the inputs are rejected. -/
def applyOverridesOf (args : ByteArray × PyValue) : Result ByteArray := do
  let (input, value) := args
  let state ← (State.Exports.ofInput input).mapError fun e => (e.code, e.message)
  let overrides ← (if containsBytes value then reject "stateOverrides: not a JSON value"
    else stateOverrides value.toJson).mapError fun reason =>
      ((RpcError.invalidParams reason).code.natAbs.toUInt32, reason)
  State.Exports.rootOf (applyOverrides state overrides)

/-- The state root after the account overrides of one block of `eth_simulateV1`.

The arguments are a state in the form of the state root export, and the object `stateOverrides`.

The moves are not checked here, and a move changes no state.

A state that does not decode has the code of its state error.

An object outside the schema has code 32602, the code of invalid parameters without its sign. -/
@[export eth_rpc_apply_overrides]
def applyOverridesExport (args : PyValue) : Result PyValue :=
  pyExport applyOverridesOf args

end EthLib.Execution.Rpc.Exports

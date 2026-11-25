module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Base.Exports.PyValue
public import EthLib.Base.Json.Document
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Execution.Rpc.BlockParam
public import EthLib.Execution.Rpc.Errors
public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Rpc.Simulate
public import EthLib.Execution.Exports.Transition

/-!
# `Exports.Rpc`

The C exports of the execution JSON-RPC API: its parameter readers and its error codes.

A chain view, built from its blocks, answers a list of requests at once.

Sources, at commit `1ca0818` of execution-apis:

- [`base-types.yaml`][types]: the schema names of the base types
- [`block.yaml`][block]: the schema names of a block

[types]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/base-types.yaml
[block]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/block.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc.Exports

open Lean (Json)
open EthLib.Exports (ExportError Result PyValue ToPy UnreadArgument rejectArgument toPy pyExport
  toResult)
open EthLib.Serialization.JsonRpc (Read RpcError address bytes reject uint uint64)

derive_py BlockTag
derive_py_laws BlockTag
-- A block parameter reads as a tuple: its kind, then its number, its tag, or its hash and flag.
derive_py BlockParam
derive_py_laws BlockParam

/-- A JSON-RPC error reaches Python with its code without its sign.

Its message is its data when the data is a string, and its own message otherwise. -/
instance : ExportError RpcError where
  code e := e.code.natAbs.toUInt32
  message e := match e.data with
    | some (.str reason) => reason
    | _ => e.message

/-- An error code crosses as whether it is negative, then its absolute value.

An error code may be negative, but a Python `int` crosses only when it is not. -/
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

/-- A value read by a reader of a schema, as a Python value. -/
def readingOf {α : Type} [ToPy α] (schema : String) (value : PyValue)
    (reader : String → Json → Read α) : Result PyValue :=
  let reading :=
    -- A value that holds Python `bytes` at any depth has no JSON form, so every schema rejects it.
    if containsBytes value then reject s!"{schema}: not a JSON value"
    else reader schema value.toJson
  -- A rejection has the code of invalid parameters, without its sign, and the reason as message.
  toResult none ((reading.map toPy).mapError RpcError.invalidParams)

/-- The value of a parameter under the schema of the given name, or why the schema rejects it. -/
def readParamOf (args : String × PyValue) : Result PyValue :=
  let (schema, value) := args
  -- A parameter crosses as the typed value of its JSON, with the name of its schema.
  --
  -- A number or a `byte` reads as an `int`, and a byte string, an address or a hash as `bytes`.
  match schema with
  | "byte" => readingOf schema value byte
  | "uint" => readingOf schema value uint
  | "uint32" => readingOf schema value uint32
  | "uint64" => readingOf schema value uint64
  | "uint256" => readingOf schema value uint256
  | "uintDecimal" => readingOf schema value uintDecimal
  -- An even number of digits, though the pattern of the source admits an odd one.
  | "bytes" => readingOf schema value bytes
  -- A storage slot reads as its 32 bytes.
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
  -- An unknown schema has code 0.
  | _ => rejectArgument none s!"unknown schema: {schema}"

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
  | _ => rejectArgument none "expected no argument"

/-- The code of history that the node pruned, with its message.

The code is a pair: whether it is negative, then its absolute value. -/
@[export eth_rpc_pruned_history_unavailable]
def prunedHistoryUnavailableExport : PyValue → Result PyValue
  | .tuple #[] => .ok (toPy (prunedHistoryUnavailable.code, prunedHistoryUnavailable.message))
  | _ => rejectArgument none "expected no argument"

/-! ## The chain view -/

open EthLib.Base (ChainConfig Fork Hash32)
open EthLib.Execution.Blocks (Block BlockChain BlockError Log Receipt RecentBlock stateTransition)
open EthLib.Execution.Blocks.Exports (blockOf)
open EthLib.Execution.State (stateRoot)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The record of a block, with its hash, from the state after it and the body that it ran. -/
def recordOf {fork : Fork} (block : Block fork Execution.Transactions.Transaction)
    (state : Execution.State.State) (receipts : List (UInt8 × Receipt fork))
    (logs : List Log) (accessList : Option Blocks.BlockAccessList := none) :
    Result BlockRecord := do
  let hash ← toResult none
    (block.header.hash.mapError fun e => UnreadArgument.mk s!"block hash: {reprStr e}")
  return ⟨fork, block, hash, state, receipts, logs, accessList⟩

/-- The record of a block after the last record of a chain, by the state transition.

The recent blocks are those of the records so far, oldest first. -/
def nextRecord (config : ChainConfig) (checkSeal : Bool) (recent : Array RecentBlock)
    (prev : BlockRecord) (block : String × ByteArray) : Result BlockRecord := do
  let ⟨fork, block⟩ ← blockOf config block.1 block.2
  -- From Paris, the transition reads only the last 255 recent blocks, so the chain keeps those.
  --
  -- Before Paris, the ommer checks read every recent block, so the chain keeps them all.
  let recent := if .paris ≤ fork then (recent.extract (recent.size - 255) recent.size).toList
    else recent.toList
  let chain : BlockChain := ⟨config, prev.state, recent⟩
  let state ← toResult s!"block {block.header.number}" (stateTransition chain block checkSeal)
  let hash ← toResult none
    (block.header.hash.mapError fun e => UnreadArgument.mk s!"block hash: {reprStr e}")
  toResult s!"block {block.header.number}" (BlockRecord.ofRun chain block hash state)

/-- The records of the lowest block and of the blocks after it.

Each block runs on the chain of the records before it. -/
def recordsOf (config : ChainConfig) (checkSeal : Bool) (lowest : BlockRecord)
    (rest : List (String × ByteArray)) : Result (List BlockRecord) := do
  -- The records and their recent blocks grow in place, one block at a time.
  let (records, _) ← rest.foldlM (init := (#[lowest], #[lowest.recent]))
    fun (records, recent) block => do
      let record ← nextRecord config checkSeal recent (records.back?.getD lowest) block
      return (records.push record, recent.push record.recent)
  return records.toList

/-- The inputs of a chain view: the configuration, the state of the lowest block, and the blocks.

Each block is the name of its fork and its RLP form, the lowest block first.

Then come the head, safe and finalized hashes, the network ID and whether to check the seal. -/
abbrev ViewInputs :=
  PyValue × ByteArray × List (String × ByteArray) × (Hash32 × Hash32 × Hash32) × Nat × Bool

/-- An optional numeric field of the chain configuration, below 2^64 as EIP-6122 requires. -/
def configNat (j : Json) (name : String) : Result (Option Nat) := do
  match j.getObjVal? name with
  | .error _ => return none
  | .ok value =>
    let some n := value.getNat?.toOption | rejectArgument none s!"config: {name} is not a number"
    unless n < 2 ^ 64 do rejectArgument none s!"config: {name} is not below 2^64"
    return some n

/-- Explicit genesis context for a pruned view, or none when neither field is given. -/
def configGenesis (j : Json) : Result (Option (Hash32 × Nat)) := do
  let time ← configNat j "genesisTime"
  match j.getObjVal? "genesisHash", time with
  | .error _, none => return none
  | .ok hash, some time =>
    let hash ← toResult none ((hash32 "genesisHash" hash).mapError UnreadArgument.mk)
    return some (hash, time)
  -- The hash and timestamp must be given together; a partial or malformed context is rejected.
  | _, _ => rejectArgument none "config: genesisHash and genesisTime must be given together"

/-- The chain view that its inputs build, or why they build none. -/
def viewOf (inputs : ViewInputs) : Result ChainView := do
  let (config, state, blocks, (head, safeHash, finalizedHash), networkId, checkSeal) := inputs
  let configJson := config.toJson
  let genesis ← configGenesis configJson
  -- The configuration may give `mergeForkBlock`, the `FORK_NEXT_VALUE` of EIP-3675.
  let mergeForkBlock ← configNat configJson "mergeForkBlock"
  let config ← ChainConfig.Exports.configOfJson configJson
  -- The embedded KZG trusted setup, which the KZG exports decode once.
  let setup ← toResult none (Cryptography.Kzg.Exports.embeddedSetup ())
  let state ← toResult none
    ((State.Exports.ofInput state).mapError fun e => UnreadArgument.mk e.message)
  let (first, rest) ← match blocks with
    | [] => rejectArgument none "no block"
    | first :: rest => pure (first, rest)
  let ⟨fork, lowest⟩ ← blockOf config first.1 first.2
  -- The lowest block must be at the active fork of its header.
  unless config.activeFork lowest.header.number lowest.header.timestamp.toNat = some fork do
    rejectArgument none "the lowest block is not at its active fork"
  -- It is taken with its state, whose root must be the state root of its header.
  let root ← toResult none
    ((stateRoot keccak256 state).mapError fun e => UnreadArgument.mk s!"state root: {reprStr e}")
  unless root = lowest.header.stateRoot do
    rejectArgument none "the state is not the state of the lowest block"
  -- It must hold no transaction, since its receipts are not given.
  unless lowest.transactions.isEmpty do
    rejectArgument none "the lowest block has transactions, whose receipts are not given"
  let lowest ← recordOf lowest state [] []
  -- When the lowest block is block zero, the genesis context is read from it.
  --
  -- Any given genesis hash and timestamp must then match it.
  --
  -- Otherwise the configuration must give both, for the method that reports the fork schedule.
  let genesis ← match lowest.genesis with
    | some actual => do
      if let some given := genesis then
        unless given = actual do
          rejectArgument none "config: genesis context disagrees with block zero"
      pure (some actual)
    | none => pure genesis
  -- Each block after it runs through the state transition, as a valid view asks.
  --
  -- It runs on the chain before it.
  --
  -- The history before the lowest block is not there.
  let records ← recordsOf config checkSeal lowest rest
  if h : records = [] then rejectArgument none "no block"
  else
    -- The head must be the last block.
    unless (records.getLast h).hash = head do rejectArgument none "the head is not the last block"
    -- A zero safe or finalized hash names no block.
    let view : ChainView := {
      config := config
      canonical := records
      nonempty := h
      safe := namedBlock safeHash
      finalized := namedBlock finalizedHash
      networkId := networkId
      genesis := genesis
      mergeForkBlock := mergeForkBlock
      setup := setup }
    return view

/-- The responses of the chain view that its inputs build, to the texts of requests, as text. -/
def serveOf (args : ViewInputs × List Nat × List String) : Result (List (Option String)) := do
  -- The access lists of the named block numbers are pruned, while their blocks remain available.
  --
  -- From Glamsterdam, the access-list methods report code 4444 for a pruned list.
  let view := (← viewOf args.1).pruneAccessLists args.2.1
  -- Each text is read by the total reader of RFC 8259.
  --
  -- A notification, or a batch of notifications, gets none.
  return args.2.2.map fun text => (view.serve (Base.Json.ofText text)).map (·.compress)

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
  let reading := if containsBytes value then reject "block access list: not a JSON value"
    else blockAccessListOfJson value.toJson
  let bal ← toResult none (reading.mapError RpcError.invalidParams)
  toResult none ((Serialization.Rlp.Codec.encode bal).mapError fun _ =>
    internalError.toRpcError (some (.str "cannot encode block access list")))

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
  let state ← toResult none (State.Exports.ofInput input)
  let reading := if containsBytes value then reject "stateOverrides: not a JSON value"
    else stateOverrides value.toJson
  let overrides ← toResult none (reading.mapError RpcError.invalidParams)
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

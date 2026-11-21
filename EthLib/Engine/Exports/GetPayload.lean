module

public import EthLib.Base.Exports.ChainConfig
public import EthLib.Cryptography.Exports.Kzg
public import EthLib.Engine.Capabilities
public import EthLib.Engine.Exports.PayloadBodies
public import EthLib.Engine.GetPayload
public import EthLib.Execution.Exports.Transition

/-!
# `Exports.GetPayload`

The C export of `engine_getPayloadV1` through `engine_getPayloadV6`.

The supplied store is a snapshot of completed builds, with no payload ID twice.

An entry holds an ID, a fork name, and the four results of the payload build export.

They are the block in RLP form, the accounts after it, the requests and the block value in wei.

Then come the network blob transactions, the override flag and the block access list.

Lean decodes the network transactions and joins their sidecars in order.

The method checks this bundle against the block, using the embedded trusted setup.

The configuration determines the fork at the block's number and timestamp.

A malformed store or method name has code 0.

A parameter or request error has code 32602, 38001 or 38005.

A second export reads a result of the method at a fork, and writes it back as JSON.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (ExportError Result PyValue UnreadArgument pyExport rejectArgument toResult)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Execution.Blocks (Block)
open EthLib.Execution.Transactions

/-- An ID, a fork, a block, accounts, requests, a value, network forms, an override and a list. -/
abbrev PayloadEntry := PayloadId × String × ByteArray × ByteArray × List ByteArray × Nat ×
  List ByteArray × Bool × Option ByteArray

/-- Decode one snapshot entry; the block access list must be given exactly from Glamsterdam. -/
def storedPayloadOf (entry : PayloadEntry) : Result (PayloadId × StoredPayload) := do
  let (id, forkName, block, accounts, requests, blockValue, sidecars, shouldOverrideBuilder,
    accessList) := entry
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  let items : Block fork Serialization.Rlp.Item ← toResult none
    ((Block.decode (fun _ => fork) block).mapError
      fun e => UnreadArgument.mk s!"store: block rejected: {reprStr e}")
  let transactions ← items.transactions.mapM fun item =>
    toResult none ((decodeBodyTransaction fork item).mapError fun e =>
      UnreadArgument.mk s!"store: transaction rejected: {reprStr e}")
  let state ← toResult none ((Execution.State.Exports.ofInput accounts).mapError
    fun e => UnreadArgument.mk s!"store: {e.message}")
  let blockAccessList ← storeField (f := .glamsterdam) (fork := fork) "block access list"
    accessList
  let network ← sidecars.mapM fun bytes =>
    toResult none ((decodeNetwork fork bytes).mapError fun e =>
      UnreadArgument.mk s!"store: network error {e.code}")
  let built : BuiltPayload fork :=
    { block := ⟨items.header, transactions, items.ommers, items.withdrawals⟩
      state, requests, blockValue, blockAccessList }
  return (id, { fork, built, bundle := .ofNetwork network, shouldOverrideBuilder })

/-- The version of an `engine_getPayloadV1` through `engine_getPayloadV6` method name. -/
def getPayloadVersion (method : String) : Option Nat := methodVersion "getPayload" method

/-- An error of the method reaches Python with a code and a message.

An error of the request has its code, and malformed data in the store has code 0. -/
instance : ExportError GetPayloadError where
  code
    | .engine e => e.code
    | _ => 0
  message
    | .engine e => s!"engine error: {ExportError.message e}"
    | .wrongFork stored active =>
      let active := match active with
        | some fork => fork.name
        | none => "no fork"
      s!"store: the fork {stored.name} is not the configured fork at the block, {active}"
    | .requests => "store: execution requests out of order, too short or before Pectra"
    | .blockValue value => s!"store: block value {value} is 2^256 or more"
    | .noPayload => "store: the block has no payload form"
    | .header e => s!"store: the payload does not give the block: error {e.code}"
    | .bundle e => s!"store: bundle error {e.code}"

/-- The answer to a get-payload request, from a snapshot of build processes. -/
def getPayloadOf (args : PyValue × List PayloadEntry × PyValue) : Result PyValue := do
  let (config, entries, request) := args
  let config ← configOfJson config.toJson
  let entries ← entries.mapM storedPayloadOf
  unless (entries.map (·.1)).Nodup do rejectArgument none "store: two entries with one payload ID"
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | rejectArgument none "request: no method"
  let some version := getPayloadVersion method | rejectArgument none s!"no method {method}"
  let id ← toResult "engine error" (getPayloadParams (request.getObjValD "params"))
  let setup ← toResult none ((Cryptography.Kzg.Exports.embeddedSetup ()).mapError
    fun e => UnreadArgument.mk s!"setup: {e.message}")
  let r ← toResult none (getPayload config setup (fun id => entries.lookup id) version id)
  return .ofJson (getPayloadResultJson (r.result version))

/-- The answer to an `engine_getPayload` request, from the configuration and a store snapshot.

The arguments are the chain configuration, the entries of the store and the request.

Each entry is the payload ID, the fork name and the four results of the payload build export.

Then come its network blob transactions, the override flag and the block access list or `None`. -/
@[export eth_engine_get_payload]
def getPayloadExport (args : PyValue) : Result PyValue := pyExport getPayloadOf args

/-- The result of the method that a name gives, read at a fork and written back as JSON. -/
def readGetPayloadResultOf (args : String × String × PyValue) : Result PyValue := do
  let (method, forkName, result) := args
  let some version := getPayloadVersion method | rejectArgument none s!"no method {method}"
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  let r ← toResult "engine error" (getPayloadResultOfJson version fork result.toJson)
  return .ofJson (getPayloadResultJson r)

/-- The result of an `engine_getPayload` method at a fork, read from its JSON and written back.

The arguments are the method name, the fork name and the result, as `json.loads` gives it.

A result that does not decode is an invalid parameter, with code 32602.

An unknown method name, or a fork after Glamsterdam, has code 0. -/
@[export eth_engine_read_get_payload_result]
def readGetPayloadResultExport (args : PyValue) : Result PyValue :=
  pyExport readGetPayloadResultOf args

end EthLib.Engine.Exports

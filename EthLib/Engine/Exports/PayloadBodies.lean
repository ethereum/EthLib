module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Engine.PayloadBodies

/-!
# `Exports.PayloadBodies`

The C export of `engine_getPayloadBodiesByHash` and `engine_getPayloadBodiesByRange`.

The store crosses as a list of entries, one per block, with no hash twice.

An entry holds the block hash, and its number if the block is canonical.

Then come the fork of the block, its transactions, its withdrawals and its block access list.

No two canonical entries share a number.

The node serves every entry by its hash.

The withdrawals are `None` exactly before Shapella.

Each withdrawal is a tuple of the index, the validator index, the address and the amount.

The block access list must be `None` before Glamsterdam, and is `None` from it when pruned.

The fork is at most Glamsterdam.

The number of the latest known block and the request limit cross beside the store.

A canonical entry must hold the latest known block, and the limit must be at least 32.

The request is a JSON-RPC request object, with its method and its parameters.

The result is the JSON answer, as a Python value.

A JSON-RPC error has the code of its Engine API error, without the sign: 32602 or 38004.

A malformed store, block number or limit has code 0.

So do a request without a method, an unknown method, and an argument that Lean cannot read.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Serialization.JsonRpc (dataJson listJson optionJson)
open EthLib.Execution.Rpc (withdrawalJson)

/-- A withdrawal as it crosses: the index, the validator index, the address and the amount. -/
abbrev WithdrawalEntry := UInt64 × UInt64 × Address × UInt64

/-- One block of the store: the hash, the canonical number, the fork, then the body's fields. -/
abbrev BodyEntry := Bytes32 × Option Nat × String × List ByteArray ×
  Option (List WithdrawalEntry) × Option ByteArray

/-- A field of a stored body, which must be given exactly when the block's fork has it. -/
def storeField {α : Type} {f fork : Fork} (what : String) (x : Option α) :
    Result (Since f fork α) :=
  (Json.since what x).mapError fun
    | .invalidParams reason => (0, s!"store: {reason}")
    | e => (0, s!"store: {reprStr e}")

/-- The hash, the canonical number and the stored body of an entry. -/
def storedOf (entry : BodyEntry) : Result (Bytes32 × Option Nat × StoredBody) := do
  let (hash, number, forkName, transactions, withdrawals, accessList) := entry
  -- The methods are specified up to Glamsterdam, the fork of their version 2.
  let fork ← EthLib.Exports.forkUpTo .glamsterdam forkName.toUTF8
  let withdrawals := withdrawals.map fun ws =>
    ws.map fun (index, validatorIndex, address, amount) =>
      ({ index, validatorIndex, address, amount } : Withdrawal)
  let withdrawals ← storeField (f := .shapella) (fork := fork) "withdrawals" withdrawals
  -- From Glamsterdam, `None` is a pruned list, so the field is always given there.
  let accessList ← storeField (f := .glamsterdam) (fork := fork) "block access list"
    (if .glamsterdam ≤ fork then some accessList else accessList.map some)
  return (hash, number, { fork, transactions, withdrawals, blockAccessList := accessList })

/-- The method of a name, as the version and whether it is by range. -/
def bodiesMethod (method : String) : Option (Nat × Bool) :=
  match method with
  | "engine_getPayloadBodiesByHashV1" => some (1, false)
  | "engine_getPayloadBodiesByHashV2" => some (2, false)
  | "engine_getPayloadBodiesByRangeV1" => some (1, true)
  | "engine_getPayloadBodiesByRangeV2" => some (2, true)
  | _ => none

/-- The JSON of a body of version 1. -/
def bodyV1Json (b : ExecutionPayloadBodyV1) : Json :=
  Json.mkObj [
    ("transactions", listJson (dataJson ·.toList) b.transactions),
    ("withdrawals", optionJson (listJson withdrawalJson) b.withdrawals)]

/-- The JSON of a body of version 2. -/
def bodyV2Json (b : ExecutionPayloadBodyV2) : Json :=
  (bodyV1Json b.toExecutionPayloadBodyV1).setObjVal! "blockAccessList"
    (optionJson (dataJson ·.toList) b.blockAccessList)

/-- The answer to a payload bodies request, from a store of bodies.

The arguments are the store's entries, the latest known block, the limit and the request. -/
def payloadBodiesOf (args : List BodyEntry × Nat × Nat × PyValue) : Result PyValue := do
  let (entries, latest, maxRequest, request) := args
  let entries ← entries.mapM storedOf
  -- A store holds each block once, and one canonical block at each number.
  unless (entries.map (·.1)).Nodup do throw (0, "store: two entries with one block hash")
  unless (entries.filterMap (·.2.1)).Nodup do throw (0, "store: two canonical entries at a number")
  let canonical (n : Nat) : Option StoredBody :=
    (entries.find? (·.2.1 == some n)).map (·.2.2)
  if missing : (canonical latest).isSome = false then
    throw (0, s!"store: no canonical entry at the latest known block {latest}")
  else
  if below : maxRequest < MIN_BODIES_REQUEST_LIMIT then
    throw (0, s!"store: a limit of {maxRequest}, below {MIN_BODIES_REQUEST_LIMIT}")
  else
  let store : BodyStore := {
    byHash := fun hash => (entries.find? (·.1 == hash)).map (·.2.2)
    canonical, latest, latest_held := Bool.not_eq_false _ ▸ missing
    maxRequest, le_maxRequest := Nat.not_lt.1 below }
  let request := request.toJson
  let some method := (request.getObjValAs? String "method").toOption
    | throw (0, "request: no method")
  let some (version, byRange) := bodiesMethod method | throw (0, s!"no method {method}")
  let engine {α : Type} (act : Except EngineError α) : Result α :=
    act.mapError fun e => (e.code, s!"engine error: {reprStr e}")
  let params := request.getObjValD "params"
  let answer : Json ← match version, byRange with
    | 1, false =>
      let hashes ← engine (bodiesByHashParams params)
      pure (listJson (optionJson bodyV1Json) (← engine (getPayloadBodiesByHashV1 store hashes)))
    | 1, true =>
      let (start, count) ← engine (bodiesByRangeParams params)
      let bodies ← engine (getPayloadBodiesByRangeV1 store start count)
      pure (listJson (optionJson bodyV1Json) bodies)
    | _, false =>
      let hashes ← engine (bodiesByHashParams params)
      pure (listJson (optionJson bodyV2Json) (← engine (getPayloadBodiesByHashV2 store hashes)))
    | _, true =>
      let (start, count) ← engine (bodiesByRangeParams params)
      let bodies ← engine (getPayloadBodiesByRangeV2 store start count)
      pure (listJson (optionJson bodyV2Json) bodies)
  return .ofJson answer

/-- The answer to a payload bodies request, from a store of bodies.

The arguments are the store's entries, the latest known block, the limit and the request.

Each entry is the block hash, its canonical number or `None`, and its fork name.

Then come its transactions, its withdrawals or `None`, and its block access list or `None`. -/
@[export eth_engine_get_payload_bodies]
def payloadBodiesExport (args : PyValue) : Result PyValue :=
  pyExport payloadBodiesOf args

end EthLib.Engine.Exports

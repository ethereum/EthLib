module

public import EthLib.Base.ChainConfig
public import EthLib.Engine.Block
public import EthLib.Engine.Json
public import EthLib.Execution.Blocks.Transition

/-!
# `Engine.NewPayload`

The checks of `engine_newPayload`, versions 1 to 5, that come before the transactions run.

Each version takes payloads of some forks only.

The fork of a payload is the active fork at its number and its timestamp.

Version 1 takes Paris, version 2 Paris and Shapella, version 3 Dencun, version 4 Pectra to BPO5.

Version 5 takes Glamsterdam, which the Engine API calls Amsterdam on the execution side.

A payload of any other fork is an unsupported fork, with JSON-RPC code `-38005`.

The Osaka API update in `amsterdam.md` sets the range of version 4: every fork before Amsterdam.

The source does not say what version 1 returns for a payload after Paris.

EthLib rejects it as an unsupported fork, as it does a payload before Paris.

Version 2 takes the payload structure of the fork: version 1 before Shapella, version 2 from it.

From version 3, it also takes the expected blob versioned hashes and the parent beacon block root.

The expected hashes must be the versioned hashes of the blob transactions, in order.

Version 4 also takes the request lists.

Each list must have more than one byte, and their types must strictly increase.

Version 5 takes version 4 of the payload structure, with the block access list and the slot number.

A list that is not the RLP form of a block access list makes the payload invalid.

Then the block of the payload must decode, and its hash must be the block hash of the payload.

A payload that fails these checks is invalid.

A payload that passes them still needs its parent's state, so without it the status is syncing.

With that state, the block of the payload runs, and its status is valid or invalid.

The method specifications state these rules, at commit `3284ee8` of execution-apis:

- [`engine_newPayloadV1`][v1], which also defines the statuses
- [`engine_newPayloadV2`][v2], with the structure by fork
- [`engine_newPayloadV3`][v3], and its update by Pectra in [`prague.md`][v3-prague]
- [`engine_newPayloadV4`][v4], and its update by Amsterdam in [`amsterdam.md`][v4-amsterdam]
- [`engine_newPayloadV5`][v5]

[v1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_newpayloadv1
[v2]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#engine_newpayloadv2
[v3]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/cancun.md#engine_newpayloadv3
[v3-prague]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#update-the-methods-of-previous-forks
[v4]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/prague.md#engine_newpayloadv4
[v4-amsterdam]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#update-the-methods-of-previous-forks
[v5]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/amsterdam.md#engine_newpayloadv5
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions
open EthLib.Engine.Json

/-- Whether a version of the method takes payloads of a fork. -/
def acceptsFork (version : Nat) (fork : Fork) : Bool :=
  match version with
  | 1 => fork == .paris
  | 2 => fork == .paris || fork == .shapella
  | 3 => fork == .dencun
  | 4 => decide (.pectra ≤ fork) && decide (fork < .glamsterdam)
  | 5 => fork == .glamsterdam
  | _ => false

/-- The number of parameters of a version of the method. -/
def paramCount (version : Nat) : Nat :=
  if version ≥ 4 then 4 else if version = 3 then 3 else 1

/-- Whether a version of the method takes a version of the payload structure.

Version 5 reads its structure, version 4, with its own decoder. -/
def acceptsStructure (version layout : Nat) : Bool :=
  match version with
  | 1 => layout == 1
  | 2 => layout == 1 || layout == 2
  | _ => layout == 3

/-- The payload of a version of the method, with its access list and its slot from version 5. -/
def payloadParam (version : Nat) (j : Json) :
    Decode (AnyPayload × Option (ByteArray × UInt64)) := do
  if version ≥ 5 then
    let (any, blockAccessList, slotNumber) ← payloadV4 j
    return (any, some (blockAccessList, slotNumber))
  else
    let any ← anyPayload j
    unless acceptsStructure version any.version do
      invalid s!"payload: version {any.version} of the structure"
    return (any, none)

/-- Whether request lists have more than one byte each, with strictly increasing types. -/
def validRequests : List ByteArray → Bool
  | [] => true
  | [r] => r.size > 1
  | r :: s :: rest =>
    match r[0]?, s[0]? with
    | some a, some b => r.size > 1 && s.size > 1 && a < b && validRequests (s :: rest)
    | _, _ => false

/-- A payload that passed the checks of a version of the method: the block at its fork. -/
structure CheckedBlock (version : Nat) where
  /-- The fork of the payload. -/
  fork : Fork
  /-- The version takes payloads of the fork. -/
  accepted : acceptsFork version fork = true
  /-- The block of the payload. -/
  block : Block fork Transaction

/-- The checks of a version of the method, under a chain configuration, before execution.

An error is a JSON-RPC error.

Otherwise the result is the invalid status with its reason, or the block of the payload. -/
def checkNewPayload (config : ChainConfig) (version : Nat) (params : Json) :
    Except EngineError (Except (PayloadStatus × PayloadError) (CheckedBlock version)) := do
  -- The parameters must have the structure of the version.
  let params ← match params with
    | .arr items => pure items.toList
    | _ => invalid "params: not an array"
  unless params.length == paramCount version ∧ params.all (!·.isNull) do
    invalid s!"params: not {paramCount version} values"
  let param (i : Nat) : Except EngineError Json :=
    match params[i]? with
    | some j => pure j
    | none => invalid s!"params: no value {i}"
  let (any, amsterdam) ← payloadParam version (← param 0)
  let hashes ← if version ≥ 3 then
    some <$> array "expectedBlobVersionedHashes" (fixed "versioned hash" 32) (← param 1)
    else pure none
  let beaconRoot ← if version ≥ 3 then
    some <$> fixed "parentBeaconBlockRoot" 32 (← param 2) else pure none
  let requests ← if version ≥ 4 then
    some <$> array "executionRequests" (bytes "request") (← param 3) else pure none
  if let some requests := requests then
    unless validRequests requests do invalid "executionRequests: out of order or too short"
  -- The fork of the payload must be one that the version takes.
  let number := any.common.blockNumber.toNat
  let timestamp := any.common.timestamp.toNat
  let some fork := config.activeFork number timestamp | throw .unsupportedFork
  if hAccepted : acceptsFork version fork = true then
    let payload ← any.atFork fork
    let beacon ← since (f := .dencun) "parentBeaconBlockRoot" beaconRoot
    let requests ← since (f := .pectra) "executionRequests" requests
    let accessList ← since (f := .glamsterdam) "blockAccessList" (amsterdam.map (·.1))
    let slot ← since (f := .glamsterdam) "slotNumber" (amsterdam.map (·.2))
    -- The checks of the payload alone.
    let invalidStatus (e : PayloadError) : PayloadStatus × PayloadError :=
      match e with
      | .wrongBlockHash .. =>
        (⟨if version = 1 then .invalidBlockHash else .invalid, none⟩, e)
      | _ => (⟨.invalid, none⟩, e)
    match payload.toBlock beacon requests accessList slot with
    | .error e => return .error (invalidStatus e)
    | .ok block =>
      if let some hashes := hashes then
        if ExecutionPayload.blobVersionedHashes block.transactions ≠ hashes then
          return .error (invalidStatus .wrongVersionedHashes)
      return .ok ⟨fork, hAccepted, block⟩
  else throw .unsupportedFork

/-- The status of `engine_newPayload` from an execution layer without the parent's state.

A payload that passes the checks before execution is syncing, since validation needs that state.
-/
def newPayloadWithoutState (config : ChainConfig) (version : Nat) (params : Json) :
    Except EngineError (PayloadStatus × Option PayloadError) := do
  match ← checkNewPayload config version params with
  | .error (status, reason) => return (status, some reason)
  | .ok _ => return (⟨.syncing, none⟩, none)

/-- The status of `engine_newPayload` from an execution layer that holds the parent's state.

The chain holds the state after its last recent block.

A payload whose parent is not that block stays syncing, since its parent's state is missing.

Otherwise a payload that passes the checks before execution runs as the next block of the chain.

It is valid when its block passes the state transition, and invalid otherwise.

The latest valid hash of a valid payload is its own block hash.

That of a payload invalid in execution is its parent's hash, or zero for a parent before Paris.

An execution that aborts, such as on missing code, leaves the payload syncing.

A valid payload also gives its block, as the new last recent block, and the state after it. -/
def newPayloadOnChain (chain : BlockChain) (version : Nat) (params : Json) :
    Except EngineError
      (PayloadStatus × Option PayloadError × Option (RecentBlock × Execution.State.State)) := do
  match ← checkNewPayload chain.config version params with
  | .error (status, reason) => return (status, some reason, none)
  | .ok checked =>
    let header := checked.block.header
    let some parent := chain.recent.getLast? | return (⟨.syncing, none⟩, none, none)
    unless parent.header.hash.toOption = some header.parentHash do
      return (⟨.syncing, none⟩, none, none)
    match stateTransition chain checked.block (checkSeal := false) with
    | .ok post =>
      return (⟨.valid, header.hash.toOption⟩, none, some (⟨checked.fork, header, []⟩, post))
    | .error (.aborted _) => return (⟨.syncing, none⟩, none, none)
    | .error e =>
      let ancestor : Hash32 := if parent.fork < .paris then 0 else header.parentHash
      return (⟨.invalid, some ancestor⟩, some (.invalidBlock e), none)

end EthLib.Engine

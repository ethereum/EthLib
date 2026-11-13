module

public import EthLib.Base.Exports.ChainConfig
public import EthLib.Consensus.Exports.HonestProposer
public import EthLib.Consensus.Exports.Transition
public import EthLib.Engine.ExecutionEngine

/-!
# `Exports.ExecutionEngine`

The C export that runs a payload request of the beacon chain through two routes.

One route writes the request as JSON and runs the method on it, without the parent's state.

The other is the execution layer of the beacon chain, with the state transition taken as passed.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Base.ChainConfig.Exports (configOfJson)
open EthLib.Consensus.Exports (decodeInput holds transitionPresetAndFork)

/-- The payload request of the beacon chain through the method and through its execution layer.

The arguments are the chain configuration, the preset, the fork and the request in SSZ.

The result is the JSON parameters, then the status of the method or the code of its error.

Last comes whether the layer accepts, with the state transition taken as passed.

Each part that does not apply is `None`. -/
def newPayloadRoutesOf (args : PyValue × String × String × ByteArray) :
    Result (PyValue × PyValue × PyValue × Bool) := do
  let (config, name, fork, request) := args
  let config ← configOfJson config.toJson
  let (preset, fork) ← transitionPresetAndFork name.toUTF8 fork.toUTF8
  let ⟨_⟩ ← holds (.bellatrix ≤ fork) s!"no payload request at {fork.name}"
  let ⟨_⟩ ← holds (fork < .hegota) s!"no version of engine_newPayload at {fork.name}"
  let request ← decodeInput (Consensus.NewPayloadRequest preset fork) request
  let chain : Execution.Blocks.BlockChain :=
    { config, state := { accounts := ∅, storage := ∅, code := ∅ }, recent := [] }
  let engine : Consensus.ExecutionEngine preset fork := executionEngine chain
  let checks : Consensus.ExecutionEngine preset fork := {
    isValidBlockHash := engine.isValidBlockHash
    isValidVersionedHashes := engine.isValidVersionedHashes
    notifyNewPayload := fun _ _ _ => true }
  let accepted := match checks.verifyAndNotifyNewPayload request with
    | .ok true => true
    | _ => false
  match newPayloadRequestJson request with
  | none => return (.none, .none, .none, accepted)
  | some params =>
    match newPayloadWithoutState config (newPayloadVersion fork) params with
    | .ok (status, _) => return (.ofJson params, .str status.status.name, .none, accepted)
    | .error e => return (.ofJson params, .none, .int e.code.toNat, accepted)

/-- The payload request of the beacon chain through the method and through its execution layer.

The arguments are the chain configuration, the preset, the fork and the request in SSZ.

The result is the JSON parameters, then the status of the method or the code of its error.

Last comes whether the layer accepts, with the state transition taken as passed.

Each part that does not apply is `None`. -/
@[export eth_engine_new_payload_routes]
def newPayloadRoutesExport (args : PyValue) : Result PyValue :=
  pyExport newPayloadRoutesOf args

end EthLib.Engine.Exports

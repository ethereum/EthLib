module

public import EthLib.Consensus.BeaconApi.LightClient
public import EthLib.Consensus.Exports.BeaconApiBlocks
public import EthLib.Consensus.Exports.LightClient

/-!
# `Exports.BeaconApiLightClient`

C-ABI exports of the answers of the Beacon API that serve a light client.

The bootstrap reads the store after the steps of a fork choice case.

Its own configuration may replace values of the named one, such as the epochs of the forks.

The updates that the node knows arrive as a list of periods, fork names and SSZ bytes.

The updates answer is in JSON or in SSZ chunks, and the chunks read back to forks and bytes.

The latest finality or optimistic update arrives as the SSZ bytes of an update, or none.

An error response of the API has its own code, such as 404.

An unknown name or fork, or an input that does not decode, has code 0.

A chunk that cannot be built or read also has code 0.
-/

@[expose] public section

namespace EthLib.Consensus.Exports

open Lean Base Serialization.Ssz
open EthLib.Exports (Result PyValue pyExport)
open Serialization.Ssz.Exports (runSsz)

/-- The bootstrap answer for a block of the store after the steps of a fork choice case. -/
def apiLightClientBootstrapOf (args : StoreCaseArgs (Option PyValue × Root)) :
    Result PyValue := do
  let (name, fork, anchorState, anchorBlock, steps, verify, replacements, root) := args
  let ⟨_, _, _, store⟩ ← storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let config ← configWithValue name replacements
  let envelope ← apiError (BeaconApi.bootstrapResponse config store root)
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the bootstrap endpoint, as a `dict`.

The first arguments build the store as a fork choice case does.

Then come replacements of values of the configuration of the bootstrap, and the root of the block.

The fork choice keeps the named configuration, as a fork choice case does. -/
@[export eth_consensus_api_light_client_bootstrap]
def apiLightClientBootstrapExport (args : PyValue) : Result PyValue :=
  pyExport apiLightClientBootstrapOf args

/-- The SSZ body of the bootstrap answer. -/
def apiLightClientBootstrapSszOf (args : StoreCaseArgs (Option PyValue × Root)) :
    Result ByteArray := do
  let (name, fork, anchorState, anchorBlock, steps, verify, replacements, root) := args
  let ⟨_, _, _, store⟩ ← storeOfCase (name, fork, anchorState, anchorBlock, steps, verify)
  let config ← configWithValue name replacements
  apiError do BeaconApi.apiSszOr500 (← BeaconApi.bootstrapFor config store root)

/-- The SSZ body of the bootstrap answer, as `bytes`.

The arguments are those of the JSON answer. -/
@[export eth_consensus_api_light_client_bootstrap_ssz]
def apiLightClientBootstrapSszExport (args : PyValue) : Result PyValue :=
  pyExport apiLightClientBootstrapSszOf args

/-- The result of building or reading chunks, with code 0 for a failure. -/
def runChunks {α : Type} (act : Except BeaconApi.ChunkError α) : Result α :=
  act.mapError fun e => (0, s!"chunk rejected: {reprStr e}")

/-- The updates that a node knows, by period, each decoded with the fork that it names. -/
def knownUpdates (preset : Preset) (known : List (UInt64 × String × ByteArray)) :
    Result (Std.TreeMap UInt64 (BeaconApi.AnyLightClientUpdate preset)) :=
  known.foldlM (init := ∅) fun map (period, fork, data) => do
    let fork ← forkOf fork.toUTF8
    return map.insert period ⟨fork, ← decodeInput (LightClientUpdate preset fork) data⟩

/-- The arguments of an updates request: the configuration, the known updates and the range. -/
abbrev UpdatesArgs :=
  String × Option PyValue × Root × List (UInt64 × String × ByteArray) × UInt64 × UInt64

/-- The JSON response of the updates endpoint.

Each update of the answer must be of the fork of its epoch, as in the SSZ answer. -/
def apiLightClientUpdatesOf
    (args : String × Option PyValue × List (UInt64 × String × ByteArray) × UInt64 × UInt64) :
    Result PyValue := do
  let (name, replacements, known, startPeriod, count) := args
  let preset ← presetOf name
  let config ← configWithValue name replacements
  let known ← knownUpdates preset known
  let updates := BeaconApi.updatesInRange known startPeriod count
  for ⟨_, update⟩ in updates do runChunks (BeaconApi.checkUpdateFork config update)
  return PyValue.ofJson (← apiError (BeaconApi.updatesJson updates))

/-- The JSON response of the updates endpoint, as a `list` of `dict`.

The arguments are the name and replacements of values of the configuration.

Then come the known updates, as periods, fork names and SSZ bytes.

The last arguments are the start period and the count. -/
@[export eth_consensus_api_light_client_updates]
def apiLightClientUpdatesExport (args : PyValue) : Result PyValue :=
  pyExport apiLightClientUpdatesOf args

/-- The SSZ body of the updates answer: the chunks of the answer, one after another. -/
def apiLightClientUpdatesSszOf (args : UpdatesArgs) : Result ByteArray := do
  let (name, replacements, genesisValidatorsRoot, known, startPeriod, count) := args
  let preset ← presetOf name
  let config ← configWithValue name replacements
  let known ← knownUpdates preset known
  runChunks (BeaconApi.encodeUpdateChunks config genesisValidatorsRoot
    (BeaconApi.updatesInRange known startPeriod count))

/-- The SSZ body of the updates answer, as `bytes`.

The first arguments are the name, replacements of values of the configuration and a root.

That root is the root of the genesis validators.

Then come the known updates, as periods, fork names and SSZ bytes.

The last arguments are the start period and the count. -/
@[export eth_consensus_api_light_client_updates_ssz]
def apiLightClientUpdatesSszExport (args : PyValue) : Result PyValue :=
  pyExport apiLightClientUpdatesSszOf args

/-- The fork name and the SSZ bytes of each update of the SSZ body of an updates answer. -/
def apiLightClientDecodeUpdatesOf (args : String × Option PyValue × Root × ByteArray) :
    Result (List (String × ByteArray)) := do
  let (name, replacements, genesisValidatorsRoot, data) := args
  let preset ← presetOf name
  let config ← configWithValue name replacements
  let updates ← runChunks (BeaconApi.decodeUpdateChunks preset config genesisValidatorsRoot data)
  updates.mapM fun ⟨fork, update⟩ => do
    return (fork.name, ← runSsz "value rejected" (SszType.serialize update))

/-- The fork name and the SSZ bytes of each update of the SSZ body of an updates answer.

The first arguments are the name, replacements of values of the configuration and a root.

That root is the root of the genesis validators, and the last argument is the body. -/
@[export eth_consensus_api_light_client_decode_updates]
def apiLightClientDecodeUpdatesExport (args : PyValue) : Result PyValue :=
  pyExport apiLightClientDecodeUpdatesOf args

/-- The JSON response of the finality or the optimistic update endpoint. -/
def apiLightClientLatestOf (args : String × String × String × Option ByteArray) :
    Result PyValue := do
  let (name, fork, kind, latest) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let latest ← latest.mapM (decodeInput (LightClientUpdate preset fork))
  let envelope ← match kind with
    | "finality" => apiError (BeaconApi.finalityUpdateResponse latest)
    | "optimistic" => apiError (BeaconApi.optimisticUpdateResponse latest)
    | other => throw (0, s!"no latest update is of kind {other}")
  return PyValue.ofJson envelope.toJson

/-- The JSON response of the finality or the optimistic update endpoint, as a `dict`.

The arguments are the name, the fork, the kind and the SSZ bytes of the latest update, or none. -/
@[export eth_consensus_api_light_client_latest]
def apiLightClientLatestExport (args : PyValue) : Result PyValue :=
  pyExport apiLightClientLatestOf args

end EthLib.Consensus.Exports

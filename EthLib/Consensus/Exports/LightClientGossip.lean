module

public import EthLib.Consensus.Exports.GossipValidation
public import EthLib.Consensus.Exports.LightClient
public import EthLib.Consensus.Gossip.LightClient

/-!
# `Exports.LightClientGossip`

C-ABI exports that validate the messages of the two light client topics, in turn, from Altair.

The exports take the tuple of their arguments as typed Python values.

Each message is a tuple of its topic, its time of arrival in milliseconds and its SSZ bytes.

The topic is `light_client_finality_update` or `light_client_optimistic_update`.

A full node also gets, with each message, its latest light client update, or none.

Every message is decoded at the given fork, and the store of a light client never upgrades.

A light client starts from a bootstrap for a trusted block root.

It processes each update at the slot of the clock, whatever the outcome.

It keeps the new store when it accepts the update, and the old one otherwise.

A forwarded message joins the forwarded updates of its topic, which the later messages read.

Each message gives `valid`, `ignore` or `reject`, and an ignore or a reject gives its reason.

An input that the export reads itself, such as a wrong length or an unknown topic, has code 0.

So does a time before genesis, or one that leaves the 64-bit range.
-/

public section

namespace EthLib.Consensus.Exports

open Base Serialization.Ssz Networking.Gossip
open EthLib.Exports (Result PyValue fromPy pyExport)

/-- A result of the clock, with code 0 for a time before genesis or out of the 64-bit range. -/
def runClock {α : Type} (act : Except ArithError α) : Result α :=
  act.mapError fun e => (0, s!"time rejected: {reprStr e}")

/-- The outcomes of light client messages at a full node, in turn.

Each message comes with the latest update of the node at that time, or none. -/
def lightClientGossipFullNodeOf (args : String × String × Option PyValue × UInt64 ×
    List (String × UInt64 × ByteArray × Option ByteArray)) :
    Result (List (String × Option String)) := do
  let (name, fork, replacements, genesisTimeMs, messages) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let mut forwarded : LightClientForwarded preset fork := {}
  let mut out := #[]
  for (topic, currentTimeMs, data, latest) in messages do
    let latest ← latest.mapM (decodeAs (LightClientUpdate preset fork))
    match topic with
      | "light_client_finality_update" =>
        let update ← decodeAs (LightClientFinalityUpdate preset fork) data
        let outcome ← runClock (forwarded.validateFinalityUpdateAtFullNode config genesisTimeMs
          latest update currentTimeMs)
        if outcome.isAccept then forwarded := forwarded.recordFinalityUpdate update
        out := out.push (outcomeRecord outcome)
      | "light_client_optimistic_update" =>
        let update ← decodeAs (LightClientOptimisticUpdate preset fork) data
        let outcome ← runClock (forwarded.validateOptimisticUpdateAtFullNode config genesisTimeMs
          latest update currentTimeMs)
        if outcome.isAccept then forwarded := forwarded.recordOptimisticUpdate update
        out := out.push (outcomeRecord outcome)
      | other => throw (0, s!"no light client topic is named {other}")
  return out.toList

/-- The outcomes of light client messages at a full node, in turn.

The arguments are the names of the preset and the fork, and replacements of the configuration.

Then come the time of genesis in milliseconds and the messages.

A message is its topic, its time in milliseconds, its bytes and the latest update of the node. -/
@[export eth_consensus_light_client_gossip_full_node]
def lightClientGossipFullNodeExport (args : PyValue) : Result PyValue :=
  pyExport lightClientGossipFullNodeOf args

/-- The outcomes of light client messages at a light client, in turn.

The store starts from a bootstrap at the given fork, and processes every update.

An update that the store refuses leaves the store as it was. -/
def lightClientGossipLightClientOf (args : String × String × Option PyValue × UInt64 × Root ×
    Root × ByteArray × Bool × List (String × UInt64 × ByteArray)) :
    Result (List (String × Option String)) := do
  let (name, fork, replacements, genesisTimeMs, trusted, genesisValidatorsRoot, bootstrap, verify,
    messages) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let checks := if verify then SignatureChecks.bls else SignatureChecks.acceptAll
  let bootstrap ← decodeAs (LightClientBootstrap preset fork) bootstrap
  let mut store ← runLightClient (initializeLightClientStore config trusted bootstrap)
  let mut forwarded : LightClientForwarded preset fork := {}
  let mut out := #[]
  for (topic, currentTimeMs, data) in messages do
    match topic with
      | "light_client_finality_update" =>
        let update ← decodeAs (LightClientFinalityUpdate preset fork) data
        let outcome ← runClock (forwarded.validateFinalityUpdateAtLightClient config genesisTimeMs
          checks store genesisValidatorsRoot update currentTimeMs)
        let currentSlot ← runClock (computeSlotAtTimeMs config genesisTimeMs currentTimeMs)
        let next := processLightClientFinalityUpdate config checks store update currentSlot
          genesisValidatorsRoot
        store := next.toOption.getD store
        if outcome.isAccept then forwarded := forwarded.recordFinalityUpdate update
        out := out.push (outcomeRecord outcome)
      | "light_client_optimistic_update" =>
        let update ← decodeAs (LightClientOptimisticUpdate preset fork) data
        let outcome ← runClock (forwarded.validateOptimisticUpdateAtLightClient config
          genesisTimeMs checks store genesisValidatorsRoot update currentTimeMs)
        let currentSlot ← runClock (computeSlotAtTimeMs config genesisTimeMs currentTimeMs)
        let next := processLightClientOptimisticUpdate config checks store update currentSlot
          genesisValidatorsRoot
        store := next.toOption.getD store
        if outcome.isAccept then forwarded := forwarded.recordOptimisticUpdate update
        out := out.push (outcomeRecord outcome)
      | other => throw (0, s!"no light client topic is named {other}")
  return out.toList

/-- The outcomes of light client messages at a light client, in turn.

The arguments are the names of the preset and the fork, and replacements of the configuration.

Then come the time of genesis in ms, the trusted block root and the root of genesis validators.

Then come the bootstrap in SSZ, whether the signature checks run, and the messages.

A message is its topic, its time in milliseconds and its bytes.

The store processes every update, whatever its outcome. -/
@[export eth_consensus_light_client_gossip_light_client]
def lightClientGossipLightClientExport (args : PyValue) : Result PyValue :=
  pyExport lightClientGossipLightClientOf args

/-- The SSZ bytes of a light client update, or of its finality or optimistic update.

The type names one of the three containers, and the update arrives in SSZ.

The arguments are the names of the preset, the fork and the type, and the update in SSZ. -/
@[export eth_consensus_light_client_update_as]
def lightClientUpdateAsExport (args : PyValue) : Result PyValue :=
  pyExport (fun (args : String × String × String × ByteArray) => do
    let (name, fork, type, data) := args
    let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
    serializeUpdate type (← decodeAs (LightClientUpdate preset fork) data)) args

end EthLib.Consensus.Exports

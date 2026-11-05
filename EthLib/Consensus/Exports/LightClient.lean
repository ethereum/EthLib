module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.LightClient.Sync

/-!
# `Exports.LightClient`

C-ABI exports of the light client sync protocol, from Altair to Fulu.

A bootstrap and the updates arrive in their SSZ encoding.

The steps of a sync arrive one after another in one byte string.

Each step is an 8-byte slot, a 4-byte length, then that many bytes of an update.

A step with no update forces an update at that slot.

After each step comes the slot, the beacon root and the execution root of two headers.

Those are the finalized header, then the optimistic header, each in 72 bytes.

Slots and lengths are little-endian.

An input that the export reads itself, such as a wrong length, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result)
open Base Serialization.Ssz
open Serialization.Ssz.Exports (runSsz)

/-- A result of the light client, with the code of its error. -/
def runLightClient {α : Type} (act : Except LightClientError α) : Result α :=
  act.mapError fun e => (e.code, s!"light client: {reprStr e}")

/-- The preset and a fork of the light client, from Altair to Fulu. -/
def lightClientPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  runLightClient (LightClientError.requireFork fork)
  return (preset, fork)

/-- The 32 bytes of a root. -/
def rootOf (bytes : ByteArray) : Result Root :=
  if h : bytes.size = 32 then return ⟨bytes.data, h⟩ else throw (0, "a root has 32 bytes")

/-- A value of a type, decoded from its SSZ bytes, with code 0 when it does not decode. -/
def decodeAs (α : Type) [SszType α] (data : ByteArray) : Result α :=
  (SszType.deserialize α data).mapError fun e => (0, s!"input rejected: {reprStr e}")

/-- The steps that the bytes hold from an offset, as slots and update bytes.

Each step reads at least 12 bytes, so as many rounds as bytes suffice. -/
def readSteps : (rounds : Nat) → ByteArray → Nat → Result (List (Slot × ByteArray))
  | 0, _, _ => throw (0, "steps do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if bytes.size < offset + 12 then throw (0, "a step is cut short")
    else do
      let slot ← decodeAs UInt64 (bytes.extract offset (offset + 8))
      let length := (← decodeAs UInt32 (bytes.extract (offset + 8) (offset + 12))).toNat
      let stop := offset + 12 + length
      if bytes.size < stop then throw (0, "an update is cut short")
      let rest ← readSteps rounds bytes stop
      return (slot, bytes.extract (offset + 12) stop) :: rest

/-- The slot, the beacon root and the execution root of a header, in 72 bytes. -/
def headerRecord {preset : Preset} {fork : Fork} (config : Config)
    (header : LightClientHeader preset fork) : Result ByteArray := do
  let beacon ← runSsz "root rejected" (SszType.hashTreeRoot header.beacon)
  let execution ← runLightClient (getLcExecutionRoot config header)
  return Base.packBytes (uintToBytes 8 header.beacon.slot.toNat) ++ Base.packBytes beacon ++
    Base.packBytes execution

/-- The headers of a sync, step by step, from a bootstrap for a trusted block root.

The configuration of the name holds, with the replacements that the JSON object gives.

Each update is checked with the BLS signature scheme. -/
@[export eth_consensus_light_client_sync]
def lightClientSyncExport (name fork replacements trusted genesisValidatorsRoot bootstrap
    steps : ByteArray) : Result ByteArray := do
  let (preset, fork) ← lightClientPresetAndFork name fork
  let config ← configWith name replacements
  let trusted ← rootOf trusted
  let genesisValidatorsRoot ← rootOf genesisValidatorsRoot
  let bootstrap ← decodeAs (LightClientBootstrap preset fork) bootstrap
  let mut store ← runLightClient (initializeLightClientStore config trusted bootstrap)
  let mut out := ByteArray.empty
  for (slot, data) in ← readSteps steps.size steps 0 do
    if data.isEmpty then
      store ← runLightClient (processLightClientStoreForceUpdate store slot)
    else
      let update ← decodeAs (LightClientUpdate preset fork) data
      store ← runLightClient (processLightClientUpdate config SignatureChecks.bls store update
        slot genesisValidatorsRoot)
    out := out ++ (← headerRecord config store.finalizedHeader) ++
      (← headerRecord config store.optimisticHeader)
  return out

/-- Whether a new update, given as bytes, ranks above an old one for a forced update. -/
@[export eth_consensus_is_better_update]
def isBetterUpdateExport (name fork newUpdate oldUpdate : ByteArray) : Result Bool := do
  let (preset, fork) ← lightClientPresetAndFork name fork
  return isBetterUpdate (← decodeAs (LightClientUpdate preset fork) newUpdate)
    (← decodeAs (LightClientUpdate preset fork) oldUpdate)

/-- The fork digest at an epoch, on the chain with the given root of the genesis validators.

The configuration of the name holds, with the replacements that the JSON object gives. -/
@[export eth_consensus_compute_fork_digest]
def computeForkDigestExport (name replacements genesisValidatorsRoot : ByteArray)
    (epoch : UInt64) : Result ByteArray := do
  let config ← configWith name replacements
  let root ← rootOf genesisValidatorsRoot
  return Base.packBytes (← runSsz "root rejected" (computeForkDigest config root epoch))

end EthLib.Consensus.Exports

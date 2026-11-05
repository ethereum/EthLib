module

public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.LightClient.FullNode
public import EthLib.Consensus.LightClient.Upgrade

/-!
# `Exports.LightClient`

C-ABI exports of the light client sync protocol, from Altair to Fulu.

A bootstrap, the updates and the blocks arrive in their SSZ encoding.

The steps of a sync arrive one after another in one byte string.

Each step starts with one byte for its kind, then an 8-byte slot.

Then come a 1-byte length and the name of a fork, then a 4-byte length and that many bytes.

Kind 0 processes an update of that fork at that slot.

Kind 1 forces an update at that slot, and kind 2 upgrades the store to that fork.

Data of an earlier fork than the store is upgraded to the fork of the store first.

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

/-- A step of a sync: its kind, its slot, the name of its fork and its bytes. -/
abbrev SyncStep := UInt8 × Slot × ByteArray × ByteArray

/-- The steps that the bytes hold from an offset.

Each step reads at least 14 bytes, so one round more than the bytes suffices. -/
def readSteps : (rounds : Nat) → ByteArray → Nat → Result (List SyncStep)
  | 0, _, _ => throw (0, "steps do not end")
  | rounds + 1, bytes, offset =>
    if offset = bytes.size then return []
    else if bytes.size < offset + 10 then throw (0, "a step is cut short")
    else do
      let kind := bytes.get! offset
      let slot ← decodeAs UInt64 (bytes.extract (offset + 1) (offset + 9))
      let nameStop := offset + 10 + (bytes.get! (offset + 9)).toNat
      if bytes.size < nameStop + 4 then throw (0, "a step is cut short")
      let length := (← decodeAs UInt32 (bytes.extract nameStop (nameStop + 4))).toNat
      let stop := nameStop + 4 + length
      if bytes.size < stop then throw (0, "the bytes of a step are cut short")
      let rest ← readSteps rounds bytes stop
      return (kind, slot, bytes.extract (offset + 10) nameStop,
        bytes.extract (nameStop + 4) stop) :: rest

/-- A fork of the light client, named by bytes, that is not later than the fork of a store. -/
def dataFork (name : ByteArray) (store : Fork) : Result {fork : Fork // fork ≤ store} := do
  let fork ← forkOf name
  runLightClient (LightClientError.requireFork fork)
  if earlier : fork ≤ store then return ⟨fork, earlier⟩
  else throw (0, s!"data of {fork.name} is later than a store of {store.name}")

/-- The slot, the beacon root and the execution root of a header, in 72 bytes. -/
def headerRecord {preset : Preset} {fork : Fork} (config : Config)
    (header : LightClientHeader preset fork) : Result ByteArray := do
  let beacon ← runSsz "root rejected" (SszType.hashTreeRoot header.beacon)
  let execution ← runLightClient (getLcExecutionRoot config header)
  return Base.packBytes (uintToBytes 8 header.beacon.slot.toNat) ++ Base.packBytes beacon ++
    Base.packBytes execution

/-- The headers of a sync, step by step, from a bootstrap for a trusted block root.

The store starts at the given fork, and the bootstrap may be of an earlier fork.

The configuration of the name holds, with the replacements that the JSON object gives.

Each update is checked with the BLS signature scheme. -/
@[export eth_consensus_light_client_sync]
def lightClientSyncExport (name fork bootstrapFork replacements trusted genesisValidatorsRoot
    bootstrap steps : ByteArray) : Result ByteArray := do
  let (preset, fork) ← lightClientPresetAndFork name fork
  let config ← configWith name replacements
  let trusted ← rootOf trusted
  let genesisValidatorsRoot ← rootOf genesisValidatorsRoot
  let ⟨bootstrapFork, earlier⟩ ← dataFork bootstrapFork fork
  let bootstrap ← decodeAs (LightClientBootstrap preset bootstrapFork) bootstrap
  let mut store : (fork : Fork) × LightClientStore preset fork :=
    ⟨fork, ← runLightClient
      (initializeLightClientStore config trusted (bootstrap.upgrade fork earlier))⟩
  let mut out := ByteArray.empty
  for (kind, slot, forkName, data) in ← readSteps (steps.size + 1) steps 0 do
    let ⟨storeFork, current⟩ := store
    match kind with
    | 0 =>
      let ⟨updateFork, earlier⟩ ← dataFork forkName storeFork
      let update ← decodeAs (LightClientUpdate preset updateFork) data
      store := ⟨storeFork, ← runLightClient (processLightClientUpdate config SignatureChecks.bls
        current (update.upgrade storeFork earlier) slot genesisValidatorsRoot)⟩
    | 1 => store := ⟨storeFork, ← runLightClient (processLightClientStoreForceUpdate current slot)⟩
    | 2 =>
      let next ← forkOf forkName
      runLightClient (LightClientError.requireFork next)
      if later : storeFork ≤ next then store := ⟨next, current.upgrade next later⟩
      else throw (0, s!"a store of {storeFork.name} cannot go back to {next.name}")
    | _ => throw (0, s!"no step of kind {kind}")
    out := out ++ (← headerRecord config store.2.finalizedHeader) ++
      (← headerRecord config store.2.optimisticHeader)
  return out

/-- The root of a block, given as bytes, then the bytes of its light client header. -/
@[export eth_consensus_block_to_light_client_header]
def blockToLightClientHeaderExport (name fork replacements block : ByteArray) :
    Result ByteArray := do
  let (preset, fork) ← lightClientPresetAndFork name fork
  let config ← configWith name replacements
  let block ← decodeAs (SignedBeaconBlock preset fork) block
  let root ← runSsz "root rejected" (SszType.hashTreeRoot block.message)
  let header ← runLightClient (blockToLightClientHeader config block)
  return Base.packBytes root ++ (← runSsz "value rejected" (SszType.serialize header))

/-- Whether the proofs of an update or a finality update, given as bytes, verify.

These are the checks of an update that read no store and no signature.

The attested header must be valid, and so must the finality branch.

The branch of the next sync committee must verify, or that committee must be zero. -/
@[export eth_consensus_light_client_update_proofs]
def lightClientUpdateProofsExport (name fork type replacements data : ByteArray) :
    Result Bool := do
  let (preset, fork) ← lightClientPresetAndFork name fork
  let config ← configWith name replacements
  let update ← match ← nameOf type with
    | "LightClientUpdate" => decodeAs (LightClientUpdate preset fork) data
    | "LightClientFinalityUpdate" =>
      LightClientFinalityUpdate.toUpdate <$> decodeAs (LightClientFinalityUpdate preset fork) data
    | other => throw (0, s!"no update of type {other}")
  runLightClient do
    LightClientError.require (← isValidLightClientHeader config update.attestedHeader)
      .invalidHeader
    validateFinality config update
    if update.isSyncCommitteeUpdate then validateNextSyncCommitteeBranch config update
    else
      LightClientError.require (update.nextSyncCommittee = SyncCommittee.empty preset)
        .unexpectedNextSyncCommittee
  return true

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

module

public import EthLib.Base.Exports.PyDerive
public import EthLib.Consensus.Exports.Ssz
public import EthLib.Consensus.LightClient.FullNode
public import EthLib.Consensus.LightClient.Upgrade

/-!
# `Exports.LightClient`

C-ABI exports of the light client sync protocol, from Altair.

A bootstrap, the updates and the blocks arrive in their SSZ encoding.

The exports that take a configuration take the tuple of their arguments as typed Python values.

The names of the preset, of the forks and of a type arrive as `str`.

A configuration replacement arrives as a `dict`.

A step of a sync processes an update of a fork at a slot, forces an update, or upgrades the store.

Data of an earlier fork than the store is upgraded to the fork of the store first.

After each step come two headers: the finalized header, then the optimistic header.

Each is the slot, the beacon root and the execution root of the header.

An input that the export reads itself, such as a wrong length, has code 0.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue ToPy FromPy LawfulPy toPy fromPy pyExport)
open Base Serialization.Ssz
open Serialization.Ssz.Exports (runSsz)

/-- A result of the light client, with the code of its error. -/
def runLightClient {α : Type} (act : Except LightClientError α) : Result α :=
  act.mapError fun e => (e.code, s!"light client: {reprStr e}")

/-- The preset and a fork of the light client, from Altair. -/
def lightClientPresetAndFork (name fork : ByteArray) : Result (Preset × Fork) := do
  let preset ← presetOf (← nameOf name)
  let fork ← forkOf fork
  runLightClient (LightClientError.requireFork fork)
  return (preset, fork)

/-- A value of a type, decoded from its SSZ bytes, with code 0 when it does not decode. -/
def decodeAs (α : Type) [SszType α] (data : ByteArray) : Result α :=
  (SszType.deserialize α data).mapError fun e => (0, s!"input rejected: {reprStr e}")

/-- A step of a sync. -/
inductive SyncStep where
  /-- An update of a fork, in SSZ, processed at a slot. -/
  | update (fork : String) (slot : UInt64) (data : ByteArray)
  /-- An update forced at a slot. -/
  | force (slot : UInt64)
  /-- An upgrade of the store to a fork. -/
  | upgrade (fork : String)

derive_py SyncStep
derive_py_laws SyncStep

/-- The slot, the beacon root and the execution root of a header. -/
structure SyncHeader where
  /-- The slot of the header. -/
  slot : UInt64
  /-- The root of the beacon block header. -/
  beaconRoot : Root
  /-- The root of the execution payload header. -/
  executionRoot : Root

/-- A header is a tuple of its slot and its two roots. -/
instance : ToPy SyncHeader := ⟨fun h => toPy (h.slot, h.beaconRoot, h.executionRoot)⟩

/-- A header is a tuple of its slot and its two roots. -/
instance : FromPy SyncHeader := ⟨fun v =>
  (fun (slot, beaconRoot, executionRoot) => ⟨slot, beaconRoot, executionRoot⟩) <$>
    fromPy (α := UInt64 × Root × Root) v⟩

instance : LawfulPy SyncHeader where
  fromPy_toPy := by
    rintro ⟨a, b, c⟩
    have h := LawfulPy.fromPy_toPy (α := UInt64 × Root × Root) (a, b, c)
    show (fun (slot, beaconRoot, executionRoot) => (⟨slot, beaconRoot, executionRoot⟩ : SyncHeader))
      <$> fromPy (α := UInt64 × Root × Root) (toPy (a, b, c)) = _
    rw [h]
    rfl

/-- A fork of the light client, by name, that is not later than the fork of a store. -/
def dataFork (name : String) (store : Fork) : Result {fork : Fork // fork ≤ store} := do
  let fork ← forkOf name.toUTF8
  runLightClient (LightClientError.requireFork fork)
  if earlier : fork ≤ store then return ⟨fork, earlier⟩
  else throw (0, s!"data of {fork.name} is later than a store of {store.name}")

/-- The slot, the beacon root and the execution root of a header. -/
def headerRecord {preset : Preset} {fork : Fork} (config : Config)
    (header : LightClientHeader preset fork) : Result SyncHeader := do
  let beacon ← runSsz "root rejected" (SszType.hashTreeRoot header.beacon)
  let execution ← runLightClient (getLcExecutionRoot config header)
  return ⟨header.beacon.slot, beacon, execution⟩

/-- The headers of a sync, step by step, from a bootstrap for a trusted block root.

The store starts at the given fork, and the bootstrap may be of an earlier fork.

Each update is checked with the BLS signature scheme. -/
def lightClientSyncOf (args : String × String × String × Option PyValue × Root × Root ×
    ByteArray × List SyncStep) : Result (List (SyncHeader × SyncHeader)) := do
  let (name, fork, bootstrapFork, replacements, trusted, genesisValidatorsRoot, bootstrap,
    steps) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let ⟨bootstrapFork, earlier⟩ ← dataFork bootstrapFork fork
  let bootstrap ← decodeAs (LightClientBootstrap preset bootstrapFork) bootstrap
  let mut store : (fork : Fork) × LightClientStore preset fork :=
    ⟨fork, ← runLightClient
      (do initializeLightClientStore config trusted (← bootstrap.upgrade config fork earlier))⟩
  let mut out := #[]
  for step in steps do
    let ⟨storeFork, current⟩ := store
    match step with
    | .update forkName slot data =>
      let ⟨updateFork, earlier⟩ ← dataFork forkName storeFork
      let update ← decodeAs (LightClientUpdate preset updateFork) data
      store := ⟨storeFork, ← runLightClient do
        processLightClientUpdate config SignatureChecks.bls current
          (← update.upgrade config storeFork earlier) slot genesisValidatorsRoot⟩
    | .force slot =>
      store := ⟨storeFork, ← runLightClient (processLightClientStoreForceUpdate current slot)⟩
    | .upgrade forkName =>
      let next ← forkOf forkName.toUTF8
      runLightClient (LightClientError.requireFork next)
      if later : storeFork ≤ next then
        store := ⟨next, ← runLightClient (current.upgrade config next later)⟩
      else throw (0, s!"a store of {storeFork.name} cannot go back to {next.name}")
    out := out.push
      (← headerRecord config store.2.finalizedHeader,
        ← headerRecord config store.2.optimisticHeader)
  return out.toList

/-- The headers of a sync, step by step, from a bootstrap for a trusted block root.

The arguments are the names of the preset, the fork of the store and the fork of the bootstrap.

Then come replacements of values of the configuration and the trusted block root.

Then come the root of the genesis validators, the bootstrap in SSZ and the steps.

A step is an update of a fork at a slot, an update forced at a slot, or an upgrade to a fork.

Each step gives the finalized header, then the optimistic header, each a slot and two roots.

Each update is checked with the BLS signature scheme. -/
@[export eth_consensus_light_client_sync]
def lightClientSyncExport (args : PyValue) : Result PyValue := pyExport lightClientSyncOf args

/-- The root of a block, given as bytes, and the bytes of its light client header, as a pair. -/
def blockToLightClientHeaderOf
    (args : String × String × Option PyValue × ByteArray) :
    Result (Root × ByteArray) := do
  let (name, fork, replacements, block) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let block ← decodeAs (SignedBeaconBlock preset fork) block
  let root ← runSsz "root rejected" (SszType.hashTreeRoot block.message)
  let header ← runLightClient (blockToLightClientHeader config block)
  return (root, ← runSsz "value rejected" (SszType.serialize header))

/-- The root of a block, given as bytes, and the bytes of its light client header, as a pair. -/
@[export eth_consensus_block_to_light_client_header]
def blockToLightClientHeaderExport (args : PyValue) : Result PyValue :=
  pyExport blockToLightClientHeaderOf args

/-- Whether the proofs of an update or a finality update, given as bytes, verify. -/
def lightClientUpdateProofsOf
    (args : String × String × String × Option PyValue × ByteArray) :
    Result Bool := do
  let (name, fork, type, replacements, data) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let update ← match type with
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

/-- Whether the proofs of an update or a finality update, given as bytes, verify.

These are the checks of an update that read no store and no signature.

The attested header must be valid, and so must the finality branch.

The branch of the next sync committee must verify, or that committee must be zero. -/
@[export eth_consensus_light_client_update_proofs]
def lightClientUpdateProofsExport (args : PyValue) : Result PyValue :=
  pyExport lightClientUpdateProofsOf args

/-- Whether a new update, given as bytes, ranks above an old one for a forced update. -/
def isBetterUpdateOf
    (args : String × String × String × Option PyValue × ByteArray × ByteArray) :
    Result Bool := do
  let (name, fork, oldFork, replacements, newUpdate, oldUpdate) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let (_, oldFork) ← lightClientPresetAndFork name.toUTF8 oldFork.toUTF8
  let config ← configWithValue name replacements
  let newUpdate ← decodeAs (LightClientUpdate preset fork) newUpdate
  let oldUpdate ← decodeAs (LightClientUpdate preset oldFork) oldUpdate
  if earlier : fork ≤ oldFork then
    return isBetterUpdate (← runLightClient (newUpdate.upgrade config oldFork earlier)) oldUpdate
  else
    let later := Nat.le_of_lt (Nat.lt_of_not_le earlier)
    return isBetterUpdate newUpdate (← runLightClient (oldUpdate.upgrade config fork later))

/-- Whether a new update, given as bytes, ranks above an old one for a forced update.

The first fork is that of the new update, and the second that of the old one.

The update of the earlier fork is first upgraded to the later fork. -/
@[export eth_consensus_is_better_update]
def isBetterUpdateExport (args : PyValue) : Result PyValue := pyExport isBetterUpdateOf args

/-- The genesis block of a state, given as bytes, with a signature of zero bytes.

No proposer signs the genesis block, so its signature is 96 zero bytes. -/
@[export eth_consensus_genesis_block]
def genesisBlockExport (name fork state : ByteArray) : Result ByteArray := do
  let (preset, fork) ← lightClientPresetAndFork name fork
  let state ← decodeAs (BeaconState preset fork) state
  let root ← runSsz "root rejected" (SszType.hashTreeRoot state)
  let block ← runSsz "default rejected" (BeaconBlock.genesis preset fork root)
  let signed : SignedBeaconBlock preset fork := ⟨block, Vector.replicate _ 0⟩
  runSsz "value rejected" (SszType.serialize signed)

/-- The bootstrap that a full node serves for a block, from the block and its post state. -/
def createLightClientBootstrapOf
    (args : String × String × Option PyValue × ByteArray × ByteArray) :
    Result ByteArray := do
  let (name, fork, replacements, state, block) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let config ← configWithValue name replacements
  let bootstrap ← runLightClient (createLightClientBootstrap config
    (← decodeAs (BeaconState preset fork) state) (← decodeAs (SignedBeaconBlock preset fork) block))
  runSsz "value rejected" (SszType.serialize bootstrap)

/-- The bootstrap that a full node serves for a block, from the block and its post state. -/
@[export eth_consensus_create_light_client_bootstrap]
def createLightClientBootstrapExport (args : PyValue) : Result PyValue :=
  pyExport createLightClientBootstrapOf args

/-- The SSZ bytes of an update, or of the finality or optimistic update that a type names. -/
def serializeUpdate {preset : Preset} {fork : Fork} (type : String)
    (update : LightClientUpdate preset fork) : Result ByteArray := do
  match type with
  | "LightClientUpdate" => runSsz "value rejected" (SszType.serialize update)
  | "LightClientFinalityUpdate" =>
    runSsz "value rejected" (SszType.serialize (createLightClientFinalityUpdate update))
  | "LightClientOptimisticUpdate" =>
    runSsz "value rejected" (SszType.serialize (createLightClientOptimisticUpdate update))
  | other => throw (0, s!"no update of type {other}")

/-- The update that a full node serves for a block, from the blocks and their post states. -/
def createLightClientUpdateOf
    (args : String × String × String × String × String × Option PyValue × ByteArray ×
      ByteArray × ByteArray × ByteArray × Option ByteArray) :
    Result ByteArray := do
  let (name, fork, attestedFork, finalizedFork, type, replacements, state, block, attestedState,
    attestedBlock, finalizedBlock) := args
  let (preset, fork) ← lightClientPresetAndFork name.toUTF8 fork.toUTF8
  let (_, attestedFork) ← lightClientPresetAndFork name.toUTF8 attestedFork.toUTF8
  let (_, finalizedFork) ← lightClientPresetAndFork name.toUTF8 finalizedFork.toUTF8
  let config ← configWithValue name replacements
  if earlier : finalizedFork ≤ attestedFork then
    let finalized ← finalizedBlock.mapM (decodeAs (SignedBeaconBlock preset finalizedFork))
    let update ← runLightClient (createLightClientUpdate config
      (← decodeAs (BeaconState preset fork) state)
      (← decodeAs (SignedBeaconBlock preset fork) block)
      (← decodeAs (BeaconState preset attestedFork) attestedState)
      (← decodeAs (SignedBeaconBlock preset attestedFork) attestedBlock) finalized earlier)
    serializeUpdate type update
  else throw (0, s!"finalized fork {finalizedFork.name} after {attestedFork.name}")

/-- The update that a full node serves for a block, from the blocks and their post states.

The type names the update, the finality update or the optimistic update that it gives.

The first fork is that of the block, the second that of its parent, which the update takes.

The third is the fork of the finalized block, at or before the second.

`None` for the finalized block stands for a finalized block that the node does not know. -/
@[export eth_consensus_create_light_client_update]
def createLightClientUpdateExport (args : PyValue) : Result PyValue :=
  pyExport createLightClientUpdateOf args

/-- The fork digest at an epoch, on the chain with the given root of the genesis validators. -/
def computeForkDigestOf (args : String × Option PyValue × Root × UInt64) : Result ByteArray := do
  let (name, replacements, genesisValidatorsRoot, epoch) := args
  let config ← configWithValue name replacements
  let digest ← runSsz "root rejected" (computeForkDigest config genesisValidatorsRoot epoch)
  return Base.packBytes digest

/-- The fork digest at an epoch, on the chain with the given root of the genesis validators.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_compute_fork_digest]
def computeForkDigestExport (args : PyValue) : Result PyValue := pyExport computeForkDigestOf args

end EthLib.Consensus.Exports

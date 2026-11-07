module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Types
public import EthLib.Networking.Enr.Consensus
public import EthLib.Networking.Gossip.Topic
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.ReqResp.Messages`

The messages of the request and response protocols of the consensus layer, up to Gloas.

Each protocol has an ID, the string `/eth2/beacon_chain/req/N/V/ssz_snappy`.

`N` names the protocol and `V` is its version, a positive integer.

Phase 0 has the status, goodbye, block range, block root, ping and metadata protocols.

Altair adds a second version of the block and metadata protocols.

Altair also adds four protocols that serve light clients.

Deneb adds the protocols of blob sidecars, by range and by root.

Fulu adds the protocols of data column sidecars, by range and by root.

Fulu also adds blocks by head, a second version of status and a third of metadata.

Fulu deprecates the blob protocols at an epoch after its start, so they stay in its list.

Gloas adds the protocols of execution payload envelopes, by range and by root.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Networking.Enr

/-- A request and response protocol of the consensus layer, without its version. -/
inductive ReqRespProtocol where
  /-- The status of a node: its fork digest, its finalized checkpoint and its head. -/
  | status
  /-- The reason a node gives when it disconnects. -/
  | goodbye
  /-- Blocks in a range of slots. -/
  | beaconBlocksByRange
  /-- Blocks by the roots of their messages. -/
  | beaconBlocksByRoot
  /-- The sequence number of the metadata of a node. -/
  | ping
  /-- The metadata of a node. -/
  | metadata
  /-- From Altair: the bootstrap of a light client at a block root. -/
  | lightClientBootstrap
  /-- From Altair: the light client updates of a range of sync committee periods. -/
  | lightClientUpdatesByRange
  /-- From Altair: the latest light client finality update. -/
  | lightClientFinalityUpdate
  /-- From Altair: the latest light client optimistic update. -/
  | lightClientOptimisticUpdate
  /-- From Deneb: blob sidecars in a range of slots. -/
  | blobSidecarsByRange
  /-- From Deneb: blob sidecars by block root and index. -/
  | blobSidecarsByRoot
  /-- From Fulu: data column sidecars of some columns in a range of slots. -/
  | dataColumnSidecarsByRange
  /-- From Fulu: data column sidecars by block root and column indices. -/
  | dataColumnSidecarsByRoot
  /-- From Fulu: blocks along the ancestry of a block root, newest first. -/
  | beaconBlocksByHead
  /-- From Gloas: the payload envelopes of the blocks of a range of slots, on the head's chain. -/
  | executionPayloadEnvelopesByRange
  /-- From Gloas: payload envelopes by the roots of their blocks. -/
  | executionPayloadEnvelopesByRoot
  deriving DecidableEq, Repr

/-- The name of a protocol in its ID. -/
def ReqRespProtocol.name : ReqRespProtocol → String
  | .status => "status"
  | .goodbye => "goodbye"
  | .beaconBlocksByRange => "beacon_blocks_by_range"
  | .beaconBlocksByRoot => "beacon_blocks_by_root"
  | .ping => "ping"
  | .metadata => "metadata"
  | .lightClientBootstrap => "light_client_bootstrap"
  | .lightClientUpdatesByRange => "light_client_updates_by_range"
  | .lightClientFinalityUpdate => "light_client_finality_update"
  | .lightClientOptimisticUpdate => "light_client_optimistic_update"
  | .blobSidecarsByRange => "blob_sidecars_by_range"
  | .blobSidecarsByRoot => "blob_sidecars_by_root"
  | .dataColumnSidecarsByRange => "data_column_sidecars_by_range"
  | .dataColumnSidecarsByRoot => "data_column_sidecars_by_root"
  | .beaconBlocksByHead => "beacon_blocks_by_head"
  | .executionPayloadEnvelopesByRange => "execution_payload_envelopes_by_range"
  | .executionPayloadEnvelopesByRoot => "execution_payload_envelopes_by_root"

/-- Every protocol: those of Phase 0 in the order of its text, then the later ones by fork. -/
def ReqRespProtocol.all : List ReqRespProtocol :=
  [.status, .goodbye, .beaconBlocksByRange, .beaconBlocksByRoot, .ping, .metadata,
    .lightClientBootstrap, .lightClientUpdatesByRange, .lightClientFinalityUpdate,
    .lightClientOptimisticUpdate, .blobSidecarsByRange, .blobSidecarsByRoot,
    .dataColumnSidecarsByRange, .dataColumnSidecarsByRoot, .beaconBlocksByHead,
    .executionPayloadEnvelopesByRange, .executionPayloadEnvelopesByRoot]

/-- A protocol and its version. -/
structure ProtocolId where
  /-- The protocol. -/
  protocol : ReqRespProtocol
  /-- The version, from 1. -/
  version : Nat
  deriving DecidableEq, Repr

/-- The ID of a protocol: `/eth2/beacon_chain/req/N/V/ssz_snappy`, with `V` in decimal. -/
def ProtocolId.toString (id : ProtocolId) : String :=
  "/eth2/beacon_chain/req/" ++ id.protocol.name ++ "/" ++ Nat.repr id.version ++ "/ssz_snappy"

/-- The versions of a protocol that a fork defines, oldest first; none before its fork. -/
def ReqRespProtocol.versions (fork : Fork) : ReqRespProtocol → List Nat
  | .status => if .fusaka ≤ fork then [1, 2] else [1]
  | .goodbye | .ping => [1]
  | .beaconBlocksByRange | .beaconBlocksByRoot => if .altair ≤ fork then [1, 2] else [1]
  | .metadata =>
    if .fusaka ≤ fork then [1, 2, 3] else if .altair ≤ fork then [1, 2] else [1]
  | .lightClientBootstrap | .lightClientUpdatesByRange | .lightClientFinalityUpdate
  | .lightClientOptimisticUpdate => if .altair ≤ fork then [1] else []
  | .blobSidecarsByRange | .blobSidecarsByRoot => if .dencun ≤ fork then [1] else []
  | .dataColumnSidecarsByRange | .dataColumnSidecarsByRoot | .beaconBlocksByHead =>
    if .fusaka ≤ fork then [1] else []
  | .executionPayloadEnvelopesByRange | .executionPayloadEnvelopesByRoot =>
    if .glamsterdam ≤ fork then [1] else []

/-- The protocol IDs of a fork, up to Gloas.

Heze adds the protocol of inclusion lists, which EthLib does not hold yet.

So from Heze there is no list. -/
def protocolIds (fork : Fork) : Option (List ProtocolId) :=
  if .hegota ≤ fork then none
  else some <| ReqRespProtocol.all.flatMap fun protocol =>
    (protocol.versions fork).map fun version => ⟨protocol, version⟩

/-- The protocol and the version that an ID names, if it names one.

The version is written in decimal with no leading zero, and is positive.
-/
def ProtocolId.parse? (text : String) : Option ProtocolId := do
  let rest ← Networking.Gossip.dropPrefix? "/eth2/beacon_chain/req/".toList text.toList
  let body ← Networking.Gossip.dropSuffix? "/ssz_snappy".toList rest
  let protocol ← ReqRespProtocol.all.find? fun p => (p.name ++ "/").toList.isPrefixOf body
  let version ← Networking.Gossip.parseSubnetId (body.drop (protocol.name.length + 1))
  if version = 0 then none else some ⟨protocol, version.toNat⟩

/-- The status of a node, which each peer sends when it connects; Fulu adds a field. -/
structure Status (fork : Fork) where
  /-- The fork digest of the current epoch. -/
  forkDigest : ForkDigest
  /-- The root of the latest finalized checkpoint. -/
  finalizedRoot : Root
  /-- The epoch of the latest finalized checkpoint. -/
  finalizedEpoch : Epoch
  /-- The root of the head block. -/
  headRoot : Root
  /-- The slot of the head block. -/
  headSlot : Slot
  /-- From Fulu: the slot of the earliest block that the node can serve. -/
  earliestAvailableSlot : Since .fusaka fork Slot

instance {fork : Fork} : SszType (Status fork) :=
  .container
    (["fork_digest", "finalized_root", "finalized_epoch", "head_root", "head_slot"] ++
      sinceNames .fusaka fork ["earliest_available_slot"])
    (fun s => (s.forkDigest, s.finalizedRoot, s.finalizedEpoch, s.headRoot, s.headSlot,
      s.earliestAvailableSlot))
    (fun (d, fr, fe, hr, hs, e) => ⟨d, fr, fe, hr, hs, e⟩)

/-- The fork whose status a version of the status protocol carries. -/
def statusFork : Nat → Option Fork
  | 1 => some .phase0
  | 2 => some .fusaka
  | _ => none

/-- The metadata of a node; Altair and Fulu each add a field. -/
structure MetaData (config : Config) (fork : Fork) where
  /-- The sequence number, which grows with each change of the metadata. -/
  seqNumber : UInt64
  /-- The attestation subnets that the node subscribes to. -/
  attnets : Attnets config.ATTESTATION_SUBNET_COUNT
  /-- From Altair: the sync committee subnets that the node subscribes to. -/
  syncnets : Since .altair fork Syncnets
  /-- From Fulu: the number of custody groups of the node. -/
  custodyGroupCount : Since .fusaka fork UInt64

instance {config : Config} {fork : Fork} : SszType (MetaData config fork) :=
  .container
    (["seq_number", "attnets"] ++ sinceNames .altair fork ["syncnets"] ++
      sinceNames .fusaka fork ["custody_group_count"])
    (fun m => (m.seqNumber, m.attnets, m.syncnets, m.custodyGroupCount))
    (fun (s, a, y, c) => ⟨s, a, y, c⟩)

/-- The fork whose metadata a version of the metadata protocol carries. -/
def metadataFork : Nat → Option Fork
  | 1 => some .phase0
  | 2 => some .altair
  | 3 => some .fusaka
  | _ => none

/-- The reason in a goodbye message. -/
inductive GoodbyeReason where
  /-- 1: the client shut down. -/
  | clientShutDown
  /-- 2: the peer is on another network. -/
  | irrelevantNetwork
  /-- 3: a fault or an error. -/
  | faultOrError
  /-- 4 to 127: reserved for later use. -/
  | reserved (code : UInt64)
  /--
  Any other code.

  Codes above 128 are reasons of a client; the text gives no meaning to 0 and 128.
  -/
  | other (code : UInt64)
  deriving DecidableEq, Repr

/-- The reason that a goodbye message carries. -/
def GoodbyeReason.ofCode (code : UInt64) : GoodbyeReason :=
  if code = 1 then .clientShutDown
  else if code = 2 then .irrelevantNetwork
  else if code = 3 then .faultOrError
  else if 4 ≤ code ∧ code ≤ 127 then .reserved code
  else .other code

/-- The code that a goodbye reason stands for. -/
def GoodbyeReason.toCode : GoodbyeReason → UInt64
  | .clientShutDown => 1
  | .irrelevantNetwork => 2
  | .faultOrError => 3
  | .reserved code | .other code => code

/-- A request for the blocks of a range of slots; the step must be 1. -/
structure BeaconBlocksByRangeRequest where
  /-- The first slot. -/
  startSlot : Slot
  /-- The number of slots. -/
  count : UInt64
  /-- The distance between two slots, which the text fixes at 1. -/
  step : UInt64
  deriving DecidableEq, Repr

instance : SszType BeaconBlocksByRangeRequest :=
  .container ["start_slot", "count", "step"] (fun r => (r.startSlot, r.count, r.step))
    (fun (s, c, t) => ⟨s, c, t⟩)

/-- The most blocks in one request: Deneb lowers the limit. -/
def Config.maxRequestBlocks (config : Config) (fork : Fork) : UInt64 :=
  if .dencun ≤ fork then config.MAX_REQUEST_BLOCKS_DENEB else config.MAX_REQUEST_BLOCKS

/-- A request for blocks by the roots of their messages. -/
abbrev BeaconBlocksByRootRequest (config : Config) (fork : Fork) :=
  SszList Root (config.maxRequestBlocks fork).toNat

/-- A request for the light client updates of a range of sync committee periods. -/
structure LightClientUpdatesByRangeRequest where
  /-- The first period. -/
  startPeriod : UInt64
  /-- The number of periods. -/
  count : UInt64
  deriving DecidableEq, Repr

instance : SszType LightClientUpdatesByRangeRequest :=
  .container ["start_period", "count"] (fun r => (r.startPeriod, r.count))
    (fun (s, c) => ⟨s, c⟩)

/-- A request for the blob sidecars of a range of slots. -/
structure BlobSidecarsByRangeRequest where
  /-- The first slot. -/
  startSlot : Slot
  /-- The number of slots. -/
  count : UInt64
  deriving DecidableEq, Repr

instance : SszType BlobSidecarsByRangeRequest :=
  .container ["start_slot", "count"] (fun r => (r.startSlot, r.count)) (fun (s, c) => ⟨s, c⟩)

/-- A request for blob sidecars by the root of their block and their index.

From Electra the limit grows with the blobs of a block. -/
abbrev BlobSidecarsByRootRequest (config : Config) (fork : Fork) :=
  SszList BlobIdentifier (computeMaxRequestBlobSidecars config fork).toNat

/-- A request for the sidecars of some columns in a range of slots. -/
structure DataColumnSidecarsByRangeRequest (preset : Preset) where
  /-- The first slot. -/
  startSlot : Slot
  /-- The number of slots. -/
  count : UInt64
  /-- The indices of the columns. -/
  columns : SszList DataAvailability.ColumnIndex preset.NUMBER_OF_COLUMNS.toNat
  deriving DecidableEq

instance {preset : Preset} : SszType (DataColumnSidecarsByRangeRequest preset) :=
  .container ["start_slot", "count", "columns"] (fun r => (r.startSlot, r.count, r.columns))
    (fun (s, c, l) => ⟨s, c, l⟩)

/-- A request for the sidecars of some columns of some blocks, each block named by its root. -/
abbrev DataColumnSidecarsByRootRequest (preset : Preset) (config : Config) :=
  SszList (DataColumnsByRootIdentifier preset) config.MAX_REQUEST_BLOCKS_DENEB.toNat

/-- A request for blocks along the ancestry of a block root, that block first. -/
structure BeaconBlocksByHeadRequest where
  /-- The root of the newest block. -/
  beaconRoot : Root
  /-- The number of blocks. -/
  count : UInt64
  deriving DecidableEq, Repr

instance : SszType BeaconBlocksByHeadRequest :=
  .container ["beacon_root", "count"] (fun r => (r.beaconRoot, r.count)) (fun (b, c) => ⟨b, c⟩)

/-- From Gloas: a request for the payload envelopes of the blocks in a range of slots. -/
structure ExecutionPayloadEnvelopesByRangeRequest where
  /-- The first slot. -/
  startSlot : Slot
  /-- The number of slots. -/
  count : UInt64
  deriving DecidableEq, Repr

instance : SszType ExecutionPayloadEnvelopesByRangeRequest :=
  .container ["start_slot", "count"] (fun r => (r.startSlot, r.count)) (fun (s, c) => ⟨s, c⟩)

/-- From Gloas: a request for payload envelopes by the roots of their blocks. -/
abbrev ExecutionPayloadEnvelopesByRootRequest (config : Config) :=
  SszList Root config.MAX_REQUEST_PAYLOADS.toNat

/-- The message of an error response, at most 256 bytes. -/
abbrev ErrorMessage := SszList UInt8 256

/--
The fewest epochs back from the current one over which a node must serve blocks.

It covers the time a validator needs to withdraw, plus half the churn quotient.
-/
def Config.computeMinEpochsForBlockRequests (config : Config) : Epoch :=
  config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY + config.CHURN_LIMIT_QUOTIENT / 2

end EthLib.Consensus

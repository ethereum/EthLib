module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config
public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.DataAvailability.Blob
public import EthLib.Consensus.DataAvailability.Column
public import EthLib.Consensus.Types
public import EthLib.Networking.Enr.Consensus
public import EthLib.Networking.Gossip.Topic
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.ReqResp.Messages`

The messages of the request and response protocols of the consensus layer, up to Heze.

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

Heze adds the protocol of inclusion lists, by slot, dependent root and committee seats.
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
  /-- From Heze: the inclusion lists of some seats of the committee of a slot. -/
  | inclusionListsByIndices
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
  | .inclusionListsByIndices => "inclusion_lists_by_indices"

/-- Every protocol: those of Phase 0 in the order of its text, then the later ones by fork. -/
def ReqRespProtocol.all : List ReqRespProtocol :=
  [.status, .goodbye, .beaconBlocksByRange, .beaconBlocksByRoot, .ping, .metadata,
    .lightClientBootstrap, .lightClientUpdatesByRange, .lightClientFinalityUpdate,
    .lightClientOptimisticUpdate, .blobSidecarsByRange, .blobSidecarsByRoot,
    .dataColumnSidecarsByRange, .dataColumnSidecarsByRoot, .beaconBlocksByHead,
    .executionPayloadEnvelopesByRange, .executionPayloadEnvelopesByRoot, .inclusionListsByIndices]

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
  | .inclusionListsByIndices => if .hegota ≤ fork then [1] else []

/-- The protocol IDs of a fork: each protocol with each version that the fork defines. -/
def protocolIds (fork : Fork) : List ProtocolId :=
  -- Each protocol in the order of the list, with each version of the fork, oldest first.
  ReqRespProtocol.all.flatMap fun protocol =>
    (protocol.versions fork).map fun version => ⟨protocol, version⟩

/-- The protocol and the version that an ID names, if it names one.

The version is written in decimal with no leading zero, and is positive.
-/
def ProtocolId.parse? (text : String) : Option ProtocolId := do
  -- The text is `/eth2/beacon_chain/req/`, then a body, then `/ssz_snappy`.
  let rest ← Base.dropPrefix? "/eth2/beacon_chain/req/".toList text.toList
  let body ← Base.dropSuffix? "/ssz_snappy".toList rest
  -- The body starts with the name of a protocol, then `/`.
  --
  -- No name holds `/`, so at most one protocol matches.
  let protocol ← ReqRespProtocol.all.find? fun p => (p.name ++ "/").toList.isPrefixOf body
  -- The rest of the body is the version, in decimal with no leading zero.
  --
  -- It is below `2^64`, a bound of EthLib.
  let version ← Networking.Gossip.parseSubnetId (body.drop (protocol.name.length + 1))
  -- The version is positive.
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
  -- Version 1 carries the status of Phase 0, and version 2 that of Fulu.
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
  -- Version 1 carries the metadata of Phase 0, 2 that of Altair, and 3 that of Fulu.
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
  -- Codes 1, 2 and 3 are a shutdown of the client, an irrelevant network, and a fault or error.
  if code = 1 then .clientShutDown
  else if code = 2 then .irrelevantNetwork
  else if code = 3 then .faultOrError
  -- Codes 4 to 127 are reserved.
  else if 4 ≤ code ∧ code ≤ 127 then .reserved code
  -- Code 0 and codes from 128 on are kept as they are.
  else .other code

/-- The code that a goodbye reason stands for. -/
def GoodbyeReason.toCode : GoodbyeReason → UInt64
  | .clientShutDown => 1
  | .irrelevantNetwork => 2
  | .faultOrError => 3
  | .reserved code | .other code => code

/-- Whether a value lies in the range of a count of values from a start.

The bound is computed without overflow, so a range past the largest value stops there.

Requests by range name their slots or their light client periods this way. -/
def InCountRange (start count value : UInt64) : Prop :=
  -- `x ≤ v < x + n` in natural numbers, for the start `x`, the count `n` and the value `v`.
  start.toNat ≤ value.toNat ∧ value.toNat < start.toNat + count.toNat

instance (start count value : UInt64) : Decidable (InCountRange start count value) :=
  inferInstanceAs (Decidable (_ ∧ _))

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
  -- `MAX_REQUEST_BLOCKS_DENEB` from Deneb, and `MAX_REQUEST_BLOCKS` before it.
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

/-- The most light client updates that a request of a count of periods allows.

The updates query of the Beacon API reads the same limit. -/
def lightClientUpdatesLimit (count : UInt64) : Nat :=
  -- `min(MAX_REQUEST_LIGHT_CLIENT_UPDATES, n)` for the count `n`, where the constant is 128.
  min MAX_REQUEST_LIGHT_CLIENT_UPDATES.toNat count.toNat

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

/-- From Heze: a request for the inclusion lists of some seats of the committee of a slot.

The seats are bits over the committee that the dependent root fixes for that slot. -/
structure InclusionListsByIndicesRequest (preset : Preset) where
  /-- The slot of the lists. -/
  slot : Slot
  /-- The root of the dependent block of the committee. -/
  dependentRoot : Root
  /-- One bit for each seat of the committee, set for each list asked for. -/
  indices : InclusionListBits preset

instance {preset : Preset} : SszType (InclusionListsByIndicesRequest preset) :=
  .container ["slot", "dependent_root", "indices"] (fun r => (r.slot, r.dependentRoot, r.indices))
    (fun (slot, dependentRoot, indices) => ⟨slot, dependentRoot, indices⟩)

/-- From Heze: the inclusion lists of a response, at most the request limit. -/
abbrev SignedInclusionLists (config : Config) :=
  SszList SignedInclusionList config.MAX_REQUEST_INCLUSION_LIST.toNat

/-- The message of an error response, at most 256 bytes. -/
abbrev ErrorMessage := SszList UInt8 256

/--
The fewest epochs back from the current one over which a node must serve blocks, at a fork.

It covers the time a validator needs to withdraw, plus half of a churn quotient, rounded down.

Before Gloas, that quotient is `CHURN_LIMIT_QUOTIENT`.

From Gloas, it comes from the weak subjectivity arithmetic of [EIP-8061].

Let `E` be `CHURN_LIMIT_QUOTIENT_GLOAS` and `C` be `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`.

For a large validator set the capped activation churn is negligible, so it drops out.

The exit churn is the stake over `E`, and the consolidation churn is the stake over `C`.

Exits weigh 2/3 against 1 for consolidations.

The stake over that weighted churn is `3 * E * C / (2 * C + 3 * E)`, rounded down.

The configuration values are 64-bit, so a sum or product of 2^64 or more is an error.

From Gloas, a zero denominator is an error too, which happens exactly when both quotients are 0.

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061#weak-subjectivity-period
-/
def Config.computeMinEpochsForBlockRequests (config : Config) (fork : Fork) :
    Except ArithError Epoch := do
  if .glamsterdam ≤ fork then
    -- The numerator `3 * E * C`.
    let exitWeight ← Uint64.mulChecked 3 config.CHURN_LIMIT_QUOTIENT_GLOAS
    let numerator ← Uint64.mulChecked exitWeight config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT
    -- The denominator `2 * C + 3 * E`, which reuses the product `3 * E` of the numerator.
    let consolidationWeight ← Uint64.mulChecked 2 config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT
    let denominator ← Uint64.addChecked consolidationWeight exitWeight
    -- `MIN_VALIDATOR_WITHDRAWABILITY_DELAY + floor(floor(3 * E * C / (2 * C + 3 * E)) / 2)`.
    let quotient ← Uint64.divChecked numerator denominator
    Uint64.addChecked config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY (quotient / 2)
  else
    -- `MIN_VALIDATOR_WITHDRAWABILITY_DELAY + floor(CHURN_LIMIT_QUOTIENT / 2)`.
    Uint64.addChecked config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY (config.CHURN_LIMIT_QUOTIENT / 2)

end EthLib.Consensus

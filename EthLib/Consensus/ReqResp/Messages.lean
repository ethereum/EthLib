module

public import EthLib.Base.Fork
public import EthLib.Consensus.Config
public import EthLib.Consensus.Types
public import EthLib.Networking.Enr.Consensus
public import EthLib.Networking.Gossip.Topic
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.ReqResp.Messages`

The messages of the request and response protocols of the consensus layer, up to Fulu.

Each protocol has an ID, the string `/eth2/beacon_chain/req/N/V/ssz_snappy`.

`N` names the protocol and `V` is its version, a positive integer.

Phase 0 has the status, goodbye, block range, block root, ping and metadata protocols.

Altair adds a second version of the block and metadata protocols.

Fulu adds a second version of the status protocol and a third of the metadata protocol.

The protocols of blobs, data columns and light clients are not part of this module.
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
  deriving DecidableEq, Repr

/-- The name of a protocol in its ID. -/
def ReqRespProtocol.name : ReqRespProtocol → String
  | .status => "status"
  | .goodbye => "goodbye"
  | .beaconBlocksByRange => "beacon_blocks_by_range"
  | .beaconBlocksByRoot => "beacon_blocks_by_root"
  | .ping => "ping"
  | .metadata => "metadata"

/-- Every protocol, in the order of the Phase 0 text. -/
def ReqRespProtocol.all : List ReqRespProtocol :=
  [.status, .goodbye, .beaconBlocksByRange, .beaconBlocksByRoot, .ping, .metadata]

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

/-- The versions of a protocol that a fork defines, oldest first. -/
def ReqRespProtocol.versions (fork : Fork) : ReqRespProtocol → List Nat
  | .status => if .fusaka ≤ fork then [1, 2] else [1]
  | .goodbye | .ping => [1]
  | .beaconBlocksByRange | .beaconBlocksByRoot => if .altair ≤ fork then [1, 2] else [1]
  | .metadata =>
    if .fusaka ≤ fork then [1, 2, 3] else if .altair ≤ fork then [1, 2] else [1]

/-- The protocol IDs of a fork. -/
def protocolIds (fork : Fork) : List ProtocolId :=
  ReqRespProtocol.all.flatMap fun protocol =>
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

/-- The message of an error response, at most 256 bytes. -/
abbrev ErrorMessage := SszList UInt8 256

/--
The fewest epochs back from the current one over which a node must serve blocks.

It covers the time a validator needs to withdraw, plus half the churn quotient.
-/
def Config.computeMinEpochsForBlockRequests (config : Config) : Epoch :=
  config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY + config.CHURN_LIMIT_QUOTIENT / 2

end EthLib.Consensus

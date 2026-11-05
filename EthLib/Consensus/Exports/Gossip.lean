module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Gossip.Topics

/-!
# `Exports.Gossip`

C-ABI exports of the gossip topics of a fork and of the subnet of a message.

A list comes back as JSON, and a subnet as an integer, or as the code and the message of its error.

A malformed node ID, an unknown name or a fork with no topic set has code 0.

A preset and a configuration are named together, by `mainnet` or `minimal`.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result forkOfName)

open Lean Base Networking.Gossip

/-- A subnet, or the code and the message of its error. -/
def subnetResult {α : Type} (result : Except (SubnetError ShuffleError) α) : Result α :=
  result.mapError fun e => (e.code, s!"subnet rejected: {reprStr e}")

/-- The names of the gossip topics of a fork, as a JSON list of strings. -/
@[export eth_consensus_gossip_topics]
def gossipTopicsExport (name fork : ByteArray) : Result ByteArray := do
  let config ← configOf (← nameOf name)
  let fork ← forkOfName fork
  let some topics := config.gossipTopics fork
    | throw (0, s!"the gossip topics of {fork.name} are not yet specified")
  return jsonBytes (toJson (topics.map GossipTopic.name))

/-- The subnet of an attestation, from the committees per slot, its slot and its committee. -/
@[export eth_consensus_compute_subnet_for_attestation]
def computeSubnetForAttestationExport (name : ByteArray)
    (committeesPerSlot slot committeeIndex : UInt64) : Result UInt64 := do
  let name ← nameOf name
  subnetResult (computeSubnetForAttestation (← presetOf name) (← configOf name)
    committeesPerSlot slot committeeIndex)

/-- The subnet of a blob sidecar at a fork, from its blob index. -/
@[export eth_consensus_compute_subnet_for_blob_sidecar]
def computeSubnetForBlobSidecarExport (name fork : ByteArray) (blobIndex : UInt64) :
    Result UInt64 := do
  let config ← configOf (← nameOf name)
  subnetResult (computeSubnetForBlobSidecar config (← forkOfName fork) blobIndex)

/-- The subnet of a data column sidecar, from its column index. -/
@[export eth_consensus_compute_subnet_for_data_column_sidecar]
def computeSubnetForDataColumnSidecarExport (name : ByteArray) (columnIndex : UInt64) :
    Result UInt64 := do
  subnetResult (computeSubnetForDataColumnSidecar (← configOf (← nameOf name)) columnIndex)

/-- The attestation subnets of a node ID of 32 bytes in an epoch, as a JSON list. -/
@[export eth_consensus_compute_subscribed_subnets]
def computeSubscribedSubnetsExport (name nodeId : ByteArray) (epoch : UInt64) :
    Result ByteArray := do
  let name ← nameOf name
  unless nodeId.size = 32 do throw (0, "a node ID is 32 bytes")
  let id : NodeID := BitVec.ofNat 256 (bytesToNat nodeId.toList)
  let subnets ← subnetResult
    (computeSubscribedSubnets (← presetOf name) (← configOf name) id epoch)
  return jsonBytes (toJson subnets)

end EthLib.Consensus.Exports

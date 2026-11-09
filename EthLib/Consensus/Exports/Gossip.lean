module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Consensus.Gossip.Topics

/-!
# `Exports.Gossip`

C-ABI exports of the gossip topics of a fork and of the subnet of a message.

The topics and the subscribed subnets take and return typed Python values.

A subnet comes back as an integer, or as the code and the message of its error.

A node ID of 2^256 or more, an unknown name or a fork with no rules yet has code 0.

The bound of a topic that the fork does not list has the code of its error.

A preset and a configuration are named together, by `mainnet` or `minimal`.
-/

public section

namespace EthLib.Consensus.Exports

open EthLib.Exports (Result PyValue pyExport forkOfName forkUpTo)

open Lean Base Networking.Gossip

/-- A subnet, or the code and the message of its error. -/
def subnetResult {α : Type} (result : Except (SubnetError ShuffleError) α) : Result α :=
  result.mapError fun e => (e.code, s!"subnet rejected: {reprStr e}")

/-- The names of the gossip topics of a fork. -/
def gossipTopicsOf (args : String × String) : Result (List String) := do
  let (name, fork) := args
  let config ← configOf name
  let fork ← forkUpTo .hegota fork.toUTF8
  return (config.gossipTopics fork).map GossipTopic.name

/-- The names of the gossip topics of a fork, as a list.

The arguments are the name of the configuration and the name of the fork. -/
@[export eth_consensus_gossip_topics]
def gossipTopicsExport (args : PyValue) : Result PyValue := pyExport gossipTopicsOf args

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

/-- The attestation subnets of a node ID in an epoch. -/
def computeSubscribedSubnetsOf (args : String × NodeID × UInt64) : Result (List UInt64) := do
  let (name, id, epoch) := args
  subnetResult (computeSubscribedSubnets (← presetOf name) (← configOf name) id epoch)

/-- The attestation subnets of a node ID in an epoch, as a list.

The arguments are the name of the preset and the configuration, the node ID and the epoch. -/
@[export eth_consensus_compute_subscribed_subnets]
def computeSubscribedSubnetsExport (args : PyValue) : Result PyValue :=
  pyExport computeSubscribedSubnetsOf args

/-- The largest length of the payload of a gossip topic at a fork. -/
@[export eth_consensus_gossip_topic_bound]
def gossipTopicBoundExport (name fork topic : ByteArray) : Result UInt64 := do
  let name ← nameOf name
  let preset ← presetOf name
  let config ← configOf name
  let fork ← forkUpTo .hegota fork
  let topicName ← nameOf topic
  let some topic := GossipTopic.ofName? topicName | throw (0, s!"{topicName} names no topic")
  unless (config.gossipTopics fork).contains topic do
    throw (BoundsError.topicNotAtFork.code, s!"{topicName} is not a topic of {fork.name}")
  let some bound := topicBound preset config fork topic
    | throw (BoundsError.topicNotAtFork.code, s!"{topicName} is not a topic of {fork.name}")
  return bound

end EthLib.Consensus.Exports

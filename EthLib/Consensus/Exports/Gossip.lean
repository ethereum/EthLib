module

public import EthLib.Base.Exports
public import EthLib.Consensus.Exports.Parameters
public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Consensus.Gossip.Decode
public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Consensus.Gossip.Topics
public import EthLib.Networking.Exports.Gossip

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

open EthLib.Exports (ExportError Result PyValue pyExport forkOfName forkUpTo rejectArgument
  toResult)

open Lean Base Networking.Gossip

/-- A subnet error reaches Python with its code and its printed form. -/
instance : ExportError (SubnetError ShuffleError) where
  code := SubnetError.code
  message := reprStr

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
  toResult "subnet rejected" (computeSubnetForAttestation (← presetOf name) (← configOf name)
    committeesPerSlot slot committeeIndex)

/-- The subnet of a blob sidecar at a fork, from its blob index. -/
@[export eth_consensus_compute_subnet_for_blob_sidecar]
def computeSubnetForBlobSidecarExport (name fork : ByteArray) (blobIndex : UInt64) :
    Result UInt64 := do
  let config ← configOf (← nameOf name)
  toResult "subnet rejected" (computeSubnetForBlobSidecar config (← forkOfName fork) blobIndex)

/-- The subnet of a data column sidecar, from its column index. -/
@[export eth_consensus_compute_subnet_for_data_column_sidecar]
def computeSubnetForDataColumnSidecarExport (name : ByteArray) (columnIndex : UInt64) :
    Result UInt64 := do
  toResult "subnet rejected"
    (computeSubnetForDataColumnSidecar (← configOf (← nameOf name)) columnIndex)

/-- The attestation subnets of a node ID in an epoch. -/
def computeSubscribedSubnetsOf (args : String × NodeID × UInt64) : Result (List UInt64) := do
  let (name, id, epoch) := args
  toResult "subnet rejected" (computeSubscribedSubnets (← presetOf name) (← configOf name) id epoch)

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
  let some topic := GossipTopic.ofName? topicName
    | rejectArgument none s!"{topicName} names no topic"
  -- Only a topic that the fork lists has a bound.
  let some bound := topicBound preset config fork topic
    | throw (BoundsError.topicNotAtFork topicName fork).fault
  return bound

/-- The code and the message of an error of a gossip message.

An error of bounds keeps its code, from 301, and the topic and payload errors keep theirs. -/
instance : ExportError GossipDecodeError where
  code
    | .topic error => ExportError.code error
    | .bounds error => error.code
    | .payload error => ExportError.code error
  message
    | .topic error => ExportError.message error
    | .bounds error => toString error
    | .payload error => ExportError.message error

/-- The payload of a gossip message at the fork of its topic's digest, with that fork and topic. -/
def gossipDecodeAtTopicOf (args : String × Option PyValue × Root × String × ByteArray) :
    Result (String × String × ByteArray) := do
  -- The name of the preset and the configuration, its replacements and the genesis validators root.
  --
  -- Then the topic string and the data of the message.
  let (name, replacements, genesisValidatorsRoot, topicString, data) := args
  let preset ← presetOf name
  let config ← configWithValue name replacements
  let (fork, topic, payload) ←
    toResult none (decodeGossipAtTopic preset config genesisValidatorsRoot topicString data)
  return (fork.name, topic.name, payload)

/-- The payload of a gossip message at the fork of its topic's digest, with that fork and the topic.

The configuration of the name holds, with the replacements that a `dict` gives. -/
@[export eth_consensus_gossip_decode_at_topic]
def gossipDecodeAtTopicExport (args : PyValue) : Result PyValue :=
  pyExport gossipDecodeAtTopicOf args

end EthLib.Consensus.Exports

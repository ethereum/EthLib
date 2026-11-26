module

public import EthLib.Consensus.ForkDigest
public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Gossip.Topic

/-!
# `Consensus.Gossip.Decode`

The data of a gossip message, decoded at the bound of its topic at the fork of the topic's digest.

A topic string carries a fork digest, and the fork of the first epoch with it fixes the type.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Networking.Gossip

/-- Why the data of a gossip message does not decode. -/
inductive GossipDecodeError where
  /-- The topic string is not of the form `/eth2/D/N/ssz_snappy`. -/
  | topic (error : TopicError)
  /-- The topic has no bound: its digest names no scheduled fork, or it is no topic of the fork. -/
  | bounds (error : BoundsError)
  /-- The data is not the Snappy block of a payload within the bound of the topic. -/
  | payload (error : PayloadError)
  deriving Repr, DecidableEq

/-- The data of a gossip message, with the fork that the topic's digest names and the topic.

It neither checks that the node subscribes to the topic nor deserializes the payload. -/
def decodeGossipAtTopic (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (topicString : String) (data : ByteArray) :
    Except GossipDecodeError (Fork × GossipTopic × ByteArray) := do
  -- The topic is `/eth2/D/N/ssz_snappy`, with the fork digest `D` and the name `N`.
  let (digest, name) ← (parseTopic topicString).mapError .topic
  -- The fork of the first epoch with the digest selects the types of the topic.
  let some start := forkOfDigest config genesisValidatorsRoot digest
    | throw (.bounds (.unknownDigest digest))
  -- An epoch has at least two slots, so the epoch of a slot is below the far future epoch.
  --
  -- So no message has a digest that only the far future epoch has.
  if start = FAR_FUTURE_EPOCH then throw (.bounds (.unscheduledDigest digest))
  let fork := config.forkAtEpoch start
  -- The name must be that of a topic of the fork.
  let some topic := GossipTopic.ofName? name | throw (.bounds (.topicNotAtFork name fork))
  unless (config.gossipTopics fork).contains topic do throw (.bounds (.topicNotAtFork name fork))
  -- A topic without a message type has no bound, and the data is refused.
  let some bound := topicBound preset config fork topic
    | throw (.bounds (.topicNotAtFork name fork))
  -- The data is the Snappy block of a payload within the payload cap and the bound of the topic.
  let payload ← (decodePayload config.MAX_PAYLOAD_SIZE bound data).mapError .payload
  return (fork, topic, payload)

end EthLib.Consensus

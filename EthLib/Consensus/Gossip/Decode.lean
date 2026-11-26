module

public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Gossip.Topic

/-!
# `Consensus.Gossip.Decode`

The payload of a gossip message, decoded at its topic's bound at the fork of the topic's digest.

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

/-- The payload of a gossip message, with the fork that the topic's digest names and the topic.

When the digests of the chain identify their forks, that fork is the fork of the digest's epoch.

It checks neither the node's subscriptions, nor the current epoch, nor the epoch of the payload.

It does not deserialize the payload. -/
def decodeGossipAtTopic (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (topicString : String) (data : ByteArray) :
    Except GossipDecodeError (Fork × GossipTopic × ByteArray) := do
  -- The topic is `/eth2/D/N/ssz_snappy`, with the fork digest `D` and the name `N`.
  let (digest, name) ← (parseTopic topicString).mapError .topic
  -- The fork of the first epoch with the digest, below the far future epoch, selects the types.
  let fork ← (forkOfScheduledDigest config genesisValidatorsRoot digest).mapError .bounds
  -- The name must be that of a topic of the fork, and only such a topic has a bound.
  let some topic := GossipTopic.ofName? name | throw (.bounds (.topicNotAtFork name fork))
  let some bound := topicBound preset config fork topic
    | throw (.bounds (.topicNotAtFork name fork))
  -- The data is the Snappy block of a payload within the payload cap and the bound of the topic.
  let payload ← (decodePayload config.MAX_PAYLOAD_SIZE bound data).mapError .payload
  return (fork, topic, payload)

end EthLib.Consensus

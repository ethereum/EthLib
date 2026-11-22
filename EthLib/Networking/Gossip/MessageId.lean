module

public import EthLib.Base.Fork
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Networking.Gossip.Cache
public import EthLib.Networking.Snappy.Block
public import EthLib.Serialization.Ssz.Codec.Serialize

/-!
# `Networking.Gossip.MessageId`

The message ID of gossip on the consensus layer.

Gossipsub is the publish-subscribe protocol of the consensus layer.

It drops a message whose ID is still in its cache of seen IDs.

The pubsub interface of libp2p lets the application choose the function that computes that ID:
<https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/README.md#message-identification>

The consensus layer computes it from the content.

So a second copy of the same data on one topic gets the same ID and is dropped.

The data of a message is Snappy-compressed.

One payload, the uncompressed content, has many compressions.

Data decompresses when the Snappy block decoder accepts it.

That decoder reads at most five preamble bytes, which hold any length up to 2^32 - 1.

Data that decompresses is hashed as its payload.

So on one topic, all data that decompresses to one payload gets one ID.

Clients reject messages over a size limit, as a separate check.

The message ID rules do not mention that limit, so the ID does not apply it.
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The domain of data that does not decompress. -/
def MESSAGE_DOMAIN_INVALID_SNAPPY : Vector UInt8 4 := #v[0x00, 0x00, 0x00, 0x00]

/-- The domain of data that decompresses. -/
def MESSAGE_DOMAIN_VALID_SNAPPY : Vector UInt8 4 := #v[0x01, 0x00, 0x00, 0x00]

namespace Phase0

/-- The bytes Phase 0 hashes: the domain, then `bytes`, the payload or the raw data. -/
def hashInput (domain : Vector UInt8 4) (bytes : ByteArray) : ByteArray :=
  -- Phase 0: the input is `d || b`, for the domain `d` and the bytes `b`.
  ⟨domain.toArray⟩ ++ bytes

end Phase0

namespace Altair

/-- The bytes Altair hashes: the domain, the topic length, the topic, then `bytes`.

The bytes are the payload or the raw data.

The length marks where the topic ends and the bytes start.
-/
def hashInput (domain : Vector UInt8 4) (topic bytes : ByteArray) : ByteArray :=
  -- From Altair: the input is `d || LE64(|t|) || t || b`, for the topic `t`.
  --
  -- `LE64(n)` is the 64-bit integer `n` as eight little-endian bytes.
  --
  -- A topic of 2^64 bytes or more has no 64-bit length, and the bytes keep the low 64 bits of it.
  --
  -- The source fails there instead, but no byte string in memory reaches that length.
  ⟨domain.toArray⟩ ++ ⟨Serialization.Ssz.uintBytes 8 topic.size⟩ ++ topic ++ bytes

end Altair

/-- The bytes hashed for a message on a topic of a fork: the Phase 0 form, or from Altair on. -/
def hashInput (fork : Base.Fork) (domain : Vector UInt8 4) (topic bytes : ByteArray) :
    ByteArray :=
  -- The rule is the one of the fork whose digest the topic carries.
  --
  -- So a message on a topic with the Phase 0 fork digest keeps the Phase 0 rule.
  --
  -- No fork after Altair changes the rule.
  if fork < .altair then Phase0.hashInput domain bytes else Altair.hashInput domain topic bytes

/--
The message ID of a message on a topic of a fork: the first 20 bytes of a SHA-256 digest.

A missing topic or data field of the protobuf message is the empty byte string.
-/
def messageId (fork : Base.Fork) (topic data : ByteArray) : MessageId :=
  match Snappy.decompress data with
  -- Data that decompresses to the payload `p`: the first 20 bytes of SHA-256 of the input.
  --
  -- There `b = p` and the domain is `d = 01 00 00 00`.
  | .ok payload =>
    (Cryptography.Hash.Sha256.hash32
      (hashInput fork MESSAGE_DOMAIN_VALID_SNAPPY topic payload)).take 20
  -- Otherwise the same, with `b` the raw data and the domain `d = 00 00 00 00`.
  --
  -- The two domains tell a payload apart from raw data with the same bytes.
  | .error _ =>
    (Cryptography.Hash.Sha256.hash32
      (hashInput fork MESSAGE_DOMAIN_INVALID_SNAPPY topic data)).take 20

end EthLib.Networking.Gossip

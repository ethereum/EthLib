module

public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Networking.Snappy.Block
public import EthLib.Serialization.Ssz.Codec.Serialize

/-!
# `Networking.Gossip.MessageId`

The message ID of gossip on the consensus layer.

Gossipsub is the publish-subscribe protocol of the consensus layer.

It drops a message whose ID is still in its cache of seen IDs.

The consensus layer computes that ID from the content.

So a second copy of the same data on one topic gets the same ID and is dropped.

The data of a message is Snappy-compressed.

One payload, the uncompressed content, has many compressions.

Data decompresses when the Snappy block decoder accepts it.

That decoder reads at most five preamble bytes, which hold any length up to 2^32 - 1.

Data that decompresses is hashed as its payload.

So on one topic, all data that decompresses to one payload gets one ID.

Data that does not decompress is hashed as it is.

A four-byte domain at the start of the hash input tells the two cases apart.

From Altair on, the ID also hashes the topic, after its length:

```text
Phase 0:  SHA256( domain: 4 | bytes )[:20]
Altair:   SHA256( domain: 4 | topic length: 8 | topic | bytes )[:20]
```

The bytes are the payload when the data decompresses, and the data itself otherwise.

The topic length is little-endian.

Messages on a topic with the Phase 0 fork digest keep the Phase 0 rule, so both rules are here.

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
  ⟨domain.toArray⟩ ++ bytes

/-- The message ID of Phase 0: the first 20 bytes of a SHA-256 digest.

Data that decompresses is hashed as its payload, under the domain `01 00 00 00`.

Other data is hashed as it is, under the domain `00 00 00 00`.
-/
def messageId (data : ByteArray) : ByteArray :=
  match Snappy.decompress data with
  | .ok payload => (Cryptography.Hash.sha256 (hashInput MESSAGE_DOMAIN_VALID_SNAPPY payload)).extract 0 20
  | .error _ => (Cryptography.Hash.sha256 (hashInput MESSAGE_DOMAIN_INVALID_SNAPPY data)).extract 0 20

end Phase0

namespace Altair

/-- The bytes Altair hashes: the domain, the topic length, the topic, then `bytes`.

The bytes are the payload or the raw data.

The length of the topic is a 64-bit integer, written as eight little-endian bytes.

A topic of 2^64 bytes or more has no 64-bit length, and the bytes keep the low 64 bits of it.

The length marks where the topic ends and the bytes start.
-/
def hashInput (domain : Vector UInt8 4) (topic bytes : ByteArray) : ByteArray :=
  ⟨domain.toArray⟩ ++ ⟨Serialization.Ssz.uintBytes 8 topic.size⟩ ++ topic ++ bytes

/-- The message ID from Altair on: the first 20 bytes of a SHA-256 digest.

Data that decompresses is hashed as its payload, under the domain `01 00 00 00`.

Other data is hashed as it is, under the domain `00 00 00 00`.

A missing topic or data field of the protobuf message is the empty byte string.
-/
def messageId (topic data : ByteArray) : ByteArray :=
  match Snappy.decompress data with
  | .ok payload => (Cryptography.Hash.sha256 (hashInput MESSAGE_DOMAIN_VALID_SNAPPY topic payload)).extract 0 20
  | .error _ => (Cryptography.Hash.sha256 (hashInput MESSAGE_DOMAIN_INVALID_SNAPPY topic data)).extract 0 20

end Altair

end EthLib.Networking.Gossip

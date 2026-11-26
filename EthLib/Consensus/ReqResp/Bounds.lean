module

public import EthLib.Consensus.ReqResp.Messages
public import EthLib.Networking.ReqResp.Bounds

/-!
# `Consensus.ReqResp.Bounds`

The SSZ type of the request of each protocol, and the length bounds of its payload.

Each protocol has one request type, the same at every version, except the status protocol.

- Status carries the status of the fork of its version.
- Goodbye and ping carry a 64-bit integer.
- Blocks by range, blobs by range and light client updates by range carry their range request.
- Blocks by root and blobs by root carry a list of roots or identifiers, with the limit of the fork.
- A light client bootstrap carries a block root.
- Data column sidecars by range and by root carry requests limited by the preset and the config.
- Blocks by head carries a block root and a count.
- From Gloas, payload envelopes by range carry a range, and by root a list of block roots.
- From Heze, inclusion lists by indices carry a slot, a dependent root and seat bits.
- Metadata and the two light client update protocols carry no request.

The type of a response depends on the context bytes of each chunk, so it is not part of this module.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The SSZ type of the request of a protocol version at a fork, if the request has content.

The status protocol carries the status of the fork of its version, and an unknown version has none.

It does not check that the fork defines the version. -/
def requestDesc (preset : Preset) (config : Config) (fork : Fork) (id : ProtocolId) :
    Option Desc :=
  match id.protocol with
  | .status => (statusFork id.version).map fun f => SszType.desc (Status f)
  | .goodbye | .ping => some (SszType.desc UInt64)
  | .beaconBlocksByRange => some (SszType.desc BeaconBlocksByRangeRequest)
  | .beaconBlocksByRoot => some (SszType.desc (BeaconBlocksByRootRequest config fork))
  | .metadata | .lightClientFinalityUpdate | .lightClientOptimisticUpdate => none
  | .lightClientBootstrap => some (SszType.desc Root)
  | .lightClientUpdatesByRange => some (SszType.desc LightClientUpdatesByRangeRequest)
  | .blobSidecarsByRange => some (SszType.desc BlobSidecarsByRangeRequest)
  | .blobSidecarsByRoot => some (SszType.desc (BlobSidecarsByRootRequest config fork))
  | .dataColumnSidecarsByRange => some (SszType.desc (DataColumnSidecarsByRangeRequest preset))
  | .dataColumnSidecarsByRoot =>
    some (SszType.desc (DataColumnSidecarsByRootRequest preset config))
  | .beaconBlocksByHead => some (SszType.desc BeaconBlocksByHeadRequest)
  | .executionPayloadEnvelopesByRange =>
    some (SszType.desc ExecutionPayloadEnvelopesByRangeRequest)
  | .executionPayloadEnvelopesByRoot =>
    some (SszType.desc (ExecutionPayloadEnvelopesByRootRequest config))
  | .inclusionListsByIndices => some (SszType.desc (InclusionListsByIndicesRequest preset))

/-- The length bounds of the request payload of a protocol version at a fork, if it has one. -/
def requestBounds (preset : Preset) (config : Config) (fork : Fork) (id : ProtocolId) :
    Option (UInt64 × UInt64) :=
  (requestDesc preset config fork id).map (Networking.ReqResp.payloadBounds config.MAX_PAYLOAD_SIZE)

/-- Why a protocol or a topic has no length bound. -/
inductive BoundsError where
  /-- The fork does not define the protocol version.

  The error gives the protocol ID and the fork. -/
  | notAtFork (protocol : String) (fork : Fork)
  /-- The protocol version, whose ID the error gives, carries no request. -/
  | noRequest (protocol : String)
  /-- The fork does not list the gossip topic.

  The error gives the name of the topic and the fork. -/
  | topicNotAtFork (topic : String) (fork : Fork)
  /-- No epoch of the chain has the digest of a successful response chunk.

  So the digest names no fork, and the chunk has no type and no bounds. -/
  | unknownDigest (digest : ForkDigest)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor.

The codes start at 301, since the consensus errors of the bindings share one class.

A new constructor takes a new code, so that each code keeps its meaning.

Code 304 stays unused, so that no code takes a second meaning. -/
def BoundsError.code : BoundsError → UInt32
  | .notAtFork .. => 301
  | .noRequest _ => 302
  | .topicNotAtFork .. => 303
  | .unknownDigest _ => 305

/-- The message of an error, with the protocol or the topic and the fork. -/
instance : ToString BoundsError where
  toString
    | .notAtFork protocol fork => s!"{protocol} is not a protocol of {fork.name}"
    | .noRequest protocol => s!"{protocol} carries no request"
    | .topicNotAtFork topic fork => s!"{topic} is not a topic of {fork.name}"
    | .unknownDigest digest => s!"no epoch of the chain has the digest {hexString digest.toList}"

/-- The code and the message of an error, as the C exports return them. -/
def BoundsError.fault (error : BoundsError) : UInt32 × String :=
  (error.code, toString error)

end EthLib.Consensus

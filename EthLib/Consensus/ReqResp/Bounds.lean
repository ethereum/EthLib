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

/-- The length bounds of the request payload of a protocol version at a fork, if it has one. -/
def requestBounds (preset : Preset) (config : Config) (fork : Fork) (id : ProtocolId) :
    Option (UInt64 × UInt64) :=
  (requestDesc preset config fork id).map Networking.ReqResp.payloadBounds

end EthLib.Consensus

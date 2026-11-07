module

public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.LightClient.Containers
public import EthLib.Consensus.ReqResp.Bounds

/-!
# `Consensus.ReqResp.ResponseBounds`

The SSZ type of one successful response chunk of each protocol, and the bounds of its length.

A protocol that sends context bytes names the fork of each chunk with them.

The caller reads that fork from the context bytes and passes it as `chunkFork`.

This module does not compute it, and it does not check that the protocol exists at that fork.

- Status carries the status of the fork of its version.
- Goodbye and ping carry a 64-bit integer.
- Metadata carries the metadata of the fork of its version.
- Blocks by range and by root carry a Phase 0 block at version 1, and a block of `chunkFork` later.
- Blocks by head carries a block of `chunkFork`.
- The four light client protocols carry their bootstrap or update of `chunkFork`.
- Blob sidecars by range and by root carry a blob sidecar.
- Data column sidecars by range and by root carry a data column sidecar of `chunkFork`.
- From Gloas, payload envelopes by range and by root carry a signed envelope of `chunkFork`.

An unknown version of the status or metadata protocol has no type.

An error chunk carries an error message instead, which the chunk decoder bounds by itself.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The SSZ type of one successful response chunk of a protocol version, for the fork of the chunk.

`chunkFork` is the fork that the context bytes of the chunk name, which the caller reads. -/
def responseDesc (preset : Preset) (config : Config) (chunkFork : Fork) (id : ProtocolId) :
    Option Desc :=
  match id.protocol with
  | .status => (statusFork id.version).map fun f => SszType.desc (Status f)
  | .goodbye | .ping => some (SszType.desc UInt64)
  | .metadata => (metadataFork id.version).map fun f => SszType.desc (MetaData config f)
  | .beaconBlocksByRange | .beaconBlocksByRoot =>
    some (SszType.desc (SignedBeaconBlock preset (if id.version = 1 then .phase0 else chunkFork)))
  | .beaconBlocksByHead => some (SszType.desc (SignedBeaconBlock preset chunkFork))
  | .lightClientBootstrap => some (SszType.desc (LightClientBootstrap preset chunkFork))
  | .lightClientUpdatesByRange => some (SszType.desc (LightClientUpdate preset chunkFork))
  | .lightClientFinalityUpdate => some (SszType.desc (LightClientFinalityUpdate preset chunkFork))
  | .lightClientOptimisticUpdate =>
    some (SszType.desc (LightClientOptimisticUpdate preset chunkFork))
  | .blobSidecarsByRange | .blobSidecarsByRoot => some (SszType.desc (BlobSidecar preset))
  | .dataColumnSidecarsByRange | .dataColumnSidecarsByRoot =>
    some (SszType.desc (DataColumnSidecar preset chunkFork))
  | .executionPayloadEnvelopesByRange | .executionPayloadEnvelopesByRoot =>
    some (SszType.desc (SignedExecutionPayloadEnvelope preset chunkFork))

/-- The length bounds of one successful response chunk of a protocol version, for its fork. -/
def responseBounds (preset : Preset) (config : Config) (chunkFork : Fork) (id : ProtocolId) :
    Option (UInt64 × UInt64) :=
  (responseDesc preset config chunkFork id).map Networking.ReqResp.payloadBounds

end EthLib.Consensus

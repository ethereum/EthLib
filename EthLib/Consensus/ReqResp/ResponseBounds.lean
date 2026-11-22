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
- From Heze, inclusion lists by indices carry a signed inclusion list.

An unknown version of the status or metadata protocol has no type.

An error chunk carries an error message instead, which the chunk decoder bounds by itself.

From Gloas, the networking specification also sets a size limit on the chunks of some protocols.

[EIP-7688](https://eips.ethereum.org/EIPS/eip-7688#network-message-size-bounds) asks for them.

- Data column sidecars by range and by root have one from Gloas, from the largest blob limit.
- Inclusion lists by indices have one from Heze, a preset value.

The largest length of a chunk is that of its type, or the size limit if that is lower.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The SSZ type of one successful response chunk of a protocol version, for the fork of the chunk.

`chunkFork` is the fork that the context bytes of the chunk name, which the caller reads. -/
def responseDesc (preset : Preset) (config : Config) (chunkFork : Fork) (id : ProtocolId) :
    Option Desc :=
  match id.protocol with
  -- Status: the status of the fork of its version, and no type for an unknown version.
  | .status => (statusFork id.version).map fun f => SszType.desc (Status f)
  -- Goodbye and ping: a 64-bit integer.
  | .goodbye | .ping => some (SszType.desc UInt64)
  -- Metadata: the metadata of the fork of its version, and no type for an unknown version.
  | .metadata => (metadataFork id.version).map fun f => SszType.desc (MetaData config f)
  -- Blocks by range and by root: a Phase 0 block at version 1, and a block of the chunk fork later.
  | .beaconBlocksByRange | .beaconBlocksByRoot =>
    some (SszType.desc (SignedBeaconBlock preset (if id.version = 1 then .phase0 else chunkFork)))
  -- Blocks by head: a block of the chunk fork.
  | .beaconBlocksByHead => some (SszType.desc (SignedBeaconBlock preset chunkFork))
  -- The light client protocols: the bootstrap or the update of the chunk fork.
  | .lightClientBootstrap => some (SszType.desc (LightClientBootstrap preset chunkFork))
  | .lightClientUpdatesByRange => some (SszType.desc (LightClientUpdate preset chunkFork))
  | .lightClientFinalityUpdate => some (SszType.desc (LightClientFinalityUpdate preset chunkFork))
  | .lightClientOptimisticUpdate =>
    some (SszType.desc (LightClientOptimisticUpdate preset chunkFork))
  -- Blob sidecars: a blob sidecar, the same type at each fork.
  | .blobSidecarsByRange | .blobSidecarsByRoot => some (SszType.desc (BlobSidecar preset))
  -- Data column sidecars: a column sidecar of the chunk fork.
  | .dataColumnSidecarsByRange | .dataColumnSidecarsByRoot =>
    some (SszType.desc (DataColumnSidecar preset chunkFork))
  -- Payload envelopes: a signed envelope of the chunk fork.
  | .executionPayloadEnvelopesByRange | .executionPayloadEnvelopesByRoot =>
    some (SszType.desc (SignedExecutionPayloadEnvelope preset chunkFork))
  -- Inclusion lists: a signed inclusion list.
  | .inclusionListsByIndices => some (SszType.desc SignedInclusionList)

/-- The size limit that the networking specification sets on the chunks of a protocol, at a fork.

Data column sidecars have one from Gloas, and inclusion lists from Heze. -/
def ReqRespProtocol.sizeLimit (preset : Preset) (config : Config) (chunkFork : Fork) :
    ReqRespProtocol → Option UInt64
  -- Data column sidecars, from Gloas: the largest size of a column sidecar.
  | .dataColumnSidecarsByRange | .dataColumnSidecarsByRoot =>
    if .glamsterdam ≤ chunkFork then some (computeMaxDataColumnSidecarSize preset config) else none
  -- Inclusion lists, from Heze: `MAX_SIGNED_INCLUSION_LIST_SIZE`.
  | .inclusionListsByIndices =>
    if .hegota ≤ chunkFork then some preset.MAX_SIGNED_INCLUSION_LIST_SIZE else none
  -- No other protocol has a size limit.
  | _ => none

/-- The length bounds of one successful response chunk of a protocol version, for its fork. -/
def responseBounds (preset : Preset) (config : Config) (chunkFork : Fork) (id : ProtocolId) :
    Option (UInt64 × UInt64) :=
  -- The least and the largest length of the type of the chunk, none when it has no type.
  (responseDesc preset config chunkFork id).map fun shape =>
    let bounds := Networking.ReqResp.payloadBounds shape
    -- With a size limit `L` for the protocol, the largest length `b` becomes `min(b, L)`.
    match id.protocol.sizeLimit preset config chunkFork with
    | some limit => (bounds.1, min bounds.2 limit)
    | none => bounds

end EthLib.Consensus

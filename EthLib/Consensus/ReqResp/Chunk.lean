module

public import EthLib.Consensus.ForkDigest
public import EthLib.Consensus.ReqResp.ResponseBounds

/-!
# `Consensus.ReqResp.Chunk`

One response chunk of a request and response protocol, decoded at the bounds of its own fork.

From Altair, some protocols put a fork digest in the context bytes of a successful chunk.

The digest names the fork of the payload, and so its type.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Networking.ReqResp

/-- Whether a protocol version sends a fork digest as the context bytes of a successful chunk. -/
def ProtocolId.sendsDigest (id : ProtocolId) : Bool :=
  match id.protocol with
  -- Status, goodbye, ping and metadata have one type at each fork, or one per version.
  | .status | .goodbye | .ping | .metadata => false
  -- Version 2, which Altair adds, sends a digest, and version 1 sends none.
  | .beaconBlocksByRange | .beaconBlocksByRoot => id.version ≠ 1
  -- Each protocol added from Altair on sends a digest.
  | .beaconBlocksByHead | .lightClientBootstrap | .lightClientUpdatesByRange
  | .lightClientFinalityUpdate | .lightClientOptimisticUpdate
  | .blobSidecarsByRange | .blobSidecarsByRoot
  | .dataColumnSidecarsByRange | .dataColumnSidecarsByRoot
  | .executionPayloadEnvelopesByRange | .executionPayloadEnvelopesByRoot
  | .inclusionListsByIndices => true

/-- The number of context bytes in a successful chunk of a protocol version: 4 or 0. -/
def ProtocolId.contextBytes (id : ProtocolId) : Nat :=
  if id.sendsDigest then 4 else 0

/-- The first fork whose digest a successful chunk of a protocol may carry.

The payload of the protocol has a type from that fork on, and none before it. -/
def ReqRespProtocol.firstChunkFork : ReqRespProtocol → Fork
  -- The three block protocols serve the blocks of every fork, from Phase 0.
  | .beaconBlocksByRange | .beaconBlocksByRoot | .beaconBlocksByHead => .phase0
  -- These protocols send no digest, so their chunks keep the fork of the exchange.
  | .status | .goodbye | .ping | .metadata => .phase0
  -- The light client messages have no type at Phase 0.
  | .lightClientBootstrap | .lightClientUpdatesByRange | .lightClientFinalityUpdate
  | .lightClientOptimisticUpdate => .altair
  -- Each other protocol has types from the fork that adds it.
  | .blobSidecarsByRange | .blobSidecarsByRoot => .dencun
  | .dataColumnSidecarsByRange | .dataColumnSidecarsByRoot => .fusaka
  | .executionPayloadEnvelopesByRange | .executionPayloadEnvelopesByRoot => .glamsterdam
  | .inclusionListsByIndices => .hegota

/-- Why a response chunk does not decode. -/
inductive ChunkError where
  /-- The chunk has no bounds: an unknown digest, or a protocol version the exchange lacks. -/
  | bounds (error : BoundsError)
  /-- The bytes are not a chunk with a payload within the bounds of its fork. -/
  | chunk (error : ReqRespError)
  deriving Repr, DecidableEq

/-- The fork of a chunk, from its bytes and the fork of the exchange.

A successful chunk of a protocol that sends a digest has the fork of the first epoch with it.

Any other chunk has the fork of the exchange. -/
def responseChunkFork (config : Config) (genesisValidatorsRoot : Root) (fork : Fork)
    (id : ProtocolId) (bs : ByteArray) : Except ChunkError Fork :=
  match bs.data.toList with
  -- The code is one byte, and the digest, when the chunk has one, the next four.
  | b :: d₀ :: d₁ :: d₂ :: d₃ :: _ =>
    -- A digest follows the code only on a success of a protocol that sends one.
    --
    -- An error chunk sends no context bytes.
    if ResponseCode.ofByte b = .success ∧ id.sendsDigest then
      match forkOfDigest config genesisValidatorsRoot #v[d₀, d₁, d₂, d₃] with
      -- The fork of the first epoch with the digest.
      --
      -- On a chain whose digests identify their forks, it is the fork of the digest's epoch.
      | some start => pure (config.forkAtEpoch start)
      -- No epoch of the chain has the digest, so it names no type and no bounds.
      | none => throw (.bounds (.unknownDigest #v[d₀, d₁, d₂, d₃]))
    else pure fork
  -- A chunk too short to hold a digest keeps the fork of the exchange.
  --
  -- The chunk decoder then rejects a success that a digest should follow.
  | _ => pure fork

/-- One response chunk of a protocol version, with the fork that selects the type of its payload.

The caller passes the fork of the exchange, and no bounds.

It does not deserialize the payload, so it does not check that the payload is of the digest's epoch.
-/
def decodeChunkAtFork (preset : Preset) (config : Config) (genesisValidatorsRoot : Root)
    (fork : Fork) (id : ProtocolId) (bs : ByteArray) :
    Except ChunkError (Fork × ResponseChunk) := do
  -- The fork of the exchange defines the protocol version.
  unless (protocolIds fork).contains id do throw (.bounds (.notAtFork id.toString fork))
  let chunkFork ← responseChunkFork config genesisValidatorsRoot fork id bs
  -- A digest of a fork before the first one of the protocol names no type.
  unless id.protocol.firstChunkFork ≤ chunkFork do
    throw (.bounds (.notAtFork id.toString chunkFork))
  -- Each version that a fork defines has a response type, so this case does not occur.
  let some (low, high) := responseBounds preset config chunkFork id
    | throw (.bounds (.notAtFork id.toString chunkFork))
  -- The code, the context bytes of the protocol, then a payload within the bounds of the fork.
  let chunk ←
    (decodeResponseChunk config.MAX_PAYLOAD_SIZE id.contextBytes low high bs).mapError .chunk
  return (chunkFork, chunk)

end EthLib.Consensus

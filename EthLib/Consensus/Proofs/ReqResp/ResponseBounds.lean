module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Consensus.Proofs.ForkDigest
public import EthLib.Consensus.ReqResp.ResponseBounds
public import EthLib.Consensus.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections

/-!
# `Consensus.Proofs.ReqResp.ResponseBounds`

A successful response chunk passes the length check of its protocol, for the fork of the chunk.

From Gloas, a size limit of its protocol bounds it too.

The fork of a chunk is a parameter, which the caller reads from the context bytes.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.ResponseBounds

open EthLib.Consensus
open EthLib.Networking.ReqResp
open EthLib.Networking.Proofs.ReqResp.Encoding
open EthLib.Networking.Proofs.ReqResp.Bounds
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {chunkFork : Base.Fork} {id : ProtocolId}

variable {protocol : ReqRespProtocol}

/-- Before Gloas, no protocol has a size limit. -/
theorem sizeLimit_of_lt_gloas (early : ¬ .glamsterdam ≤ chunkFork) :
    protocol.sizeLimit preset config chunkFork = none := by
  have notHeze : ¬ .hegota ≤ chunkFork := fun heze => early (Nat.le_trans (by decide) heze)
  cases protocol <;> simp [ReqRespProtocol.sizeLimit, early, notHeze]

/-- Only data column sidecars and inclusion lists have a size limit.

Data column sidecars by range and by root have one from Gloas, and inclusion lists from Heze. -/
theorem sizeLimit_ne_none_iff :
    protocol.sizeLimit preset config chunkFork ≠ none ↔
      .glamsterdam ≤ chunkFork ∧
          (protocol = .dataColumnSidecarsByRange ∨ protocol = .dataColumnSidecarsByRoot) ∨
        .hegota ≤ chunkFork ∧ protocol = .inclusionListsByIndices := by
  cases protocol <;> by_cases gloas : .glamsterdam ≤ chunkFork <;>
    by_cases heze : .hegota ≤ chunkFork <;> simp [ReqRespProtocol.sizeLimit, gloas, heze]

/-- From Gloas, the size limit of the two sidecar protocols is the largest size of a sidecar. -/
theorem sizeLimit_dataColumnSidecars
    (named : protocol = .dataColumnSidecarsByRange ∨ protocol = .dataColumnSidecarsByRoot)
    (gloas : .glamsterdam ≤ chunkFork) :
    protocol.sizeLimit preset config chunkFork =
      some (computeMaxDataColumnSidecarSize preset config) := by
  rcases named with rfl | rfl <;> simp [ReqRespProtocol.sizeLimit, gloas]

/-- From Heze, the size limit of inclusion lists by indices is `MAX_SIGNED_INCLUSION_LIST_SIZE`. -/
theorem sizeLimit_inclusionListsByIndices (heze : .hegota ≤ chunkFork) :
    ReqRespProtocol.inclusionListsByIndices.sizeLimit preset config chunkFork =
      some preset.MAX_SIGNED_INCLUSION_LIST_SIZE := by
  simp [ReqRespProtocol.sizeLimit, heze]

/-- The bounds of a chunk of a protocol without a size limit are the payload bounds of its type. -/
theorem responseBounds_eq {shape : Desc}
    (h : responseDesc preset config chunkFork id = some shape)
    (unlimited : id.protocol.sizeLimit preset config chunkFork = none) :
    responseBounds preset config chunkFork id =
      some (payloadBounds config.MAX_PAYLOAD_SIZE shape) := by
  simp [responseBounds, h, unlimited]

/-- With a size limit, the largest length of a chunk is the lower of the limit and that of its type.

Its smallest length is that of its type. -/
theorem responseBounds_eq_min {shape : Desc} {limit : UInt64}
    (h : responseDesc preset config chunkFork id = some shape)
    (limited : id.protocol.sizeLimit preset config chunkFork = some limit) :
    responseBounds preset config chunkFork id =
      some ((payloadBounds config.MAX_PAYLOAD_SIZE shape).1,
        min (payloadBounds config.MAX_PAYLOAD_SIZE shape).2 limit) := by
  simp [responseBounds, h, limited]

/-- The payload of a chunk is a payload that decodes at the bounds of its code.

A success reads the bounds of the chunk, and an error those of an error message. -/
private theorem decodePayload_of_decodeResponseChunk_code {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : decodeResponseChunk config.MAX_PAYLOAD_SIZE contextBytes lo hi bs = .ok chunk) :
    ∃ rest : ByteArray, decodePayload config.MAX_PAYLOAD_SIZE
      (if chunk.code = .success then lo else 0)
      (if chunk.code = .success then hi else MAX_ERROR_MESSAGE_SIZE) rest = .ok chunk.payload := by
  obtain ⟨-, -, rest, -, hd⟩ := decodeResponseChunk_eq_ok_iff.mp h
  exact ⟨rest, hd⟩

/-- The payload of a successful chunk is a payload that decodes at the bounds of the chunk. -/
theorem decodePayload_of_decodeResponseChunk {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : decodeResponseChunk config.MAX_PAYLOAD_SIZE contextBytes lo hi bs = .ok chunk)
    (hs : chunk.code = .success) :
    ∃ rest : ByteArray, decodePayload config.MAX_PAYLOAD_SIZE lo hi rest = .ok chunk.payload := by
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk_code h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hs), ite_eq_left_of_eq_true _ _ (eq_true hs)] at hp
  exact ⟨rest, hp⟩

/-- A successful chunk that decodes at the bounds of its protocol is within its type's bounds. -/
theorem withinBounds_of_decodeResponseChunk {shape : Desc} {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : responseDesc preset config chunkFork id = some shape)
    (hb : responseBounds preset config chunkFork id = some (lo, hi))
    (hd : decodeResponseChunk config.MAX_PAYLOAD_SIZE contextBytes lo hi bs = .ok chunk)
    (hs : chunk.code = .success) :
    shape.minSize ≤ chunk.payload.size ∧
      ∀ bound, shape.maxSize = some bound → chunk.payload.size ≤ bound := by
  -- A size limit only lowers the largest length, so the bounds are within those of the type.
  have bounds : lo = (payloadBounds config.MAX_PAYLOAD_SIZE shape).1 ∧
      hi ≤ (payloadBounds config.MAX_PAYLOAD_SIZE shape).2 := by
    cases hl : id.protocol.sizeLimit preset config chunkFork with
    | none =>
      rw [responseBounds_eq h hl, Option.some.injEq] at hb
      rw [hb]
      exact ⟨rfl, UInt64.le_refl _⟩
    | some limit =>
      rw [responseBounds_eq_min h hl, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact ⟨rfl, Std.min_le_left⟩
  obtain ⟨rfl, within⟩ := bounds
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk hd hs
  obtain ⟨high, low, framed⟩ := (decodePayload_eq_ok_iff hcap).mp hp
  -- The payload also decodes at the bounds of the type, whose largest length is not lower.
  have widened : decodePayload config.MAX_PAYLOAD_SIZE
      (payloadBounds config.MAX_PAYLOAD_SIZE shape).1
      (payloadBounds config.MAX_PAYLOAD_SIZE shape).2 rest = .ok chunk.payload := by
    refine (decodePayload_eq_ok_iff hcap).mpr ⟨?_, low, framed⟩
    have toHigh : (min hi config.MAX_PAYLOAD_SIZE).toNat ≤ hi.toNat :=
      UInt64.le_iff_toNat_le.mp Std.min_le_left
    have toCap : (min hi config.MAX_PAYLOAD_SIZE).toNat ≤ config.MAX_PAYLOAD_SIZE.toNat :=
      UInt64.le_iff_toNat_le.mp Std.min_le_right
    have := UInt64.le_iff_toNat_le.mp within
    rw [UInt64.min_def]
    split <;> omega
  exact withinBounds_of_decodePayload hcap widened

/-- A successful chunk that decodes at the bounds of its protocol is within its size limit. -/
theorem size_le_sizeLimit_of_decodeResponseChunk {limit lo hi : UInt64} {contextBytes : Nat}
    {bs : ByteArray} {chunk : ResponseChunk} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (limited : id.protocol.sizeLimit preset config chunkFork = some limit)
    (hb : responseBounds preset config chunkFork id = some (lo, hi))
    (hd : decodeResponseChunk config.MAX_PAYLOAD_SIZE contextBytes lo hi bs = .ok chunk)
    (hs : chunk.code = .success) :
    chunk.payload.size ≤ limit.toNat := by
  obtain ⟨shape, h, -⟩ := Option.map_eq_some_iff.mp hb
  rw [responseBounds_eq_min h limited, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, rfl⟩ := hb
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk hd hs
  have := ((decodePayload_eq_ok_iff hcap).mp hp).1
  -- The decoder holds the bound to the cap, and the bound is at most the limit.
  have hmin : (min (min (payloadBounds config.MAX_PAYLOAD_SIZE shape).2 limit)
      config.MAX_PAYLOAD_SIZE).toNat ≤ limit.toNat :=
    UInt64.le_iff_toNat_le.mp (UInt64.le_trans Std.min_le_left Std.min_le_right)
  omega

/-- A response value that a server serializes, within the cap, makes a chunk.

It must also be within the size limit of its protocol, if the protocol has one.

The chunk is the one of the encoder that may compress its payload.

The chunk decodes at the bounds of its protocol, and its payload reads back as the value. -/
theorem decodeResponseChunk_response {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data context : ByteArray} {contextBytes : Nat} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : responseDesc preset config chunkFork id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (within : data.size ≤ config.MAX_PAYLOAD_SIZE.toNat)
    (hlimit : ∀ limit, id.protocol.sizeLimit preset config chunkFork = some limit →
      data.size ≤ limit.toNat)
    (hctx : context.size = contextBytes) :
    ∃ lo hi, responseBounds preset config chunkFork id = some (lo, hi) ∧
      decodeResponseChunk config.MAX_PAYLOAD_SIZE contextBytes lo hi
        (encodeResponseChunk ⟨.success, context, data⟩) = .ok ⟨.success, context, data⟩ ∧
      SszType.deserialize α data = .ok a := by
  have untyped := SszType.serialize_ok_iff.mp wrote
  have hsize : data.size = data.data.size := rfl
  obtain ⟨hlow, hhigh⟩ := withinBounds_of_serialize (LawfulSszType.fits a) untyped
  -- The length is within the largest size of the type and the cap, so within their minimum.
  have hbound : data.size ≤ (payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc α)).2.toNat := by
    rw [toNat_payloadBounds_snd]
    cases hm : (SszType.desc α).maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact within
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  -- A size limit of the protocol holds the length too, so the bounds of the chunk admit it.
  obtain ⟨hi, hb, fits⟩ : ∃ hi, responseBounds preset config chunkFork id =
      some ((payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc α)).1, hi) ∧
        data.size ≤ hi.toNat := by
    cases hl : id.protocol.sizeLimit preset config chunkFork with
    | none => exact ⟨_, responseBounds_eq h hl, hbound⟩
    | some limit =>
      have := hlimit limit hl
      refine ⟨_, responseBounds_eq_min h hl, ?_⟩
      rw [UInt64.min_def]
      split <;> omega
  refine ⟨_, hi, hb, ?_, SszType.deserialize_serialize wrote⟩
  apply decodeResponseChunk_encodeResponseChunk hcap
  · rfl
  · simp [hctx]
  · exact within
  · simp only [↓reduceIte]
    exact fits
  · intro _
    rw [toNat_payloadBounds_fst hcap]
    show _ ≤ data.data.size
    omega

/-- The payload bounds of an error message: none below, and the error cap held to the payload cap.

A chunk decodes an error payload at these bounds, since its decoder also holds it to the cap. -/
theorem payloadBounds_errorMessage :
    payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc ErrorMessage) =
      (0, min MAX_ERROR_MESSAGE_SIZE config.MAX_PAYLOAD_SIZE) := by
  have hmin : (SszType.desc ErrorMessage).minSize = 0 := by decide
  have hmax : (SszType.desc ErrorMessage).maxSize = some 256 := by decide
  simp only [payloadBounds, hmin, hmax, Nat.zero_min, Option.getD_some]
  refine Prod.ext rfl (UInt64.toNat_inj.mp ?_)
  have := config.MAX_PAYLOAD_SIZE.toNat_lt
  rw [Base.Uint64.toNat_min, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  rfl

/-- An error chunk that decodes carries an error message: its payload reads back as one.

The message holds the bytes of the payload, whatever they are. -/
theorem deserialize_errorMessage_of_decodeResponseChunk {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : decodeResponseChunk config.MAX_PAYLOAD_SIZE contextBytes lo hi bs = .ok chunk)
    (hs : chunk.code ≠ .success) :
    ∃ message : ErrorMessage, SszType.deserialize ErrorMessage chunk.payload = .ok message ∧
      message.data = chunk.payload.data := by
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk_code h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs), ite_eq_right_of_eq_false _ _ (eq_false hs)] at hp
  have hsize : chunk.payload.size ≤ 256 := by
    have bound := ((decodePayload_eq_ok_iff hcap).mp hp).1
    have cap : (min MAX_ERROR_MESSAGE_SIZE config.MAX_PAYLOAD_SIZE).toNat ≤ 256 :=
      UInt64.le_iff_toNat_le.mp (Std.min_le_left (b := config.MAX_PAYLOAD_SIZE))
    omega
  refine ⟨⟨chunk.payload.data, hsize⟩, SszList.deserialize_uint8_eq_ok_iff.mpr ⟨?_, rfl⟩, rfl⟩
  have : 2 ^ (8 * bytesPerOffset) = 4294967296 := rfl
  omega

/-- On a chain whose digests identify the forks, the receiver reads a chunk at the right type.

The sender serializes a value of the type of its fork, at an epoch.

It puts the fork digest of that epoch in the context bytes of the chunk. -/
theorem decodeResponseChunk_forkOfDigest {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} {genesisValidatorsRoot : Root} {epoch : Epoch} {digest : ForkDigest}
    (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (h : responseDesc preset config (config.forkAtEpoch epoch) id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (within : data.size ≤ config.MAX_PAYLOAD_SIZE.toNat)
    (hlimit : ∀ limit, id.protocol.sizeLimit preset config (config.forkAtEpoch epoch) =
      some limit → data.size ≤ limit.toNat) :
    -- The search finds an epoch for that digest, whose fork is the sender's.
    ∃ start lo hi, forkOfDigest config genesisValidatorsRoot digest = some start ∧
      config.forkAtEpoch start = config.forkAtEpoch epoch ∧
      -- At the bounds of that fork, the chunk decodes with the same context bytes and payload.
      responseBounds preset config (config.forkAtEpoch start) id = some (lo, hi) ∧
      decodeResponseChunk config.MAX_PAYLOAD_SIZE 4 lo hi
        (encodeResponseChunk ⟨.success, ⟨digest.toArray⟩, data⟩) =
        .ok ⟨.success, ⟨digest.toArray⟩, data⟩ ∧
      -- The payload reads back as the value.
      SszType.deserialize α data = .ok a := by
  obtain ⟨start, found⟩ := Option.isSome_iff_exists.mp (forkOfDigest_isSome computed)
  have recovers := forkOfDigest_recovers identify computed
  rw [found] at recovers
  have same : config.forkAtEpoch start = config.forkAtEpoch epoch := by simpa using recovers
  obtain ⟨lo, hi, bounds, decoded, read⟩ :=
    decodeResponseChunk_response (contextBytes := 4) (context := ⟨digest.toArray⟩) hcap h wrote
      within hlimit (by simp [ByteArray.size])
  exact ⟨start, lo, hi, found, same, same ▸ bounds, decoded, read⟩

/-- A protocol that serves the object of a gossip topic sends the message of that topic.

The message has the type of the fork of the chunk, and the protocol has the size limit of the topic.

Blocks by range and by root at every version but 1, and blocks by head, serve blocks.

Light client finality and optimistic updates serve the updates of their topics.

Blob and data column sidecars by range and by root serve the sidecar type of every subnet topic.

Payload envelopes by range and by root serve payloads.

Inclusion lists by indices serve inclusion lists. -/
theorem responseDesc_eq_messageDesc {topic : GossipTopic}
    (serves :
      ((id.protocol = .beaconBlocksByRange ∨ id.protocol = .beaconBlocksByRoot) ∧ id.version ≠ 1 ∨
          id.protocol = .beaconBlocksByHead) ∧ topic = .beaconBlock ∨
        id.protocol = .lightClientFinalityUpdate ∧ topic = .lightClientFinalityUpdate ∨
        id.protocol = .lightClientOptimisticUpdate ∧ topic = .lightClientOptimisticUpdate ∨
        (id.protocol = .blobSidecarsByRange ∨ id.protocol = .blobSidecarsByRoot) ∧
          (∃ subnet, topic = .blobSidecar subnet) ∨
        (id.protocol = .dataColumnSidecarsByRange ∨ id.protocol = .dataColumnSidecarsByRoot) ∧
          (∃ subnet, topic = .dataColumnSidecar subnet) ∨
        (id.protocol = .executionPayloadEnvelopesByRange ∨
            id.protocol = .executionPayloadEnvelopesByRoot) ∧ topic = .executionPayload ∨
        id.protocol = .inclusionListsByIndices ∧ topic = .inclusionList) :
    responseDesc preset config chunkFork id = some (topic.messageDesc preset chunkFork) ∧
      id.protocol.sizeLimit preset config chunkFork = topic.sizeLimit preset config chunkFork := by
  obtain ⟨protocol, version⟩ := id
  simp only at serves ⊢
  rcases serves with ⟨⟨named, later⟩ | rfl, rfl⟩ | rest
  · rcases named with rfl | rfl <;>
      simp only [responseDesc, GossipTopic.messageDesc] <;>
      rw [ite_eq_right_of_eq_false _ _ (eq_false later)] <;>
      simp [ReqRespProtocol.sizeLimit, GossipTopic.sizeLimit.eq_def]
  · simp [responseDesc, GossipTopic.messageDesc, ReqRespProtocol.sizeLimit,
      GossipTopic.sizeLimit.eq_def]
  · rcases rest with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl | rfl, subnet, rfl⟩ |
        ⟨rfl | rfl, subnet, rfl⟩ | ⟨rfl | rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [responseDesc, GossipTopic.messageDesc, ReqRespProtocol.sizeLimit,
        GossipTopic.sizeLimit.eq_def]

/-- At version 1, blocks by range and by root send a Phase 0 block, whatever the fork of the chunk.

That is the message of the block topic at Phase 0. -/
theorem responseDesc_eq_messageDesc_phase0
    (named : id.protocol = .beaconBlocksByRange ∨ id.protocol = .beaconBlocksByRoot)
    (first : id.version = 1) :
    responseDesc preset config chunkFork id =
      some (GossipTopic.beaconBlock.messageDesc preset .phase0) := by
  obtain ⟨protocol, version⟩ := id
  simp only at named first
  subst first
  rcases named with rfl | rfl <;> simp [responseDesc, GossipTopic.messageDesc]

/-- A chunk with the type and the size limit of a gossip topic has the bound of the topic.

Its largest length is that bound, at a fork that lists the topic. -/
theorem responseBounds_snd_eq_topicBound {topic : GossipTopic}
    (h : responseDesc preset config chunkFork id = some (topic.messageDesc preset chunkFork))
    (same : id.protocol.sizeLimit preset config chunkFork = topic.sizeLimit preset config chunkFork)
    (listed : topic ∈ config.gossipTopics chunkFork) :
    (responseBounds preset config chunkFork id).map Prod.snd =
      topicBound preset config chunkFork topic := by
  simp only [responseBounds, topicBound, topicDesc, listed, h, same, ↓reduceIte, Option.map_some]
  cases topic.sizeLimit preset config chunkFork <;> rfl

end EthLib.Consensus.Proofs.ReqResp.ResponseBounds

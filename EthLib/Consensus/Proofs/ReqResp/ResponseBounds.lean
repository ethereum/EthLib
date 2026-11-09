module

public import EthLib.Consensus.ReqResp.ResponseBounds
public import EthLib.Consensus.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections

/-!
# `Consensus.Proofs.ReqResp.ResponseBounds`

A successful response chunk passes the length check of its protocol, for the fork of the chunk.

From Gloas, a size limit of its protocol bounds it too.

The fork of a chunk is a parameter, which the caller reads from the context bytes.

- Before Gloas, no protocol has a size limit.
- Only data column sidecars and inclusion lists have one.
- From Gloas, the size limit of the two sidecar protocols is the largest size of a sidecar.
- From Heze, the size limit of inclusion lists by indices is `MAX_SIGNED_INCLUSION_LIST_SIZE`.
- With a size limit, the largest length of a chunk is the lower of the limit and that of its type.
- Take a successful chunk that decodes at the bounds of its protocol.
  Its payload is within the bounds of its SSZ type, and within the size limit of its protocol.
- A value that a server serializes, within the payload cap, makes a chunk that decodes.
  It must also be within the size limit of its protocol, if the protocol has one.
  The chunk is the one of the encoder that may compress its payload.
- That chunk decodes at those bounds, and its payload reads back as the value.
- The decoder reads an error payload at the bounds of the error message type.
- An error chunk that decodes holds an error message, whatever the bytes of its payload.
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
    responseBounds preset config chunkFork id = some (payloadBounds shape) := by
  simp [responseBounds, h, unlimited]

/-- With a size limit, the largest length of a chunk is the lower of the limit and that of its type.

Its smallest length is that of its type. -/
theorem responseBounds_eq_min {shape : Desc} {limit : UInt64}
    (h : responseDesc preset config chunkFork id = some shape)
    (limited : id.protocol.sizeLimit preset config chunkFork = some limit) :
    responseBounds preset config chunkFork id =
      some ((payloadBounds shape).1, min (payloadBounds shape).2 limit) := by
  simp [responseBounds, h, limited]

/-- The payload of a chunk is a payload that decodes at the bounds of its code.

A success reads the bounds of the chunk, and an error those of an error message. -/
private theorem decodePayload_of_decodeResponseChunk_code {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : decodeResponseChunk contextBytes lo hi bs = .ok chunk) :
    ∃ rest : ByteArray, decodePayload (if chunk.code = .success then lo else 0)
      (if chunk.code = .success then hi else MAX_ERROR_MESSAGE_SIZE) rest = .ok chunk.payload := by
  obtain ⟨-, -, rest, -, hd⟩ := decodeResponseChunk_eq_ok_iff.mp h
  exact ⟨rest, hd⟩

/-- The payload of a successful chunk is a payload that decodes at the bounds of the chunk. -/
theorem decodePayload_of_decodeResponseChunk {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : decodeResponseChunk contextBytes lo hi bs = .ok chunk) (hs : chunk.code = .success) :
    ∃ rest : ByteArray, decodePayload lo hi rest = .ok chunk.payload := by
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk_code h
  rw [ite_eq_left_of_eq_true _ _ (eq_true hs), ite_eq_left_of_eq_true _ _ (eq_true hs)] at hp
  exact ⟨rest, hp⟩

/-- A successful chunk that decodes at the bounds of its protocol is within its type's bounds. -/
theorem withinBounds_of_decodeResponseChunk {shape : Desc} {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : responseDesc preset config chunkFork id = some shape)
    (hb : responseBounds preset config chunkFork id = some (lo, hi))
    (hd : decodeResponseChunk contextBytes lo hi bs = .ok chunk) (hs : chunk.code = .success) :
    shape.minSize ≤ chunk.payload.size ∧
      ∀ bound, shape.maxSize = some bound → chunk.payload.size ≤ bound := by
  -- A size limit only lowers the largest length, so the bounds are within those of the type.
  have bounds : lo = (payloadBounds shape).1 ∧ hi ≤ (payloadBounds shape).2 := by
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
  obtain ⟨high, low, framed⟩ := decodePayload_eq_ok_iff.mp hp
  -- The payload also decodes at the bounds of the type, whose largest length is not lower.
  have widened : decodePayload (payloadBounds shape).1 (payloadBounds shape).2 rest =
      .ok chunk.payload := by
    refine decodePayload_eq_ok_iff.mpr ⟨?_, low, framed⟩
    have toHigh : (min hi MAX_PAYLOAD_SIZE).toNat ≤ hi.toNat :=
      UInt64.le_iff_toNat_le.mp Std.min_le_left
    have toCap : (min hi MAX_PAYLOAD_SIZE).toNat ≤ MAX_PAYLOAD_SIZE.toNat :=
      UInt64.le_iff_toNat_le.mp Std.min_le_right
    have := UInt64.le_iff_toNat_le.mp within
    rw [UInt64.min_def]
    split <;> omega
  exact withinBounds_of_decodePayload widened

/-- A successful chunk that decodes at the bounds of its protocol is within its size limit. -/
theorem size_le_sizeLimit_of_decodeResponseChunk {limit lo hi : UInt64} {contextBytes : Nat}
    {bs : ByteArray} {chunk : ResponseChunk}
    (limited : id.protocol.sizeLimit preset config chunkFork = some limit)
    (hb : responseBounds preset config chunkFork id = some (lo, hi))
    (hd : decodeResponseChunk contextBytes lo hi bs = .ok chunk) (hs : chunk.code = .success) :
    chunk.payload.size ≤ limit.toNat := by
  obtain ⟨shape, h, -⟩ := Option.map_eq_some_iff.mp hb
  rw [responseBounds_eq_min h limited, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, rfl⟩ := hb
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk hd hs
  have := (decodePayload_eq_ok_iff.mp hp).1
  -- The decoder holds the bound to the cap, and the bound is at most the limit.
  have hmin : (min (min (payloadBounds shape).2 limit) MAX_PAYLOAD_SIZE).toNat ≤ limit.toNat :=
    UInt64.le_iff_toNat_le.mp (UInt64.le_trans Std.min_le_left Std.min_le_right)
  omega

/-- A response value that a server serializes, within the cap, makes a chunk.

It must also be within the size limit of its protocol, if the protocol has one.

The chunk is the one of the encoder that may compress its payload.

The chunk decodes at the bounds of its protocol, and its payload reads back as the value. -/
theorem decodeResponseChunk_response {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data context : ByteArray} {contextBytes : Nat}
    (h : responseDesc preset config chunkFork id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (hcap : data.size ≤ MAX_PAYLOAD_SIZE.toNat)
    (hlimit : ∀ limit, id.protocol.sizeLimit preset config chunkFork = some limit →
      data.size ≤ limit.toNat)
    (hctx : context.size = contextBytes) :
    ∃ lo hi, responseBounds preset config chunkFork id = some (lo, hi) ∧
      decodeResponseChunk contextBytes lo hi
        (encodeResponseChunk ⟨.success, context, data⟩) = .ok ⟨.success, context, data⟩ ∧
      SszType.deserialize α data = .ok a := by
  have untyped := SszType.serialize_ok_iff.mp wrote
  have hsize : data.size = data.data.size := rfl
  obtain ⟨hlow, hhigh⟩ := withinBounds_of_serialize (LawfulSszType.fits a) untyped
  -- The length is within the largest size of the type and the cap, so within their minimum.
  have hbound : data.size ≤ (payloadBounds (SszType.desc α)).2.toNat := by
    rw [toNat_payloadBounds_snd]
    cases hm : (SszType.desc α).maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact hcap
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  -- A size limit of the protocol holds the length too, so the bounds of the chunk admit it.
  obtain ⟨hi, hb, within⟩ : ∃ hi, responseBounds preset config chunkFork id =
      some ((payloadBounds (SszType.desc α)).1, hi) ∧ data.size ≤ hi.toNat := by
    cases hl : id.protocol.sizeLimit preset config chunkFork with
    | none => exact ⟨_, responseBounds_eq h hl, hbound⟩
    | some limit =>
      have := hlimit limit hl
      refine ⟨_, responseBounds_eq_min h hl, ?_⟩
      rw [UInt64.min_def]
      split <;> omega
  refine ⟨_, hi, hb, ?_, SszType.deserialize_serialize wrote⟩
  apply decodeResponseChunk_encodeResponseChunk
  · rfl
  · simp [hctx]
  · exact hcap
  · simp only [↓reduceIte]
    exact within
  · intro _
    rw [toNat_payloadBounds_fst]
    show _ ≤ data.data.size
    omega

/-- The bounds at which a chunk decodes an error payload are the payload bounds of its type. -/
theorem payloadBounds_errorMessage :
    payloadBounds (SszType.desc ErrorMessage) = (0, MAX_ERROR_MESSAGE_SIZE) := by
  decide

/-- An error chunk that decodes carries an error message: its payload reads back as one.

The message holds the bytes of the payload, whatever they are. -/
theorem deserialize_errorMessage_of_decodeResponseChunk {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : decodeResponseChunk contextBytes lo hi bs = .ok chunk) (hs : chunk.code ≠ .success) :
    ∃ message : ErrorMessage, SszType.deserialize ErrorMessage chunk.payload = .ok message ∧
      message.data = chunk.payload.data := by
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk_code h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs), ite_eq_right_of_eq_false _ _ (eq_false hs)] at hp
  have hsize : chunk.payload.size ≤ 256 := by
    have bound := (decodePayload_eq_ok_iff.mp hp).1
    have cap : (min MAX_ERROR_MESSAGE_SIZE MAX_PAYLOAD_SIZE).toNat = 256 := by decide
    omega
  refine ⟨⟨chunk.payload.data, hsize⟩, SszList.deserialize_uint8_eq_ok_iff.mpr ⟨?_, rfl⟩, rfl⟩
  have : 2 ^ (8 * bytesPerOffset) = 4294967296 := rfl
  omega

end EthLib.Consensus.Proofs.ReqResp.ResponseBounds

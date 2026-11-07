module

public import EthLib.Consensus.ReqResp.ResponseBounds
public import EthLib.Consensus.Proofs.ReqResp.Bounds

/-!
# `Consensus.Proofs.ReqResp.ResponseBounds`

A successful response chunk passes the length check of its protocol, for the fork of the chunk.

The fork of a chunk is a parameter, which the caller reads from the context bytes.

- Take a successful chunk that decodes at the bounds of its protocol.
  Its payload is within the bounds of its SSZ type.
- A response value that a server serializes, within the payload cap, makes a chunk that decodes.
- That chunk decodes at those bounds, and its payload reads back as the value.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.ResponseBounds

open EthLib.Consensus
open EthLib.Networking.ReqResp
open EthLib.Networking.Proofs.ReqResp.Encoding
open EthLib.Networking.Proofs.ReqResp.Bounds
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {chunkFork : Base.Fork} {id : ProtocolId}

/-- The bounds of a response chunk are the payload bounds of its SSZ type. -/
theorem responseBounds_eq {shape : Desc}
    (h : responseDesc preset config chunkFork id = some shape) :
    responseBounds preset config chunkFork id = some (payloadBounds shape) := by
  simp [responseBounds, h]

/-- The payload of a successful chunk is a payload that decodes at the bounds of the chunk. -/
theorem decodePayload_of_decodeResponseChunk {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : decodeResponseChunk contextBytes lo hi bs = .ok chunk) (hs : chunk.code = .success) :
    ∃ rest : ByteArray, decodePayload lo hi rest = .ok chunk.payload := by
  unfold decodeResponseChunk at h
  split at h
  · cases h
  · rename_i b rest _
    split at h
    · split at h
      · cases h
      · cases hp : decodePayload lo hi ⟨(rest.drop contextBytes).toArray⟩ with
        | error e => simp [hp, bind, Except.bind] at h
        | ok payload =>
          simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨_, hp⟩
    · cases hp : decodePayload 0 MAX_ERROR_MESSAGE_SIZE ⟨rest.toArray⟩ with
      | error e => simp [hp, bind, Except.bind] at h
      | ok payload =>
        simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp_all

/-- A successful chunk that decodes at the bounds of its protocol is within its type's bounds. -/
theorem withinBounds_of_decodeResponseChunk {shape : Desc} {contextBytes : Nat} {lo hi : UInt64}
    {bs : ByteArray} {chunk : ResponseChunk}
    (h : responseDesc preset config chunkFork id = some shape)
    (hb : responseBounds preset config chunkFork id = some (lo, hi))
    (hd : decodeResponseChunk contextBytes lo hi bs = .ok chunk) (hs : chunk.code = .success) :
    shape.minSize ≤ chunk.payload.size ∧
      ∀ bound, shape.maxSize = some bound → chunk.payload.size ≤ bound := by
  rw [responseBounds_eq h, Option.some.injEq] at hb
  obtain ⟨rfl, rfl⟩ : (payloadBounds shape).1 = lo ∧ (payloadBounds shape).2 = hi := by
    rw [hb]
    exact ⟨rfl, rfl⟩
  obtain ⟨rest, hp⟩ := decodePayload_of_decodeResponseChunk hd hs
  exact withinBounds_of_decodePayload hp

/-- A response value that a server serializes, within the cap, makes a chunk that decodes.

The chunk decodes at the bounds of its protocol, and its payload reads back as the value. -/
theorem decodeResponseChunk_response {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data context : ByteArray} {contextBytes : Nat}
    (h : responseDesc preset config chunkFork id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (hcap : data.size ≤ MAX_PAYLOAD_SIZE.toNat)
    (hctx : context.size = contextBytes) :
    ∃ lo hi, responseBounds preset config chunkFork id = some (lo, hi) ∧
      decodeResponseChunk contextBytes lo hi
        (encodeResponseChunkLiteral ⟨.success, context, data⟩) = .ok ⟨.success, context, data⟩ ∧
      SszType.deserialize α data = .ok a := by
  have untyped := SszType.serialize_ok_iff.mp wrote
  have hsize : data.size = data.data.size := rfl
  obtain ⟨hlow, hhigh⟩ := withinBounds_of_serialize (LawfulSszType.fits a) untyped
  refine ⟨(payloadBounds (SszType.desc α)).1, (payloadBounds (SszType.desc α)).2,
    responseBounds_eq h, ?_, SszType.deserialize_serialize wrote⟩
  apply decodeResponseChunk_encodeResponseChunkLiteral
  · rfl
  · simp [hctx]
  · exact hcap
  · simp only [↓reduceIte]
    rw [toNat_payloadBounds_snd]
    show data.data.size ≤ _
    cases hm : (SszType.desc α).maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact hcap
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  · intro _
    rw [toNat_payloadBounds_fst]
    show _ ≤ data.data.size
    omega

end EthLib.Consensus.Proofs.ReqResp.ResponseBounds

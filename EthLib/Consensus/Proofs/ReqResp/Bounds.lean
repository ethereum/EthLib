module

public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Networking.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# `Consensus.Proofs.ReqResp.Bounds`

The request of a protocol passes the length check of its protocol.

- Take a request payload that decodes at the bounds of its protocol.
  Its length is within the bounds of its SSZ type.
- Take a request that a client serializes, within the payload cap.
  It decodes at those bounds and reads back as itself.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.Bounds

open EthLib.Consensus
open EthLib.Networking.ReqResp
open EthLib.Networking.Proofs.ReqResp.Bounds
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : Base.Fork} {id : ProtocolId}

/-- The bounds of a request are the payload bounds of its SSZ type. -/
theorem requestBounds_eq {shape : Desc} (h : requestDesc preset config fork id = some shape) :
    requestBounds preset config fork id = some (payloadBounds shape) := by
  simp [requestBounds, h]

/-- A request payload that decodes at the bounds of its protocol is within its type's bounds. -/
theorem withinBounds_of_decodePayload_request {shape : Desc} {lo hi : UInt64}
    {bs data : ByteArray} (h : requestDesc preset config fork id = some shape)
    (hb : requestBounds preset config fork id = some (lo, hi))
    (hd : decodePayload lo hi bs = .ok data) :
    shape.minSize ≤ data.size ∧ ∀ bound, shape.maxSize = some bound → data.size ≤ bound := by
  rw [requestBounds_eq h, Option.some.injEq] at hb
  obtain ⟨rfl, rfl⟩ : (payloadBounds shape).1 = lo ∧ (payloadBounds shape).2 = hi := by
    rw [hb]
    exact ⟨rfl, rfl⟩
  exact withinBounds_of_decodePayload hd

/-- A request that a client serializes, within the payload cap, decodes at its bounds.

The payload then reads back as the request. -/
theorem decodePayload_request {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} (h : requestDesc preset config fork id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (hcap : data.size ≤ MAX_PAYLOAD_SIZE.toNat) :
    ∃ lo hi, requestBounds preset config fork id = some (lo, hi) ∧
      decodePayload lo hi (encodePayload data) = .ok data ∧
      SszType.deserialize α data = .ok a := by
  refine ⟨(payloadBounds (SszType.desc α)).1, (payloadBounds (SszType.desc α)).2,
    requestBounds_eq h, ?_, SszType.deserialize_serialize wrote⟩
  have untyped := SszType.serialize_ok_iff.mp wrote
  have := decodePayload_encodePayload_of_serialize (LawfulSszType.fits a) untyped hcap
  simpa using this

end EthLib.Consensus.Proofs.ReqResp.Bounds

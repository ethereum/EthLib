module

public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Networking.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Class
import EthLib.Base.Proofs.CodeInjective

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
    requestBounds preset config fork id = some (payloadBounds config.MAX_PAYLOAD_SIZE shape) := by
  simp [requestBounds, h]

/-- A request payload that decodes at the bounds of its protocol is within its type's bounds. -/
theorem withinBounds_of_decodePayload_request {shape : Desc} {lo hi : UInt64}
    {bs data : ByteArray} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : requestDesc preset config fork id = some shape)
    (hb : requestBounds preset config fork id = some (lo, hi))
    (hd : decodePayload config.MAX_PAYLOAD_SIZE lo hi bs = .ok data) :
    shape.minSize ≤ data.size ∧ ∀ bound, shape.maxSize = some bound → data.size ≤ bound := by
  rw [requestBounds_eq h, Option.some.injEq] at hb
  obtain ⟨rfl, rfl⟩ : (payloadBounds config.MAX_PAYLOAD_SIZE shape).1 = lo ∧
      (payloadBounds config.MAX_PAYLOAD_SIZE shape).2 = hi := by
    rw [hb]
    exact ⟨rfl, rfl⟩
  exact withinBounds_of_decodePayload hcap hd

/-- A request that a client serializes, within the payload cap, decodes at its bounds.

The payload then reads back as the request. -/
theorem decodePayload_request {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : requestDesc preset config fork id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (within : data.size ≤ config.MAX_PAYLOAD_SIZE.toNat) :
    ∃ lo hi, requestBounds preset config fork id = some (lo, hi) ∧
      decodePayload config.MAX_PAYLOAD_SIZE lo hi (encodePayload data) = .ok data ∧
      SszType.deserialize α data = .ok a := by
  refine ⟨(payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc α)).1,
    (payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc α)).2,
    requestBounds_eq h, ?_, SszType.deserialize_serialize wrote⟩
  have untyped := SszType.serialize_ok_iff.mp wrote
  have := decodePayload_encodePayload_of_serialize hcap (LawfulSszType.fits a) untyped within
  simpa using this

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Consensus.BoundsError.code_injective (e₁ e₂ : BoundsError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  code_injective BoundsError.code

/-- Every code is above 300, past the codes of custody, subnet and shuffle errors. -/
theorem _root_.EthLib.Consensus.BoundsError.code_gt (e : BoundsError) : 300 < e.code := by
  cases e <;> simp [BoundsError.code]

end EthLib.Consensus.Proofs.ReqResp.Bounds

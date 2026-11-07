module

public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Networking.Proofs.Gossip.Payload
public import EthLib.Networking.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# `Consensus.Proofs.Gossip.Bounds`

The payload of a gossip message is bounded by the largest size of its topic's type.

- A payload that the gossip decoder accepts at its topic's bound is within the type's largest size.
- A message that a node serializes, within the payload cap, passes the decoder once compressed.
- Its payload then reads back as the message.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.Gossip.Bounds

open EthLib.Consensus
open EthLib.Networking.ReqResp (MAX_PAYLOAD_SIZE payloadBounds)
open EthLib.Networking.Proofs.ReqResp.Bounds
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : Base.Fork} {topic : GossipTopic}

/-- The bound of a topic is the largest payload length of its type, held to the cap. -/
theorem topicBound_eq {shape : Desc} (h : topicDesc preset config fork topic = some shape) :
    topicBound preset config fork topic = some (payloadBounds shape).2 := by
  simp [topicBound, h]

/-- A payload that the gossip decoder accepts at its topic's bound is within the largest size. -/
theorem size_le_of_decodePayload {shape : Desc} {bound : UInt64} {data payload : ByteArray}
    (h : topicDesc preset config fork topic = some shape)
    (hb : topicBound preset config fork topic = some bound)
    (hd : Networking.Gossip.decodePayload bound data = .ok payload) :
    ∀ largest, shape.maxSize = some largest → payload.size ≤ largest := by
  intro largest hm
  rw [topicBound_eq h, Option.some.injEq] at hb
  subst hb
  have := (Networking.Proofs.Gossip.Payload.decodePayload_eq_ok_iff.mp hd).2.2
  have hmin : (min (payloadBounds shape).2 MAX_PAYLOAD_SIZE).toNat ≤
      (payloadBounds shape).2.toNat := UInt64.le_iff_toNat_le.mp Std.min_le_left
  rw [toNat_payloadBounds_snd, hm, Option.getD_some] at hmin
  omega

/-- A message that a node serializes, within the payload cap, passes the decoder once compressed.

Its payload then reads back as the message. -/
theorem decodePayload_message {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} (h : topicDesc preset config fork topic = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (hcap : data.size ≤ MAX_PAYLOAD_SIZE.toNat) :
    ∃ bound, topicBound preset config fork topic = some bound ∧
      Networking.Gossip.decodePayload bound (Networking.Snappy.compress data) = .ok data ∧
      SszType.deserialize α data = .ok a := by
  have untyped := SszType.serialize_ok_iff.mp wrote
  have hsize : data.size = data.data.size := rfl
  obtain ⟨-, hhigh⟩ := withinBounds_of_serialize (LawfulSszType.fits a) untyped
  refine ⟨(payloadBounds (SszType.desc α)).2, topicBound_eq h, ?_,
    SszType.deserialize_serialize wrote⟩
  apply Networking.Proofs.Gossip.Payload.decodePayload_compress
  -- The length is within the type's largest size and the cap, so within their minimum.
  have hbound : data.size ≤ (payloadBounds (SszType.desc α)).2.toNat := by
    rw [toNat_payloadBounds_snd]
    cases hm : (SszType.desc α).maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact hcap
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  rw [UInt64.min_def]
  split <;> omega

end EthLib.Consensus.Proofs.Gossip.Bounds

module

public import EthLib.Consensus.Gossip.Bounds
public import EthLib.Consensus.Proofs.Gossip.Topics
public import EthLib.Networking.Proofs.Gossip.Payload
public import EthLib.Networking.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# `Consensus.Proofs.Gossip.Bounds`

The payload of a gossip message is bounded by the largest size of its topic's type.

From Gloas, a size limit of its topic bounds it too.

- Before Gloas, no topic has a size limit.
- Only aggregates, attester slashings, bids and inclusion lists have one.
- With a size limit, the bound of a topic is the lower of the limit and the bound of its type.
- A payload that the gossip decoder accepts at its topic's bound is within the type's largest size.
- It is also within the size limit of the topic.
- A message that a node serializes, within the payload cap, passes the decoder once compressed.
- It must also be within the size limit of its topic, if the topic has one.
- Its payload then reads back as the message.
- From Heze, the topic of inclusion lists carries a signed inclusion list.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.Gossip.Bounds

open EthLib.Consensus
open EthLib.Networking.ReqResp (MAX_PAYLOAD_SIZE payloadBounds)
open EthLib.Networking.Proofs.ReqResp.Bounds
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : Base.Fork} {topic : GossipTopic}

/-- Before Gloas, no topic has a size limit. -/
theorem sizeLimit_of_lt_gloas (early : ¬ .glamsterdam ≤ fork) :
    topic.sizeLimit preset fork = none := by
  have notHeze : ¬ .hegota ≤ fork := fun heze => early (Nat.le_trans (by decide) heze)
  cases topic <;> simp [GossipTopic.sizeLimit, early, notHeze]

/-- Only aggregates, attester slashings, bids and inclusion lists have a size limit.

The first three have one from Gloas, and inclusion lists from Heze. -/
theorem sizeLimit_ne_none_iff :
    topic.sizeLimit preset fork ≠ none ↔
      .glamsterdam ≤ fork ∧ (topic = .beaconAggregateAndProof ∨ topic = .attesterSlashing ∨
        topic = .executionPayloadBid) ∨ .hegota ≤ fork ∧ topic = .inclusionList := by
  cases topic <;> by_cases gloas : .glamsterdam ≤ fork <;> by_cases heze : .hegota ≤ fork <;>
    simp [GossipTopic.sizeLimit, gloas, heze]

/-- The bound of a topic without a size limit is the bound of its type.

That is the largest payload length of the type, held to the cap. -/
theorem topicBound_eq {shape : Desc} (h : topicDesc preset config fork topic = some shape)
    (unlimited : topic.sizeLimit preset fork = none) :
    topicBound preset config fork topic = some (payloadBounds shape).2 := by
  simp [topicBound, h, unlimited]

/-- The bound of a topic with a size limit is the lower of the limit and the bound of its type. -/
theorem topicBound_eq_min {shape : Desc} {limit : UInt64}
    (h : topicDesc preset config fork topic = some shape)
    (limited : topic.sizeLimit preset fork = some limit) :
    topicBound preset config fork topic = some (min (payloadBounds shape).2 limit) := by
  simp [topicBound, h, limited]

/-- A payload that the gossip decoder accepts at its topic's bound is within the largest size. -/
theorem size_le_of_decodePayload {shape : Desc} {bound : UInt64} {data payload : ByteArray}
    (h : topicDesc preset config fork topic = some shape)
    (hb : topicBound preset config fork topic = some bound)
    (hd : Networking.Gossip.decodePayload bound data = .ok payload) :
    ∀ largest, shape.maxSize = some largest → payload.size ≤ largest := by
  intro largest hm
  -- A size limit only lowers the bound, so the bound is within that of the type.
  have hle : bound ≤ (payloadBounds shape).2 := by
    cases hl : topic.sizeLimit preset fork with
    | none =>
      rw [topicBound_eq h hl, Option.some.injEq] at hb
      subst hb
      exact UInt64.le_refl _
    | some limit =>
      rw [topicBound_eq_min h hl, Option.some.injEq] at hb
      subst hb
      exact Std.min_le_left
  have := (Networking.Proofs.Gossip.Payload.decodePayload_eq_ok_iff.mp hd).2.2
  have hmin : (min bound MAX_PAYLOAD_SIZE).toNat ≤ (payloadBounds shape).2.toNat :=
    UInt64.le_iff_toNat_le.mp (UInt64.le_trans Std.min_le_left hle)
  rw [toNat_payloadBounds_snd, hm, Option.getD_some] at hmin
  omega

/-- A payload that the gossip decoder accepts at the bound of a topic is within its size limit. -/
theorem size_le_sizeLimit_of_decodePayload {limit bound : UInt64} {data payload : ByteArray}
    (limited : topic.sizeLimit preset fork = some limit)
    (hb : topicBound preset config fork topic = some bound)
    (hd : Networking.Gossip.decodePayload bound data = .ok payload) :
    payload.size ≤ limit.toNat := by
  obtain ⟨shape, h, -⟩ := Option.map_eq_some_iff.mp hb
  rw [topicBound_eq_min h limited, Option.some.injEq] at hb
  subst hb
  have := (Networking.Proofs.Gossip.Payload.decodePayload_eq_ok_iff.mp hd).2.2
  -- The decoder holds the bound to the cap, and the bound is at most the limit.
  have hmin : (min (min (payloadBounds shape).2 limit) MAX_PAYLOAD_SIZE).toNat ≤ limit.toNat :=
    UInt64.le_iff_toNat_le.mp (UInt64.le_trans Std.min_le_left Std.min_le_right)
  omega

/-- A message that a node serializes, within the payload cap, passes the decoder once compressed.

It must also be within the size limit of its topic, if the topic has one.

Its payload then reads back as the message. -/
theorem decodePayload_message {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} (h : topicDesc preset config fork topic = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (hcap : data.size ≤ MAX_PAYLOAD_SIZE.toNat)
    (hlimit : ∀ limit, topic.sizeLimit preset fork = some limit → data.size ≤ limit.toNat) :
    ∃ bound, topicBound preset config fork topic = some bound ∧
      Networking.Gossip.decodePayload bound (Networking.Snappy.compress data) = .ok data ∧
      SszType.deserialize α data = .ok a := by
  have untyped := SszType.serialize_ok_iff.mp wrote
  have hsize : data.size = data.data.size := rfl
  obtain ⟨-, hhigh⟩ := withinBounds_of_serialize (LawfulSszType.fits a) untyped
  -- The length is within the type's largest size and the cap, so within their minimum.
  have hbound : data.size ≤ (payloadBounds (SszType.desc α)).2.toNat := by
    rw [toNat_payloadBounds_snd]
    cases hm : (SszType.desc α).maxSize with
    | none => simp only [Option.getD_none, Nat.min_self]; exact hcap
    | some m =>
      have := hhigh m hm
      simp only [Option.getD_some]
      omega
  -- A size limit of the topic holds the length too, so the bound of the topic admits it.
  obtain ⟨bound, hb, within⟩ : ∃ bound, topicBound preset config fork topic = some bound ∧
      data.size ≤ bound.toNat := by
    cases hl : topic.sizeLimit preset fork with
    | none => exact ⟨_, topicBound_eq h hl, hbound⟩
    | some limit =>
      have := hlimit limit hl
      refine ⟨_, topicBound_eq_min h hl, ?_⟩
      rw [UInt64.min_def]
      split <;> omega
  refine ⟨bound, hb, ?_, SszType.deserialize_serialize wrote⟩
  apply Networking.Proofs.Gossip.Payload.decodePayload_compress_eq_ok_iff.mpr
  rw [UInt64.min_def]
  split <;> omega

/-- From Heze, the topic of inclusion lists carries a signed inclusion list. -/
theorem topicDesc_inclusionList (heze : .hegota ≤ fork) :
    topicDesc preset config fork .inclusionList = some (SszType.desc SignedInclusionList) := by
  simp [topicDesc, Topics.gossipTopics_heze heze, GossipTopic.messageDesc]

end EthLib.Consensus.Proofs.Gossip.Bounds

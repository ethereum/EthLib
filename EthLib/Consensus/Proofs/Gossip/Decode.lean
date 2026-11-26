module

public import EthLib.Consensus.Gossip.Decode
public import EthLib.Consensus.Proofs.ForkDigest
public import EthLib.Consensus.Proofs.Gossip.Bounds
public import EthLib.Networking.Proofs.Gossip.Topic

/-!
# Proofs: the data of a gossip message at the fork of its topic

A decoded message is one that the payload decoder accepts at the bound of the topic.

On a chain whose digests identify their forks, the topic of an epoch's digest decodes at its fork.

A message that a node serializes at that fork, sent on that topic, decodes and reads back.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.Gossip.Decode

open EthLib.Consensus
open EthLib.Networking.Gossip
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {genesisValidatorsRoot : Root}

/-- No topic name contains `/`, so the topic string of a name parses back to it. -/
theorem slash_not_mem_name (topic : GossipTopic) : '/' ∉ topic.name.toList := by
  cases topic <;>
    first
    | decide
    | exact Networking.Proofs.Gossip.Topic.slash_not_mem_subnetTopicName (by decide) _

/-- A decoded message has a topic of the fork that its digest names, and a payload within its bound.
-/
theorem decodeGossipAtTopic_eq_ok {topicString : String} {data payload : ByteArray}
    {fork : Base.Fork} {topic : GossipTopic}
    (h : decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .ok (fork, topic, payload)) :
    ∃ digest name start bound, parseTopic topicString = .ok (digest, name) ∧
      GossipTopic.ofName? name = some topic ∧
      forkOfDigest config genesisValidatorsRoot digest = some start ∧
      start ≠ FAR_FUTURE_EPOCH ∧
      config.forkAtEpoch start = fork ∧ topic ∈ config.gossipTopics fork ∧
      topicBound preset config fork topic = some bound ∧
      decodePayload config.MAX_PAYLOAD_SIZE bound data = .ok payload := by
  unfold decodeGossipAtTopic at h
  -- Each step either fails, which contradicts `h`, or gives one fact of the statement.
  cases hp : parseTopic topicString with
  | error e => simp [hp, Except.mapError, bind, Except.bind] at h
  | ok parsed =>
    obtain ⟨digest, name⟩ := parsed
    simp only [hp, Except.mapError, bind, Except.bind] at h
    cases hf : forkOfDigest config genesisValidatorsRoot digest with
    | none => simp [hf, throw, throwThe, MonadExceptOf.throw] at h
    | some start =>
      simp only [hf] at h
      by_cases far : start = FAR_FUTURE_EPOCH
      · simp [far, throw, throwThe, MonadExceptOf.throw] at h
      simp only [far, ↓reduceIte] at h
      cases ho : GossipTopic.ofName? name with
      | none => simp [ho, throw, throwThe, MonadExceptOf.throw] at h
      | some found =>
        simp only [ho] at h
        by_cases member : (config.gossipTopics (config.forkAtEpoch start)).contains found
        · simp only [member, ↓reduceIte, pure, Except.pure] at h
          cases hb : topicBound preset config (config.forkAtEpoch start) found with
          | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
          | some bound =>
            simp only [hb] at h
            cases hd : decodePayload config.MAX_PAYLOAD_SIZE bound data with
            | error e => simp [hd] at h
            | ok decoded =>
              simp only [hd, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨digest, name, start, bound, rfl, ho, hf, far, rfl,
                List.contains_iff_mem.mp member, hb, hd⟩
        · have absent : found ∉ config.gossipTopics (config.forkAtEpoch start) :=
            fun mem => member (List.contains_iff_mem.mpr mem)
          simp [absent, throw, throwThe, MonadExceptOf.throw] at h

/-- A topic whose digest only the far future epoch has is refused, with the digest. -/
theorem decodeGossipAtTopic_unscheduled {topicString : String} {digest : ForkDigest} {name : String}
    {data : ByteArray} (parsed : parseTopic topicString = .ok (digest, name))
    (found : forkOfDigest config genesisValidatorsRoot digest = some FAR_FUTURE_EPOCH) :
    decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .error (.bounds (.unscheduledDigest digest)) := by
  unfold decodeGossipAtTopic
  simp [parsed, found, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The topic string of a topic, with some digest, parses back to that digest and that topic. -/
theorem parseTopic_topicString_name (digest : ForkDigest) (t : GossipTopic) :
    parseTopic (topicString digest t.name) = .ok (digest, t.name) :=
  Networking.Proofs.Gossip.Topic.parseTopic_topicString digest (slash_not_mem_name t)

/-- With digests that identify their forks, a topic of an epoch's digest has that epoch's fork.

The decoded topic is the topic of the string. -/
theorem decodeGossipAtTopic_fork_of_digest {epoch : Epoch} {digest : ForkDigest} {t : GossipTopic}
    {data payload : ByteArray} {fork : Base.Fork} {topic : GossipTopic}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (h : decodeGossipAtTopic preset config genesisValidatorsRoot (topicString digest t.name) data =
      .ok (fork, topic, payload)) :
    fork = config.forkAtEpoch epoch ∧ topic = t := by
  obtain ⟨found, name, start, _, parsed, named, hf, -, rfl, -⟩ := decodeGossipAtTopic_eq_ok h
  -- The topic string carries the digest and the name that it was built from.
  rw [parseTopic_topicString_name, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨rfl, rfl⟩ := parsed
  rw [EthLib.Consensus.Proofs.Gossip.Topics.ofName?_name, Option.some.injEq] at named
  refine ⟨?_, named.symm⟩
  have recovers := EthLib.Consensus.forkOfDigest_recovers identify computed
  rw [hf] at recovers
  simpa using recovers

/-- A message that a node serializes at the fork of an epoch decodes from the topic of its digest.

It decodes at that fork and topic, and its payload reads back as the message. -/
theorem decodeGossipAtTopic_message {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {epoch : Epoch} {digest : ForkDigest} {t : GossipTopic} {data : ByteArray}
    (hcap : config.MAX_PAYLOAD_SIZE.toNat ≤ Networking.Snappy.maxUncompressedLength)
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (scheduled : epoch ≠ FAR_FUTURE_EPOCH)
    (member : t ∈ config.gossipTopics (config.forkAtEpoch epoch))
    (typed : topicDesc preset config (config.forkAtEpoch epoch) t = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (within : data.size ≤ config.MAX_PAYLOAD_SIZE.toNat)
    (hlimit : ∀ limit, t.sizeLimit preset config (config.forkAtEpoch epoch) = some limit →
      data.size ≤ limit.toNat) :
    decodeGossipAtTopic preset config genesisValidatorsRoot (topicString digest t.name)
        (Networking.Snappy.compress data) = .ok (config.forkAtEpoch epoch, t, data) ∧
      SszType.deserialize α data = .ok a := by
  obtain ⟨bound, hb, decoded, read⟩ :=
    Proofs.Gossip.Bounds.decodePayload_message hcap typed wrote within hlimit
  refine ⟨?_, read⟩
  -- The search finds an epoch with the digest, and its fork is that of the epoch.
  have recovers := EthLib.Consensus.forkOfDigest_recovers identify computed
  obtain ⟨start, found, same⟩ : ∃ start, forkOfDigest config genesisValidatorsRoot digest =
      some start ∧ config.forkAtEpoch start = config.forkAtEpoch epoch := by
    cases hf : forkOfDigest config genesisValidatorsRoot digest with
    | none => simp [hf] at recovers
    | some start => exact ⟨start, rfl, by simpa [hf] using recovers⟩
  -- The epoch found is at or before the epoch, so it is not the far future one either.
  have early : start ≠ FAR_FUTURE_EPOCH := by
    rintro rfl
    have le := forkOfDigest_le computed found
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have below : epoch.toNat < 2 ^ 64 := epoch.toNat_lt_size
    rw [UInt64.le_iff_toNat_le, far] at le
    apply scheduled
    apply UInt64.toNat_inj.mp
    rw [far]
    omega
  unfold decodeGossipAtTopic
  simp only [parseTopic_topicString_name, Except.mapError, bind, Except.bind, found, early, same,
    EthLib.Consensus.Proofs.Gossip.Topics.ofName?_name, List.contains_iff_mem.mpr member,
    ↓reduceIte, pure, Except.pure, hb, decoded]

/-- The payload of a decoded message is within the largest size of the type of its topic. -/
theorem size_le_of_decodeGossipAtTopic {topicString : String} {data payload : ByteArray}
    {fork : Base.Fork} {topic : GossipTopic} {shape : Desc}
    (hcap : config.MAX_PAYLOAD_SIZE.toNat ≤ Networking.Snappy.maxUncompressedLength)
    (h : decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .ok (fork, topic, payload))
    (typed : topicDesc preset config fork topic = some shape) :
    ∀ largest, shape.maxSize = some largest → payload.size ≤ largest := by
  obtain ⟨_, _, _, _, -, -, -, -, -, -, hb, hd⟩ := decodeGossipAtTopic_eq_ok h
  exact Proofs.Gossip.Bounds.size_le_of_decodePayload hcap typed hb hd

end EthLib.Consensus.Proofs.Gossip.Decode

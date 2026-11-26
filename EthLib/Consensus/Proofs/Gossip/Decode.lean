module

public import EthLib.Consensus.Gossip.Decode
public import EthLib.Consensus.Proofs.Gossip.Bounds
public import EthLib.Consensus.Proofs.ReqResp.Bounds

/-!
# Proofs: the payload of a gossip message at the fork of its topic

A decoded message is one that the payload decoder accepts at the bound of the topic.

A malformed topic, a digest of no scheduled fork and a name of no topic of the fork are refused.

On a chain whose digests identify their forks, a message on an epoch's digest has the epoch's fork.

A message that a node serializes at that fork, sent on that topic, decodes and reads back.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.Gossip.Decode

open EthLib.Consensus
open EthLib.Networking.Gossip
open EthLib.Serialization.Ssz
open EthLib.Consensus.Proofs.Gossip.Topics
open EthLib.Consensus.Proofs.ReqResp.Bounds

variable {preset : Preset} {config : Config} {genesisValidatorsRoot : Root}

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
    cases hf : forkOfScheduledDigest config genesisValidatorsRoot digest with
    | error e => simp [hf] at h
    | ok found =>
      simp only [hf] at h
      obtain ⟨start, hs, far, rfl⟩ := forkOfScheduledDigest_eq_ok hf
      cases ho : GossipTopic.ofName? name with
      | none => simp [ho, throw, throwThe, MonadExceptOf.throw] at h
      | some named =>
        simp only [ho] at h
        cases hb : topicBound preset config (config.forkAtEpoch start) named with
        | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
        | some bound =>
          simp only [hb] at h
          cases hd : decodePayload config.MAX_PAYLOAD_SIZE bound data with
          | error e => simp [hd] at h
          | ok decoded =>
            simp only [hd, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            refine ⟨digest, name, start, bound, rfl, ho, hs, far, rfl, ?_, hb, hd⟩
            -- Only a topic that the fork lists has a bound.
            by_contra absent
            simp [topicBound, topicDesc, absent] at hb

/-- A topic string of the wrong form is refused, with the error of the parser. -/
theorem decodeGossipAtTopic_topic {topicString : String} {data : ByteArray} {error : TopicError}
    (bad : parseTopic topicString = .error error) :
    decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .error (.topic error) := by
  unfold decodeGossipAtTopic
  simp [bad, Except.mapError, bind, Except.bind]

/-- A topic whose digest no epoch has is refused, with the digest. -/
theorem decodeGossipAtTopic_unknown {topicString : String} {digest : ForkDigest} {name : String}
    {data : ByteArray} (parsed : parseTopic topicString = .ok (digest, name))
    (found : forkOfDigest config genesisValidatorsRoot digest = none) :
    decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .error (.bounds (.unknownDigest digest)) := by
  unfold decodeGossipAtTopic
  simp [parsed, forkOfScheduledDigest_unknown found, Except.mapError, bind, Except.bind]

/-- A topic whose digest only the far future epoch has is refused, with the digest. -/
theorem decodeGossipAtTopic_unscheduled {topicString : String} {digest : ForkDigest} {name : String}
    {data : ByteArray} (parsed : parseTopic topicString = .ok (digest, name))
    (found : forkOfDigest config genesisValidatorsRoot digest = some FAR_FUTURE_EPOCH) :
    decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .error (.bounds (.unscheduledDigest digest)) := by
  unfold decodeGossipAtTopic
  simp [parsed, forkOfScheduledDigest_unscheduled found, Except.mapError, bind, Except.bind]

/-- A name that is no topic of the fork of the digest is refused, with the name and the fork. -/
theorem decodeGossipAtTopic_topicNotAtFork {topicString : String} {digest : ForkDigest}
    {name : String} {data : ByteArray} {fork : Base.Fork}
    (parsed : parseTopic topicString = .ok (digest, name))
    (found : forkOfScheduledDigest config genesisValidatorsRoot digest = .ok fork)
    (absent : ∀ topic, GossipTopic.ofName? name = some topic → topic ∉ config.gossipTopics fork) :
    decodeGossipAtTopic preset config genesisValidatorsRoot topicString data =
      .error (.bounds (.topicNotAtFork name fork)) := by
  unfold decodeGossipAtTopic
  simp only [parsed, found, Except.mapError, bind, Except.bind]
  cases ho : GossipTopic.ofName? name with
  | none => simp [throw, throwThe, MonadExceptOf.throw]
  | some topic =>
    -- A topic that the fork does not list has no bound.
    have none : topicBound preset config fork topic = none := by
      simp [topicBound, topicDesc, absent topic ho]
    simp [none, throw, throwThe, MonadExceptOf.throw]

/-- With digests that identify their forks, a topic of an epoch's digest has that epoch's fork.

The decoded topic is the topic of the string. -/
theorem decodeGossipAtTopic_fork_of_digest {epoch : Epoch} {digest : ForkDigest} {t : GossipTopic}
    {data payload : ByteArray} {fork : Base.Fork} {topic : GossipTopic}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (h : decodeGossipAtTopic preset config genesisValidatorsRoot (topicString digest t.name) data =
      .ok (fork, topic, payload)) :
    fork = config.forkAtEpoch epoch ∧ topic = t := by
  obtain ⟨found, name, start, _, parsed, named, hf, far, rfl, -⟩ := decodeGossipAtTopic_eq_ok h
  -- The topic string carries the digest and the name that it was built from.
  rw [parseTopic_topicString_name, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨rfl, rfl⟩ := parsed
  rw [ofName?_name, Option.some.injEq] at named
  exact ⟨forkOfScheduledDigest_eq_ok_of_computed identify computed
    (forkOfScheduledDigest_of_found hf far), named.symm⟩

/-- A message that a node serializes at the fork of an epoch decodes from the topic of its digest.

The epoch is not the far future one, and the message fits the cap and the limit of the topic.

It decodes at that fork and topic, and its payload reads back as the message. -/
theorem decodeGossipAtTopic_message {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {epoch : Epoch} {digest : ForkDigest} {t : GossipTopic} {data : ByteArray}
    (hcap : config.MAX_PAYLOAD_SIZE.toNat ≤ Networking.Snappy.maxUncompressedLength)
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (scheduled : epoch ≠ FAR_FUTURE_EPOCH)
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
  unfold decodeGossipAtTopic
  simp only [parseTopic_topicString_name, Except.mapError, bind, Except.bind,
    forkOfScheduledDigest_computed identify computed scheduled, ofName?_name, hb, decoded, pure,
    Except.pure]

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

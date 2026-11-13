module

public import EthLib.Networking.Gossip.Cache
public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Validation

/-!
# `Networking.Gossip.Router`

What a gossipsub router does with one RPC that it receives from a peer.

It also joins and leaves topics, publishes the messages of this node, and runs the heartbeat.

The router is a pure function of its state, the time, and its inputs.

The rules are those of [gossipsub v1.0, "Message Processing"][proc], with the rules of v1.1 on top.

- A valid message that the router has not seen, on a joined topic, goes to the mesh of that topic.
- [Extended validators][ext]: a message is delivered and forwarded only when it is accepted.
- [Explicit peers][explicit] stay outside the mesh, and their RPCs are always accepted.
  Every valid new message goes to them too.
- [PRUNE backoff][backoff]: a GRAFT within the backoff is pruned at once.
  The backoff is then extended, and the PRUNE carries what remains of it.
- [Outbound quotas][quota]: with a mesh at the high bound or above, only outbound peers join it.
- [Spam protection][spam]: a GRAFT for an unknown topic is ignored.
- [Score thresholds][thr]: the RPCs of a graylisted peer are ignored.
  So is the gossip of a peer below the gossip threshold, unless the peer is explicit.

The standing of a peer under the score thresholds, the message ID and the validation are arguments.

So every result holds for every choice that a client makes for them.

These readings are choices of EthLib, where the sources leave the case open.

- An unknown topic is one the router has not joined, and a GRAFT for it gets no PRUNE.
- A message on a topic the router has not joined is dropped before the seen cache.
- An IHAVE or a PRUNE for a topic the router has not joined is ignored.
- A GRAFT from an explicit peer gets a PRUNE before the topic is checked.
- A GRAFT within the backoff also removes its sender from the mesh, since v1.1 prunes it at once.
- A message goes to every peer in the mesh, the peer that sent it included, as v1.0 says.
- The router knows its own messages only by the seen cache, which a publish must fill.
- The ID of a message that fails validation stays in the seen cache.
- A GRAFT declined under the outbound quota gets no answer.
- A GRAFT within the backoff extends it by a duration that the caller passes.
- A received PRUNE without a backoff sets a backoff of a duration that the caller passes.
- A received PRUNE never shortens a backoff, and the peers it offers are not recorded.
- The PRUNE that answers a GRAFT offers no peers.
- The gossip that a low standing ignores is both IHAVE and IWANT.
- A message ID that is not 20 bytes is never requested and never answered.
- IDONTWANT, from gossipsub v1.2, is ignored.
- A message goes to the mesh, then to the explicit peers, and the two lists do not overlap.

[Topic membership][member] and publishing follow v1.0, with [flood publishing][flood] of v1.1.

The choice among candidate peers is an argument, and so are the values that v1.1 leaves open.

These readings are choices of EthLib too.

- Joining takes only peers that the node may GRAFT: not explicit, score not negative, no backoff.
- Joining again within the backoff of a leave is allowed, and the peers in backoff are skipped.
- Leaving sets a backoff of this node for each pruned peer, as v1.1 asks of a pruning peer.
- A PRUNE that this node sends carries the backoff that the client chose.
- A published message goes to every explicit peer, whatever its topics.
- It goes to no other peer below the publish threshold.
- A score equal to the publish threshold is not below it.
- Flood publishing sends to the mesh peers, and to the other peers that announced the topic.
- A message whose ID is in the seen cache is not published again.
- Floodsub peers are not modelled, so a publish never sends to them.

The [heartbeat][heartbeat] follows v1.0.

It adds the [score rules of the heartbeat][hbm] and the [outbound quotas][quota] of v1.1.

It also adds the [adaptive gossip][adaptive] of v1.1.

These readings are choices of EthLib too.

- The mesh steps run in order: negative peers leave, then the low bound, the high bound, the quota.
- When the mesh is pruned, the replaced peers are the last ones kept that are not outbound.
  The outbound peers that replace them are the best-ranked ones left out.
- The PRUNEs of the heartbeat offer no peers.
- Outbound grafts may take a mesh past the high bound.
- Peers below the publish threshold leave the fanout.
- Fanout top-ups take neither them nor explicit peers.
- The gossip share is taken after the mesh, fanout and explicit peers of the topic are left out.
- The rounding of the gossip share is a client choice.
- The heartbeat also drops the expired entries of the seen cache, but keeps ended backoffs.
- A peer listed twice in a mesh, or among the peers a mesh, fanout or gossip may take, counts once.
- A fanout topic is dropped only once more than its lifetime has passed since the last publish.
- Opportunistic grafting, a "may" of v1.1 with a count that the application sets, is left out.

[proc]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-processing
[ext]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#extended-validators
[explicit]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#explicit-peering-agreements
[backoff]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#prune-backoff-and-peer-exchange
[quota]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#outbound-mesh-quotas
[spam]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#spam-protection-measures
[thr]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#score-thresholds
[member]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#topic-membership
[flood]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#flood-publishing
[heartbeat]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#heartbeat
[hbm]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#heartbeat-maintenance
[adaptive]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#adaptive-gossip-dissemination
-/

@[expose] public section

namespace EthLib.Networking.Gossip

/-- The ID of a peer: the bytes of its libp2p peer ID. -/
abbrev PeerId := ByteArray

/-- Byte arrays are equal exactly when their bytes are, so a list of peers decides membership. -/
scoped instance : LawfulBEq ByteArray where
  rfl {a} := by
    show (a.data == a.data) = true
    simp
  eq_of_beq {a b} h := by
    have : (a.data == b.data) = true := h
    exact ByteArray.ext (eq_of_beq this)

/-- What the router reads of the score of a peer: four flags, for four thresholds of gossipsub v1.1.

A client without scoring passes every flag false.

The router of one RPC reads the graylist and gossip flags.

The two others serve the heartbeat and publishing. -/
structure Standing where
  /-- The score is below zero. -/
  negative : Bool := false
  /-- The score is below the gossip threshold. -/
  belowGossip : Bool := false
  /-- The score is below the publish threshold. -/
  belowPublish : Bool := false
  /-- The score is below the graylist threshold. -/
  belowGraylist : Bool := false
  deriving DecidableEq, Repr

/-- The state of a gossipsub router. -/
structure RouterState where
  /-- The topics this node joined. -/
  topics : List String := []
  /-- The topics of each peer, from the subscriptions that the peer sent. -/
  peerTopics : List (PeerId × List String) := []
  /-- The mesh peers of each topic. -/
  mesh : List (String × List PeerId) := []
  /-- The peers of each topic that this node publishes to without joining it. -/
  fanout : List (String × List PeerId) := []
  /-- For each topic of the fanout, the time in milliseconds when this node last published to it. -/
  lastPublish : List (String × Nat) := []
  /-- For each topic and peer, the time in milliseconds when its backoff ends. -/
  backoff : List ((String × PeerId) × Nat) := []
  /-- The peers on an outbound connection. -/
  outbound : List PeerId := []
  /-- The explicit peers. -/
  explicit : List PeerId := []
  /-- The message cache. -/
  mcache : MessageCache := {}
  /-- The seen cache. -/
  seen : SeenCache := {}
  deriving DecidableEq

/-- What the router sends and delivers on one RPC, each list in the order it was produced. -/
structure Out where
  /-- The valid new messages, each with a peer it is forwarded to. -/
  forward : List (PeerId × Message) := []
  /-- The messages sent in answer to an IWANT, each with the peer that asked. -/
  answers : List (PeerId × Message) := []
  /-- The control messages, each with the peer it goes to. -/
  control : List (PeerId × Control) := []
  /-- The messages delivered to the application. -/
  delivered : List Message := []
  deriving DecidableEq

/-- The RPCs to send, one per message and one per control message, in the order of the fields. -/
def Out.rpcs (out : Out) : List (PeerId × Rpc) :=
  (out.forward ++ out.answers).map (fun (q, m) => (q, { publish := [m] })) ++
    out.control.map fun (q, c) => (q, { control := c })

/-- The peers of a topic in a map from topics to peers; none if the topic is absent. -/
def peersOf (map : List (String × List PeerId)) (topic : String) : List PeerId :=
  (map.lookup topic).getD []

/-- The map with the peers of a topic replaced. -/
def setPeers (map : List (String × List PeerId)) (topic : String) (peers : List PeerId) :
    List (String × List PeerId) :=
  (topic, peers) :: map.filter (·.1 != topic)

/-- The time when the backoff of a peer on a topic ends; zero if there is none. -/
def backoffEnd (backoff : List ((String × PeerId) × Nat)) (topic : String) (peer : PeerId) :
    Nat :=
  (backoff.lookup (topic, peer)).getD 0

/-- The backoffs with the end for a peer on a topic replaced. -/
def setBackoff (backoff : List ((String × PeerId) × Nat)) (topic : String) (peer : PeerId)
    (ends : Nat) : List ((String × PeerId) × Nat) :=
  ((topic, peer), ends) :: backoff.filter (·.1 != (topic, peer))

/-- The topics of each peer, after one subscription change from a peer. -/
def applySubscription (src : PeerId) (peerTopics : List (PeerId × List String))
    (sub : SubOpts) : List (PeerId × List String) :=
  let old := (peerTopics.lookup src).getD []
  let new :=
    if sub.subscribe then
      if sub.topicId ∈ old then old else old ++ [sub.topicId]
    else old.filter (· != sub.topicId)
  (src, new) :: peerTopics.filter (·.1 != src)

/-- The router after one published message of an RPC.

A message on a topic that this node has not joined, or whose ID is in the seen cache, is skipped.

Otherwise its ID goes into the seen cache, and it is validated.

An accepted message goes into the message cache, is delivered, and is forwarded. -/
def receiveMessage (p : GossipsubParameters) (msgId : Message → MessageId)
    (validate : Message → ValidationResult) (now : Nat) (acc : RouterState × Out)
    (m : Message) : RouterState × Out :=
  let (s, out) := acc
  let id := msgId m
  if m.topic ∉ s.topics ∨ s.seen.contains now (p.seen_ttl * 1000) id then (s, out)
  else
    let s := { s with seen := s.seen.insert now id }
    match validate m with
    | .accept =>
      ({ s with mcache := s.mcache.put id m },
        { out with
          forward := out.forward ++ (peersOf s.mesh m.topic ++ s.explicit).map (·, m)
          delivered := out.delivered ++ [m] })
    | _ => (s, out)

/-- The PRUNE of a topic with a backoff in seconds, and no peers. -/
def pruneOf (topic : String) (backoff : UInt64) : Control :=
  { prune := [{ topicId := topic, backoff := backoff }] }

/-- The whole seconds from now to the end of a backoff, both in milliseconds, rounded up.

A count beyond the range of 64 bits gives the largest such count. -/
def remainingSeconds (now ends : Nat) : UInt64 :=
  .ofNat (min ((ends - now + 999) / 1000) (2 ^ 64 - 1))

/-- The router after one GRAFT of an RPC, from the peer that sent it.

The first case that applies decides.

- From an explicit peer, the answer is a PRUNE with no backoff.
- For a topic that this node has not joined, the GRAFT is ignored.
- Within the backoff, the backoff is extended, and the peer leaves the mesh.
  The answer is a PRUNE with what remains of the backoff.
- A peer already in the mesh stays there.
- With a mesh at the high bound or above, a peer that is not outbound is not added.
- Otherwise the peer is added at the end of the mesh. -/
def receiveGraft (p : GossipsubParameters) (backoffMs now : Nat) (src : PeerId)
    (acc : RouterState × Out) (g : Graft) : RouterState × Out :=
  let (s, out) := acc
  let t := g.topicId
  let mesh := peersOf s.mesh t
  let ends := backoffEnd s.backoff t src
  if src ∈ s.explicit then (s, { out with control := out.control ++ [(src, pruneOf t 0)] })
  else if t ∉ s.topics then (s, out)
  else if now < ends then
    ({ s with
        mesh := setPeers s.mesh t (mesh.filter (· != src))
        backoff := setBackoff s.backoff t src (ends + backoffMs) },
      { out with
        control := out.control ++ [(src, pruneOf t (remainingSeconds now (ends + backoffMs)))] })
  else if src ∈ mesh then (s, out)
  else if p.D_high ≤ mesh.length ∧ src ∉ s.outbound then (s, out)
  else ({ s with mesh := setPeers s.mesh t (mesh ++ [src]) }, out)

/-- The router after one PRUNE of an RPC, from the peer that sent it.

The peer leaves the mesh of the topic.

The backoff ends at the later of its current end and now plus the seconds that the PRUNE carries.

A PRUNE that carries no backoff gives the default backoff, in milliseconds.

A PRUNE for a topic that this node has not joined is ignored. -/
def receivePrune (pruneBackoffMs now : Nat) (src : PeerId) (s : RouterState) (q : Prune) :
    RouterState :=
  let t := q.topicId
  let duration := if q.backoff = 0 then pruneBackoffMs else q.backoff.toNat * 1000
  if t ∉ s.topics then s else
  { s with
    mesh := setPeers s.mesh t ((peersOf s.mesh t).filter (· != src))
    backoff := setBackoff s.backoff t src (max (backoffEnd s.backoff t src) (now + duration)) }

/-- The IDs of an IHAVE that the router asks for: those of 20 bytes that it has not seen. -/
def wantedIds (seen : SeenCache) (now ttlMs : Nat) (ids : List ByteArray) : List ByteArray :=
  ids.filter fun b =>
    match MessageId.ofBytes? b with
    | some id => !seen.contains now ttlMs id
    | none => false

/-- The messages that answer an IWANT: those of its IDs that the message cache holds. -/
def answeredMessages (mcache : MessageCache) (ids : List ByteArray) : List Message :=
  ids.filterMap fun b => (MessageId.ofBytes? b).bind mcache.get

/-- The router after one IHAVE of an RPC: an IWANT for the unseen IDs, if there are some.

An IHAVE for a topic that this node has not joined is ignored. -/
def receiveIHave (p : GossipsubParameters) (now : Nat) (src : PeerId) (s : RouterState)
    (out : Out) (h : IHave) : Out :=
  if h.topicId ∉ s.topics then out else
  match wantedIds s.seen now (p.seen_ttl * 1000) h.messageIds with
  | [] => out
  | ids => { out with control := out.control ++ [(src, { iwant := [{ messageIds := ids }] })] }

/-- The router after one IWANT of an RPC: the messages it names that the cache holds. -/
def receiveIWant (src : PeerId) (s : RouterState) (out : Out) (w : IWant) : Out :=
  { out with answers := out.answers ++ (answeredMessages s.mcache w.messageIds).map (src, ·) }

/-- What the router does with one RPC from a peer, at a time in milliseconds.

- The RPC of a graylisted peer that is not explicit is ignored.
- The subscriptions update the topics of the peer.
- The messages are processed, then the GRAFTs, then the PRUNEs.
- Last come the IHAVEs, then the IWANTs.
  A peer below the gossip threshold that is not explicit gets neither.

The caller passes two durations in milliseconds.

They are the extension of a backoff, and the backoff of a PRUNE that carries none.

It also passes the standing of each peer, the message ID and the validation. -/
def receiveRpc (p : GossipsubParameters) (backoffMs pruneBackoffMs : Nat)
    (standing : PeerId → Standing)
    (msgId : Message → MessageId) (validate : Message → ValidationResult) (now : Nat)
    (src : PeerId) (rpc : Rpc) (s : RouterState) : RouterState × Out :=
  if (standing src).belowGraylist ∧ src ∉ s.explicit then (s, {})
  else
    let s := { s with peerTopics := rpc.subscriptions.foldl (applySubscription src) s.peerTopics }
    let acc := rpc.publish.foldl (receiveMessage p msgId validate now) (s, {})
    let (s, out) := rpc.control.graft.foldl (receiveGraft p backoffMs now src) acc
    let s := rpc.control.prune.foldl (receivePrune pruneBackoffMs now src) s
    if (standing src).belowGossip ∧ src ∉ s.explicit then (s, out)
    else
      let out := rpc.control.ihave.foldl (receiveIHave p now src s) out
      (s, rpc.control.iwant.foldl (receiveIWant src s) out)

/-- The choice that a client makes among candidate peers, given how many it wants.

Gossipsub chooses at random, so the choice is an argument. -/
abbrev Select := Nat → List PeerId → List PeerId

/-- A lawful choice keeps the order of the candidates, and takes as many as it can.

That is the count, or every candidate when there are fewer.

Any choice of a set of candidates can be listed in their order, so the order loses no choice. -/
def Select.Lawful (sel : Select) : Prop :=
  ∀ n l, (sel n l).Sublist l ∧ (sel n l).length = min n l.length

/-- The values that gossipsub v1.1 leaves to the client, and the consensus layer does not fix.

Backoffs are in seconds, as a PRUNE carries them. -/
structure ClientChoices where
  /-- The number of best-scoring peers that a mesh keeps when it is pruned. -/
  dScore : Nat
  /-- The number of outbound peers that a mesh keeps when it can. -/
  dOut : Nat
  /-- The share of the peers that get gossip, as a numerator and a denominator. -/
  gossipFactor : Nat × Nat
  /-- Whether the share of the peers that get gossip is rounded up, rather than down. -/
  gossipRoundUp : Bool
  /-- Whether this node sends its own messages to every peer of the topic. -/
  floodPublish : Bool
  /-- The backoff that a PRUNE carries when a mesh is pruned. -/
  pruneBackoffS : UInt64
  /-- The backoff that a PRUNE carries when this node leaves a topic. -/
  unsubscribeBackoffS : UInt64
  deriving DecidableEq, Repr

/-- The bounds of gossipsub v1.1 on the client choices.

The number of outbound peers is below the low bound, and at most half of the target.

The gossip factor is a fraction between zero and one, with a denominator that is not zero.

Both backoffs are positive, since a PRUNE with no backoff asks its receiver for the default. -/
def ClientChoices.Valid (p : GossipsubParameters) (c : ClientChoices) : Prop :=
  c.dOut < p.D_low ∧ 2 * c.dOut ≤ p.D ∧ 0 < c.gossipFactor.2 ∧
    c.gossipFactor.1 ≤ c.gossipFactor.2 ∧ 0 < c.pruneBackoffS ∧ 0 < c.unsubscribeBackoffS

/-- The GRAFT of a topic. -/
def graftOf (topic : String) : Control :=
  { graft := [{ topicId := topic }] }

/-- The peers that announced a topic. -/
def topicPeers (s : RouterState) (topic : String) : List PeerId :=
  (s.peerTopics.filter fun e => topic ∈ e.2).map (·.1)

/-- Whether this node may GRAFT a peer on a topic.

The peer is not explicit, its score is not negative, and its backoff has ended. -/
def graftable (standing : PeerId → Standing) (now : Nat) (s : RouterState) (topic : String)
    (q : PeerId) : Bool :=
  q ∉ s.explicit && !(standing q).negative && backoffEnd s.backoff topic q ≤ now

/-- The backoffs, with the end for one peer on one topic raised to at least a given time. -/
def extendBackoff (backoff : List ((String × PeerId) × Nat)) (topic : String) (peer : PeerId)
    (ends : Nat) : List ((String × PeerId) × Nat) :=
  setBackoff backoff topic peer (max (backoffEnd backoff topic peer) ends)

/-- The router after this node joins a topic, and the GRAFTs it sends.

The mesh takes up to the target number of peers that this node may GRAFT.

It takes them from the fanout of the topic first, then from the other peers of the topic.

The topic leaves the fanout, and each peer of the new mesh gets a GRAFT.

A peer still in a backoff is skipped, so a join soon after a leave may form a smaller mesh.

Joining a topic already joined changes nothing. -/
def join (p : GossipsubParameters) (sel : Select) (standing : PeerId → Standing) (now : Nat)
    (topic : String) (s : RouterState) : RouterState × Out :=
  if topic ∈ s.topics then (s, {}) else
  let ok := graftable standing now s topic
  let fromFanout := sel p.D ((peersOf s.fanout topic).filter ok)
  let fromTopic := sel (p.D - fromFanout.length)
    ((topicPeers s topic).filter fun q => ok q && q ∉ fromFanout)
  let mesh := fromFanout ++ fromTopic
  ({ s with
      topics := s.topics ++ [topic]
      mesh := setPeers s.mesh topic mesh
      fanout := s.fanout.filter (·.1 != topic)
      lastPublish := s.lastPublish.filter (·.1 != topic) },
    { control := mesh.map (·, graftOf topic) })

/-- The router after this node leaves a topic, and the PRUNEs it sends.

Each mesh peer of the topic gets a PRUNE with the backoff of an unsubscribe.

This node also waits that backoff before it grafts the peer again.

Then the mesh of the topic is forgotten.

Leaving a topic not joined changes nothing. -/
def leave (c : ClientChoices) (now : Nat) (topic : String) (s : RouterState) : RouterState × Out :=
  if topic ∉ s.topics then (s, {}) else
  let mesh := peersOf s.mesh topic
  let ends := now + c.unsubscribeBackoffS.toNat * 1000
  ({ s with
      topics := s.topics.filter (· != topic)
      mesh := s.mesh.filter (·.1 != topic)
      backoff := mesh.foldl (fun b q => extendBackoff b topic q ends) s.backoff },
    { control := mesh.map (·, pruneOf topic c.unsubscribeBackoffS) })

/-- The peers that a message this node publishes goes to, before the explicit peers.

They are not explicit, and their score is not below the publish threshold.

- With flood publishing, they are the mesh peers, then the other peers of the topic.
- Otherwise, on a joined topic, they are the mesh peers.
- Otherwise they are the fanout peers of the topic.
  When the fanout is empty, the router first fills it with up to the target number of them.

The router keeps the fanout, and the time of this publish, only in the last case. -/
def publishPeers (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (now : Nat) (topic : String) (s : RouterState) :
    RouterState × List PeerId :=
  let ok (q : PeerId) : Bool := q ∉ s.explicit && !(standing q).belowPublish
  let mesh := peersOf s.mesh topic
  if c.floodPublish then (s, (mesh ++ (topicPeers s topic).filter (· ∉ mesh)).filter ok)
  else if topic ∈ s.topics then (s, mesh.filter ok)
  else
    let fanout := match peersOf s.fanout topic with
      | [] => sel p.D ((topicPeers s topic).filter ok)
      | peers => peers
    ({ s with
        fanout := setPeers s.fanout topic fanout
        lastPublish := (topic, now) :: s.lastPublish.filter (·.1 != topic) },
      fanout.filter ok)

/-- The router after this node publishes a message, and where the message goes.

A message whose ID is in the seen cache is not published again.

Otherwise its ID goes into the seen cache, and the message into the message cache.

It goes to the peers chosen for publishing, then to the explicit peers. -/
def publish (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (msgId : Message → MessageId) (now : Nat) (m : Message)
    (s : RouterState) : RouterState × Out :=
  let id := msgId m
  if s.seen.contains now (p.seen_ttl * 1000) id then (s, {}) else
  let s := { s with seen := s.seen.insert now id, mcache := s.mcache.put id m }
  let (s, peers) := publishPeers p c sel standing now m.topic s
  (s, { forward := (peers ++ s.explicit).map (·, m) })

/-- The client's order of the peers by score.

It says whether the first peer ranks at least as well as the second. -/
abbrev Rank := PeerId → PeerId → Bool

/-- The time in milliseconds when this node last published to a topic.

A topic with no recorded publish reads as published at time zero. -/
def lastPublished (s : RouterState) (topic : String) : Nat :=
  (s.lastPublish.lookup topic).getD 0

/-- The peers that a mesh pruned for oversubscription keeps.

First come the best-ranked peers, up to the score count and the target.

Then come peers chosen among the others, up to the target.

If too few of them are outbound, the last ones that are not outbound give way.

The best-ranked outbound peers left out take their place, up to the outbound count. -/
def keepPeers (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
    (outbound mesh : List PeerId) : List PeerId :=
  let sorted := mesh.mergeSort rank
  let best := sorted.take (min c.dScore p.D)
  let kept := best ++ sel (p.D - best.length) (sorted.drop best.length)
  let keptIn := kept.filter (· ∉ outbound)
  let keptOut := kept.filter (· ∈ outbound)
  let add := ((sorted.filter (· ∈ outbound)).filter (· ∉ kept)).take
    (min (c.dOut - keptOut.length) keptIn.length)
  keptIn.take (keptIn.length - add.length) ++ keptOut ++ add

/-- The peers of a topic outside a mesh that a heartbeat may GRAFT.

They are not explicit, their score is not negative, and their backoff has ended.

Each peer appears once. -/
def graftCandidates (standing : PeerId → Standing) (now : Nat) (s : RouterState) (topic : String)
    (mesh : List PeerId) : List PeerId :=
  ((topicPeers s topic).filter fun q => graftable standing now s topic q && q ∉ mesh).eraseDups

/-- The mesh peers of a topic whose score is not negative, each one once. -/
def nonNegativeMesh (standing : PeerId → Standing) (s : RouterState) (topic : String) :
    List PeerId :=
  (peersOf s.mesh topic).eraseDups.filter fun q => !(standing q).negative

/-- The mesh of a joined topic after a heartbeat, in four steps.

- The peers with a negative score leave it.
- Below the low bound, it takes peers up to the target.
- Above the high bound, it keeps the target number of peers.
- With at least the low bound but too few outbound peers, it takes outbound peers.
  It takes them up to the outbound count. -/
def meshAfter (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
    (standing : PeerId → Standing) (now : Nat) (s : RouterState) (topic : String) :
    List PeerId :=
  let m1 := nonNegativeMesh standing s topic
  let m2 := if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s topic m1)
    else m1
  let m3 := if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2
  let out := (m3.filter (· ∈ s.outbound)).length
  if p.D_low ≤ m3.length ∧ out < c.dOut then
    m3 ++ sel (c.dOut - out) ((graftCandidates standing now s topic m3).filter (· ∈ s.outbound))
  else m3

/-- The fanout after a heartbeat.

A topic not published to for longer than the fanout lifetime leaves it.

Peers below the publish threshold leave the fanout of each topic, since a publish skips them.

Below the target, the peers of a topic are topped up to it with peers of the topic.

They are neither explicit nor below the publish threshold. -/
def fanoutAfter (p : GossipsubParameters) (sel : Select) (standing : PeerId → Standing)
    (now : Nat) (s : RouterState) : List (String × List PeerId) :=
  s.fanout.filterMap fun (topic, peers) =>
    if lastPublished s topic + p.fanout_ttl * 1000 < now then none
    else
      let kept := peers.filter fun q => !(standing q).belowPublish
      if kept.length < p.D then
        let ok (q : PeerId) : Bool := q ∉ s.explicit && !(standing q).belowPublish && q ∉ kept
        some (topic, kept ++ sel (p.D - kept.length) ((topicPeers s topic).filter ok).eraseDups)
      else some (topic, kept)

/-- The number of peers that get gossip, out of a count of candidates.

It is the gossip factor of them, rounded as the client chooses, and at least the lazy degree. -/
def gossipCount (p : GossipsubParameters) (c : ClientChoices) (n : Nat) : Nat :=
  let (num, den) := c.gossipFactor
  max p.D_lazy (if c.gossipRoundUp then (n * num + den - 1) / den else n * num / den)

/-- The peers that may get gossip for a topic: peers of the topic outside its mesh and fanout.

They are neither explicit nor below the gossip threshold, and each appears once. -/
def gossipCandidates (standing : PeerId → Standing) (s : RouterState) (topic : String) :
    List PeerId :=
  ((topicPeers s topic).filter fun q =>
    q ∉ peersOf s.mesh topic && q ∉ peersOf s.fanout topic && q ∉ s.explicit &&
      !(standing q).belowGossip).eraseDups

/-- The IHAVEs for a topic, naming the messages of the topic in the gossip windows.

There are none when the windows hold none.

They go to the gossip share of the candidates for gossip. -/
def gossipOf (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (s : RouterState) (topic : String) : List (PeerId × Control) :=
  match s.mcache.gossipIds p.mcache_gossip topic with
  | [] => []
  | ids =>
    let candidates := gossipCandidates standing s topic
    (sel (gossipCount p c candidates.length) candidates).map fun q =>
      (q, { ihave := [{ topicId := topic, messageIds := ids.map MessageId.toBytes }] })

/-- The router after one heartbeat, and the control messages it sends.

- The mesh of each joined topic is maintained.
  A new peer gets a GRAFT, and a removed one a PRUNE with the pruning backoff.
  This node also waits that backoff before it grafts the removed peer again.
- The fanout is maintained.
- Gossip goes out for each joined topic and each topic of the fanout.
- The message cache shifts, and the seen cache drops its expired entries.

The meshes of topics not joined are dropped, with no PRUNE. -/
def heartbeat (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
    (standing : PeerId → Standing) (now : Nat) (s : RouterState) : RouterState × Out :=
  let mesh := s.topics.map fun t => (t, meshAfter p c sel rank standing now s t)
  let changes := mesh.map fun (t, new) =>
    (t, new.filter (· ∉ peersOf s.mesh t), (peersOf s.mesh t).filter (· ∉ new))
  let grafts := changes.flatMap fun (t, added, _) => added.map (·, graftOf t)
  let prunes := changes.flatMap fun (t, _, removed) => removed.map (·, pruneOf t c.pruneBackoffS)
  let ends := now + c.pruneBackoffS.toNat * 1000
  let backoff := changes.foldl
    (fun b (t, _, removed) => removed.foldl (fun b q => extendBackoff b t q ends) b) s.backoff
  let fanout := fanoutAfter p sel standing now s
  let s := { s with
    mesh
    fanout
    lastPublish := s.lastPublish.filter fun e => (fanout.lookup e.1).isSome
    backoff }
  let gossip := (s.topics ++ s.fanout.map (·.1)).flatMap (gossipOf p c sel standing s)
  ({ s with
      mcache := s.mcache.shift p.mcache_len
      seen := s.seen.expire now (p.seen_ttl * 1000) },
    { control := grafts ++ prunes ++ gossip })

end EthLib.Networking.Gossip

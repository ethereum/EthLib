module

public import EthLib.Networking.Gossip.Cache
public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Validation

/-!
# `Networking.Gossip.Router`

What a gossipsub router does with one RPC that it receives from a peer.

It also joins and leaves topics, publishes the messages of this node, and runs the heartbeat.

The sources are these sections of gossipsub v1.0 and v1.1, and of the pubsub interface.

- v1.0: [Message Processing][proc], [Topic Membership][member] and [Heartbeat][heartbeat].
- v1.1: [Extended Validators][ext] and [Explicit Peering Agreements][explicit].
- v1.1: [PRUNE Backoff and Peer Exchange][backoff] and [Outbound Mesh Quotas][quota].
- v1.1: [Spam Protection Measures][spam], [Score Thresholds][thr] and [Flood Publishing][flood].
- v1.1: [Heartbeat Maintenance][hbm] and [Adaptive Gossip Dissemination][adaptive].
- pubsub: [The RPC][rpc], for the subscriptions of a peer.

The rules of v1.1 apply on top of those of v1.0.

Each step comment names the section that it follows, or one of its subsections.

Where the sources leave a case open, the comment says how EthLib reads it.

[proc]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.0.md#message-processing
[ext]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#extended-validators
[explicit]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#explicit-peering-agreements
[backoff]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#prune-backoff-and-peer-exchange
[quota]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#outbound-mesh-quotas
[spam]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#spam-protection-measures
[thr]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#score-thresholds
[member]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.0.md#topic-membership
[flood]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#flood-publishing
[heartbeat]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.0.md#heartbeat
[hbm]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#heartbeat-maintenance
[adaptive]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/gossipsub/gossipsub-v1.1.md#adaptive-gossip-dissemination
[rpc]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/pubsub/README.md#the-rpc
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

/-- The state of a gossipsub router.

The router is a pure function of its state, the time, and its inputs. -/
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

/-- What the router sends and delivers on one RPC, each list in the order it was produced.

Floodsub peers are not modelled, so the router never sends to them. -/
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
    -- The RPC: subscribe true subscribes to the topic; EthLib lists a topic once.
    if sub.subscribe then
      if sub.topicId ∈ old then old else old ++ [sub.topicId]
    -- Subscribe false, or absent, unsubscribes from it.
    else old.filter (· != sub.topicId)
  (src, new) :: peerTopics.filter (·.1 != src)

/-- The router after one published message of an RPC: what it records, delivers and forwards. -/
def receiveMessage (p : GossipsubParameters) (msgId : Message → MessageId)
    (validate : Message → ValidationResult) (now : Nat) (acc : RouterState × Out)
    (m : Message) : RouterState × Out :=
  let (s, out) := acc
  let id := msgId m
  -- Message Processing: a message in the seen cache was processed before, and is skipped.
  --
  -- So is a message of this node, which EthLib knows only by the seen cache that publishing fills.
  --
  -- EthLib drops a message on a topic that this node has not joined, before the seen cache.
  if m.topic ∉ s.topics ∨ s.seen.contains now (p.seen_ttl * 1000) id then (s, out)
  else
    -- EthLib inserts the ID before validation, so the ID of an invalid message stays there.
    let s := { s with seen := s.seen.insert now id }
    -- Extended Validators: the application accepts, rejects or ignores the message.
    match validate m with
    -- Accept: the message goes into the current window of the message cache, and is delivered.
    --
    -- It is forwarded to every peer of `mesh[topic]`, as v1.0 says, the peer that sent it included.
    --
    -- Then to every explicit peer, as v1.1 asks; explicit peers are never in a mesh, so none twice.
    | .accept =>
      ({ s with mcache := s.mcache.put id m },
        { out with
          forward := out.forward ++ (peersOf s.mesh m.topic ++ s.explicit).map (·, m)
          delivered := out.delivered ++ [m] })
    -- Reject or ignore: neither delivered nor forwarded; the penalty of a reject is not modelled.
    | _ => (s, out)

/-- The PRUNE of a topic with a backoff in seconds, and no peers. -/
def pruneOf (topic : String) (backoff : UInt64) : Control :=
  { prune := [{ topicId := topic, backoff := backoff }] }

/-- The whole seconds from now to the end of a backoff, both in milliseconds, rounded up.

A count beyond the range of 64 bits gives the largest such count. -/
def remainingSeconds (now ends : Nat) : UInt64 :=
  .ofNat (min ((ends - now + 999) / 1000) (2 ^ 64 - 1))

/-- The router after one GRAFT of an RPC, from the peer that sent it, and its answer if any.

The caller passes the extension of a backoff, in milliseconds. -/
def receiveGraft (p : GossipsubParameters) (backoffMs now : Nat) (src : PeerId)
    (acc : RouterState × Out) (g : Graft) : RouterState × Out :=
  let (s, out) := acc
  let t := g.topicId
  let mesh := peersOf s.mesh t
  let ends := backoffEnd s.backoff t src
  -- The first case that applies decides.
  --
  -- Explicit Peering Agreements: a GRAFT from an explicit peer should be rejected with a PRUNE.
  --
  -- EthLib checks it before the topic, and its PRUNE carries no backoff and offers no peers.
  if src ∈ s.explicit then (s, { out with control := out.control ++ [(src, pruneOf t 0)] })
  -- Spam Protection Measures: a GRAFT for an unknown topic is ignored, with no PRUNE.
  --
  -- EthLib reads an unknown topic as one that this node has not joined.
  else if t ∉ s.topics then (s, out)
  -- PRUNE Backoff: a GRAFT within the backoff is pruned at once, and the backoff is extended.
  --
  -- EthLib extends it by the duration that the caller passes, and takes the peer out of the mesh.
  --
  -- The PRUNE carries what remains of the backoff, in seconds, and offers no peers.
  else if now < ends then
    ({ s with
        mesh := setPeers s.mesh t (mesh.filter (· != src))
        backoff := setBackoff s.backoff t src (ends + backoffMs) },
      { out with
        control := out.control ++ [(src, pruneOf t (remainingSeconds now (ends + backoffMs)))] })
  -- A peer already in `mesh[topic]` stays there.
  else if src ∈ mesh then (s, out)
  -- Outbound Mesh Quotas: with a mesh degree at `D_hi` or higher, only an outbound peer joins.
  --
  -- EthLib sends no answer to a GRAFT that the quota declines.
  else if p.D_high ≤ mesh.length ∧ src ∉ s.outbound then (s, out)
  -- Message Processing: the router adds the sender to `mesh[topic]`, here at its end.
  else ({ s with mesh := setPeers s.mesh t (mesh ++ [src]) }, out)

/-- The router after one PRUNE of an RPC, from the peer that sent it.

The caller passes the default backoff, in milliseconds. -/
def receivePrune (pruneBackoffMs now : Nat) (src : PeerId) (s : RouterState) (q : Prune) :
    RouterState :=
  let t := q.topicId
  -- PRUNE Backoff: the backoff that the PRUNE carries, in seconds.
  --
  -- EthLib reads a backoff of zero, written or absent, as none, and takes the caller's default.
  let duration := if q.backoff = 0 then pruneBackoffMs else q.backoff.toNat * 1000
  -- EthLib ignores a PRUNE for a topic that this node has not joined.
  if t ∉ s.topics then s else
  -- Message Processing: the router removes the sender from `mesh[topic]`.
  --
  -- PRUNE Backoff: the pruned peer adds a backoff, which ends at now plus the duration.
  --
  -- EthLib never shortens a backoff, and does not record the peers that the PRUNE offers.
  { s with
    mesh := setPeers s.mesh t ((peersOf s.mesh t).filter (· != src))
    backoff := setBackoff s.backoff t src (max (backoffEnd s.backoff t src) (now + duration)) }

/-- The IDs of an IHAVE that the router asks for: those of 20 bytes that it has not seen. -/
def wantedIds (seen : SeenCache) (now ttlMs : Nat) (ids : List ByteArray) : List ByteArray :=
  ids.filter fun b =>
    match MessageId.ofBytes? b with
    -- Message Processing: the router requests the IDs that its seen cache does not hold.
    | some id => !seen.contains now ttlMs id
    -- EthLib never requests an ID that is not 20 bytes, the size of every message ID here.
    | none => false

/-- The messages that answer an IWANT: those of its IDs that the message cache holds. -/
def answeredMessages (mcache : MessageCache) (ids : List ByteArray) : List Message :=
  -- Message Processing: each requested message present in the message cache.
  --
  -- EthLib answers in the order asked.
  --
  -- EthLib never answers an ID that is not 20 bytes.
  ids.filterMap fun b => (MessageId.ofBytes? b).bind mcache.get

/-- The router after one IHAVE of an RPC: an IWANT for the unseen IDs, if there are some. -/
def receiveIHave (p : GossipsubParameters) (now : Nat) (src : PeerId) (s : RouterState)
    (out : Out) (h : IHave) : Out :=
  -- EthLib ignores an IHAVE for a topic that this node has not joined.
  --
  -- The caps of Spam Protection Measures on IHAVE messages per heartbeat are not modelled.
  if h.topicId ∉ s.topics then out else
  -- Message Processing: an IWANT for the IDs not seen, and none when every ID was seen.
  match wantedIds s.seen now (p.seen_ttl * 1000) h.messageIds with
  | [] => out
  | ids => { out with control := out.control ++ [(src, { iwant := [{ messageIds := ids }] })] }

/-- The router after one IWANT of an RPC: the messages it names that the cache holds. -/
def receiveIWant (src : PeerId) (s : RouterState) (out : Out) (w : IWant) : Out :=
  -- Message Processing: they go to the peer that sent the IWANT.
  --
  -- The limit of Spam Protection Measures on retransmissions to one peer is not modelled.
  { out with answers := out.answers ++ (answeredMessages s.mcache w.messageIds).map (src, ·) }

/-- What the router does with one RPC from a peer, at a time in milliseconds.

The caller passes two durations in milliseconds.

They are the extension of a backoff, and the backoff of a PRUNE that carries none.

It also passes the standing of each peer, the message ID and the validation.

So every result holds for every choice that a client makes for them. -/
def receiveRpc (p : GossipsubParameters) (backoffMs pruneBackoffMs : Nat)
    (standing : PeerId → Standing)
    (msgId : Message → MessageId) (validate : Message → ValidationResult) (now : Nat)
    (src : PeerId) (rpc : Rpc) (s : RouterState) : RouterState × Out :=
  -- Score Thresholds: below the graylist threshold, the peer is graylisted and its RPCs ignored.
  --
  -- Explicit Peering Agreements: the RPCs of an explicit peer are always accepted.
  if (standing src).belowGraylist ∧ src ∉ s.explicit then (s, {})
  else
    -- The RPC of pubsub: each subscription change updates the topics of the peer, in order.
    let s := { s with peerTopics := rpc.subscriptions.foldl (applySubscription src) s.peerTopics }
    -- Message Processing: first the message payloads, in order.
    let acc := rpc.publish.foldl (receiveMessage p msgId validate now) (s, {})
    -- Then the control messages; EthLib takes them in the order of the source's list.
    --
    -- First the GRAFTs, then the PRUNEs.
    let (s, out) := rpc.control.graft.foldl (receiveGraft p backoffMs now src) acc
    let s := rpc.control.prune.foldl (receivePrune pruneBackoffMs now src) s
    -- Score Thresholds: the gossip of a peer below the gossip threshold is ignored.
    --
    -- EthLib counts both IHAVE and IWANT as gossip, and an explicit peer is never ignored.
    if (standing src).belowGossip ∧ src ∉ s.explicit then (s, out)
    else
      -- Last the IHAVEs, then the IWANTs.
      --
      -- EthLib ignores IDONTWANT, which v1.2 allows a receiver to do.
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

/-- The choice of the first candidates, in their order: a fixed choice, for replays. -/
def Select.first : Select := fun n l => l.take n

/-- The values that gossipsub v1.1 leaves to the client, and the consensus layer does not fix.

They are an argument of the router.

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

/-- The router after this node joins a topic, and the GRAFTs it sends. -/
def join (p : GossipsubParameters) (sel : Select) (standing : PeerId → Standing) (now : Nat)
    (topic : String) (s : RouterState) : RouterState × Out :=
  -- Joining a topic already joined changes nothing.
  if topic ∈ s.topics then (s, {}) else
  -- EthLib takes only peers that this node may GRAFT: not explicit, score not negative, no backoff.
  --
  -- PRUNE Backoff asks a node to wait out the backoff of an unsubscribe before it subscribes again.
  --
  -- EthLib allows the join, and skips the peers in a backoff, so the mesh may be smaller.
  let ok := graftable standing now s topic
  -- Topic Membership, JOIN(topic): up to `D` peers, from `fanout[topic]` first.
  let fromFanout := sel p.D ((peersOf s.fanout topic).filter ok)
  -- With fewer than `D` of them, the mesh is filled from the other peers of the topic.
  let fromTopic := sel (p.D - fromFanout.length)
    ((topicPeers s topic).filter fun q => ok q && q ∉ fromFanout)
  let mesh := fromFanout ++ fromTopic
  -- The peers move from `fanout[topic]` to `mesh[topic]`, and the topic leaves the fanout.
  --
  -- Each new member of `mesh[topic]` gets a GRAFT.
  ({ s with
      topics := s.topics ++ [topic]
      mesh := setPeers s.mesh topic mesh
      fanout := s.fanout.filter (·.1 != topic)
      lastPublish := s.lastPublish.filter (·.1 != topic) },
    { control := mesh.map (·, graftOf topic) })

/-- The router after this node leaves a topic, and the PRUNEs it sends. -/
def leave (c : ClientChoices) (now : Nat) (topic : String) (s : RouterState) : RouterState × Out :=
  -- Leaving a topic not joined changes nothing.
  if topic ∉ s.topics then (s, {}) else
  let mesh := peersOf s.mesh topic
  -- PRUNE Backoff: the backoff of an unsubscribe, as the client chose it.
  --
  -- Both the pruning and the pruned peer add it, so this node waits it out before it grafts again.
  let ends := now + c.unsubscribeBackoffS.toNat * 1000
  -- Topic Membership, LEAVE(topic): a PRUNE to each peer of `mesh[topic]`, with that backoff.
  --
  -- Then the router forgets `mesh[topic]`.
  ({ s with
      topics := s.topics.filter (· != topic)
      mesh := s.mesh.filter (·.1 != topic)
      backoff := mesh.foldl (fun b q => extendBackoff b topic q ends) s.backoff },
    { control := mesh.map (·, pruneOf topic c.unsubscribeBackoffS) })

/-- The peers that a message this node publishes goes to, before the explicit peers.

The router keeps the fanout, and the time of this publish, only when it publishes to the fanout. -/
def publishPeers (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (now : Nat) (topic : String) (s : RouterState) :
    RouterState × List PeerId :=
  -- Score Thresholds: no message of this node goes to a peer below the publish threshold.
  --
  -- A score equal to the threshold is not below it.
  --
  -- The explicit peers are left out here, since the publish sends to all of them after.
  --
  -- EthLib sends to them whatever their score.
  let ok (q : PeerId) : Bool := q ∉ s.explicit && !(standing q).belowPublish
  let mesh := peersOf s.mesh topic
  -- Flood Publishing: all known peers in the topic, joined or not.
  --
  -- EthLib lists the peers of `mesh[topic]` first, then the other peers that announced the topic.
  if c.floodPublish then (s, (mesh ++ (topicPeers s topic).filter (· ∉ mesh)).filter ok)
  -- Message Processing, publishing: on a joined topic, the peers of `mesh[topic]`.
  else if topic ∈ s.topics then (s, mesh.filter ok)
  -- Otherwise the peers of `fanout[topic]`.
  --
  -- When it is empty, the router first chooses up to `D` peers of the topic and adds them to it.
  else
    let fanout := match peersOf s.fanout topic with
      | [] => sel p.D ((topicPeers s topic).filter ok)
      | peers => peers
    -- Fanout Maintenance: the router keeps the time of the last publish to the topic.
    ({ s with
        fanout := setPeers s.fanout topic fanout
        lastPublish := (topic, now) :: s.lastPublish.filter (·.1 != topic) },
      fanout.filter ok)

/-- The router after this node publishes a message, and where the message goes. -/
def publish (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (msgId : Message → MessageId) (now : Nat) (m : Message)
    (s : RouterState) : RouterState × Out :=
  let id := msgId m
  -- EthLib does not publish again a message whose ID is in the seen cache.
  if s.seen.contains now (p.seen_ttl * 1000) id then (s, {}) else
  -- The ID joins the seen cache, so the router skips the message when a peer sends it back.
  --
  -- The message goes into the current window of the message cache, so an IWANT can get it.
  let s := { s with seen := s.seen.insert now id, mcache := s.mcache.put id m }
  let (s, peers) := publishPeers p c sel standing now m.topic s
  -- The peers chosen for publishing, then every explicit peer, whatever its score or topics.
  --
  -- EthLib reads the unconditional forwarding of Explicit Peering Agreements as covering them.
  (s, { forward := (peers ++ s.explicit).map (·, m) })

/-- The client's order of the peers by score.

It says whether the first peer ranks at least as well as the second. -/
abbrev Rank := PeerId → PeerId → Bool

/-- The time in milliseconds when this node last published to a topic.

A topic with no recorded publish reads as published at time zero. -/
def lastPublished (s : RouterState) (topic : String) : Nat :=
  (s.lastPublish.lookup topic).getD 0

/-- The peers that a mesh pruned for oversubscription keeps. -/
def keepPeers (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
    (outbound mesh : List PeerId) : List PeerId :=
  -- Heartbeat Maintenance: the peer keeps the best `D_score` scoring peers, here at most `D`.
  let sorted := mesh.mergeSort rank
  let best := sorted.take (min c.dScore p.D)
  -- It selects the remaining peers to keep at random, here by the choice of the client.
  --
  -- The choice takes them among the others, in the order of the mesh, up to `D` in all.
  let kept := best ++ sel (p.D - best.length) (mesh.filter (· ∉ best))
  let keptIn := kept.filter (· ∉ outbound)
  let keptOut := kept.filter (· ∈ outbound)
  -- Outbound Mesh Quotas: at least `D_out` of the survivors are outbound connections.
  --
  -- If too few are, the best-ranked outbound peers left out come in, up to that count.
  let add := ((sorted.filter (· ∈ outbound)).filter (· ∉ kept)).take
    (min (c.dOut - keptOut.length) keptIn.length)
  -- They replace the random and lower scoring peers that are not outbound.
  --
  -- EthLib replaces the last such peers kept: the random ones, then the lowest-ranked best ones.
  keptIn.take (keptIn.length - add.length) ++ keptOut ++ add

/-- The peers of a topic outside a mesh that a heartbeat may GRAFT.

They are not explicit, their score is not negative, and their backoff has ended.

Each peer appears once. -/
def graftCandidates (standing : PeerId → Standing) (now : Nat) (s : RouterState) (topic : String)
    (mesh : List PeerId) : List PeerId :=
  -- Mesh Maintenance: the peers of the topic outside `mesh[topic]`.
  --
  -- Heartbeat Maintenance: peers with a negative score are ignored.
  --
  -- EthLib also leaves out explicit peers and peers in a backoff, and counts each peer once.
  ((topicPeers s topic).filter fun q => graftable standing now s topic q && q ∉ mesh).eraseDups

/-- The mesh peers of a topic whose score is not negative, each one once. -/
def nonNegativeMesh (standing : PeerId → Standing) (s : RouterState) (topic : String) :
    List PeerId :=
  -- Heartbeat Maintenance: peers with a negative score are pruned from all meshes.
  --
  -- EthLib counts a peer listed twice in the mesh once.
  (peersOf s.mesh topic).eraseDups.filter fun q => !(standing q).negative

/-- The mesh of a joined topic after a heartbeat. -/
def meshAfter (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
    (standing : PeerId → Standing) (now : Nat) (s : RouterState) (topic : String) :
    List PeerId :=
  -- EthLib runs the four steps in order: negative peers, low bound, high bound, outbound quota.
  --
  -- Heartbeat Maintenance: the peers with a negative score leave the mesh.
  let m1 := nonNegativeMesh standing s topic
  -- Mesh Maintenance: if `|mesh[topic]| < D_low`, select `D - |mesh[topic]|` peers to add.
  let m2 := if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s topic m1)
    else m1
  -- If `|mesh[topic]| > D_high`, keep `D` of them, by score, at random and under the quota.
  let m3 := if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2
  let out := (m3.filter (· ∈ s.outbound)).length
  -- Outbound Mesh Quotas: a mesh of at least `D_lo` peers keeps `D_out` outbound ones.
  --
  -- When it has fewer, the router grafts as many outbound peers as the quota needs.
  --
  -- EthLib lets these grafts take the mesh past `D_hi`.
  if p.D_low ≤ m3.length ∧ out < c.dOut then
    m3 ++ sel (c.dOut - out) ((graftCandidates standing now s topic m3).filter (· ∈ s.outbound))
  else m3

/-- The fanout after a heartbeat. -/
def fanoutAfter (p : GossipsubParameters) (sel : Select) (standing : PeerId → Standing)
    (now : Nat) (s : RouterState) : List (String × List PeerId) :=
  s.fanout.filterMap fun (topic, peers) =>
    -- Fanout Maintenance: if the time since last published exceeds the lifetime, the topic leaves.
    --
    -- A topic published to exactly the lifetime ago stays.
    if lastPublished s topic + p.fanout_ttl * 1000 < now then none
    else
      -- EthLib drops the peers below the publish threshold, since a publish skips them.
      let kept := peers.filter fun q => !(standing q).belowPublish
      -- If `|fanout[topic]| < D`, select `D - |fanout[topic]|` other peers of the topic to add.
      --
      -- EthLib takes neither explicit peers nor peers below the publish threshold, each once.
      if kept.length < p.D then
        let ok (q : PeerId) : Bool := q ∉ s.explicit && !(standing q).belowPublish && q ∉ kept
        some (topic, kept ++ sel (p.D - kept.length) ((topicPeers s topic).filter ok).eraseDups)
      else some (topic, kept)

/-- The number of peers that get gossip, out of a count of candidates.

It is the gossip factor of them, rounded as the client chooses, and at least the lazy degree. -/
def gossipCount (p : GossipsubParameters) (c : ClientChoices) (n : Nat) : Nat :=
  -- Adaptive Gossip Dissemination: gossip factor peers, with a minimum of `D_lazy`.
  --
  -- The source leaves the rounding open, so the client chooses it.
  let (num, den) := c.gossipFactor
  max p.D_lazy (if c.gossipRoundUp then (n * num + den - 1) / den else n * num / den)

/-- The peers that may get gossip for a topic: peers of the topic outside its mesh and fanout.

They are neither explicit nor below the gossip threshold, and each appears once. -/
def gossipCandidates (standing : PeerId → Standing) (s : RouterState) (topic : String) :
    List PeerId :=
  -- Gossip Emission: peers of the topic not in `mesh[topic]` or `fanout[topic]`.
  --
  -- Score Thresholds: no gossip is emitted to a peer below the gossip threshold.
  --
  -- EthLib also leaves out explicit peers, and counts a peer listed twice once.
  ((topicPeers s topic).filter fun q =>
    q ∉ peersOf s.mesh topic && q ∉ peersOf s.fanout topic && q ∉ s.explicit &&
      !(standing q).belowGossip).eraseDups

/-- The IHAVEs for a topic, naming the messages of the topic in the gossip windows. -/
def gossipOf (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (s : RouterState) (topic : String) : List (PeerId × Control) :=
  -- Gossip Emission: the IDs of the topic in the gossip windows, and no IHAVE if there are none.
  match s.mcache.gossipIds p.mcache_gossip topic with
  | [] => []
  | ids =>
    -- v1.0 selects peers of the topic, then emits only to those outside the mesh and fanout.
    --
    -- EthLib leaves those out first, then takes the gossip share of the rest.
    --
    -- Each chosen peer gets one IHAVE with every ID.
    let candidates := gossipCandidates standing s topic
    (sel (gossipCount p c candidates.length) candidates).map fun q =>
      (q, { ihave := [{ topicId := topic, messageIds := ids.map MessageId.toBytes }] })

/-- The router after one heartbeat, and the control messages it sends. -/
def heartbeat (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
    (standing : PeerId → Standing) (now : Nat) (s : RouterState) : RouterState × Out :=
  -- Mesh Maintenance, for each topic that this node joined.
  --
  -- EthLib drops the meshes of topics not joined, with no PRUNE.
  --
  -- Opportunistic Grafting, which v1.1 allows with a count that the application sets, is left out.
  let mesh := s.topics.map fun t => (t, meshAfter p c sel rank standing now s t)
  -- For each topic, the peers added to the mesh and the peers removed from it.
  let changes := mesh.map fun (t, new) =>
    (t, new.filter (· ∉ peersOf s.mesh t), (peersOf s.mesh t).filter (· ∉ new))
  -- Emit GRAFT(topic) to each peer added.
  let grafts := changes.flatMap fun (t, added, _) => added.map (·, graftOf t)
  -- Emit PRUNE(topic) to each peer removed, with the pruning backoff; EthLib offers no peers.
  let prunes := changes.flatMap fun (t, _, removed) => removed.map (·, pruneOf t c.pruneBackoffS)
  -- PRUNE Backoff: the pruning peer also waits that backoff before it grafts the peer again.
  let ends := now + c.pruneBackoffS.toNat * 1000
  let backoff := changes.foldl
    (fun b (t, _, removed) => removed.foldl (fun b q => extendBackoff b t q ends) b) s.backoff
  -- Fanout Maintenance; a topic that leaves the fanout loses the time of its last publish.
  let fanout := fanoutAfter p sel standing now s
  let s := { s with
    mesh
    fanout
    lastPublish := s.lastPublish.filter fun e => (fanout.lookup e.1).isSome
    backoff }
  -- Gossip Emission, for each topic in mesh and fanout, after their maintenance.
  let gossip := (s.topics ++ s.fanout.map (·.1)).flatMap (gossipOf p c sel standing s)
  -- Message Cache: the windows shift after gossip emission.
  --
  -- EthLib also drops the expired entries of the seen cache here, and keeps the ended backoffs.
  ({ s with
      mcache := s.mcache.shift p.mcache_len
      seen := s.seen.expire now (p.seen_ttl * 1000) },
    -- EthLib sends the GRAFTs, then the PRUNEs, then the IHAVEs.
    { control := grafts ++ prunes ++ gossip })

end EthLib.Networking.Gossip

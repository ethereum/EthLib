module

public import EthLib.Networking.Gossip.Cache
public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Validation

/-!
# `Networking.Gossip.Router`

What a gossipsub router does with one RPC that it receives from a peer.

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

[proc]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.0.md#message-processing
[ext]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#extended-validators
[explicit]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#explicit-peering-agreements
[backoff]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#prune-backoff-and-peer-exchange
[quota]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#outbound-mesh-quotas
[spam]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#spam-protection-measures
[thr]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/pubsub/gossipsub/gossipsub-v1.1.md#score-thresholds
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

end EthLib.Networking.Gossip

module

public import EthLib.Networking.Proofs.Gossip.Router

/-!
# Proofs: joining and leaving a topic, and publishing

For every choice of peers, standing and message ID that a client passes:

- Joining a new topic sends one GRAFT per peer of its new mesh, and nothing else.
- With a lawful choice, that mesh has at most the target number of peers, each one graftable.
- Leaving a topic sends a PRUNE to each peer of its mesh, with the backoff of an unsubscribe.
  The mesh is gone, and this node waits that backoff before it grafts the peer again.
- If no mesh holds a peer twice before a leave, none does after it, and a publish keeps every mesh.
- The same holds for a join with a lawful choice.
  That result also needs the fanout of the topic to list each peer once.
  It needs the same of the peers that announced the topic.
- If no fanout holds a peer twice before a join or a publish, none does after it.
  The publish needs a lawful choice, and the peers that announced its topic to appear once each.
- A join, a leave and a publish keep the topics of the peers and the explicit peers.
  A leave also keeps the fanout.
- If no explicit peer is in a mesh before a leave, none is after it.
  The same holds for a join with a lawful choice.
- A published message goes only to explicit peers and to peers not below the publish threshold.
- With flood publishing, a new message goes to every peer of the topic not below that threshold.
- Once this node publishes a new message, no later RPC forwards or delivers its ID.
  This holds within the lifetime of the seen cache, whatever received RPCs come between.
  So within that lifetime, the router does not forward its own messages, as v1.0 asks.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Membership

open EthLib.Networking.Gossip


/-- A topic that is filtered out of a map has no peers. -/
private theorem peersOf_filter (m : List (String × List PeerId)) (t : String) :
    peersOf (m.filter (·.1 != t)) t = [] := by
  unfold peersOf
  have : (m.filter (·.1 != t)).lookup t = none := by
    rw [List.lookup_eq_none_iff]
    intro x hx
    have := (List.mem_filter.mp hx).2
    rw [bne_comm]; exact this
  simp [this]

/-- Publishing to peers keeps the seen cache and the explicit peers. -/
private theorem publishPeers_keep (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (now : Nat) (topic : String) (s : RouterState) :
    (publishPeers p c sel standing now topic s).1.seen = s.seen ∧
      (publishPeers p c sel standing now topic s).1.explicit = s.explicit := by
  unfold publishPeers
  by_cases h1 : c.floodPublish = true
  · simp [h1]
  · by_cases h2 : topic ∈ s.topics
    · simp [h1, h2]
    · simp [h1, h2]

/-- A peer that a publish picks is not explicit and not below the publish threshold. -/
private theorem publishPeers_mem (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
    (standing : PeerId → Standing) (now : Nat) (topic : String) (s : RouterState) {q : PeerId}
    (hq : q ∈ (publishPeers p c sel standing now topic s).2) :
    q ∉ s.explicit ∧ (standing q).belowPublish = false := by
  unfold publishPeers at hq
  by_cases h1 : c.floodPublish = true
  · simp [h1] at hq
    rcases hq with ⟨-, h⟩ | ⟨-, h, -⟩ <;> exact h
  · by_cases h2 : topic ∈ s.topics
    · simp [h1, h2] at hq
      simpa using hq.2
    · simp [h1, h2] at hq
      simpa using hq.2

variable (p : GossipsubParameters) (c : ClientChoices) (sel : Select)
  (standing : PeerId → Standing) (msgId : Message → MessageId) (now : Nat) (topic : String)
  (s : RouterState)

/-- Joining a new topic sends one GRAFT per peer of its new mesh, in the mesh order.

It sends nothing else. -/
theorem join_out (h : topic ∉ s.topics) :
    (join p sel standing now topic s).2 =
      { control := (peersOf (join p sel standing now topic s).1.mesh topic).map
          (·, graftOf topic) } := by
  simp only [join, h, ↓reduceIte, Router.peersOf_setPeers]

/-- The mesh of a newly joined topic has at most the target number of peers. -/
theorem join_mesh_length (hsel : sel.Lawful) (h : topic ∉ s.topics) :
    (peersOf (join p sel standing now topic s).1.mesh topic).length ≤ p.D := by
  simp only [join, h, ↓reduceIte, Router.peersOf_setPeers]
  have h1 := (hsel p.D ((peersOf s.fanout topic).filter (graftable standing now s topic))).2
  have h2 := (hsel (p.D - (sel p.D ((peersOf s.fanout topic).filter
    (graftable standing now s topic))).length) ((topicPeers s topic).filter fun q =>
      graftable standing now s topic q && decide (q ∉ sel p.D ((peersOf s.fanout topic).filter
        (graftable standing now s topic))))).2
  rw [List.length_append]
  omega

/-- Each peer of the mesh of a newly joined topic is one that the node could GRAFT before. -/
theorem join_graftable (hsel : sel.Lawful) (h : topic ∉ s.topics) {q : PeerId}
    (hq : q ∈ peersOf (join p sel standing now topic s).1.mesh topic) :
    graftable standing now s topic q = true := by
  simp only [join, h, ↓reduceIte, Router.peersOf_setPeers] at hq
  rcases List.mem_append.mp hq with hq | hq
  · have := ((hsel _ _).1.subset hq)
    exact (List.mem_filter.mp this).2
  · have := ((hsel _ _).1.subset hq)
    have := (List.mem_filter.mp this).2
    simpa using (Bool.and_eq_true_iff.mp this).1

/-- Joining a topic keeps each mesh free of a repeated peer.

It needs a lawful choice, and no mesh holding a peer twice before.

It also needs the fanout of the topic, and the peers that announced it, to list each peer once. -/
theorem join_mesh_nodup (hsel : sel.Lawful) (hf : (peersOf s.fanout topic).Nodup)
    (ht : (topicPeers s topic).Nodup) (h : ∀ t, (peersOf s.mesh t).Nodup) (t : String) :
    (peersOf (join p sel standing now topic s).1.mesh t).Nodup := by
  by_cases hj : topic ∈ s.topics
  · simpa [join, hj] using h t
  · simp only [join, hj, ↓reduceIte, Router.peersOf_setPeers]
    split
    · rw [List.nodup_append]
      refine ⟨(hsel _ _).1.nodup (hf.filter _), (hsel _ _).1.nodup (ht.filter _),
        fun a ha b hb hab => ?_⟩
      subst hab
      have := (List.mem_filter.mp ((hsel _ _).1.subset hb)).2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2 ha
    · exact h t

/-- Joining a topic keeps each fanout free of a repeated peer.

It needs no fanout holding a peer twice before. -/
theorem join_fanout_nodup (h : ∀ t, (peersOf s.fanout t).Nodup) (t : String) :
    (peersOf (join p sel standing now topic s).1.fanout t).Nodup := by
  by_cases hj : topic ∈ s.topics
  · simpa [join, hj] using h t
  · simp only [join, hj, ↓reduceIte]
    by_cases e : t = topic
    · subst e
      rw [peersOf_filter]
      exact List.nodup_nil
    · rw [Router.peersOf_filter_ne _ e]
      exact h t

/-- Joining a topic keeps the topics of the peers. -/
theorem join_peerTopics : (join p sel standing now topic s).1.peerTopics = s.peerTopics := by
  unfold join
  split <;> rfl

/-- Joining a topic keeps the explicit peers. -/
theorem join_explicit_eq : (join p sel standing now topic s).1.explicit = s.explicit := by
  unfold join
  split <;> rfl

/-- If no explicit peer is in a mesh before a join, none is after it.

It needs a lawful choice. -/
theorem join_explicit (hsel : sel.Lawful) (h : ∀ t, ∀ q ∈ peersOf s.mesh t, q ∉ s.explicit) :
    ∀ t, ∀ q ∈ peersOf (join p sel standing now topic s).1.mesh t,
      q ∉ (join p sel standing now topic s).1.explicit := by
  intro t q hq
  rw [join_explicit_eq]
  by_cases hj : topic ∈ s.topics
  · simp only [join, hj, ↓reduceIte] at hq
    exact h t q hq
  · by_cases e : t = topic
    · subst e
      have hg := join_graftable p sel standing now t s hsel hj hq
      simp only [graftable, Bool.and_eq_true, decide_eq_true_eq] at hg
      exact hg.1.1
    · simp only [join, hj, ↓reduceIte, Router.peersOf_setPeers, e] at hq
      exact h t q hq

/-- Leaving a joined topic sends a PRUNE with the unsubscribe backoff to each of its mesh peers.

It sends nothing else. -/
theorem leave_out (h : topic ∈ s.topics) :
    (leave c now topic s).2 =
      { control := (peersOf s.mesh topic).map (·, pruneOf topic c.unsubscribeBackoffS) } := by
  simp only [leave, h, not_true_eq_false, ↓reduceIte]

/-- After leaving a topic, the topic is not joined. -/
theorem leave_topics : topic ∉ (leave c now topic s).1.topics := by
  by_cases h : topic ∈ s.topics
  · simp only [leave, h, not_true_eq_false, ↓reduceIte]
    simp
  · simp only [leave, h, not_false_eq_true, ↓reduceIte]

/-- After leaving a topic, its mesh is empty. -/
theorem leave_mesh (h : topic ∈ s.topics) : peersOf (leave c now topic s).1.mesh topic = [] := by
  simp only [leave, h, not_true_eq_false, ↓reduceIte]
  exact peersOf_filter _ _

/-- After leaving a topic, this node waits at least the unsubscribe backoff to GRAFT an old peer.
-/
theorem leave_backoff (h : topic ∈ s.topics) {q : PeerId} (hq : q ∈ peersOf s.mesh topic) :
    now + c.unsubscribeBackoffS.toNat * 1000 ≤
      backoffEnd (leave c now topic s).1.backoff topic q := by
  simp only [leave, h, not_true_eq_false, ↓reduceIte]
  exact Router.backoffEnd_fold_mem _ _ _ _ hq _

/-- Leaving a topic keeps each mesh free of a repeated peer.

It needs no mesh to hold a peer twice before. -/
theorem leave_mesh_nodup (h : ∀ t, (peersOf s.mesh t).Nodup) (t : String) :
    (peersOf (leave c now topic s).1.mesh t).Nodup := by
  by_cases hj : topic ∈ s.topics
  · by_cases e : t = topic
    · subst e
      rw [leave_mesh _ _ _ _ hj]
      exact List.nodup_nil
    · simp only [leave, hj, not_true_eq_false, ↓reduceIte]
      rw [Router.peersOf_filter_ne _ e]
      exact h t
  · simpa [leave, hj] using h t

/-- Leaving a topic keeps the fanout. -/
theorem leave_fanout : (leave c now topic s).1.fanout = s.fanout := by
  unfold leave
  split <;> rfl

/-- Leaving a topic keeps the topics of the peers. -/
theorem leave_peerTopics : (leave c now topic s).1.peerTopics = s.peerTopics := by
  unfold leave
  split <;> rfl

/-- Leaving a topic keeps the explicit peers. -/
theorem leave_explicit_eq : (leave c now topic s).1.explicit = s.explicit := by
  unfold leave
  split <;> rfl

/-- If no explicit peer is in a mesh before a leave, none is after it. -/
theorem leave_explicit (h : ∀ t, ∀ q ∈ peersOf s.mesh t, q ∉ s.explicit) :
    ∀ t, ∀ q ∈ peersOf (leave c now topic s).1.mesh t, q ∉ (leave c now topic s).1.explicit := by
  intro t q hq
  rw [leave_explicit_eq]
  by_cases hj : topic ∈ s.topics
  · by_cases e : t = topic
    · subst e
      rw [leave_mesh _ _ _ _ hj] at hq
      simp at hq
    · simp only [leave, hj, not_true_eq_false, ↓reduceIte] at hq
      rw [Router.peersOf_filter_ne _ e] at hq
      exact h t q hq
  · simp only [leave, hj, not_false_eq_true, ↓reduceIte] at hq
    exact h t q hq

/-- A publish keeps every mesh, the topics of the peers and the explicit peers. -/
private theorem publish_fields {m : Message} :
    (publish p c sel standing msgId now m s).1.mesh = s.mesh ∧
    (publish p c sel standing msgId now m s).1.peerTopics = s.peerTopics ∧
    (publish p c sel standing msgId now m s).1.explicit = s.explicit := by
  unfold publish publishPeers
  by_cases hn : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true
  · simp [hn]
  · by_cases h1 : c.floodPublish = true
    · simp [hn, h1]
    · by_cases h2 : m.topic ∈ s.topics
      · simp [hn, h1, h2]
      · simp [hn, h1, h2]

/-- A publish keeps every mesh. -/
theorem publish_mesh {m : Message} :
    (publish p c sel standing msgId now m s).1.mesh = s.mesh :=
  (publish_fields p c sel standing msgId now s).1

/-- A publish keeps the topics of the peers. -/
theorem publish_peerTopics {m : Message} :
    (publish p c sel standing msgId now m s).1.peerTopics = s.peerTopics :=
  (publish_fields p c sel standing msgId now s).2.1

/-- A publish keeps the explicit peers. -/
theorem publish_explicit_eq {m : Message} :
    (publish p c sel standing msgId now m s).1.explicit = s.explicit :=
  (publish_fields p c sel standing msgId now s).2.2

/-- Choosing the peers of a publish keeps each fanout free of a repeated peer.

It needs a lawful choice, and no fanout holding a peer twice before.

It also needs the peers that announced the topic to appear once each. -/
private theorem publishPeers_fanout_nodup (hsel : sel.Lawful)
    (ht : (topicPeers s topic).Nodup) (h : ∀ t, (peersOf s.fanout t).Nodup) (t : String) :
    (peersOf (publishPeers p c sel standing now topic s).1.fanout t).Nodup := by
  unfold publishPeers
  by_cases h1 : c.floodPublish = true
  · simpa [h1] using h t
  · by_cases h2 : topic ∈ s.topics
    · simpa [h1, h2] using h t
    · have hq := h topic
      generalize peersOf s.fanout topic = q at hq ⊢
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Router.peersOf_setPeers]
      split
      · cases q with
        | nil => exact (hsel _ _).1.nodup (ht.filter _)
        | cons a l => exact hq
      · exact h t

/-- A publish keeps each fanout free of a repeated peer.

It needs a lawful choice, and no fanout holding a peer twice before.

It also needs the peers that announced the topic of the message to appear once each. -/
theorem publish_fanout_nodup (hsel : sel.Lawful) {m : Message} (ht : (topicPeers s m.topic).Nodup)
    (h : ∀ t, (peersOf s.fanout t).Nodup) (t : String) :
    (peersOf (publish p c sel standing msgId now m s).1.fanout t).Nodup := by
  by_cases hn : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true
  · simpa [publish, hn] using h t
  · have hn' : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false := by simpa using hn
    simp only [publish, hn', Bool.false_eq_true, ↓reduceIte]
    exact publishPeers_fanout_nodup p c sel standing now m.topic
      { s with seen := s.seen.insert now (msgId m), mcache := s.mcache.put (msgId m) m } hsel ht h t

/-- A publish forwards only the message it publishes. -/
theorem publish_forward_message {m m' : Message} {q : PeerId}
    (h : (q, m') ∈ (publish p c sel standing msgId now m s).2.forward) : m' = m := by
  by_cases hn : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true
  · simp [publish, hn] at h
  · have hn' : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false := by simpa using hn
    simp only [publish, hn', Bool.false_eq_true, ↓reduceIte, List.mem_map] at h
    obtain ⟨x, -, hxe⟩ := h
    exact (Prod.mk.inj hxe).2.symm

/-- A published message goes only to explicit peers, and to peers not below the publish threshold.
-/
theorem publish_forward_peer {m m' : Message} {q : PeerId}
    (h : (q, m') ∈ (publish p c sel standing msgId now m s).2.forward) :
    q ∈ s.explicit ∨ (standing q).belowPublish = false := by
  by_cases hn : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true
  · simp [publish, hn] at h
  · have hn' : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false := by simpa using hn
    simp only [publish, hn', Bool.false_eq_true, ↓reduceIte, List.mem_map,
      List.mem_append] at h
    obtain ⟨x, hx, hxe⟩ := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj hxe
    rcases hx with hx | hx
    · exact Or.inr (publishPeers_mem p c sel standing now _ _ hx).2
    · left
      rw [(publishPeers_keep p c sel standing now _ _).2] at hx
      exact hx

/-- With flood publishing, a new message goes to each mesh peer and announcing peer of its topic.

That holds for each such peer not below the publish threshold. -/
theorem publish_flood {m : Message} (hf : c.floodPublish = true)
    (hn : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false) {q : PeerId}
    (hq : q ∈ peersOf s.mesh m.topic ∨ q ∈ topicPeers s m.topic)
    (hb : (standing q).belowPublish = false) :
    (q, m) ∈ (publish p c sel standing msgId now m s).2.forward := by
  simp only [publish, hn, Bool.false_eq_true, ↓reduceIte, publishPeers, hf]
  simp only [List.mem_map, List.mem_append, List.mem_filter]
  by_cases hx : q ∈ s.explicit
  · exact ⟨q, Or.inr hx, rfl⟩
  · refine ⟨q, Or.inl ⟨?_, by simp [hx, hb]⟩, rfl⟩
    by_cases hm : q ∈ peersOf s.mesh m.topic
    · exact Or.inl hm
    · exact Or.inr ⟨hq.resolve_left hm, by simpa using hm⟩

/-- Once this node publishes a new message, no later RPC forwards or delivers a message with its ID.

Any RPCs may come between, with any sender, parameters, message ID and validation.

Say the last RPC uses the same parameters and message ID function as the publish.

Then it neither forwards nor delivers that ID, if it comes within the lifetime of the seen cache.

So within that lifetime, this node does not forward its own message, as gossipsub v1.0 asks.

The RPCs between are received RPCs; no other step of the router comes between. -/
theorem publish_receiveRpc {m : Message}
    (hn : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false)
    (steps : List (RouterState → RouterState))
    (hsteps : ∀ f ∈ steps, ∃ (p' : GossipsubParameters) (backoffMs' pruneBackoffMs' : Nat)
      (standing' : PeerId → Standing) (msgId' : Message → MessageId)
      (validate' : Message → ValidationResult) (now' : Nat) (src' : PeerId) (rpc' : Rpc),
      f = fun r => (receiveRpc p' backoffMs' pruneBackoffMs' standing' msgId' validate' now' src'
        rpc' r).1)
    {s' : RouterState}
    (hs' : s' = steps.foldl (fun r f => f r) (publish p c sel standing msgId now m s).1)
    (backoffMs pruneBackoffMs : Nat) (standing' : PeerId → Standing)
    (validate : Message → ValidationResult) (now' : Nat) (src : PeerId) (rpc : Rpc)
    (ht : now' < now + p.seen_ttl * 1000) {q : PeerId} {m' : Message} (hid : msgId m' = msgId m) :
    (q, m') ∉ (receiveRpc p backoffMs pruneBackoffMs standing' msgId validate now' src rpc
        s').2.forward ∧
      m' ∉ (receiveRpc p backoffMs pruneBackoffMs standing' msgId validate now' src rpc
        s').2.delivered := by
  have hs : (publish p c sel standing msgId now m s).1.seen = s.seen.insert now (msgId m) := by
    simp only [publish, hn, Bool.false_eq_true, ↓reduceIte]
    exact (publishPeers_keep p c sel standing now m.topic _).1
  have he : (msgId m, now) ∈ (publish p c sel standing msgId now m s).1.seen.entries := by
    rw [hs]; simp [SeenCache.insert]
  have he' : (msgId m, now) ∈ s'.seen.entries := by
    rw [hs']
    exact Router.foldl_inv steps (fun r : RouterState => (msgId m, now) ∈ r.seen.entries)
      (fun r f => f r) (fun r f hf hr => by
        obtain ⟨p', b', pb', st', mi', v', n', sr', r', rfl⟩ := hsteps f hf
        exact Router.receiveRpc_seen p' b' pb' st' mi' v' n' sr' r' r _ hr) he
  exact Router.receiveRpc_seen_skip p backoffMs pruneBackoffMs standing' msgId validate now' src
    rpc _ he' ht hid

/-- The choice of the first candidates is lawful, so every result holds for it. -/
theorem Select.first_lawful : Select.first.Lawful := fun n l =>
  ⟨List.take_sublist n l, by simp [Select.first, List.length_take]⟩

end EthLib.Networking.Proofs.Gossip.Membership

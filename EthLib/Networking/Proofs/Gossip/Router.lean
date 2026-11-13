module

public import EthLib.Networking.Gossip.Router

/-!
# Proofs: the gossipsub router on a received RPC

For every standing, message ID and validation that a client passes:

- Only a message of the RPC, on a joined topic, unseen and accepted, is forwarded or delivered.
- A peer joins the mesh of a topic only by a GRAFT for it, and only when every rule allows it.
  The topic is joined, the peer is not explicit, its backoff is over, and the outbound quota holds.
- So a peer within its backoff never joins a mesh.
- Every IWANT goes to the sender, for unseen IDs that an IHAVE on a joined topic named.
- A peer below the gossip threshold that is not explicit gets no IWANT and no IWANT answer.
- A GRAFT from an explicit peer, or within the backoff for a joined topic, is answered with a PRUNE.
  This needs an RPC that the graylist does not drop.
- If no explicit peer is in a mesh before the RPC, none is after it.
- Every message sent in answer to an IWANT goes to the sender of the RPC.
  The IWANT named it, and the message cache after the RPC holds it.
- The RPC of a graylisted peer that is not explicit changes nothing and sends nothing.
- A GRAFT within the backoff of its sender puts the sender out of the mesh of a joined topic.
  This needs a sender that is neither explicit nor graylisted.
- No RPC removes an entry of the seen cache.
- A forwarded or delivered message has its ID in the seen cache, with the time of the RPC.
- So after an RPC forwards or delivers a message, no later RPC forwards or delivers its ID.
  This holds within the lifetime of the seen cache, whatever RPCs come between.
  The later RPC uses the same parameters and the same message ID function.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Router

open EthLib.Networking.Gossip

/-- A property of a left fold holds at the end when each step preserves it. -/
theorem foldl_inv {α β : Type} (l : List α) (P : β → Prop) (f : β → α → β)
    (h : ∀ b a, a ∈ l → P b → P (f b a)) {b : β} (hb : P b) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons x l ih =>
    exact ih (fun b a ha => h b a (List.mem_cons_of_mem _ ha)) (h b x List.mem_cons_self hb)

/-- Looking a topic up after its peers are replaced. -/
theorem peersOf_setPeers (m : List (String × List PeerId)) (t t' : String)
    (ps : List PeerId) :
    peersOf (setPeers m t ps) t' = if t' = t then ps else peersOf m t' := by
  have key : ∀ m : List (String × List PeerId), t' ≠ t →
      (m.filter (·.1 != t)).lookup t' = m.lookup t' := by
    intro m hne
    induction m with
    | nil => rfl
    | cons x m ih =>
      obtain ⟨a, b⟩ := x
      by_cases ha : a = t
      · subst ha
        have : (t' == a) = false := by simpa using hne
        simp [List.lookup, List.filter, ih, this]
      · have : (a != t) = true := by simpa using ha
        by_cases hta : t' = a
        · subst hta; simp [List.lookup, List.filter, this]
        · have : (t' == a) = false := by simpa using hta
          simp [List.lookup, List.filter, *]
  unfold peersOf setPeers
  by_cases h : t' = t
  · subst h; simp [List.lookup]
  · have : (t' == t) = false := by simpa using h
    simp [List.lookup, h, key m h, this]

/-- Looking a backoff up after one end is replaced. -/
theorem backoffEnd_setBackoff (b : List ((String × PeerId) × Nat)) (t t' : String)
    (p p' : PeerId) (e : Nat) :
    backoffEnd (setBackoff b t p e) t' p' = if t' = t ∧ p' = p then e else backoffEnd b t' p' := by
  have key : ∀ b : List ((String × PeerId) × Nat), ¬ (t' = t ∧ p' = p) →
      (b.filter (·.1 != (t, p))).lookup (t', p') = b.lookup (t', p') := by
    intro b hne
    have hne' : ((t', p') == (t, p)) = false := by simpa [Prod.ext_iff] using hne
    induction b with
    | nil => rfl
    | cons x b ih =>
      obtain ⟨k, n⟩ := x
      by_cases hk : k = (t, p)
      · subst hk
        simp [List.lookup, List.filter, ih, hne']
      · have h1 : (k != (t, p)) = true := by simpa using hk
        simp [List.lookup, List.filter, h1, ih]
  unfold backoffEnd setBackoff
  by_cases h : t' = t ∧ p' = p
  · obtain ⟨rfl, rfl⟩ := h; simp [List.lookup]
  · have : ((t', p') == (t, p)) = false := by simpa [Prod.ext_iff] using h
    simp [List.lookup, h, key b h, this]

/-- Extending the backoffs of a list of peers on one topic never lowers any end. -/
theorem backoffEnd_fold_mono (t' : String) (ends : Nat) (l : List PeerId) (t : String)
    (q : PeerId) (b : List ((String × PeerId) × Nat)) :
    backoffEnd b t q ≤ backoffEnd (l.foldl (fun b q => extendBackoff b t' q ends) b) t q := by
  induction l generalizing b with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    refine Nat.le_trans ?_ (ih _)
    simp only [extendBackoff, backoffEnd_setBackoff]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact Nat.le_max_left _ _
    · exact Nat.le_refl _

/-- Extending the backoffs of a list of peers on a topic makes each end at least the given end. -/
theorem backoffEnd_fold_mem (t : String) (ends : Nat) (l : List PeerId) (q : PeerId)
    (hq : q ∈ l) (b : List ((String × PeerId) × Nat)) :
    ends ≤ backoffEnd (l.foldl (fun b q => extendBackoff b t q ends) b) t q := by
  induction l generalizing b with
  | nil => simp at hq
  | cons x l ih =>
    rcases List.mem_cons.mp hq with rfl | hq'
    · refine Nat.le_trans ?_ (backoffEnd_fold_mono t ends l t q _)
      simp only [extendBackoff, backoffEnd_setBackoff, true_and, ↓reduceIte]
      exact Nat.le_max_right _ _
    · exact ih hq' _

/-- Inserting an ID into the seen cache keeps every ID that it held. -/
private theorem contains_insert_mono (c : SeenCache) (now ttl : Nat) (id id' : MessageId)
    (h : c.contains now ttl id' = true) : (c.insert now id).contains now ttl id' = true := by
  simp only [SeenCache.contains, SeenCache.insert, List.any_cons, Bool.or_eq_true] at h ⊢
  exact Or.inr h

section Graft

variable (p : GossipsubParameters) (backoffMs now : Nat) (src : PeerId) (s : RouterState)
  (out : Out) (g : Graft)

/-- The four things that a GRAFT does: answer a PRUNE, extend a backoff, nothing, or join. -/
private theorem graft_cases :
    (src ∈ s.explicit ∧ receiveGraft p backoffMs now src (s, out) g =
      (s, { out with control := out.control ++ [(src, pruneOf g.topicId 0)] })) ∨
    (src ∉ s.explicit ∧ g.topicId ∈ s.topics ∧ now < backoffEnd s.backoff g.topicId src ∧
      receiveGraft p backoffMs now src (s, out) g =
      ({ s with
          mesh := setPeers s.mesh g.topicId ((peersOf s.mesh g.topicId).filter (· != src))
          backoff := setBackoff s.backoff g.topicId src
            (backoffEnd s.backoff g.topicId src + backoffMs) },
        { out with control := out.control ++ [(src, pruneOf g.topicId
          (remainingSeconds now (backoffEnd s.backoff g.topicId src + backoffMs)))] })) ∨
    (src ∉ s.explicit ∧ (g.topicId ∉ s.topics ∨ ¬ now < backoffEnd s.backoff g.topicId src) ∧
      receiveGraft p backoffMs now src (s, out) g = (s, out)) ∨
    (src ∉ s.explicit ∧ g.topicId ∈ s.topics ∧ ¬ now < backoffEnd s.backoff g.topicId src ∧
      src ∉ peersOf s.mesh g.topicId ∧
      ((peersOf s.mesh g.topicId).length < p.D_high ∨ src ∈ s.outbound) ∧
      receiveGraft p backoffMs now src (s, out) g =
      ({ s with mesh := setPeers s.mesh g.topicId (peersOf s.mesh g.topicId ++ [src]) }, out)) := by
  by_cases h1 : src ∈ s.explicit
  · exact Or.inl ⟨h1, by simp [receiveGraft, h1]⟩
  by_cases h2' : g.topicId ∉ s.topics
  · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inl h2', by simp [receiveGraft, h1, h2']⟩))
  have h2 : g.topicId ∈ s.topics := by simpa using h2'
  by_cases h3 : now < backoffEnd s.backoff g.topicId src
  · exact Or.inr (Or.inl ⟨h1, h2, h3, by simp [receiveGraft, h1, h2, h3]⟩)
  by_cases h4 : src ∈ peersOf s.mesh g.topicId
  · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr h3, by simp [receiveGraft, h1, h2, h3, h4]⟩))
  by_cases h5 : p.D_high ≤ (peersOf s.mesh g.topicId).length ∧ src ∉ s.outbound
  · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr h3, by simp [receiveGraft, h1, h2, h3, h4, h5]⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, h4, ?_, ?_⟩))
    · rcases Nat.lt_or_ge (peersOf s.mesh g.topicId).length p.D_high with h | h
      · exact Or.inl h
      · exact Or.inr (Classical.byContradiction fun h' => h5 ⟨h, h'⟩)
    · simp [receiveGraft, h1, h2, h3, h4, h5]

/-- A GRAFT keeps the topics, the explicit and outbound peers, the cache and the other outputs. -/
private theorem graft_fields :
    (receiveGraft p backoffMs now src (s, out) g).1.topics = s.topics ∧
    (receiveGraft p backoffMs now src (s, out) g).1.explicit = s.explicit ∧
    (receiveGraft p backoffMs now src (s, out) g).1.outbound = s.outbound ∧
    (receiveGraft p backoffMs now src (s, out) g).1.mcache = s.mcache ∧
    (receiveGraft p backoffMs now src (s, out) g).2.forward = out.forward ∧
    (receiveGraft p backoffMs now src (s, out) g).2.delivered = out.delivered ∧
    (receiveGraft p backoffMs now src (s, out) g).2.answers = out.answers ∧
    (receiveGraft p backoffMs now src (s, out) g).1.seen = s.seen := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp [h]

/-- A GRAFT keeps the control messages already sent. -/
private theorem graft_control_mono {x : PeerId × Control} (hx : x ∈ out.control) :
    x ∈ (receiveGraft p backoffMs now src (s, out) g).2.control := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp [h, hx]

/-- A GRAFT never shortens the backoff of its sender. -/
private theorem graft_backoff_mono (t : String) :
    backoffEnd s.backoff t src ≤
      backoffEnd (receiveGraft p backoffMs now src (s, out) g).1.backoff t src := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, _, e⟩
  · simp [e]
  · rw [e]
    simp only [backoffEnd_setBackoff]
    by_cases h : t = g.topicId
    · subst h; simp
    · simp [h]
  · simp [e]
  · simp [e]

/-- A GRAFT adds new control messages that carry no IWANT. -/
private theorem graft_control_iwant {x : PeerId × Control}
    (hx : x ∈ (receiveGraft p backoffMs now src (s, out) g).2.control) :
    x ∈ out.control ∨ x.2.iwant = [] := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [h] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr rfl
  · rw [h] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr rfl
  · rw [h] at hx
    exact Or.inl hx
  · rw [h] at hx
    exact Or.inl hx

/-- A GRAFT moves an end of the backoff of its sender only above now. -/
private theorem graft_step_backoff (t : String)
    (h : backoffEnd (receiveGraft p backoffMs now src (s, out) g).1.backoff t src ≤ now) :
    backoffEnd (receiveGraft p backoffMs now src (s, out) g).1.backoff t src =
      backoffEnd s.backoff t src := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, e⟩ | ⟨_, _, h3, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, _, e⟩
  · simp [e]
  · rw [e] at h ⊢
    simp only [backoffEnd_setBackoff] at h ⊢
    by_cases ht : t = g.topicId
    · subst ht; simp at h; omega
    · simp [ht]
  · simp [e]
  · simp [e]

/-- A GRAFT whose sender is out of its backoff for a topic keeps its mesh or extends it. -/
private theorem graft_step_sublist (t : String)
    (h : backoffEnd (receiveGraft p backoffMs now src (s, out) g).1.backoff t src ≤ now) :
    (peersOf s.mesh t).Sublist
      (peersOf (receiveGraft p backoffMs now src (s, out) g).1.mesh t) := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, e⟩ | ⟨_, _, h3, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, _, _, e⟩
  · simp [e]
  · rw [e] at h ⊢
    simp only [backoffEnd_setBackoff] at h
    by_cases ht : t = g.topicId
    · subst ht; simp at h; omega
    · simp [peersOf_setPeers, ht]
  · simp [e]
  · rw [e]
    simp only [peersOf_setPeers]
    by_cases ht : t = g.topicId
    · subst ht; simp
    · simp [ht]

/-- A GRAFT adds only its sender to a mesh, and only by the rules. -/
private theorem graft_step_mesh (t : String) :
    ∀ x ∈ peersOf (receiveGraft p backoffMs now src (s, out) g).1.mesh t,
      x ∈ peersOf s.mesh t ∨ (x = src ∧ t = g.topicId ∧ g.topicId ∈ s.topics ∧ src ∉ s.explicit ∧
        backoffEnd s.backoff t src ≤ now ∧
        ((peersOf s.mesh t).length < p.D_high ∨ src ∈ s.outbound)) := by
  intro x hx
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨_, _, e⟩ | ⟨h1, h2, h3, h4, h5, e⟩
  · left; simpa [e] using hx
  · left
    rw [e] at hx
    simp only [peersOf_setPeers] at hx
    by_cases ht : t = g.topicId
    · simp only [ht, ↓reduceIte, List.mem_filter] at hx
      rw [ht]; exact hx.1
    · simpa [ht] using hx
  · left; simpa [e] using hx
  · rw [e] at hx
    simp only [peersOf_setPeers] at hx
    by_cases ht : t = g.topicId
    · subst ht
      simp only [↓reduceIte, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr ⟨rfl, rfl, h2, h1, by omega, h5⟩
    · left; simpa [ht] using hx

/-- A GRAFT from an explicit peer, or in a backoff for a joined topic, is answered with a PRUNE. -/
private theorem graft_prune
    (h : src ∈ s.explicit ∨ (g.topicId ∈ s.topics ∧ now < backoffEnd s.backoff g.topicId src)) :
    ∃ b, (src, pruneOf g.topicId b) ∈ (receiveGraft p backoffMs now src (s, out) g).2.control := by
  rcases graft_cases p backoffMs now src s out g with
    ⟨_, e⟩ | ⟨_, _, _, e⟩ | ⟨h1, h2, _⟩ | ⟨h1, h2, h3, _, _, e⟩
  · exact ⟨0, by simp [e]⟩
  · exact ⟨remainingSeconds now (backoffEnd s.backoff g.topicId src + backoffMs), by simp [e]⟩
  · rcases h with h | ⟨h3, h4⟩
    · exact absurd h h1
    · rcases h2 with h2 | h2
      · exact absurd h3 h2
      · exact absurd h4 h2
  · rcases h with h | ⟨_, h⟩
    · exact absurd h h1
    · exact absurd h h3

end Graft

section Message

variable (p : GossipsubParameters) (msgId : Message → MessageId)
  (validate : Message → ValidationResult) (now : Nat) (s : RouterState) (out : Out) (m : Message)

/-- A message changes only the caches, and adds only an accepted, new message to the outputs. -/
private theorem message_step :
    (∃ se mc, (receiveMessage p msgId validate now (s, out) m).1 =
      { s with seen := se, mcache := mc } ∧
      ∀ id, s.seen.contains now (p.seen_ttl * 1000) id = true →
        se.contains now (p.seen_ttl * 1000) id = true) ∧
    (∀ x ∈ (receiveMessage p msgId validate now (s, out) m).2.forward,
      x ∈ out.forward ∨ (x.2 = m ∧ m.topic ∈ s.topics ∧
        s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false ∧ validate m = .accept)) ∧
    (∀ y ∈ (receiveMessage p msgId validate now (s, out) m).2.delivered,
      y ∈ out.delivered ∨ (y = m ∧ m.topic ∈ s.topics ∧
        s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false ∧ validate m = .accept)) ∧
    (receiveMessage p msgId validate now (s, out) m).2.control = out.control ∧
    (receiveMessage p msgId validate now (s, out) m).2.answers = out.answers := by
  unfold receiveMessage
  by_cases hs : m.topic ∉ s.topics ∨ s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true
  · simp only [hs, ↓reduceIte]
    exact ⟨⟨s.seen, s.mcache, rfl, fun _ h => h⟩, fun x hx => Or.inl hx, fun x hx => Or.inl hx,
      trivial, trivial⟩
  · have ht : m.topic ∈ s.topics := Classical.byContradiction fun h => hs (Or.inl h)
    have hc : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false := by
      cases hh : s.seen.contains now (p.seen_ttl * 1000) (msgId m)
      · rfl
      · exact absurd (Or.inr hh) hs
    simp only [hs, ↓reduceIte]
    have mono : ∀ id, s.seen.contains now (p.seen_ttl * 1000) id = true →
        (s.seen.insert now (msgId m)).contains now (p.seen_ttl * 1000) id = true :=
      fun id h => contains_insert_mono _ _ _ _ _ h
    cases hv : validate m with
    | accept =>
      refine ⟨⟨_, _, rfl, mono⟩, ?_, ?_, rfl, rfl⟩
      · intro x hx
        simp only [List.mem_append, List.mem_map] at hx
        rcases hx with hx | ⟨a, _, rfl⟩
        · exact Or.inl hx
        · exact Or.inr ⟨rfl, ht, hc, rfl⟩
      · intro y hy
        simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | hy
        · exact Or.inl hy
        · exact Or.inr ⟨hy, ht, hc, rfl⟩
    | ignore r =>
      exact ⟨⟨_, s.mcache, rfl, mono⟩, fun x hx => Or.inl hx, fun x hx => Or.inl hx, rfl, rfl⟩
    | reject r =>
      exact ⟨⟨_, s.mcache, rfl, mono⟩, fun x hx => Or.inl hx, fun x hx => Or.inl hx, rfl, rfl⟩

/-- Receiving a message keeps the entries of the seen cache.

A message that it forwards or delivers has its ID there, with the current time. -/
private theorem message_step_seen :
    (∀ e ∈ s.seen.entries, e ∈ (receiveMessage p msgId validate now (s, out) m).1.seen.entries) ∧
    (∀ x ∈ (receiveMessage p msgId validate now (s, out) m).2.forward, x ∈ out.forward ∨
      (x.2 = m ∧ (msgId m, now) ∈
        (receiveMessage p msgId validate now (s, out) m).1.seen.entries)) ∧
    (∀ y ∈ (receiveMessage p msgId validate now (s, out) m).2.delivered, y ∈ out.delivered ∨
      (y = m ∧ (msgId m, now) ∈
        (receiveMessage p msgId validate now (s, out) m).1.seen.entries)) := by
  unfold receiveMessage
  by_cases hs : m.topic ∉ s.topics ∨ s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true
  · simp only [hs, ↓reduceIte]
    exact ⟨fun e he => he, fun x hx => Or.inl hx, fun y hy => Or.inl hy⟩
  · simp only [hs, ↓reduceIte]
    cases hv : validate m with
    | accept =>
      refine ⟨fun e he => by simp [SeenCache.insert, he], fun x hx => ?_, fun y hy => ?_⟩
      · simp only [List.mem_append, List.mem_map] at hx
        rcases hx with hx | ⟨a, _, rfl⟩
        · exact Or.inl hx
        · exact Or.inr ⟨rfl, by simp [SeenCache.insert]⟩
      · simp only [List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact Or.inl hy
        · exact Or.inr ⟨rfl, by simp [SeenCache.insert]⟩
    | ignore r =>
      exact ⟨fun e he => by simp [SeenCache.insert, he], fun x hx => Or.inl hx,
        fun y hy => Or.inl hy⟩
    | reject r =>
      exact ⟨fun e he => by simp [SeenCache.insert, he], fun x hx => Or.inl hx,
        fun y hy => Or.inl hy⟩

end Message

section Prune

/-- A PRUNE only removes a peer from a mesh, and leaves the topics, peers and caches. -/
private theorem prune_step (pruneBackoffMs now : Nat) (src : PeerId) (s : RouterState)
    (q : Prune) :
    (receivePrune pruneBackoffMs now src s q).topics = s.topics ∧
    (receivePrune pruneBackoffMs now src s q).explicit = s.explicit ∧
    (receivePrune pruneBackoffMs now src s q).mcache = s.mcache ∧
    (receivePrune pruneBackoffMs now src s q).seen = s.seen ∧
    ∀ t x, x ∈ peersOf (receivePrune pruneBackoffMs now src s q).mesh t →
      x ∈ peersOf s.mesh t := by
  by_cases ht : q.topicId ∈ s.topics
  · refine ⟨by simp [receivePrune, ht], by simp [receivePrune, ht], by simp [receivePrune, ht],
      by simp [receivePrune, ht], fun t x hx => ?_⟩
    simp only [receivePrune, ht, not_true_eq_false, ↓reduceIte, peersOf_setPeers] at hx
    by_cases h : t = q.topicId
    · simp only [h, ↓reduceIte, List.mem_filter] at hx
      rw [h]; exact hx.1
    · simpa [h] using hx
  · have e : receivePrune pruneBackoffMs now src s q = s := by simp [receivePrune, ht]
    rw [e]
    exact ⟨rfl, rfl, rfl, rfl, fun t x hx => hx⟩

end Prune

section Folds

variable (p : GossipsubParameters) (backoffMs pruneBackoffMs now : Nat) (src : PeerId)

/-- The fold of the messages starts from any state, and sends no control message. -/
private theorem message_fold (msgId : Message → MessageId)
    (validate : Message → ValidationResult) (s0 : RouterState) (l : List Message) :
    (∃ se mc, (l.foldl (receiveMessage p msgId validate now) (s0, {})).1 =
      { s0 with seen := se, mcache := mc } ∧
      ∀ id, s0.seen.contains now (p.seen_ttl * 1000) id = true →
        se.contains now (p.seen_ttl * 1000) id = true) ∧
    (∀ x ∈ (l.foldl (receiveMessage p msgId validate now) (s0, {})).2.forward,
      x.2 ∈ l ∧ x.2.topic ∈ s0.topics ∧
        s0.seen.contains now (p.seen_ttl * 1000) (msgId x.2) = false ∧ validate x.2 = .accept) ∧
    (∀ y ∈ (l.foldl (receiveMessage p msgId validate now) (s0, {})).2.delivered,
      y ∈ l ∧ y.topic ∈ s0.topics ∧
        s0.seen.contains now (p.seen_ttl * 1000) (msgId y) = false ∧ validate y = .accept) ∧
    (l.foldl (receiveMessage p msgId validate now) (s0, {})).2.control = [] ∧
    (l.foldl (receiveMessage p msgId validate now) (s0, {})).2.answers = [] := by
  have H := foldl_inv l (fun a : RouterState × Out =>
    (∃ se mc, a.1 = { s0 with seen := se, mcache := mc } ∧
      ∀ id, s0.seen.contains now (p.seen_ttl * 1000) id = true →
        se.contains now (p.seen_ttl * 1000) id = true) ∧
    (∀ x ∈ a.2.forward, x.2 ∈ l ∧ x.2.topic ∈ s0.topics ∧
      s0.seen.contains now (p.seen_ttl * 1000) (msgId x.2) = false ∧ validate x.2 = .accept) ∧
    (∀ y ∈ a.2.delivered, y ∈ l ∧ y.topic ∈ s0.topics ∧
      s0.seen.contains now (p.seen_ttl * 1000) (msgId y) = false ∧ validate y = .accept) ∧
    a.2.control = [] ∧ a.2.answers = []) (receiveMessage p msgId validate now) ?_
    (b := (s0, {})) ⟨⟨s0.seen, s0.mcache, rfl, fun _ h => h⟩, by simp, by simp, rfl, rfl⟩
  · exact H
  rintro ⟨s, o⟩ m hm ⟨⟨se, mc, hs, hmono⟩, hf, hd, hc, ha⟩
  simp only at hs hf hd hc ha
  subst hs
  obtain ⟨⟨se', mc', hs', hmono'⟩, hf', hd', hc', ha'⟩ :=
    message_step p msgId validate now { s0 with seen := se, mcache := mc } o m
  refine ⟨⟨se', mc', ?_, fun id h => hmono' id (hmono id h)⟩, ?_, ?_, ?_, ?_⟩
  · rw [hs']
  · intro x hx
    rcases hf' x hx with h | ⟨h1, h2, h3, h4⟩
    · exact hf x h
    · rw [h1]
      refine ⟨hm, h2, ?_, h4⟩
      cases hh : s0.seen.contains now (p.seen_ttl * 1000) (msgId m)
      · rfl
      · have := hmono' _ (hmono _ hh)
        simp_all
  · intro y hy
    rcases hd' y hy with h | ⟨h1, h2, h3, h4⟩
    · exact hd y h
    · rw [h1]
      refine ⟨hm, h2, ?_, h4⟩
      cases hh : s0.seen.contains now (p.seen_ttl * 1000) (msgId m)
      · rfl
      · have := hmono' _ (hmono _ hh)
        simp_all
  · rw [hc', hc]
  · rw [ha', ha]

/-- The fold of the GRAFTs: what it keeps, what it adds to the mesh, and how a backoff grows. -/
private theorem graft_fold (a1 : RouterState × Out) (l : List Graft) :
    let a2 := l.foldl (receiveGraft p backoffMs now src) a1
    a2.1.topics = a1.1.topics ∧ a2.1.explicit = a1.1.explicit ∧ a2.1.outbound = a1.1.outbound ∧
    a2.1.mcache = a1.1.mcache ∧ a2.2.forward = a1.2.forward ∧ a2.2.delivered = a1.2.delivered ∧
    a2.2.answers = a1.2.answers ∧ (∀ x ∈ a1.2.control, x ∈ a2.2.control) ∧
    a2.1.seen = a1.1.seen ∧
    (∀ x ∈ a2.2.control, x ∈ a1.2.control ∨ x.2.iwant = []) ∧
    (∀ t, ∀ x ∈ peersOf a2.1.mesh t, x ∈ peersOf a1.1.mesh t ∨
      (x = src ∧ t ∈ a1.1.topics ∧ src ∉ a1.1.explicit ∧ backoffEnd a1.1.backoff t src ≤ now ∧
        ((peersOf a1.1.mesh t).length < p.D_high ∨ src ∈ a1.1.outbound) ∧
        ∃ g ∈ l, g.topicId = t)) := by
  intro a2
  have H := foldl_inv l (fun a : RouterState × Out =>
    a.1.topics = a1.1.topics ∧ a.1.explicit = a1.1.explicit ∧ a.1.outbound = a1.1.outbound ∧
    a.1.mcache = a1.1.mcache ∧ a.2.forward = a1.2.forward ∧ a.2.delivered = a1.2.delivered ∧
    a.2.answers = a1.2.answers ∧ (∀ x ∈ a1.2.control, x ∈ a.2.control) ∧
    a.1.seen = a1.1.seen ∧
    (∀ x ∈ a.2.control, x ∈ a1.2.control ∨ x.2.iwant = []) ∧
    (∀ t, ∀ x ∈ peersOf a.1.mesh t, x ∈ peersOf a1.1.mesh t ∨
      (x = src ∧ t ∈ a1.1.topics ∧ src ∉ a1.1.explicit ∧ backoffEnd a1.1.backoff t src ≤ now ∧
        ((peersOf a1.1.mesh t).length < p.D_high ∨ src ∈ a1.1.outbound) ∧
        ∃ g ∈ l, g.topicId = t)) ∧
    (∀ t, backoffEnd a.1.backoff t src ≤ now →
      backoffEnd a.1.backoff t src = backoffEnd a1.1.backoff t src) ∧
    (∀ t, backoffEnd a.1.backoff t src ≤ now →
      (peersOf a1.1.mesh t).Sublist (peersOf a.1.mesh t)))
    (receiveGraft p backoffMs now src) ?_
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun x hx => hx, rfl, fun x hx => Or.inl hx,
      fun t x hx => Or.inl hx, fun t _ => rfl, fun t _ => List.Sublist.refl _⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -, -⟩ := H
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  rintro ⟨s, o⟩ g hg ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := graft_fields p backoffMs now src s o g
  have S1 := graft_step_backoff p backoffMs now src s o g
  have S2 := graft_step_sublist p backoffMs now src s o g
  have S3 := graft_step_mesh p backoffMs now src s o g
  have bm := graft_backoff_mono p backoffMs now src s o g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f1, h1]
  · rw [f2, h2]
  · rw [f3, h3]
  · rw [f4, h4]
  · rw [f5, h5]
  · rw [f6, h6]
  · rw [f7, h7]
  · exact fun x hx => graft_control_mono p backoffMs now src s o g (h8 x hx)
  · rw [f8, h9]
  · intro x hx
    rcases graft_control_iwant p backoffMs now src s o g hx with h | h
    · exact h10 x h
    · exact Or.inr h
  · intro t x hx
    rcases S3 t x hx with h | ⟨k1, k2, k3, k4, k5, k6⟩
    · exact h11 t x h
    · subst k2
      have hc := h12 g.topicId k5
      have hl := (h13 g.topicId k5).length_le
      refine Or.inr ⟨k1, ?_, ?_, ?_, ?_, g, hg, rfl⟩
      · rw [← h1]; exact k3
      · rw [← h2]; exact k4
      · rw [← hc]; exact k5
      · rcases k6 with k6 | k6
        · exact Or.inl (by omega)
        · exact Or.inr (by rw [← h3]; exact k6)
  · intro t ht
    have e := S1 t ht
    exact e.trans (h12 t (by omega))
  · intro t ht
    have e := S1 t ht
    exact (h13 t (by omega)).trans (S2 t ht)

/-- A GRAFT of the list that is owed a PRUNE gets one, whatever the other GRAFTs do. -/
private theorem graft_fold_prune {g : Graft} (l : List Graft) (hg : g ∈ l)
    (acc : RouterState × Out)
    (h : src ∈ acc.1.explicit ∨
      (g.topicId ∈ acc.1.topics ∧ now < backoffEnd acc.1.backoff g.topicId src)) :
    ∃ b, (src, pruneOf g.topicId b) ∈
      (l.foldl (receiveGraft p backoffMs now src) acc).2.control := by
  induction l generalizing acc with
  | nil => simp at hg
  | cons x l ih =>
    obtain ⟨s, o⟩ := acc
    simp only [List.foldl]
    rcases List.mem_cons.mp hg with rfl | hg
    · obtain ⟨b, hb⟩ := graft_prune p backoffMs now src s o g h
      have G := graft_fold p backoffMs now src (receiveGraft p backoffMs now src (s, o) g) l
      exact ⟨b, G.2.2.2.2.2.2.2.1 _ hb⟩
    · apply ih hg
      obtain ⟨f1, f2, -⟩ := graft_fields p backoffMs now src s o x
      rw [f1, f2]
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, Nat.lt_of_lt_of_le h2 (graft_backoff_mono p backoffMs now src s o x _)⟩

/-- The fold of the messages keeps the seen entries, and records the ID of each message it sends.

The ID is recorded with the time of the RPC. -/
private theorem message_fold_seen (msgId : Message → MessageId)
    (validate : Message → ValidationResult) (s0 : RouterState) (l : List Message) :
    (∀ e ∈ s0.seen.entries,
      e ∈ (l.foldl (receiveMessage p msgId validate now) (s0, {})).1.seen.entries) ∧
    (∀ x ∈ (l.foldl (receiveMessage p msgId validate now) (s0, {})).2.forward,
      (msgId x.2, now) ∈
        (l.foldl (receiveMessage p msgId validate now) (s0, {})).1.seen.entries) ∧
    (∀ y ∈ (l.foldl (receiveMessage p msgId validate now) (s0, {})).2.delivered,
      (msgId y, now) ∈
        (l.foldl (receiveMessage p msgId validate now) (s0, {})).1.seen.entries) := by
  refine foldl_inv l (fun a : RouterState × Out =>
    (∀ e ∈ s0.seen.entries, e ∈ a.1.seen.entries) ∧
    (∀ x ∈ a.2.forward, (msgId x.2, now) ∈ a.1.seen.entries) ∧
    (∀ y ∈ a.2.delivered, (msgId y, now) ∈ a.1.seen.entries))
    (receiveMessage p msgId validate now) ?_ ⟨fun e he => he, by simp, by simp⟩
  rintro ⟨s, o⟩ m _ ⟨h1, h2, h3⟩
  obtain ⟨k1, k2, k3⟩ := message_step_seen p msgId validate now s o m
  refine ⟨fun e he => k1 e (h1 e he), fun x hx => ?_, fun y hy => ?_⟩
  · rcases k2 x hx with h | ⟨rfl, h⟩
    · exact k1 _ (h2 x h)
    · exact h
  · rcases k3 y hy with h | ⟨rfl, h⟩
    · exact k1 _ (h3 y h)
    · exact h

/-- A GRAFT for a joined topic within the backoff of its sender puts the sender out of the mesh.

The later GRAFTs of the fold keep it out, since none of them ends the backoff. -/
private theorem graft_fold_leave (t : String) (l : List Graft) (acc : RouterState × Out)
    (hb : now < backoffEnd acc.1.backoff t src) (hx : src ∉ acc.1.explicit)
    (ht : t ∈ acc.1.topics) (h : src ∉ peersOf acc.1.mesh t ∨ ∃ g ∈ l, g.topicId = t) :
    src ∉ peersOf (l.foldl (receiveGraft p backoffMs now src) acc).1.mesh t := by
  induction l generalizing acc with
  | nil =>
    rcases h with h | ⟨g, hg, -⟩
    · exact h
    · simp at hg
  | cons g l ih =>
    obtain ⟨s, o⟩ := acc
    simp only [List.foldl]
    obtain ⟨f1, f2, -⟩ := graft_fields p backoffMs now src s o g
    have bm := graft_backoff_mono p backoffMs now src s o g t
    apply ih _ (Nat.lt_of_lt_of_le hb bm) (by rw [f2]; exact hx) (by rw [f1]; exact ht)
    by_cases hg : g.topicId = t
    · left
      subst hg
      rcases graft_cases p backoffMs now src s o g with
        ⟨h1, -⟩ | ⟨-, -, -, e⟩ | ⟨-, h2, -⟩ | ⟨-, -, h3, -⟩
      · exact absurd h1 hx
      · rw [e]
        simp [peersOf_setPeers]
      · rcases h2 with h2 | h2
        · exact absurd ht h2
        · exact absurd hb h2
      · exact absurd hb h3
    · rcases h with h | ⟨g', hg', ht'⟩
      · left
        intro hm
        rcases graft_step_mesh p backoffMs now src s o g t src hm with h' | ⟨-, -, -, -, h', -⟩
        · exact h h'
        · simp only at hb
          omega
      · rcases List.mem_cons.mp hg' with rfl | hg'
        · exact absurd ht' hg
        · exact Or.inr ⟨g', hg', ht'⟩

/-- The fold of the PRUNEs only removes mesh peers, and keeps the rest that matters. -/
private theorem prune_fold (s : RouterState) (l : List Prune) :
    let r := l.foldl (receivePrune pruneBackoffMs now src) s
    r.topics = s.topics ∧ r.explicit = s.explicit ∧ r.mcache = s.mcache ∧ r.seen = s.seen ∧
    ∀ t x, x ∈ peersOf r.mesh t → x ∈ peersOf s.mesh t := by
  intro r
  refine foldl_inv l (fun r : RouterState => r.topics = s.topics ∧ r.explicit = s.explicit ∧
    r.mcache = s.mcache ∧ r.seen = s.seen ∧ ∀ t x, x ∈ peersOf r.mesh t → x ∈ peersOf s.mesh t)
    (receivePrune pruneBackoffMs now src) ?_ ⟨rfl, rfl, rfl, rfl, fun t x hx => hx⟩
  intro r q _ ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨p1, p2, p3, p4, p5⟩ := prune_step pruneBackoffMs now src r q
  exact ⟨p1.trans h1, p2.trans h2, p3.trans h3, p4.trans h4, fun t x hx => h5 t x (p5 t x hx)⟩

/-- The IHAVEs change no output but the control messages, drop none, and add only IWANTs. -/
private theorem ihave_fold (s : RouterState) (o : Out) (l : List IHave) :
    let r := l.foldl (receiveIHave p now src s) o
    r.forward = o.forward ∧ r.delivered = o.delivered ∧ r.answers = o.answers ∧
    (∀ x ∈ o.control, x ∈ r.control) ∧
    ∀ x ∈ r.control, x ∈ o.control ∨ (x.1 = src ∧ ∃ i ∈ l, i.topicId ∈ s.topics ∧
      ∃ ids, x.2 = { iwant := [{ messageIds := ids }] } ∧ ∀ b ∈ ids, b ∈ i.messageIds ∧
        ∃ id, MessageId.ofBytes? b = some id ∧
          s.seen.contains now (p.seen_ttl * 1000) id = false) := by
  intro r
  refine foldl_inv l (fun r : Out => r.forward = o.forward ∧ r.delivered = o.delivered ∧
    r.answers = o.answers ∧ (∀ x ∈ o.control, x ∈ r.control) ∧
    ∀ x ∈ r.control, x ∈ o.control ∨ (x.1 = src ∧ ∃ i ∈ l, i.topicId ∈ s.topics ∧
      ∃ ids, x.2 = { iwant := [{ messageIds := ids }] } ∧ ∀ b ∈ ids, b ∈ i.messageIds ∧
        ∃ id, MessageId.ofBytes? b = some id ∧
          s.seen.contains now (p.seen_ttl * 1000) id = false))
    (receiveIHave p now src s) ?_ ⟨rfl, rfl, rfl, fun x hx => hx, fun x hx => Or.inl hx⟩
  intro r h hh ⟨h1, h2, h3, h4, h5⟩
  by_cases ht : h.topicId ∈ s.topics
  · simp only [receiveIHave, ht, not_true_eq_false, ↓reduceIte]
    split
    · exact ⟨h1, h2, h3, h4, h5⟩
    · refine ⟨h1, h2, h3, fun x hx => ?_, fun x hx => ?_⟩
      · simp [h4 x hx]
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h5 x hx
        · right
          refine ⟨rfl, h, hh, ht, _, rfl, fun b hb' => ?_⟩
          simp only [wantedIds, List.mem_filter] at hb'
          obtain ⟨hb1, hb2⟩ := hb'
          refine ⟨hb1, ?_⟩
          cases ho : MessageId.ofBytes? b with
          | none => simp [ho] at hb2
          | some id =>
            refine ⟨id, rfl, ?_⟩
            simpa [ho] using hb2
  · simp only [receiveIHave, ht, not_false_eq_true, ↓reduceIte]
    exact ⟨h1, h2, h3, h4, h5⟩

/-- The IWANTs answer only the sender, with messages that the cache holds under a named ID. -/
private theorem iwant_fold (s : RouterState) (o : Out) (l : List IWant) :
    let r := l.foldl (receiveIWant src s) o
    r.forward = o.forward ∧ r.delivered = o.delivered ∧ r.control = o.control ∧
    ∀ x ∈ r.answers, x ∈ o.answers ∨ (x.1 = src ∧ ∃ w ∈ l, ∃ b ∈ w.messageIds, ∃ id,
      MessageId.ofBytes? b = some id ∧ s.mcache.get id = some x.2) := by
  intro r
  refine foldl_inv l (fun r : Out => r.forward = o.forward ∧ r.delivered = o.delivered ∧
    r.control = o.control ∧
    ∀ x ∈ r.answers, x ∈ o.answers ∨ (x.1 = src ∧ ∃ w ∈ l, ∃ b ∈ w.messageIds, ∃ id,
      MessageId.ofBytes? b = some id ∧ s.mcache.get id = some x.2))
    (receiveIWant src s) ?_ ⟨rfl, rfl, rfl, fun x hx => Or.inl hx⟩
  intro r w hw ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, fun x hx => ?_⟩
  simp only [receiveIWant, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨m, hm, rfl⟩
  · exact h4 x hx
  · right
    refine ⟨rfl, w, hw, ?_⟩
    simp only [answeredMessages, List.mem_filterMap, Option.bind_eq_some_iff] at hm
    obtain ⟨b, hb, id, hid, hget⟩ := hm
    exact ⟨b, hb, id, hid, hget⟩

end Folds

section Rpc

variable (p : GossipsubParameters) (backoffMs pruneBackoffMs : Nat)
  (standing : PeerId → Standing) (msgId : Message → MessageId)
  (validate : Message → ValidationResult) (now : Nat) (src : PeerId) (rpc : Rpc) (s : RouterState)

/-- The RPC of a peer that is not ignored is the chain of its folds. -/
private theorem receiveRpc_eq
    (h : ¬ ((standing src).belowGraylist = true ∧ src ∉ s.explicit)) :
    ∃ pt s1 a1 a2 s3, pt = rpc.subscriptions.foldl (applySubscription src) s.peerTopics ∧
      s1 = { s with peerTopics := pt } ∧
      a1 = rpc.publish.foldl (receiveMessage p msgId validate now) (s1, {}) ∧
      a2 = rpc.control.graft.foldl (receiveGraft p backoffMs now src) a1 ∧
      s3 = rpc.control.prune.foldl (receivePrune pruneBackoffMs now src) a2.1 ∧
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1 = s3 ∧
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2 =
        if (standing src).belowGossip = true ∧ src ∉ s3.explicit then a2.2
        else rpc.control.iwant.foldl (receiveIWant src s3)
          (rpc.control.ihave.foldl (receiveIHave p now src s3) a2.2) := by
  refine ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;>
    simp only [receiveRpc, h, ite_false] <;> split <;> rfl

/-- The tail of an RPC keeps the forwards and deliveries, drops no control, and answers an IWANT. -/
private theorem tail_props (c : Prop) [Decidable c] (o fo : Out) (s3 : RouterState)
    (ctrl : Control)
    (hfo : fo = if c then o else ctrl.iwant.foldl (receiveIWant src s3)
      (ctrl.ihave.foldl (receiveIHave p now src s3) o)) :
    fo.forward = o.forward ∧ fo.delivered = o.delivered ∧ (∀ x ∈ o.control, x ∈ fo.control) ∧
    (∀ x ∈ fo.answers, x ∈ o.answers ∨ (x.1 = src ∧ ∃ w ∈ ctrl.iwant, ∃ b ∈ w.messageIds, ∃ id,
      MessageId.ofBytes? b = some id ∧ s3.mcache.get id = some x.2)) ∧
    (c → fo = o) ∧
    ∀ x ∈ fo.control, x ∈ o.control ∨ (x.1 = src ∧ ∃ i ∈ ctrl.ihave, i.topicId ∈ s3.topics ∧
      ∃ ids, x.2 = { iwant := [{ messageIds := ids }] } ∧ ∀ b ∈ ids, b ∈ i.messageIds ∧
        ∃ id, MessageId.ofBytes? b = some id ∧
          s3.seen.contains now (p.seen_ttl * 1000) id = false) := by
  by_cases hb : c
  · simp only [hb, ↓reduceIte] at hfo
    subst hfo
    exact ⟨rfl, rfl, fun x hx => hx, fun x hx => Or.inl hx, fun _ => rfl, fun x hx => Or.inl hx⟩
  · simp only [hb, ↓reduceIte] at hfo
    subst hfo
    obtain ⟨i1, i2, i3, i4, i5⟩ := ihave_fold p now src s3 o ctrl.ihave
    obtain ⟨w1, w2, w3, w4⟩ := iwant_fold src s3 (ctrl.ihave.foldl (receiveIHave p now src s3) o)
      ctrl.iwant
    refine ⟨w1.trans i1, w2.trans i2, fun x hx => ?_, fun x hx => ?_, fun h => absurd h hb,
      fun x hx => ?_⟩
    · rw [w3]; exact i4 x hx
    · rcases w4 x hx with h | h
      · exact Or.inl (i3 ▸ h)
      · exact Or.inr h
    · rw [w3] at hx
      exact i5 x hx

/-- Everything that the theorems need of the result of an RPC that is not ignored. -/
private theorem receiveRpc_facts (hn : ¬ ((standing src).belowGraylist = true ∧ src ∉ s.explicit))
    (r : RouterState × Out)
    (hr : receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s = r) :
    (∀ x ∈ r.2.forward, x.2 ∈ rpc.publish ∧ x.2.topic ∈ s.topics ∧
      s.seen.contains now (p.seen_ttl * 1000) (msgId x.2) = false ∧ validate x.2 = .accept) ∧
    (∀ y ∈ r.2.delivered, y ∈ rpc.publish ∧ y.topic ∈ s.topics ∧
      s.seen.contains now (p.seen_ttl * 1000) (msgId y) = false ∧ validate y = .accept) ∧
    (∀ t q, q ∈ peersOf r.1.mesh t → q ∈ peersOf s.mesh t ∨
      (q = src ∧ t ∈ s.topics ∧ src ∉ s.explicit ∧ backoffEnd s.backoff t src ≤ now ∧
        ((peersOf s.mesh t).length < p.D_high ∨ src ∈ s.outbound) ∧
        ∃ g ∈ rpc.control.graft, g.topicId = t)) ∧
    (∀ g ∈ rpc.control.graft, (src ∈ s.explicit ∨
      (g.topicId ∈ s.topics ∧ now < backoffEnd s.backoff g.topicId src)) →
      ∃ b, (src, pruneOf g.topicId b) ∈ r.2.control) ∧
    r.1.explicit = s.explicit ∧
    (∀ x ∈ r.2.answers, x.1 = src ∧ ∃ w ∈ rpc.control.iwant, ∃ b ∈ w.messageIds, ∃ id,
      MessageId.ofBytes? b = some id ∧ r.1.mcache.get id = some x.2) ∧
    (∀ x ∈ r.2.control, ∀ w ∈ x.2.iwant, x.1 = src ∧ ∃ i ∈ rpc.control.ihave,
      i.topicId ∈ s.topics ∧ ∀ b ∈ w.messageIds, b ∈ i.messageIds ∧ ∃ id,
        MessageId.ofBytes? b = some id ∧ s.seen.contains now (p.seen_ttl * 1000) id = false) ∧
    ((standing src).belowGossip = true → src ∉ s.explicit →
      r.2.answers = [] ∧ ∀ x ∈ r.2.control, x.2.iwant = []) := by
  obtain ⟨pt, s1, a1, a2, s3, hpt, hs1, ha1, ha2, hs3, hr1, hr2⟩ :=
    receiveRpc_eq p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn
  rw [hr] at hr1 hr2
  subst hs1
  obtain ⟨⟨se, mc, e1, mono⟩, M1, M2, M3, M4⟩ := message_fold p now msgId validate
    { s with peerTopics := pt } rpc.publish
  rw [← ha1] at e1 M1 M2 M3 M4
  have G := graft_fold p backoffMs now src a1 rpc.control.graft
  dsimp only at G
  rw [← ha2] at G
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11⟩ := G
  obtain ⟨P1, P2, P3, P4, P5⟩ := prune_fold pruneBackoffMs now src a2.1 rpc.control.prune
  rw [← hs3] at P1 P2 P3 P4 P5
  obtain ⟨T1, T2, T3, T4, T5, T6⟩ := tail_props p now src _ a2.2 _ s3 rpc.control hr2
  have hmesh1 : a1.1.mesh = s.mesh := by rw [e1]
  have htop1 : a1.1.topics = s.topics := by rw [e1]
  have hexp1 : a1.1.explicit = s.explicit := by rw [e1]
  have hbo1 : a1.1.backoff = s.backoff := by rw [e1]
  have hob1 : a1.1.outbound = s.outbound := by rw [e1]
  have hseen : ∀ id, s.seen.contains now (p.seen_ttl * 1000) id = true →
      s3.seen.contains now (p.seen_ttl * 1000) id = true := by
    intro id h
    rw [P4, G9, e1]
    exact mono id h
  have htop3 : s3.topics = s.topics := by rw [P1, G1, htop1]
  have hexp3 : s3.explicit = s.explicit := by rw [P2, G2, hexp1]
  subst hr1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [T1, G5] at hx
    exact M1 x hx
  · intro y hy
    rw [T2, G6] at hy
    exact M2 y hy
  · intro t q hq
    rcases G11 t q (P5 t q hq) with h | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl (by simpa [hmesh1] using h)
    · refine Or.inr ⟨h1, ?_, ?_, ?_, ?_, h6⟩
      · exact htop1 ▸ h2
      · exact hexp1 ▸ h3
      · exact hbo1 ▸ h4
      · simpa [hmesh1, hob1] using h5
  · intro g hg h
    obtain ⟨b, hb⟩ := graft_fold_prune p backoffMs now src rpc.control.graft hg a1
      (by rw [hexp1, htop1, hbo1]; exact h)
    exact ⟨b, T3 _ (by rw [ha2]; exact hb)⟩
  · rw [hexp3]
  · intro x hx
    rcases T4 x hx with h | h
    · rw [G7, M4] at h
      simp at h
    · exact h
  · intro x hx w hw
    rcases T6 x hx with h | ⟨k1, i, hi, k2, ids, k3, k4⟩
    · rcases G10 x h with h | h
      · rw [M3] at h
        simp at h
      · rw [h] at hw
        simp at hw
    · rw [k3] at hw
      simp only [List.mem_singleton] at hw
      subst hw
      refine ⟨k1, i, hi, htop3 ▸ k2, fun b hb => ?_⟩
      obtain ⟨hb1, id, hid, hc⟩ := k4 b hb
      refine ⟨hb1, id, hid, ?_⟩
      cases hh : s.seen.contains now (p.seen_ttl * 1000) id
      · rfl
      · rw [hseen id hh] at hc
        exact absurd hc (by simp)
  · intro hg hx
    have hc : (standing src).belowGossip = true ∧ src ∉ r.1.explicit :=
      ⟨hg, by rw [hexp3]; exact hx⟩
    have e := T5 hc
    refine ⟨by rw [e, G7, M4], fun x hx => ?_⟩
    rw [e] at hx
    rcases G10 x hx with h | h
    · rw [M3] at h
      simp at h
    · exact h

/-- An RPC that the graylist does not drop keeps the seen entries.

It records the ID of each message it forwards or delivers, with the time of the RPC. -/
private theorem receiveRpc_seen_facts
    (hn : ¬ ((standing src).belowGraylist = true ∧ src ∉ s.explicit)) (r : RouterState × Out)
    (hr : receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s = r) :
    (∀ e ∈ s.seen.entries, e ∈ r.1.seen.entries) ∧
    (∀ x ∈ r.2.forward, (msgId x.2, now) ∈ r.1.seen.entries) ∧
    (∀ y ∈ r.2.delivered, (msgId y, now) ∈ r.1.seen.entries) := by
  obtain ⟨pt, s1, a1, a2, s3, -, hs1, ha1, ha2, hs3, hr1, hr2⟩ :=
    receiveRpc_eq p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn
  rw [hr] at hr1 hr2
  subst hs1
  obtain ⟨S1, S2, S3⟩ := message_fold_seen p now msgId validate { s with peerTopics := pt }
    rpc.publish
  rw [← ha1] at S1 S2 S3
  have G := graft_fold p backoffMs now src a1 rpc.control.graft
  dsimp only at G
  rw [← ha2] at G
  obtain ⟨-, -, -, -, G5, G6, -, -, G9, -⟩ := G
  obtain ⟨-, -, -, P4, -⟩ := prune_fold pruneBackoffMs now src a2.1 rpc.control.prune
  rw [← hs3] at P4
  obtain ⟨T1, T2, -⟩ := tail_props p now src _ a2.2 _ s3 rpc.control hr2
  rw [hr1, P4, G9, T1, G5, T2, G6]
  exact ⟨S1, S2, S3⟩

/-- A GRAFT for a joined topic within the backoff of its sender puts the sender out of the mesh.

This needs a sender that is not explicit, in an RPC that the graylist does not drop. -/
private theorem receiveRpc_leave_facts
    (hn : ¬ ((standing src).belowGraylist = true ∧ src ∉ s.explicit)) {g : Graft}
    (hg : g ∈ rpc.control.graft) (hx : src ∉ s.explicit) (ht : g.topicId ∈ s.topics)
    (hb : now < backoffEnd s.backoff g.topicId src) :
    src ∉ peersOf
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.mesh
        g.topicId := by
  obtain ⟨pt, s1, a1, a2, s3, -, hs1, ha1, ha2, hs3, hr1, -⟩ :=
    receiveRpc_eq p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn
  subst hs1
  obtain ⟨⟨se, mc, e1, -⟩, -⟩ := message_fold p now msgId validate { s with peerTopics := pt }
    rpc.publish
  rw [← ha1] at e1
  have L := graft_fold_leave p backoffMs now src g.topicId rpc.control.graft a1
    (by rw [e1]; exact hb) (by rw [e1]; exact hx) (by rw [e1]; exact ht) (Or.inr ⟨g, hg, rfl⟩)
  rw [← ha2] at L
  obtain ⟨-, -, -, -, P5⟩ := prune_fold pruneBackoffMs now src a2.1 rpc.control.prune
  rw [← hs3] at P5
  rw [hr1]
  exact fun h => L (P5 _ _ h)

end Rpc

variable (p : GossipsubParameters) (backoffMs pruneBackoffMs : Nat)
  (standing : PeerId → Standing) (msgId : Message → MessageId)
  (validate : Message → ValidationResult) (now : Nat) (src : PeerId) (rpc : Rpc) (s : RouterState)

/-- The RPC of a graylisted peer that is not explicit changes nothing and sends nothing. -/
theorem receiveRpc_graylist (hg : (standing src).belowGraylist = true) (hx : src ∉ s.explicit) :
    receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s = (s, {}) := by
  simp [receiveRpc, hg, hx]

/-- Only a message of the RPC that its validation accepted is forwarded or delivered.

Its topic was joined, and its ID was not in the seen cache before the RPC. -/
theorem receiveRpc_forward_accept {q : PeerId} {m : Message}
    (h : (q, m) ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.forward ∨
      m ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.delivered) :
    m ∈ rpc.publish ∧ m.topic ∈ s.topics ∧
      s.seen.contains now (p.seen_ttl * 1000) (msgId m) = false ∧ validate m = .accept := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2] at h
    simp at h
  · obtain ⟨F, D, -⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId validate now
      src rpc s hn _ rfl
    rcases h with h | h
    · exact F _ h
    · exact D _ h

/-- A peer is in the mesh of a topic after the RPC only if it was there, or every rule let it in.

It then sent a GRAFT for the topic, which this node joined.

It is not explicit, and its backoff for the topic had ended.

The mesh was below the high bound before the RPC, or the peer is outbound. -/
theorem receiveRpc_mesh {t : String} {q : PeerId}
    (h : q ∈ peersOf
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.mesh t) :
    q ∈ peersOf s.mesh t ∨
      (q = src ∧ t ∈ s.topics ∧ src ∉ s.explicit ∧ backoffEnd s.backoff t src ≤ now ∧
        ((peersOf s.mesh t).length < p.D_high ∨ src ∈ s.outbound) ∧
        ∃ g ∈ rpc.control.graft, g.topicId = t) := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2] at h
    exact Or.inl h
  · obtain ⟨-, -, M, -⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId validate now
      src rpc s hn _ rfl
    exact M t q h

/-- A peer within its backoff for a topic, and outside its mesh, stays outside it. -/
theorem receiveRpc_graft_backoff {t : String} {q : PeerId} (hb : now < backoffEnd s.backoff t q)
    (hm : q ∉ peersOf s.mesh t) :
    q ∉ peersOf
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.mesh t := by
  intro hq
  rcases receiveRpc_mesh p backoffMs pruneBackoffMs standing msgId validate now src rpc s hq with
    h | ⟨rfl, -, -, h2, -⟩
  · exact hm h
  · omega

/-- A GRAFT from an explicit peer gets a PRUNE.

So does a GRAFT for a joined topic within the backoff of its sender.

This holds for every RPC that the graylist does not drop. -/
theorem receiveRpc_graft_prune {g : Graft} (hg : g ∈ rpc.control.graft)
    (hn : ¬((standing src).belowGraylist = true ∧ src ∉ s.explicit))
    (h : src ∈ s.explicit ∨ (g.topicId ∈ s.topics ∧ now < backoffEnd s.backoff g.topicId src)) :
    ∃ b, (src, pruneOf g.topicId b) ∈
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.control := by
  obtain ⟨-, -, -, P, -⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId validate now
    src rpc s hn _ rfl
  exact P g hg h

/-- If no explicit peer is in a mesh before the RPC, none is after it. -/
theorem receiveRpc_explicit (h : ∀ t, ∀ q ∈ peersOf s.mesh t, q ∉ s.explicit) :
    ∀ t, ∀ q ∈ peersOf
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.mesh t,
      q ∉ (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc
        s).1.explicit := by
  intro t q hq
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2] at hq ⊢
    exact h t q hq
  · obtain ⟨-, -, -, -, E, -⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId
      validate now src rpc s hn _ rfl
    rw [E]
    rcases receiveRpc_mesh p backoffMs pruneBackoffMs standing msgId validate now src rpc s hq with
      h' | ⟨rfl, -, h2, -⟩
    · exact h t q h'
    · exact h2

/-- Every message sent in answer to an IWANT goes to the sender of the RPC.

The IWANT named its ID, and the message cache after the RPC holds the message under that ID. -/
theorem receiveRpc_iwant {q : PeerId} {m : Message}
    (h : (q, m) ∈
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.answers) :
    q = src ∧ ∃ w ∈ rpc.control.iwant, ∃ b ∈ w.messageIds, ∃ id,
      MessageId.ofBytes? b = some id ∧
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.mcache.get
          id = some m := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2] at h
    simp at h
  · obtain ⟨-, -, -, -, -, A, -⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId
      validate now src rpc s hn _ rfl
    exact A _ h

/-- Every IWANT goes to the sender of the RPC, and answers an IHAVE for a joined topic.

Each ID it asks for was in that IHAVE, has 20 bytes, and was unseen before the RPC. -/
theorem receiveRpc_ihave {q : PeerId} {c : Control} {w : IWant}
    (h : (q, c) ∈
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.control)
    (hw : w ∈ c.iwant) :
    q = src ∧ ∃ i ∈ rpc.control.ihave, i.topicId ∈ s.topics ∧ ∀ b ∈ w.messageIds,
      b ∈ i.messageIds ∧ ∃ id, MessageId.ofBytes? b = some id ∧
        s.seen.contains now (p.seen_ttl * 1000) id = false := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2] at h
    simp at h
  · obtain ⟨-, -, -, -, -, -, I, -⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId
      validate now src rpc s hn _ rfl
    exact I _ h w hw

/-- A peer below the gossip threshold that is not explicit gets no IWANT and no IWANT answer. -/
theorem receiveRpc_gossip (hg : (standing src).belowGossip = true) (hx : src ∉ s.explicit) :
    (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.answers =
        [] ∧
      ∀ x ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.control,
        x.2.iwant = [] := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2]
    simp
  · obtain ⟨-, -, -, -, -, -, -, K⟩ := receiveRpc_facts p backoffMs pruneBackoffMs standing msgId
      validate now src rpc s hn _ rfl
    exact K hg hx

/-- A GRAFT within the backoff of its sender puts the sender out of the mesh of its topic.

This needs a joined topic and a sender that is neither explicit nor graylisted. -/
theorem receiveRpc_graft_backoff_leave {g : Graft} (hg : g ∈ rpc.control.graft)
    (hl : (standing src).belowGraylist = false) (hx : src ∉ s.explicit)
    (ht : g.topicId ∈ s.topics) (hb : now < backoffEnd s.backoff g.topicId src) :
    src ∉ peersOf
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.mesh
        g.topicId :=
  receiveRpc_leave_facts p backoffMs pruneBackoffMs standing msgId validate now src rpc s
    (by simp [hl]) hg hx ht hb

/-- Every entry of the seen cache before an RPC is in it after the RPC. -/
theorem receiveRpc_seen (e : MessageId × Nat) (he : e ∈ s.seen.entries) :
    e ∈ (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.seen.entries
    := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2]
    exact he
  · exact (receiveRpc_seen_facts p backoffMs pruneBackoffMs standing msgId validate now src rpc s
      hn _ rfl).1 e he

/-- A message that an RPC forwards or delivers has its ID in the seen cache after the RPC.

The entry carries the time of the RPC. -/
theorem receiveRpc_forward_seen {q : PeerId} {m : Message}
    (h : (q, m) ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.forward ∨
      m ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.delivered) :
    (msgId m, now) ∈
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1.seen.entries
    := by
  by_cases hn : (standing src).belowGraylist = true ∧ src ∉ s.explicit
  · rw [receiveRpc_graylist p backoffMs pruneBackoffMs standing msgId validate now src rpc s hn.1
      hn.2] at h
    simp at h
  · obtain ⟨-, F, D⟩ := receiveRpc_seen_facts p backoffMs pruneBackoffMs standing msgId validate
      now src rpc s hn _ rfl
    rcases h with h | h
    · exact F _ h
    · exact D _ h

/-- An RPC neither forwards nor delivers a message whose ID is in the seen cache.

This holds while the entry of the ID is younger than the lifetime of the cache. -/
theorem receiveRpc_seen_skip {id : MessageId} {t₀ : Nat} (he : (id, t₀) ∈ s.seen.entries)
    (ht : now < t₀ + p.seen_ttl * 1000) {q : PeerId} {m : Message} (hid : msgId m = id) :
    (q, m) ∉
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.forward ∧
      m ∉
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.delivered
    := by
  have hc : s.seen.contains now (p.seen_ttl * 1000) (msgId m) = true := by
    simp only [SeenCache.contains, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨(id, t₀), he, hid.symm, ht⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (receiveRpc_forward_accept p backoffMs pruneBackoffMs standing msgId validate now src
      rpc s (Or.inl h)).2.2.1
    simp [hc] at this
  · have := (receiveRpc_forward_accept p backoffMs pruneBackoffMs standing msgId validate now src
      rpc s (q := q) (Or.inr h)).2.2.1
    simp [hc] at this

/-- After an RPC forwards or delivers a message, no later RPC forwards or delivers its ID.

Any RPCs may come between, with any sender, parameters, message ID and validation.

Say the last RPC uses the same parameters and the same message ID function as the first.

Then it neither forwards nor delivers a message with that ID.

This holds while the last RPC comes less than the lifetime of the seen cache after the first. -/
theorem receiveRpc_forward_once {q : PeerId} {m : Message}
    (h : (q, m) ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.forward ∨
      m ∈
        (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).2.delivered)
    (steps : List (RouterState → RouterState))
    (hsteps : ∀ f ∈ steps, ∃ (p' : GossipsubParameters) (backoffMs' pruneBackoffMs' : Nat)
      (standing' : PeerId → Standing) (msgId' : Message → MessageId)
      (validate' : Message → ValidationResult) (now' : Nat) (src' : PeerId) (rpc' : Rpc),
      f = fun r => (receiveRpc p' backoffMs' pruneBackoffMs' standing' msgId' validate' now' src'
        rpc' r).1)
    {s' : RouterState} (hs' : s' = steps.foldl (fun r f => f r)
      (receiveRpc p backoffMs pruneBackoffMs standing msgId validate now src rpc s).1)
    (backoffMs' pruneBackoffMs' : Nat) (standing' : PeerId → Standing)
    (validate' : Message → ValidationResult) (now' : Nat) (src' : PeerId) (rpc' : Rpc)
    (ht : now' < now + p.seen_ttl * 1000) {q' : PeerId} {m' : Message}
    (hid : msgId m' = msgId m) :
    (q', m') ∉
        (receiveRpc p backoffMs' pruneBackoffMs' standing' msgId validate' now' src' rpc'
          s').2.forward ∧
      m' ∉
        (receiveRpc p backoffMs' pruneBackoffMs' standing' msgId validate' now' src' rpc'
          s').2.delivered := by
  have he := receiveRpc_forward_seen p backoffMs pruneBackoffMs standing msgId validate now src rpc
    s h
  have he' : (msgId m, now) ∈ s'.seen.entries := by
    rw [hs']
    exact foldl_inv steps (fun r : RouterState => (msgId m, now) ∈ r.seen.entries)
      (fun r f => f r) (fun r f hf hr => by
        obtain ⟨p', b', pb', st', mi', v', n', sr', r', rfl⟩ := hsteps f hf
        exact receiveRpc_seen p' b' pb' st' mi' v' n' sr' r' r _ hr) he
  exact receiveRpc_seen_skip p backoffMs' pruneBackoffMs' standing' msgId validate' now' src' rpc'
    _ he' ht hid

end EthLib.Networking.Proofs.Gossip.Router

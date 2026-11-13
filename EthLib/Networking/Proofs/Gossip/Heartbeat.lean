module

public import EthLib.Networking.Gossip.Router
public import EthLib.Base.Proofs.List
public import EthLib.Networking.Proofs.Gossip.Router

/-!
# Proofs: the gossipsub heartbeat

For every lawful choice of peers, and every rank and standing that a client passes:

- After a heartbeat, every mesh has at most the high bound plus the outbound count of peers.
  At most the high bound of them are not outbound, and none appears twice.
- A joined topic whose mesh is below the low bound, once negative peers leave, fills it.
  It reaches the target, or stops early only when it runs out of peers that it may GRAFT.
- A joined topic whose mesh is between the bounds, once negative peers leave, keeps those peers.
  It adds only outbound peers that it may GRAFT, until it holds the outbound count or runs out.
- No mesh holds a peer with a negative score.
- A mesh of a joined topic pruned for oversubscription has the outbound count of outbound peers.
  It has fewer only when it held fewer once its negative peers left.
- Every peer added to a mesh gets a GRAFT.
- Every peer removed from the mesh of a joined topic gets a PRUNE with the backoff.
  The backoff of this node for that peer ends no earlier.
- No IHAVE goes to a peer in the mesh or fanout of its topic.
- No IHAVE goes to a peer below the gossip threshold.
- The gossip of a topic whose windows hold message IDs reaches its gossip share of the candidates.
- A fanout topic not published to for longer than its lifetime is gone.

The upper bounds and the outbound result of a pruned mesh need a target at most the high bound.

The consensus layer sets them so.

That outbound result also needs an outbound count at most the target.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Heartbeat

open EthLib.Networking.Gossip

/-- Looking a topic up in a map built from a list of topics. -/
private theorem peersOf_map (topics : List String) (f : String → List PeerId) (t : String) :
    peersOf (topics.map fun t => (t, f t)) t = if t ∈ topics then f t else [] := by
  induction topics with
  | nil => simp [peersOf]
  | cons a l ih =>
    by_cases h : t = a
    · subst h
      simp [peersOf]
    · have hb : (t == a) = false := by simpa using h
      simp only [peersOf, List.map_cons, List.lookup, hb, List.mem_cons, h, false_or] at ih ⊢
      exact ih

variable (p : GossipsubParameters) (c : ClientChoices) (sel : Select) (rank : Rank)
  (standing : PeerId → Standing) (now : Nat) (s : RouterState)

/-- The mesh of a topic after a heartbeat: the maintained mesh if joined, else none. -/
private theorem mesh_eq (t : String) :
    peersOf (heartbeat p c sel rank standing now s).1.mesh t =
      if t ∈ s.topics then meshAfter p c sel rank standing now s t else [] :=
  peersOf_map _ _ t

/-- A lawful choice of no peers is empty. -/
private theorem sel_zero (hsel : sel.Lawful) (l : List PeerId) : sel 0 l = [] :=
  List.length_eq_zero_iff.1 ((hsel 0 l).2.trans (Nat.zero_min _))

/-- A list splits into the peers outside a list and the peers in it. -/
private theorem length_filter_split (l o : List PeerId) :
    (l.filter (· ∉ o)).length + (l.filter (· ∈ o)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : a ∈ o <;> simp [h] at ih ⊢ <;> omega

/-- The best-ranked peers of a mesh are at most the score count and the target, all from it.

They appear once each when the mesh has no repeated peer. -/
private theorem best_spec (m : List PeerId) :
    ((m.mergeSort rank).take (min c.dScore p.D)).length = min (min c.dScore p.D) m.length ∧
      (∀ q ∈ (m.mergeSort rank).take (min c.dScore p.D), q ∈ m) ∧
      (m.Nodup → ((m.mergeSort rank).take (min c.dScore p.D)).Nodup) := by
  have hperm := List.mergeSort_perm m rank
  refine ⟨by rw [List.length_take, hperm.length_eq], fun q hq => ?_, fun hnd => ?_⟩
  · exact hperm.mem_iff.1 (List.mem_of_mem_take hq)
  · exact (List.take_sublist _ _).nodup (hperm.nodup_iff.2 hnd)

/-- The peers that a pruned mesh keeps before the outbound swap number at most the target.

Each is a best-ranked peer or a peer of the mesh. -/
private theorem kept_le (hsel : sel.Lawful) (m best : List PeerId) (hb : best.length ≤ p.D) :
    (best ++ sel (p.D - best.length) (m.filter (· ∉ best))).length ≤ p.D ∧
      ∀ q ∈ best ++ sel (p.D - best.length) (m.filter (· ∉ best)), q ∈ best ∨ q ∈ m := by
  refine ⟨?_, fun q hq => ?_⟩
  · rw [List.length_append, (hsel _ _).2]
    omega
  · rcases List.mem_append.1 hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr (List.mem_filter.1 ((hsel _ _).1.subset hq)).1

/-- Without repeated peers in the mesh, the kept peers appear once each.

They number the target, or the whole mesh. -/
private theorem kept_nodup (hsel : sel.Lawful) (m best : List PeerId) (hnd : m.Nodup)
    (hbn : best.Nodup) (hbm : ∀ q ∈ best, q ∈ m) (hb : best.length ≤ min p.D m.length) :
    (best ++ sel (p.D - best.length) (m.filter (· ∉ best))).Nodup ∧
      (best ++ sel (p.D - best.length) (m.filter (· ∉ best))).length = min p.D m.length := by
  have hsplit := length_filter_split m best
  have hin : (m.filter (· ∈ best)).length = best.length := by
    apply Nat.le_antisymm
    · apply List.Nodup.length_le_of_subset (hnd.filter _)
      intro q hq
      exact of_decide_eq_true (List.mem_filter.1 hq).2
    · apply hbn.length_le_of_subset
      intro q hq
      exact List.mem_filter.2 ⟨hbm q hq, decide_eq_true hq⟩
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hbn, (hsel _ _).1.nodup (hnd.filter _), ?_⟩
    intro a ha b hb' hab
    subst hab
    have := (List.mem_filter.1 ((hsel _ _).1.subset hb')).2
    simp only [decide_eq_true_eq] at this
    exact this ha
  · rw [List.length_append, (hsel _ _).2]
    omega

/-- A pruned mesh keeps at most the target number of peers, all from the mesh. -/
private theorem keepPeers_le (hsel : sel.Lawful) (o m : List PeerId) :
    (keepPeers p c sel rank o m).length ≤ p.D ∧ ∀ q ∈ keepPeers p c sel rank o m, q ∈ m := by
  obtain ⟨hbl, hbm, -⟩ := best_spec p c rank m
  have hperm := List.mergeSort_perm m rank
  simp only [keepPeers]
  generalize m.mergeSort rank = sorted at *
  generalize sorted.take (min c.dScore p.D) = best at *
  obtain ⟨hkl, hkm⟩ := kept_le p sel hsel m best (by omega)
  generalize best ++ sel (p.D - best.length) (m.filter (· ∉ best)) = kept at *
  have hsplit := length_filter_split kept o
  have hk : ∀ q ∈ kept, q ∈ m := fun q hq => (hkm q hq).elim (hbm q) id
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_take]
    omega
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact hk q (List.mem_filter.1 (List.mem_of_mem_take hq)).1
    · exact hk q (List.mem_filter.1 hq).1
    · exact hperm.mem_iff.1
        (List.mem_filter.1 (List.mem_filter.1 (List.mem_of_mem_take hq)).1).1

/-- A pruned mesh without repeated peers keeps the target number of peers, or the whole mesh. -/
private theorem keepPeers_length (hsel : sel.Lawful) (o m : List PeerId) (hnd : m.Nodup) :
    (keepPeers p c sel rank o m).length = min p.D m.length := by
  obtain ⟨hbl, hbm, hbn⟩ := best_spec p c rank m
  simp only [keepPeers]
  generalize m.mergeSort rank = sorted at *
  generalize sorted.take (min c.dScore p.D) = best at *
  obtain ⟨-, hkl⟩ := kept_nodup p sel hsel m best hnd (hbn hnd) hbm (by omega)
  generalize best ++ sel (p.D - best.length) (m.filter (· ∉ best)) = kept at *
  have hsplit := length_filter_split kept o
  simp only [List.length_append, List.length_take]
  omega

/-- A pruned mesh without repeated peers keeps the outbound count of outbound peers, or all. -/
private theorem keepPeers_outbound (hsel : sel.Lawful) (o m : List PeerId) (hnd : m.Nodup)
    (hdo : c.dOut ≤ p.D) (hm : p.D ≤ m.length) :
    min c.dOut (m.filter (· ∈ o)).length ≤
      ((keepPeers p c sel rank o m).filter (· ∈ o)).length := by
  obtain ⟨hbl, hbm, hbn⟩ := best_spec p c rank m
  have hperm := List.mergeSort_perm m rank
  simp only [keepPeers]
  generalize m.mergeSort rank = sorted at *
  generalize sorted.take (min c.dScore p.D) = best at *
  obtain ⟨-, hlen⟩ := kept_nodup p sel hsel m best hnd (hbn hnd) hbm (by omega)
  generalize best ++ sel (p.D - best.length) (m.filter (· ∉ best)) = kept at *
  have hsplit := length_filter_split kept o
  have hO : (sorted.filter (· ∈ o)).length = (m.filter (· ∈ o)).length :=
    (hperm.filter _).length_eq
  have hnds : sorted.Nodup := hperm.nodup_iff.2 hnd
  have hL := length_filter_split (sorted.filter (· ∈ o)) kept
  have hin : ((sorted.filter (· ∈ o)).filter (· ∈ kept)).length ≤
      (kept.filter (· ∈ o)).length := by
    apply List.Nodup.length_le_of_subset ((hnds.filter _).filter _)
    intro q hq
    simp only [List.mem_filter, decide_eq_true_eq] at hq ⊢
    exact ⟨hq.2, hq.1.2⟩
  have hadd : ∀ k, (((sorted.filter (· ∈ o)).filter (· ∉ kept)).take k).filter (· ∈ o) =
      ((sorted.filter (· ∈ o)).filter (· ∉ kept)).take k := by
    intro k
    apply List.filter_eq_self.2
    intro q hq
    exact (List.mem_filter.1 (List.mem_filter.1 (List.mem_of_mem_take hq)).1).2
  have hko : (kept.filter (· ∈ o)).filter (· ∈ o) = kept.filter (· ∈ o) := by
    apply List.filter_eq_self.2
    intro q hq
    exact (List.mem_filter.1 hq).2
  rw [List.filter_append, List.filter_append, hadd, hko]
  simp only [List.length_append, List.length_take]
  omega

/-- The mesh peers without a negative score appear once each. -/
private theorem nonNegativeMesh_nodup (t : String) : (nonNegativeMesh standing s t).Nodup :=
  (EthLib.Base.nodup_eraseDups _).filter _

/-- The members of the mesh peers without a negative score. -/
private theorem mem_nonNegativeMesh {t : String} {q : PeerId} :
    q ∈ nonNegativeMesh standing s t ↔
      q ∈ peersOf s.mesh t ∧ (standing q).negative = false := by
  simp [nonNegativeMesh, List.mem_eraseDups]

/-- The members of the GRAFT candidates. -/
private theorem mem_graftCandidates {t : String} {m : List PeerId} {q : PeerId} :
    q ∈ graftCandidates standing now s t m ↔
      q ∈ topicPeers s t ∧ graftable standing now s t q = true ∧ q ∉ m := by
  simp [graftCandidates, List.mem_eraseDups]

/-- The GRAFT candidates appear once each. -/
private theorem graftCandidates_nodup (t : String) (m : List PeerId) :
    (graftCandidates standing now s t m).Nodup :=
  EthLib.Base.nodup_eraseDups _

/-- A pruned mesh without repeated peers keeps no peer twice. -/
private theorem keepPeers_nodup (hsel : sel.Lawful) (o m : List PeerId) (hnd : m.Nodup) :
    (keepPeers p c sel rank o m).Nodup := by
  obtain ⟨hbl, hbm, hbn⟩ := best_spec p c rank m
  have hperm := List.mergeSort_perm m rank
  simp only [keepPeers]
  generalize m.mergeSort rank = sorted at *
  generalize sorted.take (min c.dScore p.D) = best at *
  obtain ⟨hndk, -⟩ := kept_nodup p sel hsel m best hnd (hbn hnd) hbm (by omega)
  generalize best ++ sel (p.D - best.length) (m.filter (· ∉ best)) = kept at *
  have hnds : sorted.Nodup := hperm.nodup_iff.2 hnd
  generalize min (c.dOut - (kept.filter (· ∈ o)).length) (kept.filter (· ∉ o)).length = k
  have hadd : (((sorted.filter (· ∈ o)).filter (· ∉ kept)).take k).Nodup :=
    (List.take_sublist _ _).nodup ((hnds.filter _).filter _)
  generalize (kept.filter (· ∉ o)).length -
    (((sorted.filter (· ∈ o)).filter (· ∉ kept)).take k).length = n
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨(List.take_sublist _ _).nodup (hndk.filter _), hndk.filter _, ?_⟩, hadd, ?_⟩
  · intro a ha b hb hab
    subst hab
    have h1 := (List.mem_filter.1 (List.mem_of_mem_take ha)).2
    have h2 := (List.mem_filter.1 hb).2
    simp only [decide_eq_true_eq] at h1 h2
    exact h1 h2
  · intro a ha b hb hab
    subst hab
    have h1 : a ∈ kept := by
      rcases List.mem_append.1 ha with ha | ha
      · exact (List.mem_filter.1 (List.mem_of_mem_take ha)).1
      · exact (List.mem_filter.1 ha).1
    have h2 := (List.mem_filter.1 (List.mem_of_mem_take hb)).2
    simp only [decide_eq_true_eq] at h2
    exact h2 h1

/-- A mesh without repeated peers that takes GRAFT candidates holds no peer twice. -/
private theorem grown_nodup (hsel : sel.Lawful) (t : String) (m1 : List PeerId) (h1 : m1.Nodup)
    (n : Nat) : (m1 ++ sel n (graftCandidates standing now s t m1)).Nodup := by
  rw [List.nodup_append]
  refine ⟨h1, (hsel _ _).1.nodup (graftCandidates_nodup standing now s t m1), ?_⟩
  intro a ha b hb hab
  subst hab
  exact ((mem_graftCandidates standing now s).1 ((hsel _ _).1.subset hb)).2.2 ha

/-- A maintained mesh has at most the high bound plus the outbound count of peers. -/
private theorem meshAfter_le (hsel : sel.Lawful) (hD : p.D ≤ p.D_high) (t : String) :
    (meshAfter p c sel rank standing now s t).length ≤ p.D_high + c.dOut := by
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1
  generalize (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1) = m2
  have h3 : (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2).length ≤
      p.D_high := by
    split
    · have := (keepPeers_le p c sel rank hsel s.outbound m2).1
      omega
    · omega
  generalize (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2) = m3 at *
  split
  · rw [List.length_append, (hsel _ _).2]
    omega
  · omega

/-- A maintained mesh has at most the high bound of peers that are not outbound. -/
private theorem meshAfter_le_inbound (hsel : sel.Lawful) (hD : p.D ≤ p.D_high) (t : String) :
    ((meshAfter p c sel rank standing now s t).filter (· ∉ s.outbound)).length ≤ p.D_high := by
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1
  generalize (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1) = m2
  have h3 : (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2).length ≤
      p.D_high := by
    split
    · have := (keepPeers_le p c sel rank hsel s.outbound m2).1
      omega
    · omega
  generalize (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2) = m3 at *
  have h4 : (m3.filter (· ∉ s.outbound)).length ≤ p.D_high :=
    Nat.le_trans (List.length_filter_le _ _) h3
  split
  · rw [List.filter_append, List.length_append]
    have h5 : (sel (c.dOut - (m3.filter (· ∈ s.outbound)).length)
        ((graftCandidates standing now s t m3).filter (· ∈ s.outbound))).filter
          (· ∉ s.outbound) = [] := by
      apply List.filter_eq_nil_iff.2
      intro q hq
      have := (List.mem_filter.1 ((hsel _ _).1.subset hq)).2
      simpa using this
    rw [h5, List.length_nil]
    omega
  · exact h4

/-- A maintained mesh holds no peer twice. -/
private theorem meshAfter_nodup (hsel : sel.Lawful) (t : String) :
    (meshAfter p c sel rank standing now s t).Nodup := by
  have h1 := nonNegativeMesh_nodup standing s t
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1 at *
  have h2 : (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1).Nodup := by
    split
    · exact grown_nodup sel standing now s hsel t m1 h1 _
    · exact h1
  generalize (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1) = m2 at *
  have h3 : (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2).Nodup := by
    split
    · exact keepPeers_nodup p c sel rank hsel _ _ h2
    · exact h2
  generalize (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2) = m3 at *
  split
  · rw [List.nodup_append]
    refine ⟨h3, (hsel _ _).1.nodup ((graftCandidates_nodup standing now s t m3).filter _), ?_⟩
    intro a ha b hb hab
    subst hab
    exact ((mem_graftCandidates standing now s).1
      (List.mem_filter.1 ((hsel _ _).1.subset hb)).1).2.2 ha
  · exact h3

/-- A maintained mesh below the low bound is filled up to the target, or with every candidate. -/
private theorem meshAfter_ge (hsel : sel.Lawful) (t : String)
    (hlow : (nonNegativeMesh standing s t).length < p.D_low) :
    min p.D ((nonNegativeMesh standing s t).length +
        (graftCandidates standing now s t (nonNegativeMesh standing s t)).length) ≤
      (meshAfter p c sel rank standing now s t).length := by
  have h1 := nonNegativeMesh_nodup standing s t
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1 at *
  generalize hX : min p.D (m1.length + (graftCandidates standing now s t m1).length) = X
  have h2 : (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1).Nodup ∧
      X ≤ (if m1.length < p.D_low then
        m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1).length := by
    simp only [hlow, ↓reduceIte]
    refine ⟨grown_nodup sel standing now s hsel t m1 h1 _, ?_⟩
    rw [List.length_append, (hsel _ _).2]
    omega
  generalize (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1) = m2 at *
  obtain ⟨h2n, h2l⟩ := h2
  have h3 : X ≤
      (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2).length := by
    split
    · rw [keepPeers_length p c sel rank hsel _ _ h2n]
      omega
    · exact h2l
  generalize (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2) = m3 at *
  split
  · rw [List.length_append]
    omega
  · exact h3

/-- Every peer of a maintained mesh is in the old mesh without negative peers, or a candidate. -/
private theorem meshAfter_mem (hsel : sel.Lawful) (t : String) (P : PeerId → Prop)
    (h1 : ∀ q ∈ nonNegativeMesh standing s t, P q)
    (hg : ∀ m, ∀ q ∈ graftCandidates standing now s t m, P q) :
    ∀ q ∈ meshAfter p c sel rank standing now s t, P q := by
  have hs : ∀ n l q, q ∈ sel n l → q ∈ l := fun n l _ h => (hsel n l).1.subset h
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1 at *
  have h2 : ∀ q ∈ (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1), P q := by
    split
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · exact hg _ q (hs _ _ q hq)
    · exact h1
  generalize (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1) = m2 at *
  have h3 : ∀ q ∈ (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2),
      P q := by
    split
    · exact fun q hq => h2 q ((keepPeers_le p c sel rank hsel _ _).2 q hq)
    · exact h2
  generalize (if p.D_high < m2.length then keepPeers p c sel rank s.outbound m2 else m2) = m3 at *
  split
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact h3 q hq
    · exact hg _ q (List.mem_filter.1 (hs _ _ q hq)).1
  · exact h3

/-- A maintained mesh pruned for oversubscription keeps the outbound count of outbound peers. -/
private theorem meshAfter_outbound (hsel : sel.Lawful) (hD : p.D ≤ p.D_high)
    (hc : c.dOut ≤ p.D) (t : String)
    (hhigh : p.D_high < (nonNegativeMesh standing s t).length) :
    min c.dOut ((nonNegativeMesh standing s t).filter (· ∈ s.outbound)).length ≤
      ((meshAfter p c sel rank standing now s t).filter (· ∈ s.outbound)).length := by
  have hnd1 := nonNegativeMesh_nodup standing s t
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1 at *
  have h2 : (if m1.length < p.D_low then
      m1 ++ sel (p.D - m1.length) (graftCandidates standing now s t m1) else m1) = m1 := by
    split
    · have := (hsel (p.D - m1.length) (graftCandidates standing now s t m1)).2
      rw [List.length_eq_zero_iff.1 (show (sel (p.D - m1.length)
        (graftCandidates standing now s t m1)).length = 0 by omega), List.append_nil]
    · rfl
  rw [h2]
  simp only [hhigh, ↓reduceIte]
  have hk := keepPeers_outbound p c sel rank hsel s.outbound m1 hnd1 (by omega) (by omega)
  generalize keepPeers p c sel rank s.outbound m1 = m3 at *
  split
  · rw [List.filter_append, List.length_append]
    omega
  · exact hk

/-- Every IHAVE of the gossip of a topic names that topic.

It goes to a peer outside its mesh and fanout, not below the gossip threshold. -/
private theorem gossipOf_spec (hsel : sel.Lawful) (s' : RouterState) (u : String) {q : PeerId}
    {ctl : Control} (hc : (q, ctl) ∈ gossipOf p c sel standing s' u) {h : IHave}
    (hh : h ∈ ctl.ihave) :
    h.topicId = u ∧ q ∉ peersOf s'.mesh u ∧ q ∉ peersOf s'.fanout u ∧
      (standing q).belowGossip = false := by
  unfold gossipOf at hc
  split at hc
  · simp at hc
  · obtain ⟨r, hr, he⟩ := List.mem_map.1 hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp only [List.mem_singleton] at hh
    subst hh
    have := (hsel _ _).1.subset hr
    simp only [gossipCandidates, List.mem_eraseDups] at this
    replace this := List.mem_filter.1 this
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact ⟨rfl, this.2.1.1.1, this.2.1.1.2, this.2.2⟩

/-- A key that a map step drops, while keeping the key of every entry it keeps, is absent. -/
private theorem lookup_filterMap {β : Type} (l : List (String × β))
    (f : String × β → Option (String × β)) (t : String)
    (hf : ∀ e, f e = none ∨ ∃ v, f e = some (e.1, v)) (ht : ∀ e, e.1 = t → f e = none) :
    (l.filterMap f).lookup t = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rcases hf e with h | ⟨v, h⟩
    · rw [List.filterMap_cons_none h]
      exact ih
    · rw [List.filterMap_cons_some h]
      have hne : e.1 ≠ t := fun he => by rw [ht e he] at h; cases h
      have hb : (t == e.1) = false := by simpa using fun h => hne h.symm
      simp only [List.lookup, hb]
      exact ih

/-- After a heartbeat, every mesh has at most the high bound plus the outbound count of peers.

Outbound grafts may take a mesh past the high bound, so the bound adds the outbound count. -/
theorem heartbeat_mesh_le (hsel : sel.Lawful) (hD : p.D ≤ p.D_high) (t : String) :
    (peersOf (heartbeat p c sel rank standing now s).1.mesh t).length ≤ p.D_high + c.dOut := by
  rw [mesh_eq]
  split
  · exact meshAfter_le p c sel rank standing now s hsel hD t
  · simp

/-- After a heartbeat, every mesh has at most the high bound of peers that are not outbound.

So only outbound peers can take a mesh past the high bound. -/
theorem heartbeat_mesh_le_inbound (hsel : sel.Lawful) (hD : p.D ≤ p.D_high) (t : String) :
    ((peersOf (heartbeat p c sel rank standing now s).1.mesh t).filter
      (· ∉ s.outbound)).length ≤ p.D_high := by
  rw [mesh_eq]
  split
  · exact meshAfter_le_inbound p c sel rank standing now s hsel hD t
  · simp

/-- After a heartbeat, no mesh holds a peer twice. -/
theorem heartbeat_mesh_nodup (hsel : sel.Lawful) (t : String) :
    (peersOf (heartbeat p c sel rank standing now s).1.mesh t).Nodup := by
  rw [mesh_eq]
  split
  · exact meshAfter_nodup p c sel rank standing now s hsel t
  · exact List.nodup_nil

/-- A joined topic whose mesh is below the low bound, once negative peers leave, is filled.

It reaches the target, or takes every peer that it may GRAFT. -/
theorem heartbeat_mesh_ge (hsel : sel.Lawful) {t : String}
    (ht : t ∈ s.topics) (hlow : (nonNegativeMesh standing s t).length < p.D_low) :
    min p.D ((nonNegativeMesh standing s t).length +
        (graftCandidates standing now s t (nonNegativeMesh standing s t)).length) ≤
      (peersOf (heartbeat p c sel rank standing now s).1.mesh t).length := by
  rw [mesh_eq]
  simp only [ht, ↓reduceIte]
  exact meshAfter_ge p c sel rank standing now s hsel t hlow

/-- After a heartbeat, no mesh holds a peer with a negative score. -/
theorem heartbeat_no_negative (hsel : sel.Lawful) {t : String} {q : PeerId}
    (hq : q ∈ peersOf (heartbeat p c sel rank standing now s).1.mesh t) :
    (standing q).negative = false := by
  rw [mesh_eq] at hq
  split at hq
  · refine meshAfter_mem p c sel rank standing now s hsel t (fun q => (standing q).negative = false)
      (fun q hq => ((mem_nonNegativeMesh standing s).1 hq).2) (fun m q hq => ?_) q hq
    have := ((mem_graftCandidates standing now s).1 hq).2.1
    simp only [graftable, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact this.1.2
  · simp at hq

/-- A mesh of a joined topic pruned for oversubscription has the outbound count of outbound peers.

It has fewer only when it held fewer once its negative peers left.

This needs a target at most the high bound, and an outbound count at most the target. -/
theorem heartbeat_outbound (hsel : sel.Lawful) (hD : p.D ≤ p.D_high) (hc : c.dOut ≤ p.D)
    {t : String} (ht : t ∈ s.topics)
    (hhigh : p.D_high < (nonNegativeMesh standing s t).length) :
    min c.dOut (((nonNegativeMesh standing s t).filter (· ∈ s.outbound)).length) ≤
      ((peersOf (heartbeat p c sel rank standing now s).1.mesh t).filter
        (· ∈ s.outbound)).length := by
  rw [mesh_eq]
  simp only [ht, ↓reduceIte]
  exact meshAfter_outbound p c sel rank standing now s hsel hD hc t hhigh

/-- The mesh of a joined topic between the bounds, once negative peers leave, after a heartbeat.

It keeps those peers in their order, then takes outbound peers that it may GRAFT.

It stops when it holds the outbound count of outbound peers, or when it runs out of them.

So a mesh at the low bound does not grow to the target. -/
theorem heartbeat_mesh_eq (hsel : sel.Lawful) {t : String} (ht : t ∈ s.topics)
    (hlow : p.D_low ≤ (nonNegativeMesh standing s t).length)
    (hhigh : (nonNegativeMesh standing s t).length ≤ p.D_high) :
    peersOf (heartbeat p c sel rank standing now s).1.mesh t =
      nonNegativeMesh standing s t ++
        sel (c.dOut - ((nonNegativeMesh standing s t).filter (· ∈ s.outbound)).length)
          ((graftCandidates standing now s t (nonNegativeMesh standing s t)).filter
            (· ∈ s.outbound)) := by
  rw [mesh_eq]
  simp only [ht, ↓reduceIte]
  unfold meshAfter
  dsimp only
  generalize nonNegativeMesh standing s t = m1 at *
  have h2 : ¬m1.length < p.D_low := by omega
  have h3 : ¬p.D_high < m1.length := by omega
  simp only [h2, h3, ↓reduceIte]
  split
  · rfl
  · have h0 : c.dOut - (m1.filter (· ∈ s.outbound)).length = 0 := by omega
    rw [h0, sel_zero sel hsel, List.append_nil]

/-- A joined topic between the bounds, once negative peers leave, keeps that mesh.

This holds when that mesh has at least the outbound count of outbound peers. -/
theorem heartbeat_mesh_stable (hsel : sel.Lawful) {t : String} (ht : t ∈ s.topics)
    (hlow : p.D_low ≤ (nonNegativeMesh standing s t).length)
    (hhigh : (nonNegativeMesh standing s t).length ≤ p.D_high)
    (hout : c.dOut ≤ ((nonNegativeMesh standing s t).filter (· ∈ s.outbound)).length) :
    peersOf (heartbeat p c sel rank standing now s).1.mesh t = nonNegativeMesh standing s t := by
  rw [heartbeat_mesh_eq p c sel rank standing now s hsel ht hlow hhigh, Nat.sub_eq_zero_of_le hout,
    sel_zero sel hsel, List.append_nil]

/-- A joined topic between the bounds, once negative peers leave, reaches the outbound count.

It holds fewer outbound peers only when its own and those it may GRAFT number fewer. -/
theorem heartbeat_outbound_between (hsel : sel.Lawful) {t : String} (ht : t ∈ s.topics)
    (hlow : p.D_low ≤ (nonNegativeMesh standing s t).length)
    (hhigh : (nonNegativeMesh standing s t).length ≤ p.D_high) :
    min c.dOut (((nonNegativeMesh standing s t).filter (· ∈ s.outbound)).length +
        ((graftCandidates standing now s t (nonNegativeMesh standing s t)).filter
          (· ∈ s.outbound)).length) ≤
      ((peersOf (heartbeat p c sel rank standing now s).1.mesh t).filter
        (· ∈ s.outbound)).length := by
  rw [heartbeat_mesh_eq p c sel rank standing now s hsel ht hlow hhigh, List.filter_append,
    List.length_append]
  generalize nonNegativeMesh standing s t = m1
  have hg : ∀ q ∈ (graftCandidates standing now s t m1).filter (· ∈ s.outbound),
      q ∈ s.outbound := fun q hq => by simpa using (List.mem_filter.1 hq).2
  generalize (graftCandidates standing now s t m1).filter (· ∈ s.outbound) = g at hg ⊢
  have hk := (hsel (c.dOut - (m1.filter (· ∈ s.outbound)).length) g).2
  rw [List.filter_eq_self.2 fun q hq => decide_eq_true (hg q ((hsel _ _).1.subset hq)), hk]
  omega

/-- Every peer that a heartbeat adds to a mesh gets a GRAFT for its topic. -/
theorem heartbeat_graft {t : String} {q : PeerId}
    (hnew : q ∈ peersOf (heartbeat p c sel rank standing now s).1.mesh t)
    (hold : q ∉ peersOf s.mesh t) :
    (q, graftOf t) ∈ (heartbeat p c sel rank standing now s).2.control := by
  rw [mesh_eq] at hnew
  split at hnew
  · rename_i ht
    simp only [heartbeat, List.mem_append, List.mem_flatMap, List.mem_map]
    refine Or.inl (Or.inl ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, q, ?_, rfl⟩)
    exact List.mem_filter.2 ⟨hnew, by simpa using hold⟩
  · simp at hnew

/-- Every peer that a heartbeat removes from the mesh of a joined topic gets a PRUNE.

The PRUNE carries the backoff of a pruned mesh. -/
theorem heartbeat_prune {t : String} (ht : t ∈ s.topics) {q : PeerId}
    (hold : q ∈ peersOf s.mesh t)
    (hnew : q ∉ peersOf (heartbeat p c sel rank standing now s).1.mesh t) :
    (q, pruneOf t c.pruneBackoffS) ∈ (heartbeat p c sel rank standing now s).2.control := by
  rw [mesh_eq] at hnew
  simp only [ht, ↓reduceIte] at hnew
  have hrem : q ∈ (peersOf s.mesh t).filter (· ∉ meshAfter p c sel rank standing now s t) :=
    List.mem_filter.2 ⟨hold, by simpa using hnew⟩
  simp only [heartbeat, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inl (Or.inr ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, q, hrem, rfl⟩)

/-- After a heartbeat removes a peer from the mesh of a joined topic, this node waits the backoff.

The backoff of the peer on that topic ends no earlier than the pruning backoff from now. -/
theorem heartbeat_prune_backoff {t : String} (ht : t ∈ s.topics) {q : PeerId}
    (hold : q ∈ peersOf s.mesh t)
    (hnew : q ∉ peersOf (heartbeat p c sel rank standing now s).1.mesh t) :
    now + c.pruneBackoffS.toNat * 1000 ≤
      backoffEnd (heartbeat p c sel rank standing now s).1.backoff t q := by
  rw [mesh_eq] at hnew
  simp only [ht, ↓reduceIte] at hnew
  have hrem : q ∈ (peersOf s.mesh t).filter (· ∉ meshAfter p c sel rank standing now s t) :=
    List.mem_filter.2 ⟨hold, by simpa using hnew⟩
  simp only [heartbeat]
  have reach : ∀ {α : Type} (l : List α) (f : List ((String × PeerId) × Nat) → α →
      List ((String × PeerId) × Nat)) (x : α), x ∈ l →
      (∀ b a, backoffEnd b t q ≤ backoffEnd (f b a) t q) →
      (∀ b, now + c.pruneBackoffS.toNat * 1000 ≤ backoffEnd (f b x) t q) →
      ∀ b, now + c.pruneBackoffS.toNat * 1000 ≤ backoffEnd (l.foldl f b) t q := by
    intro α l f x hx hmono hstep b
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hx
    rw [List.foldl_append, List.foldl_cons]
    exact Router.foldl_inv l2 (fun b' => now + c.pruneBackoffS.toNat * 1000 ≤ backoffEnd b' t q)
      f (fun b' a _ h => Nat.le_trans h (hmono b' a)) (hstep _)
  exact reach _ _ _ (List.mem_map_of_mem (List.mem_map_of_mem (f := fun t =>
      (t, meshAfter p c sel rank standing now s t)) ht))
    (fun b (a : String × List PeerId × List PeerId) =>
      Router.backoffEnd_fold_mono a.1 _ a.2.2 t q b)
    (fun b => Router.backoffEnd_fold_mem t _ _ q hrem b) _

/-- No IHAVE of a heartbeat goes to a peer in the mesh of its topic after the heartbeat. -/
theorem heartbeat_gossip_mesh (hsel : sel.Lawful) {q : PeerId} {ctl : Control}
    (hc : (q, ctl) ∈ (heartbeat p c sel rank standing now s).2.control) {h : IHave}
    (hh : h ∈ ctl.ihave) :
    q ∉ peersOf (heartbeat p c sel rank standing now s).1.mesh h.topicId := by
  simp only [heartbeat, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with (⟨_, _, a, _, he⟩ | ⟨_, _, a, _, he⟩) | ⟨u, hu, hg⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj he
    simp [graftOf] at hh
  · obtain ⟨-, rfl⟩ := Prod.mk.inj he
    simp [pruneOf] at hh
  · obtain ⟨rfl, h1, h2, h3⟩ := gossipOf_spec p c sel standing hsel _ u hg hh
    exact h1

/-- No IHAVE of a heartbeat goes to a peer in the fanout of its topic after the heartbeat. -/
theorem heartbeat_gossip_fanout (hsel : sel.Lawful) {q : PeerId} {ctl : Control}
    (hc : (q, ctl) ∈ (heartbeat p c sel rank standing now s).2.control) {h : IHave}
    (hh : h ∈ ctl.ihave) :
    q ∉ peersOf (heartbeat p c sel rank standing now s).1.fanout h.topicId := by
  simp only [heartbeat, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with (⟨_, _, a, _, he⟩ | ⟨_, _, a, _, he⟩) | ⟨u, hu, hg⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj he
    simp [graftOf] at hh
  · obtain ⟨-, rfl⟩ := Prod.mk.inj he
    simp [pruneOf] at hh
  · obtain ⟨rfl, h1, h2, h3⟩ := gossipOf_spec p c sel standing hsel _ u hg hh
    exact h2

/-- No IHAVE of a heartbeat goes to a peer below the gossip threshold. -/
theorem heartbeat_gossip_standing (hsel : sel.Lawful) {q : PeerId} {ctl : Control}
    (hc : (q, ctl) ∈ (heartbeat p c sel rank standing now s).2.control) {h : IHave}
    (hh : h ∈ ctl.ihave) :
    (standing q).belowGossip = false := by
  simp only [heartbeat, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with (⟨_, _, a, _, he⟩ | ⟨_, _, a, _, he⟩) | ⟨u, hu, hg⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj he
    simp [graftOf] at hh
  · obtain ⟨-, rfl⟩ := Prod.mk.inj he
    simp [pruneOf] at hh
  · obtain ⟨rfl, h1, h2, h3⟩ := gossipOf_spec p c sel standing hsel _ u hg hh
    exact h3

/-- The gossip of a topic whose windows hold message IDs reaches the gossip share of its candidates.

That share is at least the lazy degree, or every candidate when there are fewer. -/
theorem gossipOf_length (hsel : sel.Lawful) (s' : RouterState) {t : String}
    (h : s'.mcache.gossipIds p.mcache_gossip t ≠ []) :
    (gossipOf p c sel standing s' t).length =
      min (gossipCount p c (gossipCandidates standing s' t).length)
        (gossipCandidates standing s' t).length := by
  unfold gossipOf
  split
  · contradiction
  · rw [List.length_map, (hsel _ _).2]

/-- A fanout topic not published to for longer than its lifetime is gone after a heartbeat. -/
theorem heartbeat_fanout {t : String} (ht : lastPublished s t + p.fanout_ttl * 1000 < now) :
    (heartbeat p c sel rank standing now s).1.fanout.lookup t = none := by
  show (fanoutAfter p sel standing now s).lookup t = none
  unfold fanoutAfter
  refine lookup_filterMap _ _ t (fun e => ?_) (fun e he => ?_)
  · obtain ⟨u, peers⟩ := e
    dsimp only
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
  · obtain ⟨u, peers⟩ := e
    dsimp only at he ⊢
    subst he
    simp only [ht, ↓reduceIte]

end EthLib.Networking.Proofs.Gossip.Heartbeat

module

public import EthLib.Consensus.Proofs.Models.Ffg.Model

/-!
# Casper FFG: accountable safety

Two conflicting finalized checkpoints make validators slashable.

When each checkpoint has its own validator set, the slashable stake is bounded below.

The bound loses the stake that activated and exited since a reference set.

That result is Theorem 8.3 of Gasper §8.6, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

Against one reference set, such as the set of a trusted checkpoint, the bound has a simple form.

The slashable stake is at least a third of the reference stake.

It loses a third of the change of both sets since the reference set.

There an exit counts twice and an activation once.

When the sets change by at most `d` in each of `n` steps, the loss is at most `2 n d / 3`.

With one validator set for all votes, the slashable validators hold one third of its stake.

That result is Theorem 1 of Casper FFG §2.1 and Theorem 5.2 of Gasper.

Accountable safety holds for `k`-finalization with every `k ≥ 1`.

The proof follows Gasper Lemma 4.11, Lemma 5.1 and Lemma 8.2.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν β : Type*} [Preorder β] {V : Checkpoint β → Finset ν} {w : ν → ℕ} {genesis : β}
  {votes : Set (Vote ν β)}

/-- Two supermajority links that break a slashing condition.

Each link starts from a justified checkpoint, so its target is justified too.

Their target epochs lie from `lo` to `hi`.

For each validator, its votes for the two links make a double vote or a surround vote.

So each validator that votes for both links is slashable.

Gasper Lemma 8.2 finds such links when two finalized checkpoints conflict. -/
def SlashableLinks (V : Checkpoint β → Finset ν) (w : ν → ℕ) (genesis : β)
    (votes : Set (Vote ν β)) (lo hi : ℕ) : Prop :=
  ∃ s₁ t₁ s₂ t₂ : Checkpoint β, lo ≤ t₁.epoch ∧ t₁.epoch ≤ hi ∧ lo ≤ t₂.epoch ∧ t₂.epoch ≤ hi ∧
    Justified V w genesis votes s₁ ∧ Justified V w genesis votes s₂ ∧
    SupermajorityLink V w votes s₁ t₁ ∧ SupermajorityLink V w votes s₂ t₂ ∧
    ∀ v : ν, DoubleVote ⟨v, s₁, t₁⟩ ⟨v, s₂, t₂⟩ ∨ SurroundVote ⟨v, s₁, t₁⟩ ⟨v, s₂, t₂⟩

theorem SlashableLinks.mono {lo hi lo' hi' : ℕ} (h : SlashableLinks V w genesis votes lo hi)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : SlashableLinks V w genesis votes lo' hi' := by
  obtain ⟨s₁, t₁, s₂, t₂, h₁, h₁', h₂, h₂', h⟩ := h
  exact ⟨s₁, t₁, s₂, t₂, hlo.trans h₁, h₁'.trans hhi, hlo.trans h₂, h₂'.trans hhi, h⟩

/-- Double votes: two different supermajority links have one target epoch.

Both start from justified checkpoints. -/
theorem SupermajorityLink.slashableLinks_of_double {s₁ t₁ s₂ t₂ : Checkpoint β}
    (hs₁ : Justified V w genesis votes s₁) (hs₂ : Justified V w genesis votes s₂)
    (h₁ : SupermajorityLink V w votes s₁ t₁) (h₂ : SupermajorityLink V w votes s₂ t₂)
    (hne : s₁ ≠ s₂ ∨ t₁ ≠ t₂) (he : t₁.epoch = t₂.epoch) :
    SlashableLinks V w genesis votes t₁.epoch t₁.epoch :=
  ⟨s₁, t₁, s₂, t₂, le_rfl, le_rfl, he.le, he.ge, hs₁, hs₂, h₁, h₂, fun _ =>
    .inl ⟨fun h => by cases h; simp at hne, he⟩⟩

/-- Surround votes: one supermajority link surrounds another in epochs.

Both start from justified checkpoints. -/
theorem SupermajorityLink.slashableLinks_of_surround {s₁ t₁ s₂ t₂ : Checkpoint β}
    (hs₁ : Justified V w genesis votes s₁) (hs₂ : Justified V w genesis votes s₂)
    (h₁ : SupermajorityLink V w votes s₁ t₁) (h₂ : SupermajorityLink V w votes s₂ t₂)
    (hs : s₁.epoch < s₂.epoch) (ht : t₂.epoch < t₁.epoch) :
    SlashableLinks V w genesis votes t₂.epoch t₁.epoch :=
  ⟨s₁, t₁, s₂, t₂, ht.le, le_rfl, le_rfl, ht.le, hs₁, hs₂, h₁, h₂, fun _ => .inr ⟨hs, h₂.1, ht⟩⟩

/-- Gasper Lemma 4.11: two justified checkpoints of one epoch are equal.

Otherwise two links with that target epoch break a slashing condition. -/
theorem Justified.eq_or_slashableLinks {c₁ c₂ : Checkpoint β}
    (h₁ : Justified V w genesis votes c₁) (h₂ : Justified V w genesis votes c₂)
    (he : c₁.epoch = c₂.epoch) :
    c₁ = c₂ ∨ SlashableLinks V w genesis votes c₁.epoch c₁.epoch := by
  cases h₁ with
  | root =>
    cases h₂ with
    | root => exact .inl rfl
    | link _ hl => exact absurd he (by have := hl.1; dsimp at this ⊢; omega)
  | link hs₁ hl₁ =>
    cases h₂ with
    | root => exact absurd he (by have := hl₁.1; dsimp at this ⊢; omega)
    | link hs₂ hl₂ =>
      by_cases hc : c₁ = c₂
      · exact .inl hc
      · exact .inr (hl₁.slashableLinks_of_double hs₁ hs₂ hl₂ (.inr hc) he)

/-- A finalized checkpoint is justified. -/
theorem Finalized.justified {c : Checkpoint β} (h : Finalized V w genesis votes c) :
    Justified V w genesis votes c := by
  rcases h with rfl | ⟨k, hk, b, hb, -, hj, -⟩
  · exact .root
  · simpa [hb] using hj 0 hk

/-- If each block is in the chain of the next one, the first block is in the chain of each. -/
theorem le_of_chain {b : ℕ → β} {k : ℕ} (h : ∀ i < k, b i ≤ b (i + 1)) :
    ∀ i ≤ k, b 0 ≤ b i
  | 0, _ => le_rfl
  | i + 1, hi => (le_of_chain h i (by omega)).trans (h i (by omega))

/-- Gasper Lemma 5.1.

Take a finalized checkpoint, and a justified checkpoint with a later epoch.

Then the finalized block is in the chain of the justified block.

Otherwise two links break a slashing condition.

Their target epochs lie from the finalized epoch to the justified epoch. -/
theorem Finalized.le_or_slashableLinks {f j : Checkpoint β}
    (hf : Finalized V w genesis votes f) (hj : Justified V w genesis votes j)
    (hlt : f.epoch < j.epoch) :
    f.block ≤ j.block ∨ SlashableLinks V w genesis votes f.epoch j.epoch := by
  induction hj with
  | root => exact absurd hlt (Nat.not_lt_zero _)
  | @link s t hs hl ih =>
    rcases lt_trichotomy s.epoch f.epoch with hsf | hsf | hsf
    · -- The link starts before `f`, so `f` is `k`-finalized with `k ≥ 1`.
      have hfj := hf.justified
      rcases hf with rfl | ⟨k, hk, b, hb, hchain, hjust, hlink⟩
      · exact absurd hsf (Nat.not_lt_zero _)
      rcases lt_trichotomy t.epoch (f.epoch + k) with htk | htk | htk
      · -- The target shares its epoch with a justified checkpoint of the finalization.
        have hi : t.epoch - f.epoch < k := by omega
        rcases (Justified.link hs hl).eq_or_slashableLinks (hjust _ hi)
          (by dsimp; omega) with heq | h
        · rw [heq, ← hb]
          exact .inl (le_of_chain hchain _ hi.le)
        · exact .inr (h.mono hlt.le le_rfl)
      · -- The two links share a target epoch, and their sources differ in epoch.
        exact .inr ((hl.slashableLinks_of_double hs hfj hlink
          (.inl fun h => by rw [h] at hsf; exact lt_irrefl _ hsf) htk).mono hlt.le le_rfl)
      · -- The link surrounds the link that finalizes `f`.
        exact .inr ((hl.slashableLinks_of_surround hs hfj hlink hsf htk).mono
          (by dsimp; omega) le_rfl)
    · -- The source shares its epoch with `f`, so it is `f` itself.
      rcases hs.eq_or_slashableLinks hf.justified hsf with rfl | h
      · exact .inl hl.2.1
      · exact .inr (h.mono hsf.ge hl.1.le)
    · exact (ih hsf).imp (fun h => h.trans hl.2.1) fun h => h.mono le_rfl hl.1.le

/-- Gasper Lemma 8.2: two conflicting finalized checkpoints give two supermajority links.

For each validator, a vote for one link and a vote for the other break a slashing condition.

Their target epochs lie between the epochs of the two checkpoints. -/
theorem Finalized.slashableLinks {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized V w genesis votes c₁) (h₂ : Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    SlashableLinks V w genesis votes (min c₁.epoch c₂.epoch) (max c₁.epoch c₂.epoch) := by
  rcases lt_trichotomy c₁.epoch c₂.epoch with h | h | h
  · exact ((h₁.le_or_slashableLinks h₂.justified h).resolve_left hc.1).mono (min_le_left _ _)
      (le_max_right _ _)
  · rcases h₁.justified.eq_or_slashableLinks h₂.justified h with rfl | h
    · exact absurd le_rfl hc.1
    · exact h.mono (min_le_left _ _) (le_max_left _ _)
  · exact ((h₂.le_or_slashableLinks h₁.justified h).resolve_left hc.2).mono (min_le_right _ _)
      (le_max_left _ _)

open scoped Classical in
/-- The slashable stake of two supermajority links, as in the proof of Gasper Theorem 8.3.

Each validator that votes for both links is slashable.

The links have the validator sets `L` and `R` of their targets.

`V₀` is any reference set, and the stake of `L \ V₀` and `V₀ \ R` counts the change since it.

The slashable validators of both sets then hold stake `x` with this bound.

The bound: `2 * w(L) ≤ 3 * x + w(R) + 3 * (w(L \ V₀) + w(V₀ \ R))`. -/
theorem SupermajorityLink.two_mul_stake_le_of_slashable {s₁ t₁ s₂ t₂ : Checkpoint β}
    (h₁ : SupermajorityLink V w votes s₁ t₁) (h₂ : SupermajorityLink V w votes s₂ t₂)
    (h : ∀ v : ν, ⟨v, s₁, t₁⟩ ∈ votes → ⟨v, s₂, t₂⟩ ∈ votes → Slashable votes v)
    (V₀ : Finset ν) :
    2 * stake w (V t₁) ≤ 3 * stake w {v ∈ V t₁ ∩ V t₂ | Slashable votes v} + stake w (V t₂) +
      3 * (stake w (V t₁ \ V₀) + stake w (V₀ \ V t₂)) := by
  classical
  refine (two_mul_stake_le_stake_inter_add V₀ (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) h₁.2.2 h₂.2.2).trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left 3 (stake_mono ?_)) _) _)
  intro v hv
  simp only [Finset.mem_inter, Finset.mem_filter] at hv
  simp only [Finset.mem_filter, Finset.mem_inter]
  exact ⟨⟨hv.1.1, hv.2.1⟩, h v hv.1.2 hv.2.2⟩

open scoped Classical in
/-- Accountable safety with a validator set for each checkpoint: Gasper Theorem 8.3.

Take two finalized checkpoints whose blocks conflict.

Then two justified checkpoints `l` and `r` have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

Take the validator sets `L` and `R` of `l` and `r`, and any reference set `V₀`.

The stake `aL` of `L \ V₀` and `aR` of `R \ V₀` activated since `V₀`.

The stake `eL` of `V₀ \ L` and `eR` of `V₀ \ R` exited since `V₀`.

The slashable validators of both sets hold stake `x` with two bounds, one for each side.

The first bound: `2 * w(L) ≤ 3 * x + w(R) + 3 * (aL + eR)`.

The second bound is the first with the two sides swapped.

Gasper states the bound `max(w(L) - aL - eR, w(R) - aR - eL) - w(L)/3 - w(R)/3`.

Each bound here is that bound with one term of the maximum, times three.

That form needs neither division nor subtraction.

The two checkpoints do not depend on the reference set.

If `L` or `R` has no stake, both bounds hold with no slashable validator.

So the theorem has content only when each justified checkpoint in the window has positive stake. -/
theorem accountable_safety_dynamic {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized V w genesis votes c₁) (h₂ : Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      Justified V w genesis votes l ∧ Justified V w genesis votes r ∧ ∀ V₀ : Finset ν,
        2 * stake w (V l) ≤ 3 * stake w {v ∈ V l ∩ V r | Slashable votes v} +
          stake w (V r) + 3 * (stake w (V l \ V₀) + stake w (V₀ \ V r)) ∧
        2 * stake w (V r) ≤ 3 * stake w {v ∈ V l ∩ V r | Slashable votes v} +
          stake w (V l) + 3 * (stake w (V r \ V₀) + stake w (V₀ \ V l)) := by
  obtain ⟨s₁, t₁, s₂, t₂, lo₁, hi₁, lo₂, hi₂, hs₁, hs₂, hl₁, hl₂, h⟩ := h₁.slashableLinks h₂ hc
  -- A validator that votes for both links signs the two votes that break a condition.
  have hboth : ∀ v : ν, ⟨v, s₁, t₁⟩ ∈ votes → ⟨v, s₂, t₂⟩ ∈ votes → Slashable votes v :=
    fun v hv₁ hv₂ => ⟨_, hv₁, _, hv₂, rfl, rfl, h v⟩
  refine ⟨t₁, t₂, lo₁, hi₁, lo₂, hi₂, .link hs₁ hl₁, .link hs₂ hl₂, fun V₀ =>
    ⟨hl₁.two_mul_stake_le_of_slashable hl₂ hboth V₀, ?_⟩⟩
  rw [Finset.inter_comm]
  exact hl₂.two_mul_stake_le_of_slashable hl₁ (fun v hv₂ hv₁ => hboth v hv₁ hv₂) V₀

open scoped Classical in
/-- Accountable safety against a fixed reference set `V₀`, such as the set of a trusted checkpoint.

Take two finalized checkpoints whose blocks conflict.

Then two justified checkpoints `l` and `r` have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

Take the validator sets `L` and `R` of `l` and `r`.

Measure the change of `L` since `V₀` as the stake that joined plus twice the stake that left.

The slashable validators of both sets hold stake `x` with the bound below.

The bound: `w(V₀) ≤ 3 * x + (w(L \ V₀) + 2 * w(V₀ \ L)) + (w(R \ V₀) + 2 * w(V₀ \ R))`.

So `x` is at least a third of the stake of `V₀`, less a third of the two changes.

An exit lowers the stake of its set, which the bound counts twice, so an exit counts twice.

The two checkpoints do not depend on the reference set.

The bound follows from the first bound of Gasper Theorem 8.3. -/
theorem accountable_safety_reference [DecidableEq ν] {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized V w genesis votes c₁) (h₂ : Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      Justified V w genesis votes l ∧ Justified V w genesis votes r ∧ ∀ V₀ : Finset ν,
      stake w V₀ ≤ 3 * stake w {v ∈ V l ∩ V r | Slashable votes v} +
        (stake w (V l \ V₀) + 2 * stake w (V₀ \ V l)) +
        (stake w (V r \ V₀) + 2 * stake w (V₀ \ V r)) := by
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, h⟩ := accountable_safety_dynamic h₁ h₂ hc
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, fun V₀ => ?_⟩
  -- The theorem above decides equality classically; this statement uses the given test.
  have hbound : 2 * stake w (V l) ≤ 3 * stake w {v ∈ V l ∩ V r | Slashable votes v} +
      stake w (V r) + 3 * (stake w (V l \ V₀) + stake w (V₀ \ V r)) := by
    convert (h V₀).1
  -- Each set and what left `V₀` weigh as much as `V₀` and what joined.
  have hL := stake_add_stake_sdiff (w := w) (V l) V₀
  have hR := stake_add_stake_sdiff (w := w) (V r) V₀
  omega

open scoped Classical in
/-- Accountable safety when the validator sets change little since a reference set `V₀`.

Take two finalized checkpoints whose blocks conflict.

Take each justified checkpoint whose epoch lies between theirs.

Assume the stake that joined its set since `V₀`, plus twice the stake that left, is at most `b`.

Then two such justified checkpoints `l` and `r` have slashable validators of both sets.

Their stake `x` satisfies `w(V₀) ≤ 3 * x + 2 * b`. -/
theorem accountable_safety_of_change [DecidableEq ν] {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized V w genesis votes c₁) (h₂ : Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) (V₀ : Finset ν) (b : ℕ)
    (change : ∀ c : Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch → Justified V w genesis votes c →
      stake w (V c \ V₀) + 2 * stake w (V₀ \ V c) ≤ b) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      Justified V w genesis votes l ∧ Justified V w genesis votes r ∧
      stake w V₀ ≤ 3 * stake w {v ∈ V l ∩ V r | Slashable votes v} + 2 * b := by
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, h⟩ := accountable_safety_reference h₁ h₂ hc
  have h := h V₀
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, ?_⟩
  have := change l lo₁ hi₁ hl
  have := change r lo₂ hi₂ hr
  omega

open scoped Classical in
/-- Accountable safety when the validator sets change slowly after a reference set `V₀`.

Take two finalized checkpoints whose blocks conflict.

Take each justified checkpoint whose epoch lies between theirs.

Assume its set is reached from `V₀` in at most `n` steps of sets.

At each step, the stake that joins plus twice the stake that leaves is at most `d`.

Then two such justified checkpoints `l` and `r` have slashable validators of both sets.

Their stake `x` satisfies `w(V₀) ≤ 3 * x + 2 * n * d`.

So `x` is at least a third of the stake of `V₀`, less two thirds of `n * d`.

A step can stand for one epoch.

Then `d` bounds the stake that activates plus twice the stake that exits in an epoch.

The sequence of steps may depend on the checkpoint, as each branch has its own sets. -/
theorem accountable_safety_of_steps [DecidableEq ν] {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized V w genesis votes c₁) (h₂ : Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) (V₀ : Finset ν) (n d : ℕ)
    (steps : ∀ c : Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch → Justified V w genesis votes c →
      ∃ S : ℕ → Finset ν, ∃ m ≤ n, S 0 = V₀ ∧ S m = V c ∧
        ∀ i < m, stake w (S (i + 1) \ S i) + 2 * stake w (S i \ S (i + 1)) ≤ d) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      Justified V w genesis votes l ∧ Justified V w genesis votes r ∧
      stake w V₀ ≤ 3 * stake w {v ∈ V l ∩ V r | Slashable votes v} + 2 * (n * d) := by
  -- The change of each set since `V₀` is at most the changes of its steps, so at most `n * d`.
  refine accountable_safety_of_change h₁ h₂ hc V₀ (n * d) fun c lo hi hj => ?_
  obtain ⟨S, m, hm, h0, hS, hstep⟩ := steps c lo hi hj
  rw [← h0, ← hS]
  exact (stake_sdiff_add_two_mul_le S hstep).trans (Nat.mul_le_mul_right d hm)

/-- Accountable safety with one validator set `V` for every vote.

Take two finalized checkpoints whose blocks conflict.

Then validators of `V` with at least one third of its stake are slashable.

With zero total stake the conclusion holds for every set of votes.

So the theorem has content only for positive stake. -/
theorem accountable_safety {V : Finset ν} {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized (fun _ => V) w genesis votes c₁)
    (h₂ : Finalized (fun _ => V) w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) : OneThirdSlashable V w votes := by
  classical
  obtain ⟨l, r, -, -, -, -, -, -, h⟩ := accountable_safety_dynamic h₁ h₂ hc
  have h := (h V).1
  simp only [Finset.inter_self, Finset.sdiff_self, stake, Finset.sum_empty] at h
  unfold OneThirdSlashable
  simp only [stake]
  omega

end EthLib.Consensus.Models.Ffg

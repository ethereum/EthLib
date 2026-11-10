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

Those lemmas use only the order of each link.

So they hold for every kind of link that raises the epoch and follows the chain.

With slack links, each stake bound also loses twice the slack of two links.

Each checkpoint then has a set of weights, and its links hold under some weights of that set.

The bounds measure every stake under reference weights.

They lose the change from the reference weights to the weights of each of the two links.

A gain of weight counts like an activation, and a loss like an exit.

With one stake function that change is zero, which gives the bounds of Gasper.

With no slack, a slack link is a supermajority link, which gives the bounds without slack.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν β : Type*} [Preorder β] {V U : Checkpoint β → Finset ν} {w : ν → ℕ} {genesis : β}
  {votes : Set (Vote ν β)} {link : Checkpoint β → Checkpoint β → Prop}

/-- Two links that break a slashing condition.

Each link starts from a justified checkpoint, so its target is justified too.

Their target epochs lie from `lo` to `hi`.

For each validator, its votes for the two links make a double vote or a surround vote.

So each validator that votes for both links is slashable.

Gasper Lemma 8.2 finds such links when two finalized checkpoints conflict. -/
def SlashableLinksBy (link : Checkpoint β → Checkpoint β → Prop) (genesis : β) (lo hi : ℕ) :
    Prop :=
  ∃ s₁ t₁ s₂ t₂ : Checkpoint β, lo ≤ t₁.epoch ∧ t₁.epoch ≤ hi ∧ lo ≤ t₂.epoch ∧ t₂.epoch ≤ hi ∧
    JustifiedBy link genesis s₁ ∧ JustifiedBy link genesis s₂ ∧ link s₁ t₁ ∧ link s₂ t₂ ∧
    ∀ v : ν, DoubleVote ⟨v, s₁, t₁⟩ ⟨v, s₂, t₂⟩ ∨ SurroundVote ⟨v, s₁, t₁⟩ ⟨v, s₂, t₂⟩

omit [Preorder β] in
theorem SlashableLinksBy.mono {lo hi lo' hi' : ℕ}
    (h : SlashableLinksBy (ν := ν) link genesis lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    SlashableLinksBy (ν := ν) link genesis lo' hi' := by
  obtain ⟨s₁, t₁, s₂, t₂, h₁, h₁', h₂, h₂', h⟩ := h
  exact ⟨s₁, t₁, s₂, t₂, hlo.trans h₁, h₁'.trans hhi, hlo.trans h₂, h₂'.trans hhi, h⟩

omit [Preorder β] in
/-- Double votes: two different links have one target epoch.

Both start from justified checkpoints. -/
theorem slashableLinksBy_of_double {s₁ t₁ s₂ t₂ : Checkpoint β}
    (hs₁ : JustifiedBy link genesis s₁) (hs₂ : JustifiedBy link genesis s₂)
    (h₁ : link s₁ t₁) (h₂ : link s₂ t₂) (hne : s₁ ≠ s₂ ∨ t₁ ≠ t₂) (he : t₁.epoch = t₂.epoch) :
    SlashableLinksBy (ν := ν) link genesis t₁.epoch t₁.epoch :=
  ⟨s₁, t₁, s₂, t₂, le_rfl, le_rfl, he.le, he.ge, hs₁, hs₂, h₁, h₂, fun _ =>
    .inl ⟨fun h => by cases h; simp at hne, he⟩⟩

omit [Preorder β] in
/-- Surround votes: one link surrounds another in epochs.

Both start from justified checkpoints, and the second source comes before its target. -/
theorem slashableLinksBy_of_surround {s₁ t₁ s₂ t₂ : Checkpoint β}
    (hs₁ : JustifiedBy link genesis s₁) (hs₂ : JustifiedBy link genesis s₂)
    (h₁ : link s₁ t₁) (h₂ : link s₂ t₂) (hs : s₁.epoch < s₂.epoch)
    (hst : s₂.epoch < t₂.epoch) (ht : t₂.epoch < t₁.epoch) :
    SlashableLinksBy (ν := ν) link genesis t₂.epoch t₁.epoch :=
  ⟨s₁, t₁, s₂, t₂, ht.le, le_rfl, le_rfl, ht.le, hs₁, hs₂, h₁, h₂, fun _ => .inr ⟨hs, hst, ht⟩⟩

omit [Preorder β] in
/-- Gasper Lemma 4.11: two justified checkpoints of one epoch are equal.

Otherwise two links with that target epoch break a slashing condition.

Each link must raise the epoch. -/
theorem JustifiedBy.eq_or_slashableLinksBy
    (raises : ∀ {s t}, link s t → s.epoch < t.epoch) {c₁ c₂ : Checkpoint β}
    (h₁ : JustifiedBy link genesis c₁) (h₂ : JustifiedBy link genesis c₂)
    (he : c₁.epoch = c₂.epoch) :
    c₁ = c₂ ∨ SlashableLinksBy (ν := ν) link genesis c₁.epoch c₁.epoch := by
  cases h₁ with
  | root =>
    cases h₂ with
    | root => exact .inl rfl
    | link _ hl => exact absurd he (by have := raises hl; dsimp at this ⊢; omega)
  | link hs₁ hl₁ =>
    cases h₂ with
    | root => exact absurd he (by have := raises hl₁; dsimp at this ⊢; omega)
    | link hs₂ hl₂ =>
      by_cases hc : c₁ = c₂
      · exact .inl hc
      · exact .inr (slashableLinksBy_of_double hs₁ hs₂ hl₁ hl₂ (.inr hc) he)

/-- A finalized checkpoint is justified. -/
theorem FinalizedBy.justifiedBy {c : Checkpoint β} (h : FinalizedBy link genesis c) :
    JustifiedBy link genesis c := by
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

Their target epochs lie from the finalized epoch to the justified epoch.

Each link must raise the epoch, and its source block must be in the chain of its target block. -/
theorem FinalizedBy.le_or_slashableLinksBy
    (ordered : ∀ {s t}, link s t → s.epoch < t.epoch ∧ s.block ≤ t.block) {f j : Checkpoint β}
    (hf : FinalizedBy link genesis f) (hj : JustifiedBy link genesis j)
    (hlt : f.epoch < j.epoch) :
    f.block ≤ j.block ∨ SlashableLinksBy (ν := ν) link genesis f.epoch j.epoch := by
  induction hj with
  | root => exact absurd hlt (Nat.not_lt_zero _)
  | @link s t hs hl ih =>
    rcases lt_trichotomy s.epoch f.epoch with hsf | hsf | hsf
    · -- The link starts before `f`, so `f` is `k`-finalized with `k ≥ 1`.
      have hfj := hf.justifiedBy
      rcases hf with rfl | ⟨k, hk, b, hb, hchain, hjust, hlink⟩
      · exact absurd hsf (Nat.not_lt_zero _)
      rcases lt_trichotomy t.epoch (f.epoch + k) with htk | htk | htk
      · -- The target shares its epoch with a justified checkpoint of the finalization.
        have hi : t.epoch - f.epoch < k := by omega
        rcases (JustifiedBy.link hs hl).eq_or_slashableLinksBy (fun h => (ordered h).1) (hjust _ hi)
          (by dsimp; omega) with heq | h
        · rw [heq, ← hb]
          exact .inl (le_of_chain hchain _ hi.le)
        · exact .inr (h.mono hlt.le le_rfl)
      · -- The two links share a target epoch, and their sources differ in epoch.
        exact .inr ((slashableLinksBy_of_double hs hfj hl hlink
          (.inl fun h => by rw [h] at hsf; exact lt_irrefl _ hsf) htk).mono hlt.le le_rfl)
      · -- The link surrounds the link that finalizes `f`.
        exact .inr ((slashableLinksBy_of_surround hs hfj hl hlink hsf (ordered hlink).1
          htk).mono (by dsimp; omega) le_rfl)
    · -- The source shares its epoch with `f`, so it is `f` itself.
      rcases hs.eq_or_slashableLinksBy (fun h => (ordered h).1) hf.justifiedBy hsf with rfl | h
      · exact .inl (ordered hl).2
      · exact .inr (h.mono hsf.ge (ordered hl).1.le)
    · exact (ih hsf).imp (fun h => h.trans (ordered hl).2) fun h => h.mono le_rfl (ordered hl).1.le

/-- Gasper Lemma 8.2: two conflicting finalized checkpoints give two links.

For each validator, a vote for one link and a vote for the other break a slashing condition.

Their target epochs lie between the epochs of the two checkpoints.

Each link must raise the epoch, and its source block must be in the chain of its target block. -/
theorem FinalizedBy.slashableLinksBy
    (ordered : ∀ {s t}, link s t → s.epoch < t.epoch ∧ s.block ≤ t.block) {c₁ c₂ : Checkpoint β}
    (h₁ : FinalizedBy link genesis c₁) (h₂ : FinalizedBy link genesis c₂)
    (hc : Conflicting c₁.block c₂.block) :
    SlashableLinksBy (ν := ν) link genesis (min c₁.epoch c₂.epoch) (max c₁.epoch c₂.epoch) := by
  rcases lt_trichotomy c₁.epoch c₂.epoch with h | h | h
  · exact ((h₁.le_or_slashableLinksBy ordered h₂.justifiedBy h).resolve_left hc.1).mono
      (min_le_left _ _) (le_max_right _ _)
  · rcases h₁.justifiedBy.eq_or_slashableLinksBy (fun h => (ordered h).1) h₂.justifiedBy h with
        rfl | h
    · exact absurd le_rfl hc.1
    · exact h.mono (min_le_left _ _) (le_max_left _ _)
  · exact ((h₂.le_or_slashableLinksBy ordered h₁.justifiedBy h).resolve_left hc.2).mono
      (min_le_right _ _) (le_max_left _ _)

open scoped Classical in
omit [Preorder β] in
/-- The slashable stake of two links up to slack, as in the proof of Gasper Theorem 8.3.

Each validator that votes for both links is slashable.

The links have the validator sets `L` and `R` of their targets.

Under weights `w₁`, twice the stake of `L` is at most three times that of its voters plus its slack.

The same holds for `R` under weights `w₂`.

`V₀` is any reference set, and the stake of `L \ V₀` and `V₀ \ R` counts the change since it.

Every stake is measured under any reference weights `w₀`.

The slashable validators of both sets then hold stake `x` with the bound below.

The bound: `2 * w₀(L) ≤ 3 * x + w₀(R) + 3 * (w₀(L \ V₀) + w₀(V₀ \ R)) + δL + δR`.

There `δL` is the change from `w₀` to `w₁` on `L`, plus twice the slack of `L` under `w₁`.

`δR` is the same for `R` and `w₂`. -/
theorem two_mul_stake_le_of_slashable {s₁ t₁ s₂ t₂ : Checkpoint β} {w₁ w₂ : ν → ℕ}
    (h₁ : 2 * stake w₁ (V t₁) ≤
      3 * stake w₁ (signers (V t₁) votes s₁ t₁) + 2 * stake w₁ (V t₁ \ U t₁))
    (h₂ : 2 * stake w₂ (V t₂) ≤
      3 * stake w₂ (signers (V t₂) votes s₂ t₂) + 2 * stake w₂ (V t₂ \ U t₂))
    (h : ∀ v : ν, ⟨v, s₁, t₁⟩ ∈ votes → ⟨v, s₂, t₂⟩ ∈ votes → Slashable votes v)
    (V₀ : Finset ν) (w₀ : ν → ℕ) :
    2 * stake w₀ (V t₁) ≤ 3 * stake w₀ {v ∈ V t₁ ∩ V t₂ | Slashable votes v} +
      stake w₀ (V t₂) + 3 * (stake w₀ (V t₁ \ V₀) + stake w₀ (V₀ \ V t₂)) +
      ((weightChange w₀ w₁ (V t₁) + 2 * stake w₁ (V t₁ \ U t₁)) +
        (weightChange w₀ w₂ (V t₂) + 2 * stake w₂ (V t₂ \ U t₂))) := by
  classical
  refine (two_mul_stake_le_stake_inter_add_slack V₀ (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)
    ((two_mul_stake_le_add_weightChange (Finset.filter_subset _ _) h₁).trans_eq
      (Nat.add_assoc _ _ _))
    ((two_mul_stake_le_add_weightChange (Finset.filter_subset _ _) h₂).trans_eq
      (Nat.add_assoc _ _ _))).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left 3 (stake_mono ?_)) _) _) _)
  intro v hv
  simp only [Finset.mem_inter, Finset.mem_filter] at hv
  simp only [Finset.mem_filter, Finset.mem_inter]
  exact ⟨⟨hv.1.1, hv.2.1⟩, h v hv.1.2 hv.2.2⟩

open scoped Classical in
/-- Accountable safety with slack links, and a validator set and a set of weights per checkpoint.

This extends Gasper Theorem 8.3, which has no slack and one stake for each validator.

Take two slack-finalized checkpoints whose blocks conflict.

Then two slack-justified checkpoints `l` and `r` have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

Their links hold under some weights `wl` of the set of `l` and `wr` of the set of `r`.

Take the validator sets `L` and `R` of `l` and `r`, a reference set `V₀` and reference weights `w₀`.

Under `w₀`, the sets `L \ V₀` and `R \ V₀`, of stake `aL` and `aR`, activated since `V₀`.

Under `w₀`, the sets `V₀ \ L` and `V₀ \ R`, of stake `eL` and `eR`, exited since `V₀`.

The term `δL` is the change from `w₀` to `wl` on `L`.

It adds twice the slack of `l`: the stake of `L` outside the second set of `l`, under `wl`.

The term `δR` is the same for `r` and `wr`.

The slashable validators of both sets hold stake `x` under `w₀`, with two bounds.

The first bound: `2 * w₀(L) ≤ 3 * x + w₀(R) + 3 * (aL + eR) + δL + δR`.

The second bound is the first with the two sides swapped.

The two checkpoints and their weights do not depend on the reference set or weights. -/
theorem accountable_safety_dynamic_slack {W : Checkpoint β → Set (ν → ℕ)} {c₁ c₂ : Checkpoint β}
    (h₁ : SlackFinalized V U W genesis votes c₁) (h₂ : SlackFinalized V U W genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      SlackJustified V U W genesis votes l ∧ SlackJustified V U W genesis votes r ∧
      ∃ wl ∈ W l, ∃ wr ∈ W r, ∀ (V₀ : Finset ν) (w₀ : ν → ℕ),
        2 * stake w₀ (V l) ≤ 3 * stake w₀ {v ∈ V l ∩ V r | Slashable votes v} +
          stake w₀ (V r) + 3 * (stake w₀ (V l \ V₀) + stake w₀ (V₀ \ V r)) +
          ((weightChange w₀ wl (V l) + 2 * stake wl (V l \ U l)) +
            (weightChange w₀ wr (V r) + 2 * stake wr (V r \ U r))) ∧
        2 * stake w₀ (V r) ≤ 3 * stake w₀ {v ∈ V l ∩ V r | Slashable votes v} +
          stake w₀ (V l) + 3 * (stake w₀ (V r \ V₀) + stake w₀ (V₀ \ V l)) +
          ((weightChange w₀ wr (V r) + 2 * stake wr (V r \ U r)) +
            (weightChange w₀ wl (V l) + 2 * stake wl (V l \ U l))) := by
  obtain ⟨s₁, t₁, s₂, t₂, lo₁, hi₁, lo₂, hi₂, hs₁, hs₂, hl₁, hl₂, h⟩ :=
    h₁.slashableLinksBy (ν := ν) SlackLink.ordered h₂ hc
  -- A validator that votes for both links signs the two votes that break a condition.
  have hboth : ∀ v : ν, ⟨v, s₁, t₁⟩ ∈ votes → ⟨v, s₂, t₂⟩ ∈ votes → Slashable votes v :=
    fun v hv₁ hv₂ => ⟨_, hv₁, _, hv₂, rfl, rfl, h v⟩
  obtain ⟨-, -, w₁, hw₁, b₁⟩ := id hl₁
  obtain ⟨-, -, w₂, hw₂, b₂⟩ := id hl₂
  refine ⟨t₁, t₂, lo₁, hi₁, lo₂, hi₂, .link hs₁ hl₁, .link hs₂ hl₂, w₁, hw₁, w₂, hw₂,
    fun V₀ w₀ => ⟨two_mul_stake_le_of_slashable b₁ b₂ hboth V₀ w₀, ?_⟩⟩
  rw [Finset.inter_comm]
  exact two_mul_stake_le_of_slashable b₂ b₁ (fun v hv₂ hv₁ => hboth v hv₁ hv₂) V₀ w₀

open scoped Classical in
/-- Accountable safety with a validator set for each checkpoint: Gasper Theorem 8.3.

Take two finalized checkpoints whose blocks conflict.

Then two justified checkpoints `l` and `r` have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

Take the validator sets `L` and `R` of `l` and `r`, and any reference set `V₀`.

The sets `L \ V₀` and `R \ V₀`, of stake `aL` and `aR`, activated since `V₀`.

The sets `V₀ \ L` and `V₀ \ R`, of stake `eL` and `eR`, exited since `V₀`.

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
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, wl, hwl, wr, hwr, h⟩ :=
    accountable_safety_dynamic_slack (U := V) (h₁.slackFinalized V) (h₂.slackFinalized V) hc
  rw [Set.mem_singleton_iff] at hwl hwr
  subst wl wr
  rw [slackJustified_self] at hl hr
  exact ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, fun V₀ => by simpa using h V₀ w⟩

open scoped Classical in
/-- Accountable safety with slack links against a reference set `V₀` and reference weights `w₀`.

Take two slack-finalized checkpoints whose blocks conflict.

Then two slack-justified checkpoints `l` and `r` have the property below.

Their epochs lie between the epochs of the two finalized checkpoints.

Their links hold under some weights `wl` of the set of `l` and `wr` of the set of `r`.

Take the validator sets `L` and `R` of `l` and `r`.

Under `w₀`, measure the change of `L` since `V₀` as the stake that joined plus twice what left.

Add the change from `w₀` to `wl` on `L`, where a gain counts once and a loss twice.

Add twice the slack of `l`, the stake of `L` outside the second set of `l`, under `wl`.

Do the same for `R` and `wr`.

The slashable validators of both sets hold stake `x` under `w₀`.

It is at least a third of `w₀(V₀)`, less a third of the two sums.

So a validator that counts in the slack weighs as much as one that left.

It stays slashable, but it weakens the quorum of its link.

The bound has content only when the reference weights stay close to the weights of both links.

The two checkpoints and their weights do not depend on the reference set or weights. -/
theorem accountable_safety_reference_slack [DecidableEq ν] {W : Checkpoint β → Set (ν → ℕ)}
    {c₁ c₂ : Checkpoint β}
    (h₁ : SlackFinalized V U W genesis votes c₁) (h₂ : SlackFinalized V U W genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      SlackJustified V U W genesis votes l ∧ SlackJustified V U W genesis votes r ∧
      ∃ wl ∈ W l, ∃ wr ∈ W r, ∀ (V₀ : Finset ν) (w₀ : ν → ℕ),
      stake w₀ V₀ ≤ 3 * stake w₀ {v ∈ V l ∩ V r | Slashable votes v} +
        (stake w₀ (V l \ V₀) + 2 * stake w₀ (V₀ \ V l) + weightChange w₀ wl (V l) +
          2 * stake wl (V l \ U l)) +
        (stake w₀ (V r \ V₀) + 2 * stake w₀ (V₀ \ V r) + weightChange w₀ wr (V r) +
          2 * stake wr (V r \ U r)) := by
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, wl, hwl, wr, hwr, h⟩ :=
    accountable_safety_dynamic_slack h₁ h₂ hc
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, wl, hwl, wr, hwr, fun V₀ w₀ => ?_⟩
  -- The theorem above decides equality classically; this statement uses the given test.
  have hbound : 2 * stake w₀ (V l) ≤ 3 * stake w₀ {v ∈ V l ∩ V r | Slashable votes v} +
      stake w₀ (V r) + 3 * (stake w₀ (V l \ V₀) + stake w₀ (V₀ \ V r)) +
      ((weightChange w₀ wl (V l) + 2 * stake wl (V l \ U l)) +
        (weightChange w₀ wr (V r) + 2 * stake wr (V r \ U r))) := by
    convert (h V₀ w₀).1
  -- Each set and what left `V₀` weigh as much as `V₀` and what joined.
  have hL := stake_add_stake_sdiff (w := w₀) (V l) V₀
  have hR := stake_add_stake_sdiff (w := w₀) (V r) V₀
  omega

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
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, wl, hwl, wr, hwr, h⟩ :=
    accountable_safety_reference_slack (U := V) (h₁.slackFinalized V) (h₂.slackFinalized V) hc
  rw [Set.mem_singleton_iff] at hwl hwr
  subst wl wr
  rw [slackJustified_self] at hl hr
  exact ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, fun V₀ => by simpa using h V₀ w⟩

open scoped Classical in
/-- Accountable safety with slack links when the sets and weights change little since a reference.

The reference is a set `V₀` with weights `w₀`.

Take two slack-finalized checkpoints whose blocks conflict.

Take each slack-justified checkpoint whose epoch lies between theirs, and each of its weights.

Under `w₀`, take the stake that joined its set since `V₀`, plus twice the stake that left.

Add the change from `w₀` to those weights on its set, where a gain counts once and a loss twice.

Add twice its slack, the stake of its set outside its second set, under those weights.

Assume that sum is at most `b`.

Then two such slack-justified checkpoints `l` and `r` have slashable validators of both sets.

Their stake `x` under `w₀` satisfies `w₀(V₀) ≤ 3 * x + 2 * b`.

The bound has content only when `w₀` stays close to the weights of each such checkpoint. -/
theorem accountable_safety_of_change_slack [DecidableEq ν] {W : Checkpoint β → Set (ν → ℕ)}
    {c₁ c₂ : Checkpoint β}
    (h₁ : SlackFinalized V U W genesis votes c₁) (h₂ : SlackFinalized V U W genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) (V₀ : Finset ν) (w₀ : ν → ℕ) (b : ℕ)
    (change : ∀ c : Checkpoint β, min c₁.epoch c₂.epoch ≤ c.epoch →
      c.epoch ≤ max c₁.epoch c₂.epoch → SlackJustified V U W genesis votes c → ∀ w ∈ W c,
      stake w₀ (V c \ V₀) + 2 * stake w₀ (V₀ \ V c) + weightChange w₀ w (V c) +
        2 * stake w (V c \ U c) ≤ b) :
    ∃ l r : Checkpoint β, min c₁.epoch c₂.epoch ≤ l.epoch ∧ l.epoch ≤ max c₁.epoch c₂.epoch ∧
      min c₁.epoch c₂.epoch ≤ r.epoch ∧ r.epoch ≤ max c₁.epoch c₂.epoch ∧
      SlackJustified V U W genesis votes l ∧ SlackJustified V U W genesis votes r ∧
      stake w₀ V₀ ≤ 3 * stake w₀ {v ∈ V l ∩ V r | Slashable votes v} + 2 * b := by
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, wl, hwl, wr, hwr, h⟩ :=
    accountable_safety_reference_slack h₁ h₂ hc
  have h := h V₀ w₀
  refine ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, ?_⟩
  have := change l lo₁ hi₁ hl wl hwl
  have := change r lo₂ hi₂ hr wr hwr
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
  obtain ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, h⟩ := accountable_safety_of_change_slack (U := V)
    (h₁.slackFinalized V) (h₂.slackFinalized V) hc V₀ w b
    fun c lo hi hj w' hw' => by
      rw [Set.mem_singleton_iff] at hw'
      subst w'
      rw [slackJustified_self] at hj
      simpa using change c lo hi hj
  rw [slackJustified_self] at hl hr
  exact ⟨l, r, lo₁, hi₁, lo₂, hi₂, hl, hr, h⟩

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

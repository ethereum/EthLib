module

public import EthLib.Consensus.Proofs.Models.Ffg.Model

/-!
# Casper FFG: accountable safety

Two conflicting finalized checkpoints make validators with one third of the stake slashable.

The result is Theorem 1 of Casper FFG §2.1 and Theorem 5.2 of Gasper.

It holds for `k`-finalization with every `k ≥ 1`.

The proof follows Gasper Lemma 4.11 and Lemma 5.1.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν β : Type*} [Preorder β] {V : Finset ν} {w : ν → ℕ} {genesis : β}
  {votes : Set (Vote ν β)}

/-- Take two supermajority links whose two votes break a slashing condition for each validator.

Then the validators that vote for both links hold one third of the stake, and are slashable. -/
theorem SupermajorityLink.oneThirdSlashable {s₁ t₁ s₂ t₂ : Checkpoint β}
    (h₁ : SupermajorityLink V w votes s₁ t₁) (h₂ : SupermajorityLink V w votes s₂ t₂)
    (h : ∀ v : ν, DoubleVote ⟨v, s₁, t₁⟩ ⟨v, s₂, t₂⟩ ∨ SurroundVote ⟨v, s₁, t₁⟩ ⟨v, s₂, t₂⟩) :
    OneThirdSlashable V w votes := by
  classical
  refine (stake_inter (Finset.filter_subset _ _) (Finset.filter_subset _ _) h₁.2.2 h₂.2.2).trans
    (Nat.mul_le_mul_left 3 (stake_mono ?_))
  intro v hv
  simp only [Finset.mem_inter, Finset.mem_filter] at hv
  simp only [Finset.mem_filter]
  exact ⟨hv.1.1, _, hv.1.2, _, hv.2.2, rfl, rfl, h v⟩

/-- Double votes: two different supermajority links have one target epoch.

One third of the stake is then slashable. -/
theorem SupermajorityLink.oneThirdSlashable_of_double {s₁ t₁ s₂ t₂ : Checkpoint β}
    (h₁ : SupermajorityLink V w votes s₁ t₁) (h₂ : SupermajorityLink V w votes s₂ t₂)
    (hne : s₁ ≠ s₂ ∨ t₁ ≠ t₂) (he : t₁.epoch = t₂.epoch) : OneThirdSlashable V w votes :=
  h₁.oneThirdSlashable h₂ fun _ =>
    .inl ⟨fun h => by cases h; simp at hne, he⟩

/-- Surround votes: one supermajority link surrounds another in epochs.

One third of the stake is then slashable. -/
theorem SupermajorityLink.oneThirdSlashable_of_surround {s₁ t₁ s₂ t₂ : Checkpoint β}
    (h₁ : SupermajorityLink V w votes s₁ t₁) (h₂ : SupermajorityLink V w votes s₂ t₂)
    (hs : s₁.epoch < s₂.epoch) (ht : t₂.epoch < t₁.epoch) : OneThirdSlashable V w votes :=
  h₁.oneThirdSlashable h₂ fun _ => .inr ⟨hs, h₂.1, ht⟩

/-- Gasper Lemma 4.11: two justified checkpoints of one epoch are equal.

Otherwise one third of the stake is slashable. -/
theorem Justified.eq_or_oneThirdSlashable {c₁ c₂ : Checkpoint β}
    (h₁ : Justified V w genesis votes c₁) (h₂ : Justified V w genesis votes c₂)
    (he : c₁.epoch = c₂.epoch) : c₁ = c₂ ∨ OneThirdSlashable V w votes := by
  cases h₁ with
  | root =>
    cases h₂ with
    | root => exact .inl rfl
    | link _ hl => exact absurd he (by have := hl.1; dsimp at this ⊢; omega)
  | link _ hl₁ =>
    cases h₂ with
    | root => exact absurd he (by have := hl₁.1; dsimp at this ⊢; omega)
    | link _ hl₂ =>
      by_cases hc : c₁ = c₂
      · exact .inl hc
      · exact .inr (hl₁.oneThirdSlashable_of_double hl₂ (.inr hc) he)

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

Otherwise one third of the stake is slashable. -/
theorem Finalized.le_or_oneThirdSlashable {f j : Checkpoint β}
    (hf : Finalized V w genesis votes f) (hj : Justified V w genesis votes j)
    (hlt : f.epoch < j.epoch) : f.block ≤ j.block ∨ OneThirdSlashable V w votes := by
  induction hj with
  | root => exact absurd hlt (Nat.not_lt_zero _)
  | @link s t hs hl ih =>
    rcases lt_trichotomy s.epoch f.epoch with hsf | hsf | hsf
    · -- The link starts before `f`, so `f` is `k`-finalized with `k ≥ 1`.
      rcases hf with rfl | ⟨k, hk, b, hb, hchain, hjust, hlink⟩
      · exact absurd hsf (Nat.not_lt_zero _)
      rcases lt_trichotomy t.epoch (f.epoch + k) with htk | htk | htk
      · -- The target shares its epoch with a justified checkpoint of the finalization.
        have hi : t.epoch - f.epoch < k := by omega
        rcases (Justified.link hs hl).eq_or_oneThirdSlashable (hjust _ hi)
          (by dsimp; omega) with heq | h
        · rw [heq, ← hb]
          exact .inl (le_of_chain hchain _ hi.le)
        · exact .inr h
      · -- The two links share a target epoch, and their sources differ in epoch.
        exact .inr (hl.oneThirdSlashable_of_double hlink
          (.inl fun h => by rw [h] at hsf; exact lt_irrefl _ hsf) htk)
      · -- The link surrounds the link that finalizes `f`.
        exact .inr (hl.oneThirdSlashable_of_surround hlink hsf htk)
    · -- The source shares its epoch with `f`, so it is `f` itself.
      rcases hs.eq_or_oneThirdSlashable hf.justified hsf with rfl | h
      · exact .inl hl.2.1
      · exact .inr h
    · exact (ih hsf).imp_left fun h => h.trans hl.2.1

/-- Accountable safety.

Take two finalized checkpoints whose blocks conflict.

Then validators of `V` with at least one third of its stake are slashable.

The validator set and the stakes are the same for every vote. -/
theorem accountable_safety {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized V w genesis votes c₁) (h₂ : Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) : OneThirdSlashable V w votes := by
  rcases lt_trichotomy c₁.epoch c₂.epoch with h | h | h
  · exact (h₁.le_or_oneThirdSlashable h₂.justified h).resolve_left hc.1
  · rcases h₁.justified.eq_or_oneThirdSlashable h₂.justified h with rfl | h
    · exact absurd le_rfl hc.1
    · exact h
  · exact (h₂.le_or_oneThirdSlashable h₁.justified h).resolve_left hc.2

end EthLib.Consensus.Models.Ffg

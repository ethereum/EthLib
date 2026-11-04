module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Casper FFG: plausible liveness

Honest validators with two thirds of the stake can always finalize a new checkpoint.

They do so without making any honest validator slashable.

The result is Theorem 2 of Casper FFG §2.1 and Theorem 6.1 of Gasper.

An honest validator votes only from a justified source, as Casper FFG §2, Table 1, asks.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

variable {ν β : Type*} [Preorder β] {V : Finset ν} {w : ν → ℕ} {genesis : β}
  {votes votes' : Set (Vote ν β)}

omit [Preorder β] in
theorem signers_mono (h : votes ⊆ votes') (s t : Checkpoint β) :
    signers V votes s t ⊆ signers V votes' s t := by
  classical
  intro v hv
  simp only [signers, Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, h hv.2⟩

theorem SupermajorityLink.mono (h : votes ⊆ votes') {s t : Checkpoint β}
    (hl : SupermajorityLink V w votes s t) : SupermajorityLink V w votes' s t :=
  ⟨hl.1, hl.2.1, hl.2.2.trans (Nat.mul_le_mul_left 3 (stake_mono (signers_mono h s t)))⟩

/-- More votes justify more checkpoints. -/
theorem Justified.mono (h : votes ⊆ votes') {c : Checkpoint β}
    (hc : Justified V w genesis votes c) : Justified V w genesis votes' c := by
  induction hc with
  | root => exact .root
  | link _ hl ih => exact .link ih (hl.mono h)

/-- With positive stake, a supermajority link has a vote. -/
theorem SupermajorityLink.exists_vote (hV : 0 < stake w V) {s t : Checkpoint β}
    (hl : SupermajorityLink V w votes s t) : ∃ v, (⟨v, s, t⟩ : Vote ν β) ∈ votes := by
  classical
  by_contra hne
  have hempty : signers V votes s t = ∅ := by
    ext v
    simp only [signers, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    exact fun _ hv => hne ⟨v, hv⟩
  have h := hl.2.2
  rw [hempty] at h
  simp only [stake, Finset.sum_empty] at h hV
  omega

/-- With positive stake, a bound on the target epochs of the votes bounds every justified epoch. -/
theorem Justified.epoch_le (hV : 0 < stake w V) {m : ℕ}
    (hm : ∀ x ∈ votes, x.target.epoch ≤ m) {c : Checkpoint β}
    (hc : Justified V w genesis votes c) : c.epoch ≤ m := by
  cases hc with
  | root => exact Nat.zero_le _
  | link _ hl =>
    obtain ⟨v, hv⟩ := hl.exists_vote hV
    exact hm _ hv

/-- Plausible liveness.

Take honest validators `H` in `V` with at least two thirds of its stake.

The set of votes is finite, and the stake of `V` is positive.

Each honest vote has a justified source, and no honest validator is slashable.

Then some justified checkpoint `a` has this property.

Take any block `b` that has the block of `a` in its chain.

Honest validators can add votes that finalize `b` at an epoch after every justified epoch.

Each added vote has a justified source, and no honest validator becomes slashable. -/
theorem plausible_liveness {H : Finset ν} (hfin : votes.Finite) (hV : 0 < stake w V)
    (hH : H ⊆ V) (hq : 2 * stake w V ≤ 3 * stake w H)
    (hsrc : ∀ x ∈ votes, x.validator ∈ H → Justified V w genesis votes x.source)
    (hsafe : ∀ v ∈ H, ¬Slashable votes v) :
    ∃ a, Justified V w genesis votes a ∧ ∀ b, a.block ≤ b → ∃ e, ∃ votes' : Set (Vote ν β),
      (∀ c, Justified V w genesis votes c → c.epoch < e) ∧
      (∀ x ∈ votes', x.validator ∈ H) ∧
      Finalized V w genesis (votes ∪ votes') ⟨b, e⟩ ∧
      (∀ x ∈ votes', Justified V w genesis (votes ∪ votes') x.source) ∧
      ∀ v ∈ H, ¬Slashable (votes ∪ votes') v := by
  classical
  -- Every target epoch, and so every justified epoch, is at most `m`.
  set m := hfin.toFinset.sup fun x => x.target.epoch
  have hm : ∀ x ∈ votes, x.target.epoch ≤ m := fun x hx =>
    Finset.le_sup (f := fun x : Vote ν β => x.target.epoch) (hfin.mem_toFinset.mpr hx)
  have hjm : ∀ c, Justified V w genesis votes c → c.epoch ≤ m := fun c hc => hc.epoch_le hV hm
  -- The justified checkpoints are finite: the genesis one and the vote targets.
  have hJfin : {c | Justified V w genesis votes c}.Finite := by
    refine ((hfin.image fun x => x.target).insert ⟨genesis, 0⟩).subset ?_
    intro c hc
    cases hc with
    | root => exact Set.mem_insert _ _
    | link _ hl =>
      obtain ⟨v, hv⟩ := hl.exists_vote hV
      exact Set.mem_insert_of_mem _ ⟨_, hv, rfl⟩
  -- `a` is a justified checkpoint of greatest epoch.
  obtain ⟨a, ha, hmax⟩ :=
    Set.exists_max_image _ (fun c : Checkpoint β => c.epoch) hJfin ⟨_, Justified.root⟩
  refine ⟨a, ha, fun b hab => ?_⟩
  set e := m + 1
  let t : Checkpoint β := ⟨b, e⟩
  let t' : Checkpoint β := ⟨b, e + 1⟩
  let new : Set (Vote ν β) :=
    {x | x.validator ∈ H ∧ (x.source = a ∧ x.target = t ∨ x.source = t ∧ x.target = t')}
  have hae : a.epoch < e := Nat.lt_succ_of_le (hjm a ha)
  have hsub : votes ⊆ votes ∪ new := Set.subset_union_left
  -- Every honest validator signs both new links, so each link has two thirds of the stake.
  have hlink : ∀ s u : Checkpoint β, s.epoch < u.epoch → s.block ≤ u.block →
      (∀ v ∈ H, (⟨v, s, u⟩ : Vote ν β) ∈ new) →
      SupermajorityLink V w (votes ∪ new) s u := fun s u he hb hn => by
    refine ⟨he, hb, hq.trans (Nat.mul_le_mul_left 3 (stake_mono fun v hv => ?_))⟩
    simp only [signers, Finset.mem_filter]
    exact ⟨hH hv, Or.inr (hn v hv)⟩
  have hl₁ : SupermajorityLink V w (votes ∪ new) a t :=
    hlink a t hae hab fun v hv => ⟨hv, .inl ⟨rfl, rfl⟩⟩
  have hl₂ : SupermajorityLink V w (votes ∪ new) t t' :=
    hlink t t' (Nat.lt_succ_self e) le_rfl fun v hv => ⟨hv, .inr ⟨rfl, rfl⟩⟩
  have hjt : Justified V w genesis (votes ∪ new) t := .link (ha.mono hsub) hl₁
  refine ⟨e, new, fun c hc => Nat.lt_succ_of_le (hjm c hc), fun x hx => hx.1,
    .inr ⟨1, le_rfl, fun _ => b, rfl, fun _ _ => le_rfl,
      fun i hi => by obtain rfl : i = 0 := by omega
                     simpa using hjt, hl₂⟩, ?_, ?_⟩
  · rintro x ⟨-, ⟨hs, -⟩ | ⟨hs, -⟩⟩ <;> rw [hs]
    · exact ha.mono hsub
    · exact hjt
  · -- An honest vote is either old, with an early target and source, or one of the two new ones.
    rintro v hv ⟨x, hx, y, hy, hxv, hyv, hxy⟩
    have hcases : ∀ z ∈ votes ∪ new, z.validator = v →
        (z ∈ votes ∧ z.target.epoch < e ∧ z.source.epoch ≤ a.epoch) ∨
          z = ⟨v, a, t⟩ ∨ z = ⟨v, t, t'⟩ := by
      rintro z (hz | ⟨-, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩) hzv
      · refine .inl ⟨hz, Nat.lt_succ_of_le (hm z hz), hmax _ (hsrc z hz ?_)⟩
        rw [hzv]
        exact hv
      · exact .inr (.inl (Vote.ext hzv hs ht))
      · exact .inr (.inr (Vote.ext hzv hs ht))
    rcases hcases x hx hxv with ⟨hx, hxt, hxs⟩ | rfl | rfl <;>
      rcases hcases y hy hyv with ⟨hy, hyt, hys⟩ | rfl | rfl
    · exact hsafe v hv ⟨x, hx, y, hy, hxv, hyv, hxy⟩
    all_goals
      simp only [DoubleVote, SurroundVote, ne_eq, not_true_eq_false, false_and, false_or, t, t']
        at hxy ⊢
      omega

end EthLib.Consensus.Models.Ffg

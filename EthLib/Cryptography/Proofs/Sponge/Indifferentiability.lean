module

public import EthLib.Cryptography.Proofs.Sponge.Agree
public import EthLib.Cryptography.Proofs.Sponge.Switch

/-!
# Proofs: the sponge is indifferentiable from a random oracle

A game of cost `N` has advantage at most `N (N - 1) / (2 |S|) + (N (2N + 1) + N (N + 1)) / |C|`.

Here `S` is the set of sponge states and `C` the set of capacities.

It is a version of Theorem 2 of [Bertoni et al., Eurocrypt 2008][sponge], §4.3, with one squeeze.

Its simulator is simpler.

Its capacity term is about `3 N^2 / |C|`; the term of their Lemma 5 is about `N^2 / (2 |C|)`.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec ENNReal LazyPermutation Indifferentiability Indiff

/-- The advantage bound for a cost `N`, with `cardS` states and `cardC` capacities. -/
noncomputable def spongeIndiffBound (cardS cardC N : ℕ) : ℝ≥0∞ :=
  -- The switch from the uniform permutation to independent answers.
  (N.choose 2 : ℝ≥0∞) / cardS +
    -- The visible collisions, then the hidden ones.
    ((N * (2 * N + 1) + N * (N + 1) : ℕ) : ℝ≥0∞) / cardC

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-! ## Indifferentiability -/

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E] [Fintype C] [FinEnum (SpongeState Dg E C)]

/-- **An event is at most the bound more likely in the real world than in the ideal world.**

The game costs at most `N`, and the real world draws a uniform permutation. -/
theorem prEvent_real_le_ideal {α : Type}
    {oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α} {N : ℕ}
    (hN : WithinCost (fun m => (P.pad m).length) oa N) (p : α → Prop) :
    Pr{let π ← $ᵗ (Equiv.Perm (SpongeState Dg E C))
       let a ← simulateQ (realImpl (spongeHash P iv) π) oa}[p a] ≤
      Pr{let a ← (simulateQ (Msg →ₒ Dg).romImpl
        ((simulateQ (idealImpl (simulator P)) oa).run' (SimState.init iv))).run' ∅}[p a] +
        spongeIndiffBound (Fintype.card (SpongeState Dg E C)) (Fintype.card C) N := by
  -- The two sides of the combined game are identical until an answer differs.
  have hRI := (agreeUntilBad_foldReal_foldIdeal P iv).prEvent_simulateQ_run_le_add_bad_right
    (preservesInv_foldComb_diff P iv fun _ p => p.2) oa
    ((CState.init iv : CState Dg E C Msg), ∅) fun z => p z.1
  rw [prEvent_foldReal_eq_funImpl, prEvent_foldIdeal_eq_ideal] at hRI
  unfold spongeIndiffBound
  rw [← FinEnum.card_eq_fintypeCard]
  calc _ ≤ _ := prEvent_real_le_funImpl P iv hN p
    _ ≤ _ := add_le_add hRI le_rfl
    _ ≤ _ := by
      rw [add_assoc]
      exact add_le_add le_rfl
        ((add_comm _ _).le.trans (add_le_add le_rfl (prEvent_foldIdeal_diff_le P iv hN)))

/-- **An event is at most the bound more likely in the ideal world than in the real world.**

The game costs at most `N`, and the ideal world runs the simulator from `iv`. -/
theorem prEvent_ideal_le_real {α : Type}
    {oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α} {N : ℕ}
    (hN : WithinCost (fun m => (P.pad m).length) oa N) (p : α → Prop) :
    Pr{let a ← (simulateQ (Msg →ₒ Dg).romImpl
        ((simulateQ (idealImpl (simulator P)) oa).run' (SimState.init iv))).run' ∅}[p a] ≤
      Pr{let π ← $ᵗ (Equiv.Perm (SpongeState Dg E C))
         let a ← simulateQ (realImpl (spongeHash P iv) π) oa}[p a] +
        spongeIndiffBound (Fintype.card (SpongeState Dg E C)) (Fintype.card C) N := by
  have hagree := agreeUntilBad_foldReal_foldIdeal P iv
  have hIR := hagree.symm.prEvent_simulateQ_run_le_add_bad_right
    (preservesInv_foldComb_diff P iv fun _ p => p.1) oa
    ((CState.init iv : CState Dg E C Msg), ∅) fun z => p z.1
  -- A differing answer has the same chance on both sides.
  rw [hagree.prEvent_simulateQ_run_bad_eq (preservesInv_foldComb_diff P iv fun _ p => p.1)
    (preservesInv_foldComb_diff P iv fun _ p => p.2), prEvent_foldReal_eq_funImpl,
    prEvent_foldIdeal_eq_ideal] at hIR
  unfold spongeIndiffBound
  rw [← FinEnum.card_eq_fintypeCard]
  refine hIR.trans ?_
  calc _ ≤ _ := add_le_add (prEvent_funImpl_le_real P iv hN p) (prEvent_foldIdeal_diff_le P iv hN)
    _ = _ := by rw [add_assoc]

/-- **The sponge is indifferentiable from a random oracle**, with the simulator from `iv`. -/
theorem indifferentiable_spongeHash :
    Indifferentiable (spongeHash P iv) (fun m => (P.pad m).length)
      (spongeIndiffBound (Fintype.card (SpongeState Dg E C)) (Fintype.card C)) :=
  ⟨SimState Dg E C, SimState.init iv, simulator P, asksOnce_simulator P, fun _ _ hN =>
    ⟨prEvent_real_le_ideal P iv hN _, prEvent_ideal_le_real P iv hN _⟩⟩

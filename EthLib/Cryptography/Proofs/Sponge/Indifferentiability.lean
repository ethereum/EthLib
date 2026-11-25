module

public import EthLib.Cryptography.Proofs.Sponge.Agree
public import EthLib.Cryptography.Proofs.Sponge.Switch

/-!
# Proofs: the sponge is indifferentiable from a random oracle

A game of cost `N` has advantage at most `C(N, 2) / |S| + (N (2N + 1) + N (N + 1)) / |C|`.

It is Theorem 2 of [Bertoni et al., Eurocrypt 2008][sponge], §4.3, with a simpler simulator.

So its bound is a sum of collision bounds, weaker than theirs.

The games agree until bad: the fundamental lemma of [Bellare, Rogaway, Eurocrypt 2006][br].

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/
[br]: https://eprint.iacr.org/2004/331

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec ENNReal LazyPermutation Indifferentiability Indiff

/-- The advantage bound for a cost `N`, with `cardS` states and `cardC` capacities. -/
noncomputable def spongeIndiffBound (cardS cardC N : ℕ) : ℝ≥0∞ :=
  -- The switch from the uniform permutation to independent answers.
  -- The simulator draws new answers uniformly over all states, a simplification of theirs.
  --
  -- So the bound is a sum of collision bounds, not the exact term of their Lemma 5.
  --
  (N.choose 2 : ℝ≥0∞) / cardS +
    -- The visible collisions, then the hidden ones.
    ((N * (2 * N + 1) + N * (N + 1) : ℕ) : ℝ≥0∞) / cardC

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-! ## Indifferentiability -/

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E] [Fintype C] [FinEnum (SpongeState Dg E C)]

/-- **The real world is at most the ideal world plus the bound.**

The game has cost `N`, and the event `p` is any event of its output. -/
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

/-- **The ideal world is at most the real world plus the bound.**

The game has cost `N`, and the event `p` is any event of its output. -/
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
  -- A differing answer has one chance on both sides.
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

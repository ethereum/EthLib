module

public import EthLib.Cryptography.Proofs.Sponge.Bound
public import EthLib.Cryptography.Proofs.Sponge.Real
public import EthLib.Cryptography.Proofs.Sponge.Switch

/-!
# Proofs: the sponge is indifferentiable from a random oracle

A game of cost `N` has advantage at most `C(N, 2) / |S| + (N (2N + 1) + N (N + 1)) / |C|`.

This is Theorem 2 of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §4.

The games are identical until bad, as in [Bellare, Rogaway, Eurocrypt 2006][br], §3.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
[br]: https://eprint.iacr.org/2004/331
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec ENNReal LazyPermutation Indifferentiability

/-- The advantage bound for a cost `N`, with `cardS` states and `cardC` capacities. -/
noncomputable def spongeIndiffBound (cardS cardC N : ℕ) : ℝ≥0∞ :=
  -- The simulator draws new answers uniformly over all states, a simplification of theirs.
  --
  -- So the bound is a sum of collision bounds, not the exact term of their Lemma 5.
  --
  -- The switch from the uniform permutation to independent answers.
  (N.choose 2 : ℝ≥0∞) / cardS +
    -- The visible collisions, then the hidden ones.
    ((N * (2 * N + 1) + N * (N + 1) : ℕ) : ℝ≥0∞) / cardC

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-! ## The two sides of the combined game agree until an answer differs -/

/-- One step of the folded ideal side of the combined game. -/
theorem foldIdeal_run (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) :
    ((foldIdeal P iv) t).run (cs, c) = (fun z => (z.1.1.2, (z.1.2, z.2))) <$>
      (simulateQ (ASpec Msg Dg E C).romImpl ((combStep P iv t).run cs)).run c := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp [combIdeal, StateT.run_map, simulateQ_map, Functor.map_map]

/-- While no answer differs, the two answers agree, and a differing answer stays recorded. -/
theorem combStep_answer_eq (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain)
    (cs : CState Dg E C Msg) (c : ACache Msg Dg E C) {w}
    (hw : w ∈ support ((simulateQ (ASpec Msg Dg E C).romImpl
      ((combStep P iv t).run cs)).run c)) :
    (w.1.2.diff = false → w.1.1.1 = w.1.1.2) ∧ (cs.diff = true → w.1.2.diff = true) := by
  rcases t with (n | x | y) | m
  · simp [combStep, unifFwdImpl] at hw
    obtain ⟨u, rfl⟩ := hw
    exact ⟨fun _ => rfl, id⟩
  · obtain ⟨u, r, -, hz⟩ := combFwd_support P iv x cs c hw
    rw [hz]
    simp only [fwdOut, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not]
    exact ⟨fun h => h.2, fun h => by simp [h]⟩
  · obtain ⟨u, rfl⟩ := combInv_support iv y cs c hw
    simp only [invOut, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not]
    exact ⟨fun h => h.2, fun h => by simp [h]⟩
  · obtain ⟨w', c₁, d, -, -, hz⟩ := combHash_support P iv m cs c hw
    rw [hz]
    simp only [hashOut, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_not]
    exact ⟨fun h => h.2, fun h => by simp [h]⟩

/-- The two sides of the combined game agree until an answer differs. -/
theorem agreeUntilBad_foldReal_foldIdeal :
    QueryImpl.AgreeUntilBad (foldReal P iv) (foldIdeal P iv)
      fun s : CState Dg E C Msg × ACache Msg Dg E C => s.1.diff = true := by
  intro t s _ Q
  rw [foldReal_run, foldIdeal_run, prEvent_map, prEvent_map]
  refine prEvent_congr_of_support _ _ _ fun w hw => ?_
  have h := (combStep_answer_eq P iv t s.1 s.2 hw).1
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h (by simpa using h2)]
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [h (by simpa using h2)]
    exact ⟨h1, h2⟩

/-- A differing answer stays recorded, with either answer. -/
theorem preservesInv_foldComb_diff (sel : Selector Dg E C Msg) :
    QueryImpl.PreservesInv (foldComb P iv sel)
      fun s : CState Dg E C Msg × ACache Msg Dg E C => s.1.diff = true := by
  intro t s hs z hz
  obtain ⟨w, hw, hz2⟩ := mem_support_foldComb_run P iv sel t s hz
  rw [hz2]
  exact (combStep_answer_eq P iv t s.1 s.2 hw).2 hs

/-! ## The ideal side of the combined game -/

/-- The folded ideal side, run, is the ideal side under the random oracles. -/
theorem run_simulateQ_foldIdeal {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (cs : CState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (simulateQ (ASpec Msg Dg E C).romImpl ((simulateQ (combIdeal P iv) oa).run cs)).run c =
      (fun z => ((z.1, z.2.1), z.2.2)) <$> (simulateQ (foldIdeal P iv) oa).run (cs, c) :=
  simulateQ_mapStateTBase_run_eq_map_flattenStateT _ _ oa cs c

/-- The output of the visible game with its end phase is the output of the game alone. -/
theorem visRun_output (pre : Bool) {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (vs : VState Dg E C Msg)
    (c : ACache Msg Dg E C) :
    (fun z => z.1.1) <$> (simulateQ (ASpec Msg Dg E C).romImpl (visRun P iv pre oa vs)).run c =ᵈ
      (simulateQ (ASpec Msg Dg E C).romImpl
        ((simulateQ (visImpl P iv pre) oa).run' vs)).run' c := by
  simp only [visRun, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind,
    map_pure, StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.bind_right _ fun w => EvalDistEq.bind_const _ _

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- **The ideal side of the combined game is the ideal world.** -/
theorem foldIdeal_evalDistEq_idealGame {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) :
    (simulateQ (foldIdeal P iv) oa).run' ((CState.init iv : CState Dg E C Msg), ∅) =ᵈ
      (simulateQ (Msg →ₒ Dg).romImpl
        ((simulateQ (idealImpl (simulator P)) oa).run' (SimState.init iv))).run' ∅ := by
  have e1 : (simulateQ (foldIdeal P iv) oa).run' ((CState.init iv : CState Dg E C Msg), ∅) =
      (simulateQ (ASpec Msg Dg E C).romImpl ((simulateQ (combIdeal P iv) oa).run'
        (CState.init iv : CState Dg E C Msg))).run' ∅ := by
    rw [StateT.run'_eq, StateT.run'_eq, StateT.run'_eq, simulateQ_map, StateT.run_map,
      run_simulateQ_foldIdeal, Functor.map_map, Functor.map_map]
  have hv : (simulateQ (combIdeal P iv) oa).run' (CState.init iv : CState Dg E C Msg) =
      (simulateQ (visImpl P iv true) oa).run' (SimState.init iv, [], false) := by
    have h2 : Prod.map id CState.vis <$> (simulateQ (combIdeal P iv) oa).run
        (CState.init iv : CState Dg E C Msg) =
        (simulateQ (visImpl P iv true) oa).run (SimState.init iv, [], false) :=
      map_run_combIdeal P iv oa _
    rw [StateT.run'_eq, StateT.run'_eq, ← h2, Functor.map_map]
    rfl
  have hf : (simulateQ (visImpl P iv false) oa).run' ((SimState.init iv : SimState Dg E C),
      ([] : List Msg), false) = (simulateQ (idealTImpl P) oa).run' (SimState.init iv) := by
    have h3 : Prod.map id Prod.fst <$> (simulateQ (visImpl P iv false) oa).run
        ((SimState.init iv : SimState Dg E C), ([] : List Msg), false) =
        (simulateQ (idealTImpl P) oa).run (SimState.init iv) :=
      map_run_visImpl_false P iv oa _
    rw [StateT.run'_eq, StateT.run'_eq, ← h3, Functor.map_map]
    rfl
  rw [e1, hv]
  calc _ =ᵈ (fun z => z.1.1) <$> (simulateQ (ASpec Msg Dg E C).romImpl
        (visRun P iv true oa (SimState.init iv, [], false))).run ∅ :=
          (visRun_output P iv _ oa _ _).symm
    _ =ᵈ (fun z => z.1.1) <$> (simulateQ (ASpec Msg Dg E C).romImpl
        (visRun P iv false oa (SimState.init iv, [], false))).run ∅ :=
          (visRun_true_evalDistEq_false P iv oa _ _).map _
    _ =ᵈ _ := visRun_output P iv _ oa _ _
    _ = _ := by rw [hf]
    _ =ᵈ _ := idealTGame_evalDistEq_idealGame P iv oa

variable [Fintype C]

/-- **A differing answer is unlikely.**

On the ideal side, an answer of a game of cost `N` differs with chance at most the collision bound.
-/
theorem prEvent_foldIdeal_diff_le {α : Type}
    {oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α} {N : ℕ}
    (hN : WithinCost (fun m => (P.pad m).length) oa N) :
    Pr{let z ← (simulateQ (foldIdeal P iv) oa).run ((CState.init iv : CState Dg E C Msg), ∅)}[
      z.2.1.diff = true] ≤
      ((N * (2 * N + 1) + N * (N + 1) : ℕ) : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  refine (prEvent_mono_of_support _ _ _ fun z hz h =>
    diff_imp_bad_or_EC P iv (fun _ p => p.2) oa hz h).trans ?_
  calc _ = Pr{let z ← (simulateQ (ASpec Msg Dg E C).romImpl
        ((simulateQ (visImpl P iv true) oa).run (SimState.init iv, [], false))).run ∅}[
        z.1.2.2.2 = true ∨ EC P iv z.1.2 z.2] := by
          have h2 : Prod.map id CState.vis <$> (simulateQ (combIdeal P iv) oa).run
              (CState.init iv : CState Dg E C Msg) =
              (simulateQ (visImpl P iv true) oa).run (SimState.init iv, [], false) :=
            map_run_combIdeal P iv oa _
          rw [← h2, simulateQ_map, StateT.run_map, run_simulateQ_foldIdeal, Functor.map_map,
            prEvent_map]
          rfl
    _ ≤ Pr{let z ← (simulateQ (ASpec Msg Dg E C).romImpl
        (visRun P iv false oa (SimState.init iv, [], false))).run ∅}[
        z.1.2.2.2 = true ∨ EC P iv z.1.2 z.2] := by
          -- The end phase only adds cached answers.
          rw [← (visRun_true_evalDistEq_false P iv oa _ ∅).prEvent_eq]
          simp only [visRun, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
          conv_lhs => rw [← bind_pure ((simulateQ (ASpec Msg Dg E C).romImpl
            ((simulateQ (visImpl P iv true) oa).run (SimState.init iv, [], false))).run ∅)]
          refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun w _ => ?_
          classical
          by_cases hw : w.1.2.2.2 = true ∨ EC P iv w.1.2 w.2
          · rw [prEvent_pure, prEvent_eq_one_of_forall_mem_support _ _ fun z hz => ?_]
            · simp [hw]
            · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
              obtain ⟨e, he, rfl⟩ := hz
              have hle := (endPhase_support P _ w.2 he).1
              rcases hw with hw | ⟨β, v, hβ, hv, h⟩
              · exact Or.inl hw
              · refine Or.inr ⟨β, v, hβ, valC_mono P hle hv, ?_⟩
                rcases h with h | ⟨γ, w', hγ, hne, hw', hwv⟩
                · exact Or.inl h
                · exact Or.inr ⟨γ, w', hγ, hne, valC_mono P hle hw', hwv⟩
          · simp [hw]
    _ ≤ _ := prEvent_visRun_le P iv oa hN

/-! ## Indifferentiability -/

variable [FinEnum (SpongeState Dg E C)]

omit [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E] [Fintype C] in
/-- An event has one chance on the real side of the combined game and over independent answers. -/
theorem prEvent_foldReal_eq_funImpl {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (p : α → Prop) :
    Pr{let z ← (simulateQ (foldReal P iv) oa).run ((CState.init iv : CState Dg E C Msg), ∅)}[
      p z.1] = Pr{let a ← (simulateQ (funImpl P iv) oa).run' ([], false)}[p a] := by
  rw [← (combReal_run_evalDistEq P iv oa).prEvent_eq p, StateT.run'_eq, prEvent_map]

omit [Fintype C] [FinEnum (SpongeState Dg E C)] in
/-- An event has one chance on the ideal side of the combined game and in the ideal world. -/
theorem prEvent_foldIdeal_eq_ideal {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) (p : α → Prop) :
    Pr{let z ← (simulateQ (foldIdeal P iv) oa).run ((CState.init iv : CState Dg E C Msg), ∅)}[
      p z.1] = Pr{let a ← (simulateQ (Msg →ₒ Dg).romImpl
        ((simulateQ (idealImpl (simulator P)) oa).run' (SimState.init iv))).run' ∅}[p a] := by
  rw [← (foldIdeal_evalDistEq_idealGame P iv oa).prEvent_eq p, StateT.run'_eq, prEvent_map]

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

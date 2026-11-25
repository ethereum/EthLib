module

public import EthLib.Cryptography.Proofs.ProjectionInLaw
public import EthLib.Cryptography.Proofs.Sponge.Games

/-!
# Proofs: the real world of the sponge over independent answers

Each hash call of a game unfolds into the calls of the sponge to the permutation.

A uniform permutation then answers alike to independent uniform answers, up to the birthday bound.

This is the switching lemma of [Bellare, Rogaway, Eurocrypt 2006][br], §2.

[br]: https://eprint.iacr.org/2004/331
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec ENNReal LazyPermutation Indifferentiability

variable {Dg E C Msg : Type} [XorOp Dg] [XorOp E]

/-! ## The hash calls unfolded -/

/-- The calls of a game, with each hash call replaced by the calls of the sponge. -/
def toPerm (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg) (PermComp (SpongeState Dg E C))
  | .inl t => liftM ((unifSpec + PermSpec (SpongeState Dg E C)).query t)
  | .inr m => (sponge (Dg := Dg) P iv (fun x => liftM
      ((unifSpec + PermSpec (SpongeState Dg E C)).query (.inr (.inl x)))) m :
        PermComp (SpongeState Dg E C) Dg)

/-- Running the sponge's calls of the permutation is the sponge over the forward answers. -/
theorem simulateQ_absorbAll {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + PermSpec (SpongeState Dg E C)) m)
    (s : SpongeState Dg E C) (bs : List (Dg × E)) :
    simulateQ impl (absorbAll (fun x => (liftM ((unifSpec + PermSpec (SpongeState Dg E C)).query
      (.inr (.inl x))) : PermComp (SpongeState Dg E C) _)) s bs) =
      absorbAll (fun x => impl (.inr (.inl x))) s bs := by
  induction bs generalizing s with
  | nil => simp [absorbAll]
  | cons B bs ih => simp [absorbAll_cons, ih]

/-- The sponge over a pure function, in a lawful monad, returns the pure hash. -/
theorem absorbAll_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : SpongeState Dg E C → SpongeState Dg E C) (s : SpongeState Dg E C)
    (bs : List (Dg × E)) :
    absorbAll (fun x => (pure (π x) : m _)) s bs =
      pure (Id.run (absorbAll (fun x => (pure (π x) : Id _)) s bs)) := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih => simp only [absorbAll_cons, pure_bind, ih]

/-- **The real world unfolds into the permutation model.** -/
theorem simulateQ_permImpl_toPerm (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)
    (π : Equiv.Perm (SpongeState Dg E C)) {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) :
    simulateQ (permImpl π) (simulateQ (toPerm P iv) oa) =
      simulateQ (realImpl (spongeHash P iv) π) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with t | m
  · rcases t with n | x | y
    · rfl
    · simp [toPerm]
      rfl
    · simp [toPerm]
      rfl
  · simp only [toPerm, sponge, simulateQ_map, simulateQ_absorbAll]
    change SpongeState.out <$> absorbAll (fun x => (pure (π x) : ProbComp _)) iv (P.pad m) =
      pure (spongeHash P iv π m)
    rw [absorbAll_pure, map_pure]
    rfl

/-- The sponge asks the permutation once per block. -/
theorem isQueryBoundP_absorbAll (s : SpongeState Dg E C) (bs : List (Dg × E)) :
    IsQueryBoundP (absorbAll (fun x => (liftM ((unifSpec + PermSpec (SpongeState Dg E C)).query
      (.inr (.inl x))) : PermComp (SpongeState Dg E C) _)) s bs) (·.isRight = true)
      bs.length := by
  induction bs generalizing s with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons B bs ih =>
    rw [absorbAll_cons, List.length_cons, add_comm]
    exact isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun y _ => ih y

/-- **A game of cost `N` unfolds into at most `N` calls of the permutation.** -/
theorem isQueryBoundP_toPerm (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) {α : Type}
    {oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α} {N : ℕ}
    (hN : WithinCost (fun m => (P.pad m).length) oa N) :
    IsQueryBoundP (simulateQ (toPerm P iv) oa) (·.isRight = true) N := by
  induction oa using OracleComp.inductionOn generalizing N with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [WithinCost, isQueryBound_query_bind_iff] at hN
    obtain ⟨hle, hk⟩ := hN
    rw [simulateQ_query_bind]
    have hstep : IsQueryBoundP (toPerm P iv t) (·.isRight = true)
        (queryCost (fun m => (P.pad m).length) t) := by
      rcases t with (n | q) | m
      · exact (isQueryBoundP_query_iff _ _ _).2 (by simp)
      · exact (isQueryBoundP_query_iff _ _ _).2 (by simp [queryCost])
      · have h := isQueryBoundP_bind (m := 0) (isQueryBoundP_absorbAll iv (P.pad m))
          fun s _ => isQueryBoundP_pure (spec := unifSpec + PermSpec (SpongeState Dg E C))
            (fun t => t.isRight = true) (SpongeState.out s) 0
        rw [Nat.add_zero, bind_pure_comp] at h
        exact h
    have := isQueryBoundP_bind hstep fun u _ => ih u (hk u)
    rwa [Nat.add_sub_cancel' hle] at this

/-! ## The switch to independent answers -/

section Switch

variable [FinEnum (SpongeState Dg E C)] (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)

/-- The real world over independent answers unfolds into the permutation model. -/
theorem simulateQ_indepPermImpl_toPerm {α : Type}
    (oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α) :
    simulateQ indepPermImpl (simulateQ (toPerm P iv) oa) = simulateQ (funImpl P iv) oa := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  rcases t with t | m
  · simp [toPerm]
    rfl
  · simp only [toPerm, sponge, simulateQ_map, simulateQ_absorbAll]
    rfl

/-- **A uniform permutation answers as independent values, up to the birthday bound.**

A game of cost `N` makes at most `N` calls of the permutation, sponge calls included. -/
theorem prEvent_real_le_funImpl {α : Type}
    {oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α} {N : ℕ}
    (hN : WithinCost (fun m => (P.pad m).length) oa N) (p : α → Prop) :
    Pr{let π ← $ᵗ (Equiv.Perm (SpongeState Dg E C))
       let a ← simulateQ (realImpl (spongeHash P iv) π) oa}[p a] ≤
      Pr{let a ← (simulateQ (funImpl P iv) oa).run' ([], false)}[p a] +
        (N.choose 2 : ℝ≥0∞) / FinEnum.card (SpongeState Dg E C) := by
  simp_rw [← simulateQ_permImpl_toPerm, prEvent_let_let]
  have hl := (uniformSample_bind_simulateQ_permImpl_evalDistEq
    (simulateQ (toPerm P iv) oa)).prEvent_eq p
  refine (le_of_eq hl).trans <|
    (prEvent_lazyPermImpl_le_indepPermImpl _ (isQueryBoundP_toPerm P iv hN) p).trans
      (add_le_add ?_ le_rfl)
  rw [simulateQ_indepPermImpl_toPerm, StateT.run'_eq, prEvent_map]
  exact prEvent_mono _ _ _ fun z hz => hz.1

/-- **Independent answers answer as a uniform permutation, up to the birthday bound.**

Both runs never fail, so the bound of the other direction holds for the complement. -/
theorem prEvent_funImpl_le_real {α : Type}
    {oa : OracleComp (GameSpec (SpongeState Dg E C) Msg Dg) α} {N : ℕ}
    (hN : WithinCost (fun m => (P.pad m).length) oa N) (p : α → Prop) :
    Pr{let a ← (simulateQ (funImpl P iv) oa).run' ([], false)}[p a] ≤
      Pr{let π ← $ᵗ (Equiv.Perm (SpongeState Dg E C))
         let a ← simulateQ (realImpl (spongeHash P iv) π) oa}[p a] +
        (N.choose 2 : ℝ≥0∞) / FinEnum.card (SpongeState Dg E C) := by
  simp_rw [← simulateQ_permImpl_toPerm, prEvent_let_let]
  have hl := (uniformSample_bind_simulateQ_permImpl_evalDistEq
    (simulateQ (toPerm P iv) oa)).prEvent_eq p
  refine le_of_le_of_eq ?_ (congrArg (· + _) hl.symm)
  have h := prEvent_lazyPermImpl_le_indepPermImpl _ (isQueryBoundP_toPerm P iv hN) (¬ p ·)
  rw [simulateQ_indepPermImpl_toPerm] at h
  set F := (simulateQ (funImpl P iv) oa).run' ([], false)
  set L := (simulateQ lazyPermImpl (simulateQ (toPerm P iv) oa)).run' []
  -- The run with the flag puts at least the mass of the event without the flag.
  have hF : Pr{let z ← (simulateQ (funImpl P iv) oa).run ([], false)}[¬p z.1 ∧ z.2.2 = false] ≤
      Pr{let x ← F}[¬p x] := by
    rw [show F = _ from StateT.run'_eq _ _, prEvent_map]
    exact prEvent_mono _ _ _ fun z hz => hz.1
  have h2 := tsub_le_iff_right.2 (h.trans (add_le_add hF le_rfl))
  -- Neither run fails, so each event has the mass its complement leaves.
  have e1 : Pr{let x ← F}[p x] = 1 - Pr{let x ← F}[¬p x] := by
    simpa using prEvent_not_eq_one_sub F (fun x => ¬p x)
  have e2 : Pr{let x ← L}[p x] = 1 - Pr{let x ← L}[¬p x] := by
    simpa using prEvent_not_eq_one_sub L (fun x => ¬p x)
  rw [e1, e2]
  exact (tsub_le_tsub_left h2 _).trans tsub_tsub_le_tsub_add

end Switch

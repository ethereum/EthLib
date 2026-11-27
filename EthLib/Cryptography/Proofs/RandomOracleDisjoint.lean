module

public import EthLib.Cryptography.Proofs.QueryAvoidance
public import EthLib.Cryptography.Proofs.EvalDistEq
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Proofs: queries on disjoint inputs under one random oracle are independent

Two computations share one lazily sampled random oracle.

Each hash query of the first has its input in one set, and each of the second in another.

The second computation may depend on the output of the first.

When the two sets are disjoint, the second finds in the cache no entry that the first wrote.

So it runs as it would from the empty cache, and the two outputs are independent.

The first runs entirely before the second; queries that interleave are not covered here.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleSpec OracleComp ENNReal

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)]

/-! ## Queries in a set of inputs -/

/-- A coin, or a hash query whose input is in `P`. -/
def CoinOrHashIn (hs : OracleSpec ι) (P : ι → Prop) : (unifSpec + hs).Domain → Prop
  | .inl _ => True
  | .inr x => P x

/-- A hash query whose input is in `P`, and no coin. -/
def HashIn (hs : OracleSpec ι) (P : ι → Prop) : (unifSpec + hs).Domain → Prop
  | .inl _ => False
  | .inr x => P x

instance (P : ι → Prop) [DecidablePred P] : DecidablePred (HashIn hs P)
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr x => inferInstanceAs (Decidable (P x))

omit [DecidableEq ι] [∀ t : hs.Domain, SampleableType (hs.Range t)] in
/-- A computation that queries only `P` makes no hash query in a set disjoint from `P`. -/
theorem isQueryBoundP_hashIn_zero {α : Type} {P Q : ι → Prop} [DecidablePred Q]
    (hPQ : ∀ x, P x → ¬Q x) {oa : OracleComp (unifSpec + hs) α}
    (h : oa.AllQueriesSatisfy (CoinOrHashIn hs P)) :
    IsQueryBoundP oa (HashIn hs Q) 0 := by
  have hnot : oa.AllQueriesSatisfy fun t => ¬HashIn hs Q t :=
    h.mono fun t ht => by
      rcases t with n | x
      · exact id
      · exact hPQ x ht
  exact (isQueryBoundP_congr_pred fun _ => not_not).1 ((isQueryBoundP_zero_iff oa _).2 hnot)

/-! ## A run reads its cache only at its own queries -/

/-- **Two caches that agree on `Q` give the same run to a computation that queries only `Q`.**

A query in `Q` finds the same entry in both caches, cached or not.

A fresh answer is cached in both, so they still agree on `Q` after it. -/
theorem run'_simulateQ_romImpl_eq_of_eqOn {α : Type} {Q : ι → Prop}
    {oa : OracleComp (unifSpec + hs) α} (h : oa.AllQueriesSatisfy (CoinOrHashIn hs Q)) :
    ∀ {c c' : hs.QueryCache}, (∀ x, Q x → c x = c' x) →
      (simulateQ hs.romImpl oa).run' c = (simulateQ hs.romImpl oa).run' c' := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro c c' _; rfl
  | query_bind t k ih =>
    intro c c' hc
    rw [allQueriesSatisfy_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run'_eq, StateT.run_bind, map_bind]
    rcases t with n | x
    · -- A coin leaves both caches as they are.
      rw [roSim.run_apply_inl, roSim.run_apply_inl, bind_map_left, bind_map_left]
      exact bind_congr fun u => by
        simpa only [StateT.run'_eq] using ih u (h.2 u) hc
    · -- The input is in `Q`, so both caches hold the same entry for it.
      rw [romImpl_apply_inr, randomOracle.run_eq, randomOracle.run_eq, hc x h.1]
      cases hx : c' x with
      | some u =>
        simp only [pure_bind]
        simpa only [StateT.run'_eq] using ih u (h.2 u) hc
      | none =>
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun u => ?_
        have hc' : ∀ y, Q y → c.cacheQuery x u y = c'.cacheQuery x u y := fun y hy => by
          by_cases hyx : y = x
          · subst hyx
            simp
          · rw [QueryCache.cacheQuery_of_ne _ _ hyx, QueryCache.cacheQuery_of_ne _ _ hyx]
            exact hc y hy
        simpa only [StateT.run'_eq] using ih u (h.2 u) hc'

/-! ## Independence -/

/-- **A second computation on disjoint inputs runs as from the empty cache.**

Every hash query of the first has its input in `P`.

Every hash query of the second, for each output of the first, has its input in `Q`.

From the empty cache, the second then has the law it has when it runs alone. -/
theorem run'_simulateQ_romImpl_bind_evalDistEq {α β : Type} {P Q : ι → Prop}
    (hPQ : ∀ x, P x → ¬Q x) {oa : OracleComp (unifSpec + hs) α}
    {f : α → OracleComp (unifSpec + hs) β} (ha : oa.AllQueriesSatisfy (CoinOrHashIn hs P))
    (hf : ∀ a, (f a).AllQueriesSatisfy (CoinOrHashIn hs Q)) :
    (simulateQ hs.romImpl (oa >>= f)).run' ∅ =ᵈ
      ((simulateQ hs.romImpl oa).run' ∅ >>= fun a => (simulateQ hs.romImpl (f a)).run' ∅) := by
  classical
  rw [run'_simulateQ_romImpl_bind, StateT.run'_eq, bind_map_left]
  refine EvalDistEq.bind_congr_of_support _ fun z hz => EvalDistEq.of_eq ?_
  -- The first run caches no input of `Q`, so its cache agrees with the empty one on `Q`.
  have hcache := cache_eq_none_of_mem_support_run_romImpl
    (isQueryBoundP_hashIn_zero hPQ ha) (cache := ∅) (fun _ _ => rfl) hz
  exact run'_simulateQ_romImpl_eq_of_eqOn (hf z.1) fun x hx => by
    rw [hcache x hx]
    rfl

/-- **Two computations whose hash queries lie in disjoint sets are independent.**

Every hash query of the first has its input in `P`, and every one of the second in `Q`.

Run one after the other from the empty cache, their pair of outputs has the law of two runs
that each start from the empty cache. -/
theorem run'_simulateQ_romImpl_prod_evalDistEq {α β : Type} {P Q : ι → Prop}
    (hPQ : ∀ x, P x → ¬Q x) {oa : OracleComp (unifSpec + hs) α}
    {ob : OracleComp (unifSpec + hs) β} (ha : oa.AllQueriesSatisfy (CoinOrHashIn hs P))
    (hb : ob.AllQueriesSatisfy (CoinOrHashIn hs Q)) :
    (simulateQ hs.romImpl (oa >>= fun a => ob >>= fun b => pure (a, b))).run' ∅ =ᵈ
      ((simulateQ hs.romImpl oa).run' ∅ >>= fun a =>
        (simulateQ hs.romImpl ob).run' ∅ >>= fun b => pure (a, b)) := by
  refine (run'_simulateQ_romImpl_bind_evalDistEq hPQ ha fun a =>
    allQueriesSatisfy_bind hb fun _ => allQueriesSatisfy_pure _ _).trans
      (EvalDistEq.of_eq (bind_congr fun a => ?_))
  -- The pairing step makes no query.
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

/-- The two outputs are independent: two events of them hold together with the product of
their probabilities. -/
theorem prEvent_run'_simulateQ_romImpl_and {α β : Type} {P Q : ι → Prop}
    (hPQ : ∀ x, P x → ¬Q x) {oa : OracleComp (unifSpec + hs) α}
    {ob : OracleComp (unifSpec + hs) β} (ha : oa.AllQueriesSatisfy (CoinOrHashIn hs P))
    (hb : ob.AllQueriesSatisfy (CoinOrHashIn hs Q)) (E : α → Prop) (F : β → Prop) :
    Pr{let z ← (simulateQ hs.romImpl (oa >>= fun a => ob >>= fun b => pure (a, b))).run' ∅}[
        E z.1 ∧ F z.2] =
      Pr{let a ← (simulateQ hs.romImpl oa).run' ∅}[E a] *
        Pr{let b ← (simulateQ hs.romImpl ob).run' ∅}[F b] := by
  rw [(run'_simulateQ_romImpl_prod_evalDistEq hPQ ha hb).prEvent_eq]
  simp

end EthLib.Cryptography

module

public import EthLib.Cryptography.Proofs.EvalDistEq
public import EthLib.Cryptography.Proofs.HashSig
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Proofs: programmed tables of a lazy random oracle

The XMSS and SPHINCS security proofs replace the secret seed by fresh uniform values.

For that step they write a table of distinct inputs and their outputs into the oracle's cache.

Querying fresh inputs gives a uniform table and the cache that records it.

An answer of the oracle can be sampled before a computation runs, without changing its output.
-/

@[expose] public section

open OracleComp OracleSpec

namespace EthLib.Cryptography.HashSig

/-! ## Uniform tables -/

/-- A head and a tail of length `count`, as a function on `count + 1` indices. -/
def finHeadTailEquiv (α : Type) (count : Nat) :
    (α × (Fin count → α)) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp
  right_inv values := by
    funext index
    cases index using Fin.cases <;> simp

/-- Two independent uniform draws form one uniform pair. -/
theorem evalDist_independent_uniform_pair
    {α β : Type} [SampleableType α] [SampleableType β] [SampleableType (α × β)] :
    (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right) : ProbComp (α × β)) =ᵈ
    ($ᵗ (α × β) : ProbComp (α × β)) := by
  -- The draws form a uniform pair under the product sampler, and two samplers agree in law.
  have h := @SampleableType.map_uniformSample_evalDistEq_of_bijective _ _
    (instSampleableTypeProd α β) _ _ Function.bijective_id
  rw [id_map, SampleableType.uniformSample_prod_eq_bind] at h
  exact h

/-- Independent uniform draws for `n` indices form one uniform table. -/
theorem evalDist_sequenceFin_uniform {R : Type} [SampleableType R] [Fintype R] (n : Nat) :
    sequenceFin (fun _ : Fin n => ($ᵗ R : ProbComp R)) =ᵈ
      ($ᵗ (Fin n → R) : ProbComp (Fin n → R)) := by
  classical
  induction n with
  | zero =>
      refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun values => ?_
      have heq : values = Fin.elim0 := funext fun i => i.elim0
      simp [sequenceFin, heq, Subsingleton.elim (default : Fin 0 → R) Fin.elim0,
        Finset.filter_singleton]
  | succ n ih =>
      calc
        _ =ᵈ (finHeadTailEquiv R n <$> (do
            let head ← $ᵗ R
            let tail ← $ᵗ (Fin n → R)
            pure (head, tail))) := by
          simp only [sequenceFin, map_bind, finHeadTailEquiv, Equiv.coe_fn_mk, bind_pure_comp]
          refine EvalDistEq.bind_right _ fun head => (ih.map _).trans (.of_eq ?_)
          rw [Functor.map_map]
        _ =ᵈ (finHeadTailEquiv R n <$> ($ᵗ (R × (Fin n → R)))) :=
          evalDist_independent_uniform_pair.map _
        _ =ᵈ _ := SampleableType.map_uniformSample_evalDistEq_of_bijective
          (finHeadTailEquiv R n).bijective

section

variable (J R : Type) [Fintype J]

/-- A table on a finite type, as a table on the indices of an enumeration of that type. -/
noncomputable def finTableEquiv : (Fin (Fintype.card J) → R) ≃ (J → R) where
  toFun values j := values (Fintype.equivFin J j)
  invFun values i := values ((Fintype.equivFin J).symm i)
  left_inv values := by funext i; simp
  right_inv values := by funext j; simp

end

/-! ## Programmed caches -/

variable {D R : Type} [DecidableEq D]

/-- The cache with each input written with its output, in index order. -/
def cacheFin : {n : Nat} → QueryCache (D →ₒ R) → (Fin n → D) → (Fin n → R) →
    QueryCache (D →ₒ R)
  | 0, cache, _, _ => cache
  | _ + 1, cache, inputs, outputs =>
      cacheFin (cache.cacheQuery (inputs 0) (outputs 0))
        (fun i => inputs i.succ) (fun i => outputs i.succ)

theorem cacheFin_apply_of_not_mem {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (outputs : Fin n → R) (input : D)
    (hinput : ∀ i, input ≠ inputs i) : cacheFin cache inputs outputs input = cache input := by
  induction n generalizing cache with
  | zero => rfl
  | succ n ih =>
      rw [cacheFin, ih _ _ _ (fun i => hinput i.succ)]
      exact QueryCache.cacheQuery_of_ne cache (outputs 0) (hinput 0)

theorem cacheFin_apply {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (hinj : Function.Injective inputs) (outputs : Fin n → R) (i : Fin n) :
    cacheFin cache inputs outputs (inputs i) = some (outputs i) := by
  induction n generalizing cache with
  | zero => exact i.elim0
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [cacheFin, cacheFin_apply_of_not_mem]
          · exact QueryCache.cacheQuery_self _ _ _
          · intro j h
            have := hinj h
            exact Fin.succ_ne_zero j this.symm
      | succ i =>
          exact ih _ _ (fun _ _ h => Fin.succ_injective _ (hinj h)) _ i

/-- Distinct fresh queries give independent uniform outputs and the cache that records them. -/
theorem run_sequenceFin_fresh [SampleableType R] {n : Nat} (inputs : Fin n → D)
    (hinj : Function.Injective inputs) (cache : QueryCache (D →ₒ R))
    (hfresh : ∀ i, cache (inputs i) = none) :
    (simulateQ randomOracle (sequenceFin fun i =>
      (liftM ((D →ₒ R).query (inputs i)) : OracleComp (D →ₒ R) R))).run cache =
      (do
        let outputs ← sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)
        pure (outputs, cacheFin cache inputs outputs)) := by
  induction n generalizing cache with
  | zero => simp only [sequenceFin, simulateQ_pure, StateT.run_pure, pure_bind, cacheFin]
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_none _ (hfresh 0)]
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp, map_bind]
      change (($ᵗ R) >>= _) = (($ᵗ R) >>= _)
      apply bind_congr
      intro head
      have htail : ∀ i : Fin n, (cache.cacheQuery (inputs 0) head) (inputs i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh i.succ
        · intro h
          exact Fin.succ_ne_zero i (hinj h)
      rw [ih (fun i => inputs i.succ) (fun _ _ h => Fin.succ_injective _ (hinj h)) _ htail]
      simp only [bind_pure_comp, Functor.map_map, cacheFin]
      rfl

/-! ## Tables on a finite type -/

variable {J : Type} [Fintype J]

/-- The cache with each input of a finite table written with its output. -/
noncomputable def cacheTable (cache : QueryCache (D →ₒ R)) (inputs : J → D) (outputs : J → R) :
    QueryCache (D →ₒ R) :=
  cacheFin cache (fun i => inputs ((Fintype.equivFin J).symm i))
    ((finTableEquiv J R).symm outputs)

theorem cacheTable_apply (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (hinj : Function.Injective inputs) (outputs : J → R) (j : J) :
    cacheTable cache inputs outputs (inputs j) = some (outputs j) := by
  have h := cacheFin_apply cache (fun i => inputs ((Fintype.equivFin J).symm i))
    (hinj.comp (Fintype.equivFin J).symm.injective) ((finTableEquiv J R).symm outputs)
    (Fintype.equivFin J j)
  rw [(Fintype.equivFin J).symm_apply_apply] at h
  simpa only [cacheTable, finTableEquiv, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using h

theorem cacheTable_apply_of_not_mem (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (outputs : J → R) (input : D) (hinput : ∀ j, input ≠ inputs j) :
    cacheTable cache inputs outputs input = cache input :=
  cacheFin_apply_of_not_mem _ _ _ _ (fun _ => hinput _)

/-- Query every input of a finite table, in the order of an enumeration of its index type. -/
noncomputable def queryTable (inputs : J → D) : OracleComp (D →ₒ R) (J → R) :=
  finTableEquiv J R <$> sequenceFin fun i =>
    (liftM ((D →ₒ R).query (inputs ((Fintype.equivFin J).symm i))) : OracleComp (D →ₒ R) R)

/-- Querying a table of distinct fresh inputs gives a uniform table.

The final cache records that table. -/
theorem evalDist_queryTable_fresh [SampleableType R] [Fintype R] [SampleableType (J → R)]
    (inputs : J → D) (hinj : Function.Injective inputs)
    (cache : QueryCache (D →ₒ R)) (hfresh : ∀ j, cache (inputs j) = none) :
    (simulateQ randomOracle (queryTable inputs)).run cache =ᵈ
      (fun outputs => (outputs, cacheTable cache inputs outputs)) <$> ($ᵗ (J → R)) := by
  classical
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_sequenceFin_fresh (fun i => inputs ((Fintype.equivFin J).symm i))
      (fun _ _ h => (Fintype.equivFin J).symm.injective (hinj h)) cache (fun _ => hfresh _)]
  have h := (((evalDist_sequenceFin_uniform (R := R) (Fintype.card J)).map
    (finTableEquiv J R)).trans (SampleableType.map_uniformSample_evalDistEq_of_bijective
      (finTableEquiv J R).bijective)).map
    (fun outputs => (outputs, cacheTable cache inputs outputs))
  simpa only [bind_pure_comp, Functor.map_map, id_map', Function.comp_def, cacheTable,
    Equiv.symm_apply_apply] using h

/-! ## Sampling an answer early -/

/-- A run that starts with a query continues from the answer and the cache of that query. -/
theorem run'_query_bind {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (cache : σ) :
    (simulateQ impl (liftM (spec.query input) >>= next)).run' cache =
      ((impl input).run cache >>= fun result =>
        (simulateQ impl (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

variable [SampleableType R]

/-- Take an input that is missing from the cache.

Then its answer can be sampled before the computation runs, whether or not it is queried. -/
theorem evalDist_presample_fresh {α : Type} (computation : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : QueryCache (D →ₒ R)) (target : D) (hfresh : cache target = none) :
    (simulateQ (D →ₒ R).romImpl computation).run' cache =ᵈ (do
      let output ← $ᵗ R
      (simulateQ (D →ₒ R).romImpl computation).run' (cache.cacheQuery target output) :
        ProbComp α) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (EvalDistEq.bind_const _ _).symm
  | query_bind input next ih =>
      cases input with
      | inl input =>
          have hrun (cache : QueryCache (D →ₒ R)) :
              (simulateQ (D →ₒ R).romImpl
                (liftM ((unifSpec + (D →ₒ R)).query (.inl input)) >>= next)).run' cache =
                ((liftM (unifSpec.query input) : ProbComp _) >>= fun answer =>
                  (simulateQ (D →ₒ R).romImpl (next answer)).run' cache) := by
            rw [run'_query_bind]
            change (((fun answer => (answer, cache)) <$>
              (liftM (unifSpec.query input) : ProbComp _)) >>= _) = _
            exact bind_map_left (m := ProbComp) (fun answer => (answer, cache))
              (liftM (unifSpec.query input) : ProbComp _)
              (fun result => (simulateQ (D →ₒ R).romImpl (next result.1)).run' result.2)
          rw [hrun]
          refine EvalDistEq.trans (my := (do
            let answer ← (liftM (unifSpec.query input) : ProbComp _)
            let output ← $ᵗ R
            (simulateQ (D →ₒ R).romImpl (next answer)).run' (cache.cacheQuery target output)))
            ?_ ?_
          · exact EvalDistEq.bind_right _ (fun answer => ih answer cache hfresh)
          · refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
            apply EvalDistEq.bind_right
            intro output
            rw [hrun]
      | inr input =>
          have hrun (cache : QueryCache (D →ₒ R)) :
              (simulateQ (D →ₒ R).romImpl
                (liftM ((unifSpec + (D →ₒ R)).query (.inr input)) >>= next)).run' cache =
                ((randomOracle (spec := D →ₒ R) input).run cache >>= fun result =>
                  (simulateQ (D →ₒ R).romImpl (next result.1)).run' result.2) :=
            run'_query_bind _ _ _ _
          by_cases heq : input = target
          · subst target
            rw [hrun, QueryImpl.withCaching_run_none _ hfresh, bind_map_left]
            apply EvalDistEq.bind_right
            intro output
            rw [hrun, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _),
              pure_bind]
          · have hfresh' (output : R) : (cache.cacheQuery input output) target = none := by
              rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq), hfresh]
            cases hinput : cache input with
            | some answer =>
                rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
                refine (ih answer cache hfresh).trans ?_
                apply EvalDistEq.bind_right
                intro output
                rw [hrun, QueryImpl.withCaching_run_some _ (by
                  rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), pure_bind]
            | none =>
                rw [hrun, QueryImpl.withCaching_run_none _ hinput, bind_map_left]
                refine EvalDistEq.trans (my := (do
                  let answer ← $ᵗ R
                  let output ← $ᵗ R
                  (simulateQ (D →ₒ R).romImpl (next answer)).run'
                    ((cache.cacheQuery input answer).cacheQuery target output))) ?_ ?_
                · exact EvalDistEq.bind_right _ (fun answer => ih answer _ (hfresh' answer))
                · refine (EvalDistEq.bind_bind_swap _ _ _).trans ?_
                  apply EvalDistEq.bind_right
                  intro output
                  rw [hrun, QueryImpl.withCaching_run_none _ (by
                    rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), bind_map_left]
                  apply EvalDistEq.bind_right
                  intro answer
                  rw [QueryCache.cacheQuery_comm cache heq]

/-- Querying the oracle once before a computation does not change its output distribution. -/
theorem evalDist_presample_query {α : Type} (computation : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache : QueryCache (D →ₒ R)) (target : D) :
    (simulateQ (D →ₒ R).romImpl computation).run' cache =ᵈ
      ((randomOracle (spec := D →ₒ R) target).run cache >>= fun result =>
        (simulateQ (D →ₒ R).romImpl computation).run' result.2) := by
  cases hc : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
      exact evalDist_presample_fresh computation cache target hc
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]

/-- Run a preparation first, then the computation from the cache that the preparation leaves.

This does not change the output distribution of the computation. -/
theorem evalDist_presample_computation {α β : Type}
    (computation : OracleComp (unifSpec + (D →ₒ R)) α)
    (preparation : OracleComp (unifSpec + (D →ₒ R)) β) (cache : QueryCache (D →ₒ R)) :
    (simulateQ (D →ₒ R).romImpl computation).run' cache =ᵈ
      ((simulateQ (D →ₒ R).romImpl preparation).run cache >>= fun result =>
        (simulateQ (D →ₒ R).romImpl computation).run' result.2) := by
  induction preparation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      refine EvalDistEq.trans (my := (((D →ₒ R).romImpl input).run cache >>= fun result =>
        (simulateQ (D →ₒ R).romImpl computation).run' result.2)) ?_ ?_
      · cases input with
        | inl input =>
            refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
            simp [OracleSpec.romImpl, unifFwdImpl]
        | inr input => exact evalDist_presample_query computation cache input
      · exact EvalDistEq.bind_right _ (fun result => ih result.1 result.2)

end EthLib.Cryptography.HashSig

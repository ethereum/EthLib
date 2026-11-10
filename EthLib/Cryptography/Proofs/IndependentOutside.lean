module

public import EthLib.Cryptography.Proofs.IndependentAnswers
public import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Proofs: independent answers to a permutation, asked of one outside oracle

The oracle with independent answers draws each new forward answer itself.

Here each new forward answer is one query to an outside oracle with no input.

New inverse answers still come from coins.

The cache and the flag change as before, and each new forward query is logged with its answer.

With uniform answers from the outside oracle, the output, the cache and the flag keep their law.

A replay forking lemma rewinds a run at one query of an oracle.

So a run in this form can be rewound at a new forward query of the permutation.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

The change is the forward part of their Game G2 of Figure 7, in the proof of their Theorem 2.

Its lines 01 and 19 answer new forward queries with values `β_1, …, β_Q` drawn up front.

The inverse answers stay those of their Game G1, line 25.

Their Game G2 also changes those, in lines 26 to 28, which this run leaves out.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A : Type}

/-- The oracles of a run in this form: coins, and one outside oracle with no input. -/
abbrev OutsideSpec (A : Type) := unifSpec + (Unit →ₒ A)

/-- The state: the cache and the flag of independent answers, then the log.

The log holds each new forward query with its answer, the first one first. -/
abbrev OutsideState (A : Type) := IndepState A × List (A × A)

variable [FinEnum A]

/-- The permutation oracle with independent answers, the new forward ones asked outside.

A query answered before gets its answer again, in either direction.

A new forward query asks the outside oracle once, and joins the log with its answer.

A new inverse query gets a uniform value of `A` from coins.

The cache and the flag change by the same rules as with independent answers. -/
def outsideOracle : QueryImpl (PermSpec A) (StateT (OutsideState A) (OracleComp (OutsideSpec A)))
  | .inl a => fun s =>
    match s.1.1.lookup a with
    | some b => pure (b, s)
    | none =>
      (fun b : A => (b, (IndepState.addForward s.1 a b, s.2 ++ [(a, b)]))) <$>
        (query (spec := OutsideSpec A) (.inr ()) : OracleComp (OutsideSpec A) A)
  | .inr b => fun s =>
    match (s.1.1.map Prod.swap).lookup b with
    | some a => pure (a, s)
    | none =>
      (fun a => (a, (IndepState.addInverse s.1 a b, s.2))) <$>
        liftComp (uniformOutside [] b) (OutsideSpec A)

/-- The oracles of this form: coins, passed to the coins outside, then the oracle above. -/
def outsideImpl :
    QueryImpl (unifSpec + PermSpec A) (StateT (OutsideState A) (OracleComp (OutsideSpec A)))
  | .inl n => fun s =>
    (·, s) <$> (query (spec := OutsideSpec A) (.inl n) : OracleComp (OutsideSpec A) (Fin (n + 1)))
  | .inr t => outsideOracle t

/-- Each step adds at most one pair to the log, and only a new forward query adds one. -/
theorem length_log_le_of_mem_support_outsideImpl (t : (unifSpec + PermSpec A).Domain)
    (s : OutsideState A) (z) (hz : z ∈ support ((outsideImpl t).run s)) :
    z.2.2.length ≤ s.2.length + if t.isRight = true then 1 else 0 := by
  rcases t with n | a | b
  · simp only [outsideImpl, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · simp only [outsideImpl, outsideOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp
  · simp only [outsideImpl, outsideOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp

/-- A run that asks the permutation at most `Q` times adds at most `Q` pairs to the log. -/
theorem length_log_le_of_mem_support_simulateQ_outsideImpl {α : Type} {oa : PermComp A α}
    {Q : ℕ} (hQ : IsQueryBoundP oa (·.isRight = true) Q) (s : OutsideState A) (z)
    (hz : z ∈ support ((simulateQ outsideImpl oa).run s)) : z.2.2.length ≤ s.2.length + Q :=
  hQ.cost_le_of_mem_support_run_simulateQ (impl := outsideImpl) (fun s => s.2.length)
    (fun t ht s w hw => by simpa [ht] using length_log_le_of_mem_support_outsideImpl t s w hw)
    (fun t ht s w hw => by simpa [ht] using length_log_le_of_mem_support_outsideImpl t s w hw)
    s z hz

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

omit [FinEnum A] in
/-- The outside oracle, with uniform answers, is a uniform value of `A`. -/
theorem query_outside_evalDistEq :
    EvalDistEq (query (spec := OutsideSpec A) (.inr ()) : OracleComp (OutsideSpec A) A)
      ($ᵗ A : ProbComp A) := by
  let : MeasurableSpace A := ⊤
  have : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  refine EvalDistEq.of_evalDist_eq (α := A) ?_
  rw [SampleableType.evalDist_uniformSample]
  exact evalDist_query_uniform (spec := OutsideSpec A) (.inr ())

omit [FinEnum A] [SampleableType A] in
/-- A value returned outright has the same law in both runs. -/
theorem pure_outside_evalDistEq {α : Type} (x : α) :
    EvalDistEq (pure x : OracleComp (OutsideSpec A) α) (pure x : ProbComp α) :=
  EvalDistEq.of_forall_prEvent_eq fun p => by
    classical
    rw [prEvent_pure, prEvent_pure]

/-- With the log dropped, each step has the law of the step with independent answers. -/
theorem outsideImpl_run_evalDistEq (t : (unifSpec + PermSpec A).Domain) (s : IndepState A)
    (l : List (A × A)) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (outsideImpl t).run (s, l))
      ((indepPermImpl t).run s) := by
  obtain ⟨c, f⟩ := s
  rcases t with n | a | b
  · rw [passthrough_add_inl_run]
    simp only [outsideImpl, StateT.run, Functor.map_map]
    exact (evalDistEq_liftM_query_uniform (spec := unifSpec) (superSpec := OutsideSpec A) n).map _
  · rw [indepPermImpl_inr, indepPermOracle_inl_run]
    simp only [outsideImpl, outsideOracle, StateT.run]
    cases c.lookup a with
    | some b => simpa only [map_pure] using pure_outside_evalDistEq _
    | none =>
      simp only [Functor.map_map]
      exact (query_outside_evalDistEq.trans (uniformOutside_nil_evalDistEq a).symm).map _
  · rw [indepPermImpl_inr, indepPermOracle_inr_run]
    simp only [outsideImpl, outsideOracle, StateT.run]
    cases (c.map Prod.swap).lookup b with
    | some a => simpa only [map_pure] using pure_outside_evalDistEq _
    | none =>
      simp only [Functor.map_map]
      exact (evalDistEq_liftComp_uniform _).map _

/-- **Asking new forward answers outside keeps the law of the run with independent answers.**

Drop the log at the end: the output, the cache and the flag have the same law. -/
theorem simulateQ_outsideImpl_run_evalDistEq {α : Type} (oa : PermComp A α) (s : IndepState A)
    (l : List (A × A)) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (simulateQ outsideImpl oa).run (s, l))
      ((simulateQ indepPermImpl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s l with
  | pure x => simpa only [simulateQ_pure, StateT.run_pure, map_pure] using pure_outside_evalDistEq _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, map_bind]
    refine (EvalDistEq.bind_right ((outsideImpl t).run (s, l))
      (g := fun z => liftComp ((simulateQ indepPermImpl (k z.1)).run z.2.1) (OutsideSpec A))
      fun z => ?_).trans ?_
    · simpa only [Prod.mk.eta] using
        (ih z.1 z.2.1 z.2.2).trans (evalDistEq_liftComp_uniform _).symm
    · have h := (outsideImpl_run_evalDistEq t s l).bind
        (f := fun z => liftComp ((simulateQ indepPermImpl (k z.1)).run z.2) (OutsideSpec A))
        (g := fun z => (simulateQ indepPermImpl (k z.1)).run z.2)
        fun _ => evalDistEq_liftComp_uniform _
      simpa only [bind_map_left] using h

end EthLib.Cryptography.LazyPermutation

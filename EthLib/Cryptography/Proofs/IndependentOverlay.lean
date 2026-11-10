module

public import EthLib.Cryptography.Proofs.IndependentAnswers
public import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Proofs: independent answers to a permutation, asked of one outside oracle

The oracle with independent answers draws each new forward answer itself.

Here each new forward answer is one query to an outside oracle with no input.

New inverse answers still come from coins.

The cache and the flag change as before, and the new forward queries are logged in order.

With uniform answers from the outside oracle, the output, the cache and the flag keep their law.

The forking lemma rewinds a run at one query of an oracle.

So a run in this form can be rewound at a new forward query of the permutation.

The source is [Fersch, Kiltz, Poettering, CCS 2016](https://doi.org/10.1145/2976749.2978413).

Their algorithm `A` of Figure 8 answers new forward queries with values given as input.

It answers new inverse queries from its coins.
-/

@[expose] public section

namespace EthLib.Cryptography.LazyPermutation

open OracleComp OracleSpec ENNReal

variable {A : Type}

/-- The oracles of a run in this form: coins, and one outside oracle with no input. -/
abbrev OverlaySpec (A : Type) := unifSpec + (Unit →ₒ A)

/-- The state: the cache and the flag of independent answers, then the new forward queries.

The new forward queries are in the order asked, the first one first. -/
abbrev OverlayState (A : Type) := IndepState A × List A

variable [FinEnum A]

/-- The permutation oracle with independent answers, the new forward ones asked outside.

A query answered before gets its answer again, in either direction.

A new forward query asks the outside oracle once, and joins the log.

A new inverse query gets a uniform value of `A` from coins.

The cache and the flag change as with independent answers. -/
def overlayOracle : QueryImpl (PermSpec A) (StateT (OverlayState A) (OracleComp (OverlaySpec A)))
  | .inl a => fun s =>
    match s.1.1.lookup a with
    | some b => pure (b, s)
    | none =>
      (fun b => (b, (((a, b) :: s.1.1, s.1.2 || decide (b ∈ s.1.1.map Prod.snd)), s.2 ++ [a]))) <$>
        (query (spec := OverlaySpec A) (.inr ()) : OracleComp (OverlaySpec A) A)
  | .inr b => fun s =>
    match (s.1.1.map Prod.swap).lookup b with
    | some a => pure (a, s)
    | none =>
      (fun a => (a, (((a, b) :: s.1.1, s.1.2 || decide (a ∈ s.1.1.map Prod.fst)), s.2))) <$>
        liftComp (uniformOutside [] b) (OverlaySpec A)

/-- The oracles of this form: coins, passed to the coins outside, then the oracle above. -/
def overlayImpl :
    QueryImpl (unifSpec + PermSpec A) (StateT (OverlayState A) (OracleComp (OverlaySpec A)))
  | .inl n => fun s =>
    (·, s) <$> (query (spec := OverlaySpec A) (.inl n) : OracleComp (OverlaySpec A) (Fin (n + 1)))
  | .inr t => overlayOracle t

/-- A run of coins alone with independent answers leaves the state unchanged. -/
theorem simulateQ_indepPermImpl_liftM_run {α : Type} (oa : ProbComp α) (s : IndepState A) :
    (simulateQ indepPermImpl (liftM oa : PermComp A α)).run s = (·, s) <$> oa := by
  rw [QueryImpl.simulateQ_liftM_eq_of_query indepPermImpl
    ((QueryImpl.id' unifSpec).liftTarget (StateT (IndepState A) ProbComp))
    (fun t => by simp [indepPermImpl]) oa]
  simp [StateT.run_monadLift]

/-- Each step adds at most one query to the log, and only a query of the permutation adds one. -/
theorem length_log_le_of_mem_support_overlayImpl (t : (unifSpec + PermSpec A).Domain)
    (s : OverlayState A) (z) (hz : z ∈ support ((overlayImpl t).run s)) :
    z.2.2.length ≤ s.2.length + if t.isRight = true then 1 else 0 := by
  rcases t with n | a | b
  · simp only [overlayImpl, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    simp
  · simp only [overlayImpl, overlayOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp
  · simp only [overlayImpl, overlayOracle, StateT.run] at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      simp [hz]
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      simp

/-- A run that asks the permutation at most `Q` times logs at most `Q` new forward queries. -/
theorem length_log_le_of_mem_support_simulateQ_overlayImpl {α : Type} {oa : PermComp A α}
    {Q : ℕ} (hQ : IsQueryBoundP oa (·.isRight = true) Q) (s : OverlayState A) (z)
    (hz : z ∈ support ((simulateQ overlayImpl oa).run s)) : z.2.2.length ≤ s.2.length + Q :=
  hQ.cost_le_of_mem_support_run_simulateQ (impl := overlayImpl) (fun s => s.2.length)
    (fun t ht s w hw => by simpa [ht] using length_log_le_of_mem_support_overlayImpl t s w hw)
    (fun t ht s w hw => by simpa [ht] using length_log_le_of_mem_support_overlayImpl t s w hw)
    s z hz

variable [SampleableType A] [UniformAnswerMeasure (Unit →ₒ A)]

/-- The outside oracle, with uniform answers, is a uniform value of `A`. -/
theorem query_overlay_evalDistEq :
    EvalDistEq (query (spec := OverlaySpec A) (.inr ()) : OracleComp (OverlaySpec A) A)
      ($ᵗ A : ProbComp A) := by
  let : MeasurableSpace A := ⊤
  have : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  refine EvalDistEq.of_evalDist_eq (α := A) ?_
  rw [SampleableType.evalDist_uniformSample]
  exact evalDist_query_uniform (spec := OverlaySpec A) (.inr ())

omit [FinEnum A] [SampleableType A] in
/-- A value returned outright has the same law in both runs. -/
theorem pure_evalDistEq {α : Type} (x : α) :
    EvalDistEq (pure x : OracleComp (OverlaySpec A) α) (pure x : ProbComp α) :=
  EvalDistEq.of_forall_prEvent_eq fun p => by
    classical
    rw [prEvent_pure, prEvent_pure]

/-- With the log dropped, each step has the law of the step with independent answers. -/
theorem overlayImpl_run_evalDistEq (t : (unifSpec + PermSpec A).Domain) (s : IndepState A)
    (l : List A) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (overlayImpl t).run (s, l))
      ((indepPermImpl t).run s) := by
  obtain ⟨c, f⟩ := s
  rcases t with n | a | b
  · rw [passthrough_add_inl_run]
    simp only [overlayImpl, StateT.run, Functor.map_map]
    exact (evalDistEq_liftM_query_uniform (spec := unifSpec) (superSpec := OverlaySpec A) n).map _
  · rw [indepPermImpl_inr, indepPermOracle_inl_run]
    simp only [overlayImpl, overlayOracle, StateT.run]
    cases c.lookup a with
    | some b => simpa only [map_pure] using pure_evalDistEq _
    | none =>
      simp only [Functor.map_map]
      exact (query_overlay_evalDistEq.trans (uniformOutside_nil_evalDistEq a).symm).map _
  · rw [indepPermImpl_inr, indepPermOracle_inr_run]
    simp only [overlayImpl, overlayOracle, StateT.run]
    cases (c.map Prod.swap).lookup b with
    | some a => simpa only [map_pure] using pure_evalDistEq _
    | none =>
      simp only [Functor.map_map]
      exact (evalDistEq_liftComp_uniform _).map _

/-- **Asking new forward answers outside keeps the law of the run with independent answers.**

Drop the log at the end: the output, the cache and the flag have the same law. -/
theorem simulateQ_overlayImpl_run_evalDistEq {α : Type} (oa : PermComp A α) (s : IndepState A)
    (l : List A) :
    EvalDistEq ((fun z => (z.1, z.2.1)) <$> (simulateQ overlayImpl oa).run (s, l))
      ((simulateQ indepPermImpl oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s l with
  | pure x => simpa only [simulateQ_pure, StateT.run_pure, map_pure] using pure_evalDistEq _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, map_bind]
    refine (EvalDistEq.bind_right ((overlayImpl t).run (s, l))
      (g := fun z => liftComp ((simulateQ indepPermImpl (k z.1)).run z.2.1) (OverlaySpec A))
      fun z => ?_).trans ?_
    · simpa only [Prod.mk.eta] using
        (ih z.1 z.2.1 z.2.2).trans (evalDistEq_liftComp_uniform _).symm
    · have h := (overlayImpl_run_evalDistEq t s l).bind
        (f := fun z => liftComp ((simulateQ indepPermImpl (k z.1)).run z.2) (OverlaySpec A))
        (g := fun z => (simulateQ indepPermImpl (k z.1)).run z.2)
        fun _ => evalDistEq_liftComp_uniform _
      simpa only [bind_map_left] using h

end EthLib.Cryptography.LazyPermutation

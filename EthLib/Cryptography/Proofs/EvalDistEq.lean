module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.EvalDist.Monad.UniformTable

/-!
# Proofs: equality in distribution

Elaboration aids and small lemmas for two computations with the same output distribution.

Uniform samplers and uniform tables are the main cases.

Two inequalities bound an event after a common draw, from a bound at each output of the draw.
-/

@[expose] public section

universe v

/-- Elaborate both sides of the infix notation against a common type, as `=` does.

So a side whose monad is only known from the other elaborates.

For example, a `do` block or `pure` in a `calc` step. -/
macro_rules | `($a =ᵈ $b) => `(binrel% EvalDistEq $a $b)

/-- Syntactically equal computations are equal in distribution. -/
theorem EvalDistEq.of_eq {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type}
    {mx my : m α} (h : mx = my) : mx =ᵈ my :=
  h ▸ EvalDistEq.rfl

/-- Every uniform sampler of a type is equal in distribution to every other. -/
theorem SampleableType.uniformSample_evalDistEq_of_inst {A : Type} (i₁ i₂ : SampleableType A) :
    (@uniformSample A i₁) =ᵈ (@uniformSample A i₂) :=
  EvalDistEq.of_forall_prEvent_eq fun p => SampleableType.prEvent_uniformSample_inst_irrel i₁ i₂ p

/-- Overwrite one cell of a uniform table with an independent uniform value.

The table stays uniform, before any continuation. -/
theorem evalDistEq_uniformSample_bind_update {D R α : Type} [Finite D] [DecidableEq D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)] (t : D) (f : (D → R) → ProbComp α) :
    ($ᵗ R >>= fun u => $ᵗ (D → R) >>= fun g => f (Function.update g t u)) =ᵈ
      ($ᵗ (D → R) >>= f) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace α := ⊤
  exact evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R)) SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample t f

/-- Restricting a uniform table along an injection gives a uniform table. -/
theorem evalDistEq_uniformSample_map_comp_injective {A B R : Type} [Finite A] [Finite B]
    [Finite R] [Nonempty R] [SampleableType (A → R)] [SampleableType (B → R)]
    {e : A → B} (he : Function.Injective e) :
    ((fun g : B → R => g ∘ e) <$> ($ᵗ (B → R))) =ᵈ ($ᵗ (A → R)) :=
  let : MeasurableSpace R := ⊤
  EvalDistEq.of_evalDist_eq (evalDist_map_table_comp_injective ($ᵗ (A → R)) ($ᵗ (B → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample he)

/-- Reading a uniform vector at distinct positions gives a uniform table of the values read. -/
theorem evalDistEq_uniformSample_vector_map_getElem_injective {R : Type} {m n : Nat} [Finite R]
    [Nonempty R] [SampleableType (Vector R m)] [SampleableType (Fin m → R)]
    [SampleableType (Fin n → R)] {e : Fin n → Fin m} (he : Function.Injective e) :
    ((fun v : Vector R m => fun j => v[(e j).val]) <$> ($ᵗ (Vector R m))) =ᵈ
      ($ᵗ (Fin n → R)) :=
  calc
    _ =ᵈ ((fun g : Fin m → R => g ∘ e) <$>
        (arrayVectorEquivFin R m <$> ($ᵗ (Vector R m)))) := by
      simp only [Functor.map_map]
      exact EvalDistEq.rfl
    _ =ᵈ ((fun g : Fin m → R => g ∘ e) <$> ($ᵗ (Fin m → R))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective
        (arrayVectorEquivFin R m).bijective).map _
    _ =ᵈ ($ᵗ (Fin n → R)) := evalDistEq_uniformSample_map_comp_injective he

/-- A bound on each continuation, over the support, bounds the binds.

The event of one continuation is at most the sum of the events of two others.

The sum is taken after a common draw. -/
theorem OracleComp.prEvent_bind_le_add_of_forall_le_of_support {α β γ δ : Type}
    (oa : ProbComp α) (g : α → ProbComp β) (h : α → ProbComp γ) (k : α → ProbComp δ)
    (p : β → Prop) (q : γ → Prop) (r : δ → Prop)
    (hle : ∀ y ∈ support oa,
      Pr{let z ← g y}[p z] ≤ Pr{let z ← h y}[q z] + Pr{let z ← k y}[r z]) :
    Pr{let z ← oa >>= g}[p z] ≤ Pr{let z ← oa >>= h}[q z] + Pr{let z ← oa >>= k}[r z] := by
  rw [bind_eq_attach_bind oa g, bind_eq_attach_bind oa h, bind_eq_attach_bind oa k]
  exact prEvent_bind_le_add_of_forall_le _ _ _ _ p q r fun y => hle y.1 y.2

open MeasureTheory in
/-- Take continuation events within `ε` of each other at every possible output of a common prefix.

They stay within `ε` after the prefix. -/
theorem OracleComp.prEvent_bind_congr_le_add {ι : Type} {spec : OracleSpec ι}
    [OracleSpec.AnswerMeasure spec] {α β : Type} {mx : OracleComp spec α}
    {my oc : α → OracleComp spec β} {q : β → Prop} {ε : ENNReal}
    (h : ∀ x ∈ support mx, Pr{let y ← my x}[q y] ≤ Pr{let y ← oc x}[q y] + ε) :
    Pr{let y ← mx >>= my}[q y] ≤ Pr{let y ← mx >>= oc}[q y] + ε := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ x, Pr{let y ← my x}[q y] ∂𝒟[mx]
      ≤ ∫⁻ x, (Pr{let y ← oc x}[q y] + ε) ∂𝒟[mx] :=
        lintegral_mono_ae (OracleComp.ae_evalDist_of_forall_mem_support mx h)
    _ = (∫⁻ x, Pr{let y ← oc x}[q y] ∂𝒟[mx]) + ε * 𝒟[mx] Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ (∫⁻ x, Pr{let y ← oc x}[q y] ∂𝒟[mx]) + ε := by
        gcongr
        exact mul_le_of_le_one_right' prob_le_one

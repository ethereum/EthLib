module

public import Batteries.Data.Fin.Coding
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.IrreducibleDef
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.SubSpec
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.ProgramLogic.Relational.ProgrammingOracle
public import VCVio.ProgramLogic.Relational.Quantitative

/-!
# Oracle and sampling lemmas

This module counts the queries of a computation that satisfy a predicate.

It splits a uniform table along an injection into two independent uniform tables.

It also shows that one cell of a uniform table can be sampled first, apart from the rest.
-/

@[expose] public section

namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec

variable {Index : Type} {spec : OracleSpec Index} {Result Next : Type}
  (selected : Index → Prop) [DecidablePred selected]

/-- The computation, paired with the number of its queries that satisfy the predicate. -/
noncomputable def counted (computation : OracleComp spec Result) :
    OracleComp spec (Result × Nat) :=
  OracleComp.construct (fun result => pure (result, 0))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, (if selected input then 1 else 0) + result.2)) computation

theorem counted_pure (result : Result) :
    counted selected (pure result : OracleComp spec Result) = pure (result, 0) := rfl

theorem counted_query_bind (input : spec.Domain)
    (next : spec.Range input → OracleComp spec Result) :
    counted selected (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← counted selected (next answer)
      pure (result.1, (if selected input then 1 else 0) + result.2)) := rfl

theorem counted_query (input : spec.Domain) :
    counted selected (liftM (spec.query input)) =
      (fun answer => (answer, if selected input then 1 else 0)) <$>
        (liftM (spec.query input) : OracleComp spec _) := by
  change (do
    let answer ← liftM (spec.query input)
    pure (answer, (if selected input then 1 else 0) + 0)) = _
  simp only [Nat.add_zero, pure_bind, bind_pure_comp]

theorem simulate_withCost {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (computation : OracleComp spec α) :
    simulateQ impl (counted selected computation) =
      (simulateQ (impl.withAddCost (fun input => if selected input then 1 else (0 : Nat)))
        computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih,
        WriterT.run_bind]
      simp [QueryImpl.withAddCost, QueryImpl.withCost,
        WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, map_eq_bind_pure_comp, bind_assoc]
      rfl

theorem counted_bind (computation : OracleComp spec Result)
    (next : Result → OracleComp spec Next) :
    counted selected (computation >>= next) = (do
      let first ← counted selected computation
      let second ← counted selected (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, counted_pure, zero_add, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, counted_query_bind, ih, pure_bind, Nat.add_assoc]

theorem counted_map (computation : OracleComp spec Result) (f : Result → Next) :
    counted selected (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> counted selected computation := by
  rw [show f <$> computation = computation >>= fun result => pure (f result) from
      (bind_pure_comp f computation).symm,
    counted_bind]
  simp only [counted_pure, Nat.add_zero, bind_pure_comp, map_pure]

end SphincsSecurity.QueryCap

namespace SphincsSecurity.UniformTableSplit

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable

variable {Index Cell Answer : Type}

/-- The cells outside the image of the injection. -/
abbrev Outside (embed : Index → Cell) := {cell : Cell // cell ∉ Set.range embed}

/-- A table on all cells, as a table on the indices and a table on the cells outside the image. -/
noncomputable def split (embed : Index → Cell) (hinj : Function.Injective embed) :
    (Cell → Answer) ≃ (Index → Answer) × (Outside embed → Answer) :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range embed)).symm.trans
    ((Equiv.ofInjective embed hinj).symm.sumCongr (Equiv.refl (Outside embed))))
      (Equiv.refl Answer)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)

theorem split_fst (embed : Index → Cell) (hinj : Function.Injective embed)
    (table : Cell → Answer) :
    (split embed hinj table).1 = table ∘ embed := by
  funext index
  simp [split, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]

theorem split_snd (embed : Index → Cell) (hinj : Function.Injective embed)
    (table : Cell → Answer) :
    (split embed hinj table).2 = fun cell => table cell.val := by
  funext cell
  simp [split, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
  rfl

/-- The table on all cells with the given rows on the image and the given values outside it. -/
noncomputable def join (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) : Cell → Answer :=
  (split embed hinj).symm (rows, outside)

@[simp] theorem join_embed (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) (index : Index) :
    join embed hinj rows outside (embed index) = rows index := by
  have h := congrArg Prod.fst ((split embed hinj).apply_symm_apply (rows, outside))
  rw [split_fst] at h
  exact congrFun h index

@[simp] theorem join_outside (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) (cell : Outside embed) :
    join embed hinj rows outside cell.val = outside cell := by
  have h := congrArg Prod.snd ((split embed hinj).apply_symm_apply (rows, outside))
  rw [split_snd] at h
  exact congrFun h cell

/-- Two independent uniform draws combined by a bijection are one uniform draw. -/
theorem uniform_pair_of_bijective {Left Right Joined : Type} [SampleableType Left]
    [SampleableType Right] [SampleableType Joined] {combine : Left → Right → Joined}
    (hcombine : Function.Bijective (Function.uncurry combine)) :
    ($ᵗ Joined : ProbComp Joined) =ᵈ
      (do let left ← $ᵗ Left; let right ← $ᵗ Right; pure (combine left right) :
        ProbComp Joined) := by
  have h : Function.uncurry combine <$>
      (do let left ← $ᵗ Left; let right ← $ᵗ Right; return (left, right) : ProbComp _) =ᵈ
        ($ᵗ Joined : ProbComp Joined) := by
    let : MeasurableSpace Left := ⊤
    let : MeasurableSpace Right := ⊤
    let : MeasurableSpace Joined := ⊤
    refine EvalDistEq.of_evalDist_eq ?_
    rw [evalDist_map_of_discrete, evalDist_pair, SampleableType.evalDist_uniformSample,
      SampleableType.evalDist_uniformSample, SampleableType.evalDist_uniformSample,
      ← ProbabilityTheory.uniformOn_univ_prod]
    exact ProbabilityTheory.map_uniformOn_univ_of_bijective Measurable.of_discrete hcombine
  simpa only [map_bind, map_pure, Function.uncurry_apply_pair] using h.symm

/-- A uniform draw from a product is two independent uniform draws. -/
theorem uniform_product {Left Right : Type} [SampleableType Left] [SampleableType Right] :
    ($ᵗ (Left × Right) : ProbComp (Left × Right)) =ᵈ
      (do let left ← $ᵗ Left; let right ← $ᵗ Right; pure (left, right) : ProbComp _) :=
  uniform_pair_of_bijective (combine := Prod.mk) Function.bijective_id

/-- A uniform table is a uniform table on the image of the injection and a table on the rest.

The table on the other cells is uniform and independent. -/
theorem uniform_join [SampleableType Answer] [SampleableType (Cell → Answer)]
    [SampleableType (Index → Answer)] (embed : Index → Cell) (hinj : Function.Injective embed)
    [SampleableType (Outside embed → Answer)] :
    ($ᵗ (Cell → Answer) : ProbComp (Cell → Answer)) =ᵈ
      (do
        let rows ← $ᵗ (Index → Answer)
        let outside ← $ᵗ (Outside embed → Answer)
        pure (join embed hinj rows outside) : ProbComp _) :=
  uniform_pair_of_bijective (split embed hinj).symm.bijective

end SphincsSecurity.UniformTableSplit

namespace SphincsSecurity.FiniteGraphSampling

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling

variable {Cell Answer : Type} [DecidableEq Cell] [_root_.Finite Cell]
  [SampleableType Answer] [SampleableType (Cell → Answer)]

/-- A uniform table and one of its cells can be drawn in the other order.

Draw the cell value first, then a uniform table, and write the value into that cell. -/
theorem evalDist_table_extract {Result : Type} (cell : Cell)
    (next : (Cell → Answer) → Answer → ProbComp Result) :
    (do let table ← ($ᵗ (Cell → Answer) : ProbComp _); next table (table cell)) =ᵈ
      (do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next (Function.update table cell answer) answer) := by
  have h : (do
      let answer ← ($ᵗ Answer : ProbComp _)
      let table ← ($ᵗ (Cell → Answer) : ProbComp _)
      pure (Function.update table cell answer)) =ᵈ ($ᵗ (Cell → Answer) : ProbComp _) := by
    let : MeasurableSpace Answer := ⊤
    refine EvalDistEq.of_evalDist_eq ?_
    simpa only [id_eq, bind_pure] using evalDist_uniformSample_bind_update_map
      (SampleableType.evalDist_uniformSample (β := Answer))
      (SampleableType.evalDist_uniformSample (β := Cell → Answer)) cell id
  have h' := h.symm.bind_left (fun table => next table (table cell))
  simpa only [bind_assoc, pure_bind, Function.update_self] using h'

omit [DecidableEq Cell] [_root_.Finite Cell] [SampleableType Answer]
  [SampleableType (Cell → Answer)] in
/-- Two independent draws have the same joint distribution in either order. -/
theorem bind_bind_swap {α β γ : Type} (mx : ProbComp α) (my : ProbComp β)
    (f : α → β → ProbComp γ) :
    (mx >>= fun a => my >>= fun b => f a b) =ᵈ (my >>= fun b => mx >>= fun a => f a b) := by
  let : MeasurableSpace γ := ⊤
  exact EvalDistEq.of_evalDist_eq (evalDist_bind_bind_swap mx my f)

end SphincsSecurity.FiniteGraphSampling

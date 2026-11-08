module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.HiddenOracle

/-!
# Resampling the hidden coordinates

The seed-free experiment is an average over every public and structural sample.

For each sample, it runs the hidden-row program on a coordinate table.

That table is an exact uniform completion of the known coordinates.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.HiddenBridge

variable [Params]

open Completeness SeedModel Graph Assembly Reduce HiddenGraph
open UniformTableSplit

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Swapping the known parts of two tables is an involution. -/
noncomputable def swapKnown (parameter : PublicParameter)
    (pair : HiddenGraph.Table × HiddenGraph.Table) :
    HiddenGraph.Table × HiddenGraph.Table :=
  (mix parameter pair.1 pair.2, mix parameter pair.2 pair.1)

theorem swapKnown_involutive (parameter : PublicParameter) :
    Function.Involutive (swapKnown parameter) := by
  intro pair
  apply Prod.ext <;> funext coordinate <;>
    by_cases h : KnownCoordinate parameter coordinate <;> simp [swapKnown, mix, h]

omit [Params] in
theorem uniform_map_fst {α β : Type} [SampleableType α] [SampleableType β] :
    Prod.fst <$> ($ᵗ (α × β) : ProbComp (α × β)) =ᵈ ($ᵗ α : ProbComp α) := by
  refine (uniform_product.map Prod.fst).trans ?_
  simp only [map_bind, map_pure]
  calc (($ᵗ α : ProbComp α) >>= fun a => ($ᵗ β : ProbComp β) >>= fun _ => (pure a : ProbComp α))
      =ᵈ (($ᵗ α : ProbComp α) >>= fun a => (pure a : ProbComp α)) :=
        EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.bind_const _ _
    _ =ᵈ ($ᵗ α : ProbComp α) := by rw [bind_pure]

noncomputable local instance sampleCellFintypeInst : Fintype SampleCell := sampleCellFintype
noncomputable local instance sampleCellDecEq : DecidableEq SampleCell := Classical.decEq _
noncomputable local instance hiddenTableSampleable : SampleableType HiddenGraph.Table :=
  SampleableType.ofFintype _
noncomputable local instance highsSampleable : SampleableType CoordinateHighs :=
    SampleableType.ofFintype _
noncomputable local instance remainingSampleable : SampleableType RemainingOutputs :=
  SampleableType.ofFintype _

theorem uniform_mix (parameter : PublicParameter) :
    (($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table) >>= fun fixed =>
      mix parameter fixed <$> ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)) =ᵈ
      ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table) := by
  have hpair : Prod.fst <$> (swapKnown parameter <$>
      ($ᵗ (HiddenGraph.Table × HiddenGraph.Table) : ProbComp
          (HiddenGraph.Table × HiddenGraph.Table))) =ᵈ
      (($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table) >>= fun fixed =>
        mix parameter fixed <$> ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)) := by
    rw [Functor.map_map]
    refine (uniform_product.map _).trans ?_
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, swapKnown,
      EvalDistEq.refl]
  exact hpair.symm.trans (((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (swapKnown_involutive parameter).bijective).map Prod.fst).trans uniform_map_fst)

omit [Params] in
theorem evalDist_uniform_congr {α : Type} [Fintype α] [Nonempty α] (left right : SampleableType α) :
    (@uniformSample α left : ProbComp α) =ᵈ (@uniformSample α right : ProbComp α) :=
  EvalDistEq.of_forall_prEvent_eq fun p =>
      SampleableType.prEvent_uniformSample_inst_irrel left right p

theorem evalDist_mix (parameter : PublicParameter) :
    (($ᵗ HiddenGraph.Table) >>= fun fixed => mix parameter fixed <$> ($ᵗ HiddenGraph.Table)) =ᵈ
      ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table) :=
  uniform_mix parameter

theorem evalDist_mix_bind {β : Type} (parameter : PublicParameter)
    (next : HiddenGraph.Table → ProbComp β) :
    ($ᵗ HiddenGraph.Table) >>= next =ᵈ
      (($ᵗ HiddenGraph.Table) >>= fun fixed => ($ᵗ HiddenGraph.Table) >>= fun fresh =>
        next (mix parameter fixed fresh)) := by
  have h := (evalDist_mix parameter).symm.bind_left next
  simpa only [bind_assoc, bind_map_left] using h

theorem evalDist_completion_bind {β : Type} (known : HiddenReveal.Knowledge Coordinate)
    (next : HiddenGraph.Table → ProbComp β) :
    HiddenReveal.completion known >>= next =ᵈ
      (($ᵗ HiddenGraph.Table) >>= fun fresh => next (tableExtending known fresh)) := by
  unfold HiddenReveal.completion
  refine (Eager.evalDist_map_bind' _ _ _).trans ?_
  exact (evalDist_uniform_congr HiddenReveal.tableSampleable hiddenTableSampleable).bind_left _

/-- The hidden-row run of one public and structural sample, at a given coordinate table. -/
noncomputable def hiddenRun (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (outsideTable : Eager.Table) (table : HiddenGraph.Table) :
    ProbComp (Option Bool × List (HiddenCost.Entry HashInput)) :=
  Stop.costRun
    (HiddenGraph.answer (truncateHash parameterOutput)
        (candidateActive (truncateHash parameterOutput))
      table (fun address => highs address.outputCoordinate)
      (outsideFn (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed) outsideTable))
    table
    (HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
      (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed)) steps) adversary) q)

/-- The seed-free experiment first samples every public and structural value.

It then samples the coordinate table as an exact completion of the known coordinates. -/
theorem evalDist_seedFree_completion (adversary : Adversary) (q : Nat)
    (steps : Message → Randomness) :
    seedFreeExperiment adversary q steps =ᵈ
      (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        let table ← HiddenReveal.completion (knownOf (truncateHash parameterOutput) fixed)
        hiddenRun adversary q steps parameterOutput fixed highs remaining outsideTable table) := by
  unfold seedFreeExperiment
  refine (evalDist_material_graph_continuation _).trans ?_
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  -- The seed-free run does not read the PRF key, so the draw of that key can be dropped.
  rw [show (fun prf : HashOutput => sampleSplitPair >>= fun pair =>
      ($ᵗ Eager.Table) >>= seedFreeRun adversary q steps ((parameterOutput, prf), pair.1)
        pair.2) =
      fun _ => sampleSplitPair >>= fun pair =>
        ($ᵗ Eager.Table) >>= seedFreeRun adversary q steps ((parameterOutput, 0), pair.1) pair.2
      from rfl]
  refine (OracleComp.EvalDistEq.bind_const _ _).trans ?_
  simp only [sampleSplitPair, bind_assoc, bind_map_left]
  refine (evalDist_mix_bind (truncateHash parameterOutput) _).trans ?_
  refine EvalDistEq.bind_right _ fun fixed => ?_
  simp only [joinedPair]
  change (($ᵗ HiddenGraph.Table) >>= fun fresh => ($ᵗ CoordinateHighs) >>= fun highs =>
      ($ᵗ RemainingOutputs) >>= fun remaining => ($ᵗ Eager.Table) >>= fun outsideTable =>
        seedFreeRun adversary q steps
          (splitMaterial parameterOutput highs remaining
              (mix (truncateHash parameterOutput) fixed fresh))
          (splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed fresh))
              outsideTable) =ᵈ _
  simp only [seedFreeRun_mix]
  refine (FiniteGraphSampling.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun highs => ?_
  refine (FiniteGraphSampling.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun remaining => ?_
  refine (FiniteGraphSampling.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun outsideTable => ?_
  refine EvalDistEq.trans ?_ (evalDist_completion_bind _ _).symm
  rfl

omit [Params] in
theorem probEvent_bind_mono_support {α β γ : Type} (p : ProbComp α) (k₁ : α → ProbComp β)
    (k₂ : α → ProbComp γ) (event₁ : β → Prop) (event₂ : γ → Prop)
    (h : ∀ a ∈ support p, Pr{let x ← k₁ a}[event₁ x] ≤ Pr{let x ← k₂ a}[event₂ x]) :
    Pr{let x ← p >>= k₁}[event₁ x] ≤ Pr{let x ← p >>= k₂}[event₂ x] := by
  simp only [OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support p
  · exact mul_le_mul' le_rfl (h a ha)
  · rw [(prEvent_eq_zero_of_not_mem_support _) ha]
    simp

/-- The row model of one sample, whose high halves are the independent sampled ones. -/
noncomputable def sampleModel (parameterOutput : HashOutput) (highs : CoordinateHighs) :
    HiddenRows.Model HashInput HashOutput Address Coordinate :=
  rowModel (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
    (fun address => highs address.outputCoordinate)

/-- The capped graph-view program of one sample. -/
noncomputable def sampleProgram (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    OracleComp GraphView.CostSpec (Option Bool) :=
  HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
    (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed)) steps) adversary) q

theorem hiddenRun_eq (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (parameterOutput : HashOutput)
    (fixed : HiddenGraph.Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (outsideTable : Eager.Table) (table : HiddenGraph.Table) :
    hiddenRun adversary q steps parameterOutput fixed highs remaining outsideTable table =
      Stop.costRun (HiddenRows.answer (sampleModel parameterOutput highs) table
        (outsideFn (splitMaterial parameterOutput highs remaining fixed)
          (splitAnswers highs remaining fixed) outsideTable)) table
        (sampleProgram adversary q steps parameterOutput fixed highs remaining) := by
  unfold hiddenRun sampleModel sampleProgram
  rw [rowModel_answer]

/-- From the seed-free experiment to the stopped one.

The chance of an event in the seed-free experiment is at most an average over the samples.

The samples are the public and the structural ones.

Each term is the chance of the event or a hidden stop in the stopped hidden-row experiment. -/
theorem seedFree_le_stopped (adversary : Adversary) (q : Nat) (steps : Message → Randomness)
    (event : Option Bool × List (HiddenCost.Entry HashInput) → Prop) :
    Pr{let x ← seedFreeExperiment adversary q steps}[event x] ≤
      Pr{let x ← (do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        HiddenRows.stoppedExperiment (sampleModel parameterOutput highs)
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) outsideTable)
          (HiddenCost.erase (HiddenCost.trace
            (sampleProgram adversary q steps parameterOutput fixed highs remaining)))
          (knownOf (truncateHash parameterOutput) fixed))}[(HiddenReveal.StopOr event) x] := by
  rw [(evalDist_seedFree_completion adversary q steps).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun parameterOutput _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun fixed _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun highs _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun remaining _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun outsideTable _ => ?_
  unfold HiddenRows.stoppedExperiment
  rw [(evalDist_completion_bind _ _).prEvent_eq, (evalDist_completion_bind _ _).prEvent_eq]
  refine probEvent_bind_mono_support _ _ _ _ _ fun fresh _ => ?_
  have hagree := HiddenRows.knownAgrees_completion
      (knownOf (truncateHash parameterOutput) fixed) fresh
  have h := costRun_le_stopped (sampleModel parameterOutput highs)
    (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
    (outsideFn (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) outsideTable)
    (sampleProgram adversary q steps parameterOutput fixed highs remaining)
    (knownOf (truncateHash parameterOutput) fixed) hagree event
  rw [hiddenRun_eq]
  exact h

end SphincsSecurity.Security.HiddenBridge

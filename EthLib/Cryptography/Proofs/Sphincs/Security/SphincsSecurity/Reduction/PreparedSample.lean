module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Reduction.EagerOracle
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.GraphView.CountedGame

/-!
# One sample of the short-query experiment

A sample holds seed material, graph labels and a uniform table on the other short inputs.

It gives a prepared cache and a fixed answer function.

That answer function agrees with the material, the graph labels and their surrogate boundary.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.Assembly

variable [Params]

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph

set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

omit [Params] in
theorem OnlyW.counted {α : Type} (selected : OracleWorld.Domain → Prop) [DecidablePred selected]
    (oa : OracleComp OracleWorld α) (h : OnlyW oa) :
    OnlyW (QueryCap.counted selected oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyW.pure' _
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      rw [QueryCap.counted_query_bind, OnlyW, isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun answer => ?_⟩
      have hnext : OnlyW (next answer) := by
        have := h.2 answer
        split at this <;> simpa [OnlyW] using this
      have hbind : OnlyW (QueryCap.counted selected (next answer) >>= fun result =>
          (pure (result.1, (if selected input then 1 else 0) + result.2) :
            OracleComp OracleWorld (α × Nat))) :=
        OnlyW.bind (ih answer hnext) (fun _ => OnlyW.pure' _)
      split <;> simpa [OnlyW] using hbind

omit [Params] in
/-- Handlers that answer each query equally in distribution simulate equally in distribution. -/
theorem evalDist_simulateQ_congr {ι : Type} {spec : OracleSpec ι}
    (impl₁ impl₂ : QueryImpl spec ProbComp)
    (h : ∀ input, impl₁ input =ᵈ impl₂ input) {α : Type} (oa : OracleComp spec α) :
    simulateQ impl₁ oa =ᵈ simulateQ impl₂ oa := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure, simulateQ_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query]
      exact (h input).bind ih

omit [Params] in
/-- The fixed-answer oracle is the fixed-hash source world. -/
theorem evalDist_fixedRom_eq_fixedHashWorld (f : HashInput → HashOutput) {α : Type}
    (oa : OracleComp OracleWorld α) :
    simulateQ (fixedRom f) oa = simulateQ (Prefix.fixedHashWorld f) oa := by
  congr 1

/-- Canonical labels completed from independent answers and the boundary surrogates. -/
noncomputable def labelsOf (material : Material) (answers : CanonicalGraphLabels) :
    CanonicalGraphLabels :=
  completedLabels (graphOrder (PrunedGraph.active (parameter material)))
    (PrunedGraph.initialLabels (parameter material)
      (GraphCorrectness.materialSurrogates material)) answers

/-- The prepared cache: seed material, then every active canonical graph response. -/
noncomputable def preparedCache (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) : QueryCache HashSpec :=
  programGraphCache (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) (graphOrder (PrunedGraph.active (parameter material)))
    (labelsOf material answers) (programCache ∅ seed material)

/-! ### Every sample is a consistent fixed answer function -/

omit [Params] in
theorem extend_cached {cache : QueryCache HashSpec} {table : Eager.Table} {input : HashInput}
    {answer : HashOutput} (h : cache input = some answer) : extend cache table input = answer := by
  simp [extend, h]

theorem preparedCache_other (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (input : HashInput)
    (hmiss : ∀ position, input ≠ canonicalGraphInput (parameter material)
      (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material) position
      (labelsOf material answers)) :
    preparedCache material seed answers input = programCache ∅ seed material input :=
  HiddenGraph.programGraphCache_preserves_other _ _ _ _ _ _ _ (fun position _ => hmiss position)

theorem preparedCache_parameter (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) :
    preparedCache material seed answers (parameterInput seed) =
      some (parameterOutput material) := by
  rw [preparedCache_other material seed answers (parameterInput seed)
    (fun position => keySeedInput_ne_tweakableHashInput _ _ _ _ _), programCache_parameter]

theorem preparedCache_prf (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) :
    preparedCache material seed answers (prfInput seed) = some (prf material) := by
  rw [preparedCache_other material seed answers (prfInput seed)
    (fun position => keySeedInput_ne_tweakableHashInput _ _ _ _ _), programCache_prf]

theorem preparedCache_secret (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (position : SecretPosition) :
    preparedCache material seed answers (secretInput seed material position) =
      some (material.2 position) := by
  rw [preparedCache_other material seed answers (secretInput seed material position)
    (fun other => keygenInput_ne_hashInput _ _ _ _ _ _), programCache_secret]

theorem preparedCache_label (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (position : Position)
    (hactive : PrunedGraph.active (parameter material) position) :
    preparedCache material seed answers (canonicalGraphInput (parameter material)
      (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material) position
      (labelsOf material answers)) = some (labelsOf material answers position) :=
  HiddenGraph.programGraphCache_label _ _ _ _ _ _ _ ((mem_graphOrder _ _).2 hactive)

/-- The answer function of one sample. -/
noncomputable def sampleFn (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) : QueryImpl HashSpec Id :=
  fun input => extend (preparedCache material seed answers) table input

theorem sample_agreement (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    PreparedAgreement (sampleFn material seed answers table) seed material :=
  ⟨extend_cached (preparedCache_parameter material seed answers),
    extend_cached (preparedCache_prf material seed answers),
    fun position => extend_cached (preparedCache_secret material seed answers position)⟩

theorem sample_consistent (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    GraphCorrectness.Consistent (sampleFn material seed answers table) (parameter material) seed
      (labelsOf material answers) := by
  intro position hactive
  rw [← GraphCorrectness.materialOts_eq _ seed material
      (sample_agreement material seed answers table),
    ← GraphCorrectness.materialFts_eq _ seed material
      (sample_agreement material seed answers table)]
  exact (extend_cached (preparedCache_label material seed answers position hactive)).symm

theorem sample_boundary (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    GraphCorrectness.BoundaryCorrect (sampleFn material seed answers table) (parameter material)
      seed (labelsOf material answers) := by
  intro position value hboundary
  rw [← GraphCorrectness.materialSurrogates_eq _ seed material
    (sample_agreement material seed answers table)] at hboundary
  have hinactive := PrunedGraph.boundary_inactive _ _ position value hboundary
  have hnot : position ∉ graphOrder (PrunedGraph.active (parameter material)) :=
    fun hmem => hinactive ((mem_graphOrder _ _).1 hmem)
  simp only [labelsOf, completedLabels, hnot, ↓reduceIte]
  exact PrunedGraph.initialLabels_boundary _ _ position value hboundary

theorem sample_parameter (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    evalWithAnswerFn (sampleFn material seed answers table)
      (derivePublicSeed seed : OracleComp HashSpec PublicParameter) = parameter material :=
  eval_parameter_prepared _ seed material (sample_agreement material seed answers table)

/-- Coordinates of one sample, read from its answer function. -/
noncomputable def sampleCoordinates (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) : HiddenGraph.Table :=
  HiddenGraph.coordinates
    (GraphCorrectness.otsSecrets (sampleFn material seed answers table) (parameter material) seed)
    (GraphCorrectness.ftsSecrets (sampleFn material seed answers table) (parameter material) seed)
    (labelsOf material answers)

omit [Params] in
theorem fixedHashWorld_countHashQueries (f : QueryImpl HashSpec Id) {α : Type}
    (oa : OracleComp OracleWorld α) :
    simulateQ (Prefix.fixedHashWorld f) (countHashQueries oa) =
      (simulateQ (Prefix.fixedWorldCost f) oa).run := by
  rw [countHashQueries, QueryCap.simulate_withCost, Prefix.fixedWorldCost]
  congr 3
  funext input
  cases input <;> rfl

end SphincsSecurity.Security.Assembly

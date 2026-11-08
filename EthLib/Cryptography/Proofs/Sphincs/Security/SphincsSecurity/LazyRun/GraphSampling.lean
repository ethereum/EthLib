module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.LazyRun.GraphRows
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Prelude

/-!
# Splitting the sampled outputs into coordinates

The secret outputs and the graph labels split into independent uniform parts.

Each hidden digest is the low part of a distinct sampled output.

The high bits and the unselected outputs stay as independent residual data.
-/

@[expose] public section

open OracleComp OracleSpec
namespace SphincsSecurity.Security.HiddenGraph

variable [Params]
open Graph SeedModel UniformTableSplit
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev SampleCell := SecretPosition ⊕ Position
abbrev JoinedOutputs := SampleCell → HashOutput

@[irreducible] noncomputable def sampleCellFintype : Fintype SampleCell := inferInstance
noncomputable local instance : Fintype SampleCell := sampleCellFintype
noncomputable local instance : DecidableEq SampleCell := Classical.decEq _

/-- The sampled full answer containing each hidden 128-bit coordinate. -/
def coordinateCell : Coordinate → SampleCell
  | .chain lay tree leaf chainIdx position =>
      if h : position.val = 0 then .inl (.inl (lay, tree, leaf, chainIdx))
      else .inr (.chain lay tree leaf chainIdx
        ⟨position.val - 1, by
          have := position.isLt; simp only [chainLength, winternitzBits] at *; omega⟩)
  | .fors index κ leaf position =>
      if position.val = 0 then .inl (.inr (.inl (index, κ, leaf))) else .inr (.fleaf index κ leaf)

def coordinateAtCell : SampleCell → Option Coordinate
  | .inl (.inl (lay, tree, leaf, chainIdx)) => some (.chain lay tree leaf chainIdx ⟨0, by decide⟩)
  | .inl (.inr (.inl (index, κ, leaf))) => some (.fors index κ leaf 0)
  | .inl (.inr (.inr _)) => none
  | .inr (.chain lay tree leaf chainIdx step) =>
      some (.chain lay tree leaf chainIdx ⟨step.val + 1, by have := step.isLt; omega⟩)
  | .inr (.fleaf index κ leaf) => some (.fors index κ leaf 1)
  | .inr _ => none

theorem coordinateAtCell_cell (coordinate : Coordinate) :
    coordinateAtCell (coordinateCell coordinate) = some coordinate := by
  cases coordinate with
  | chain lay tree leaf chainIdx position => fin_cases position <;> rfl
  | fors index κ leaf position => fin_cases position <;> rfl

theorem coordinateCell_injective : Function.Injective coordinateCell := by
  intro left right heq
  exact Option.some.inj (by simpa only [coordinateAtCell_cell] using congrArg coordinateAtCell heq)

theorem coordinateCell_outgoing (address : Address) :
    coordinateCell address.outputCoordinate = .inr address.position := by
  cases address with
  | chain lay tree leaf chainIdx step => fin_cases step <;> rfl
  | fleaf index κ leaf => rfl

abbrev CoordinateHighs := Coordinate → Prefix.High
abbrev RemainingOutputs := Outside coordinateCell → HashOutput

noncomputable def splitCoordinateRows :
    (Coordinate → HashOutput) ≃ Table × CoordinateHighs where
  toFun outputs := (fun coordinate => truncateHash (outputs coordinate),
    fun coordinate => (splitHashOutput digestBits (outputs coordinate)).2)
  invFun pair coordinate := Prefix.combine (pair.1 coordinate) (pair.2 coordinate)
  left_inv outputs := funext fun coordinate => Prefix.combine_split (outputs coordinate)
  right_inv pair := Prod.ext
    (funext fun coordinate => Prefix.truncate_combine (pair.1 coordinate) (pair.2 coordinate))
    (funext fun coordinate =>
      congrArg Prod.snd (Prefix.split_combine (pair.1 coordinate) (pair.2 coordinate)))

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType
noncomputable local instance : SampleableType CanonicalGraphLabels := graphLabelsSampleable
noncomputable local instance : SampleableType Table := SampleableType.ofFintype _
noncomputable local instance : SampleableType CoordinateHighs := SampleableType.ofFintype _
noncomputable local instance : SampleableType RemainingOutputs := SampleableType.ofFintype _
noncomputable local instance : SampleableType (Coordinate → HashOutput) :=
  SampleableType.ofFintype _
noncomputable local instance : SampleableType JoinedOutputs := SampleableType.ofFintype _

theorem uniform_coordinate_rows :
    ($ᵗ (Coordinate → HashOutput) : ProbComp _) =ᵈ
      (do
        let lows ← $ᵗ Table
        let highs ← $ᵗ CoordinateHighs
        pure (fun coordinate => Prefix.combine (lows coordinate) (highs coordinate)) :
          ProbComp _) := by
  have hcombine : Function.uncurry (fun (lows : Table) (highs : CoordinateHighs) coordinate =>
      Prefix.combine (lows coordinate) (highs coordinate)) = splitCoordinateRows.symm := by
    funext pair
    rfl
  exact uniform_pair_of_bijective (hcombine ▸ splitCoordinateRows.symm.bijective)

noncomputable def assemble (lows : Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) : JoinedOutputs :=
  join coordinateCell coordinateCell_injective
    (fun coordinate => Prefix.combine (lows coordinate) (highs coordinate)) remaining

theorem assemble_coordinate (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (coordinate : Coordinate) :
    assemble lows highs remaining (coordinateCell coordinate) =
      Prefix.combine (lows coordinate) (highs coordinate) :=
  join_embed coordinateCell coordinateCell_injective _ remaining coordinate

theorem assemble_remaining (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (cell : Outside coordinateCell) :
    assemble lows highs remaining cell.val = remaining cell :=
  join_outside coordinateCell coordinateCell_injective _ remaining cell

/-- A uniform joined table is equal in distribution to independent lows, highs and rest. -/
theorem uniform_joined_outputs :
    ($ᵗ JoinedOutputs : ProbComp _) =ᵈ
      (do
        let lows ← $ᵗ Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        pure (assemble lows highs remaining) : ProbComp _) := by
  refine (uniform_join coordinateCell coordinateCell_injective).trans ?_
  refine (EvalDistEq.bind_left uniform_coordinate_rows _).trans ?_
  simp only [bind_assoc, pure_bind]
  rfl

def joinedSecrets (outputs : JoinedOutputs) : SecretOutputs := outputs ∘ Sum.inl
def joinedLabels (outputs : JoinedOutputs) : CanonicalGraphLabels := outputs ∘ Sum.inr
def joinedPair (outputs : JoinedOutputs) : SecretOutputs × CanonicalGraphLabels :=
  (joinedSecrets outputs, joinedLabels outputs)

theorem joinedPair_bijective : Function.Bijective joinedPair :=
  (Equiv.sumArrowEquivProdArrow SecretPosition Position HashOutput).bijective

/-- Uniform secret outputs and graph labels are equal in distribution to an assembly of parts.

The parts are an independent coordinate table, high bits and remaining outputs. -/
theorem uniform_material_graph_outputs :
    (do
      let secrets ← $ᵗ SecretOutputs
      let labels ← $ᵗ CanonicalGraphLabels
      pure (secrets, labels) : ProbComp _) =ᵈ
      (do
        let lows ← $ᵗ Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        pure (joinedPair (assemble lows highs remaining)) : ProbComp _) := by
  have hpair := uniform_pair_of_bijective (Left := SecretOutputs) (Right := CanonicalGraphLabels)
    (Joined := JoinedOutputs)
    (combine := fun secrets labels =>
      (Equiv.sumArrowEquivProdArrow SecretPosition Position HashOutput).symm (secrets, labels))
    (Equiv.sumArrowEquivProdArrow SecretPosition Position HashOutput).symm.bijective
  have hleft := hpair.symm.map joinedPair
  have hright := uniform_joined_outputs.map joinedPair
  simp only [map_bind, map_pure] at hleft hright
  refine EvalDistEq.trans ?_ (hleft.trans hright)
  rfl

def otsFromOutputs (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) : Digest :=
  truncateHash (outputs (.inl (lay, tree, leaf, chainIdx)))

def ftsFromOutputs (outputs : SecretOutputs) : ForsSecrets := fun index κ leaf =>
  truncateHash (outputs (.inr (.inl (index, κ, leaf))))

theorem coordinates_joined (outputs : JoinedOutputs) (coordinate : Coordinate) :
    coordinates (otsFromOutputs (joinedSecrets outputs)) (ftsFromOutputs (joinedSecrets outputs))
      (joinedLabels outputs) coordinate = truncateHash (outputs (coordinateCell coordinate)) := by
  cases coordinate with
  | chain lay tree leaf chainIdx position => fin_cases position <;> rfl
  | fors index κ leaf position => fin_cases position <;> rfl

/-- The coordinates of an assembled output are its table of low parts. -/
theorem coordinates_assemble (lows : Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) :
    coordinates (otsFromOutputs (joinedSecrets (assemble lows highs remaining)))
      (ftsFromOutputs (joinedSecrets (assemble lows highs remaining)))
      (joinedLabels (assemble lows highs remaining)) = lows := by
  funext coordinate
  rw [coordinates_joined, assemble_coordinate, Prefix.truncate_combine]

theorem highHalves_assemble (lows : Table) (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (address : Address) :
    highHalves (joinedLabels (assemble lows highs remaining)) address =
      highs address.outputCoordinate := by
  simp only [highHalves, joinedLabels, Function.comp_def]
  rw [← coordinateCell_outgoing address, assemble_coordinate, Prefix.split_combine]

theorem completed_active_label (active : Position → Prop) (initial answers : CanonicalGraphLabels)
    (position : Position) (hactive : active position) :
    completedLabels (graphOrder active) initial answers position = answers position := by
  simp only [completedLabels, (mem_graphOrder active position).mpr hactive, ↓reduceIte]

theorem completed_row_high (active : Position → Prop) (initial answers : CanonicalGraphLabels)
    (address : Address) (hactive : active address.position) :
    highHalves (completedLabels (graphOrder active) initial answers) address =
      highHalves answers address := by
  unfold highHalves
  rw [completed_active_label _ _ _ _ hactive]

noncomputable def sampleSplitPair : ProbComp (SecretOutputs × CanonicalGraphLabels) := do
  let lows ← $ᵗ Table
  let highs ← $ᵗ CoordinateHighs
  (fun remaining => joinedPair (assemble lows highs remaining)) <$> ($ᵗ RemainingOutputs)

/-- Drawing secret outputs and then labels is equal in distribution to the split sampler. -/
theorem evalDist_sampleSplitPair :
    (($ᵗ SecretOutputs) >>= fun secrets =>
      (fun labels => (secrets, labels)) <$> ($ᵗ CanonicalGraphLabels)) =ᵈ sampleSplitPair := by
  simpa only [sampleSplitPair, map_eq_bind_pure_comp, Function.comp_def] using
    uniform_material_graph_outputs

/-- Drawing the material and then the labels is equal in distribution to the split sampler.

The output for the public parameter stays an independent draw outside the split. -/
theorem evalDist_sampleMaterial_graph :
    (sampleMaterial >>= fun material =>
      (fun labels => (material, labels)) <$> ($ᵗ CanonicalGraphLabels)) =ᵈ
      (($ᵗ HashOutput) >>= fun parameterOutput => ($ᵗ HashOutput) >>= fun prf =>
        (fun pair => (((parameterOutput, prf), pair.1), pair.2)) <$> sampleSplitPair) := by
  simp only [sampleMaterial, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  refine (FiniteGraphSampling.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun prf => ?_
  have h := EvalDistEq.map evalDist_sampleSplitPair
    (fun pair : SecretOutputs × CanonicalGraphLabels =>
      (((parameterOutput, prf), pair.1), pair.2))
  simpa only [map_bind, Functor.map_map, Function.comp_def] using h

/-- The split holds in distribution under every continuation of the material and the labels. -/
theorem evalDist_material_graph_continuation {α : Type}
    (next : Material → CanonicalGraphLabels → ProbComp α) :
    (sampleMaterial >>= fun material => ($ᵗ CanonicalGraphLabels) >>= next material) =ᵈ
      (($ᵗ HashOutput) >>= fun parameterOutput => ($ᵗ HashOutput) >>= fun prf =>
        sampleSplitPair >>= fun pair => next ((parameterOutput, prf), pair.1) pair.2) := by
  have h := evalDist_sampleMaterial_graph.bind_left fun pair => next pair.1 pair.2
  simpa only [bind_assoc, bind_map_left] using h

end SphincsSecurity.Security.HiddenGraph

module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LocalTree
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedResidual

/-!
# Structural signature schedules before the physical query cutoff

The leanXMSS draft in "The scheme" uses the tree root, chain values and authentication path.

Their normalized schedules consist only of graph-cell reads and touches.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

open Constants HashSig OracleComp OracleSpec LayerGraph.Hidden CanonicalGraph.PairedQueries
open RealClient.GraphPrefix (MixedWorld)

/-- Internal graph operations are forwarded directly.

A public half query reads one full word and projects its requested half. -/
noncomputable def structuralQuery : QueryImpl SharedSpec (OracleComp MixedWorld)
  | .inl (.inl (.inl n)) => query (spec := MixedWorld) (.inl (.inl n))
  | .inl (.inl (.inr (.inl b))) => (fun w => (PairedHashWord.halves w).1) <$>
      query (spec := MixedWorld) (.inl (.inr b))
  | .inl (.inl (.inr (.inr b))) => (fun w => (PairedHashWord.halves w).2) <$>
      query (spec := MixedWorld) (.inl (.inr b))
  | .inl (.inr x) => query (spec := MixedWorld) (.inr (.inl x))
  | .inr op => query (spec := MixedWorld) (.inr (.inr op))

/-- Emit the schedule into the caller language on which the physical cap runs. -/
noncomputable def emitStructure {α : Type}
    (p : OracleComp SharedSpec α) : OracleComp MixedWorld α :=
  simulateQ structuralQuery p

/-- Expansion recovers the original program and every emitted query has zero cost. -/
def StructuralSchedule {α : Type} (p : OracleComp SharedSpec α) : Prop :=
  simulateQ (expand PairedHashWord.halves) (emitStructure p) = p ∧
    (emitStructure p).AllQueriesSatisfy (fun t => mixedCost (H := ChainGraph.Word)
    (F := HashOutput) (fun _ => 0) t = 0)

private theorem pure_structural {α : Type} (a : α) : StructuralSchedule (pure a) := by
  change simulateQ _ (simulateQ structuralQuery (pure a)) = _ ∧ _
  simp [emitStructure]

private theorem bind_structural {α β : Type} {p : OracleComp SharedSpec α}
    {k : α → OracleComp SharedSpec β} (hp : StructuralSchedule p) (hk : ∀ a,
      StructuralSchedule (k a)) :
    StructuralSchedule (p >>= k) := by
  rcases hp with ⟨eq, free⟩
  simp only [StructuralSchedule, emitStructure, simulateQ_bind] at *
  exact ⟨by simp only [eq, fun a => (hk a).1], allQueriesSatisfy_bind free fun a => (hk a).2⟩

private theorem map_structural {α β : Type} {p : OracleComp SharedSpec α} (f : α → β)
    (hp : StructuralSchedule p) : StructuralSchedule (f <$> p) := by
  rw [← bind_pure_comp]
  exact bind_structural hp fun a => pure_structural (f a)

private theorem internal_structural (t : (Internal Start Row ChainGraph.Word).Domain) :
    StructuralSchedule (internalRead (L := HashInput) t) := by
  rcases t with x | op
  · exact ⟨rfl, (allQueriesSatisfy_query_iff _ _).2 rfl⟩
  · exact ⟨rfl, (allQueriesSatisfy_query_iff _ _).2 rfl⟩

private theorem touch_structural (pp : PublicParam) (l : Layer) (c : LayerGraph.Cell) :
    StructuralSchedule (simulateQ (selection pp l).liftQuery (touchCell (some c))) :=
  internal_structural (.inr (.inl (inLayer l c)))

private theorem read_structural (pp : PublicParam) (l : Layer) (c : LayerGraph.Cell) :
    StructuralSchedule (simulateQ (selection pp l).liftQuery (readCell (some c))) := by
  rcases c with x | k
  · exact internal_structural (.inl (l, x))
  · exact internal_structural (.inr (.inr ((selection pp l).node k)))

private theorem mark_structural (pp : PublicParam) (l : Layer) {p : OracleComp LayerGraph.Spec Unit}
    (marks : ∀ P : OracleComp LayerGraph.Spec Unit → Prop, P (pure ()) →
      (∀ a b, P a → P b → P (a >>= fun _ => b)) →
      (∀ c, P (touchCell (some c))) → P p) :
    StructuralSchedule (simulateQ (selection pp l).liftQuery p) := by
  apply marks
  · exact pure_structural ()
  · intro a b ha hb
    rw [simulateQ_bind]
    exact bind_structural ha fun _ => hb
  · exact touch_structural pp l

/-- All internal two-layer hash chain walks lift without spending a physical public query. -/
theorem beforeValues_structural (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) :
    StructuralSchedule (simulateQ (selection pp l).liftQuery (beforeValues pp l e x)) :=
  mark_structural pp l fun P ret seq touch => beforeValues_pred P ret seq touch pp l e x

private theorem collect_structural {α : Type} : ∀ n (f : Fin n → OracleComp SharedSpec α),
    (∀ i, StructuralSchedule (f i)) → StructuralSchedule (ofFnInOrder n f)
  | 0, _, _ => pure_structural _
  | n + 1, f, h => bind_structural (h 0) fun _ =>
    bind_structural (collect_structural n (fun i => f i.succ) (fun i => h i.succ)) fun _ =>
      pure_structural _

/-- Reading the chosen digits preserves the order of all 58 returned chain values. -/
theorem revealValues_structural (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) :
    StructuralSchedule (simulateQ (selection pp l).liftQuery (revealValues e x)) := by
  unfold revealValues
  rw [HashSig.ofFnInOrder_map_monad (fun {_} p => simulateQ (selection pp l).liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _)]
  apply collect_structural
  intro i
  rw [simulateQ_map]
  exact map_structural _ (read_structural pp l _)

/-- Building a subtree touches its children in order, reads its root, and touches the upper half. -/
theorem root_structural (pp : PublicParam) (l : Layer) (h j : Nat) :
    StructuralSchedule (simulateQ (selection pp l).liftQuery
      (beforeNode pp l h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j))) := by
  rw [simulateQ_bind]
  apply bind_structural (mark_structural pp l fun P ret seq touch => beforeNode_pred
    P ret seq touch pp l h j)
  intro _
  unfold LayerGraph.readOutput
  simp only [simulateQ_bind, simulateQ_pure]
  exact bind_structural (read_structural pp l _) fun _ =>
    bind_structural (touch_structural pp l _) fun _ => pure_structural _

/-- Each sibling of the top authentication path is built and released in the native order. -/
theorem path_structural (pp : PublicParam) (l : Layer)
    (e : Nat) : StructuralSchedule (pathSchedule pp l e) :=
  collect_structural _ _ fun _ => root_structural pp l _ _

/-- The bottom path is read from the stored tree only after successful top signing. -/
theorem bottomPath_structural (pp : PublicParam)
    (idx : LeafIndex) : StructuralSchedule (bottomPathSchedule pp idx) := by
  unfold bottomPathSchedule revealPath
  rw [HashSig.ofFnInOrder_map_monad (fun {_} p => simulateQ (selection pp .bottom).liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _)]
  apply collect_structural
  intro i
  rw [simulateQ_map]
  exact map_structural _ (read_structural pp .bottom _)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph.Honest

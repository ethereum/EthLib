module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedPublicRoot
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedVerifierCut

/-!
# The exact rows returned in a normalized signature

A released digest is the value of its own chain or sibling cell.

Every later request preserves that value.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec
  LayerGraph.Hidden
open ChainGraph (Word Public digestEquiv)

/-- Each returned digest has its stored word at the same index in the original vector. -/
@[expose] def Stored {n : Nat} (labels : Fin n → Cell) (v : Vector Digest n) (s : SharedState) :=
  ∀ i : Fin n, s.2 (labels i) = some (digestEquiv v[i])

theorem Stored.mono {n labels v s t} (h : Stored (n := n) labels v s) (grow : s ≤ t) :
    Stored labels v t := fun i => grow.2 (h i)

def sibling (l : Layer) (e : Nat) (k : Fin LAYER_HEIGHT) : Cell :=
  .inr (.inl (l,LayerGraph.treeRole k.val ((e / 2 ^ k.val) ^^^ 1)))

def chainAt (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V) (i : Fin V) : Cell :=
  inLayer l (LayerGraph.position e i x[i].val)

private theorem collected (pp : PublicParam) (n : Nat) (f : Fin n → OracleComp SharedSpec Digest)
    (labels : Fin n → Cell)
    (entry : ∀ i s a t, (a,t) ∈ support ((simulateQ (graph pp).deferredImpl (f i)).run s) →
      t.1.2 (labels i) = some (digestEquiv a))
    {s v t} (ran : (v,t) ∈ support ((simulateQ (graph pp).deferredImpl (ofFnInOrder n f)).run s)) :
    Stored labels v t.1 := by
  induction n generalizing s with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    simp only [ofFnInOrder, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at ran
    obtain ⟨⟨a,m⟩, head, ⟨vs,last⟩, tail, eq⟩ := ran
    cases eq
    have growth := (graph pp).le_of_mem_support_simulateQ_deferredImpl _ tail
    have rest := ih (fun i => f i.succ) (fun i => labels i.succ) (fun i => entry i.succ) tail
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using growth.2 (entry 0 s a m head)
    · simpa using rest j

private theorem read_one (pp : PublicParam) (l : Layer) (c : LayerGraph.Cell) {s a t}
    (ran : (a,t) ∈ support ((simulateQ (graph pp).deferredImpl
      (simulateQ (selection pp l).liftQuery (digestEquiv.symm <$> readCell (some c)))).run s)) :
    t.1.2 (inLayer l c) = some (digestEquiv a) := by
  have image : simulateQ (selection pp l).liftQuery (readCell (some c)) =
      (readCell (some (inLayer l c)) : OracleComp SharedSpec Word) := by cases c <;> rfl
  simp only [simulateQ_map, image, StateT.run_map, support_map] at ran
  obtain ⟨⟨w,m⟩, raw, eq⟩ := ran
  cases eq
  rw [Equiv.apply_symm_apply]
  exact (graph pp).cell_eq_of_mem_support_simulateQ_deferredImpl_readCell raw

/-- Reading the 58 selected WOTS+C values returns the words in their addressed low or start cells.
-/
theorem chain_rows (pp : PublicParam) (l : Layer) (e : UInt32) (x : Vector (Fin CHAIN_LENGTH) V)
    {s v t}
    (ran : (v,t) ∈ support ((simulateQ (graph pp).deferredImpl
      (simulateQ (selection pp l).liftQuery (revealValues e x))).run s)) :
    Stored (chainAt l e x) v t.1 := by
  rw [revealValues, ofFnInOrder_map_monad (simulateQ _) (simulateQ_pure _)
      (simulateQ_bind _)] at ran
  exact collected pp _ _ _ (fun _ _ _ _ h => read_one pp l _ h) ran

/-- The top path returns sixteen actual subtree root labels ordered from the leaf upwards. -/
theorem top_rows (pp : PublicParam) (e : Nat) {s v t}
    (ran : (v,t) ∈ support ((simulateQ (graph pp).deferredImpl (pathSchedule pp .top e)).run s)) :
    Stored (sibling .top e) v t.1 := by
  apply collected pp _ _ _ _ ran
  intro i before a after h
  obtain ⟨_, log⟩ := logged_of_run (pp := pp) h
  exact logged_root_value pp .top i.val ((e / 2 ^ i.val) ^^^ 1) log

/-- The bottom path is read from the same stored siblings, after the top finder succeeds. -/
theorem bottom_rows (pp : PublicParam) (idx : LeafIndex) {s v t}
    (ran : (v,t) ∈ support ((simulateQ (graph pp).deferredImpl
      (bottomPathSchedule pp idx)).run s)) :
    Stored (sibling .bottom idx.toNat) v t.1 := by
  rw [bottomPathSchedule, revealPath,
    ofFnInOrder_map_monad (simulateQ _) (simulateQ_pure _) (simulateQ_bind _)] at ran
  exact collected pp _ _ _ (fun _ _ _ _ h => read_one pp .bottom _ h) ran

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

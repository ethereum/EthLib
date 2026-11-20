module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphSchedule
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerHonest

/-!
# Disclosures from an honest subtree

The leanXMSS draft, section "The scheme", releases a root at key generation.

Both layers use the same hash oracle.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV

open Constants HashSig OracleComp Merkle Wots

namespace LayerGraph.Hidden

variable (P : OracleComp Spec Unit → Prop) (ret : P (pure ()))
  (seq : ∀ p q, P p → P q → P (p >>= fun _ => q))
  (touch : ∀ c : Cell, P (touchCell (some c)))

include ret seq in
private theorem visit_pred : ∀ n (f : Fin n → OracleComp Spec Unit),
    (∀ i, P (f i)) → P (visit n f)
  | 0, _, _ => ret
  | n + 1, f, each => seq _ _ (each 0)
      (visit_pred n (fun i => f i.succ) (fun i => each i.succ))

include ret seq touch in
private theorem chain_pred (pp : PublicParam) (l : Layer) (e : UInt32) (i : Fin V) :
    ∀ n (bound : 0 + n ≤ CHAIN_LENGTH - 1),
      P (Wots.chain (GraphChain.touchStep (schedule pp l e i)) 0 n bound ())
  | 0, _ => ret
  | n + 1, _ => seq _ _ (chain_pred pp l e i n (by omega)) (seq _ _ (touch _) (touch _))

include ret seq touch in
/-- A traversal needs only pure sequencing and touches, at every depth. -/
theorem beforeNode_pred (pp : PublicParam) (l : Layer) : ∀ h j, P (beforeNode pp l h j)
  | 0, j => seq _ _
      (visit_pred P ret seq _ (startPair (UInt32.ofNat j)) fun _ => seq _ _ (touch _) (touch _))
      (visit_pred P ret seq _ (chainEdges pp l (UInt32.ofNat j)) fun i =>
        chain_pred P ret seq touch pp l (UInt32.ofNat j) i _ _)
  | h + 1, j => seq _ _ (beforeNode_pred pp l h (2*j)) (seq _ _ (seq _ _ (touch _) (touch _))
      (seq _ _ (beforeNode_pred pp l h (2*j+1)) (seq _ _ (touch _) (touch _))))

include ret seq touch in
/-- A successful digit vector can be processed using touches before any of its values are read. -/
theorem beforeValues_pred (pp : PublicParam) (l : Layer) (e : UInt32)
    (x : Vector (Fin CHAIN_LENGTH) V) : P (beforeValues pp l e x) :=
  seq _ _ (visit_pred P ret seq _ (startPair e) fun _ => seq _ _ (touch _) (touch _))
    (visit_pred P ret seq _ _ fun i => chain_pred P ret seq touch pp l e i (x[i]).val _)

end LayerGraph.Hidden

namespace TwoLayerGraph.Honest
open LayerGraph.Hidden

/-- The shared eager evaluation of the actual node releases just its root digest.

The state includes both layers' labels and both halves of every ordinary public hash entry. -/
theorem node_schedule (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (h j : Nat) (bound : h ≤ LAYER_HEIGHT) :
    simulateQ (graph pp).eagerImpl (Xmss.node hash pp (prf pp l other) l h j) =
      simulateQ (graph pp).eagerImpl (simulateQ (selection pp l).liftQuery
        (beforeNode pp l h j >>= fun _ => LayerGraph.readOutput (LayerGraph.treeRole h j))) := by
  let v := selection pp l
  have actual := Xmss.node_map_monad (fun {_} p => simulateQ v.liftQuery p)
    (simulateQ_pure _) (simulateQ_bind _) LayerGraph.hash (LayerGraph.startPrf pp l other) pp l h j
  simp only [v, hash_image] at actual
  rw [show Xmss.node hash pp (prf pp l other) l h j = _ from actual.symm]
  ext s : 1
  apply v.run_eq_of_exact (node_selected pp l other h j bound).2
  · apply v.exact_bind (beforeNode_pred (fun p => v.Exact p) (v.exact_pure ())
      (fun _ _ hp hq => v.exact_bind hp fun _ => hq) v.exact_touchCell pp l h j)
    intro _
    exact v.exact_bind (v.exact_readCell _) fun _ => v.exact_bind (v.exact_touchCell _)
      fun _ => v.exact_pure _
  · exact fun t => congrArg (fun m => StateT.run m t) (LayerGraph.Hidden.node pp l other h j bound)

/-- Each sibling subtree touches its hidden rows and reads the one digest included in the path. -/
@[expose] noncomputable def pathSchedule (pp : PublicParam) (l : Layer) (e : Nat) :
    OracleComp SharedSpec (Vector Digest LAYER_HEIGHT) :=
  ofFnInOrder LAYER_HEIGHT fun k =>
    let j := (e / 2 ^ k.val) ^^^ 1
    simulateQ (selection pp l).liftQuery (beforeNode pp l k.val j >>=
      fun _ => LayerGraph.readOutput (LayerGraph.treeRole k.val j))

/-- The library's actual path releases its sixteen siblings in order and keeps the entire state. -/
theorem path_schedule (pp : PublicParam) (l : Layer) (other : SeedPrf (OracleComp LayerGraph.Spec))
    (e : Nat) :
    simulateQ (graph pp).eagerImpl (Xmss.path hash pp (prf pp l other) l e) =
      simulateQ (graph pp).eagerImpl (pathSchedule pp l e) := by
  unfold Xmss.path Merkle.path pathSchedule
  rw [LayerGraph.siblings_in_order]
  simp only [Nat.zero_add, ofFnInOrder_map_monad (fun {_} p => simulateQ (graph pp).eagerImpl p)
    (simulateQ_pure _) (simulateQ_bind _)]
  congr 1
  funext k
  exact node_schedule pp l other k.val _ (Nat.le_of_lt k.isLt)

end TwoLayerGraph.Honest
end EthLib.Cryptography.Xmss.Unforgeability.VCV

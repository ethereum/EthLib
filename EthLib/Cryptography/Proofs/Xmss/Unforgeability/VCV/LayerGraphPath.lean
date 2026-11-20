module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphLeaf

/-!
# Honest authentication paths in the layer graph

The leanXMSS draft, section "Trees", orders the siblings from the leaf to the root.
At height `k`, the sibling index is the leaf index divided by `2^k` with the low bit flipped.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

open Constants HashSig OracleComp

/-- Express the library's bottom-up sibling calls as one ordered vector computation. -/
private theorem siblings_in_order {m : Type → Type} [Monad m] {α : Type}
    (h : Merkle.Position → α → α → m α) (base : Nat → m α) (n level j : Nat) :
    Merkle.siblings h base ⟨level, j⟩ n = ofFnInOrder n fun k =>
      Merkle.node h base ⟨level + k.val, (j / 2 ^ k.val) ^^^ 1⟩ := by
  induction n generalizing level j with
  | zero => rfl
  | succ n ih =>
    rw [Merkle.siblings, ofFnInOrder, Merkle.Position.parent, ih]
    simp only [Merkle.Position.sibling, Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.pow_zero, Nat.div_one,
      Nat.div_div_eq_div_mul, Nat.pow_succ', Nat.add_assoc, Nat.add_comm 1]

/-- The returned sibling at each height is present in the final cache. -/
def PathRecorded (pp : PublicParam) (layer : Layer) (n e : Nat)
    (p : OracleComp Spec (Vector Digest n)) : Prop :=
  ∀ (st : State) (z : Vector Digest n × State),
    z ∈ support ((simulateQ (graph pp layer).eagerImpl p).run st) →
    ∀ k : Fin n, Recorded (treeRole k.val ((e / 2 ^ k.val) ^^^ 1)) z.1[k] z.2

private theorem siblings_recorded (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (n e : Nat) (bound : n ≤ LAYER_HEIGHT) :
    PathRecorded pp layer n e (Merkle.path (nodeHash hash pp layer)
      (leaves hash pp (startPrf pp layer other) layer) n e) := by
  intro st z run
  simp only [Merkle.path, siblings_in_order, Nat.zero_add] at run
  exact collect_recorded pp layer n
    (fun k => Xmss.node hash pp (startPrf pp layer other) layer k.val ((e / 2 ^ k.val) ^^^ 1))
    (fun k d s => Recorded (treeRole k.val ((e / 2 ^ k.val) ^^^ 1)) d s) st
    (fun _ _ _ _ ext old => ext.2 old)
    (fun k s _ => (node_settles pp layer other k.val _ ((Nat.le_of_lt k.isLt).trans bound)).2 s) run

/-- Every sibling returned by the actual honest path remains in its graph row at the end.
This includes the low digest from each earlier subtree after all later subtrees have run. -/
theorem path_recorded (pp : PublicParam) (layer : Layer) (other : SeedPrf (OracleComp Spec))
    (e : Nat) : PathRecorded pp layer LAYER_HEIGHT e
      (Xmss.path hash pp (startPrf pp layer other) layer e) :=
  siblings_recorded pp layer other LAYER_HEIGHT e le_rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.LayerGraph

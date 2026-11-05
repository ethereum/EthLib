module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.LabLeaf

/-!
# Proofs: Merkle trees in the eager game

A Merkle node is computed from the leaves below it, level by level.

Two Merkle computations are related when their leaves are related and their parent steps are.

- A node of one tree and the node of the other at the same position have one law.
- So do the siblings along a path.

In a tree of the hypertree, the lab tree runs each key's lab leaf and reads each parent's cell.

Its nodes, its root and its paths have the law of the honest ones.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability

open EthLib.Cryptography.Sphincs.Constants
open OracleSpec OracleComp

section Merkle

variable {ι : Type} {spec : OracleSpec ι} {σ : Type} {so : QueryImpl spec (StateT σ ProbComp)}
  {r : σ → σ → Prop} [IsPreorder σ r] {α : Type}
  {hash hash' : Nat → Nat → α → α → OracleComp spec α} {leaves leaves' : Nat → OracleComp spec α}
  (Inv : σ → Prop) (Valid : Nat → Nat → Prop) (Hd : Nat → Nat → α → σ → Prop)

/-- **Merkle nodes.**

Let the valid positions be closed under taking children.

Let each pair of leaves form a triple that keeps `Inv` and holds its output at its position.

Let each pair of parent steps, from children held at their positions, form such a triple.

Then the nodes at each valid position form such a triple, if holding survives every later step. -/
theorem node_eqDistTriple (hValid : ∀ level j, Valid (level + 1) j →
      Valid level (2 * j) ∧ Valid level (2 * j + 1))
    (hHd : ∀ level j y s s', r s s' → Hd level j y s → Hd level j y s')
    (hleaf : ∀ j, Valid 0 j →
      so.EqDistTriple r Inv (leaves j) (leaves' j) fun y s => Inv s ∧ Hd 0 j y s)
    (hhash : ∀ level j left right, Valid (level + 1) j →
      so.EqDistTriple r (fun s => Inv s ∧ Hd level (2 * j) left s ∧ Hd level (2 * j + 1) right s)
        (hash (level + 1) j left right) (hash' (level + 1) j left right)
        fun y s => Inv s ∧ Hd (level + 1) j y s) :
    ∀ level j, Valid level j →
      so.EqDistTriple r Inv (Merkle.node hash leaves level j) (Merkle.node hash' leaves' level j)
        fun y s => Inv s ∧ Hd level j y s
  | 0, j, hv => hleaf j hv
  | level + 1, j, hv => by
    obtain ⟨hl, hr⟩ := hValid level j hv
    simp only [Merkle.node]
    refine (node_eqDistTriple hValid hHd hleaf hhash level _ hl).bind fun left => ?_
    refine ((node_eqDistTriple hValid hHd hleaf hhash level _ hr).frame
      (hHd level (2 * j) left)).bind fun right => ?_
    exact (hhash level j left right hv).mono (fun _ h => ⟨h.1.1, h.2, h.1.2⟩) fun _ _ h => h

/-- **Merkle siblings.**

Under the same hypotheses, the siblings of `n` ancestors form a triple.

The sibling at height `i` above `(level, j)` is held at its position. -/
theorem siblings_eqDistTriple (hValid : ∀ level j, Valid (level + 1) j →
      Valid level (2 * j) ∧ Valid level (2 * j + 1))
    (hHd : ∀ level j y s s', r s s' → Hd level j y s → Hd level j y s')
    (hleaf : ∀ j, Valid 0 j →
      so.EqDistTriple r Inv (leaves j) (leaves' j) fun y s => Inv s ∧ Hd 0 j y s)
    (hhash : ∀ level j left right, Valid (level + 1) j →
      so.EqDistTriple r (fun s => Inv s ∧ Hd level (2 * j) left s ∧ Hd level (2 * j + 1) right s)
        (hash (level + 1) j left right) (hash' (level + 1) j left right)
        fun y s => Inv s ∧ Hd (level + 1) j y s) :
    ∀ n level j, (∀ i < n, Valid (level + i) (j / 2 ^ i ^^^ 1)) →
      so.EqDistTriple r Inv (Merkle.siblings hash leaves level j n)
        (Merkle.siblings hash' leaves' level j n)
        fun v s => Inv s ∧ ∀ i : Fin n, Hd (level + i) (j / 2 ^ i.val ^^^ 1) v[i] s
  | 0, _, _, _ => QueryImpl.EqDistTriple.pure _ fun _ h => ⟨h, fun i => i.elim0⟩
  | n + 1, level, j, hv => by
    simp only [Merkle.siblings]
    refine (node_eqDistTriple Inv Valid Hd hValid hHd hleaf hhash level _
      (by simpa using hv 0 (Nat.succ_pos n))).bind fun sib => ?_
    refine ((siblings_eqDistTriple hValid hHd hleaf hhash n (level + 1) (j / 2)
      fun i hi => ?_).frame (hHd level (j ^^^ 1) sib)).bind fun rest => ?_
    · have := hv (i + 1) (by omega)
      rwa [show level + 1 + i = level + (i + 1) by omega, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    refine QueryImpl.EqDistTriple.pure _ fun s ⟨⟨hI, hrest⟩, hsib⟩ => ⟨hI, fun i => ?_⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using hsib
    · have := hrest k
      simp only [Fin.val_succ]
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        show level + (k.val + 1) = level + 1 + k.val by omega]
      simpa using this

end Merkle

/-! ## The trees of the hypertree -/

/-- The cell of node `j` on `level` of a tree: a key's leaf on level 0, a tree node above. -/
def treeCell (layer : Layer) (tree : Fin (2 ^ 18)) : Nat → Nat → Cell
  | 0, j => .inr (.otsLeaf ⟨layer, tree, Fin.ofNat _ j⟩)
  | level + 1, j => .inr (.treeNode layer tree ⟨level % TOP_HEIGHT, Nat.mod_lt _ (by decide)⟩
      (Fin.ofNat _ j))

/-- The lab node of a tree: the lab leaves, and a read of each parent's cell. -/
noncomputable def labTreeNode (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18))
    (level j : Nat) : OracleComp LabWorld Digest :=
  Merkle.node (fun level j _ _ => readCell (some (treeCell layer tree level j)))
    (fun j => labOtsLeaf P ⟨layer, tree, Fin.ofNat _ j⟩) level j

/-- A position of a tree: a level up to the height, and an index on that level. -/
def TreePos (layer : Layer) (level j : Nat) : Prop :=
  level ≤ layer.height ∧ j < 2 ^ (layer.height - level)

/-- The children of a position of a tree are positions. -/
theorem TreePos.children {layer : Layer} {level j : Nat} (h : TreePos layer (level + 1) j) :
    TreePos layer level (2 * j) ∧ TreePos layer level (2 * j + 1) := by
  obtain ⟨hl, hj⟩ := h
  have e : 2 ^ (layer.height - level) = 2 * 2 ^ (layer.height - (level + 1)) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- A key's leaf, at a position of level 0. -/
theorem leaves_labTriple (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18)) (j : Nat)
    (hj : TreePos layer 0 j) :
    LabTriple P (fun _ => True) (leaves labH P labPrf layer tree.val j)
      (labOtsLeaf P ⟨layer, tree, Fin.ofNat _ j⟩)
      fun y st => True ∧ st.2 (treeCell layer tree 0 j) = some y := by
  have hj' : j < 2 ^ TOP_HEIGHT :=
    lt_of_lt_of_le hj.2 (Nat.pow_le_pow_right (by decide) (by have := layer.height_le; omega))
  have e : leaves labH P labPrf layer tree.val j =
      otsPublicLeaf labH P labPrf (GraphKey.toOtsKey ⟨layer, tree, Fin.ofNat _ j⟩) := by
    simp only [leaves, GraphKey.toOtsKey, Fin.val_ofNat, Nat.mod_eq_of_lt hj']
  rw [e]
  exact (otsPublicLeaf_labTriple P _).mono (fun _ h => h) fun _ _ h => ⟨trivial, h⟩

/-- A parent step of a tree, at a position above level 0, from children held in their cells. -/
theorem nodeHash_labTriple (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18))
    (level j : Nat) (left right : Digest) (h : TreePos layer (level + 1) j) :
    LabTriple P (fun st => True ∧ st.2 (treeCell layer tree level (2 * j)) = some left ∧
        st.2 (treeCell layer tree level (2 * j + 1)) = some right)
      (nodeHash labH P layer tree.val (level + 1) j left right)
      (readCell (some (treeCell layer tree (level + 1) j)))
      fun y st => True ∧ st.2 (treeCell layer tree (level + 1) j) = some y := by
  have hl : level < TOP_HEIGHT := by
    have := layer.height_le
    have := h.1
    omega
  have hj : j < 2 ^ TOP_HEIGHT :=
    lt_of_lt_of_le h.2 (Nat.pow_le_pow_right (by decide) (by have := layer.height_le; omega))
  have e : nodeHash labH P layer tree.val (level + 1) j left right =
      th labH P (Node.treeNode layer tree ⟨level, hl⟩ ⟨j, hj⟩).address
        (digestsBytes [left, right] ++ (Node.treeNode layer tree ⟨level, hl⟩ ⟨j, hj⟩).suffix) := by
    simp only [nodeHash, Node.address, Node.suffix, digestsBytes_pair, ByteArray.append_empty]
  have hc :
      treeCell layer tree (level + 1) j = .inr (.treeNode layer tree ⟨level, hl⟩ ⟨j, hj⟩) := by
    simp only [treeCell, Nat.mod_eq_of_lt hl, Fin.ofNat, Nat.mod_eq_of_lt hj]
  rw [e, hc]
  refine (th_labTriple P _ [left, right]).mono (fun st ⟨_, hL, hR⟩ => ?_) fun _ _ h => ⟨trivial, h⟩
  rcases level with _ | l
  · exact .cons hL (.cons hR .nil)
  · have hl' : (⟨l % TOP_HEIGHT, Nat.mod_lt _ (by decide)⟩ : Fin TOP_HEIGHT) = ⟨l, by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    simp only [treeCell] at hL hR
    rw [hl'] at hL hR
    simp only [Node.children, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact .cons hL (.cons hR .nil)

/-- **Tree nodes.**

The honest node at a position of a tree and its lab node have one law of output and state.

The node's cell then holds the result. -/
theorem node_labTriple (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18)) (level j : Nat)
    (h : TreePos layer level j) :
    LabTriple P (fun _ => True) (node labH P labPrf layer tree.val level j)
      (labTreeNode P layer tree level j)
      fun y st => True ∧ st.2 (treeCell layer tree level j) = some y :=
  node_eqDistTriple (so := (graph P).eagerImpl) (fun _ => True) (TreePos layer)
    (fun level j y (st : LabState) => st.2 (treeCell layer tree level j) = some y)
    (fun _ _ h => h.children)
    (fun _ _ _ _ _ (hle : (_ : LabState) ≤ _) h => hle.2 h) (leaves_labTriple P layer tree)
    (nodeHash_labTriple P layer tree) level j h

/-- **Tree roots.**

The honest root of a tree and its lab root have one law of the output and the final state. -/
theorem treeRoot_labTriple (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18)) :
    LabTriple P (fun _ => True) (treeRoot labH P labPrf layer tree.val)
      (labTreeNode P layer tree layer.height 0)
      fun y st => True ∧ st.2 (treeCell layer tree layer.height 0) = some y :=
  node_labTriple P layer tree layer.height 0 ⟨le_rfl, Nat.two_pow_pos _⟩

/-- The lab path of key `e` of a tree: the lab nodes of its siblings, from the leaf up. -/
noncomputable def labTreePath (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18)) (e : Nat) :
    OracleComp LabWorld (Vector Digest layer.height) :=
  Merkle.path (fun level j _ _ => readCell (some (treeCell layer tree level j)))
    (fun j => labOtsLeaf P ⟨layer, tree, Fin.ofNat _ j⟩) layer.height e

/-- **Tree paths.**

The honest path of a key of a tree and its lab path have one law of output and state.

The cell of each sibling then holds its value. -/
theorem path_labTriple (P : PublicParam) (layer : Layer) (tree : Fin (2 ^ 18)) (e : Nat)
    (he : e < 2 ^ layer.height) :
    LabTriple P (fun _ => True) (path labH P labPrf layer tree.val e) (labTreePath P layer tree e)
      fun v st => True ∧ ∀ i : Fin layer.height,
        st.2 (treeCell layer tree (0 + i) (e / 2 ^ i.val ^^^ 1)) = some v[i] :=
  siblings_eqDistTriple (so := (graph P).eagerImpl) (fun _ => True) (TreePos layer)
    (fun level j y (st : LabState) => st.2 (treeCell layer tree level j) = some y)
    (fun _ _ h => h.children)
    (fun _ _ _ _ _ (hle : (_ : LabState) ≤ _) h => hle.2 h) (leaves_labTriple P layer tree)
    (nodeHash_labTriple P layer tree) layer.height 0 e fun i hi => by
      refine ⟨by omega, Nat.xor_lt_two_pow ?_ (Nat.one_lt_two_pow (by omega))⟩
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      convert he using 2
      omega

end EthLib.Cryptography.Sphincs.Unforgeability

/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Reachability
public import HashSig.GXMSS.Hypertree.Coordinates

/-!
# EthLib coordinates in the reviewed generic hypertree

The concrete shape has two layers of height sixteen. Bottom source indices
remain global; top source indices are the numbers of the certified bottom trees.
-/

public section

namespace EthereumXMSSHypertree.ConcreteHypertree

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants

/-- The source's two-layer, height-sixteen, four-position, 58-chain shape. -/
@[expose, reducible] def shape : GXMSS.Hypertree.Shape := ⟨2, 16, 2, 58, by decide⟩

/-- The exact finite source epoch in the reviewed generic coordinate domain. -/
@[expose] def sourceEpoch (idx : LeafIndex) : GXMSS.Hypertree.Epoch shape := leafIndexEquiv idx

/-- The source layer tag of a complete generic component-tree coordinate. -/
@[expose] def sourceLayer (tree : GXMSS.Hypertree.TreePosition shape) : Layer :=
  layerEquiv.symm tree.1

/-- The source's global key index in one layer. -/
@[expose] def globalIndex (position : GXMSS.Hypertree.OTSPosition shape) : Nat :=
  position.1.2.val * 2 ^ 16 + position.2.val

/-- The exact source key word associated with a generic complete one-time-key coordinate. -/
@[expose] def sourceKey (position : GXMSS.Hypertree.OTSPosition shape) : UInt32 :=
  UInt32.ofNat (globalIndex position)

/-- A source tree's global node index at a local level and node. -/
@[expose] def nodeGlobalIndex (tree : GXMSS.Hypertree.TreePosition shape)
    (level localNode : Nat) : Nat :=
  tree.2.val * 2 ^ (16 - level) + localNode

/-- The generic layer tag is the source layer's exact number. -/
@[simp] theorem sourceLayer_toNat (tree : GXMSS.Hypertree.TreePosition shape) :
    (sourceLayer tree).toNat = tree.1.val := by
  exact congrArg Fin.val (layerEquiv.apply_symm_apply tree.1)

/-- Each generic component has at most 65,536 possible tree numbers. -/
theorem treeIndex_lt (tree : GXMSS.Hypertree.TreePosition shape) : tree.2.val < 2 ^ 16 := by
  have ht := tree.2.isLt
  simp only [GXMSS.Hypertree.TreeIndex, GXMSS.Hypertree.Shape.branching, shape] at ht
  have hp : 2 - 1 - tree.1.val ≤ 1 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2 ^ 16) hp
  exact Nat.lt_of_lt_of_le ht (by simpa using hpow)

/-- The top component tree has index zero. -/
theorem top_treeIndex_eq_zero (tree : GXMSS.Hypertree.TreePosition shape) (h : tree.1.val = 1) :
    tree.2.val = 0 := by
  have ht := tree.2.isLt
  simp only [GXMSS.Hypertree.TreeIndex, GXMSS.Hypertree.Shape.branching, shape, h] at ht
  omega

/-- Every generic complete key index lies in the source's exact layer-dependent domain. -/
theorem globalIndex_lt (position : GXMSS.Hypertree.OTSPosition shape) :
    globalIndex position < 2 ^ Reachability.layerBits (sourceLayer position.1) := by
  have ht := treeIndex_lt position.1
  have he := position.2.isLt
  have hl := position.1.1.isLt
  have hs := sourceLayer_toNat position.1
  cases hsource : sourceLayer position.1 with
  | bottom =>
    simp only [globalIndex, Reachability.layerBits, GXMSS.Hypertree.Shape.branching, shape] at *
    omega
  | top =>
    have htop : position.1.1.val = 1 := by simpa only [hsource, Layer.toNat] using hs.symm
    have hz := top_treeIndex_eq_zero position.1 htop
    simp only [globalIndex, hz, Nat.zero_mul, Nat.zero_add, Reachability.layerBits]
    exact he

/-- The complete generic key has the source's exact finite key coordinate. -/
@[expose] def sourceKeyCoordinate (position : GXMSS.Hypertree.OTSPosition shape) :
    Reachability.KeyCoordinate (sourceLayer position.1) :=
  ⟨globalIndex position, globalIndex_lt position⟩

/-- The source key word conversion does not wrap. -/
@[simp] theorem sourceKey_toNat (position : GXMSS.Hypertree.OTSPosition shape) :
    (sourceKey position).toNat = globalIndex position :=
  Reachability.keyCoordinate_no_wrap (sourceKeyCoordinate position)

/-- Global key decomposition preserves the original component tree number. -/
theorem globalIndex_div (position : GXMSS.Hypertree.OTSPosition shape) :
    globalIndex position / 2 ^ 16 = position.1.2.val := by
  have he := position.2.isLt
  simp only [GXMSS.Hypertree.Shape.branching, shape] at he
  unfold globalIndex
  omega

/-- Global key decomposition preserves the original local leaf number. -/
theorem globalIndex_mod (position : GXMSS.Hypertree.OTSPosition shape) :
    globalIndex position % 2 ^ 16 = position.2.val := by
  have he := position.2.isLt
  simp only [GXMSS.Hypertree.Shape.branching, shape] at he
  unfold globalIndex
  omega

/-- Layer and global source key uniquely recover a complete generic OTS coordinate. -/
theorem sourceKey_injective {first second : GXMSS.Hypertree.OTSPosition shape}
    (hl : sourceLayer first.1 = sourceLayer second.1) (he : sourceKey first = sourceKey second) :
    first = second := by
  have hg : globalIndex first = globalIndex second := by
    simpa only [sourceKey_toNat] using congrArg UInt32.toNat he
  have ht : first.1.1 = second.1.1 := layerEquiv.symm.injective hl
  have hi : first.1.2.val = second.1.2.val := by
    rw [← globalIndex_div, ← globalIndex_div, hg]
  have hf : first.2.val = second.2.val := by
    rw [← globalIndex_mod, ← globalIndex_mod, hg]
  exact Prod.ext (GXMSS.Hypertree.treePosition_ext ht hi) (Fin.ext hf)

/-- Bottom epoch selection preserves the source's entire global key index. -/
theorem positionAt_bottom_globalIndex (idx : LeafIndex) :
    globalIndex (GXMSS.Hypertree.positionAt shape (sourceEpoch idx) 0) = idx.toNat := by
  exact GXMSS.Hypertree.positionAt_bottom_recompose shape (sourceEpoch idx)

/-- Bottom epoch selection preserves the source's bottom tree number. -/
theorem positionAt_bottom_tree (idx : LeafIndex) :
    (GXMSS.Hypertree.positionAt shape (sourceEpoch idx) 0).1.2.val = bottomTree idx := rfl

/-- Bottom epoch selection preserves the source's local bottom leaf. -/
theorem positionAt_bottom_leaf (idx : LeafIndex) :
    (GXMSS.Hypertree.positionAt shape (sourceEpoch idx) 0).2.val = localLeaf idx := by
  simp [GXMSS.Hypertree.positionAt, sourceEpoch, shape,
    GXMSS.Hypertree.Shape.branching, localLeaf, LAYER_HEIGHT]

/-- Top epoch selection preserves the source's original bottom-tree signing key. -/
theorem positionAt_top_globalIndex (idx : LeafIndex) :
    globalIndex (GXMSS.Hypertree.positionAt shape (sourceEpoch idx) 1) = bottomTree idx := by
  exact GXMSS.Hypertree.positionAt_recompose shape (sourceEpoch idx) 1

/-- Every bottom component's parent is the source top key with that bottom tree number. -/
theorem parent_globalIndex (tree : GXMSS.Hypertree.TreePosition shape)
    (h : tree.1.val + 1 < shape.d) :
    globalIndex (GXMSS.Hypertree.parent shape tree h) = tree.2.val :=
  GXMSS.Hypertree.parent_recompose shape tree h

/-- A reached local component node stays inside the source's global layer-level domain. -/
theorem nodeGlobalIndex_bound (tree : GXMSS.Hypertree.TreePosition shape)
    (level localNode : Nat) (hl : level ≤ 16) (hn : localNode < 2 ^ (16 - level)) :
    NodeBound (Reachability.layerBits (sourceLayer tree)) level
      (nodeGlobalIndex tree level localNode) := by
  have ht := treeIndex_lt tree
  have hs := sourceLayer_toNat tree
  cases hsource : sourceLayer tree with
  | bottom =>
    have hbound : nodeGlobalIndex tree level localNode < 2 ^ 16 * 2 ^ (16 - level) := by
      calc
        _ < (tree.2.val + 1) * 2 ^ (16 - level) := by
          unfold nodeGlobalIndex
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left hn _
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have hexp : 16 + (16 - level) = 32 - level := by omega
    simpa only [NodeBound, Reachability.layerBits, ← Nat.pow_add, hexp] using hbound
  | top =>
    have htop : tree.1.val = 1 := by simpa only [hsource, Layer.toNat] using hs.symm
    have hz := top_treeIndex_eq_zero tree htop
    simpa only [NodeBound, Reachability.layerBits, nodeGlobalIndex, hz,
      Nat.zero_mul, Nat.zero_add] using hn

/-- Reached component node indices survive the source word conversion without wrapping. -/
theorem nodeGlobalIndex_no_wrap (tree : GXMSS.Hypertree.TreePosition shape)
    (level localNode : Nat) (hl : level ≤ 16) (hn : localNode < 2 ^ (16 - level)) :
    (UInt32.ofNat (nodeGlobalIndex tree level localNode)).toNat =
      nodeGlobalIndex tree level localNode :=
  nodeIndex_no_wrap (Reachability.layerBits_bounds (sourceLayer tree)).2
    (nodeGlobalIndex_bound tree level localNode hl hn)

/-- Local source leaf coordinates and level-zero global node coordinates coincide. -/
theorem nodeGlobalIndex_zero (tree : GXMSS.Hypertree.TreePosition shape)
    (leaf : Fin (2 ^ 16)) : nodeGlobalIndex tree 0 leaf.val = globalIndex (tree, leaf) := rfl

/-- A source global leaf's ancestor is the component's offset plus the local ancestor. -/
theorem globalIndex_ancestor (tree : GXMSS.Hypertree.TreePosition shape)
    (leaf : Fin (2 ^ 16)) (level : Nat) (hl : level ≤ 16) :
    globalIndex (tree, leaf) / 2 ^ level = nodeGlobalIndex tree level (leaf.val / 2 ^ level) := by
  have hpow : 2 ^ 16 = 2 ^ (16 - level) * 2 ^ level := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hl]
  unfold globalIndex nodeGlobalIndex
  conv_lhs => enter [1, 1, 2]; rw [hpow]
  rw [← Nat.mul_assoc]
  simpa only [Nat.add_comm, Nat.mul_comm] using
    Nat.add_mul_div_left leaf.val (tree.2.val * 2 ^ (16 - level)) (Nat.two_pow_pos level)

/-- Source left/right child indices agree with local component recursion. -/
theorem nodeGlobalIndex_children (tree : GXMSS.Hypertree.TreePosition shape)
    (level node : Nat) (hl : level < 16) :
    nodeGlobalIndex tree level (2 * node) = 2 * nodeGlobalIndex tree (level + 1) node ∧
      nodeGlobalIndex tree level (2 * node + 1) =
        2 * nodeGlobalIndex tree (level + 1) node + 1 := by
  have hp : 16 - level = (16 - (level + 1)) + 1 := by omega
  simp only [nodeGlobalIndex, hp, Nat.pow_succ]
  constructor <;> ring

end EthereumXMSSHypertree.ConcreteHypertree

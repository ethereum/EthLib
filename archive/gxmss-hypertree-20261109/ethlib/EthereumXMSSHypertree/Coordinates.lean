/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trail of Bits
-/

module
public import EthLib.Cryptography.Xmss.Verify
public import Mathlib.Logic.Equiv.Basic

/-!
# Source coordinates for the two-layer leanXMSS hypertree

The source uses global bottom-layer indices and a 32-bit embedded signature index.
The coordinate equivalences retain those indices exactly. The bounds below justify
the source's conversions to machine words on the reached tree coordinates.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- The source's complete lifetime, with its original numeric index. -/
abbrev Epoch := Fin (2 ^ 32)

/-- A position inside one source layer's tree, or a bottom tree number. -/
abbrev TreePosition := Fin (2 ^ LAYER_HEIGHT)

/-- The source leaf index and its exact finite domain. -/
@[expose] def leafIndexEquiv : LeafIndex ≃ Epoch where
  toFun idx := ⟨idx.toNat, idx.toNat_lt⟩
  invFun e := UInt32.ofNat e.val
  left_inv idx := UInt32.ofNat_toNat
  right_inv e := by
    apply Fin.ext
    exact UInt32.toNat_ofNat_of_lt' e.isLt

/-- The finite epoch keeps the source index's numerical value. -/
@[simp] theorem leafIndexEquiv_val (idx : LeafIndex) :
    (leafIndexEquiv idx).val = idx.toNat := rfl

/-- Returning from a finite epoch does not wrap modulo the word size. -/
@[simp] theorem leafIndexEquiv_symm_toNat (e : Epoch) :
    (leafIndexEquiv.symm e).toNat = e.val :=
  UInt32.toNat_ofNat_of_lt' e.isLt

/-- Epoch equality is exact numerical equality with the embedded source index. -/
theorem leafIndexEquiv_eq_iff (idx : LeafIndex) (e : Epoch) :
    leafIndexEquiv idx = e ↔ idx.toNat = e.val := Fin.ext_iff

/-- The source layer tags, retaining bottom as zero and top as one. -/
@[expose] def layerEquiv : Layer ≃ Fin 2 where
  toFun l := ⟨l.toNat, by cases l <;> decide⟩
  invFun l := if l.val = 0 then .bottom else .top
  left_inv l := by cases l <;> rfl
  right_inv l := by
    apply Fin.ext
    have hl := l.isLt
    change (if l.val = 0 then Layer.bottom else Layer.top).toNat = l.val
    by_cases h : l.val = 0
    · simp [h, Layer.toNat]
    · have h1 : l.val = 1 := by omega
      simp [h1, Layer.toNat]

/-- The layer equivalence preserves the source's address layer number. -/
@[simp] theorem layerEquiv_val (l : Layer) : (layerEquiv l).val = l.toNat := rfl

/-- The local leaf inside the bottom tree. -/
@[expose] def localLeaf (idx : LeafIndex) : Nat :=
  idx.toNat % 2 ^ LAYER_HEIGHT

/-- Every source bottom tree number fits in one tree position. -/
theorem bottomTree_lt (idx : LeafIndex) : bottomTree idx < 2 ^ LAYER_HEIGHT := by
  have h := idx.toNat_lt
  simp only [bottomTree, LAYER_HEIGHT] at *
  omega

/-- Every local bottom leaf fits in one tree position. -/
theorem localLeaf_lt (idx : LeafIndex) : localLeaf idx < 2 ^ LAYER_HEIGHT :=
  Nat.mod_lt _ (by decide)

/-- The bottom tree number followed by the local leaf reconstructs the source index. -/
theorem bottomTree_localLeaf_reconstruct (idx : LeafIndex) :
    bottomTree idx * 2 ^ LAYER_HEIGHT + localLeaf idx = idx.toNat := by
  simpa only [bottomTree, localLeaf, Nat.mul_comm] using
    Nat.div_add_mod idx.toNat (2 ^ LAYER_HEIGHT)

/-- Exact decomposition of the embedded index into bottom tree and local leaf. -/
@[expose] def treePositionEquiv : LeafIndex ≃ TreePosition × TreePosition where
  toFun idx := (⟨bottomTree idx, bottomTree_lt idx⟩, ⟨localLeaf idx, localLeaf_lt idx⟩)
  invFun p := UInt32.ofNat (p.1.val * 2 ^ LAYER_HEIGHT + p.2.val)
  left_inv idx := by
    change UInt32.ofNat (bottomTree idx * 2 ^ LAYER_HEIGHT + localLeaf idx) = idx
    rw [bottomTree_localLeaf_reconstruct]
    exact UInt32.ofNat_toNat
  right_inv p := by
    have ht := p.1.isLt
    have hl := p.2.isLt
    have hn : p.1.val * 2 ^ LAYER_HEIGHT + p.2.val < UInt32.size := by
      simp only [LAYER_HEIGHT, UInt32.size] at *
      omega
    apply Prod.ext
    · apply Fin.ext
      simp only [bottomTree, UInt32.toNat_ofNat_of_lt' hn]
      simp only [LAYER_HEIGHT] at *
      omega
    · apply Fin.ext
      simp only [localLeaf, UInt32.toNat_ofNat_of_lt' hn]
      simp only [LAYER_HEIGHT] at *
      omega

/-- The decomposition's first coordinate is the source's global bottom tree number. -/
@[simp] theorem treePositionEquiv_tree (idx : LeafIndex) :
    (treePositionEquiv idx).1.val = bottomTree idx := rfl

/-- The decomposition's second coordinate is the original local leaf. -/
@[simp] theorem treePositionEquiv_leaf (idx : LeafIndex) :
    (treePositionEquiv idx).2.val = localLeaf idx := rfl

/-- Recombining the coordinates recovers their concatenated numerical value. -/
@[simp] theorem treePositionEquiv_symm_toNat (p : TreePosition × TreePosition) :
    (treePositionEquiv.symm p).toNat = p.1.val * 2 ^ LAYER_HEIGHT + p.2.val := by
  apply UInt32.toNat_ofNat_of_lt'
  have ht := p.1.isLt
  have hl := p.2.isLt
  simp only [LAYER_HEIGHT, UInt32.size] at *
  omega

/-- A source finite node index at level `level` of a layer with `bits` leaf bits. -/
@[expose] def NodeBound (bits level j : Nat) : Prop := j < 2 ^ (bits - level)

/-- Every ancestor of a bounded source leaf is bounded at its own level. -/
theorem ancestor_bound {bits e level : Nat} (he : e < 2 ^ bits) (hl : level ≤ bits) :
    NodeBound bits level (e / 2 ^ level) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).mpr
  simpa only [NodeBound, ← Nat.pow_add, Nat.sub_add_cancel hl] using he

/-- Sibling selection preserves the index bound below the root. -/
theorem sibling_bound {bits level j : Nat} (hj : NodeBound bits level j)
    (hl : level < bits) : NodeBound bits level (j ^^^ 1) := by
  apply Nat.xor_lt_two_pow hj
  have hp : 0 < bits - level := by omega
  exact Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt hp)

/-- Each child of a bounded non-leaf source node is bounded at the lower level. -/
theorem children_bound {bits level j : Nat} (hl : level < bits)
    (hj : NodeBound bits (level + 1) j) :
    NodeBound bits level (2 * j) ∧ NodeBound bits level (2 * j + 1) := by
  have hp : bits - level = bits - (level + 1) + 1 := by omega
  unfold NodeBound at *
  rw [hp, Nat.pow_succ]
  omega

/-- Source node-address conversion is exact for every bounded reached coordinate. -/
theorem nodeIndex_no_wrap {bits level j : Nat} (hb : bits ≤ 32)
    (hj : NodeBound bits level j) : (UInt32.ofNat j).toNat = j := by
  apply UInt32.toNat_ofNat_of_lt'
  apply Nat.lt_of_lt_of_le hj
  change 2 ^ (bits - level) ≤ 2 ^ 32
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Every source tree level from zero through sixteen is preserved by `Fin.ofNat`. -/
theorem nodeLevel_no_wrap (level : Nat) (hl : level ≤ LAYER_HEIGHT) :
    (Fin.ofNat (LAYER_HEIGHT + 1) level).val = level := by
  simp [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : level < LAYER_HEIGHT + 1)]

/-- Bottom ancestors stay in the global source coordinate domain. -/
theorem bottom_ancestor_bound (idx : LeafIndex) (level : Nat) (hl : level ≤ 32) :
    NodeBound 32 level (idx.toNat / 2 ^ level) :=
  ancestor_bound idx.toNat_lt hl

/-- Bottom authentication siblings stay in the global source coordinate domain. -/
theorem bottom_sibling_bound (idx : LeafIndex) (level : Nat) (hl : level < LAYER_HEIGHT) :
    NodeBound 32 level ((idx.toNat / 2 ^ level) ^^^ 1) := by
  have hlevel : level < 32 := by simpa only [LAYER_HEIGHT] using Nat.lt_trans hl (by decide)
  exact sibling_bound (bottom_ancestor_bound idx level (Nat.le_of_lt hlevel)) hlevel

/-- Top ancestors retain the bottom tree number as their starting source index. -/
theorem top_ancestor_bound (idx : LeafIndex) (level : Nat) (hl : level ≤ LAYER_HEIGHT) :
    NodeBound LAYER_HEIGHT level (bottomTree idx / 2 ^ level) :=
  ancestor_bound (bottomTree_lt idx) hl

/-- Top authentication siblings remain inside the single top tree. -/
theorem top_sibling_bound (idx : LeafIndex) (level : Nat) (hl : level < LAYER_HEIGHT) :
    NodeBound LAYER_HEIGHT level ((bottomTree idx / 2 ^ level) ^^^ 1) :=
  sibling_bound (top_ancestor_bound idx level (Nat.le_of_lt hl)) hl

/-- Converting a bottom ancestor index into a source address word does not wrap. -/
theorem bottom_ancestor_no_wrap (idx : LeafIndex) (level : Nat) (hl : level ≤ 32) :
    (UInt32.ofNat (idx.toNat / 2 ^ level)).toNat = idx.toNat / 2 ^ level :=
  nodeIndex_no_wrap (by decide) (bottom_ancestor_bound idx level hl)

/-- Converting a bottom sibling index into a source address word does not wrap. -/
theorem bottom_sibling_no_wrap (idx : LeafIndex) (level : Nat) (hl : level < LAYER_HEIGHT) :
    (UInt32.ofNat ((idx.toNat / 2 ^ level) ^^^ 1)).toNat =
      (idx.toNat / 2 ^ level) ^^^ 1 :=
  nodeIndex_no_wrap (by decide) (bottom_sibling_bound idx level hl)

/-- Converting a top ancestor index into a source address word does not wrap. -/
theorem top_ancestor_no_wrap (idx : LeafIndex) (level : Nat) (hl : level ≤ LAYER_HEIGHT) :
    (UInt32.ofNat (bottomTree idx / 2 ^ level)).toNat = bottomTree idx / 2 ^ level :=
  nodeIndex_no_wrap (by decide) (top_ancestor_bound idx level hl)

/-- Converting a top sibling index into a source address word does not wrap. -/
theorem top_sibling_no_wrap (idx : LeafIndex) (level : Nat) (hl : level < LAYER_HEIGHT) :
    (UInt32.ofNat ((bottomTree idx / 2 ^ level) ^^^ 1)).toNat =
      (bottomTree idx / 2 ^ level) ^^^ 1 :=
  nodeIndex_no_wrap (by decide) (top_sibling_bound idx level hl)

/-- Bottom verification's leaf index reaches the root of its original bottom tree. -/
theorem bottom_root_index (idx : LeafIndex) :
    idx.toNat / 2 ^ LAYER_HEIGHT = bottomTree idx := rfl

/-- Top verification's index reaches the unique top root. -/
theorem top_root_index (idx : LeafIndex) :
    bottomTree idx / 2 ^ LAYER_HEIGHT = 0 :=
  Nat.div_eq_of_lt (bottomTree_lt idx)

end EthereumXMSSHypertree

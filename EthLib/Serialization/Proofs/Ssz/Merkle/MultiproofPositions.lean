module

public import EthLib.Serialization.Proofs.Ssz.Merkle.Gindex
public import EthLib.Cryptography.Proofs.Merkle.Multiproof

/-!
Generalized indices and positions in a Merkle tree of a fixed height.

The index of a node at depth `d` with offset `i` in its level is `2^d + i`.

The two namings agree on parents, siblings, children and ancestors.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

open Cryptography.Merkle

/-- The depth of `2^e + i` is `e`, for `i < 2^e`. -/
theorem log2_two_pow_add {e i : Nat} (lt : i < 2 ^ e) : Nat.log2 (2 ^ e + i) = e :=
  (Nat.log2_eq_iff (by have := Nat.two_pow_pos e; omega)).mpr
    ⟨by omega, by rw [Nat.pow_succ]; omega⟩

/-- An index is at least `2^d` and below `2^(d + 1)`, for its depth `d`. -/
theorem gindex_bounds {g : Nat} (named : 1 ≤ g) :
    2 ^ Nat.log2 g ≤ g ∧ g < 2 * 2 ^ Nat.log2 g := by
  have := Nat.lt_log2_self (n := g)
  rw [Nat.pow_succ] at this
  exact ⟨Nat.log2_self_le (by omega), by omega⟩

/-- A node of the tree of height `H` lies below its root. -/
abbrev InTree (H : Nat) (p : Position) : Prop :=
  (⟨H, 0⟩ : Position).IsAncestor p

/-- A node lies in the tree exactly when its level is at most `H` and its index is in range. -/
theorem inTree_iff {H : Nat} {p : Position} :
    InTree H p ↔ p.level ≤ H ∧ p.index < 2 ^ (H - p.level) := by
  rw [InTree, Position.isAncestor_iff]
  -- The index is below `2^(H - level)` exactly when it halves to 0 on the way up.
  dsimp only
  rw [eq_comm (a := 0), Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]

/-- The position of an index at depth at most `H` lies in the tree of height `H`. -/
theorem gindexPosition_inTree {H g : Nat} (named : 1 ≤ g) (deep : Nat.log2 g ≤ H) :
    InTree H (gindexPosition H g) := by
  have := gindex_bounds named
  refine inTree_iff.mpr ⟨by simp [gindexPosition], ?_⟩
  simp only [gindexPosition, show H - (H - Nat.log2 g) = Nat.log2 g by omega]
  omega

/-- The index of the position of an index is the index. -/
theorem positionGindex_gindexPosition {H g : Nat} (named : 1 ≤ g) (deep : Nat.log2 g ≤ H) :
    positionGindex H (gindexPosition H g) = g := by
  have := gindex_bounds named
  simp only [positionGindex, gindexPosition, show H - (H - Nat.log2 g) = Nat.log2 g by omega]
  omega

/-- The index of a node of the tree is at least 1, at the depth `H - level`. -/
theorem positionGindex_bounds {H : Nat} {p : Position} (inside : InTree H p) :
    1 ≤ positionGindex H p ∧ Nat.log2 (positionGindex H p) = H - p.level := by
  have range := (inTree_iff.mp inside).2
  exact ⟨by have := Nat.two_pow_pos (H - p.level); simp only [positionGindex]; omega,
    log2_two_pow_add range⟩

/-- The position of the index of a node of the tree is the node. -/
theorem gindexPosition_positionGindex {H : Nat} {p : Position} (inside : InTree H p) :
    gindexPosition H (positionGindex H p) = p := by
  obtain ⟨low, range⟩ := inTree_iff.mp inside
  have depth := log2_two_pow_add range
  simp only [gindexPosition, positionGindex] at depth ⊢
  rw [depth]
  exact Position.ext (by dsimp only; omega) (by dsimp only; omega)

/-- Two nodes of the tree with one index are the same node. -/
theorem positionGindex_injective {H : Nat} {p q : Position} (pInside : InTree H p)
    (qInside : InTree H q) (same : positionGindex H p = positionGindex H q) : p = q := by
  rw [← gindexPosition_positionGindex pInside, same, gindexPosition_positionGindex qInside]

/-- An ancestor of a node of the tree, at most at the root, is in the tree. -/
theorem inTree_ancestor {H : Nat} {p : Position} (inside : InTree H p) {k : Nat}
    (top : p.level + k ≤ H) : InTree H (p.ancestor k) := by
  obtain ⟨-, range⟩ := inTree_iff.mp inside
  refine inTree_iff.mpr ⟨by simpa using top, ?_⟩
  -- Halving `k` times takes an index below `2^(H - level)` below `2^(H - level - k)`.
  simp only [Position.ancestor_level, Position.ancestor_index]
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
    show H - (p.level + k) + k = H - p.level by omega]
  exact range

/-- The index of the ancestor `k` levels up is the index shifted right by `k`. -/
theorem positionGindex_ancestor {H : Nat} {p : Position} (inside : InTree H p) {k : Nat}
    (top : p.level + k ≤ H) : positionGindex H (p.ancestor k) = positionGindex H p >>> k := by
  obtain ⟨-, range⟩ := inTree_iff.mp inside
  simp only [positionGindex, Position.ancestor_level, Position.ancestor_index,
    Nat.shiftRight_eq_div_pow]
  -- The leading `2^(H - level)` splits into `2^k` times `2^(H - level - k)`.
  rw [show 2 ^ (H - p.level) = 2 ^ k * 2 ^ (H - (p.level + k)) by
    rw [← Nat.pow_add]; congr 1; omega, Nat.mul_add_div (Nat.two_pow_pos _), Nat.add_comm]

/-- The sibling of a node of the tree below its root is in the tree. -/
theorem inTree_sibling {H : Nat} {p : Position} (inside : InTree H p) (low : p.level < H) :
    InTree H p.sibling := by
  obtain ⟨-, range⟩ := inTree_iff.mp inside
  refine inTree_iff.mpr ⟨by simp; omega, ?_⟩
  -- The bound `2^(H - level)` is even, so flipping the low bit stays below it.
  have bound : 2 ^ (H - p.level) = 2 * 2 ^ (H - p.level - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  simp only [Position.sibling_level, Position.sibling_index]
  rcases Nat.mod_two_eq_zero_or_one p.index with parity | parity
  · rw [xor_one_of_even parity]; omega
  · rw [xor_one_of_odd parity]; omega

/-- The index of the sibling is the sibling of the index, below the root. -/
theorem positionGindex_sibling {H : Nat} {p : Position} (low : p.level < H) :
    positionGindex H p.sibling = gindexSibling (positionGindex H p) := by
  simp only [positionGindex, Position.sibling_level, Position.sibling_index, gindexSibling]
  -- The leading `2^(H - level)` is even, so the index and its offset have one parity.
  obtain ⟨E, even⟩ : ∃ E, 2 ^ (H - p.level) = 2 * E :=
    ⟨2 ^ (H - p.level - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
  rw [even]
  rcases Nat.mod_two_eq_zero_or_one p.index with parity | parity
  · rw [xor_one_of_even parity, xor_one_of_even (by omega)]
    omega
  · rw [xor_one_of_odd parity, xor_one_of_odd (by omega)]
    omega

/-- The index of the left child is twice the index, above level 0. -/
theorem positionGindex_left {H : Nat} {p : Position} (low : 1 ≤ p.level) (top : p.level ≤ H) :
    positionGindex H p.left = 2 * positionGindex H p := by
  simp only [positionGindex, Position.left_level, Position.left_index]
  rw [show H - (p.level - 1) = (H - p.level) + 1 by omega, Nat.pow_succ]
  omega

/-- The index of the right child is twice the index plus 1, above level 0. -/
theorem positionGindex_right {H : Nat} {p : Position} (low : 1 ≤ p.level) (top : p.level ≤ H) :
    positionGindex H p.right = 2 * positionGindex H p + 1 := by
  simp only [positionGindex, Position.right_level, Position.right_index]
  rw [show H - (p.level - 1) = (H - p.level) + 1 by omega, Nat.pow_succ]
  omega

/-- The children of a node of the tree above level 0 are in the tree. -/
theorem inTree_children {H : Nat} {p : Position} (inside : InTree H p) (low : 1 ≤ p.level) :
    InTree H p.left ∧ InTree H p.right :=
  ⟨inside.trans (Position.isAncestor_of_parent (Position.left_parent (by omega))),
    inside.trans (Position.isAncestor_of_parent (Position.right_parent (by omega)))⟩

/-- The ancestor `k` levels above the position of an index is the position of its shift. -/
theorem gindexPosition_ancestor {H g : Nat} (named : 1 ≤ g) (deep : Nat.log2 g ≤ H) {k : Nat}
    (short : k ≤ Nat.log2 g) : (gindexPosition H g).ancestor k = gindexPosition H (g >>> k) := by
  have inside := gindexPosition_inTree named deep
  have top : (gindexPosition H g).level + k ≤ H := by simp [gindexPosition]; omega
  rw [← gindexPosition_positionGindex (inTree_ancestor inside top),
    positionGindex_ancestor inside top, positionGindex_gindexPosition named deep]

/-- Moving an index to a tree `k` levels taller lifts its position by `k` levels. -/
theorem gindexPosition_lift {H g : Nat} (deep : Nat.log2 g ≤ H) (k : Nat) :
    gindexPosition (H + k) g =
      ⟨(gindexPosition H g).level + k, (gindexPosition H g).index⟩ :=
  Position.ext (by simp [gindexPosition]; omega) rfl

/-! ## Heights -/

/-- Folding by the maximum never goes below the starting value. -/
theorem le_foldl_max (values : List Nat) (initial : Nat) : initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => exact Nat.le_refl _
  | cons head rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Folding by the maximum bounds every value folded. -/
theorem member_le_foldl_max {values : List Nat} {value : Nat} (member : value ∈ values)
    (initial : Nat) : value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (Nat.le_max_right initial value) (le_foldl_max rest _)
    · exact ih member _

/-- Every index of a request is at most as deep as their tree. -/
theorem log2_le_gindexHeight {indices : List Nat} {g : Nat} (member : g ∈ indices) :
    Nat.log2 g ≤ gindexHeight indices :=
  member_le_foldl_max (List.mem_map_of_mem member) 0

/-- The paths of the positions of indices are the paths of the indices. -/
theorem paths_gindexPosition {H : Nat} {indices : List Nat}
    (valid : ∀ g ∈ indices, 1 ≤ g ∧ Nat.log2 g ≤ H) :
    ((indices.map (gindexPosition H)).flatMap (pathTo H)).map (positionGindex H) =
      indices.flatMap fun g => (List.range (Nat.log2 g)).map fun step => g >>> step := by
  induction indices with
  | nil => rfl
  | cons g rest ih =>
    obtain ⟨named, deep⟩ := valid g (by simp)
    simp only [List.map_cons, List.flatMap_cons, List.map_append,
      ih fun g' member => valid g' (List.mem_cons_of_mem _ member)]
    congr 1
    -- The path of the position climbs `log2 g` levels, and each step shifts the index once.
    have count : H - (gindexPosition H g).level = Nat.log2 g := by simp [gindexPosition]; omega
    simp only [pathTo, count, List.map_map]
    refine List.map_congr_left fun step below => ?_
    have top : (gindexPosition H g).level + step ≤ H := by
      simp [gindexPosition] at below ⊢; omega
    simp only [Function.comp_apply]
    rw [positionGindex_ancestor (gindexPosition_inTree named deep) top,
      positionGindex_gindexPosition named deep]

end EthLib.Serialization.Ssz

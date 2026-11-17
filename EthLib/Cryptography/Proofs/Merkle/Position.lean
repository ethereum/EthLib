module

public import EthLib.Cryptography.Merkle.Tree

/-!
# Proofs: positions in a Merkle tree

How the parent, the sibling, the children and the ancestors of a node relate.

The index arithmetic is proved here once, so that other proofs reason about positions.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

/-- Halving an index, then dividing by `2^n`, divides it by `2^(n + 1)`. -/
theorem div_two_div_pow (j n : Nat) : j / 2 / 2 ^ n = j / 2 ^ (n + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

namespace Position

/-- Two positions with the same level and the same index are equal. -/
@[ext] theorem ext {p q : Position} (hlevel : p.level = q.level) (hindex : p.index = q.index) :
    p = q := by
  cases p
  cases q
  simp_all

/-- A position is its level and its index. -/
@[simp] theorem eta (p : Position) : (⟨p.level, p.index⟩ : Position) = p :=
  rfl

/-! ## Siblings -/

/-- A node and its sibling have the same parent. -/
@[simp] theorem sibling_parent (p : Position) : p.sibling.parent = p.parent := by
  ext
  · rfl
  · simp [Nat.xor_div_two]

/-- The sibling of the sibling of a node is the node. -/
@[simp] theorem sibling_sibling (p : Position) : p.sibling.sibling = p := by
  ext
  · rfl
  · simp [Nat.xor_assoc]

/-- Exactly one of a node and its sibling is a left child. -/
@[simp] theorem isLeft_sibling (p : Position) : p.sibling.isLeft = !p.isLeft := by
  -- Flipping the low bit changes the parity.
  have hm : (p.index ^^^ 1) % 2 = 1 ↔ p.index % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one p.index
  have h2 := Nat.mod_two_eq_zero_or_one (p.index ^^^ 1)
  simp only [isLeft, sibling_index]
  by_cases h : p.index % 2 = 0
  · simp [h, hm.mpr h]
  · have h' : (p.index ^^^ 1) % 2 = 0 := by omega
    simp [h, h']

/-- A node is a left child when its index is even. -/
theorem isLeft_iff (p : Position) : p.isLeft = true ↔ p.index % 2 = 0 := by
  simp [isLeft]

/-! ## Children -/

/-- The left child of a parent is the even node of the pair. -/
theorem parent_left (p : Position) : p.parent.left = ⟨p.level, 2 * (p.index / 2)⟩ :=
  rfl

/-- The right child of a parent is the odd node of the pair. -/
theorem parent_right (p : Position) : p.parent.right = ⟨p.level, 2 * (p.index / 2) + 1⟩ :=
  rfl

/-- The parent of the left child of a node above the leaves is the node. -/
theorem left_parent {p : Position} (hlevel : p.level ≠ 0) : p.left.parent = p := by
  ext
  · simp only [parent_level, left_level]
    omega
  · simp

/-- The parent of the right child of a node above the leaves is the node. -/
theorem right_parent {p : Position} (hlevel : p.level ≠ 0) : p.right.parent = p := by
  ext
  · simp only [parent_level, right_level]
    omega
  · simp only [parent_index, right_index]
    omega

/-- A left child is a left child. -/
@[simp] theorem isLeft_left (p : Position) : p.left.isLeft = true := by
  simp [isLeft]

/-- A right child is not a left child. -/
@[simp] theorem isLeft_right (p : Position) : p.right.isLeft = false := by
  simp [isLeft, Nat.add_mod]

/-- A left child is the left child of its parent. -/
theorem parent_left_of_isLeft {p : Position} (h : p.isLeft = true) : p.parent.left = p := by
  rw [isLeft_iff] at h
  ext
  · simp
  · simp only [left_index, parent_index]
    omega

/-- A right child is the right child of its parent. -/
theorem parent_right_of_not_isLeft {p : Position} (h : p.isLeft = false) :
    p.parent.right = p := by
  have h' : p.index % 2 = 1 := by
    have := Nat.mod_two_eq_zero_or_one p.index
    simp only [isLeft, decide_eq_false_iff_not] at h
    omega
  ext
  · simp
  · simp only [right_index, parent_index]
    omega

/-! ## Ancestors -/

/-- A node is its own ancestor zero levels up. -/
@[simp] theorem ancestor_zero (p : Position) : p.ancestor 0 = p := by
  ext <;> simp

/-- The ancestor one level up is the parent. -/
@[simp] theorem ancestor_one (p : Position) : p.ancestor 1 = p.parent := by
  ext <;> simp

/-- The parent of the ancestor `k` levels up is the ancestor `k + 1` levels up. -/
theorem parent_ancestor (p : Position) (k : Nat) : (p.ancestor k).parent = p.ancestor (k + 1) := by
  ext
  · simp only [parent_level, ancestor_level]
    omega
  · simp [Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- The ancestor `k` levels above the parent is the ancestor `k + 1` levels above the node. -/
theorem ancestor_parent (p : Position) (k : Nat) : p.parent.ancestor k = p.ancestor (k + 1) := by
  ext
  · simp only [ancestor_level, parent_level]
    omega
  · simp [div_two_div_pow]

/-- Climbing `a` levels, then `b` more, climbs `a + b` levels. -/
@[simp] theorem ancestor_ancestor (p : Position) (a b : Nat) :
    (p.ancestor a).ancestor b = p.ancestor (a + b) := by
  ext
  · simp only [ancestor_level]
    omega
  · simp [Nat.div_div_eq_div_mul, Nat.pow_add]

/-- The ancestor `k` levels up of a node among the first `2^k` of its level is the first node. -/
theorem ancestor_of_lt {p : Position} {k : Nat} (h : p.index < 2 ^ k) :
    p.ancestor k = ⟨p.level + k, 0⟩ := by
  ext
  · rfl
  · simp [Nat.div_eq_of_lt h]

/-- A node is an ancestor of itself. -/
theorem IsAncestor.refl (p : Position) : p.IsAncestor p :=
  ⟨0, (ancestor_zero p).symm⟩

/-- Every ancestor of a node is an ancestor of its descendants. -/
theorem IsAncestor.trans {a b p : Position} (hab : a.IsAncestor b) (hbp : b.IsAncestor p) :
    a.IsAncestor p := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨l, rfl⟩ := hbp
  exact ⟨l + k, ancestor_ancestor p l k⟩

/-- The node `k` levels above another is its ancestor. -/
theorem isAncestor_ancestor (p : Position) (k : Nat) : (p.ancestor k).IsAncestor p :=
  ⟨k, rfl⟩

/-- An ancestor sits at or above the node. -/
theorem IsAncestor.level_le {a p : Position} (h : a.IsAncestor p) : p.level ≤ a.level := by
  obtain ⟨k, rfl⟩ := h
  simp

end Position

end EthLib.Cryptography.Merkle

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

/-- Dividing an index by `2^n`, then halving it, divides it by `2^(n + 1)`. -/
theorem div_pow_div_two (j n : Nat) : j / 2 ^ n / 2 = j / 2 ^ (n + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

namespace Position

/-- A position is its level and its index. -/
@[simp] theorem eta (p : Position) : (⟨p.level, p.index⟩ : Position) = p :=
  rfl

/-! ## The operations on a level and an index -/

/-- The parent of the node at level `l` and index `j` is at level `l + 1` and index `j / 2`. -/
theorem parent_mk (l j : Nat) : (⟨l, j⟩ : Position).parent = ⟨l + 1, j / 2⟩ :=
  rfl

/-- The sibling of the node at level `l` and index `j` has the low bit of `j` flipped. -/
theorem sibling_mk (l j : Nat) : (⟨l, j⟩ : Position).sibling = ⟨l, j ^^^ 1⟩ :=
  rfl

/-- The left child of the node at level `l + 1` and index `j` is at level `l` and index `2j`. -/
theorem left_mk (l j : Nat) : (⟨l + 1, j⟩ : Position).left = ⟨l, 2 * j⟩ :=
  rfl

/-- The right child of the node at level `l + 1` and index `j` is at index `2j + 1`. -/
theorem right_mk (l j : Nat) : (⟨l + 1, j⟩ : Position).right = ⟨l, 2 * j + 1⟩ :=
  rfl

/-- The ancestor `k` levels above level `l` and index `j` is at index `j / 2^k`. -/
theorem ancestor_mk (l j k : Nat) : (⟨l, j⟩ : Position).ancestor k = ⟨l + k, j / 2 ^ k⟩ :=
  rfl

/-- The ancestor of leaf `j` on level `n` is the node at index `j / 2^n`. -/
theorem ancestor_mk_zero (j n : Nat) : (⟨0, j⟩ : Position).ancestor n = ⟨n, j / 2 ^ n⟩ := by
  ext <;> simp

/-! ## Siblings -/

/-- A node is a left child when its index is even. -/
theorem isLeft_iff (p : Position) : p.isLeft = true ↔ p.index % 2 = 0 := by
  simp [isLeft]

/-- A node is a right child when its index is odd. -/
theorem isLeft_eq_false_iff (p : Position) : p.isLeft = false ↔ p.index % 2 = 1 := by
  -- An index has parity 0 or 1, so not even means odd.
  have := Nat.mod_two_eq_zero_or_one p.index
  simp only [isLeft, decide_eq_false_iff_not]
  omega

/-- A node and its sibling have the same parent. -/
@[simp] theorem sibling_parent (p : Position) : p.sibling.parent = p.parent := by
  ext
  · rfl
  · -- Halving the index drops the low bit, which is the only bit the sibling changes.
    simp [Nat.xor_div_two]

/-- The sibling of the sibling of a node is the node. -/
@[simp] theorem sibling_sibling (p : Position) : p.sibling.sibling = p := by
  ext
  · rfl
  · -- Flipping the low bit twice restores it.
    simp [Nat.xor_assoc]

/-- Exactly one of a node and its sibling is a left child. -/
@[simp] theorem isLeft_sibling (p : Position) : p.sibling.isLeft = !p.isLeft := by
  -- Flipping the low bit flips the parity.
  have hparity : (p.index ^^^ 1) % 2 = 0 ↔ ¬ p.index % 2 = 0 := by
    have := Nat.xor_mod_two_eq_one (a := p.index) (b := 1)
    omega
  have := Nat.mod_two_eq_zero_or_one p.index
  by_cases h : p.index % 2 = 0 <;> simp [isLeft, hparity, h] <;> omega

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
  · -- Going down then up is the identity on levels above 0.
    simp only [parent_level, left_level]
    omega
  · simp

/-- The parent of the right child of a node above the leaves is the node. -/
theorem right_parent {p : Position} (hlevel : p.level ≠ 0) : p.right.parent = p := by
  ext
  · simp only [parent_level, right_level]
    omega
  · -- (2j + 1) / 2 = j.
    simp only [parent_index, right_index]
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
  · -- An even index j satisfies 2 * (j / 2) = j.
    simp only [left_index, parent_index]
    omega

/-- A right child is the right child of its parent. -/
theorem parent_right_of_not_isLeft {p : Position} (h : p.isLeft = false) :
    p.parent.right = p := by
  rw [isLeft_eq_false_iff] at h
  ext
  · simp
  · -- An odd index j satisfies 2 * (j / 2) + 1 = j.
    simp only [right_index, parent_index]
    omega

/-! ## Ancestors -/

/-- A node is its own ancestor zero levels up. -/
@[simp] theorem ancestor_zero (p : Position) : p.ancestor 0 = p := by
  ext <;> simp

/-- The ancestor one level up is the parent. -/
@[simp] theorem ancestor_one (p : Position) : p.ancestor 1 = p.parent := by
  ext <;> simp

/-- The parent of the ancestor `k` levels up is the ancestor `k + 1` levels up. -/
@[simp] theorem parent_ancestor (p : Position) (k : Nat) :
    (p.ancestor k).parent = p.ancestor (k + 1) := by
  ext
  · simp only [parent_level, ancestor_level]
    omega
  · simp [div_pow_div_two]

/-- The ancestor `k` levels above the parent is the ancestor `k + 1` levels above the node. -/
@[simp] theorem ancestor_parent (p : Position) (k : Nat) :
    p.parent.ancestor k = p.ancestor (k + 1) := by
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

/-- The ancestor `k` levels up of a node among the first `2^k` of its level is the first node.

For example, every leaf of a tree of height `h` has the root as its ancestor `h` levels up. -/
theorem ancestor_eq_of_index_lt {p : Position} {k : Nat} (h : p.index < 2 ^ k) :
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

/-- A node is an ancestor of another when it is at or above its level.

Its index is then the other's index divided by 2 to the power of the level difference. -/
theorem isAncestor_iff {a p : Position} :
    a.IsAncestor p ↔ p.level ≤ a.level ∧ a.index = p.index / 2 ^ (a.level - p.level) := by
  constructor
  · -- The ancestor `k` levels up is `k` levels higher, at the index divided by `2^k`.
    rintro ⟨k, rfl⟩
    simp
  · -- Conversely, the level difference is the number of levels to climb.
    rintro ⟨hlevel, hindex⟩
    refine ⟨a.level - p.level, ?_⟩
    ext
    · simp only [ancestor_level]
      omega
    · simpa using hindex

/-- Whether a node is an ancestor of another is decided by its level and its index. -/
instance (a p : Position) : Decidable (a.IsAncestor p) :=
  decidable_of_iff _ isAncestor_iff.symm

end Position

end EthLib.Cryptography.Merkle

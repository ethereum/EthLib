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

/-! ## Ancestors on one level -/

/-- Flipping the low bit of an even number adds 1.

So the sibling of a left child is the next node of its level. -/
theorem xor_one_of_even {x : Nat} (even : x % 2 = 0) : x ^^^ 1 = x + 1 := by
  -- The flip keeps the half and makes the number odd.
  have half : (x ^^^ 1) / 2 = x / 2 := by simp [Nat.xor_div_two]
  have parity := Nat.xor_mod_two_eq_one (a := x) (b := 1)
  omega

/-- Flipping the low bit of an odd number subtracts 1.

So the sibling of a right child is the previous node of its level. -/
theorem xor_one_of_odd {x : Nat} (odd : x % 2 = 1) : x ^^^ 1 = x - 1 := by
  -- The flip keeps the half and makes the number even.
  have half : (x ^^^ 1) / 2 = x / 2 := by simp [Nat.xor_div_two]
  have parity := Nat.xor_mod_two_eq_one (a := x) (b := 1)
  omega

namespace Position

/-- A node is its own ancestor only at its own level.

So two nodes on one level, one an ancestor of the other, are the same node. -/
theorem IsAncestor.eq_of_level_le {a p : Position} (h : a.IsAncestor p) (le : a.level ≤ p.level) :
    a = p := by
  obtain ⟨k, rfl⟩ := h
  -- Climbing zero levels stays in place.
  have : k = 0 := by simp only [ancestor_level] at le; omega
  subst this
  exact ancestor_zero p

/-- An ancestor of a node strictly above it is an ancestor of its parent.

So an ancestor of a node is found again by climbing one level. -/
theorem IsAncestor.parent {a p : Position} (h : a.IsAncestor p) (lt : p.level < a.level) :
    a.IsAncestor p.parent := by
  obtain ⟨k, rfl⟩ := h
  -- The ancestor is at least one level up, so it is above the parent.
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [ancestor_level] at lt; omega⟩
  exact ⟨k, (ancestor_parent p k).symm⟩

/-- A parent is an ancestor of each of its children. -/
theorem isAncestor_of_parent {a p : Position} (h : p.parent = a) : a.IsAncestor p :=
  ⟨1, by simp [h]⟩

/-- Two nodes with one parent are the same node or siblings.

So the two children of a node on a path are the path node and its sibling. -/
theorem eq_or_eq_sibling_of_parent_eq {a b : Position} (h : a.parent = b.parent) :
    a = b ∨ a = b.sibling := by
  obtain ⟨la, ia⟩ := a
  obtain ⟨lb, ib⟩ := b
  simp only [parent_mk, mk.injEq] at h
  obtain ⟨levels, half⟩ := h
  obtain rfl : la = lb := by omega
  -- The sibling has the same half and the other parity, which pins down a different index.
  by_cases same : ia = ib
  · exact .inl (by rw [same])
  refine .inr ?_
  rw [sibling_mk, mk.injEq]
  refine ⟨rfl, ?_⟩
  have half' : (ib ^^^ 1) / 2 = ib / 2 := by simp [Nat.xor_div_two]
  have parity := Nat.xor_mod_two_eq_one (a := ib) (b := 1)
  have := Nat.mod_two_eq_zero_or_one ib
  have := Nat.mod_two_eq_zero_or_one ia
  have := Nat.mod_two_eq_zero_or_one (ib ^^^ 1)
  omega

/-- Two ancestors of one node on one level are the same node. -/
theorem IsAncestor.unique {a b p : Position} (ha : a.IsAncestor p) (hb : b.IsAncestor p)
    (level : a.level = b.level) : a = b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  simp only [ancestor_level] at level
  obtain rfl : m = n := by omega
  rfl

/-- Of two ancestors of one node, the higher one is an ancestor of the lower one. -/
theorem IsAncestor.of_both {a b p : Position} (ha : a.IsAncestor p) (hb : b.IsAncestor p)
    (le : b.level ≤ a.level) : a.IsAncestor b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  simp only [ancestor_level] at le
  exact ⟨m - n, by rw [ancestor_ancestor]; congr 1; omega⟩

/-- A node strictly above another is an ancestor of the other's sibling too. -/
theorem IsAncestor.sibling {a q : Position} (h : a.IsAncestor q) (lt : q.level < a.level) :
    a.IsAncestor q.sibling := by
  -- Both share the parent, which the ancestor sits above.
  have parent := h.parent lt
  rw [← sibling_parent] at parent
  exact parent.trans (isAncestor_of_parent rfl)

/-- A node is an ancestor of its left child. -/
theorem isAncestor_left (l j : Nat) : (⟨l + 1, j⟩ : Position).IsAncestor ⟨l, 2 * j⟩ :=
  isAncestor_of_parent (Position.ext rfl (by show 2 * j / 2 = j; omega))

/-- A node is an ancestor of its right child. -/
theorem isAncestor_right (l j : Nat) : (⟨l + 1, j⟩ : Position).IsAncestor ⟨l, 2 * j + 1⟩ :=
  isAncestor_of_parent (Position.ext rfl (by show (2 * j + 1) / 2 = j; omega))

/-- The sibling of the left child is the right child. -/
theorem sibling_left (l j : Nat) : (⟨l, 2 * j⟩ : Position).sibling = ⟨l, 2 * j + 1⟩ := by
  rw [sibling_mk, xor_one_of_even (by omega)]

/-- The sibling of the right child is the left child. -/
theorem sibling_right (l j : Nat) : (⟨l, 2 * j + 1⟩ : Position).sibling = ⟨l, 2 * j⟩ := by
  rw [sibling_mk, xor_one_of_odd (by omega)]
  rfl

/-- A node below another, at least one level lower, lies below one of its two children. -/
theorem IsAncestor.child {l j : Nat} {q : Position} (h : (⟨l + 1, j⟩ : Position).IsAncestor q)
    (low : q.level ≤ l) :
    (⟨l, 2 * j⟩ : Position).IsAncestor q ∨ (⟨l, 2 * j + 1⟩ : Position).IsAncestor q := by
  obtain ⟨m, hm⟩ := h
  have level := congrArg Position.level hm
  have index := congrArg Position.index hm
  simp only [ancestor_level, ancestor_index] at level index
  -- The ancestor of `q` one level below the node is the child on its side.
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have half : q.index / 2 ^ m / 2 = j := by rw [div_pow_div_two]; exact index.symm
  rcases Nat.mod_two_eq_zero_or_one (q.index / 2 ^ m) with even | odd
  · exact .inl ⟨m, Position.ext (by simp; omega) (by simp; omega)⟩
  · exact .inr ⟨m, Position.ext (by simp; omega) (by simp; omega)⟩

/-- No node lies below both children of a node. -/
theorem IsAncestor.not_both {l j : Nat} {q : Position}
    (left : (⟨l, 2 * j⟩ : Position).IsAncestor q)
    (right : (⟨l, 2 * j + 1⟩ : Position).IsAncestor q) : False := by
  have := congrArg Position.index (left.unique right rfl)
  simp at this

end Position

/-- A node is never its own sibling. -/
theorem Position.sibling_ne (q : Position) : q.sibling ≠ q := by
  intro same
  have index : q.index ^^^ 1 = q.index := congrArg Position.index same
  have parity := Nat.xor_mod_two_eq_one (a := q.index) (b := 1)
  omega

end EthLib.Cryptography.Merkle

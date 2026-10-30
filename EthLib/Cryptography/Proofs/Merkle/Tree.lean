import EthLib.Cryptography.Merkle.Tree

/-!
# Proofs: `Merkle.Tree`

An honest path leads from a leaf to its ancestor on the top level.

For a leaf `e < 2^h`, that ancestor is the root.

The statements hold for every node hash, so every tree built from `Merkle.node` inherits them.
-/

namespace EthLib.Cryptography.Merkle

variable {α : Type} {height : Nat}
variable {nodeHash : Fin (height + 1) → Nat → α → α → α} {leaves : Nat → α}

/-! ## Unfolding a node -/

/-- A node on level 0 is a leaf. -/
theorem node_zero (h : 0 ≤ height) (j : Nat) : node nodeHash leaves 0 h j = leaves j :=
  rfl

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (l : Nat) (h : l + 1 ≤ height) (j : Nat) :
    node nodeHash leaves (l + 1) h j = nodeHash ⟨l + 1, by omega⟩ j
      (node nodeHash leaves l (by omega) (2 * j)) (node nodeHash leaves l (by omega) (2 * j + 1)) :=
  rfl

/-- A node depends on its bound only as a proof. -/
theorem node_congr_bound (l : Nat) (h h' : l ≤ height) (j : Nat) :
    node nodeHash leaves l h j = node nodeHash leaves l h' j :=
  rfl

/-! ## One climb step -/

/-- The two children a climb step on `level` hashes, the left one first.

Bit `level` of `e` says whether the held node is the left child. -/
def stepChildren (e level : Nat) (current sibling : α) : α × α :=
  if (e >>> level) % 2 == 0 then (current, sibling) else (sibling, current)

/-- A climb step hashes its two children, in tree order, at the parent's position. -/
theorem climbStep_eq (e : Nat) (level : Fin height) (current sibling : α) :
    Internal.climbStep nodeHash e level current sibling
      = nodeHash level.succ (e >>> (level.val + 1))
          (stepChildren e level current sibling).1 (stepChildren e level current sibling).2 := by
  unfold Internal.climbStep stepChildren
  split <;> rfl

/-- The children determine the held node and its sibling. -/
theorem stepChildren_inj {e level : Nat} {current sibling current' sibling' : α} :
    stepChildren e level current sibling = stepChildren e level current' sibling' ↔
      current = current' ∧ sibling = sibling' := by
  unfold stepChildren
  split <;> simp only [Prod.mk.injEq, and_comm]

/-- Flipping the bottom bit, written as arithmetic. -/
private theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  -- The bits above the bottom one are untouched.
  have hd : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  -- The bottom one is swapped.
  have hm : (n ^^^ 1) % 2 = 1 ↔ n % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one n
  have h2 := Nat.mod_two_eq_zero_or_one (n ^^^ 1)
  omega

/-- An ancestor of leaf `e` and its sibling are the two children of the next ancestor.

Here `f` reads any one level of a tree. -/
theorem stepChildren_siblingIndex (f : Nat → α) (e level : Nat) :
    stepChildren e level (f (e >>> level)) (f (siblingIndex e level))
      = (f (2 * (e >>> (level + 1))), f (2 * (e >>> (level + 1)) + 1)) := by
  have hhalf : e >>> (level + 1) = (e >>> level) / 2 := Nat.shiftRight_succ _ _
  unfold stepChildren
  rcases Nat.mod_two_eq_zero_or_one (e >>> level) with hr | hr
  · -- Bit `level` is zero: the ancestor is the left child, its sibling the right one.
    have ha : 2 * (e >>> (level + 1)) = e >>> level := by
      rw [hhalf]
      omega
    have hb : 2 * (e >>> (level + 1)) + 1 = siblingIndex e level := by
      rw [hhalf]
      simp only [siblingIndex, xor_one]
      omega
    rw [hb, ha]
    simp [hr]
  · -- Bit `level` is one: the sibling is the left child, the ancestor the right one.
    have ha : 2 * (e >>> (level + 1)) = siblingIndex e level := by
      rw [hhalf]
      simp only [siblingIndex, xor_one]
      omega
    have hb : 2 * (e >>> (level + 1)) + 1 = e >>> level := by
      rw [hhalf]
      omega
    rw [hb, ha]
    simp [hr]

/-! ## The path reaches the root -/

/-- The verifier's node on each level is the signer's, all the way up. -/
theorem climbUpto_eq_node (e : Nat) :
    ∀ (levels : Nat) (hl : levels ≤ height),
      Internal.climbUpto nodeHash e (path nodeHash leaves e) (leaves e) levels hl
        = node nodeHash leaves levels hl (e >>> levels) := by
  intro levels
  induction levels with
  | zero => intro _; rfl
  | succ l ih =>
    intro hl
    -- Below the last step the two sides agree by the induction hypothesis.
    simp only [Internal.climbUpto, climbStep_eq]
    rw [ih (by omega)]
    simp only [path, Vector.getElem_ofFn]
    -- The held node and the path's sibling are the two children of the next node up.
    rw [stepChildren_siblingIndex (fun j => node nodeHash leaves l (by omega) j)]
    rfl

/-- An honest path leads from leaf `e` to node `floor(e / 2^height)` on the top level. -/
theorem fold_path (e : Nat) :
    fold nodeHash e (leaves e) (path nodeHash leaves e)
      = node nodeHash leaves height (Nat.le_refl _) (e >>> height) :=
  climbUpto_eq_node e height (Nat.le_refl _)

/-- An honest path leads from a leaf `e < 2^height` to the root. -/
theorem fold_path_root {e : Nat} (he : e < 2 ^ height) :
    fold nodeHash e (leaves e) (path nodeHash leaves e) = root nodeHash leaves := by
  rw [fold_path, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt he]
  rfl

/-! ## Trees whose node hash ignores the position -/

/-- In a tree that hashes every node alike, node `j` on `level` is the root of its own subtree.

That subtree's leaves are the `2^level` leaves below node `j`, starting at `j * 2^level`.

Its height does not matter, since nothing reads the position. -/
theorem node_const_shift (combine : α → α → α) :
    ∀ (level : Nat) {height height' : Nat} (leaves : Nat → α) (h : level ≤ height)
      (h' : level ≤ height') (j : Nat),
      node (height := height) (fun _ _ => combine) leaves level h j
        = node (height := height') (fun _ _ => combine)
            (fun i => leaves (j * 2 ^ level + i)) level h' 0 := by
  intro level
  induction level with
  | zero => intro _ _ leaves _ _ j; simp [node]
  | succ l ih =>
    intro height height' leaves h h' j
    let shifted := fun i => leaves (j * 2 ^ (l + 1) + i)
    -- The left child's subtree starts where its parent's does.
    have left : node (height := height) (fun _ _ => combine) leaves l (by omega) (2 * j)
        = node (height := height') (fun _ _ => combine) shifted l (by omega) 0 := by
      rw [ih (height' := height') leaves (by omega) (by omega) (2 * j),
        ih (height := height') (height' := height') shifted (by omega) (by omega) 0]
      congr 1
      funext i
      simp only [shifted]
      congr 1
      rw [Nat.pow_succ]; simp only [Nat.zero_mul, Nat.zero_add]
      rw [Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2]
    -- The right child's subtree starts `2^l` leaves later.
    have right : node (height := height) (fun _ _ => combine) leaves l (by omega) (2 * j + 1)
        = node (height := height') (fun _ _ => combine) shifted l (by omega) 1 := by
      rw [ih (height' := height') leaves (by omega) (by omega) (2 * j + 1),
        ih (height := height') (height' := height') shifted (by omega) (by omega) 1]
      congr 1
      funext i
      simp only [shifted]
      congr 1
      rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul, Nat.mul_comm 2 j, Nat.mul_assoc, Nat.mul_comm 2,
        Nat.add_assoc]
    simp only [node_succ, left, right]
    rfl

end EthLib.Cryptography.Merkle

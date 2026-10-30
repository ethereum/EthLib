import EthLib.Cryptography.Vrf.Tree

/-!
# Proofs: `Vrf.Tree`

- The path of index `i` leads from `i`'s leaf to the root.
- Two paths that lead to one root from one index are equal, or the node hash collides.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

variable {secrets : UInt32 → Digest}

/-! ## Unfolding -/

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (l j : Nat) :
    node secrets (l + 1) j = nodeHash (node secrets l (2 * j)) (node secrets l (2 * j + 1)) :=
  rfl

/-- The two children a climb step hashes on `level`, the left one first. -/
def stepChildren (i : UInt32) (level : Nat) (current sibling : Digest) : Digest × Digest :=
  if (i.toNat >>> level) % 2 == 0 then (current, sibling) else (sibling, current)

/-- A climb step hashes its two children in tree order. -/
theorem climbStep_eq (i : UInt32) (level : Nat) (current sibling : Digest) :
    Internal.climbStep i level current sibling
      = nodeHash (stepChildren i level current sibling).1 (stepChildren i level current sibling).2 := by
  unfold Internal.climbStep stepChildren
  split <;> rfl

/-- The children determine the held node and its sibling. -/
theorem stepChildren_inj {i : UInt32} {level : Nat} {c s c' s' : Digest} :
    stepChildren i level c s = stepChildren i level c' s' ↔ c = c' ∧ s = s' := by
  unfold stepChildren
  split <;> simp only [Prod.mk.injEq, and_comm]

/-! ## The path reaches the root -/

/-- Flipping the bottom bit, written as arithmetic. -/
private theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  -- The bits above the bottom one are untouched.
  have hd : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  -- The bottom one is swapped.
  have hm : (n ^^^ 1) % 2 = 1 ↔ n % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one n
  have h2 := Nat.mod_two_eq_zero_or_one (n ^^^ 1)
  omega

/-- An ancestor of index `i` and its sibling are the two children of the next ancestor.

Here `f` reads one level of the tree. -/
theorem stepChildren_siblingIndex (f : Nat → Digest) (i : UInt32) (level : Nat) :
    stepChildren i level (f (i.toNat >>> level)) (f (siblingIndex i.toNat level))
      = (f (2 * (i.toNat >>> (level + 1))), f (2 * (i.toNat >>> (level + 1)) + 1)) := by
  have hhalf : i.toNat >>> (level + 1) = (i.toNat >>> level) / 2 := Nat.shiftRight_succ _ _
  unfold stepChildren
  rcases Nat.mod_two_eq_zero_or_one (i.toNat >>> level) with hr | hr
  · -- Bit zero: the ancestor is the left child, its sibling the right one.
    have ha : 2 * (i.toNat >>> (level + 1)) = i.toNat >>> level := by
      rw [hhalf]
      omega
    have hb : 2 * (i.toNat >>> (level + 1)) + 1 = siblingIndex i.toNat level := by
      rw [hhalf]
      simp only [siblingIndex, xor_one]
      omega
    rw [hb, ha]
    simp [hr]
  · -- Bit one: the sibling is the left child, the ancestor the right one.
    have ha : 2 * (i.toNat >>> (level + 1)) = siblingIndex i.toNat level := by
      rw [hhalf]
      simp only [siblingIndex, xor_one]
      omega
    have hb : 2 * (i.toNat >>> (level + 1)) + 1 = i.toNat >>> level := by
      rw [hhalf]
      omega
    rw [hb, ha]
    simp [hr]

/-- The leaf of index `i` is node `i` on level 0. -/
theorem node_zero_toNat (i : UInt32) : node secrets 0 i.toNat = leafHash (secrets i) := by
  simp [node]

/-- The verifier's node on each level is the tree's, all the way up. -/
theorem climbUpto_eq_node (i : UInt32) :
    ∀ (levels : Nat) (hl : levels ≤ VRF_TREE_HEIGHT),
      Internal.climbUpto i (path secrets i) (leafHash (secrets i)) levels hl
        = node secrets levels (i.toNat >>> levels) := by
  intro levels
  induction levels with
  | zero => intro _; simp [Internal.climbUpto, node_zero_toNat]
  | succ l ih =>
    intro hl
    -- Below the last step the two sides agree by the induction hypothesis.
    simp only [Internal.climbUpto, climbStep_eq]
    rw [ih (by omega)]
    simp only [path, Vector.getElem_ofFn]
    -- The held node and the path's sibling are the two children of the next node up.
    rw [stepChildren_siblingIndex (fun j => node secrets l j)]
    rfl

/-- The path of index `i` leads from `i`'s leaf to the root. -/
theorem pathRoot_path (i : UInt32) :
    pathRoot i (leafHash (secrets i)) (path secrets i) = root secrets := by
  rw [pathRoot, climbUpto_eq_node]
  -- An index below `2^32` has no ancestor on level 32 other than node 0.
  have htop : i.toNat >>> VRF_TREE_HEIGHT = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt i.toNat_lt
  rw [htop]
  rfl

/-! ## A path binds its leaf -/

/-- Two different child pairs with one parent. -/
def NodeCollision : Prop :=
  ∃ x y : Digest × Digest, x ≠ y ∧ nodeHash x.1 x.2 = nodeHash y.1 y.2

/-- Two climbs from one index that meet after `levels` levels agree below, or the node hash collides. -/
theorem climbUpto_binding (i : UInt32) (pi pi' : Vector Digest VRF_TREE_HEIGHT) (a b : Digest) :
    ∀ (levels : Nat) (hl : levels ≤ VRF_TREE_HEIGHT),
      Internal.climbUpto i pi a levels hl = Internal.climbUpto i pi' b levels hl →
      (a = b ∧ ∀ l (h : l < levels), pi[l]'(by omega) = pi'[l]'(by omega)) ∨ NodeCollision := by
  intro levels
  induction levels with
  | zero =>
    -- No level climbed: both sides are their leaves.
    intro _ heq
    exact .inl ⟨heq, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hl heq
    simp only [Internal.climbUpto, climbStep_eq] at heq
    by_cases hpair : stepChildren i k (Internal.climbUpto i pi a k (by omega)) (pi[k]'(by omega))
        = stepChildren i k (Internal.climbUpto i pi' b k (by omega)) (pi'[k]'(by omega))
    · -- Equal pairs: the held nodes and the siblings on level `k` agree.
      obtain ⟨hheld, hsib⟩ := stepChildren_inj.mp hpair
      rcases ih (by omega) hheld with ⟨hab, hbelow⟩ | hcol
      · refine .inl ⟨hab, fun l h => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
        · exact hbelow l h
        · exact hsib
      · exact .inr hcol
    · -- Different pairs with one parent: a collision on level `k + 1`.
      exact .inr ⟨_, _, hpair, heq⟩

/-- Two paths from one index to one root have the same leaf and siblings, or the node hash collides. -/
theorem pathRoot_binding {i : UInt32} {a b : Digest} {pi pi' : Vector Digest VRF_TREE_HEIGHT}
    (heq : pathRoot i a pi = pathRoot i b pi') : (a = b ∧ pi = pi') ∨ NodeCollision := by
  rcases climbUpto_binding i pi pi' a b VRF_TREE_HEIGHT (Nat.le_refl _) heq with ⟨hab, hpi⟩ | hcol
  · exact .inl ⟨hab, Vector.ext fun l h => hpi l h⟩
  · exact .inr hcol

end EthLib.Cryptography.Vrf

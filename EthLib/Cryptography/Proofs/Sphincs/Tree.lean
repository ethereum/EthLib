import EthLib.Cryptography.Sphincs.Tree

/-!
# Proofs: `Sphincs.Tree`

An honest path leads from a key's leaf to the root of its tree.

The key `e` of a tree of height `h` reaches node `floor(e / 2^h)` on the top level.

So a key below `2^h`, which every key of the tree is, reaches the root.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {seed : Seed} {layer : Layer} {tree : Nat}

/-! ## Unfolding a node -/

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (l : Nat) (h : l + 1 ≤ layer.height) (j : Nat) :
    node pp seed layer tree (l + 1) h j
      = nodeHash pp layer tree ⟨l + 1, by have := layer.height_le; omega⟩ j
          (node pp seed layer tree l (by omega) (2 * j))
          (node pp seed layer tree l (by omega) (2 * j + 1)) :=
  rfl

/-! ## Indices -/

/-- Flipping the bottom bit, written as arithmetic. -/
theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  -- The bits above the bottom one are untouched.
  have hd : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  -- The bottom one is swapped.
  have hm : (n ^^^ 1) % 2 = 1 ↔ n % 2 = 0 := by simp
  have h1 := Nat.mod_two_eq_zero_or_one n
  have h2 := Nat.mod_two_eq_zero_or_one (n ^^^ 1)
  omega

/-! ## The path reaches the root -/

/-- The verifier's node on each level is the signer's, all the way up. -/
theorem climbUpto_eq_node (e : Nat) :
    ∀ (levels : Nat) (hl : levels ≤ layer.height),
      Internal.climbUpto pp layer tree e (path pp seed layer tree e)
          (node pp seed layer tree 0 (Nat.zero_le _) e) levels hl
        = node pp seed layer tree levels hl (e >>> levels) := by
  intro levels
  induction levels with
  | zero => intro _; rfl
  | succ l ih =>
    intro hl
    -- Below the last step the two sides agree by the induction hypothesis.
    simp only [Internal.climbUpto, ih (by omega)]
    simp only [path, Vector.getElem_ofFn, Internal.climbStep, node_succ l hl]
    have hhalf : e >>> (l + 1) = (e >>> l) / 2 := Nat.shiftRight_succ _ _
    rcases Nat.mod_two_eq_zero_or_one (e >>> l) with hr | hr
    · -- Bit `l` is zero, so the path node is the right child.
      have hb : 2 * (e >>> (l + 1)) + 1 = siblingIndex e l := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      have ha : 2 * (e >>> (l + 1)) = e >>> l := by
        rw [hhalf]
        omega
      rw [hb, ha]
      simp [hr]
    · -- Bit `l` is one, so the path node is the left child.
      have hb : 2 * (e >>> (l + 1)) + 1 = e >>> l := by
        rw [hhalf]
        omega
      have ha : 2 * (e >>> (l + 1)) = siblingIndex e l := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      rw [hb, ha]
      simp [hr]

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^h)` on the top level. -/
theorem fold_path (e : Nat) :
    fold pp layer tree e (node pp seed layer tree 0 (Nat.zero_le _) e) (path pp seed layer tree e)
      = node pp seed layer tree layer.height (Nat.le_refl _) (e >>> layer.height) :=
  climbUpto_eq_node e layer.height (Nat.le_refl _)

/-- A key of the tree, below `2^h`, reaches the tree's root. -/
theorem fold_path_root {e : Nat} (he : e < 2 ^ layer.height) :
    fold pp layer tree e (otsPublicLeaf pp seed ⟨layer, tree, e⟩) (path pp seed layer tree e)
      = treeRoot pp seed layer tree := by
  have := fold_path (pp := pp) (seed := seed) (layer := layer) (tree := tree) e
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt he] at this
  exact this

end EthLib.Cryptography.Sphincs

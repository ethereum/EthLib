import EthLib.Cryptography.Xmss.Tree

/-!
# Proofs: `Xmss.Tree`

An honest path leads from a key's leaf to the root of its tree.

On the bottom layer, key `idx` reaches the root of bottom tree `floor(idx / 2^16)`.

On the top layer, key `b < 2^16` reaches the root of the one top tree.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {pp : PublicParam} {seed : Seed} {layer : Layer}

/-! ## Unfolding a node -/

/-- Every node above level 0 is the hash of its two children. -/
theorem node_succ (l : Nat) (h : l + 1 ≤ LAYER_HEIGHT) (j : Nat) :
    node pp seed layer (l + 1) h j = nodeHash pp layer ⟨l + 1, by omega⟩ j
      (node pp seed layer l (by omega) (2 * j)) (node pp seed layer l (by omega) (2 * j + 1)) :=
  rfl

/-! ## Indices -/

/-- Flipping the bottom bit, written as arithmetic. -/
private theorem xor_one (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
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
    ∀ (levels : Nat) (hl : levels ≤ LAYER_HEIGHT),
      Internal.climbUpto pp layer e (path pp seed layer e) (node pp seed layer 0 (by omega) e)
          levels hl
        = node pp seed layer levels hl (e >>> levels) := by
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
    · -- Bit `l` is zero, so the path node is the left child.
      have hb : 2 * (e >>> (l + 1)) + 1 = siblingIndex e l := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      have ha : 2 * (e >>> (l + 1)) = e >>> l := by
        rw [hhalf]
        omega
      rw [hb, ha]
      simp [hr]
    · -- Bit `l` is one, so the sibling is the left child.
      have hb : 2 * (e >>> (l + 1)) + 1 = e >>> l := by
        rw [hhalf]
        omega
      have ha : 2 * (e >>> (l + 1)) = siblingIndex e l := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      rw [hb, ha]
      simp [hr]

/-- An honest path leads from key `e`'s leaf to node `floor(e / 2^16)` on the top level. -/
theorem fold_path (e : Nat) :
    fold pp layer e (node pp seed layer 0 (by omega) e) (path pp seed layer e)
      = node pp seed layer LAYER_HEIGHT (Nat.le_refl _) (e >>> LAYER_HEIGHT) :=
  climbUpto_eq_node e LAYER_HEIGHT (Nat.le_refl _)

/-- On the top layer, key `b < 2^16` reaches the root of the one top tree. -/
theorem fold_path_top {b : Nat} (hb : b < 2 ^ LAYER_HEIGHT) :
    fold pp .top b (node pp seed .top 0 (by omega) b) (path pp seed .top b)
      = node pp seed .top LAYER_HEIGHT (Nat.le_refl _) 0 := by
  rw [fold_path, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hb]

end EthLib.Cryptography.Xmss

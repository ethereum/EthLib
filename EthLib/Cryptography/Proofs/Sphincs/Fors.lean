import EthLib.Cryptography.Sphincs.Fors
import EthLib.Cryptography.Proofs.Sphincs.Tree

/-!
# Proofs: `Sphincs.Fors`

An honest FORS opening leads back to the instance's FORS key.

- Climbing levels 0 to 8 from leaf `l` reaches `Y_{9, floor(l / 512)}`.
- The last path node is the other one, `Y_{9, floor(l / 512) xor 1}`.
- Bit 9 of `l` puts the two in order, which gives `(Y_{9,0}, Y_{9,1})`.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {pp : PublicParam} {seed : Seed} {idx : Nat} {kappa : Fin FORS_TREES}

/-! ## Unfolding a node -/

/-- Every FORS node above level 0 is the hash of its two children. -/
theorem forsNode_succ (l : Nat) (h : l + 1 < FORS_HEIGHT) (j : Nat) :
    forsNode pp seed idx kappa (l + 1) h j
      = forsNodeHash pp idx kappa ⟨l + 1, h⟩ j
          (forsNode pp seed idx kappa l (by omega) (2 * j))
          (forsNode pp seed idx kappa l (by omega) (2 * j + 1)) :=
  rfl

/-- A leaf index is its own position. -/
theorem forsIndex_val (l : Fin (2 ^ FORS_HEIGHT)) : forsIndex l.val = l :=
  Fin.ext (Nat.mod_eq_of_lt l.isLt)

/-- The leaf an opening reveals is the honest level-0 node. -/
theorem forsLeafHash_forsSecret (l : Fin (2 ^ FORS_HEIGHT)) :
    forsLeafHash pp idx kappa l (forsSecret pp seed idx kappa l)
      = forsNode pp seed idx kappa 0 (by decide) l.val := by
  simp only [forsNode, forsIndex_val]

/-! ## The climb reaches level 9 -/

/-- The verifier's node on each level is the signer's, up to level 9. -/
theorem forsClimbUpto_eq_node (l : Nat) :
    ∀ (levels : Nat) (hl : levels ≤ FORS_HEIGHT - 1),
      Internal.forsClimbUpto pp idx kappa l
          (Vector.ofFn fun level : Fin FORS_HEIGHT =>
            forsNode pp seed idx kappa level level.isLt (siblingIndex l level))
          (forsNode pp seed idx kappa 0 (by decide) l) levels hl
        = forsNode pp seed idx kappa levels (by simp only [FORS_HEIGHT] at *; omega)
            (l >>> levels) := by
  intro levels
  induction levels with
  | zero => intro _; rfl
  | succ k ih =>
    intro hl
    -- Below the last step the two sides agree by the induction hypothesis.
    simp only [Internal.forsClimbUpto, ih (by omega)]
    simp only [Vector.getElem_ofFn, Internal.forsClimbStep, forsNode_succ k (by omega)]
    have hhalf : l >>> (k + 1) = (l >>> k) / 2 := Nat.shiftRight_succ _ _
    rcases Nat.mod_two_eq_zero_or_one (l >>> k) with hr | hr
    · -- Bit `k` is zero, so the path node is the right child.
      have hb : 2 * (l >>> (k + 1)) + 1 = siblingIndex l k := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      have ha : 2 * (l >>> (k + 1)) = l >>> k := by
        rw [hhalf]
        omega
      rw [hb, ha]
      simp [hr]
    · -- Bit `k` is one, so the path node is the left child.
      have hb : 2 * (l >>> (k + 1)) + 1 = l >>> k := by
        rw [hhalf]
        omega
      have ha : 2 * (l >>> (k + 1)) = siblingIndex l k := by
        rw [hhalf]
        simp only [siblingIndex, xor_one]
        omega
      rw [hb, ha]
      simp [hr]

/-! ## An honest opening leads to the FORS key -/

/-- An honest opening of one tree recovers the tree's two level-9 nodes, in order. -/
theorem treeRecover_treeOpen (l : Fin (2 ^ FORS_HEIGHT)) :
    treeRecover pp idx kappa l (treeOpen pp seed idx kappa l)
      = (forsNode pp seed idx kappa (FORS_HEIGHT - 1) (by decide) 0,
          forsNode pp seed idx kappa (FORS_HEIGHT - 1) (by decide) 1) := by
  -- Step 1: the revealed leaf is the honest one, and the climb reaches level 9.
  have hclimb := forsClimbUpto_eq_node (pp := pp) (seed := seed) (idx := idx) (kappa := kappa)
    l.val (FORS_HEIGHT - 1) (Nat.le_refl _)
  simp only [treeRecover, treeOpen, forsLeafHash_forsSecret]
  rw [hclimb]
  simp only [Vector.getElem_ofFn, siblingIndex]
  -- Step 2: a leaf below `2^10` has a level-9 ancestor of index 0 or 1.
  have hl : l.val < 1024 := l.isLt
  have htop : l.val >>> (FORS_HEIGHT - 1) < 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    show l.val / 512 < 2
    omega
  -- Step 3: bit 9 puts the reached node and the other one in order.
  obtain h | h : l.val >>> (FORS_HEIGHT - 1) = 0 ∨ l.val >>> (FORS_HEIGHT - 1) = 1 := by
    generalize l.val >>> (FORS_HEIGHT - 1) = t at htop
    omega
  · simp only [h]
    rfl
  · simp only [h]
    rfl

/-- Honest openings of every tree recover the instance's FORS key. -/
theorem forsRecover_forsSign (leaves : Vector (Fin (2 ^ FORS_HEIGHT)) FORS_TREES) :
    forsRecover pp idx leaves (forsSign pp seed idx leaves) = forsKey pp seed idx := by
  -- Tree by tree, the opening recovers the tree's part of the key.
  unfold forsRecover forsSign forsKey
  refine Vector.ext fun k hk => ?_
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hopen : (Vector.ofFn fun kappa => treeOpen pp seed idx kappa leaves[kappa])[(⟨k, hk⟩ : Fin _)]
      = treeOpen pp seed idx ⟨k, hk⟩ leaves[(⟨k, hk⟩ : Fin _)] := by
    rw [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [hopen]
  exact treeRecover_treeOpen _

end EthLib.Cryptography.Sphincs

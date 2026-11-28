module

public import EthLib.Cryptography.ScalarProduct
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.Module

/-!
# Proofs: the scalar product of a curve point

The NAF method gives `k P` and `k P + l Q` from any doubling and addition that follow a group law.

The curves prove their law once, and these theorems give their scalar product.
-/

@[expose] public section

namespace EthLib.Cryptography.ScalarProduct

variable {α β G : Type} [AddCommGroup G]

/-! ## A change of representation -/

section Map

variable (f : α → β) {double : α → α} {add : α → α → α} {double' : β → β} {add' : β → β → β}
  (hd : ∀ q, f (double q) = double' (f q)) (ha : ∀ q r, f (add q r) = add' (f q) (f r))
include hd ha

omit hd in
/-- A map that commutes with the addition commutes with the addition of a digit. -/
theorem map_addDigit (p np : α) (kc hc : List Nat) (i : Nat) (q : α) :
    f (addDigit add p np kc hc i q) = addDigit add' (f p) (f np) kc hc i (f q) := by
  unfold addDigit
  cases bit hc i <;> cases bit kc i <;> simp only [ha]

/-- A map that commutes with the doubling and the addition commutes with the steps. -/
theorem map_jointSteps (p np q nq : α) (kc hc lc hc' : List Nat) (n : Nat) (acc : α) :
    f (jointSteps double add p np q nq kc hc lc hc' n acc) =
      jointSteps double' add' (f p) (f np) (f q) (f nq) kc hc lc hc' n (f acc) := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp only [jointSteps, ih, map_addDigit f ha, hd]

/-- A map that commutes with the doubling and the addition commutes with the joint product. -/
theorem map_joint (zero p np q nq : α) (k l : Nat) :
    f (joint double add zero p np q nq k l) =
      joint double' add' (f zero) (f p) (f np) (f q) (f nq) k l :=
  map_jointSteps f hd ha p np q nq _ _ _ _ _ zero

/-- A map that commutes with the doubling and the addition commutes with the scalar product. -/
theorem map_naf (zero p np : α) (k : Nat) :
    f (naf double add zero p np k) = naf double' add' (f zero) (f p) (f np) k :=
  map_joint f hd ha zero p np zero zero k 0

end Map

/-! ## The bits of the limbs -/

/-- The limbs of a number give back its bits. -/
theorem bit_limbs (n i : Nat) : bit (limbs n) i = n.testBit i := by
  unfold bit limbs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i / 62 < n.log2 / 62 + 1
  · rw [List.getElem?_range h, Option.map_some, Option.getD_some, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, decide_eq_true (Nat.mod_lt i (by norm_num)), Bool.true_and,
      Nat.div_add_mod]
  · rw [List.getElem?_eq_none (by simpa using h), Option.map_none, Option.getD_none,
      Nat.zero_testBit]
    -- Above the top limb, `i` is above the top bit of `n`.
    have hlt : n.log2 < i := by omega
    exact (Nat.testBit_lt_two_pow
      (lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) hlt))).symm

/-! ## The group law -/

/-- The difference of the quotients of `h` and `k` by `2^i`, as an integer. -/
private def quotDiff (k h i : Nat) : ℤ := ((h / 2 ^ i : Nat) : ℤ) - ((k / 2 ^ i : Nat) : ℤ)

/-- The quotient by `2^i` is twice the quotient by `2^(i+1)`, plus bit `i`. -/
private theorem div_two_pow_eq (x i : Nat) :
    ((x / 2 ^ i : Nat) : ℤ) = 2 * ((x / 2 ^ (i + 1) : Nat) : ℤ) + ((x.testBit i).toNat : ℤ) := by
  have h1 : x / 2 ^ (i + 1) = x / 2 ^ i / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [h1, Nat.toNat_testBit]
  omega

/-- The difference at `i` is twice the difference at `i + 1`, plus digit `i`. -/
private theorem quotDiff_eq (k h i : Nat) :
    quotDiff k h i = 2 * quotDiff k h (i + 1) +
      (((h.testBit i).toNat : ℤ) - ((k.testBit i).toNat : ℤ)) := by
  rw [quotDiff, quotDiff, div_two_pow_eq h i, div_two_pow_eq k i]
  ring

/-- Above the top bit of `3k`, both quotients vanish. -/
private theorem quotDiff_top (k n : Nat) (hn : (3 * k).log2 ≤ n) :
    quotDiff k (3 * k) (n + 1) = 0 := by
  have hlt : 3 * k < 2 ^ (n + 1) :=
    lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [quotDiff, Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (by omega : k < 2 ^ (n + 1))]
  simp

/-- At `1`, the difference of the quotients of `3k` and `k` is `k`. -/
private theorem quotDiff_one (k : Nat) : quotDiff k (3 * k) 1 = k := by
  simp only [quotDiff, pow_one]
  omega

section Law

variable (valid : α → Prop) (toPoint : α → G) {double : α → α} {add : α → α → α}
  (hd : ∀ q, valid q → valid (double q) ∧ toPoint (double q) = toPoint q + toPoint q)
  (ha : ∀ q r, valid q → valid r → valid (add q r) ∧ toPoint (add q r) = toPoint q + toPoint r)
include ha

/-- Adding a digit keeps a valid accumulator valid, and adds the digit times `p`. -/
private theorem addDigit_spec {p np : α} (hp : valid p) (hnp : valid np)
    (hneg : toPoint np = -toPoint p) (k h i : Nat) {q : α} (hq : valid q) :
    valid (addDigit add p np (limbs k) (limbs h) i q) ∧
      toPoint (addDigit add p np (limbs k) (limbs h) i q) =
        toPoint q + (((h.testBit i).toNat : ℤ) - ((k.testBit i).toNat : ℤ)) • toPoint p := by
  unfold addDigit
  rw [bit_limbs, bit_limbs]
  cases h.testBit i <;> cases k.testBit i
  · exact ⟨hq, by simp⟩
  · refine ⟨(ha _ _ hq hnp).1, ?_⟩
    rw [(ha _ _ hq hnp).2, hneg]
    simp [sub_eq_add_neg]
  · refine ⟨(ha _ _ hq hp).1, ?_⟩
    rw [(ha _ _ hq hp).2]
    simp
  · exact ⟨hq, by simp⟩

include hd

/-- The steps from `acc` give `2^n acc`, plus the digits read so far times `p` and `q`. -/
private theorem jointSteps_spec {p np q nq : α} (hp : valid p) (hnp : valid np)
    (hneg : toPoint np = -toPoint p) (hq : valid q) (hnq : valid nq)
    (hnegq : toPoint nq = -toPoint q) (k h l h' n : Nat) {acc : α} (hacc : valid acc) :
    valid (jointSteps double add p np q nq (limbs k) (limbs h) (limbs l) (limbs h') n acc) ∧
      toPoint (jointSteps double add p np q nq (limbs k) (limbs h) (limbs l) (limbs h') n acc) =
        (2 ^ n : ℤ) • toPoint acc +
        (quotDiff k h 1 - 2 ^ n * quotDiff k h (n + 1)) • toPoint p +
        (quotDiff l h' 1 - 2 ^ n * quotDiff l h' (n + 1)) • toPoint q := by
  induction n generalizing acc with
  | zero => exact ⟨hacc, by simp [jointSteps]⟩
  | succ n ih =>
    obtain ⟨hdv, hdp⟩ := hd acc hacc
    obtain ⟨h1v, h1p⟩ := addDigit_spec valid toPoint ha hp hnp hneg k h (n + 1) hdv
    obtain ⟨h2v, h2p⟩ := addDigit_spec valid toPoint ha hq hnq hnegq l h' (n + 1) h1v
    obtain ⟨hv, hpt⟩ := ih h2v
    refine ⟨hv, ?_⟩
    simp only [jointSteps]
    rw [hpt, h2p, h1p, hdp, quotDiff_eq k h (n + 1), quotDiff_eq l h' (n + 1), pow_succ]
    module

/-- The joint product of valid points is valid, and it is `k p + l q` in the group. -/
theorem joint_spec {zero p np q nq : α} (hz : valid zero) (hz' : toPoint zero = 0)
    (hp : valid p) (hnp : valid np) (hneg : toPoint np = -toPoint p) (hq : valid q)
    (hnq : valid nq) (hnegq : toPoint nq = -toPoint q) (k l : Nat) :
    valid (joint double add zero p np q nq k l) ∧
      toPoint (joint double add zero p np q nq k l) = k • toPoint p + l • toPoint q := by
  obtain ⟨hv, hpt⟩ := jointSteps_spec valid toPoint hd ha hp hnp hneg hq hnq hnegq k (3 * k) l
    (3 * l) (max (3 * k).log2 (3 * l).log2) hz
  refine ⟨hv, ?_⟩
  rw [joint, hpt, hz', smul_zero, zero_add, quotDiff_top k _ (le_max_left _ _),
    quotDiff_top l _ (le_max_right _ _), quotDiff_one, quotDiff_one, mul_zero, sub_zero,
    sub_zero, natCast_zsmul, natCast_zsmul]

/-- The scalar product of a valid point is valid, and it is the action of `ℕ` on the group. -/
theorem naf_spec {zero p np : α} (hz : valid zero) (hz' : toPoint zero = 0) (hp : valid p)
    (hnp : valid np) (hneg : toPoint np = -toPoint p) (k : Nat) :
    valid (naf double add zero p np k) ∧ toPoint (naf double add zero p np k) = k • toPoint p := by
  obtain ⟨hv, hpt⟩ := joint_spec valid toPoint hd ha hz hz' hp hnp hneg hz hz
    (by rw [hz', neg_zero]) k 0
  exact ⟨hv, hpt.trans (by rw [zero_smul, add_zero])⟩

end Law

end EthLib.Cryptography.ScalarProduct

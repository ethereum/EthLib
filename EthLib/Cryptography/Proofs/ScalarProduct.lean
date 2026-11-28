module

public import EthLib.Cryptography.ScalarProduct
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.Module

/-!
# Proofs: the scalar product of a curve point

The binary NAF method gives `k P` from any doubling and addition that follow a group law.

The curves prove their law once, and these theorems give their scalar product.
-/

@[expose] public section

namespace EthLib.Cryptography.ScalarProduct

variable {α β G : Type} [AddCommGroup G]

/-! ## A change of representation -/

/-- A map that commutes with the doubling and the addition commutes with the steps. -/
theorem map_nafSteps (f : α → β) {double : α → α} {add : α → α → α} {double' : β → β}
    {add' : β → β → β} (hd : ∀ q, f (double q) = double' (f q))
    (ha : ∀ q r, f (add q r) = add' (f q) (f r)) (p np : α) (k h n : Nat) (q : α) :
    f (nafSteps double add p np k h n q) = nafSteps double' add' (f p) (f np) k h n (f q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [nafSteps]
    rw [ih]
    split <;> simp only [ha, hd]

/-- A map that commutes with the doubling and the addition commutes with the scalar product. -/
theorem map_naf (f : α → β) {double : α → α} {add : α → α → α} {double' : β → β}
    {add' : β → β → β} (hd : ∀ q, f (double q) = double' (f q))
    (ha : ∀ q r, f (add q r) = add' (f q) (f r)) (zero p np : α) (k : Nat) :
    f (naf double add zero p np k) = naf double' add' (f zero) (f p) (f np) k :=
  map_nafSteps f hd ha p np k _ _ zero

/-! ## The group law -/

/-- The difference of the quotients of `h` and `k` by `2^i`, as an integer. -/
private def quotDiff (k h i : Nat) : ℤ := ((h / 2 ^ i : Nat) : ℤ) - ((k / 2 ^ i : Nat) : ℤ)

/-- The quotient by `2^i` is twice the quotient by `2^(i+1)`, plus bit `i`. -/
private theorem div_two_pow_eq (x i : Nat) :
    ((x / 2 ^ i : Nat) : ℤ) = 2 * ((x / 2 ^ (i + 1) : Nat) : ℤ) + ((x.testBit i).toNat : ℤ) := by
  have h1 : x / 2 ^ (i + 1) = x / 2 ^ i / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [h1, Nat.toNat_testBit]
  omega

/-- The steps keep a valid accumulator valid. -/
theorem valid_nafSteps (valid : α → Prop) {double : α → α} {add : α → α → α}
    (hd : ∀ q, valid q → valid (double q)) (ha : ∀ q r, valid q → valid r → valid (add q r))
    {p np : α} (hp : valid p) (hnp : valid np) (k h n : Nat) {q : α}
    (hq : valid q) : valid (nafSteps double add p np k h n q) := by
  induction n generalizing q with
  | zero => exact hq
  | succ n ih =>
    rw [nafSteps]
    apply ih
    have hdq := hd q hq
    split
    · exact ha _ _ hdq hp
    · exact ha _ _ hdq hnp
    · exact hdq

section Law

variable (valid : α → Prop) (toPoint : α → G) {double : α → α} {add : α → α → α}
  (hd : ∀ q, valid q → valid (double q) ∧ toPoint (double q) = toPoint q + toPoint q)
  (ha : ∀ q r, valid q → valid r → valid (add q r) ∧ toPoint (add q r) = toPoint q + toPoint r)
include hd ha

/-- The steps from `q` give `2^n q` plus the digits read so far, times `p`. -/
private theorem toPoint_nafSteps {p np : α} (hp : valid p) (hnp : valid np)
    (hneg : toPoint np = -toPoint p) (k h n : Nat) {q : α} (hq : valid q) :
    toPoint (nafSteps double add p np k h n q) = (2 ^ n : ℤ) • toPoint q +
      (quotDiff k h 1 - 2 ^ n * quotDiff k h (n + 1)) • toPoint p := by
  induction n generalizing q with
  | zero => simp [nafSteps]
  | succ n ih =>
    rw [nafSteps]
    obtain ⟨hdq, hdp⟩ := hd q hq
    have hq2 : quotDiff k h (n + 1) = 2 * quotDiff k h (n + 1 + 1) +
        (((h.testBit (n + 1)).toNat : ℤ) - ((k.testBit (n + 1)).toNat : ℤ)) := by
      rw [quotDiff, quotDiff, div_two_pow_eq h (n + 1), div_two_pow_eq k (n + 1)]
      ring
    cases hh : h.testBit (n + 1) <;> cases hk : k.testBit (n + 1)
    · rw [ih hdq, hq2, hh, hk, hdp, pow_succ]
      simp only [Bool.toNat_false, Nat.cast_zero, sub_zero, add_zero]
      module
    · rw [ih (ha _ _ hdq hnp).1, (ha _ _ hdq hnp).2, hq2, hh, hk, hneg, hdp, pow_succ]
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one]
      module
    · rw [ih (ha _ _ hdq hp).1, (ha _ _ hdq hp).2, hq2, hh, hk, hdp, pow_succ]
      simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one]
      module
    · rw [ih hdq, hq2, hh, hk, hdp, pow_succ]
      simp only [Bool.toNat_true, Nat.cast_one, sub_self, add_zero]
      module

/-- The scalar product of a valid point is valid, and it is the action of `ℕ` on the group. -/
theorem naf_spec {zero p np : α} (hz : valid zero) (hz' : toPoint zero = 0) (hp : valid p)
    (hnp : valid np) (hneg : toPoint np = -toPoint p) (k : Nat) :
    valid (naf double add zero p np k) ∧ toPoint (naf double add zero p np k) = k • toPoint p := by
  refine ⟨valid_nafSteps valid (fun q hq => (hd q hq).1) (fun q r hq hr => (ha q r hq hr).1)
    hp hnp k _ _ hz, ?_⟩
  rw [naf, toPoint_nafSteps valid toPoint hd ha hp hnp hneg _ _ _ hz, hz', smul_zero, zero_add]
  -- Above the top bit of `3k`, both quotients vanish.
  have hlt : 3 * k < 2 ^ ((3 * k).log2 + 1) := Nat.lt_log2_self
  have htop : quotDiff k (3 * k) ((3 * k).log2 + 1) = 0 := by
    rw [quotDiff, Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (by omega : k < 2 ^ ((3 * k).log2 + 1))]
    simp
  have hone : quotDiff k (3 * k) 1 = k := by
    simp only [quotDiff, pow_one]
    omega
  rw [htop, hone, mul_zero, sub_zero, natCast_zsmul]

end Law

end EthLib.Cryptography.ScalarProduct

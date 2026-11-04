module

public import EthLib.Cryptography.Proofs.AltBn128.Curve
public import EthLib.Cryptography.Proofs.Pratt
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Proofs: the order of `G_1`

[EIP-197](https://eips.ethereum.org/EIPS/eip-197) §"Definition of the groups" defines `G_1` and `q`.

The curve over `Fp` has exactly `q` points, so `G_1` is the whole group.

The kernel computes `q P1 = O`, so `q` divides the number of points.

At most `2 p + 1 < 3 q` points exist, so the count is `q` or `2 q`.

A count of `2 q` needs a point `(x, 0)` with `x^3 = -3`.

Euler's criterion rules it out: `(-3)^((p - 1) / 3) != 1`, since `p = 1 mod 3`.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

open WeierstrassCurve

-- The kernel computes powers and multiples of 256-bit numbers, deeper than the default.
set_option maxRecDepth 8000

namespace Point

/-! ## The order of `P1` -/

/-- The generator is on the curve. -/
theorem isOnCurve_generator : generator.isOnCurve = true := by decide +kernel

/-- `q P1 = O`, as the kernel computes it by double and add. -/
theorem mulBits_order_generator : mulBits 256 Fr.modulus generator = infinity := by decide +kernel

/-- `P1` is not the point at infinity. -/
theorem toPoint_generator_ne_zero : toPoint generator ≠ 0 := fun h =>
  absurd ((toPoint_eq_zero isOnCurve_generator).mp h) (by decide)

/-- `P1` has order `q`, a prime. -/
theorem addOrderOf_generator : addOrderOf (toPoint generator) = Fr.modulus := by
  refine addOrderOf_eq_prime ?_ toPoint_generator_ne_zero
  rw [← toPoint_mulBits 256 _ isOnCurve_generator (by decide), mulBits_order_generator]
  rfl

end Point

/-! ## At most `2 p + 1` points

Over the field `ZMod p`, a point is fixed by its `x` and the parity of its `y`.

The equation leaves two roots `y` and `-y`, and they have opposite parities, since `p` is odd. -/

/-- `y` and `-y` have opposite parities, unless `y = 0`. -/
theorem val_neg_mod_two {y : ZMod Fp.modulus} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 := by
  rw [ZMod.neg_val, ite_eq_right hy]
  have hlt := ZMod.val_lt y
  have hodd : Fp.modulus % 2 = 1 := by decide
  omega

/-- Two points of the curve with the same `x` and the same parity of `y` are equal. -/
theorem y_eq_of_parity {x y1 y2 : ZMod Fp.modulus} (h1 : y1 * y1 = x * x * x + 3)
    (h2 : y2 * y2 = x * x * x + 3) (hpar : y1.val % 2 = y2.val % 2) : y1 = y2 := by
  rcases Fp.eq_or_eq_neg_of_mul_self (h2.trans h1.symm) with h | h
  · exact h.symm
  · by_cases hy : y1 = 0
    · rw [h, hy, neg_zero]
    · exact absurd (h ▸ hpar.symm) (val_neg_mod_two hy)

/-- A group element as its `x` and the parity of its `y`, or `none` for `0`. -/
def pointCode : curve.Point → Option (ZMod Fp.modulus × Bool)
  | 0 => none
  | .some x y _ => some (x, decide (y.val % 2 = 1))

theorem pointCode_injective : Function.Injective pointCode := by
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some => cases h
  | some x1 y1 h1 => cases Q with
    | zero => cases h
    | some x2 y2 h2 =>
      simp only [pointCode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hb⟩ := h
      have hpar : y1.val % 2 = y2.val % 2 := by
        have := decide_eq_decide.mp hb
        omega
      have := y_eq_of_parity ((equation_iff _ _).mp h1.1) ((equation_iff _ _).mp h2.1) hpar
      subst this
      rfl

instance : Finite curve.Point := Finite.of_injective _ pointCode_injective

theorem card_point_le : Nat.card curve.Point ≤ 2 * Fp.modulus + 1 := by
  have := Nat.card_le_card_of_injective _ pointCode_injective
  rwa [Finite.card_option, Nat.card_prod, Nat.card_zmod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    mul_comm] at this

/-! ## No point of order 2 -/

/-- `-3` is not a cube mod `p`, so `x^3 + 3` has no root in `Fp`. -/
theorem cube_ne_neg_three (x : ZMod Fp.modulus) : x * x * x ≠ -3 := by
  intro h
  have hx : x ≠ 0 := by
    rintro rfl
    exact absurd h (by decide)
  -- A cube `-3 = x^3` gives `(-3)^((p - 1) / 3) = x^(p - 1) = 1`.
  have hpow : ((Fp.modulus - 3 : Nat) : ZMod Fp.modulus) ^ ((Fp.modulus - 1) / 3) = 1 := by
    rw [show ((Fp.modulus - 3 : Nat) : ZMod Fp.modulus) = -3 by decide, ← h, show x * x * x = x ^ 3 by ring,
      ← pow_mul,
      show 3 * ((Fp.modulus - 1) / 3) = Fp.modulus - 1 by decide]
    exact ZMod.pow_card_sub_one_eq_one hx
  -- The kernel computes that power, and it is not `1`.
  rw [PowMod.natCast_pow_eq_one_iff _ 256 _ _ (by decide)] at hpow
  exact absurd hpow (by decide)

/-- No point has order 2. -/
theorem addOrderOf_ne_two (X : curve.Point) : addOrderOf X ≠ 2 := by
  intro h
  have h2 : (2 : Nat) • X = 0 := h ▸ addOrderOf_nsmul_eq_zero X
  cases X with
  | zero => rw [← Affine.Point.zero_def, addOrderOf_zero] at h; omega
  | some x y hn =>
    -- `2 X = 0` makes `X = -X`, so `y = -y`, so `y = 0`, and then `x^3 = -3`.
    have hneg : Affine.Point.some x y hn = -Affine.Point.some x y hn := by
      rw [two_nsmul] at h2
      exact eq_neg_of_add_eq_zero_left h2
    rw [Affine.Point.neg_some, Affine.Point.some.injEq, negY_eq] at hneg
    have hy : y = 0 := by
      have : 2 * y = 0 := by linear_combination hneg.2
      exact (mul_eq_zero.mp this).resolve_left (by decide)
    have he := (equation_iff x y).mp hn.1
    rw [hy] at he
    exact cube_ne_neg_three x (by linear_combination -he)

/-! ## Exactly `q` points -/

/-- The group of alt_bn128 over `Fp` has `q` points: the cofactor is 1. -/
theorem card_point : Nat.card curve.Point = Fr.modulus := by
  obtain ⟨m, hm⟩ : Fr.modulus ∣ Nat.card curve.Point :=
    Point.addOrderOf_generator ▸ addOrderOf_dvd_natCard _
  have hle := card_point_le
  have hpos : 0 < Nat.card curve.Point := Nat.card_pos
  -- `2 p + 1 < 3 q`, so `m` is 1 or 2.
  have hlt : 2 * Fp.modulus + 1 < 3 * Fr.modulus := by decide
  have hm2 : m ≤ 2 := by
    by_contra hc
    have : Fr.modulus * 3 ≤ Fr.modulus * m := Nat.mul_le_mul_left _ (by omega)
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl
  · simpa using hm
  · -- `m = 2` would give a point of order 2.
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨X, hX⟩ := exists_prime_addOrderOf_dvd_card' 2 (hm ▸ dvd_mul_left 2 _)
    exact absurd hX (addOrderOf_ne_two X)

/-- `q X = 0` for every point `X`. -/
theorem nsmul_order (X : curve.Point) : Fr.modulus • X = 0 :=
  card_point ▸ card_nsmul_eq_zero'

/-- The scalars `ZMod q` act on the group, since `q X = 0`. -/
instance : Module (ZMod Fr.modulus) curve.Point := AddCommGroup.zmodModule nsmul_order

/-- A scalar acts through its value. -/
theorem smul_eq_val_nsmul (k : ZMod Fr.modulus) (X : curve.Point) : k • X = k.val • X := rfl

namespace Point

/-- `q P = O` for every point on the curve.

So the subgroup check of ECPAIRING accepts every point of the curve over `Fp`. -/
theorem mulBits_order {p : Point} (hp : p.isOnCurve = true) : mulBits 256 Fr.modulus p = infinity := by
  rw [← toPoint_eq_zero (isOnCurve_mulBits _ _ hp), toPoint_mulBits _ _ hp (by decide)]
  exact nsmul_order _

/-- Every point on the curve is `k P1` for one `k < q`. -/
theorem exists_eq_mulBits_generator {p : Point} (hp : p.isOnCurve = true) :
    ∃ k < Fr.modulus, p = mulBits 256 k generator := by
  -- `P1` has order `q`, the size of the group, so its multiples are the whole group.
  have htop : AddSubgroup.zmultiples (toPoint generator) = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, addOrderOf_generator, card_point])
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (htop ▸ AddSubgroup.mem_top (toPoint p))
  have hlt : (k : ZMod Fr.modulus).val < Fr.modulus := ZMod.val_lt _
  refine ⟨(k : ZMod Fr.modulus).val, hlt, ?_⟩
  refine ((toPoint_inj hp (isOnCurve_mulBits _ _ isOnCurve_generator)).mp ?_)
  rw [toPoint_mulBits _ _ isOnCurve_generator (lt_trans hlt (by decide)), ← smul_eq_val_nsmul, ← hk]
  exact (Int.cast_smul_eq_zsmul (ZMod Fr.modulus) k _).symm

end Point

end EthLib.Cryptography.AltBn128

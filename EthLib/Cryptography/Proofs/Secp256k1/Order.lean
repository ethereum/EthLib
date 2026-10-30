import EthLib.Cryptography.Proofs.Secp256k1.Curve
import EthLib.Cryptography.Proofs.Pratt
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.OrderOfElement

/-!
# Proofs: the order of secp256k1

The group of secp256k1 has exactly `n` points, and `G` generates it.

SEC 2 v2 §2.4.1 states this as the order `n` of `G` and the cofactor `h = 1`.

The proof has three steps.

- The kernel runs `n G` and gets `O`, so `G` has order `n`, a prime.
- So `n` divides the number of points.
- At most `2 p + 1` points exist, fewer than `3 n`, so the count is `n` or `2 n`.

A group of `2 n` points would hold a point of order 2, which is `(x, 0)` with `x^3 = -7`.

No such `x` exists, because `-7` is not a cube mod `p`.

The kernel checks that by Euler's criterion: `(-7)^((p - 1) / 3) != 1`, since `p = 1 mod 3`.

With `n` points, `n X = 0` for every point `X`, so the scalars of `Fn` act on the group.

- `card_point`: the group has `n` points.
- `nsmul_order`: `n X = 0` for every point.
- `toPoint_mul'`: `mul k P` is `k P` with `k` in `ZMod n`.
- `exists_eq_mul_generator`: every point on the curve is `k G` for some scalar `k`.
-/

namespace EthLib.Cryptography.Secp256k1

open WeierstrassCurve

-- The kernel computes powers and multiples of 256-bit numbers, deeper than the default.
set_option maxRecDepth 8000

namespace Point

/-! ## The order of `G` -/

/-- The base point is on the curve. -/
theorem isOnCurve_generator : generator.isOnCurve = true := by decide +kernel

/-- `n G = O`, as the kernel computes it by double and add. -/
theorem mulBits_order_generator : mulBits 256 Fn.modulus generator = infinity := by decide +kernel

/-- `G` is not the point at infinity. -/
theorem toPoint_generator_ne_zero : toPoint generator ≠ 0 := fun h =>
  absurd ((toPoint_eq_zero isOnCurve_generator).mp h) (by decide)

/-- `G` has order `n`, a prime. -/
theorem addOrderOf_generator : addOrderOf (toPoint generator) = Fn.modulus := by
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
theorem y_eq_of_parity {x y1 y2 : ZMod Fp.modulus} (h1 : y1 * y1 = x * x * x + 7)
    (h2 : y2 * y2 = x * x * x + 7) (hpar : y1.val % 2 = y2.val % 2) : y1 = y2 := by
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

/-- `-7` is not a cube mod `p`. -/
theorem cube_ne_neg_seven (x : ZMod Fp.modulus) : x * x * x ≠ -7 := by
  intro h
  have hx : x ≠ 0 := by
    rintro rfl
    exact absurd h (by decide)
  -- A cube `-7 = x^3` gives `(-7)^((p - 1) / 3) = x^(p - 1) = 1`.
  have hpow : ((Fp.modulus - 7 : Nat) : ZMod Fp.modulus) ^ ((Fp.modulus - 1) / 3) = 1 := by
    rw [show ((Fp.modulus - 7 : Nat) : ZMod Fp.modulus) = -7 by decide, ← h, show x * x * x = x ^ 3 by ring,
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
    -- `2 X = 0` makes `X = -X`, so `y = -y`, so `y = 0`, and then `x^3 = -7`.
    have hneg : Affine.Point.some x y hn = -Affine.Point.some x y hn := by
      rw [two_nsmul] at h2
      exact eq_neg_of_add_eq_zero_left h2
    rw [Affine.Point.neg_some, Affine.Point.some.injEq, negY_eq] at hneg
    have hy : y = 0 := by
      have : 2 * y = 0 := by linear_combination hneg.2
      exact (mul_eq_zero.mp this).resolve_left (by decide)
    have he := (equation_iff x y).mp hn.1
    rw [hy] at he
    exact cube_ne_neg_seven x (by linear_combination -he)

/-! ## Exactly `n` points -/

/-- The group of secp256k1 has `n` points: the cofactor is 1. -/
theorem card_point : Nat.card curve.Point = Fn.modulus := by
  obtain ⟨m, hm⟩ : Fn.modulus ∣ Nat.card curve.Point :=
    Point.addOrderOf_generator ▸ addOrderOf_dvd_natCard _
  have hle := card_point_le
  have hpos : 0 < Nat.card curve.Point := Nat.card_pos
  -- `2 p + 1 < 3 n`, so `m` is 1 or 2.
  have hlt : 2 * Fp.modulus + 1 < 3 * Fn.modulus := by decide
  have hm2 : m ≤ 2 := by
    by_contra hc
    have : Fn.modulus * 3 ≤ Fn.modulus * m := Nat.mul_le_mul_left _ (by omega)
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

/-- `n X = 0` for every point `X`. -/
theorem nsmul_order (X : curve.Point) : Fn.modulus • X = 0 :=
  card_point ▸ card_nsmul_eq_zero'

/-- The scalars `ZMod n` act on the group, since `n X = 0`. -/
instance : Module (ZMod Fn.modulus) curve.Point := AddCommGroup.zmodModule nsmul_order

/-- A scalar acts through its value. -/
theorem smul_eq_val_nsmul (k : ZMod Fn.modulus) (X : curve.Point) : k • X = k.val • X := rfl

namespace Point

/-- `mul k P` is `k P`, with `k` in `ZMod n`. -/
theorem toPoint_mul' (k : Fn) {p : Point} (hp : p.isOnCurve = true) :
    toPoint (mul k p) = Fn.toZMod k • toPoint p :=
  toPoint_mul k hp

/-- Every point on the curve is `k G` for one scalar `k`: every public key has a private key. -/
theorem exists_eq_mul_generator {p : Point} (hp : p.isOnCurve = true) : ∃ k : Fn, p = mul k generator := by
  -- `G` has order `n`, the size of the group, so its multiples are the whole group.
  have htop : AddSubgroup.zmultiples (toPoint generator) = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, addOrderOf_generator, card_point])
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (htop ▸ AddSubgroup.mem_top (toPoint p))
  refine ⟨Fn.toZMod.symm k, ((toPoint_inj hp (isOnCurve_mul _ isOnCurve_generator)).mp ?_)⟩
  rw [toPoint_mul' _ isOnCurve_generator, RingEquiv.apply_symm_apply, ← hk]
  exact (Int.cast_smul_eq_zsmul (ZMod Fn.modulus) k _).symm

end Point

end EthLib.Cryptography.Secp256k1

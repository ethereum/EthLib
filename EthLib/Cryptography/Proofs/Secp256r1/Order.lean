module

public import EthLib.Cryptography.Proofs.Secp256r1.Curve
public import Mathlib.Algebra.Module.ZMod

/-!
# Proofs: the order of secp256r1

The group of secp256r1 has exactly `n` points, and `G` generates it.

SEC 2 v2 §2.4.2 states this as the order `n` of `G` and the cofactor `h = 1`.

The proof has three steps.

- The kernel runs `n G` and gets `O`, so `G` has order `n`, a prime.
- So `n` divides the number of points.
- At most `2 p + 1` points exist, fewer than `3 n`, so the count is `n` or `2 n`.

A group of `2 n` points would hold a point of order 2, which is `(x, 0)` with `f(x) = 0` for `f = X^3 + a X + b`.

No such `x` exists, since `X^p - X` and `f` have no common factor in `Fp[X]`.

Every `x` of `Fp` is a root of `X^p - X`, so a root of `f` would be a common root.

The kernel computes `X^p mod f` by square and multiply, and checks an inverse of `X^p - X` mod `f`.

With `n` points, `n X = 0` for every point `X`, so the scalars of `Fn` act on the group.

- `card_point`: the group has `n` points.
- `nsmul_order`: `n X = 0` for every point.
- `toPoint_mul'`: `mul k P` is `k P` with `k` in `ZMod n`.
- `exists_eq_mul_generator`: every point on the curve is `k G` for some scalar `k`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256r1

open WeierstrassCurve

-- The kernel computes multiples and powers mod 256-bit numbers, deeper than the default.
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

/-! ## No root of `f = X^3 + a X + b`

A residue mod `f` is `c0 + c1 X + c2 X^2`, written as the triple `(c0, c1, c2)`.

The product reduces `X^3` to `-a X - b` and `X^4` to `-a X^2 - b X`.

At a root `x` of `f`, evaluation at `x` respects that product. -/

/-- The product of two residues mod `f`. -/
private def residueMul (s t : Fp × Fp × Fp) : Fp × Fp × Fp :=
  let c0 := s.1 * t.1
  let c1 := s.1 * t.2.1 + s.2.1 * t.1
  let c2 := s.1 * t.2.2 + s.2.1 * t.2.1 + s.2.2 * t.1
  let c3 := s.2.1 * t.2.2 + s.2.2 * t.2.1
  let c4 := s.2.2 * t.2.2
  (c0 - b * c3, c1 - a * c3 - b * c4, c2 - a * c4)

/-- `s^e` mod `f`, for `e < 2^fuel`, by square and multiply. -/
private def residuePow : Nat → Fp × Fp × Fp → Nat → Fp × Fp × Fp
  | 0, _, _ => (1, 0, 0)
  | fuel + 1, s, e =>
    let half := residuePow fuel (residueMul s s) (e / 2)
    if e % 2 = 1 then residueMul s half else half

/-- The value of a residue at `x`. -/
private def residueEval (x : ZMod Fp.modulus) (s : Fp × Fp × Fp) : ZMod Fp.modulus :=
  Fp.toZMod s.1 + Fp.toZMod s.2.1 * x + Fp.toZMod s.2.2 * x * x

private theorem residueEval_mul {x : ZMod Fp.modulus} (hx : x * x * x + Fp.toZMod a * x + Fp.toZMod b = 0)
    (s t : Fp × Fp × Fp) : residueEval x (residueMul s t) = residueEval x s * residueEval x t := by
  simp only [residueEval, residueMul, map_add, map_sub, map_mul]
  linear_combination (-(Fp.toZMod s.2.1 * Fp.toZMod t.2.2 + Fp.toZMod s.2.2 * Fp.toZMod t.2.1)
    - Fp.toZMod s.2.2 * Fp.toZMod t.2.2 * x) * hx

private theorem residueEval_pow {x : ZMod Fp.modulus} (hx : x * x * x + Fp.toZMod a * x + Fp.toZMod b = 0)
    (fuel : Nat) (s : Fp × Fp × Fp) (e : Nat) (he : e < 2 ^ fuel) :
    residueEval x (residuePow fuel s e) = residueEval x s ^ e := by
  induction fuel generalizing s e with
  | zero =>
    obtain rfl : e = 0 := by simpa using he
    simp [residuePow, residueEval]
  | succ fuel ih =>
    have h2 : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at he; omega
    -- `s^e = s^(e mod 2) * (s^2)^(e / 2)`.
    simp only [residuePow]
    split_ifs with h
    · rw [residueEval_mul hx, ih _ _ h2, residueEval_mul hx, ← pow_two, ← pow_mul, ← pow_succ']
      congr 1
      omega
    · rw [ih _ _ h2, residueEval_mul hx, ← pow_two, ← pow_mul]
      congr 1
      omega

/-- An inverse of `X^p - X` mod `f`, computed outside Lean and checked by the kernel. -/
private def residueInv : Fp × Fp × Fp :=
  (0xa969487079f1744798bf0de6fded091b66e9d328eb0645fe5d979d1339b7f47f,
    0xa4a08891884100c13323460107a8d28eede4387fa3e6e9bfebec9f6d72d0b5cc,
    0x4cde11cf86cb876cd59cf0115813c55af0ecd3cda667d98bb9a347a56aa74a6d)

/-- `X^p - X` mod `f`. -/
private def frobeniusSubX : Fp × Fp × Fp :=
  let g := residuePow 256 (0, 1, 0) Fp.modulus
  (g.1, g.2.1 - 1, g.2.2)

/-- The kernel computes `X^p mod f` and checks that `X^p - X` is invertible mod `f`. -/
private theorem residueInv_mul : residueMul residueInv frobeniusSubX = (1, 0, 0) := by decide +kernel

/-- `x^3 + a x + b` has no root in `Fp`.

At a root `x`, the residue `X^p - X` takes the value `x^p - x = 0`, so it has no inverse mod `f`. -/
theorem cubic_ne_zero (x : ZMod Fp.modulus) : x * x * x + Fp.toZMod a * x + Fp.toZMod b ≠ 0 := by
  intro hx
  have h := congrArg (residueEval x) residueInv_mul
  have hfrob : residueEval x frobeniusSubX = 0 := by
    have hg := residueEval_pow hx 256 (0, 1, 0) Fp.modulus (by decide)
    simp only [residueEval, Fp.toZMod_zero, Fp.toZMod_one, zero_add, one_mul, zero_mul, add_zero] at hg
    simp only [frobeniusSubX, residueEval, Fp.toZMod_sub, Fp.toZMod_one]
    rw [ZMod.pow_card] at hg
    linear_combination hg
  rw [residueEval_mul hx, hfrob, mul_zero] at h
  exact absurd h (by simp [residueEval])

/-! ## Exactly `n` points -/

/-- The group of secp256r1 has `n` points: the cofactor is 1. -/
theorem card_point : Nat.card curve.Point = Fn.modulus :=
  ShortWeierstrass.card_point_eq (by decide) cubic_ne_zero Point.addOrderOf_generator (by decide)

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

end EthLib.Cryptography.Secp256r1

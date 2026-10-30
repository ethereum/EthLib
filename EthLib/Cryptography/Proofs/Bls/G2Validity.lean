module

public import EthLib.Cryptography.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G2Group

/-!
# Proofs: `G2` twist membership and generator validity

This file links `isOnTwist` to `G2.Valid` (Mathlib's `curve.Nonsingular`).

Curve and subgroup parameters follow `IRTF draft-irtf-cfrg-bls-signature-04 §1.3 and Appendix A`.

Twist parameters also match `draft-irtf-cfrg-pairing-friendly-curves-07 §4.2.1`.

`cube_add_bTwist_ne_zero` proves that `x^3 + 4*(1 + i)` has no root in `Fp2`.

Every affine solution `(x, y)` therefore has `y != 0` and nonzero `y`-derivative `2 * y`.

`valid_of_isOnTwist_of_z_one` deduces `Valid` for `z = 1` twist points, certifying `valid_generator` in the kernel.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian
open scoped EthLib.Cryptography.Bls.Fp

/-! ## Twist curve membership -/

/-- Accepts every `z = 0` triple, whereas `Valid` restricts `z = 0` to `![1, 1, 0]` up to scaling. -/
def isOnTwist (p : G2) : Bool :=
  if p.isInfinity then true
  else
    let z2 := p.z * p.z
    let z3 := z2 * p.z
    let z6 := z3 * z3
    p.y * p.y == p.x * p.x * p.x + bTwist * z6

@[simp] theorem isOnTwist_zero : isOnTwist zero = true := by
  decide

/-- Checked in the kernel on the 381-bit `Fp2` generator coordinates. -/
theorem isOnTwist_generator : isOnTwist generator = true := by
  decide +kernel

/-! ## Nonsingularity of affine twist points -/

set_option maxRecDepth 8000 in
set_option exponentiation.threshold 512 in
/-- `32` is not a cube modulo `Fp.modulus`, checked via Euler's cubic criterion. -/
private theorem cube_ne_32_zmod (n : ZMod Fp.modulus) :
    n * n * n ≠ 32 := by
  intro h
  -- Rewrite `n^3 = 32` over `Nat` cast so Fermat's little theorem factors through `3 * ((p - 1) / 3)`.
  have h3 : n ^ 3 = ((32 : Nat) : ZMod Fp.modulus) := by
    have h32 : (32 : ZMod Fp.modulus) = ((32 : Nat) : ZMod Fp.modulus) := by decide
    rw [← h32]
    linear_combination h
  have hn : n ≠ 0 := by
    intro hn0
    rw [hn0] at h
    revert h; decide
  have hfermat : n ^ (Fp.modulus - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one hn
  rw [show Fp.modulus - 1 = 3 * ((Fp.modulus - 1) / 3) by decide,
    pow_mul, h3] at hfermat
  -- The kernel evaluates `32^((p - 1) / 3) mod p` and confirms it is not `1`.
  exact PowMod.natCast_pow_div_ne_one Fp.modulus 384 32 3
    (by decide) (by decide) hfermat

/-- The twist right-hand side `x^3 + bTwist` never vanishes in `Fp2`.

If `x^3 = -4*(1 + i)`, taking norms into `Fp` yields `N(x)^3 = N(-4 - 4*i) = 32`.

Euler's cubic criterion (`32^((p - 1) / 3) != 1 mod p`) rules out any cube equal to `32` in `Fp`.
-/
theorem cube_add_bTwist_ne_zero (x : Fp2) :
    x * x * x + bTwist ≠ 0 := by
  intro h
  -- Take `Fp2.norm` of both sides of `x^3 = -bTwist` to descend into `Fp`.
  have hcube : x * x * x = -bTwist := eq_neg_of_add_eq_zero_left h
  have hnorm : Fp2.norm (x * x * x) = Fp2.norm (-bTwist) := congrArg Fp2.norm hcube
  rw [Fp2.norm_mul, Fp2.norm_mul] at hnorm
  have hbt : (Fp2.norm (-bTwist) : ZMod Fp.modulus) = 32 := by decide
  exact cube_ne_32_zmod (Fp2.norm x) (hnorm.trans hbt)

/-- Because `x^3 + bTwist` has no root, any affine solution has `2 * y != 0` and is nonsingular. -/
theorem valid_of_affine_equation {x y : Fp2}
    (h : y * y = x * x * x + bTwist) : Valid ⟨x, y, Fp2.one⟩ := by
  -- Because `x^3 + bTwist != 0`, `y` cannot be zero.
  have hy : y ≠ 0 := by
    intro hy
    apply cube_add_bTwist_ne_zero x
    rw [← h, hy]
    decide
  have h2 : (2 : Fp2) ≠ 0 := by decide
  show curve.Nonsingular (rep ⟨x, y, Fp2.one⟩)
  rw [nonsingular_iff, equation_iff]
  simp only [show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl,
    show curve.a₆ = bTwist from rfl, rep_x, rep_y, rep_z,
    show Fp2.one = (1 : Fp2) from rfl]
  constructor
  · linear_combination h
  -- Select the `y`-partial derivative `2 * y` of `y^2 - x^3 - bTwist` and show `2 * y != 0`.
  · right
    left
    simpa using _root_.mul_ne_zero h2 hy

/-- Setting `z = 1` rules out the `z = 0` branch where `isOnTwist` is weaker than `Valid`. -/
theorem valid_of_isOnTwist_of_z_one {p : G2}
    (hz : p.z = Fp2.one) (h : isOnTwist p = true) : Valid p := by
  rcases p with ⟨x, y, z⟩
  dsimp only at hz
  subst z
  have heq : y * y = x * x * x + bTwist := by
    simpa [isOnTwist, isInfinity, show (1 : Fp2).isZero = false from rfl] using h
  exact valid_of_affine_equation heq

theorem valid_generator : Valid generator :=
  valid_of_isOnTwist_of_z_one rfl isOnTwist_generator

end EthLib.Cryptography.Bls.G2

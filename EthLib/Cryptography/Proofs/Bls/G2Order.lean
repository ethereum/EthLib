module

public import EthLib.Cryptography.Proofs.Bls.G2Equiv
public import EthLib.Cryptography.Proofs.Bls.FrZMod
public import EthLib.Cryptography.Proofs.Bls.FpModel
public import EthLib.Cryptography.Proofs.Bls.CurveMap

/-!
# Proofs: the order of the `G2` generator and the action of `Fr`

The generator `g_2` has prime order `r`, and scalars mod `r` act on its span.

The curve and the subgroup follow draft-04, §1.3 and Appendix A.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04>

The twist also matches draft-07, §4.2.1.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-07>

- The kernel checks `[r] g_2 = 0` in the model of `Fp`, by double and add on a fuel argument.
- Since `r` is prime and `g_2 != 0`, the order of `g_2` is exactly `r`.
- The map `s ↦ [s] g_2` is linear in `s` modulo `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

set_option maxRecDepth 8000

/-! ## `[r] * g_2 = 0` -/

/-- Fuel-based double-and-add, structurally recursive so the kernel can evaluate it.

The spec's `mulNat` is well-founded recursion, which does not reduce definitionally. -/
def mulNatAux {F : Type} [BaseField F] : Nat → G2 F → Nat → G2 F
  | 0, _, _ => zero
  | fuel + 1, p, k =>
    if k = 0 then zero
    else
      let half := mulNatAux fuel (double p) (k / 2)
      if k % 2 = 1 then add p half else half

theorem mulNatAux_eq (fuel : Nat) (p : G2) (k : Nat)
    (hk : k < 2 ^ fuel) : mulNatAux fuel p k = mulNat p k := by
  induction fuel generalizing p k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst this
    rw [mulNatAux, mulNat_def]
    simp
  | succ fuel ih =>
    rw [mulNatAux, mulNat_def]
    by_cases h0 : k = 0
    · simp [h0]
    · have h2 : k / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hk
        omega
      rw [ite_eq_right h0, ite_eq_right h0, ih (double p) (k / 2) h2]

/-- A map of base fields commutes with the ladder. -/
theorem map_mulNatAux {F G : Type} [BaseField F] [BaseField G] (f : BaseField.Hom F G)
    (fuel : Nat) (p : G2 F) (k : Nat) :
    map f (mulNatAux fuel p k) = mulNatAux fuel (map f p) k := by
  induction fuel generalizing p k with
  | zero => exact map_zero f
  | succ fuel ih =>
    rw [mulNatAux, mulNatAux]
    split
    · exact map_zero f
    · dsimp only
      rw [← map_double, ← ih]
      split
      · exact map_add f _ _
      · rfl

/-- A map of base fields commutes with the sum, written as a function. -/
theorem map_add_fn {F G : Type} [BaseField F] [BaseField G] (f : BaseField.Hom F G)
    (p q : G2 F) : map f (add p q) = add (map f p) (map f q) :=
  map_add f p q

/-- A map of base fields commutes with the negation, written as a function. -/
theorem map_neg_fn {F G : Type} [BaseField F] [BaseField G] (f : BaseField.Hom F G)
    (p : G2 F) : map f (neg p) = neg (map f p) :=
  map_neg f p

/-- A map of base fields keeps the projective equality of two points. -/
theorem map_projectiveEq {F G : Type} [BaseField F] [BaseField G] (f : BaseField.Hom F G)
    (p q : G2 F) : projectiveEq (map f p) (map f q) = projectiveEq p q := by
  simp only [projectiveEq, map, Fp2.map_isZero, ← Fp2.map_mul, Fp2.map_beq]

/-- The test for the point at infinity reads the same on the image in the model. -/
theorem isInfinity_model (p : G2) : p.isInfinity = (map Fp.toModel p).isInfinity :=
  (map_isInfinity Fp.toModel p).symm

/-- The projective equality reads the same on the images in the model. -/
theorem projectiveEq_model (p q : G2) :
    projectiveEq p q = projectiveEq (map Fp.toModel p) (map Fp.toModel q) :=
  (map_projectiveEq Fp.toModel p q).symm

/-- Decides a test on points of `G2` over `Fp` in the model.

The test is one for the point at infinity or for projective equality.

The listed definitions of points are unfolded, and the map is pushed down to their coordinates.

So the kernel computes in the model, on natural numbers. -/
macro "decide_g2_at_model" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [isInfinity_model, projectiveEq_model]
             simp only [map_mulNatAux, map_add_fn, map_neg_fn, map_add, map_neg, map_double,
               map_mk, map_generator, map_zero, Fp2.map_mk, Fp2.map_one, Fp2.map_zero,
               Fp.toModel_ofNat, Fp.toModel_zero, Fp.toModel_one, $ids,*]
             decide +kernel))

/-- `[r]g₂` is the point at infinity.

The kernel runs the ladder in the model, 255 doublings and additions on 381-bit integers. -/
theorem modulus_smul_generator :
    Fr.modulus • toPoint generator = 0 := by
  rw [← toPoint_mulNat valid_generator]
  refine Point.toAffine_of_Z_eq_zero (isZero_iff.mp ?_)
  rw [← mulNatAux_eq 256 generator Fr.modulus (by decide)]
  have h : (mulNatAux 256 (generator : G2 Fp.Model) Fr.modulus).isInfinity = true := by
    decide +kernel
  rwa [← map_generator Fp.toModel, ← map_mulNatAux, map_isInfinity] at h

theorem toPoint_generator_ne_zero : toPoint generator ≠ 0 := by
  -- Because `z = 1 != 0`, `generator` maps to `Point.some ...`, which cannot equal `Point.zero`.
  rw [toPoint, Point.toAffine_of_Z_ne_zero valid_generator
    (by exact fun h => absurd (isZero_iff.mpr h) (by decide))]
  exact fun h => by cases h

/-- Because `r` is prime and `[r] * g_2 = 0` with `g_2 != 0`, the order of `g_2` cannot be `1` and must be `r`. -/
theorem addOrderOf_toPoint_generator :
    addOrderOf (toPoint generator) = Fr.modulus :=
  addOrderOf_eq_prime modulus_smul_generator toPoint_generator_ne_zero

/-! ## The `Fr` action on the `G2` generator subgroup -/

theorem nsmul_generator_mod (k : Nat) :
    k • toPoint generator = (k % Fr.modulus) • toPoint generator := by
  -- Split `k = r * (k / r) + k % r` and annihilate the multiple of `r`.
  conv_lhs => rw [← Nat.div_add_mod k Fr.modulus]
  rw [add_nsmul, Nat.mul_comm Fr.modulus (k / Fr.modulus), mul_nsmul',
      modulus_smul_generator, nsmul_zero]
  simp

/-- Canonical embedding of `Fr` into the subgroup spanned by `G2.generator`. -/
noncomputable def ofFr (s : Fr) : curve.toAffine.Point :=
  s.val • toPoint generator

theorem ofFr_zero : ofFr 0 = 0 := by rw [ofFr, Fr.val_zero, zero_nsmul]

theorem ofFr_one : ofFr 1 = toPoint generator := by rw [ofFr, Fr.val_one, one_nsmul]

/-- Reduction modulo `r` in `Fr` agrees with curve addition because `[r] * g_2 = 0`. -/
theorem ofFr_add (s t : Fr) : ofFr (s + t) = ofFr s + ofFr t := by
  rw [ofFr, ofFr, ofFr, Fr.val_add,
      ← nsmul_generator_mod, add_nsmul]

theorem ofFr_mul (s t : Fr) : ofFr (s * t) = s.val • ofFr t := by
  rw [ofFr, ofFr, Fr.val_mul,
      ← nsmul_generator_mod, mul_nsmul']

theorem toPoint_mul_generator (s : Fr) :
    toPoint (mul generator s) = ofFr s :=
  toPoint_mulNat valid_generator s.val

end EthLib.Cryptography.Bls.G2

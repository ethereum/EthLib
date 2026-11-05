module

public import EthLib.Cryptography.Proofs.Bls.G2Validity
public import EthLib.Cryptography.Proofs.Bls.FrZMod

/-!
# Proofs: the order of the `G2` generator and the action of `Fr`

The generator `g_2` has prime order `r`, and scalars mod `r` act on its span.

The curve and the subgroup follow draft-04, §1.3 and Appendix A.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04>

The twist also matches draft-07, §4.2.1.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-07>

- The kernel checks `[r] g_2 = 0`, by double and add on a fuel argument.
- Since `r` is prime and `g_2 != 0`, the order of `g_2` is exactly `r`.
- The map `s ↦ [s] g_2` is linear in `s` modulo `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Jacobian

set_option maxRecDepth 8000

/-! ## `[r] * g_2 = 0` -/

/-- Fuel-based double-and-add ladder, structurally recursive so the kernel reduces closed calls directly. -/
private def mulNatAux : Nat → G2 → Nat → G2
  | 0, _, _ => zero
  | fuel + 1, p, k =>
    if k = 0 then zero
    else
      let half := mulNatAux fuel (double p) (k / 2)
      if k % 2 = 1 then add p half else half

private theorem mulNatAux_eq (fuel : Nat) (p : G2) (k : Nat)
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

/-- Verified in the kernel across 256 ladder steps over `Fp2`. -/
theorem modulus_smul_generator :
    Fr.modulus • toPoint generator = 0 := by
  rw [← toPoint_mulNat valid_generator]
  refine Point.toAffine_of_Z_eq_zero (isZero_iff.mp ?_)
  -- Replace well-founded `mulNat` with 256 steps of structural `mulNatAux` for kernel evaluation.
  rw [← mulNatAux_eq 256 generator Fr.modulus (by decide)]
  decide

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

module

public import EthLib.Cryptography.Proofs.Bls.G1Group
public import EthLib.Cryptography.Proofs.Bls.FrZMod
public import EthLib.Cryptography.Proofs.Bls.FpModel
public import EthLib.Cryptography.Proofs.Bls.CurveMap
public import EthLib.Cryptography.Proofs.Bls.Fp2

/-!
# Proofs: the order of the `G1` generator and the action of `Fr`

The trusted-setup proofs need three facts about the generator `g_1`.

- The generator is a nonsingular point of the curve, which the kernel checks.
- `[r] g_1 = 0`, which the kernel checks by running double and add.
- The map `s ↦ [s] g_1` is linear in `s`, so scalars mod `r` act on the span of `g_1`.

The double and add runs through a copy that recurses on a fuel argument.

The kernel does not reduce well-founded recursion.

Since `r` is prime and `g_1 ≠ 0`, the order of `g_1` is exactly `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve.Jacobian

set_option maxRecDepth 8000

/-! ## Generator validity -/

/-- The spec's generator is a nonsingular point of the curve. -/
theorem valid_generator : Valid generator :=
  valid_of_affine_eq (by decide_eq_at_model [])

/-! ## `[r]g₁ = 0` -/

/-- Fuel-based double-and-add, structurally recursive so the kernel
can evaluate it (the spec's `mulNat` is well-founded recursion, which
does not reduce definitionally). Correctness: `mulNatAux_eq`. -/
def mulNatAux {F : Type} [BaseField F] : Nat → G1 F → Nat → G1 F
  | 0, _, _ => zero
  | fuel + 1, p, k =>
    if k = 0 then zero
    else
      let half := mulNatAux fuel (double p) (k / 2)
      if k % 2 = 1 then add p half else half

theorem mulNatAux_eq (fuel : Nat) (p : G1) (k : Nat)
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
    (fuel : Nat) (p : G1 F) (k : Nat) :
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

/-- The test for the point at infinity reads the same on the image in the model. -/
theorem isInfinity_model (p : G1) : p.isInfinity = (map Fp.toModel p).isInfinity :=
  (map_isInfinity Fp.toModel p).symm

/-- A map of base fields commutes with the sum, written as a function. -/
theorem map_add_fn {F G : Type} [BaseField F] [BaseField G] (f : BaseField.Hom F G)
    (p q : G1 F) : map f (add p q) = add (map f p) (map f q) :=
  map_add f p q

/-- A map of base fields commutes with the negation, written as a function. -/
theorem map_neg_fn {F G : Type} [BaseField F] [BaseField G] (f : BaseField.Hom F G)
    (p : G1 F) : map f (neg p) = neg (map f p) :=
  map_neg f p

/-- Decides a test for the point at infinity on points of `Fp` in the model.

The listed definitions of points are unfolded, and the map is pushed down to their coordinates.

So the kernel computes in the model, on natural numbers. -/
macro "decide_at_model" "[" ids:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (rw [isInfinity_model]
             simp only [map_mulNatAux, map_add_fn, map_neg_fn, map_mk, Fp.toModel_ofNat,
               Fp.toModel_zero, Fp.toModel_one, $ids,*]
             decide +kernel))

/-- `[r]g₁` is the point at infinity.

The kernel runs the ladder in the model, 255 doublings and additions on 381-bit integers. -/
theorem modulus_smul_generator :
    Fr.modulus • toPoint generator = 0 := by
  rw [← toPoint_mulNat valid_generator]
  refine Point.toAffine_of_Z_eq_zero ?_
  rw [rep_z]
  apply (isZero_iff (a := (generator.mulNat Fr.modulus).z)).mp
  rw [← mulNatAux_eq 256 generator Fr.modulus (by decide)]
  have h : (mulNatAux 256 (generator : G1 Fp.Model) Fr.modulus).isInfinity = true := by
    decide +kernel
  rw [← map_generator Fp.toModel, ← map_mulNatAux, map_isInfinity,
    show ∀ p : G1, p.isInfinity = p.z.isZero from fun _ => rfl] at h
  exact h

/-- The generator is not the identity (its representative has
`z = 1 ≠ 0`, so it maps to an affine point). -/
theorem toPoint_generator_ne_zero : toPoint generator ≠ 0 := by
  rw [toPoint, Point.toAffine_of_Z_ne_zero valid_generator
    (by
      rw [rep_z, show generator.z = Fp.one from rfl, Fp.one_def, Fp.toZMod_one]
      exact one_ne_zero)]
  exact fun h => by cases h

/-- The generator has additive order exactly `r`. -/
theorem addOrderOf_toPoint_generator :
    addOrderOf (toPoint generator) = Fr.modulus :=
  addOrderOf_eq_prime modulus_smul_generator toPoint_generator_ne_zero

/-! ## The `Fr` action on `⟨g₁⟩` -/

/-- Scalar multiples of `g₁` only depend on the scalar mod `r`. -/
theorem nsmul_generator_mod (k : Nat) :
    k • toPoint generator = (k % Fr.modulus) • toPoint generator := by
  conv_lhs => rw [← Nat.div_add_mod k Fr.modulus]
  rw [add_nsmul, Nat.mul_comm Fr.modulus (k / Fr.modulus), mul_nsmul',
      modulus_smul_generator, nsmul_zero, zero_add]

/-- The image of a scalar in the curve group: `ofFr s = [s]g₁`.
`WellFormed` trusted-setup statements are phrased with this map. -/
noncomputable def ofFr (s : Fr) : curve.toAffine.Point :=
  s.val • toPoint generator

theorem ofFr_zero : ofFr 0 = 0 := by rw [ofFr, Fr.val_zero, zero_nsmul]

theorem ofFr_one : ofFr 1 = toPoint generator := by rw [ofFr, Fr.val_one, one_nsmul]

/-- `ofFr` is additive: `Fr` addition (mod `r`) matches group
addition. -/
theorem ofFr_add (s t : Fr) : ofFr (s + t) = ofFr s + ofFr t := by
  rw [ofFr, ofFr, ofFr, Fr.val_add,
      ← nsmul_generator_mod, add_nsmul]

/-- `ofFr` intertwines `Fr` multiplication with the scalar action. -/
theorem ofFr_mul (s t : Fr) : ofFr (s * t) = s.val • ofFr t := by
  rw [ofFr, ofFr, Fr.val_mul,
      ← nsmul_generator_mod, mul_nsmul']

/-- The spec's scalar multiplication of the generator is `ofFr`. -/
theorem toPoint_mul_generator (s : Fr) :
    toPoint (mul generator s) = ofFr s :=
  toPoint_mulNat valid_generator s.val

/-! ## Reference multi-scalar multiplication

`msmRef` is the naive fold `Σ_i [sᵢ]Pᵢ`; `toPoint_msmRef` maps it to a
`Finset.sum` in the curve group. The spec's windowed-Pippenger `msm`
will be proved equal to `msmRef` separately (that proof is about the
bucketing algorithm, not about the group). -/

/-- Naive multi-scalar multiplication: `Σ_i [scalars i] (points i)`
over the first `n` indices. -/
def msmRef (points : Nat → G1) (scalars : Nat → Fr) : Nat → G1
  | 0 => zero
  | n + 1 => add (msmRef points scalars n) (mul (points n) (scalars n))

theorem valid_msmRef {points : Nat → G1} (scalars : Nat → Fr)
    (hp : ∀ i, Valid (points i)) (n : Nat) :
    Valid (msmRef points scalars n) := by
  induction n with
  | zero => exact valid_zero
  | succ n ih => exact valid_add ih (valid_mul (hp n) _)

/-- The reference MSM computes the sum of the scalar multiples in the
curve group. -/
theorem toPoint_msmRef {points : Nat → G1} (scalars : Nat → Fr)
    (hp : ∀ i, Valid (points i)) (n : Nat) :
    toPoint (msmRef points scalars n)
      = ∑ i ∈ Finset.range n, (scalars i).val • toPoint (points i) := by
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    exact toPoint_zero
  | succ n ih =>
    rw [msmRef, toPoint_add (valid_msmRef scalars hp n) (valid_mul (hp n) _),
        ih, toPoint_mul (hp n), Finset.sum_range_succ]

end EthLib.Cryptography.Bls.G1

module

public import EthLib.Cryptography.Proofs.Bls.JacobianLaw
public import EthLib.Cryptography.Proofs.Bls.FpZMod

/-!
# Proofs: the group structure of `G1`

The points of `G1` are Jacobian triples on `y^2 = x^3 + 4` over `Fp`.

The group law holds for the formulas over any field, through a map into a field of Mathlib.

Here the map sends `Fp` to `ZMod p`, where Mathlib's elliptic curves give the group.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve (Jacobian)
open WeierstrassCurve.Jacobian

/-- The BLS12-381 curve `y^2 = x^3 + 4`.

It is a Mathlib Weierstrass curve in Jacobian coordinates over `ZMod Fp.modulus`. -/
def curve : Jacobian (ZMod Fp.modulus) := Law.curveOf 4

/-- The Mathlib Jacobian representative of a spec point: its coordinates, mapped to `ZMod p`. -/
def rep (P : G1) : Fin 3 → ZMod Fp.modulus := Law.repOf Fp.embedding P

@[simp] theorem rep_x (P : G1) : rep P 0 = Fp.toZMod P.x := rfl
@[simp] theorem rep_y (P : G1) : rep P 1 = Fp.toZMod P.y := rfl
@[simp] theorem rep_z (P : G1) : rep P 2 = Fp.toZMod P.z := rfl

/-- Validity of a spec point: its representative is a nonsingular curve point.

Spec-produced points satisfy this (see the `valid_*` lemmas).

Raw `G1.mk` triples need not. -/
def Valid (P : G1) : Prop := curve.Nonsingular (rep P)

/-- The group element a spec point denotes: the affine Mathlib point of its representative.

It is total: singular representatives are sent to `0`.

It is only meaningful on `Valid` points. -/
noncomputable def toPoint (P : G1) : curve.toAffine.Point :=
  WeierstrassCurve.Jacobian.Point.toAffine curve (rep P)

/-! ## Boolean-test bridges -/

theorem isZero_iff {a : Fp} : a.isZero = true ↔ Fp.toZMod a = 0 :=
  Fp.embedding.isZero_iff a

theorem beq_iff {a b : Fp} : a.beq b = true ↔ Fp.toZMod a = Fp.toZMod b :=
  Fp.embedding.beq_iff a b

/-- `2` is not zero in `ZMod p`, since `p` is odd. -/
private theorem two_ne_zero' : (2 : ZMod Fp.modulus) ≠ 0 := by decide

/-! ## The group law, from the formulas over any field -/

theorem rep_zero : rep zero = ![1, 1, 0] := Law.repOf_zero Fp.embedding

/-- On a valid triple, `z = 0` exactly when the point is the zero of the group.

Singular triples with `z ≠ 0` also map to zero, so the hypothesis is needed. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero {P : G1} (hP : Valid P) :
    P.isInfinity = true ↔ toPoint P = 0 :=
  Law.isInfinity_eq_true_iff_toPoint_eq_zero Fp.embedding 4 hP

/-- The point at infinity passes the test for infinity. -/
@[simp] theorem isInfinity_zero : (zero : G1).isInfinity = true := Fp.zero_isZero

theorem valid_zero : Valid zero := Law.valid_zero Fp.embedding 4

theorem toPoint_zero : toPoint zero = 0 := Law.toPoint_zero Fp.embedding 4

theorem rep_neg (P : G1) : rep (neg P) = curve.neg (rep P) := Law.repOf_neg Fp.embedding 4 P

theorem valid_neg {P : G1} (h : Valid P) : Valid (neg P) := Law.valid_neg Fp.embedding 4 h

theorem toPoint_neg {P : G1} (h : Valid P) : toPoint (neg P) = -toPoint P :=
  Law.toPoint_neg Fp.embedding 4 h

theorem rep_double {P : G1} (hz : ¬P.z.isZero = true) :
    rep (double P) = curve.dblXYZ (rep P) :=
  Law.repOf_double Fp.embedding 4 hz

theorem valid_double {P : G1} (h : Valid P) : Valid (double P) :=
  Law.valid_double Fp.embedding 4 h

theorem toPoint_double {P : G1} (h : Valid P) :
    toPoint (double P) = toPoint P + toPoint P :=
  Law.toPoint_double Fp.embedding 4 h

/-- The curve equation of a valid point, in `linear_combination`-ready form (`y^2 = x^3 + 4z^6`). -/
theorem valid_equation {P : G1} (h : Valid P) :
    rep P 1 ^ 2 = rep P 0 ^ 3 + 4 * rep P 2 ^ 6 :=
  Law.valid_equation Fp.embedding 4 h

theorem valid_add {P Q : G1} (hP : Valid P) (hQ : Valid Q) : Valid (add P Q) :=
  Law.valid_add Fp.embedding 4 two_ne_zero' hP hQ

theorem toPoint_add {P Q : G1} (hP : Valid P) (hQ : Valid Q) :
    toPoint (add P Q) = toPoint P + toPoint Q :=
  Law.toPoint_add Fp.embedding 4 two_ne_zero' hP hQ

theorem valid_mulNat {P : G1} (h : Valid P) (k : Nat) : Valid (mulNat P k) :=
  Law.valid_mulNat Fp.embedding 4 two_ne_zero' h k

/-- The spec's double-and-add scalar multiplication is Mathlib's `ℕ` scalar action on the group.

The group is the curve group. -/
theorem toPoint_mulNat {P : G1} (h : Valid P) (k : Nat) :
    toPoint (mulNat P k) = k • toPoint P :=
  Law.toPoint_mulNat Fp.embedding 4 two_ne_zero' h k

/-- The spec's `Fr`-scalar multiplication acts through the scalar's value. -/
theorem toPoint_mul {P : G1} (h : Valid P) (s : Fr) :
    toPoint (mul P s) = s.val • toPoint P :=
  toPoint_mulNat h s.val

theorem valid_mul {P : G1} (h : Valid P) (s : Fr) : Valid (mul P s) :=
  valid_mulNat h s.val

/-- The chain `[t^2] ([t^2] P - P) + P` keeps a valid point valid. -/
theorem valid_mulModulus {P : G1} (h : Valid P) : Valid (mulModulus P) :=
  valid_add (valid_mulNat (valid_mulNat (valid_add (valid_mulNat (valid_mulNat h _) _)
    (valid_neg h)) _) _) h

/-- The chain `[t^2] ([t^2] P - P) + P` of `mulModulus` is `[r] P`. -/
theorem toPoint_mulModulus {P : G1} (h : Valid P) :
    toPoint (mulModulus P) = Fr.modulus • toPoint P := by
  have h₁ := valid_mulNat (valid_mulNat h blsX) blsX
  have h₂ := valid_add h₁ (valid_neg h)
  have h₃ := valid_mulNat (valid_mulNat h₂ blsX) blsX
  simp only [mulModulus, toPoint_add h₃ h, toPoint_mulNat (valid_mulNat h₂ blsX),
    toPoint_mulNat h₂, toPoint_add h₁ (valid_neg h), toPoint_mulNat (valid_mulNat h blsX),
    toPoint_mulNat h, toPoint_neg h]
  have hle : blsX ^ 2 ≤ blsX ^ 4 := Nat.pow_le_pow_right (by decide) (by decide)
  rw [Fr.modulus_eq_blsX, add_smul, one_smul, sub_nsmul _ hle]
  simp only [smul_smul, ← pow_two]
  rw [nsmul_add, neg_nsmul, smul_smul, ← pow_add]

end EthLib.Cryptography.Bls.G1

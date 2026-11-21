module

public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Proofs.Bls.JacobianLaw
public import EthLib.Cryptography.Proofs.Bls.Fp2

/-!
# Proofs: the group structure of `G2`

The points of `G2` are Jacobian triples on the twist `E' : y^2 = x^3 + 4 (1 + i)` over `Fp2`.

The curve and the subgroup follow draft-04, §1.3 and Appendix A.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04>

The twist also matches draft-07, §4.2.1.
<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-07>

A point of `G2` is a point of `G1` over `Fp2`, so it follows the group law of the formulas.

Here `Fp2` is itself a field of Mathlib, and the map is the identity.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve (Jacobian)
open WeierstrassCurve.Jacobian
open G1 (double mulNat)

/-- The BLS12-381 twisted curve `y^2 = x^3 + 4*(1 + i)` in Jacobian coordinates over `Fp2`. -/
def curve : Jacobian Fp2 := G1.Law.curveOf bTwist

/-- Mathlib Jacobian coordinate vector `![P.x, P.y, P.z]` of a `G2` triple. -/
def rep (P : G2) : Fin 3 → Fp2 := G1.Law.repOf Fp2.embedding P

@[simp] theorem rep_x (P : G2) : rep P 0 = P.x := rfl
@[simp] theorem rep_y (P : G2) : rep P 1 = P.y := rfl
@[simp] theorem rep_z (P : G2) : rep P 2 = P.z := rfl

/-- Nonsingularity of a `G2` Jacobian triple on `curve`.

For `P.z = 0`, nonsingularity restricts `rep P` to the projective class of `![1, 1, 0]`.
-/
def Valid (P : G2) : Prop := curve.Nonsingular (rep P)

/-- Affine group element denoted by a `G2` triple.

Singular triples map to `0`, so group homomorphisms require `Valid` inputs.
-/
noncomputable def toPoint (P : G2) : curve.toAffine.Point :=
  WeierstrassCurve.Jacobian.Point.toAffine curve (rep P)

/-! ## Boolean-test bridges -/

theorem isZero_iff {a : Fp2} : a.isZero = true ↔ a = 0 := Fp2.isZero_iff

theorem beq_iff {a b : Fp2} : a.beq b = true ↔ a = b := Fp2.beq_iff_eq

private theorem two_ne_zero' : (2 : Fp2) ≠ 0 := by decide_eq_at_model []

/-! ## The group law, from the formulas over any field -/

theorem rep_zero : rep zero = ![1, 1, 0] := G1.Law.repOf_zero Fp2.embedding

theorem valid_zero : Valid zero := G1.Law.valid_zero Fp2.embedding bTwist

theorem toPoint_zero : toPoint zero = 0 := G1.Law.toPoint_zero Fp2.embedding bTwist

theorem rep_neg (P : G2) : rep (neg P) = curve.neg (rep P) :=
  G1.Law.repOf_neg Fp2.embedding bTwist P

theorem valid_neg {P : G2} (h : Valid P) : Valid (neg P) := G1.Law.valid_neg Fp2.embedding bTwist h

theorem toPoint_neg {P : G2} (h : Valid P) : toPoint (neg P) = -toPoint P :=
  G1.Law.toPoint_neg Fp2.embedding bTwist h

/-- Finite `double` needs no projective rescaling because `dbl-2009-l` has unit weight `u = 1`. -/
theorem rep_double {P : G2} (hz : ¬P.z.isZero = true) :
    rep (double P) = curve.dblXYZ (rep P) :=
  G1.Law.repOf_double Fp2.embedding bTwist hz

theorem valid_double {P : G2} (h : Valid P) : Valid (double P) :=
  G1.Law.valid_double Fp2.embedding bTwist h

theorem toPoint_double {P : G2} (h : Valid P) :
    toPoint (double P) = toPoint P + toPoint P :=
  G1.Law.toPoint_double Fp2.embedding bTwist h

/-- Homogeneous curve equation `y^2 = x^3 + bTwist * z^6` of a valid point. -/
theorem valid_equation {P : G2} (h : Valid P) :
    rep P 1 ^ 2 = rep P 0 ^ 3 + bTwist * rep P 2 ^ 6 :=
  G1.Law.valid_equation Fp2.embedding bTwist h

theorem valid_add {P Q : G2} (hP : Valid P) (hQ : Valid Q) : Valid (add P Q) :=
  G1.Law.valid_add Fp2.embedding bTwist two_ne_zero' hP hQ

theorem toPoint_add {P Q : G2} (hP : Valid P) (hQ : Valid Q) :
    toPoint (add P Q) = toPoint P + toPoint Q :=
  G1.Law.toPoint_add Fp2.embedding bTwist two_ne_zero' hP hQ

theorem valid_mulNat {P : G2} (h : Valid P) (k : Nat) : Valid (mulNat P k) :=
  G1.Law.valid_mulNat Fp2.embedding bTwist two_ne_zero' h k

theorem toPoint_mulNat {P : G2} (h : Valid P) (k : Nat) :
    toPoint (mulNat P k) = k • toPoint P :=
  G1.Law.toPoint_mulNat Fp2.embedding bTwist two_ne_zero' h k

theorem toPoint_mul {P : G2} (h : Valid P) (s : Fr) :
    toPoint (mul P s) = s.val • toPoint P :=
  toPoint_mulNat h s.val

theorem valid_mul {P : G2} (h : Valid P) (s : Fr) : Valid (mul P s) :=
  valid_mulNat h s.val

end EthLib.Cryptography.Bls.G2

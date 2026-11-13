module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap

/-!
# Proofs: the u-only ladder on a Montgomery curve

The Montgomery curve `v^2 = u^3 + A u^2 + u` is the Weierstrass curve with `a_2 = A` and `a_4 = 1`.

So Mathlib's group law applies to its points as they are, with no change of coordinates.

A pair `(X : Z)` stands for the u-coordinate `X / Z` of a point, and `(1 : 0)` for infinity.

The ladder of [RFC 7748 §5][rfc] combines two formulas on such pairs.

- The doubling sends a pair of `Q` to a pair of `Q + Q`.
- The differential addition sends pairs of `Q` and `R` to a pair of `Q + R`.
  It needs the u-coordinate of `R - Q`, which must not be `0`, and a field in which `2 ≠ 0`.

Each formula holds for every point, the point at infinity and the points of order 2 included.

[rfc]: https://www.rfc-editor.org/rfc/rfc7748#section-5
-/

@[expose] public section

namespace EthLib.Cryptography.MontgomeryCurve

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- The curve `v^2 = u^3 + A u^2 + u`, as a Weierstrass curve with `a_2 = A` and `a_4 = 1`. -/
def curve (A : F) : WeierstrassCurve.Affine F :=
  { a₁ := 0, a₂ := A, a₃ := 0, a₄ := 1, a₆ := 0 }

/-- The equation of the curve. -/
theorem equation_iff (A u v : F) : (curve A).Equation u v ↔ v * v = u * u * u + A * u * u + u := by
  rw [Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

/-- The discriminant of the curve is `16 (A^2 - 4)`. -/
theorem discriminant_eq (A : F) : (curve A).Δ = 16 * (A ^ 2 - 4) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, curve]
  ring

/-- The u-coordinate of a point, and `0` at infinity, as RFC 7748 §5 returns it. -/
def uCoord {A : F} : (curve A).Point → F
  | .zero => 0
  | .some u _ _ => u

/-- `(X : Z)` is a nonzero multiple of `(u : 1)` for the point `(u, v)`.

At infinity, it is a nonzero multiple of `(1 : 0)`. -/
def Represents {A : F} (X Z : F) (Q : (curve A).Point) : Prop :=
  ∃ t : F, t ≠ 0 ∧ X = t * Q.xRep 0 ∧ Z = t * Q.xRep 1

/-- The doubling of the ladder, with `a24 = (A - 2) / 4`, RFC 7748 §5. -/
def double (a24 X Z : F) : F × F :=
  let aa := (X + Z) * (X + Z)
  let bb := (X - Z) * (X - Z)
  let e := aa - bb
  (aa * bb, e * (aa + a24 * e))

/-- The differential addition of the ladder, where `u` is the u-coordinate of the difference.

It is the RFC 7748 §5 step, with `(X2 : Z2)` and `(X3 : Z3)` the two points. -/
def diffAdd (u X2 Z2 X3 Z3 : F) : F × F :=
  let a := X2 + Z2
  let b := X2 - Z2
  let c := X3 + Z3
  let d := X3 - Z3
  let da := d * a
  let cb := c * b
  ((da + cb) * (da + cb), u * ((da - cb) * (da - cb)))

variable {A : F}

/-- A pair of a point gives its u-coordinate as `X / Z`, and `0` at infinity, where `Z = 0`. -/
theorem Represents.uCoord_eq {X Z : F} {Q : (curve A).Point} (h : Represents X Z Q) :
    uCoord Q = X * Z⁻¹ := by
  obtain ⟨t, ht, rfl, rfl⟩ := h
  cases Q with
  | zero => simp [uCoord, Point.xRep]
  | some u v hv => simp [uCoord, Point.xRep, mul_right_comm t u, ht]

/-- The addition-and-subtraction map of the curve, written out. -/
private lemma addSubMap_curve (v : Fin 3 → F) :
    (addSubMap (curve A) · |>.eval v) =
      ![(v 0 - v 2) ^ 2, 2 * v 1 * (v 0 + v 2) + 4 * A * v 0 * v 2, v 1 ^ 2 - 4 * v 0 * v 2] := by
  ext i : 1
  fin_cases i <;> simp [addSubMap, b₂, b₄, b₆, b₈, curve] <;> ring

variable [DecidableEq F]

/-- The doubling of a pair of `Q` is a pair of `Q + Q`. -/
theorem Represents.double {a24 X Z : F} {Q : (curve A).Point}
    (ha24 : 4 * a24 = A - 2) (h : Represents X Z Q) :
    Represents (double a24 X Z).1 (double a24 X Z).2 (Q + Q) := by
  obtain ⟨s, hs, rfl, rfl⟩ := h
  obtain ⟨t, ht, hm⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x Q Q
  rw [sub_self, addSubMap_curve] at hm
  have h0 := congrFun hm 0
  have h1 := congrFun hm 1
  simp [Point.sym2x_eq] at h0 h1
  refine ⟨s ^ 4 * t, by simp [hs, ht], ?_, ?_⟩
  · simp only [MontgomeryCurve.double]
    linear_combination (-s ^ 4) * h0
  · simp only [MontgomeryCurve.double]
    linear_combination (-s ^ 4) * h1 + 4 * s ^ 4 * Q.xRep 0 ^ 2 * Q.xRep 1 ^ 2 * ha24

/-- The differential addition of pairs of `Q` and `R` is a pair of `Q + R`.

It needs the u-coordinate `u` of `R - Q`, with `u ≠ 0`, and a field in which `2 ≠ 0`. -/
theorem Represents.diffAdd {u X2 Z2 X3 Z3 : F} {Q R : (curve A).Point} (h2 : (2 : F) ≠ 0)
    (hQ : Represents X2 Z2 Q) (hR : Represents X3 Z3 R) (hd : uCoord (R - Q) = u) (hu : u ≠ 0) :
    Represents (diffAdd u X2 Z2 X3 Z3).1 (diffAdd u X2 Z2 X3 Z3).2 (Q + R) := by
  obtain ⟨s2, hs2, rfl, rfl⟩ := hQ
  obtain ⟨s3, hs3, rfl, rfl⟩ := hR
  obtain ⟨t, ht, hm⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x R Q
  rw [addSubMap_curve, add_comm R Q] at hm
  generalize R - Q = D at hm hd
  cases D with
  | zero => exact absurd hd.symm (by simpa [uCoord] using hu)
  | some x y hxy =>
    simp only [uCoord] at hd
    subst hd
    have h0 := congrFun hm 0
    have h2' := congrFun hm 2
    simp [Point.sym2x_eq] at h0 h2'
    refine ⟨4 * s2 ^ 2 * s3 ^ 2 * t * x, ?_, ?_, ?_⟩
    · have h4 : (4 : F) ≠ 0 := by
        rw [show (4 : F) = 2 * 2 by norm_num]
        exact mul_ne_zero h2 h2
      have hx : x ≠ 0 := hu
      simp [h4, hs2, hs3, ht, hx]
    · simp only [MontgomeryCurve.diffAdd]
      linear_combination (-4 * s2 ^ 2 * s3 ^ 2) * h0
    · simp only [MontgomeryCurve.diffAdd]
      linear_combination (-4 * s2 ^ 2 * s3 ^ 2 * x) * h2'

end EthLib.Cryptography.MontgomeryCurve

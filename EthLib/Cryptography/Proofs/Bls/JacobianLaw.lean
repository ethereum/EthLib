module

public import EthLib.Cryptography.Proofs.Bls.CurveMap
public import EthLib.Cryptography.Proofs.BaseField
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.Tactic.Module

/-!
# Proofs: the group law of the Jacobian formulas, over any field

The Jacobian formulas read only the field operations of their base field.

So `G1` runs them over `Fp`, and `G2` runs the same code over `Fp2`.

This file proves the group law once, for a base field mapped into a field of Mathlib.

The curve is `y^2 = x^3 + b`, for any `b`, since the formulas never read `b`.

Mathlib's Jacobian points form a commutative group.

A triple is valid when its image is a nonsingular point, and then it denotes a point of the group.

Zero, negation and doubling keep validity, and they are the group law.

Addition and scalar multiplication do too when `2 ≠ 0` in the field, as for every odd prime.

Doubling agrees with Mathlib's doubling exactly.

Addition agrees with Mathlib's addition up to the scaling `u = -(2 z_1 z_2)`.

That agreement holds modulo the two curve equations.

The mixed addition gives the coordinates of the general addition when `z_2 = 1`.

The formulas are `dbl-2009-l`, `add-2007-bl` and `madd-2007-bl` of the explicit-formulas database.
<https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html>
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve (Jacobian)
open WeierstrassCurve.Jacobian

variable {F : Type} [FieldOps F]

namespace Law

variable {K : Type} [Field K]

/-- The curve `y^2 = x^3 + b` over `K`, in Jacobian coordinates. -/
def curveOf (b : K) : Jacobian K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := b }

/-- The image of a triple in `K`, as a Mathlib Jacobian vector. -/
def repOf (e : FieldOps.Embedding F K) (P : G1 F) : Fin 3 → K :=
  ![e.toFun P.x, e.toFun P.y, e.toFun P.z]

/-- A triple is valid when its image is a nonsingular point of the curve.

The code keeps validity, in a field where `2 ≠ 0`. -/
def Valid (e : FieldOps.Embedding F K) (b : K) (P : G1 F) : Prop :=
  (curveOf b).Nonsingular (repOf e P)

/-- The point of the group that a triple denotes.

It is total: a singular image is sent to `0`, so it is meaningful on valid triples only. -/
noncomputable def toPoint [DecidableEq K] (e : FieldOps.Embedding F K) (b : K) (P : G1 F) :
    (curveOf b).toAffine.Point :=
  Point.toAffine (curveOf b) (repOf e P)

variable (e : FieldOps.Embedding F K) (b : K)

@[simp] theorem repOf_x (P : G1 F) : repOf e P 0 = e.toFun P.x := rfl
@[simp] theorem repOf_y (P : G1 F) : repOf e P 1 = e.toFun P.y := rfl
@[simp] theorem repOf_z (P : G1 F) : repOf e P 2 = e.toFun P.z := rfl

/-- The coefficients `a_1` to `a_4` vanish. -/
private theorem a₁_eq : (curveOf b).a₁ = 0 := rfl
private theorem a₂_eq : (curveOf b).a₂ = 0 := rfl
private theorem a₃_eq : (curveOf b).a₃ = 0 := rfl
private theorem a₄_eq : (curveOf b).a₄ = 0 := rfl
private theorem a₆_eq : (curveOf b).a₆ = b := rfl

/-- Pushes the map through each field operation. -/
local macro "push_map" : tactic =>
  `(tactic| simp only [e.map_add, e.map_sub, e.map_mul, e.map_neg, e.map_zero, e.map_one])

/-- Reads the entries of a vector `![x, y, z]` and the coefficients of the curve. -/
local macro "read_vec" : tactic =>
  `(tactic| simp only [a₁_eq, a₂_eq, a₃_eq, a₄_eq, a₆_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])

/-- The negation of the curve negates `y`, since `a_1 = a_3 = 0`. -/
private theorem curve_negY (Q : Fin 3 → K) : (curveOf b).negY Q = -Q 1 := by
  rw [negY, a₁_eq, a₃_eq]
  ring

/-- A nonzero test that fails means a nonzero image. -/
theorem z_ne_zero {a : F} (h : ¬FieldOps.isZero a = true) : e.toFun a ≠ 0 :=
  fun h0 => h ((e.isZero_iff a).mpr h0)

/-! ## Zero and negation -/

theorem repOf_zero : repOf e (zero : G1 F) = ![1, 1, 0] := by
  funext i
  fin_cases i
  · exact e.map_one
  · exact e.map_one
  · exact e.map_zero

theorem valid_zero : Valid e b (zero : G1 F) := by
  rw [Valid, repOf_zero]
  exact nonsingular_zero

theorem toPoint_zero [DecidableEq K] : toPoint e b (zero : G1 F) = 0 := by
  rw [toPoint, repOf_zero]
  exact Point.toAffine_zero

/-- A triple at infinity denotes the zero of the group. -/
theorem toPoint_of_isZero [DecidableEq K] {P : G1 F} (h : FieldOps.isZero P.z = true) :
    toPoint e b P = 0 :=
  Point.toAffine_of_Z_eq_zero ((e.isZero_iff _).mp h)

theorem repOf_neg (P : G1 F) : repOf e (neg P) = (curveOf b).neg (repOf e P) := by
  funext i
  fin_cases i
  · show e.toFun P.x = (curveOf b).neg (repOf e P) 0
    rw [neg_X]
    rfl
  · show e.toFun (-P.y) = (curveOf b).neg (repOf e P) 1
    rw [neg_Y, curve_negY, e.map_neg]
    rfl
  · show e.toFun P.z = (curveOf b).neg (repOf e P) 2
    rw [neg_Z]
    rfl

theorem valid_neg {P : G1 F} (h : Valid e b P) : Valid e b (neg P) := by
  rw [Valid, repOf_neg]
  exact nonsingular_neg h

theorem toPoint_neg [DecidableEq K] {P : G1 F} (h : Valid e b P) :
    toPoint e b (neg P) = -toPoint e b P := by
  rw [toPoint, repOf_neg]
  exact Point.toAffine_neg h

/-! ## Doubling

The `dbl-2009-l` formulas are Mathlib's doubling, as polynomial identities.

No curve equation is needed. -/

theorem repOf_double {P : G1 F} (hz : ¬FieldOps.isZero P.z = true) :
    repOf e (double P) = (curveOf b).dblXYZ (repOf e P) := by
  funext i
  fin_cases i
  · show e.toFun (double P).x = (curveOf b).dblX ![e.toFun P.x, e.toFun P.y, e.toFun P.z]
    rw [double, ite_eq_right hz, dblX, dblU_eq, curve_negY]
    push_map
    read_vec
    ring
  · show e.toFun (double P).y = (curveOf b).dblY ![e.toFun P.x, e.toFun P.y, e.toFun P.z]
    rw [double, ite_eq_right hz, dblY, curve_negY]
    show _ = -(curveOf b).negDblY _
    rw [negDblY, dblX, dblU_eq, curve_negY]
    push_map
    read_vec
    ring
  · show e.toFun (double P).z = (curveOf b).dblZ ![e.toFun P.x, e.toFun P.y, e.toFun P.z]
    rw [double, ite_eq_right hz, dblZ, curve_negY]
    push_map
    read_vec
    ring

theorem valid_double {P : G1 F} (h : Valid e b P) : Valid e b (double P) := by
  by_cases hz : FieldOps.isZero P.z = true
  · rw [double, ite_eq_left hz]
    exact h
  · rw [Valid, repOf_double e b hz, ← add_of_equiv (Setoid.refl (repOf e P))]
    exact nonsingular_add h h

theorem toPoint_double [DecidableEq K] {P : G1 F} (h : Valid e b P) :
    toPoint e b (double P) = toPoint e b P + toPoint e b P := by
  by_cases hz : FieldOps.isZero P.z = true
  · rw [double, ite_eq_left hz, toPoint_of_isZero e b hz, add_zero]
  · rw [toPoint, repOf_double e b hz, ← add_of_equiv (Setoid.refl (repOf e P))]
    exact Point.toAffine_add h h

/-! ## Equality of points -/

include e in
/-- The projective equality is reflexive, since the tests of the base field are lawful. -/
theorem projectiveEq_refl (P : G1 F) : P.projectiveEq P = true := by
  unfold projectiveEq
  by_cases hz : FieldOps.isZero P.z = true
  · rw [ite_eq_left hz]
    exact hz
  · rw [ite_eq_right hz, ite_eq_right hz, Bool.and_eq_true, e.beq_iff, e.beq_iff]
    exact ⟨rfl, rfl⟩

/-- Among valid triples, exactly those at infinity denote zero. -/
theorem isInfinity_eq_true_iff_toPoint_eq_zero [DecidableEq K] {P : G1 F} (h : Valid e b P) :
    P.isInfinity = true ↔ toPoint e b P = 0 := by
  refine ⟨toPoint_of_isZero e b, fun h0 => ?_⟩
  by_contra hz
  rw [toPoint, Point.toAffine_of_Z_ne_zero h (z_ne_zero e hz)] at h0
  cases h0

/-- Two valid triples denote the same point exactly when their images are equivalent. -/
theorem toPoint_eq_iff_rep_equiv [DecidableEq K] {P Q : G1 F} (hP : Valid e b P)
    (hQ : Valid e b Q) :
    toPoint e b P = toPoint e b Q ↔ repOf e P ≈ repOf e Q := by
  refine ⟨fun h => ?_, Point.toAffine_of_equiv⟩
  have he : ({ point := ⟦repOf e P⟧, nonsingular := hP } : (curveOf b).Point) =
      ({ point := ⟦repOf e Q⟧, nonsingular := hQ } : (curveOf b).Point) :=
    (Point.toAffineAddEquiv (curveOf b)).injective h
  exact Quotient.eq.mp (congrArg Point.point he)

/-- The projective equality of two valid triples is the equivalence of their images. -/
theorem projectiveEq_eq_true_iff_rep_equiv {P Q : G1 F} (hP : Valid e b P) (hQ : Valid e b Q) :
    projectiveEq P Q = true ↔ repOf e P ≈ repOf e Q := by
  unfold projectiveEq
  by_cases hpz : FieldOps.isZero P.z = true
  · rw [ite_eq_left hpz]
    refine ⟨fun hqz => equiv_of_Z_eq_zero hP hQ ((e.isZero_iff _).mp hpz)
      ((e.isZero_iff _).mp hqz), fun he => ?_⟩
    exact (e.isZero_iff _).mpr ((Z_eq_zero_of_equiv he).mp ((e.isZero_iff _).mp hpz))
  rw [ite_eq_right hpz]
  by_cases hqz : FieldOps.isZero Q.z = true
  · rw [ite_eq_left hqz]
    exact iff_of_false Bool.false_ne_true
      (not_equiv_of_Z_eq_zero_right (z_ne_zero e hpz) ((e.isZero_iff _).mp hqz))
  rw [ite_eq_right hqz, Bool.and_eq_true, e.beq_iff, e.beq_iff]
  push_map
  constructor
  · rintro ⟨h1, h2⟩
    refine equiv_of_X_eq_of_Y_eq (z_ne_zero e hpz) (z_ne_zero e hqz) ?_ ?_
    · simp only [repOf_x, repOf_z]
      linear_combination h1
    · simp only [repOf_y, repOf_z]
      linear_combination h2
  · intro he
    have hx := X_eq_of_equiv he
    have hy := Y_eq_of_equiv he
    simp only [repOf_x, repOf_y, repOf_z] at hx hy
    exact ⟨by linear_combination hx, by linear_combination hy⟩

/-- On valid triples, projective equality is equality of the points they denote. -/
theorem projectiveEq_eq_true_iff_toPoint_eq [DecidableEq K] {P Q : G1 F} (hP : Valid e b P)
    (hQ : Valid e b Q) :
    projectiveEq P Q = true ↔ toPoint e b P = toPoint e b Q :=
  (projectiveEq_eq_true_iff_rep_equiv e b hP hQ).trans (toPoint_eq_iff_rep_equiv e b hP hQ).symm

/-! ## Addition

The `add-2007-bl` formulas agree with Mathlib's `addXYZ` up to the scaling `u = -(2 z_1 z_2)`.

They agree modulo the curve equations of the two inputs.

The special branches go through Mathlib's equivalence lemmas, at the affine level. -/

/-- The curve equation of a valid triple, `y^2 = x^3 + b z^6`. -/
theorem valid_equation {P : G1 F} (h : Valid e b P) :
    repOf e P 1 ^ 2 = repOf e P 0 ^ 3 + b * repOf e P 2 ^ 6 := by
  have heq := ((nonsingular_iff (repOf e P)).mp h).1
  rw [equation_iff] at heq
  simp only [a₁_eq, a₂_eq, a₃_eq, a₄_eq, a₆_eq] at heq
  linear_combination heq

/-- The three coordinates of the general addition, as weighted coordinates of `addXYZ`.

The intermediate values of the formulas are binders, pinned by their defining equations.

The coefficients of each combination of the curve equations were computed symbolically. -/
private theorem add_components
    (x1 y1 z1 x2 y2 z2 z11 z22 u1 u2 s1 s2 h i j r v xp : K)
    (hz11 : z11 = z1 * z1) (hz22 : z22 = z2 * z2)
    (hu1 : u1 = x1 * z22) (hu2 : u2 = x2 * z11)
    (hs1 : s1 = y1 * z2 * z22) (hs2 : s2 = y2 * z1 * z11)
    (hh : h = u2 - u1) (hi : i = (h + h) * (h + h)) (hj : j = h * i)
    (hr : r = s2 - s1 + (s2 - s1)) (hv : v = u1 * i)
    (hxp : xp = r * r - j - (v + v))
    (hP : y1 ^ 2 = x1 ^ 3 + b * z1 ^ 6) (hQ : y2 ^ 2 = x2 ^ 3 + b * z2 ^ 6) :
    xp = (-(2 * (z1 * z2))) ^ 2 * (curveOf b).addX ![x1, y1, z1] ![x2, y2, z2]
    ∧ r * (v - xp) - (s1 + s1) * j
        = (-(2 * (z1 * z2))) ^ 3 * (curveOf b).addY ![x1, y1, z1] ![x2, y2, z2]
    ∧ ((z1 + z2) * (z1 + z2) - z11 - z22) * h
        = -(2 * (z1 * z2)) * addZ ![x1, y1, z1] ![x2, y2, z2] := by
  subst hz11 hz22 hu1 hu2 hs1 hs2 hh hi hj hr hv hxp
  refine ⟨?_, ?_, ?_⟩
  · rw [addX]
    read_vec
    linear_combination (4 * z2 ^ 6) * hP + (4 * z1 ^ 6) * hQ
  · rw [addY, curve_negY]
    show _ = (-(2 * (z1 * z2))) ^ 3 * -(curveOf b).negAddY ![x1, y1, z1] ![x2, y2, z2]
    rw [negAddY]
    read_vec
    linear_combination (8 * z2 ^ 6 * (y1 * z2 ^ 3 - y2 * z1 ^ 3)) * hP
      + (8 * z1 ^ 6 * (y1 * z2 ^ 3 - y2 * z1 ^ 3)) * hQ
  · rw [addZ]
    read_vec
    ring

/-- The general formulas, in their last branch, as a weighted `addXYZ`. -/
private theorem repOf_addGeneral {P Q : G1 F} (hP : Valid e b P) (hQ : Valid e b Q)
    (hu : ¬FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) = true) :
    repOf e (addGeneral P Q)
      = (-(2 * (repOf e P 2 * repOf e Q 2))) • (curveOf b).addXYZ (repOf e P) (repOf e Q) := by
  let z1z1 := P.z * P.z
  let z2z2 := Q.z * Q.z
  let u1 := P.x * z2z2
  let u2 := Q.x * z1z1
  let s1 := P.y * Q.z * z2z2
  let s2 := Q.y * P.z * z1z1
  let h := u2 - u1
  let i := (h + h) * (h + h)
  let j := h * i
  let r := s2 - s1 + (s2 - s1)
  let v := u1 * i
  let x3 := r * r - j - (v + v)
  obtain ⟨hX, hY, hZ⟩ := add_components b (e.toFun P.x) (e.toFun P.y) (e.toFun P.z)
    (e.toFun Q.x) (e.toFun Q.y) (e.toFun Q.z) (e.toFun z1z1) (e.toFun z2z2) (e.toFun u1)
    (e.toFun u2) (e.toFun s1) (e.toFun s2) (e.toFun h) (e.toFun i) (e.toFun j) (e.toFun r)
    (e.toFun v) (e.toFun x3)
    (e.map_mul _ _) (e.map_mul _ _) (e.map_mul _ _) (e.map_mul _ _)
    (by simp only [s1, e.map_mul]) (by simp only [s2, e.map_mul])
    (e.map_sub _ _) (by simp only [i, e.map_mul, e.map_add]) (e.map_mul _ _)
    (by simp only [r, e.map_add, e.map_sub]) (e.map_mul _ _)
    (by simp only [x3, e.map_sub, e.map_mul, e.map_add])
    (valid_equation e b hP) (valid_equation e b hQ)
  have hbranch : addGeneral P Q = ⟨x3, r * (v - x3) - (s1 + s1) * j,
      ((P.z + Q.z) * (P.z + Q.z) - z1z1 - z2z2) * h⟩ := by
    rw [addGeneral]
    exact ite_eq_right hu
  have hs := smul_fin3_ext ((curveOf b).addXYZ (repOf e P) (repOf e Q))
    (-(2 * (repOf e P 2 * repOf e Q 2)))
  rw [hbranch]
  funext k
  fin_cases k
  · show e.toFun x3 = (_ • (curveOf b).addXYZ (repOf e P) (repOf e Q)) 0
    exact hX.trans (hs.1).symm
  · show e.toFun (r * (v - x3) - (s1 + s1) * j)
      = (_ • (curveOf b).addXYZ (repOf e P) (repOf e Q)) 1
    refine Eq.trans ?_ (hY.trans (hs.2.1).symm)
    simp only [e.map_sub, e.map_mul, e.map_add]
  · show e.toFun (((P.z + Q.z) * (P.z + Q.z) - z1z1 - z2z2) * h)
      = (_ • (curveOf b).addXYZ (repOf e P) (repOf e Q)) 2
    refine Eq.trans ?_ (hZ.trans (hs.2.2).symm)
    simp only [e.map_sub, e.map_mul, e.map_add]

/-- The mixed formulas give the image of the general formulas when the second `z` maps to 1. -/
private theorem repOf_addMixed {P Q : G1 F} (hq : e.toFun Q.z = 1) :
    repOf e (addMixed P Q) = repOf e (addGeneral P Q) := by
  -- The two branch tests agree, since `u1 = x1` and `s1 = y1` when `z2 = 1`.
  have cx : FieldOps.beq P.x (Q.x * (P.z * P.z))
      = FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) := by
    rw [Bool.eq_iff_iff, e.beq_iff, e.beq_iff]
    push_map
    rw [hq, mul_one, mul_one]
  have cy : FieldOps.beq P.y (Q.y * P.z * (P.z * P.z))
      = FieldOps.beq (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z)) := by
    rw [Bool.eq_iff_iff, e.beq_iff, e.beq_iff]
    push_map
    rw [hq, mul_one, mul_one, mul_one]
  unfold addMixed addGeneral
  dsimp only
  rw [cx, cy]
  split_ifs
  · rfl
  · rfl
  · funext k
    fin_cases k <;>
    · show e.toFun _ = e.toFun _
      push_map
      rw [hq]
      ring

/-- For finite triples, the addition has the image of the general formulas. -/
theorem repOf_add {P Q : G1 F} (hz1 : ¬FieldOps.isZero P.z = true)
    (hz2 : ¬FieldOps.isZero Q.z = true) : repOf e (add P Q) = repOf e (addGeneral P Q) := by
  rw [add, ite_eq_right hz1, ite_eq_right hz2]
  split
  · rename_i h1
    refine repOf_addMixed e ?_
    rw [← e.map_one]
    exact (e.beq_iff _ _).mp h1
  · rfl

private theorem add_of_left_zero {P Q : G1 F} (hz1 : FieldOps.isZero P.z = true) :
    add P Q = Q := by
  rw [add]
  exact ite_eq_left hz1

private theorem add_of_right_zero {P Q : G1 F} (hz1 : ¬FieldOps.isZero P.z = true)
    (hz2 : FieldOps.isZero Q.z = true) : add P Q = P := by
  rw [add, ite_eq_right hz1]
  exact ite_eq_left hz2

private theorem addGeneral_of_dbl {P Q : G1 F}
    (hu : FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) = true)
    (hs : FieldOps.beq (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z)) = true) :
    addGeneral P Q = double P := by
  rw [addGeneral]
  exact (ite_eq_left hu).trans (ite_eq_left hs)

private theorem addGeneral_of_opp {P Q : G1 F}
    (hu : FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) = true)
    (hs : ¬FieldOps.beq (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z)) = true) :
    addGeneral P Q = zero := by
  rw [addGeneral]
  exact (ite_eq_left hu).trans (ite_eq_right hs)

/-- The first branch test of the general formulas, on the images. -/
private theorem beq_x_iff {P Q : G1 F} :
    FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) = true
      ↔ repOf e P 0 * repOf e Q 2 ^ 2 = repOf e Q 0 * repOf e P 2 ^ 2 := by
  rw [e.beq_iff, e.map_mul, e.map_mul, e.map_mul, e.map_mul]
  simp only [repOf_x, repOf_z, sq]

/-- The second branch test of the general formulas, on the images. -/
private theorem beq_y_iff {P Q : G1 F} :
    FieldOps.beq (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z)) = true
      ↔ repOf e P 1 * repOf e Q 2 ^ 3 = repOf e Q 1 * repOf e P 2 ^ 3 := by
  rw [e.beq_iff]
  push_map
  simp only [repOf_y, repOf_z]
  constructor <;> intro h <;> linear_combination h

/-- The weight of the general branch is a unit, when 2 is not zero. -/
private theorem isUnit_scale (h2 : (2 : K) ≠ 0) {P Q : G1 F} (hz1 : ¬FieldOps.isZero P.z = true)
    (hz2 : ¬FieldOps.isZero Q.z = true) : IsUnit (-(2 * (repOf e P 2 * repOf e Q 2))) :=
  (neg_ne_zero.mpr (mul_ne_zero h2 (mul_ne_zero (z_ne_zero e hz1) (z_ne_zero e hz2)))).isUnit

/-- The general formulas keep validity. -/
private theorem valid_addGeneral (h2 : (2 : K) ≠ 0) {P Q : G1 F} (hP : Valid e b P)
    (hQ : Valid e b Q) (hz1 : ¬FieldOps.isZero P.z = true) (hz2 : ¬FieldOps.isZero Q.z = true) :
    Valid e b (addGeneral P Q) := by
  by_cases hu : FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) = true
  · by_cases hs : FieldOps.beq (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z)) = true
    · rw [addGeneral_of_dbl hu hs]
      exact valid_double e b hP
    · rw [addGeneral_of_opp hu hs]
      exact valid_zero e b
  · rw [Valid, repOf_addGeneral e b hP hQ hu, nonsingular_smul _ (isUnit_scale e h2 hz1 hz2),
      ← add_of_not_equiv (fun heq => hu ((beq_x_iff e).mpr (X_eq_of_equiv heq)))]
    exact nonsingular_add hP hQ

theorem valid_add (h2 : (2 : K) ≠ 0) {P Q : G1 F} (hP : Valid e b P) (hQ : Valid e b Q) :
    Valid e b (add P Q) := by
  by_cases hz1 : FieldOps.isZero P.z = true
  · rw [add_of_left_zero hz1]
    exact hQ
  by_cases hz2 : FieldOps.isZero Q.z = true
  · rw [add_of_right_zero hz1 hz2]
    exact hP
  rw [Valid, repOf_add e hz1 hz2]
  exact valid_addGeneral e b h2 hP hQ hz1 hz2

theorem toPoint_add [DecidableEq K] (h2 : (2 : K) ≠ 0) {P Q : G1 F} (hP : Valid e b P)
    (hQ : Valid e b Q) :
    toPoint e b (add P Q) = toPoint e b P + toPoint e b Q := by
  by_cases hz1 : FieldOps.isZero P.z = true
  · rw [add_of_left_zero hz1, toPoint_of_isZero e b hz1, zero_add]
  by_cases hz2 : FieldOps.isZero Q.z = true
  · rw [add_of_right_zero hz1 hz2, toPoint_of_isZero e b hz2, add_zero]
  rw [toPoint, repOf_add e hz1 hz2, ← toPoint]
  by_cases hu : FieldOps.beq (P.x * (Q.z * Q.z)) (Q.x * (P.z * P.z)) = true
  · have hx := (beq_x_iff e).mp hu
    by_cases hs : FieldOps.beq (P.y * Q.z * (Q.z * Q.z)) (Q.y * P.z * (P.z * P.z)) = true
    · -- The same point: the formulas double it.
      have hequiv : repOf e P ≈ repOf e Q :=
        equiv_of_X_eq_of_Y_eq (z_ne_zero e hz1) (z_ne_zero e hz2) hx ((beq_y_iff e).mp hs)
      rw [addGeneral_of_dbl hu hs, toPoint_double e b hP,
        show toPoint e b P = toPoint e b Q from Point.toAffine_of_equiv hequiv]
    · -- Opposite points: the formulas return zero.
      have hy := fun heq => hs ((beq_y_iff e).mpr heq)
      have hyneg := Y_eq_of_Y_ne ((nonsingular_iff (repOf e P)).mp hP).1
        ((nonsingular_iff (repOf e Q)).mp hQ).1 hx hy
      have hequiv : repOf e P ≈ (curveOf b).neg (repOf e Q) := by
        refine equiv_of_X_eq_of_Y_eq (z_ne_zero e hz1) ?_ ?_ ?_
        · rw [neg_Z]
          exact z_ne_zero e hz2
        · rw [neg_X, neg_Z]
          exact hx
        · rw [neg_Y, neg_Z]
          exact hyneg
      rw [addGeneral_of_opp hu hs, toPoint_zero,
        show toPoint e b P = -toPoint e b Q from (Point.toAffine_of_equiv hequiv).trans
          (Point.toAffine_neg hQ),
        neg_add_cancel]
  · -- The general branch: a unit scaling of `addXYZ`.
    have hne : ¬repOf e P ≈ repOf e Q := fun heq => hu ((beq_x_iff e).mpr (X_eq_of_equiv heq))
    rw [toPoint, repOf_addGeneral e b hP hQ hu,
      Point.toAffine_of_equiv (smul_equiv _ (isUnit_scale e h2 hz1 hz2)), ← add_of_not_equiv hne]
    exact Point.toAffine_add hP hQ

/-! ## Scalar multiplication -/

theorem valid_mulNat (h2 : (2 : K) ≠ 0) {P : G1 F} (h : Valid e b P) (k : Nat) :
    Valid e b (mulNat P k) := by
  induction k using Nat.strongRecOn generalizing P with
  | _ k ih =>
    rw [mulNat_def]
    by_cases hk : k = 0
    · rw [ite_eq_left hk]
      exact valid_zero e b
    rw [ite_eq_right hk]
    by_cases h2k : k % 2 = 1
    · rw [ite_eq_left h2k]
      exact valid_add e b h2 h (ih (k / 2) (by omega) (valid_double e b h))
    · rw [ite_eq_right h2k]
      exact ih (k / 2) (by omega) (valid_double e b h)

/-- The double-and-add scalar multiplication is the action of `ℕ` on the group. -/
theorem toPoint_mulNat [DecidableEq K] (h2 : (2 : K) ≠ 0) {P : G1 F} (h : Valid e b P) (k : Nat) :
    toPoint e b (mulNat P k) = k • toPoint e b P := by
  induction k using Nat.strongRecOn generalizing P with
  | _ k ih =>
    rw [mulNat_def]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, toPoint_zero, hk, zero_nsmul]
    rw [ite_eq_right hk]
    by_cases h2k : k % 2 = 1
    · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      rw [ite_eq_left h2k, toPoint_add e b h2 h (valid_mulNat e b h2 (valid_double e b h) _),
        show (2 * m + 1) / 2 = m by omega, ih m (by omega) (valid_double e b h),
        toPoint_double e b h]
      module
    · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      rw [ite_eq_right h2k, show 2 * m / 2 = m by omega, ih m (by omega) (valid_double e b h),
        toPoint_double e b h]
      module

/-! ## Special values -/

include e in
/-- One fails the zero test. -/
theorem isZero_one : FieldOps.isZero (FieldOps.one : F) = false :=
  Bool.eq_false_iff.mpr fun h => one_ne_zero (e.map_one.symm.trans ((e.isZero_iff _).mp h))

include e in
/-- Adding to the point at infinity returns the other operand. -/
theorem zero_add (Q : G1 F) : add zero Q = Q := by
  rw [add]
  exact ite_eq_left ((e.isZero_iff _).mpr e.map_zero)

include e in
/-- Adding the point at infinity to a finite triple returns the triple. -/
theorem add_zero {P : G1 F} (hP : P.isInfinity = false) : add P zero = P := by
  have hz : FieldOps.isZero P.z = false := hP
  rw [add, ite_eq_right (Bool.eq_false_iff.mp hz)]
  exact ite_eq_left ((e.isZero_iff _).mpr e.map_zero)

/-- The product by zero is the point at infinity. -/
theorem mulNat_zero (P : G1 F) : mulNat P 0 = zero := by
  rw [mulNat_def, ite_eq_left rfl]

include e in
/-- The product of a finite triple by one is the triple. -/
theorem mulNat_one {P : G1 F} (hP : P.isInfinity = false) : mulNat P 1 = P := by
  rw [mulNat_def, ite_eq_right one_ne_zero, ite_eq_left rfl, mulNat_zero]
  exact add_zero e hP

include e in
/-- A triple with `z = 1` is its own affine form. -/
theorem toAffine_mk_one (x y : F) : G1.toAffine (⟨x, y, FieldOps.one⟩ : G1 F) = (x, y) := by
  simp only [G1.toAffine, isZero_one e, Bool.false_eq_true, ↓reduceIte]
  refine Prod.ext (e.injective ?_) (e.injective ?_) <;>
    simp only [e.map_mul, e.map_inverse, e.map_one, inv_one] <;> ring

/-- Two nonsingular representatives of one point are both at infinity or both finite. -/
private theorem Z_eq_zero_iff_of_toAffine_eq [DecidableEq K] {W : Jacobian K} {P Q : Fin 3 → K}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : Point.toAffine W P = Point.toAffine W Q) : P 2 = 0 ↔ Q 2 = 0 := by
  by_cases hPz : P 2 = 0 <;> by_cases hQz : Q 2 = 0
  · simp [hPz, hQz]
  · rw [Point.toAffine_of_Z_eq_zero hPz, Point.toAffine_of_Z_ne_zero hQ hQz] at h
    cases h
  · rw [Point.toAffine_of_Z_ne_zero hP hPz, Point.toAffine_of_Z_eq_zero hQz] at h
    cases h
  · simp [hPz, hQz]

/-- Two finite nonsingular representatives of one point have the same affine coordinates. -/
private theorem affine_eq_of_toAffine_eq [DecidableEq K] {W : Jacobian K} {P Q : Fin 3 → K}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : Point.toAffine W P = Point.toAffine W Q) (hPz : P 2 ≠ 0) (hQz : Q 2 ≠ 0) :
    P 0 / P 2 ^ 2 = Q 0 / Q 2 ^ 2 ∧ P 1 / P 2 ^ 3 = Q 1 / Q 2 ^ 3 := by
  rw [Point.toAffine_of_Z_ne_zero hP hPz, Point.toAffine_of_Z_ne_zero hQ hQz] at h
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at h
  exact h

/-- Two valid triples that denote the same point have the same affine form. -/
theorem toAffine_congr [DecidableEq K] {P Q : G1 F} (hP : Valid e b P) (hQ : Valid e b Q)
    (h : toPoint e b P = toPoint e b Q) :
    P.isInfinity = Q.isInfinity ∧ P.toAffine = Q.toAffine := by
  have hz : FieldOps.isZero P.z = true ↔ FieldOps.isZero Q.z = true :=
    (e.isZero_iff _).trans ((Z_eq_zero_iff_of_toAffine_eq hP hQ h).trans (e.isZero_iff _).symm)
  refine ⟨Bool.eq_iff_iff.mpr hz, ?_⟩
  by_cases hPz : FieldOps.isZero P.z = true
  · simp only [G1.toAffine, hPz, hz.mp hPz, ↓reduceIte]
  have hQz : ¬FieldOps.isZero Q.z = true := fun h => hPz (hz.mpr h)
  obtain ⟨hx, hy⟩ := affine_eq_of_toAffine_eq hP hQ h (z_ne_zero e hPz) (z_ne_zero e hQz)
  simp only [repOf_x, repOf_y, repOf_z] at hx hy
  simp only [G1.toAffine, hPz, hQz, Bool.false_eq_true, ↓reduceIte]
  refine Prod.ext (e.injective ?_) (e.injective ?_) <;> simp only [e.map_mul, e.map_inverse]
  · linear_combination hx
  · linear_combination hy

end Law

end EthLib.Cryptography.Bls.G1

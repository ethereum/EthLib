module

public import EthLib.Cryptography.Proofs.Bls.G1Order
public import Mathlib.GroupTheory.Index

/-!
# Proofs: elementary cardinality bound for `G1`

Every finite point `(x, y)` on `E : y^2 = x^3 + 4` over `ZMod Fp.modulus` satisfies `y^2 = x^3 + 4`.

For each `x`, at most two values of `y` solve that quadratic equation, and `0` adds one point at infinity.

Injecting `curve.toAffine.Point` into an optional pair of a residue mod `p` and a sign bit gives `#E(Fp) <= 2 * p + 1`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve.Affine

set_option maxRecDepth 10000

private theorem curve_equation (x y : ZMod Fp.modulus) :
    curve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + 4 := by
  simp [WeierstrassCurve.Affine.equation_iff, curve]

/-- Witness `y`-coordinate when some `y` on the curve has coordinate `x`, or `0` otherwise. -/
noncomputable def chosenY (x : ZMod Fp.modulus) : ZMod Fp.modulus := by
  classical
  exact if h : ∃ y, curve.toAffine.Nonsingular x y then Classical.choose h else 0

private theorem chosenY_valid {x y : ZMod Fp.modulus} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular x (chosenY x) := by
  have he : ∃ y, curve.toAffine.Nonsingular x y := ⟨y, h⟩
  simpa only [chosenY, dite_eq_left he] using Classical.choose_spec he

/-- Over the field `ZMod p`, `y^2 = (chosenY x)^2` leaves at most the two roots `chosenY x` and `-chosenY x`. -/
private theorem y_eq_or_neg_chosen {x y : ZMod Fp.modulus} (h : curve.toAffine.Nonsingular x y) :
    y = chosenY x ∨ y = -(chosenY x) := by
  -- Both `(x, y)` and `(x, chosenY x)` satisfy `y^2 = x^3 + 4`, so their squares agree in `ZMod p`.
  have h1 := (curve_equation x y).mp h.1
  have h2 := (curve_equation x (chosenY x)).mp (chosenY_valid h).1
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  linear_combination h1 - h2

/-- Encodes `0` as `none` and a finite point `(x, y)` as `some (x, decide (y = chosenY x))`. -/
noncomputable def pointCode : curve.toAffine.Point → Option (ZMod Fp.modulus × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y = chosenY x))

/-- `pointCode` is injective because `x` and `decide (y = chosenY x)` uniquely pick `y` in `{chosenY x, -chosenY x}`. -/
theorem pointCode_injective : Function.Injective pointCode := by
  classical
  intro P Q h
  cases P with
  | zero => cases Q <;> simp_all [pointCode]
  | some x y hp =>
    cases Q with
    | zero => simp [pointCode] at h
    | some xx yy hq =>
      have he : x = xx ∧ decide (y = chosenY x) = decide (yy = chosenY xx) := by
        simpa only [pointCode, Option.some.injEq, Prod.mk.injEq] using h
      rcases he with ⟨rfl, he⟩
      -- Recover `y = yy` from the boolean sign flag in `{chosenY x, -chosenY x}`.
      have hy : y = yy := by
        by_cases hy : y = chosenY x
        · have hyy : yy = chosenY x := of_decide_eq_true
            (by simpa only [hy, decide_true] using he.symm)
          exact hy.trans hyy.symm
        · have hyy : yy ≠ chosenY x := of_decide_eq_false
            (by simpa only [decide_eq_false hy] using he.symm)
          exact ((y_eq_or_neg_chosen hp).resolve_left hy).trans
            ((y_eq_or_neg_chosen hq).resolve_left hyy).symm
      subst yy
      rfl

instance : Finite curve.toAffine.Point :=
  Finite.of_injective pointCode pointCode_injective

/-- Bounds `#E(Fp) <= 2 * p + 1` via injection into an optional pair of a residue mod `p` and a sign bit. -/
theorem card_point_le : Nat.card curve.toAffine.Point ≤ 2 * Fp.modulus + 1 := by
  classical
  let _ : Fintype curve.toAffine.Point := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective pointCode pointCode_injective
  rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
    ZMod.card] at h
  simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using h

end EthLib.Cryptography.Bls.G1

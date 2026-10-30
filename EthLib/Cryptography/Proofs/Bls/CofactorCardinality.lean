module

public import EthLib.Cryptography.Proofs.Bls.CofactorAlgebra
public import Mathlib.GroupTheory.Index

/-!
# Proofs: Elementary cardinality bound for the `G2` twist curve

A finite point `(x, y)` on `E' : y^2 = x^3 + 4*(1 + i)` is fixed by `x` and the choice between `y` and `-y`.

`Fp2` has `p^2` elements, and there is one point at infinity.

So `#E'(Fp2) <= 2 * p^2 + 1`, with no appeal to Hasse's theorem.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G2

open WeierstrassCurve.Affine

/-- Witness `y`-coordinate when some `y` in `Fp2` lies on `E'` above `x`, or `0` otherwise. -/
noncomputable def chosenY (x : Fp2) : Fp2 := by
  classical
  exact if h : ∃ y, curve.toAffine.Nonsingular x y then Classical.choose h else 0

private theorem chosenY_valid {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular x (chosenY x) := by
  have he : ∃ y, curve.toAffine.Nonsingular x y := ⟨y, h⟩
  simpa only [chosenY, dite_eq_left he] using Classical.choose_spec he

private theorem y_eq_or_neg_chosen {x y : Fp2} (h : curve.toAffine.Nonsingular x y) :
    y = chosenY x ∨ y = -(chosenY x) := by
  have h1 := (TwistFrobenius.short_equation bTwist x y).mp h.1
  have h2 := (TwistFrobenius.short_equation bTwist x (chosenY x)).mp (chosenY_valid h).1
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  linear_combination h1 - h2

/-- Encodes `0` as `none` and a finite twist point `(x, y)` as `some (x, decide (y = chosenY x))`. -/
noncomputable def pointCode : curve.toAffine.Point → Option (Fp2 × Bool)
  | .zero => none
  | .some x y _ => some (x, decide (y = chosenY x))

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

/-- Elementary upper bound `#E'(Fp2) <= 2 * p^2 + 1`. -/
theorem card_point_le : Nat.card curve.toAffine.Point ≤ 2 * Fp.modulus ^ 2 + 1 := by
  classical
  let _ : Fintype curve.toAffine.Point := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective pointCode pointCode_injective
  rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool, TwistFrobenius.card_fp2] at h
  simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using h

end EthLib.Cryptography.Bls.G2

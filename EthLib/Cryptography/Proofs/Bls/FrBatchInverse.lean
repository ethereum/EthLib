import EthLib.Cryptography.Proofs.Bls.FrZMod

/-!
# Proofs: batch inversion computes every inverse

`Fr.batchInverse` inverts a whole array with one inversion.

The headline result is `batchInverse_eq_map`: it returns `xs.map inverse`, for every input.

Zeros included, since both sides map zero to zero.
-/

namespace EthLib.Cryptography.Bls.Fr

open scoped EthLib.Cryptography.Bls.Fr

/-- `isZero` tests equality with zero. -/
private theorem isZero_iff' (a : Fr) : a.isZero = true ↔ a = 0 := by
  unfold isZero
  rw [beq_iff_eq]
  exact ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩

/-- The algebra of one step, in any field.

It is stated generically, as in `VanishingNonzero`, so the scoped field instance on `Fr` is used without a diamond. -/
private theorem step_inverses {F : Type*} [Field F] {pre x : F} (hpre : pre ≠ 0) (hx : x ≠ 0) :
    pre * (pre * x)⁻¹ = x⁻¹ ∧ (pre * x)⁻¹ * x = pre⁻¹ := by
  refine ⟨?_, ?_⟩ <;> field_simp

/-- A product of nonzero elements is nonzero, in any field. -/
private theorem field_mul_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 :=
  mul_ne_zero ha hb

/-- The recursion returns every inverse, and the inverse of the prefix product. -/
theorem batchInverseAux_eq (pre : Fr) (hpre : pre ≠ 0) (xs : List Fr) :
    batchInverseAux pre xs = (xs.map inverse, pre.inverse) := by
  induction xs generalizing pre with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.isZero = true
    -- A zero is skipped, and its inverse is zero.
    · have hx0 : x = 0 := (isZero_iff' x).mp hx
      rw [batchInverseAux, ite_eq_left hx, ih pre hpre, List.map_cons, hx0]
      simp only [inverse_eq_inv]
      -- `0⁻¹` sits under an instance path `rw` does not match, so `inv_zero` goes in by `congrArg`.
      exact congrArg (fun z => (z :: List.map inverse xs, pre⁻¹)) (inv_zero (G₀ := Fr)).symm
    -- A nonzero x moves into the prefix product.
    --
    --     s = (pre * x)⁻¹   →   pre * s = x⁻¹   and   s * x = pre⁻¹
    · have hx0 : x ≠ 0 := fun h => hx ((isZero_iff' x).mpr h)
      rw [batchInverseAux, ite_eq_right hx, ih (pre * x) (field_mul_ne_zero (F := Fr) hpre hx0), List.map_cons]
      obtain ⟨h1, h2⟩ := step_inverses (F := Fr) hpre hx0
      simp only [inverse_eq_inv, Prod.mk.injEq, List.cons.injEq]
      exact ⟨⟨h1, trivial⟩, h2⟩

/-- Batch inversion equals elementwise inversion. -/
theorem batchInverse_eq_map (xs : Array Fr) : batchInverse xs = xs.map inverse := by
  rw [batchInverse, batchInverseAux_eq one (by decide) xs.toList]
  apply Array.ext' 
  simp

end EthLib.Cryptography.Bls.Fr

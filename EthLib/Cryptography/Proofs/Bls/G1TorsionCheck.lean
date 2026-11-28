module

public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G1Order
public import EthLib.Cryptography.Proofs.Bls.FpModel
public import EthLib.Cryptography.Proofs.Bls.CurveMap
public import EthLib.Cryptography.Proofs.Bls.G1NatCheck

/-!
# Proofs: a kernel check that a point of `G1` has order dividing `r`

A point `P` of `G1` lies in the subgroup of order `r` when `[r] P` is the point at infinity.

The kernel can check this for a concrete point by running the scalar product.

The BLS parameter is `t = -0xd201000000010000`, and `r = t^4 - t^2 + 1`.

So the check computes `[r] P` as `[t^2] ([t^2] P - P) + P`.

The check on naturals has a module of its own; this one proves that it agrees with `G1`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1.TorsionCheck

open WeierstrassCurve.Jacobian

/-- The coordinates of a point, as naturals below `p`. -/
def coords (q : G1) : Coords := (q.x.val, q.y.val, q.z.val)

/-- The sum in the notation of `Fin`, for proofs. -/
private theorem fadd_eq (a b : Nat) : fadd a b = (a + b) % Fp.modulus := rfl

/-- The product in the notation of `Fin`, for proofs. -/
private theorem fmul_eq (a b : Nat) : fmul a b = a * b % Fp.modulus := rfl

/-! ## The values agree with `Fp` -/

/-- The kernel evaluates the equality test of naturals directly.

It agrees with the equality test that the spec writes. -/
private theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by simp)

/-- The coordinates of a point over the model of the kernel, as naturals below `p`. -/
private def modelCoords (q : G1 Fp.Model) : Coords := (q.x.val, q.y.val, q.z.val)

/-- A point and its image in the model have the same coordinates. -/
private theorem coords_eq (q : G1) : coords q = modelCoords (G1.map Fp.toModel.toHom q) := by
  simp only [coords, modelCoords, G1.map, Fp.val_toModel]

private theorem modelCoords_double (q : G1 Fp.Model) :
    modelCoords (G1.double q) = double (modelCoords q) := by
  unfold G1.double double
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((modelCoords q).2.2 == 0) = BaseField.isZero q.z from rfl]
  by_cases h : BaseField.isZero q.z = true <;> simp only [h, ↓reduceIte]
  rfl

private theorem modelCoords_addMixed (p q : G1 Fp.Model) :
    modelCoords (G1.addMixed p q) = addMixed (modelCoords p) (modelCoords q) := by
  unfold G1.addMixed addMixed
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((modelCoords p).1 == fmul (modelCoords q).1
      (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq p.x (q.x * FieldOps.square p.z) from rfl,
    show ((modelCoords p).2.1 == fmul (fmul (modelCoords q).2.1 (modelCoords p).2.2)
      (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq p.y (q.y * p.z * FieldOps.square p.z) from rfl]
  by_cases h₁ : BaseField.beq p.x (q.x * FieldOps.square p.z) = true
  · by_cases h₂ : BaseField.beq p.y (q.y * p.z * FieldOps.square p.z) = true
    · simp only [h₁, h₂, ↓reduceIte, modelCoords_double]
    · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [h₁, ↓reduceIte, Bool.false_eq_true]
    rfl

private theorem modelCoords_addGeneral (p q : G1 Fp.Model) :
    modelCoords (G1.addGeneral p q) = addGeneral (modelCoords p) (modelCoords q) := by
  unfold G1.addGeneral addGeneral
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show (fmul (modelCoords p).1 (fmul (modelCoords q).2.2 (modelCoords q).2.2) ==
      fmul (modelCoords q).1 (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq (p.x * FieldOps.square q.z) (q.x * FieldOps.square p.z) from rfl,
    show (fmul (fmul (modelCoords p).2.1 (modelCoords q).2.2)
      (fmul (modelCoords q).2.2 (modelCoords q).2.2) ==
      fmul (fmul (modelCoords q).2.1 (modelCoords p).2.2)
        (fmul (modelCoords p).2.2 (modelCoords p).2.2)) =
      BaseField.beq (p.y * q.z * FieldOps.square q.z) (q.y * p.z * FieldOps.square p.z) from rfl]
  by_cases h₁ : BaseField.beq (p.x * FieldOps.square q.z) (q.x * FieldOps.square p.z) = true
  · by_cases h₂ :
      BaseField.beq (p.y * q.z * FieldOps.square q.z) (q.y * p.z * FieldOps.square p.z) = true
    · simp only [h₁, h₂, ↓reduceIte, modelCoords_double]
    · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      rfl
  · simp only [h₁, ↓reduceIte, Bool.false_eq_true]
    rfl

private theorem modelCoords_add (p q : G1 Fp.Model) :
    modelCoords (G1.add p q) = add (modelCoords p) (modelCoords q) := by
  unfold G1.add add
  simp only [beq_eq, Bool.cond_eq_ite]
  rw [show ((modelCoords p).2.2 == 0) = BaseField.isZero p.z from rfl,
    show ((modelCoords q).2.2 == 0) = BaseField.isZero q.z from rfl,
    show ((modelCoords q).2.2 == 1) = BaseField.beq q.z BaseField.one from rfl]
  by_cases h₁ : BaseField.isZero p.z = true
  · simp only [h₁, ↓reduceIte]
  by_cases h₂ : BaseField.isZero q.z = true
  · simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
  by_cases h₃ : BaseField.beq q.z BaseField.one = true
  · simp only [h₁, h₂, h₃, ↓reduceIte, Bool.false_eq_true, modelCoords_addMixed]
  · simp only [h₁, h₂, h₃, ↓reduceIte, Bool.false_eq_true, modelCoords_addGeneral]

theorem coords_double (q : G1) : coords (G1.double q) = double (coords q) := by
  rw [coords_eq, G1.map_double, modelCoords_double, ← coords_eq]

theorem coords_addMixed (p q : G1) : coords (G1.addMixed p q) = addMixed (coords p) (coords q) := by
  rw [coords_eq, G1.map_addMixed, modelCoords_addMixed, ← coords_eq, ← coords_eq]

theorem coords_addGeneral (p q : G1) :
    coords (G1.addGeneral p q) = addGeneral (coords p) (coords q) := by
  rw [coords_eq, G1.map_addGeneral, modelCoords_addGeneral, ← coords_eq, ← coords_eq]

theorem coords_add (p q : G1) : coords (G1.add p q) = add (coords p) (coords q) := by
  have h := G1.map_add Fp.toModel.toHom p q
  rw [coords_eq, show G1.map Fp.toModel.toHom (G1.add p q) = G1.add (G1.map Fp.toModel.toHom p)
    (G1.map Fp.toModel.toHom q) from h, modelCoords_add, ← coords_eq, ← coords_eq]

theorem coords_neg (q : G1) : coords (G1.neg q) = neg (coords q) := by
  simp only [coords, neg, G1.neg, Fp.val_neg]

theorem coords_zero : coords (G1.zero : G1) = zero := by
  rw [coords_eq, G1.map_zero]
  rfl

theorem coords_mulNat (q : G1) (k : Nat) : coords (G1.mulNat q k) = mulNat (coords q) k := by
  rw [G1.mulNat, mulNat, ScalarProduct.map_naf coords coords_double coords_add, coords_zero,
    coords_neg]

/-! ## The check -/

/-- The check computes the coordinates of the chain `G1.mulModulus`, step for step. -/
private theorem coords_mulModulus (q : G1) :
    coords (G1.mulModulus q) = mulModulus (coords q) := by
  simp only [G1.mulModulus, mulModulus, coords_add, coords_mulNat, coords_neg]

/-- A point `(x, y, 1)` of the curve whose `x` passes the check has order dividing `r`. -/
theorem modulus_smul_eq_zero {x y : Fp} (hc : check x.val = true)
    (hy : y * y = x * x * x + Fp.ofNat 4) :
    Fr.modulus • toPoint ⟨x, y, Fp.one⟩ = 0 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, fadd_eq, fmul_eq] at hc
  obtain ⟨⟨-, hsq⟩, hz⟩ := hc
  -- The candidate root, as an element of `Fp`.
  obtain ⟨y₀, hy₀v⟩ : ∃ y₀ : Fp, y₀.val = rootCandidate x.val :=
    ⟨_, Fp.val_ofNat_of_lt (Nat.mod_lt _ Fp.modulus_pos)⟩
  have hy₀ : y₀ * y₀ = x * x * x + Fp.ofNat 4 := by
    apply Fp.ext
    rw [Fp.val_mul, Fp.val_add, Fp.val_mul, Fp.val_mul, Fp.val_ofNat, hy₀v]
    exact hsq
  have hv : Valid ⟨x, y₀, Fp.one⟩ := valid_of_affine_eq hy₀
  -- The chain reaches the point at infinity, so `[r] (x, y₀, 1) = 0`.
  have hr : Fr.modulus • toPoint ⟨x, y₀, Fp.one⟩ = 0 := by
    rw [← toPoint_mulModulus hv]
    have hc : coords ⟨x, y₀, Fp.one⟩ = (x.val, rootCandidate x.val, 1) := by
      simp only [coords, hy₀v, Fp.one_def, Fp.val_one]
    have h := congrArg (fun c : Coords => c.2.2) (coords_mulModulus ⟨x, y₀, Fp.one⟩)
    rw [hc, hz] at h
    generalize G1.mulModulus ⟨x, y₀, Fp.one⟩ = X at h ⊢
    apply Point.toAffine_of_Z_eq_zero
    rw [rep_z]
    apply (isZero_iff (a := X.z)).mp
    rw [Fp.isZero_eq]
    exact beq_iff_eq.mpr h
  have hsq' : Fp.toZMod y * Fp.toZMod y = Fp.toZMod y₀ * Fp.toZMod y₀ := by
    rw [← Fp.toZMod_mul, ← Fp.toZMod_mul, hy, hy₀]
  rcases sqrt_pm hsq' with h | h
  · rw [Fp.toZMod_inj.mp h]
    exact hr
  · have hn : y = -y₀ := Fp.toZMod.injective (by rw [h, Fp.toZMod_neg])
    rw [show (⟨x, y, Fp.one⟩ : G1) = G1.neg ⟨x, y₀, Fp.one⟩ by rw [hn]; rfl,
      toPoint_neg hv, neg_nsmul, hr, neg_zero]

end EthLib.Cryptography.Bls.G1.TorsionCheck

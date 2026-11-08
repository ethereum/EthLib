module

public import EthLib.Cryptography.Proofs.Bls.G1Order
public import EthLib.Cryptography.Proofs.ScaledCurve

/-!
# Proofs: the endomorphism `σ(x, y) = (β x, y)` of `G1`

The subgroup check of `G1` tests `σ(P) = [-t^2] P`, after Scott.
<https://eprint.iacr.org/2021/1130>

This file proves the facts on `σ` that the check needs.

- `σ` scales `x` by `β^4 = β` and `y` by `β^6 = 1`, so it is a group endomorphism of `E(Fp)`.
- `P + σ(P) + σ(σ(P)) = 0` for every `P`, since the three points lie on one line `Y = y`.
- So `σ(P) = [-n] P` gives `[n^2 - n + 1] P = 0`, and `t^4 - t^2 + 1 = r`.
- The kernel checks `σ(g_1) = [-t^2] g_1` for the generator.

Projective equality of Jacobian triples agrees with equality of the points they denote.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1

open WeierstrassCurve WeierstrassCurve.Jacobian

local notation "F" => ZMod Fp.modulus

/-! ## Projective equality -/

theorem toPoint_eq_iff_rep_equiv {p q : G1} (hp : Valid p) (hq : Valid q) :
    toPoint p = toPoint q ↔ rep p ≈ rep q := by
  constructor
  · intro h
    have he : ({ point := ⟦rep p⟧, nonsingular := hp } : curve.Point) =
        ({ point := ⟦rep q⟧, nonsingular := hq } : curve.Point) :=
      (Point.toAffineAddEquiv curve).injective h
    exact Quotient.eq.mp (congrArg Point.point he)
  · exact Point.toAffine_of_equiv

theorem projectiveEq_eq_true_iff_rep_equiv {p q : G1} (hp : Valid p) (hq : Valid q) :
    projectiveEq p q = true ↔ rep p ≈ rep q := by
  have hz (a : G1) : BaseField.isZero a.z = true ↔ rep a 2 = 0 := isZero_iff
  unfold projectiveEq
  by_cases hpz : BaseField.isZero p.z = true
  · rw [ite_eq_left hpz]
    constructor
    · intro hqz
      exact equiv_of_Z_eq_zero hp hq ((hz p).mp hpz) ((hz q).mp hqz)
    · intro he
      exact (hz q).mpr ((Z_eq_zero_of_equiv he).mp ((hz p).mp hpz))
  · rw [ite_eq_right hpz]
    by_cases hqz : BaseField.isZero q.z = true
    · rw [ite_eq_left hqz]
      exact iff_of_false Bool.false_ne_true
        (not_equiv_of_Z_eq_zero_right (fun h => hpz ((hz p).mpr h)) ((hz q).mp hqz))
    · rw [ite_eq_right hqz, Bool.and_eq_true]
      have hx : BaseField.beq (p.x * (q.z * q.z)) (q.x * (p.z * p.z)) = true ↔
          rep p 0 * rep q 2 ^ 2 = rep q 0 * rep p 2 ^ 2 := by
        rw [show BaseField.beq (p.x * (q.z * q.z)) (q.x * (p.z * p.z)) =
          (p.x * (q.z * q.z)).beq (q.x * (p.z * p.z)) from rfl, beq_iff]
        simp only [rep_x, rep_z, Fp.toZMod_mul]
        constructor <;> intro h <;> linear_combination h
      have hy : BaseField.beq (p.y * (q.z * q.z * q.z)) (q.y * (p.z * p.z * p.z)) = true ↔
          rep p 1 * rep q 2 ^ 3 = rep q 1 * rep p 2 ^ 3 := by
        rw [show BaseField.beq (p.y * (q.z * q.z * q.z)) (q.y * (p.z * p.z * p.z)) =
          (p.y * (q.z * q.z * q.z)).beq (q.y * (p.z * p.z * p.z)) from rfl, beq_iff]
        simp only [rep_y, rep_z, Fp.toZMod_mul]
        constructor <;> intro h <;> linear_combination h
      rw [hx, hy]
      constructor
      · rintro ⟨h1, h2⟩
        exact equiv_of_X_eq_of_Y_eq (fun h => hpz ((hz p).mpr h))
          (fun h => hqz ((hz q).mpr h)) h1 h2
      · intro he
        exact ⟨X_eq_of_equiv he, Y_eq_of_equiv he⟩

/-- On valid triples, projective equality is equality of the points they denote. -/
theorem projectiveEq_eq_true_iff_toPoint_eq {p q : G1} (hp : Valid p) (hq : Valid q) :
    projectiveEq p q = true ↔ toPoint p = toPoint q :=
  (projectiveEq_eq_true_iff_rep_equiv hp hq).trans (toPoint_eq_iff_rep_equiv hp hq).symm

/-! ## `β` in `ZMod p` -/

/-- `β` as an element of `ZMod p`. -/
def betaZ : F :=
  0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe

/-- The constant `β` of the specification reads the same in `ZMod p`. -/
theorem toZMod_beta : Fp.toZMod (beta : Fp) = betaZ :=
  Fp.toZMod_ofNat _

theorem betaZ_cube : betaZ ^ 3 = 1 := by decide

theorem betaZ_ne_one : betaZ ≠ 1 := by decide

theorem betaZ_ne_zero : betaZ ≠ 0 := by decide

/-- `β` is a root of `1 + X + X^2`, since `β^3 = 1` and `β ≠ 1`. -/
theorem one_add_beta_add_sq : 1 + betaZ + betaZ ^ 2 = 0 := by
  have h : (betaZ - 1) * (1 + betaZ + betaZ ^ 2)
      = 0 := by
    linear_combination betaZ_cube
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr betaZ_ne_one)

/-! ## `σ` as a group endomorphism -/

theorem scale_six : (RingHom.id F) 4 * (betaZ ^ 2) ^ 6 = 4 := by
  rw [RingHom.id_apply, ← pow_mul, show 2 * 6 = 3 * 4 from rfl, pow_mul, betaZ_cube, one_pow,
    mul_one]

/-- The map `(x, y) ↦ (x u^2, y u^3)` with `u = β^2`, which is `(x, y) ↦ (β x, y)`. -/
noncomputable def sigmaHom : curve.toAffine.Point →+ curve.toAffine.Point :=
  ShortWeierstrass.scaledHom (RingHom.id F) (pow_ne_zero 2 betaZ_ne_zero) scale_six

private theorem scale_x (x : F) : (RingHom.id F) x * (betaZ ^ 2) ^ 2 =
    betaZ * x := by
  rw [RingHom.id_apply]
  linear_combination x * betaZ * betaZ_cube

private theorem scale_y (y : F) : (RingHom.id F) y * (betaZ ^ 2) ^ 3 = y := by
  rw [RingHom.id_apply]
  linear_combination y * (betaZ ^ 3 + 1) * betaZ_cube

/-- `(β x, y)` is on the curve when `(x, y)` is. -/
theorem nonsingular_beta {x y : F} (h : curve.toAffine.Nonsingular x y) :
    curve.toAffine.Nonsingular (betaZ * x) y := by
  have hs := ShortWeierstrass.scaled_nonsingular (RingHom.id F) _
    (pow_ne_zero 2 betaZ_ne_zero) scale_six h
  rwa [scale_x, scale_y] at hs

/-- Points with the same coordinates are equal, whatever the proofs that they are on the curve. -/
private theorem some_congr {x y x' y' : F} (hx : x = x') (hy : y = y')
    (h : curve.toAffine.Nonsingular x y) (h' : curve.toAffine.Nonsingular x' y') :
    (Affine.Point.some x y h : curve.toAffine.Point) = .some x' y' h' := by
  subst hx hy
  rfl

theorem sigmaHom_some {x y : F} (h : curve.toAffine.Nonsingular x y) :
    sigmaHom (.some x y h) = .some _ _ (nonsingular_beta h) :=
  some_congr (scale_x x) (scale_y y) _ _

/-- `P + σ(P) + σ(σ(P)) = 0`, since the three points lie on the line `Y = y`. -/
theorem add_sigmaHom_add_sigmaHom (P : curve.toAffine.Point) :
    P + sigmaHom P + sigmaHom (sigmaHom P) = 0 := by
  cases P with
  | zero => rw [← Affine.Point.zero_def, _root_.map_zero, _root_.map_zero, add_zero, add_zero]
  | some x y h =>
    rw [sigmaHom_some, sigmaHom_some]
    have h₃ := nonsingular_beta (nonsingular_beta h)
    have h₃' : curve.toAffine.Nonsingular (betaZ ^ 2 * x) y := by
      rwa [← mul_assoc, ← sq] at h₃
    rw [some_congr (by ring) rfl h₃ h₃']
    exact ShortWeierstrass.some_add_some_add_some one_add_beta_add_sq betaZ_ne_one h _ _

/-- Scott's criterion: if `σ(P) = [-t^2] P`, then `[r] P = 0`.

Applying `σ` again gives `σ(σ(P)) = [t^4] P`, so `[t^4 - t^2 + 1] P = 0`. -/
theorem modulus_smul_eq_zero_of_sigmaHom {P : curve.toAffine.Point}
    (h : sigmaHom P = -((blsX * blsX) • P)) : Fr.modulus • P = 0 := by
  have h2 : sigmaHom (sigmaHom P) = ((blsX * blsX) * (blsX * blsX)) • P := by
    rw [h, _root_.map_neg, _root_.map_nsmul, h, neg_nsmul, neg_neg, smul_smul]
  have hs := add_sigmaHom_add_sigmaHom P
  rw [h2, h] at hs
  have hle : blsX * blsX ≤ blsX * blsX * (blsX * blsX) := Nat.le_mul_of_pos_right _ (by decide)
  rw [Fr.modulus_eq_blsX, show blsX ^ 4 - blsX ^ 2 + 1 =
      (blsX * blsX * (blsX * blsX) - blsX * blsX) + 1 by decide,
    add_nsmul, sub_nsmul P hle, one_nsmul, ← hs]
  abel

/-! ## `σ` on spec points

The lemmas below hold for any `a` in place of `β`, as long as `a` reads as `β` in `ZMod p`.

They are stated so, so that no proof unfolds the numeral of `β`.
-/

/-- Scaling `X` by `a` multiplies the first coordinate of the representative by `a`. -/
theorem rep_scale (a : Fp) (P : G1) :
    rep ⟨a * P.x, P.y, P.z⟩ = ![Fp.toZMod a * rep P 0, rep P 1, rep P 2] := by
  rw [show rep ⟨a * P.x, P.y, P.z⟩ = ![Fp.toZMod (a * P.x), Fp.toZMod P.y, Fp.toZMod P.z] from rfl,
    Fp.toZMod_mul]
  rfl

theorem rep_sigma (P : G1) : rep (sigma P) = ![betaZ * rep P 0, rep P 1, rep P 2] := by
  rw [← toZMod_beta]
  exact rep_scale beta P

/-- Scaling `X` by a cube root of unity keeps a Jacobian triple nonsingular. -/
theorem nonsingular_scale {a : F} (ha : a ^ 3 = 1) {P : Fin 3 → F} (h : curve.Nonsingular P) :
    curve.Nonsingular ![a * P 0, P 1, P 2] := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  rw [nonsingular_iff, equation_iff] at h ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl, show curve.a₆ = 4 from rfl,
    zero_mul, mul_zero, add_zero] at h ⊢
  obtain ⟨he, hd⟩ := h
  refine ⟨by linear_combination he - P 0 ^ 3 * ha, ?_⟩
  rcases hd with hd | hd
  · left
    rw [show 0 - 3 * (a * P 0) ^ 2 = a ^ 2 * (0 - 3 * P 0 ^ 2) by ring]
    exact mul_ne_zero (pow_ne_zero 2 ha0) hd
  · right
    exact hd

/-- With `u^3 = 1`, the scaling `(x, y) ↦ (u^2 x, u^3 y)` maps `(X, Y, Z)` to `(u^2 X, Y, Z)`. -/
theorem toAffine_scale {u : F} (hu : u ≠ 0) (hc : (RingHom.id F) 4 * u ^ 6 = 4)
    (hu3 : u ^ 3 = 1) {P : Fin 3 → F} (h : curve.Nonsingular P) :
    Point.toAffine curve ![u ^ 2 * P 0, P 1, P 2] =
      ShortWeierstrass.scaledHom (RingHom.id F) hu hc (Point.toAffine curve P) := by
  have ha : (u ^ 2) ^ 3 = 1 := by rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hu3,
    one_pow]
  by_cases hz : P 2 = 0
  · rw [Point.toAffine_of_Z_eq_zero (show (![u ^ 2 * P 0, P 1, P 2] : Fin 3 → F) 2 = 0 from hz),
      Point.toAffine_of_Z_eq_zero hz]
    rfl
  · have hz' : (![u ^ 2 * P 0, P 1, P 2] : Fin 3 → F) 2 ≠ 0 := hz
    rw [Point.toAffine_of_Z_ne_zero h hz, Point.toAffine_of_Z_ne_zero (nonsingular_scale ha h) hz']
    show _ = Affine.Point.some _ _ _
    apply some_congr
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        RingHom.id_apply]
      ring
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, RingHom.id_apply, hu3, mul_one]

theorem valid_sigma {P : G1} (h : Valid P) : Valid (sigma P) := by
  rw [Valid, rep_sigma]
  exact nonsingular_scale betaZ_cube h

theorem toPoint_sigma {P : G1} (h : Valid P) : toPoint (sigma P) = sigmaHom (toPoint P) := by
  have hb : (betaZ ^ 2) ^ 2 = betaZ := by linear_combination betaZ * betaZ_cube
  have hb3 : (betaZ ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, betaZ_cube, one_pow]
  rw [toPoint, toPoint, rep_sigma, ← hb]
  exact toAffine_scale (pow_ne_zero 2 betaZ_ne_zero) scale_six hb3 h

/-! ## The eigenvalue on the generator -/

/-- A map of base fields fixes `β`. -/
theorem map_beta {K L : Type} [BaseField K] [BaseField L] (f : BaseField.Hom K L) :
    f beta = beta :=
  f.map_ofNat _

/-- A map of base fields commutes with `σ`. -/
theorem map_sigma {K L : Type} [BaseField K] [BaseField L] (f : BaseField.Hom K L) (p : G1 K) :
    map f (sigma p) = sigma (map f p) := by
  simp only [sigma, map, f.map_mul, map_beta]

/-- A map of base fields keeps the projective equality of two points. -/
theorem map_projectiveEq {K L : Type} [BaseField K] [BaseField L] (f : BaseField.Hom K L)
    (p q : G1 K) : projectiveEq (map f p) (map f q) = projectiveEq p q := by
  simp only [projectiveEq, map, f.map_isZero, ← f.map_mul, f.map_beq]

/-- `σ(g_1) = [-t^2] g_1`, checked by the kernel in the model of `Fp`. -/
theorem projectiveEq_sigma_generator :
    projectiveEq (sigma (generator : G1)) (neg (mulNat (mulNat generator blsX) blsX)) = true := by
  rw [← mulNatAux_eq 64 generator blsX (by decide),
    ← mulNatAux_eq 64 _ blsX (by decide), ← map_projectiveEq Fp.toModel, map_sigma,
    map_neg_fn, map_mulNatAux, map_mulNatAux, map_generator]
  decide +kernel

theorem sigmaHom_generator :
    sigmaHom (toPoint generator) = -((blsX * blsX) • toPoint generator) := by
  have hv := valid_mulNat (valid_mulNat valid_generator blsX) blsX
  rw [← toPoint_sigma valid_generator,
    (projectiveEq_eq_true_iff_toPoint_eq (valid_sigma valid_generator) (valid_neg hv)).mp
      projectiveEq_sigma_generator,
    toPoint_neg hv, toPoint_mulNat (valid_mulNat valid_generator blsX),
    toPoint_mulNat valid_generator, smul_smul]

end EthLib.Cryptography.Bls.G1

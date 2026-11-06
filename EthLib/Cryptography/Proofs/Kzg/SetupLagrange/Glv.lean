module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Points
public import EthLib.Cryptography.Proofs.Bls.G1Rotation

/-!
# Proofs: products by a scalar that split it in two halves

Let `z` be the BLS parameter, and let `λ = z^2 - 1`.

Then `λ^2 + λ + 1 = r`, so `λ` is a cube root of unity mod `r`, and `λ < 2^128`.

The map `(x, y) ↦ (β' x, y)` sends the curve to itself, for a cube root of unity `β'` of `Fp`.

It is a group homomorphism, and on the points of order dividing `r` it is the product by `λ`.

The proof checks this on the generator, which spans those points.

So a product `[s] P` with `s < r` equals `[s mod λ] P + [s / λ] (β' x, y)`.

Both scalars are below `2^128`, and one run of double and add computes the two products together.

That takes 128 doublings instead of 255.

The run uses the operations of the torsion check, on naturals, so the kernel can run it.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.G1
open WeierstrassCurve WeierstrassCurve.Jacobian

local notation "F" => ZMod Fp.modulus

/-! ## The endomorphism -/

/-- The cube root of unity `β'` of `Fp`, as a natural. -/
def cubeRootNat : Nat :=
  0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac

/-- The cube root of unity `β' = β^2`. -/
def cubeRoot : F := G1Rotation.beta ^ 2

/-- The scalar `λ = z^2 - 1`. -/
def eigenvalue : Nat := blsX ^ 2 - 1

theorem cubeRoot_val : cubeRoot.val = cubeRootNat := by decide +kernel

theorem cubeRoot_cube : cubeRoot ^ 3 = 1 := by
  rw [cubeRoot, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, G1Rotation.beta_cube, one_pow]

theorem beta_ne_zero : (G1Rotation.beta : F) ≠ 0 := by decide

theorem four_mul_beta_pow_six : (RingHom.id F) 4 * G1Rotation.beta ^ 6 = 4 := by
  rw [RingHom.id_apply, show 6 = 3 * 2 from rfl, pow_mul, G1Rotation.beta_cube, one_pow, mul_one]

/-- The map `(x, y) ↦ (β' x, y)` of the curve, as a group homomorphism. -/
noncomputable def endoHom : curve.toAffine.Point →+ curve.toAffine.Point :=
  ShortWeierstrass.scaledHom (RingHom.id F) beta_ne_zero four_mul_beta_pow_six

/-- The map `(x, y) ↦ (β' x, y)`, in Jacobian coordinates. -/
def endo (q : G1) : G1 := ⟨cubeRoot * rep q 0, q.y, q.z⟩

private theorem rep_endo (q : G1) : rep (endo q) = ![cubeRoot * rep q 0, rep q 1, rep q 2] := by
  funext i
  fin_cases i <;> rfl

private theorem nonsingular_endo {P : Fin 3 → F} (h : curve.Nonsingular P) :
    curve.Nonsingular ![cubeRoot * P 0, P 1, P 2] := by
  have hb := cubeRoot_cube
  have hb0 : cubeRoot ≠ 0 := by decide +kernel
  rw [nonsingular_iff, equation_iff] at h ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, show curve.a₁ = 0 from rfl, show curve.a₂ = 0 from rfl,
    show curve.a₃ = 0 from rfl, show curve.a₄ = 0 from rfl, show curve.a₆ = 4 from rfl,
    zero_mul, mul_zero, add_zero] at h ⊢
  obtain ⟨he, hd⟩ := h
  refine ⟨by linear_combination he - P 0 ^ 3 * hb, ?_⟩
  rcases hd with hd | hd
  · left
    rw [show 0 - 3 * (cubeRoot * P 0) ^ 2 = cubeRoot ^ 2 * (0 - 3 * P 0 ^ 2) by ring]
    exact mul_ne_zero (pow_ne_zero 2 hb0) hd
  · right
    exact hd

theorem valid_endo {q : G1} (h : Valid q) : Valid (endo q) := by
  rw [Valid, rep_endo]
  exact nonsingular_endo h

/-- An affine point `(x', y')` with `x' = β' x` and `y' = y` is the image of `(x, y)`. -/
private theorem some_eq_endoHom {x y x' y' : F} {h : curve.toAffine.Nonsingular x y}
    {h' : curve.toAffine.Nonsingular x' y'} (hx : x' = x * G1Rotation.beta ^ 2)
    (hy : y' = y * G1Rotation.beta ^ 3) :
    Affine.Point.some x' y' h' = endoHom (.some x y h) := by
  subst hx hy
  rfl

private theorem toAffine_endo {P : Fin 3 → F} (h : curve.Nonsingular P) :
    Point.toAffine curve ![cubeRoot * P 0, P 1, P 2] = endoHom (Point.toAffine curve P) := by
  by_cases hz : P 2 = 0
  · rw [Point.toAffine_of_Z_eq_zero (show (![cubeRoot * P 0, P 1, P 2] : Fin 3 → F) 2 = 0 from hz),
      Point.toAffine_of_Z_eq_zero hz, _root_.map_zero]
  · have hz' : (![cubeRoot * P 0, P 1, P 2] : Fin 3 → F) 2 ≠ 0 := hz
    rw [Point.toAffine_of_Z_ne_zero h hz, Point.toAffine_of_Z_ne_zero (nonsingular_endo h) hz']
    refine some_eq_endoHom ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        cubeRoot]
      ring
    · have hb := G1Rotation.beta_cube
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons]
      linear_combination -(P 1 / P 2 ^ 3) * hb

/-- In Jacobian coordinates, the map computes the homomorphism. -/
theorem toPoint_endo {q : G1} (h : Valid q) : toPoint (endo q) = endoHom (toPoint q) := by
  rw [toPoint, toPoint, rep_endo]
  exact toAffine_endo h

/-- The image of the generator `(x, y)` is `(β' x, y)`. -/
private theorem coords_endo_generator :
    TorsionCheck.coords (endo generator) =
      (TorsionCheck.fmul cubeRootNat (TorsionCheck.coords generator).1,
        (TorsionCheck.coords generator).2.1, 1) := by
  decide +kernel

theorem eigenvalue_lt : eigenvalue < 2 ^ 128 := by decide +kernel

/-- On the generator, the homomorphism is the product by `λ`, which the kernel checks. -/
theorem endoHom_generator : endoHom (toPoint generator) = eigenvalue • toPoint generator := by
  rw [← toPoint_endo valid_generator, ← toPoint_mulNat valid_generator,
    ← mulNatAux_eq 128 generator eigenvalue eigenvalue_lt]
  refine (toPoint_eq_of_sameAffine coords_endo_generator ?_).symm
  rw [TorsionCheck.coords_mulNatAux]
  decide +kernel

/-- On a point of order dividing `r`, the map `(x, y) ↦ (β' x, y)` is the product by `λ`. -/
theorem toPoint_endo_of_torsion {q : G1} (h : Valid q) (ht : Fr.modulus • toPoint q = 0) :
    toPoint (endo q) = eigenvalue • toPoint q := by
  obtain ⟨n, -, he⟩ := exists_nsmul_generator_of_modulus_smul_eq_zero ht
  rw [toPoint_endo h, he, map_nsmul, endoHom_generator, smul_comm]

/-! ## Two products in one run -/

/-- `[a] p + [b] q` by double and add from the top bits, with `t = p + q`. -/
def jointMul : Nat → G1 → G1 → G1 → Nat → Nat → G1
  | 0, _, _, _, _, _ => zero
  | fuel + 1, p, q, t, a, b =>
    if a = 0 ∧ b = 0 then zero
    else
      let h := double (jointMul fuel p q t (a / 2) (b / 2))
      if a % 2 = 1 then (if b % 2 = 1 then add h t else add h p)
      else (if b % 2 = 1 then add h q else h)

private theorem nsmul_halves {A : Type*} [AddCommMonoid A] (n : Nat) (P : A) :
    n • P = (n / 2) • P + (n / 2) • P + (n % 2) • P := by
  rw [← add_nsmul, ← add_nsmul]
  congr 1
  omega

theorem jointMul_spec {p q t : G1} (hp : Valid p) (hq : Valid q) (ht : Valid t)
    (hpq : toPoint t = toPoint p + toPoint q) (fuel : Nat) {a b : Nat} (ha : a < 2 ^ fuel)
    (hb : b < 2 ^ fuel) :
    Valid (jointMul fuel p q t a b) ∧
      toPoint (jointMul fuel p q t a b) = a • toPoint p + b • toPoint q := by
  induction fuel generalizing a b with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : b = 0 := by simpa using hb
    simp only [jointMul, zero_nsmul, add_zero]
    exact ⟨valid_zero, toPoint_zero⟩
  | succ fuel ih =>
    rw [Nat.pow_succ] at ha hb
    obtain ⟨hv, hpt⟩ := ih (a := a / 2) (b := b / 2) (by omega) (by omega)
    have hdv := valid_double hv
    have hdp : toPoint (double (jointMul fuel p q t (a / 2) (b / 2))) =
        (a / 2) • toPoint p + (b / 2) • toPoint q +
          ((a / 2) • toPoint p + (b / 2) • toPoint q) := by
      rw [toPoint_double hv, hpt]
    simp only [jointMul]
    by_cases h0 : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp only [and_self, ↓reduceIte, zero_nsmul, add_zero]
      exact ⟨valid_zero, toPoint_zero⟩
    simp only [h0, ↓reduceIte]
    rw [nsmul_halves a, nsmul_halves b]
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;>
      simp only [ha2, hb2, zero_ne_one, ↓reduceIte, one_nsmul, zero_nsmul, add_zero]
    · exact ⟨hdv, by rw [hdp]; abel⟩
    · exact ⟨valid_add hdv hq, by rw [toPoint_add hdv hq, hdp]; abel⟩
    · exact ⟨valid_add hdv hp, by rw [toPoint_add hdv hp, hdp]; abel⟩
    · exact ⟨valid_add hdv ht, by rw [toPoint_add hdv ht, hdp, hpq]; abel⟩

/-- The product by `s`, as `[s mod λ] p + [s / λ] (β' x, y)` in one run. -/
def glvMul (p : G1) (s : Nat) : G1 :=
  let e := endo p
  jointMul 128 p e (add p e) (s % eigenvalue) (s / eigenvalue)

/-- On a point of order dividing `r`, the split product is the product by `s`, for `s < r`. -/
theorem glvMul_spec {p : G1} (hp : Valid p) (ht : Fr.modulus • toPoint p = 0) {s : Nat}
    (hs : s < Fr.modulus) :
    Valid (glvMul p s) ∧ toPoint (glvMul p s) = s • toPoint p := by
  have he := valid_endo hp
  have hlt : Fr.modulus ≤ 2 ^ 128 * eigenvalue := by decide +kernel
  have hpos : 0 < eigenvalue := by decide +kernel
  obtain ⟨hv, hpt⟩ := jointMul_spec hp he (valid_add hp he) (toPoint_add hp he) 128
    (a := s % eigenvalue) (b := s / eigenvalue)
    (Nat.lt_trans (Nat.mod_lt s hpos) eigenvalue_lt)
    ((Nat.div_lt_iff_lt_mul hpos).mpr (Nat.lt_of_lt_of_le hs hlt))
  refine ⟨hv, ?_⟩
  rw [glvMul, hpt, toPoint_endo_of_torsion hp ht, smul_smul, ← add_nsmul, Nat.mod_add_div']

/-! ## The same run on naturals -/

open TorsionCheck (Coords coords fmul)

/-- The map `(x, y) ↦ (β' x, y)` on coordinates. -/
def endoNat (q : Coords) : Coords := (fmul cubeRootNat q.1, q.2.1, q.2.2)

/-- The two products in one run, on coordinates. -/
def jointNat : Nat → Coords → Coords → Coords → Nat → Nat → Coords
  | 0, _, _, _, _, _ => TorsionCheck.zero
  | fuel + 1, p, q, t, a, b =>
    bif Nat.beq a 0 && Nat.beq b 0 then TorsionCheck.zero
    else
      let h := TorsionCheck.double (jointNat fuel p q t (a / 2) (b / 2))
      bif Nat.beq (a % 2) 1 then
        (bif Nat.beq (b % 2) 1 then TorsionCheck.add h t else TorsionCheck.add h p)
      else (bif Nat.beq (b % 2) 1 then TorsionCheck.add h q else h)

/-- The split product, on coordinates. -/
def glvNat (p : Coords) (s : Nat) : Coords :=
  let e := endoNat p
  jointNat 128 p e (TorsionCheck.add p e) (s % eigenvalue) (s / eigenvalue)

private theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.mpr (by simp)

theorem coords_endo (q : G1) : coords (endo q) = endoNat (coords q) := by
  simp only [coords, endo, endoNat, fmul, Prod.mk.injEq, and_true]
  rw [← cubeRoot_val]
  exact Fp.val_mul cubeRoot q.x

theorem coords_jointMul (fuel : Nat) (p q t : G1) (a b : Nat) :
    coords (jointMul fuel p q t a b) =
      jointNat fuel (coords p) (coords q) (coords t) a b := by
  induction fuel generalizing a b with
  | zero => rfl
  | succ fuel ih =>
    rw [jointMul, jointNat]
    simp only [beq_eq, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq]
    by_cases h0 : a = 0 ∧ b = 0
    · simp only [h0, and_self, ↓reduceIte]
      rfl
    simp only [h0, ↓reduceIte]
    split <;> split <;> simp only [TorsionCheck.coords_add, TorsionCheck.coords_double, ih]

theorem coords_glvMul (p : G1) (s : Nat) : coords (glvMul p s) = glvNat (coords p) s := by
  rw [glvMul, glvNat, coords_jointMul, TorsionCheck.coords_add, coords_endo]

end EthLib.Cryptography.Kzg.SetupLagrange

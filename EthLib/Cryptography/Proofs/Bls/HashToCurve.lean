module

public import EthLib.Cryptography.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Bls.SqrtRatio

/-!
# Proofs: the SSWU map of the hash to G2

Source: RFC 9380 §6.6.2, §6.6.3, §8.8.2 and Appendix F.2.

The map of §6.6.2 as written never fails, and each output lies on `E'`.

The straight-line map of the specification, with `x` as a fraction, gives the same point.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-! ## The map of §6.6.2 as written -/

namespace Affine

/-- The simplified SWU map of [RFC 9380 §6.6.2][sswu], as written: affine, with inversions.

It is the reference for the map of the specification, which computes the same point.

[sswu]: https://www.rfc-editor.org/rfc/rfc9380#section-6.6.2
-/
def simpleSwu {F : Type} [BaseField F] (u : Fp2 F) : Except BlsError (Fp2 F × Fp2 F) := do
  let u2 := u * u
  let zu2 := Z * u2
  -- The denominator `Z^2 * u^4 + Z * u^2` of step 1.
  let denom := zu2 * zu2 + zu2
  let x1 :=
    -- Step 1: `tv1 = inv0(Z^2 * u^4 + Z * u^2)`, which is 0 exactly when the denominator is.
    if denom.isZero then
      -- Step 3: if `tv1 = 0`, then `x1 = B' / (Z * A')`.
      --
      -- The denominator is 0 when `Z * u^2` is 0 or -1.
      Bprime / (Z * Aprime)
    else
      -- Step 2: `x1 = (-B' / A') * (1 + tv1)`.
      (-Bprime / Aprime) * (Fp2.one + denom.inverse)
  -- Step 4: `gx1 = x1^3 + A' * x1 + B'`.
  let gx1 : Fp2 F := x1 * x1 * x1 + Aprime * x1 + Bprime
  match Fp2.sqrt gx1 with
  | some y =>
    -- Step 7: `gx1` is a square, so `x = x1` and `y = sqrt(gx1)`.
    --
    -- Step 9: if `sgn0(u) ≠ sgn0(y)`, then `y = -y`.
    return (x1, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y)
  | none =>
    -- Step 5: `x2 = Z * u^2 * x1`, needed only when `gx1` is not a square.
    let x2 := zu2 * x1
    -- Steps 6 and 8: `x = x2` and `y = sqrt(gx2)`, with `gx2 = x2^3 + A' * x2 + B'`.
    match Fp2.sqrt (x2 * x2 * x2 + Aprime * x2 + Bprime : Fp2 F) with
    | none => .error .notASquare
    | some y =>
      -- Step 9: if `sgn0(u) ≠ sgn0(y)`, then `y = -y`.
      return (x2, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y)

end Affine

/-! ## Simplified SWU onto `E' : y^2 = x^3 + A'*x + B'` -/

/-- Right-hand side `g(x) = x^3 + A'*x + B'` of the 3-isogenous curve `E'`. -/
def swuG {F : Type} [BaseField F] (x : Fp2 F) : Fp2 F :=
  x * x * x + Aprime * x + Bprime

/-- First candidate abscissa `x1(u)` in SSWU (`RFC 9380 §6.6.2`). -/
def swuX1 {F : Type} [BaseField F] (u : Fp2 F) : Fp2 F :=
  let u2 := u * u
  let zu2 := Z * u2
  let denom := zu2 * zu2 + zu2
  if denom.isZero then Bprime / (Z * Aprime)
  else (-Bprime / Aprime) * (Fp2.one + denom.inverse)

/-- Second candidate abscissa `x2(u) = Z * u^2 * x1(u)` in SSWU (`RFC 9380 §6.6.2`). -/
def swuX2 {F : Type} [BaseField F] (u : Fp2 F) : Fp2 F :=
  Z * (u * u) * swuX1 u

private theorem aprime_ne_zero : Aprime ≠ (0 : Fp2) := by
  decide_eq_at_model [Aprime]

private theorem swuG_x2_aux (t A B invA invD : Fp2)
    (hd_inv : (t * t + t) * invD = 1) (ha_inv : A * invA = 1) :
    let x1 := (-B * invA) * (1 + invD)
    (t * x1) * (t * x1) * (t * x1) + A * (t * x1) + B =
      t * t * t * (x1 * x1 * x1 + A * x1 + B) := by
  linear_combination
    B * A * invA * (t - 1) * hd_inv
    + B * (t * t * t - 1) * ha_inv

private theorem swuX1_non_zero_denom (u : Fp2)
    (hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false) :
    swuX1 u = (-(Bprime : Fp2) * (Aprime : Fp2).inverse) *
      (Fp2.one + ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse) := by
  unfold swuX1
  dsimp only
  rw [hdenom]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Fundamental SSWU polynomial identity (`RFC 9380 §6.6.2`).

When `Z^2 * u^4 + Z * u^2 ≠ 0`, `g(x2(u)) = (Z * u^2)^3 * g(x1(u))`.
-/
theorem swuG_x2_eq (u : Fp2)
    (hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false) :
    swuG (swuX2 u) =
      (Z * (u * u)) * (Z * (u * u)) * (Z * (u * u)) * swuG (swuX1 u) := by
  have hd_ne : (Z * (u * u)) * (Z * (u * u)) + Z * (u * u) ≠ 0 := fun h0 => by
    rw [Fp2.isZero_iff.mpr h0] at hdenom
    cases hdenom
  have hd_inv : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)) *
      ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse = 1 :=
    Fp2.mul_inverse_cancel hd_ne
  have ha_inv : (Aprime : Fp2) * Aprime.inverse = 1 := Fp2.mul_inverse_cancel aprime_ne_zero
  unfold swuG swuX2
  rewrite [swuX1_non_zero_denom u hdenom, Fp2.one_eq_one]
  -- The constants become variables, so unification never evaluates the inverse of `A'`.
  generalize ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse = invD at hd_inv ⊢
  generalize Z * (u * u) = t at hd_inv ⊢
  generalize (Aprime : Fp2).inverse = invA at ha_inv ⊢
  generalize (Aprime : Fp2) = A at ha_inv ⊢
  generalize (Bprime : Fp2) = B
  exact swuG_x2_aux t A B invA invD hd_inv ha_inv

private theorem sq_ite_neg (P : Prop) [Decidable P] (y : Fp2) :
    (if P then y else -y) * (if P then y else -y) = y * y := by
  by_cases h : P <;> simp [h]

section SwuComplete
open scoped EthLib.Cryptography.Bls.Fp

/-- Because `p = 3 mod 4`, the candidate root squares to `a` or to `-a`. -/
theorem sq_or_neg_sq (a : Fp) :
    let s := Fp.powNat a ((Fp.modulus + 1) / 4)
    s * s = a ∨ s * s = -a := by
  simpa only [Fp.sqrtCandidate_eq_powNat] using Fp.sqrtCandidate_sq_or_neg a

/-- Any `a : Fp2` whose `Fp` norm is a square in `Fp` has a square root returned by `Fp2.sqrt`. -/
theorem sqrt_of_norm_sq {a : Fp2} {sn : Fp} (hsn : sn * sn = Fp2.norm a) :
    ∃ c, Fp2.sqrt a = some c :=
  Fp2.sqrt_isSome_of_norm ⟨_, Fp.baseField_sqrt_complete hsn⟩

private def zaInv : Fp2 :=
  ⟨Fp.ofNat 0x1ab297833e723eac0fabc0aa0e7a110618a36faaa1445aed7798865356042fe7a49c1b4d2a1c369cbb8aeb851eb7fa5,
   Fp.ofNat 0x35652f067ce47d581f5781541cf4220c3146df554288b5daef310ca6ac085fcf4938369a54386d397715d70a3d6ff4a⟩

private theorem za_mul_zaInv : (Z * Aprime) * zaInv = 1 := by
  decide_eq_at_model [Z, Aprime, zaInv]

private theorem za_ne_zero : (Z : Fp2) * Aprime ≠ 0 := by
  decide_eq_at_model [Z, Aprime]

private theorem za_inverse_eq : ((Z : Fp2) * Aprime).inverse = zaInv := by
  have h1 : ((Z : Fp2) * Aprime) * ((Z : Fp2) * Aprime).inverse = 1 :=
    Fp2.mul_inverse_cancel za_ne_zero
  linear_combination zaInv * h1 - ((Z : Fp2) * Aprime).inverse * za_mul_zaInv

private def sqrtNormGx1Zero : Fp :=
  Fp.ofNat 0x14bc2d072749c399567308a4ea62f9640737884f167efe5f0485541babeb2042e44ddf51fdf7a7164c1d372558051161

private theorem sqrtNormGx1Zero_sq :
    sqrtNormGx1Zero * sqrtNormGx1Zero = Fp2.norm (swuG (Bprime * zaInv)) := by
  decide_eq_at_model [sqrtNormGx1Zero, swuG, Aprime, Bprime, zaInv]

private theorem norm_gx2_sq_zmod {nz nu ng sz sg : ZMod Fp.modulus}
    (hsz : sz * sz = -nz) (hsg : sg * sg = -ng) :
    (sz * (nz * (nu * nu * nu)) * sg) * (sz * (nz * (nu * nu * nu)) * sg) =
      ((nz * (nu * nu)) * (nz * (nu * nu)) * (nz * (nu * nu))) * ng := by
  linear_combination
    nz * nz * nu ^ 6 * sg * sg * hsz
    - nz ^ 3 * nu ^ 6 * hsg

/-- For every `u`, at least one of `g(x1(u))` and `g(x2(u))` has a square root in `Fp2`. -/
theorem simpleSwu_sqrt_complete (u : Fp2) :
    (∃ y, Fp2.sqrt (swuG (swuX1 u)) = some y) ∨
    (∃ y, Fp2.sqrt (swuG (swuX2 u)) = some y) := by
  by_cases hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = true
  -- Exceptional denominator `Z^2 * u^4 + Z * u^2 = 0`: `x1 = B' / (Z * A')` has square norm directly.
  · left
    have hx1 : swuX1 u = Bprime * zaInv := by
      unfold swuX1
      dsimp only
      rw [hdenom, ite_eq_left rfl]
      change Bprime * ((Z : Fp2) * Aprime).inverse = Bprime * zaInv
      rw [za_inverse_eq]
    rw [hx1]
    exact sqrt_of_norm_sq sqrtNormGx1Zero_sq
  -- Generic denominator: if `N(g(x1))` is not a square, `-N(g(x1))` and `-N(Z)` are both squares.
  · have hdenom_f : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false :=
      Bool.eq_false_iff.mpr hdenom
    rcases sq_or_neg_sq (Fp2.norm (swuG (swuX1 u))) with hs1 | hs2
    · left
      exact sqrt_of_norm_sq hs1
    · right
      set s1 := Fp.powNat (Fp2.norm (swuG (swuX1 u))) ((Fp.modulus + 1) / 4)
      have hnorm2 : Fp2.norm (swuG (swuX2 u)) =
          ((Fp2.norm Z * (Fp2.norm u * Fp2.norm u)) *
           (Fp2.norm Z * (Fp2.norm u * Fp2.norm u)) *
           (Fp2.norm Z * (Fp2.norm u * Fp2.norm u))) *
          Fp2.norm (swuG (swuX1 u)) := by
        rw [swuG_x2_eq u hdenom_f]
        simp only [Fp2.norm_mul]
      have hw_sq :
          ((sqrtNegNormZ : Fp) * (Fp2.norm Z * (Fp2.norm u * Fp2.norm u * Fp2.norm u)) * s1) *
            ((sqrtNegNormZ : Fp) * (Fp2.norm Z * (Fp2.norm u * Fp2.norm u * Fp2.norm u)) * s1) =
          Fp2.norm (swuG (swuX2 u)) := by
        rw [hnorm2]
        apply Fp.toZMod.injective
        have hsz := congrArg Fp.toZMod sqrtNegNormZ_sq
        have hsg := congrArg Fp.toZMod hs2
        push_toZMod at hsz hsg ⊢
        exact norm_gx2_sq_zmod hsz hsg
      exact sqrt_of_norm_sq hw_sq

-- The next two proofs hold for any base field, where no step can evaluate the square roots.
--
-- Over `Fp` in Montgomery form, the kernel would instead reduce them on the constants.

/-- The SSWU map succeeds on `u` when `g(x1(u))` or `g(x2(u))` has a root, over any base field. -/
private theorem simpleSwu_ok_of_sqrt {F : Type} [BaseField F] (u : Fp2 F)
    (hor : (∃ y, Fp2.sqrt (swuG (swuX1 u)) = some y) ∨
      (∃ y, Fp2.sqrt (swuG (swuX2 u)) = some y)) :
    ∃ p, Affine.simpleSwu u = .ok p := by
  revert hor
  rw [Affine.simpleSwu]
  unfold swuG swuX2 swuX1
  generalize (Fp2.sqrt : Fp2 F → Option (Fp2 F)) = sqrtFn
  rintro (⟨y1, hy1⟩ | ⟨y2, hy2⟩)
  · -- `g(x1)` has a root, so the map returns at its first square root.
    dsimp only at hy1
    rw [hy1]
    exact ⟨_, rfl⟩
  · -- Otherwise `g(x2)` has a root, and the map returns at its second square root.
    dsimp only at hy2
    cases sqrtFn _ with
    | some y1 => exact ⟨_, rfl⟩
    | none =>
      dsimp only
      rw [hy2]
      exact ⟨_, rfl⟩

/-- An output of the SSWU map is a returned root of `g(x)` or its negation, over any base field. -/
private theorem exists_sqrt_of_affine_simpleSwu_eq_ok {F : Type} [BaseField F] {u : Fp2 F}
    {p : Fp2 F × Fp2 F} (h : Affine.simpleSwu u = .ok p) :
    ∃ y, Fp2.sqrt (swuG p.1) = some y ∧ p.2 = if Fp2.sgn0 u = Fp2.sgn0 y then y else -y := by
  revert h
  rw [Affine.simpleSwu]
  unfold swuG
  cases h1 : Fp2.sqrt (F := F) _ with
  | some y1 =>
    rintro ⟨⟩
    exact ⟨y1, h1, rfl⟩
  | none =>
    dsimp only
    cases h2 : Fp2.sqrt (F := F) _ with
    | none => rintro ⟨⟩
    | some y2 =>
      rintro ⟨⟩
      exact ⟨y2, h2, rfl⟩

/-- The SSWU map succeeds on every `u` (RFC 9380 §6.6.2). -/
theorem Affine.simpleSwu_ok (u : Fp2) : ∃ p, Affine.simpleSwu u = .ok p :=
  simpleSwu_ok_of_sqrt u (simpleSwu_sqrt_complete u)

/-- Every output of the SSWU map lies on `E' : y^2 = x^3 + A' * x + B'`. -/
theorem Affine.simpleSwu_curve_eq {u : Fp2} {p : Fp2 × Fp2} (h : Affine.simpleSwu u = .ok p) :
    p.2 * p.2 = swuG p.1 := by
  obtain ⟨y, hy, hp⟩ := exists_sqrt_of_affine_simpleSwu_eq_ok h
  rw [hp, sq_ite_neg]
  exact Fp2.sqrt_mul_self hy

end SwuComplete

/-! ## The straight-line map of the specification (Appendix F.2) -/

-- The next three proofs hold for any base field, where no step can evaluate the constants.

/-- A property of the output of the map follows from it on the named steps, over any base field. -/
private theorem simpleSwu_cases {F : Type} [BaseField F] (u : Fp2 F)
    (P : Fp2 F × Fp2 F × Fp2 F → Prop)
    (h : ∀ tv1 tv2 tv3 tv4 gx1 tv6 : Fp2 F,
      tv1 = Z * FieldOps.square u → tv2 = FieldOps.square tv1 + tv1 →
      tv3 = Bprime * (tv2 + Fp2.one) → tv4 = Aprime * (if tv2.isZero then Z else -tv2) →
      gx1 = (FieldOps.square tv3 + Aprime * FieldOps.square tv4) * tv3 +
        Bprime * (FieldOps.square tv4 * tv4) →
      tv6 = FieldOps.square tv4 * tv4 →
      P (if (sqrtRatio gx1 tv6).1 then tv3 else tv1 * tv3, tv4,
        if Fp2.sgn0 u = Fp2.sgn0 (if (sqrtRatio gx1 tv6).1 then (sqrtRatio gx1 tv6).2
            else tv1 * u * (sqrtRatio gx1 tv6).2)
        then (if (sqrtRatio gx1 tv6).1 then (sqrtRatio gx1 tv6).2
            else tv1 * u * (sqrtRatio gx1 tv6).2)
        else -(if (sqrtRatio gx1 tv6).1 then (sqrtRatio gx1 tv6).2
            else tv1 * u * (sqrtRatio gx1 tv6).2))) :
    P (simpleSwu u) :=
  h _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

/-- When `g(x1)` has a root, the map of §6.6.2 returns `x1` and that root, up to sign. -/
private theorem affine_of_sqrt_x1 {F : Type} [BaseField F] (u y : Fp2 F)
    (h : Fp2.sqrt (swuG (swuX1 u)) = some y) :
    Affine.simpleSwu u = .ok (swuX1 u, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y) := by
  unfold swuG swuX1 at h
  rw [Affine.simpleSwu]
  dsimp only at h ⊢
  rw [h]
  rfl

/-- When only `g(x2)` has a root, the map of §6.6.2 returns `x2` and that root, up to sign. -/
private theorem affine_of_sqrt_x2 {F : Type} [BaseField F] (u y : Fp2 F)
    (h1 : Fp2.sqrt (swuG (swuX1 u)) = none) (h : Fp2.sqrt (swuG (swuX2 u)) = some y) :
    Affine.simpleSwu u = .ok (swuX2 u, if Fp2.sgn0 u = Fp2.sgn0 y then y else -y) := by
  unfold swuG swuX1 at h1
  unfold swuG swuX2 swuX1 at h
  rw [Affine.simpleSwu]
  dsimp only at h1 h ⊢
  rw [h1]
  dsimp only
  rw [h]
  rfl

/-- Negating a nonzero element of `Fp` flips its parity, since `p` is odd. -/
private theorem fp_sgn0_neg {a : Fp} (h : a ≠ 0) : BaseField.sgn0 (-a) = !BaseField.sgn0 a := by
  have h0 : 0 < a.val := Nat.pos_of_ne_zero (fun hh => h (Fp.ext (hh.trans Fp.val_zero.symm)))
  have hlt := Fp.val_lt a
  have hv : (-a).val = Fp.modulus - a.val := by rw [Fp.val_neg, Nat.mod_eq_of_lt (by omega)]
  have hodd : Fp.modulus % 2 = 1 := by decide
  simp only [Fp.baseField_sgn0, hv]
  rcases Nat.mod_two_eq_zero_or_one a.val with h2 | h2
  · have h3 : (Fp.modulus - a.val) % 2 = 1 := by omega
    simp [h2, h3]
  · have h3 : (Fp.modulus - a.val) % 2 = 0 := by omega
    simp [h2, h3]

/-- Negating a nonzero element of `Fp2` flips its sign `sgn0`. -/
private theorem fp2_sgn0_neg {y : Fp2} (hy : y ≠ 0) : Fp2.sgn0 (-y) = !Fp2.sgn0 y := by
  simp only [Fp2.sgn0, Fp2.neg_c0, Fp2.neg_c1, Fp.baseField_isZero]
  by_cases hc0 : y.c0 = 0
  -- When `y0 = 0`, the sign is that of `y1`, which is not 0.
  · have hc1 : y.c1 ≠ 0 := fun hc1 => hy (Fp2.ext hc0 hc1)
    have hs0 : BaseField.sgn0 (0 : Fp) = false := by simp [Fp.baseField_sgn0]
    simp only [hc0, neg_zero, hs0, Fp.isZero_iff.mpr rfl, fp_sgn0_neg hc1]
    simp
  -- Otherwise the sign is that of `y0`.
  · have hn : (-y.c0).isZero = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hc0 (neg_eq_zero.mp (Fp.isZero_iff.mp h))
    have hp : y.c0.isZero = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hc0 (Fp.isZero_iff.mp h)
    simp only [hn, hp, fp_sgn0_neg hc0]
    simp

/-- Two roots of the same square give the same root once their sign is set by `sgn0(u)`. -/
private theorem sgn0_select_eq {u y y' : Fp2} (h : y * y = y' * y') :
    (if Fp2.sgn0 u = Fp2.sgn0 y then y else -y) =
      (if Fp2.sgn0 u = Fp2.sgn0 y' then y' else -y') := by
  have hf : (y - y') * (y + y') = 0 := by linear_combination h
  rcases mul_eq_zero.mp hf with h1 | h1
  · rw [sub_eq_zero.mp h1]
  · have hy : y = -y' := eq_neg_of_add_eq_zero_left h1
    subst hy
    by_cases h0 : y' = 0
    · subst h0
      simp
    · rw [fp2_sgn0_neg h0]
      cases Fp2.sgn0 u <;> cases Fp2.sgn0 y' <;> simp

private theorem swuZ_ne_zero : Z ≠ (0 : Fp2) := by
  decide_eq_at_model [Z]

private theorem x1_aux_zero (A B Zc : Fp2) : B / (Zc * A) = B * (0 + 1) / (A * Zc) := by
  rw [zero_add, mul_one, mul_comm Zc A]

private theorem x1_aux (A B t : Fp2) (hA : A ≠ 0) (ht : t ≠ 0) :
    (-B * A⁻¹) * (1 + t⁻¹) = B * (t + 1) / (A * -t) := by
  field_simp

private theorem gx1_aux (A B t3 t4 : Fp2) (h4 : t4 ≠ 0) :
    ((t3 * t3 + A * (t4 * t4)) * t3 + B * (t4 * t4 * t4)) / (t4 * t4 * t4) =
      (t3 / t4) * (t3 / t4) * (t3 / t4) + A * (t3 / t4) + B := by
  field_simp

private theorem y2_aux (Zc u t g y1 : Fp2) (h1 : t = Zc * (u * u)) (hy : y1 * y1 = Zc * g) :
    (t * u * y1) * (t * u * y1) = t * t * t * g := by
  subst h1
  linear_combination (Zc * Zc * (u * u) * (u * u) * (u * u)) * hy

private theorem square_eq_mul (a : Fp2) : FieldOps.square a = a * a := by
  rw [Cryptography.Fp2.fieldOps_square, Cryptography.Fp2.square_eq Fp.embedding]

/-- The denominator `tv4 = A' * (tv2 = 0 ? Z : -tv2)` is not 0. -/
private theorem tv4_ne_zero {tv2 tv4 : Fp2}
    (h4 : tv4 = Aprime * (if tv2.isZero then Z else -tv2)) : tv4 ≠ 0 := by
  subst h4
  by_cases hz : tv2.isZero = true
  · simp only [hz, ↓reduceIte]
    exact mul_ne_zero aprime_ne_zero swuZ_ne_zero
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    exact mul_ne_zero aprime_ne_zero (neg_ne_zero.mpr fun h => hz (Fp2.isZero_iff.mpr h))

/-- The first candidate abscissa is `x1 = tv3 / tv4`, in both branches. -/
private theorem swuX1_eq_parts {u tv1 tv2 tv3 tv4 : Fp2}
    (h1 : tv1 = Z * (u * u)) (h2 : tv2 = tv1 * tv1 + tv1) (h3 : tv3 = Bprime * (tv2 + 1))
    (h4 : tv4 = Aprime * (if tv2.isZero then Z else -tv2)) :
    swuX1 u = tv3 / tv4 := by
  unfold swuX1
  dsimp only
  rw [← h1, ← h2]
  subst h3 h4
  by_cases hz : tv2.isZero = true
  · simp only [hz, ↓reduceIte]
    rw [Fp2.isZero_iff.mp hz]
    exact x1_aux_zero _ _ _
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    rw [Fp2.div_eq_mul_inverse, Fp2.one_eq_one, ← Fp2.inv_eq_inverse, ← Fp2.inv_eq_inverse]
    exact x1_aux _ _ _ aprime_ne_zero fun h => hz (Fp2.isZero_iff.mpr h)

/-- On the exceptional denominator `tv2 = 0`, `g(x1)` has a square root. -/
private theorem sqrt_gx1_of_tv2_zero {u tv1 tv2 : Fp2}
    (h1 : tv1 = Z * (u * u)) (h2 : tv2 = tv1 * tv1 + tv1) (hz : tv2 = 0) :
    ∃ y, Fp2.sqrt (swuG (swuX1 u)) = some y := by
  have hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = true := by
    rw [← h1, ← h2, hz]
    exact Fp2.isZero_iff.mpr rfl
  have hx1 : swuX1 u = Bprime * zaInv := by
    unfold swuX1
    dsimp only
    rw [hdenom, ite_eq_left rfl]
    change Bprime * ((Z : Fp2) * Aprime).inverse = Bprime * zaInv
    rw [za_inverse_eq]
  rw [hx1]
  exact sqrt_of_norm_sq sqrtNormGx1Zero_sq

/-- The map of §6.6.2 returns the point of the named steps of Appendix F.2. -/
private theorem affine_eq_parts {u tv1 tv2 tv3 tv4 gx1 tv6 : Fp2}
    (h1 : tv1 = Z * (u * u)) (h2 : tv2 = tv1 * tv1 + tv1) (h3 : tv3 = Bprime * (tv2 + 1))
    (h4 : tv4 = Aprime * (if tv2.isZero then Z else -tv2))
    (hg : gx1 = (tv3 * tv3 + Aprime * (tv4 * tv4)) * tv3 + Bprime * (tv4 * tv4 * tv4))
    (h6 : tv6 = tv4 * tv4 * tv4) :
    Affine.simpleSwu u =
      .ok ((if (sqrtRatio gx1 tv6).1 then tv3 else tv1 * tv3) / tv4,
        if Fp2.sgn0 u = Fp2.sgn0 (if (sqrtRatio gx1 tv6).1 then (sqrtRatio gx1 tv6).2
            else tv1 * u * (sqrtRatio gx1 tv6).2)
        then (if (sqrtRatio gx1 tv6).1 then (sqrtRatio gx1 tv6).2
            else tv1 * u * (sqrtRatio gx1 tv6).2)
        else -(if (sqrtRatio gx1 tv6).1 then (sqrtRatio gx1 tv6).2
            else tv1 * u * (sqrtRatio gx1 tv6).2)) := by
  have h4ne : tv4 ≠ 0 := tv4_ne_zero h4
  have hx1 : swuX1 u = tv3 / tv4 := swuX1_eq_parts h1 h2 h3 h4
  have h6ne : tv6 ≠ 0 := by
    rw [h6]
    exact mul_ne_zero (mul_ne_zero h4ne h4ne) h4ne
  -- `gx1 / tv4^3 = g(x1)`, so the flag of the square root says whether `g(x1)` is a square.
  have hgx : gx1 / tv6 = swuG (swuX1 u) := by
    rw [hg, h6, hx1]
    unfold swuG
    exact gx1_aux _ _ _ _ h4ne
  have hfst := sqrtRatio_fst (u := gx1) h6ne
  have hsnd := sqrtRatio_snd (u := gx1) h6ne
  rw [hgx] at hfst hsnd
  generalize (sqrtRatio gx1 tv6).1 = b at hfst hsnd ⊢
  generalize (sqrtRatio gx1 tv6).2 = y1 at hfst hsnd ⊢
  cases b with
  | true =>
    -- `g(x1)` is a square: both maps take `x1` and a root of `g(x1)`.
    simp only [↓reduceIte] at hsnd ⊢
    obtain ⟨y0, hy0⟩ := Fp2.sqrt_complete hsnd
    have hyy : y1 * y1 = y0 * y0 := hsnd.trans (Fp2.sqrt_mul_self hy0).symm
    rw [affine_of_sqrt_x1 u y0 hy0, hx1, sgn0_select_eq hyy]
  | false =>
    -- Otherwise `tv2 ≠ 0`, and `tv1 u y1` is a root of `g(x2) = tv1^3 g(x1)`.
    simp only [Bool.false_eq_true, ↓reduceIte] at hsnd ⊢
    have hnone : Fp2.sqrt (swuG (swuX1 u)) = none :=
      Fp2.sqrt_eq_none_iff.mpr fun y hy => Bool.false_ne_true (hfst.mpr ⟨y, hy⟩)
    have hz : tv2.isZero = false := by
      rw [Bool.eq_false_iff]
      intro hz
      obtain ⟨y, hy⟩ := sqrt_gx1_of_tv2_zero h1 h2 (Fp2.isZero_iff.mp hz)
      rw [hnone] at hy
      cases hy
    have hdenom : ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).isZero = false := by
      rw [← h1, ← h2]
      exact hz
    have hg2 := swuG_x2_eq u hdenom
    rw [← h1] at hg2
    have hy2 : (tv1 * u * y1) * (tv1 * u * y1) = swuG (swuX2 u) := by
      rw [hg2]
      exact y2_aux _ _ _ _ _ h1 hsnd
    obtain ⟨y0, hy0⟩ := Fp2.sqrt_complete hy2
    have hx2 : swuX2 u = tv1 * tv3 / tv4 := by
      unfold swuX2
      rw [← h1, hx1, mul_div_assoc]
    rw [affine_of_sqrt_x2 u y0 hnone hy0, hx2,
      sgn0_select_eq ((Fp2.sqrt_mul_self hy0).trans hy2.symm)]

/-- The denominator `xd` of the SSWU map is never 0. -/
theorem simpleSwu_xd_ne_zero (u : Fp2) : (simpleSwu u).2.1 ≠ 0 := by
  refine simpleSwu_cases u (fun p => p.2.1 ≠ 0) ?_
  intro tv1 tv2 tv3 tv4 gx1 tv6 h1 h2 h3 h4 hg h6
  exact tv4_ne_zero h4

/-- The SSWU map gives the point of the map of §6.6.2 as written, with `x = xn / xd`. -/
theorem simpleSwu_eq_affine (u : Fp2) :
    Affine.simpleSwu u = .ok ((simpleSwu u).1 / (simpleSwu u).2.1, (simpleSwu u).2.2) := by
  refine simpleSwu_cases u (fun p => Affine.simpleSwu u = .ok (p.1 / p.2.1, p.2.2)) ?_
  intro tv1 tv2 tv3 tv4 gx1 tv6 h1 h2 h3 h4 hg h6
  simp only [square_eq_mul, Fp2.one_eq_one] at h1 h2 h3 hg h6
  dsimp only
  exact affine_eq_parts h1 h2 h3 h4 hg h6

-- Stated on a variable triple, so that no step unfolds the map.
private theorem curve_eq_of_affine {u : Fp2} {p : Fp2 × Fp2 × Fp2}
    (h : Affine.simpleSwu u = .ok (p.1 / p.2.1, p.2.2)) : p.2.2 * p.2.2 = swuG (p.1 / p.2.1) := by
  -- The pair is reduced first: unification would instead unfold the field arithmetic.
  have h2 := Affine.simpleSwu_curve_eq h
  dsimp only at h2
  exact h2

/-- Every output `(xn, xd, y)` of the SSWU map is the point `(xn / xd, y)` of `E'`. -/
theorem simpleSwu_curve_eq (u : Fp2) :
    (simpleSwu u).2.2 * (simpleSwu u).2.2 = swuG ((simpleSwu u).1 / (simpleSwu u).2.1) :=
  curve_eq_of_affine (simpleSwu_eq_affine u)

end EthLib.Cryptography.Bls.HashToCurve

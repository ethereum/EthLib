module

public import EthLib.Cryptography.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Bls.Fp2

/-!
# Proofs: the SSWU map of the hash to G2 never fails

Source: RFC 9380 §6.6.2, §6.6.3 and §8.8.2.

`Z` is not a square, so `g(x1)` or `g(x2)` is a square, and the map finds a square root.

Each output `(x, y)` of the map lies on `E' : y^2 = x^3 + A' * x + B'`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.HashToCurve

open EthLib.Cryptography.Bls

/-! ## Simplified SWU onto `E' : y^2 = x^3 + A'*x + B'` -/

/-- Right-hand side `g(x) = x^3 + A'*x + B'` of the 3-isogenous curve `E'`. -/
def swuG (x : Fp2) : Fp2 :=
  x * x * x + Aprime * x + Bprime

/-- First candidate abscissa `x1(u)` in SSWU (`RFC 9380 §6.6.2`). -/
def swuX1 (u : Fp2) : Fp2 :=
  let u2 := u * u
  let zu2 := Z * u2
  let denom := zu2 * zu2 + zu2
  if denom.isZero then
    @HDiv.hDiv Fp2 Fp2 Fp2 (@instHDiv Fp2 Fp2.instDiv) Bprime (Z * Aprime)
  else
    @HDiv.hDiv Fp2 Fp2 Fp2 (@instHDiv Fp2 Fp2.instDiv) (-Bprime) Aprime * (Fp2.one + denom.inverse)

/-- Second candidate abscissa `x2(u) = Z * u^2 * x1(u)` in SSWU (`RFC 9380 §6.6.2`). -/
def swuX2 (u : Fp2) : Fp2 :=
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

When `Z^2 * u^4 + Z * u^2 != 0`, `g(x2(u)) = (Z * u^2)^3 * g(x1(u))`.
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
  simpa only [Fp.sqrtCandidate, Fp.powLimbs_sqrtExponent] using Fp.sqrtCandidate_sq_or_neg a

private theorem try_sub_sq_zmod {a0 a1 s twoInv r rInv : ZMod Fp.modulus}
    (hs : s * s = a0 * a0 + a1 * a1)
    (hr : r * r = -((a0 + s) * twoInv))
    (hrInv : r * rInv = 1) :
    (a1 * twoInv * rInv) * (a1 * twoInv * rInv) = (a0 - s) * twoInv := by
  linear_combination
    -rInv * rInv * ((a0 - s) * twoInv) * hr
    - rInv * rInv * twoInv * twoInv * hs
    + ((a0 - s) * twoInv) * (r * rInv + 1) * hrInv

private theorem r_ne_zero_of_neg_try1 {a0 a1 s twoInv r : ZMod Fp.modulus}
    (ha1 : a1 ≠ 0) (h2inv : (2 : ZMod Fp.modulus) * twoInv = 1)
    (hs : s * s = a0 * a0 + a1 * a1)
    (hr : r * r = -((a0 + s) * twoInv)) : r ≠ 0 := by
  intro hr0
  have h2ne : twoInv ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h2inv; exact zero_ne_one h2inv
  have hprod : (a1 * twoInv) * (a1 * twoInv) = 0 := by
    linear_combination -((a0 - s) * twoInv) * hr - twoInv * twoInv * hs
      + r * ((a0 - s) * twoInv) * hr0
  exact mul_ne_zero ha1 h2ne (mul_self_eq_zero.mp hprod)

/-- Any `a : Fp2` whose `Fp` norm is a square in `Fp` has a square root returned by `Fp2.sqrt`. -/
theorem sqrt_of_norm_sq {a : Fp2} {sn : Fp} (hsn : sn * sn = Fp2.norm a) :
    ∃ c, Fp2.sqrt a = .ok c := by
  apply (Fp2.sqrt_isOk_iff_reference a).2
  have hsqrt : ∀ {x b : Fp}, b * b = x →
      sqrtOrError x = .ok (Fp.powNat x ((Fp.modulus + 1) / 4)) :=
    fun hb => (Fp.sqrtOrError_eq _).trans (Fp.sqrt_complete hb)
  cases hz : BaseField.isZero a.c1
  · have ha1 : Fp.toZMod a.c1 ≠ 0 := fun h0 => by
      have h' : BaseField.isZero a.c1 = true := G1.isZero_iff.mpr h0
      rw [hz] at h'
      cases h'
    have hsqrt_n := hsqrt hsn
    refine Fp2.sqrtReference_isOk_of_c1_ne hz hsqrt_n ?_
    -- The inverse of 2 becomes a variable, so the kernel never evaluates it.
    generalize htwo : BaseField.inverse (BaseField.ofNat 2 : Fp) = twoInv
    -- The prime `p` does not divide 2, since `p > 2`.
    have h2ne : (2 : ZMod Fp.modulus) ≠ 0 := fun h =>
      absurd (Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 _).mp (by exact_mod_cast h)))
        (by simp [Fp.modulus])
    have h2inv : (2 : ZMod Fp.modulus) * Fp.toZMod twoInv = 1 := by
      subst htwo
      rw [Fp.baseField_inverse, Fp.baseField_ofNat, Fp.toZMod_inverse, Fp.toZMod_ofNat,
        Nat.cast_ofNat]
      exact mul_inv_cancel₀ h2ne
    set s := Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)
    have hs : s * s = a.c0 * a.c0 + a.c1 * a.c1 := Fp.sqrt_ok (Fp.sqrt_complete hsn)
    have hsZ := congrArg Fp.toZMod hs
    push_toZMod at hsZ
    rcases sq_or_neg_sq ((a.c0 + s) * twoInv) with htry1 | hneg1
    · exact Or.inl ⟨_, hsqrt htry1⟩
    · set r := Fp.powNat ((a.c0 + s) * twoInv) ((Fp.modulus + 1) / 4)
      have hrZ := congrArg Fp.toZMod hneg1
      push_toZMod at hrZ
      have hr_ne : Fp.toZMod r ≠ 0 := r_ne_zero_of_neg_try1 ha1 h2inv hsZ hrZ
      have hrInv : Fp.toZMod r * Fp.toZMod r.inverse = 1 := by
        rw [Fp.toZMod_inverse]
        exact mul_inv_cancel₀ hr_ne
      refine Or.inr ⟨_, hsqrt (b := a.c1 * twoInv * r.inverse) ?_⟩
      apply Fp.toZMod.injective
      push_toZMod
      exact try_sub_sq_zmod hsZ hrZ hrInv
  · refine Fp2.sqrtReference_isOk_of_c1_zero hz ?_
    rcases sq_or_neg_sq a.c0 with hs1 | hs2
    · exact Or.inl ⟨_, hsqrt hs1⟩
    · exact Or.inr ⟨_, hsqrt hs2⟩

private def sqrtNegNormZ : Fp :=
  Fp.ofNat 0x186417302d5a65347a88b0f999ab2b504614aa5e2eebdeb1a014c40bceb7d2306c12a6d436befcf94d39c9db7b263cd4

private theorem sqrtNegNormZ_sq : sqrtNegNormZ * sqrtNegNormZ = -Fp2.norm Z := by
  decide_eq_at_model [sqrtNegNormZ, Z]

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
    (∃ y, Fp2.sqrt (swuG (swuX1 u)) = .ok y) ∨
    (∃ y, Fp2.sqrt (swuG (swuX2 u)) = .ok y) := by
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
          (sqrtNegNormZ * (Fp2.norm Z * (Fp2.norm u * Fp2.norm u * Fp2.norm u)) * s1) *
            (sqrtNegNormZ * (Fp2.norm Z * (Fp2.norm u * Fp2.norm u * Fp2.norm u)) * s1) =
          Fp2.norm (swuG (swuX2 u)) := by
        rw [hnorm2]
        apply Fp.toZMod.injective
        have hsz := congrArg Fp.toZMod sqrtNegNormZ_sq
        have hsg := congrArg Fp.toZMod hs2
        push_toZMod at hsz hsg ⊢
        exact norm_gx2_sq_zmod hsz hsg
      exact sqrt_of_norm_sq hw_sq

-- The matcher of the map is named on purpose: its equations select a branch without evaluation.
set_option linter.auxLemma false in
/-- The SSWU map succeeds on every `u` (RFC 9380 §6.6.2). -/
theorem simpleSwu_ok (u : Fp2) : ∃ p, simpleSwu u = .ok p := by
  have hor := simpleSwu_sqrt_complete u
  revert hor
  -- `unfold` and `delta` make the kernel time out here when `Fp` is in Montgomery form.
  rw [simpleSwu]
  unfold swuG swuX2 swuX1
  generalize (Fp2.sqrt : Fp2 → Except BlsError Fp2) = sqrtFn
  rintro (⟨y1, hy1⟩ | ⟨y2, hy2⟩)
  · dsimp only at hy1
    rw [hy1]
    exact ⟨_, rfl⟩
  · dsimp only at hy2
    cases sqrtFn _ with
    | ok y1 => exact ⟨_, rfl⟩
    | error _ =>
      simp (config := { zeta := false, iota := false, beta := false }) only
        [simpleSwu.match_1.eq_2]
      extract_lets x2
      rw [show sqrtFn (x2 * x2 * x2 + Aprime * x2 + Bprime) = .ok y2 from hy2]
      exact ⟨_, rfl⟩

-- The matcher of the map is named on purpose: its equations select a branch without evaluation.
set_option linter.auxLemma false in
/-- Every output of the SSWU map lies on `E' : y^2 = x^3 + A' * x + B'`. -/
theorem simpleSwu_curve_eq {u : Fp2} {p : Fp2 × Fp2} (h : simpleSwu u = .ok p) :
    p.2 * p.2 = swuG p.1 := by
  have hsqrt : ∀ {a c : Fp2}, Fp2.sqrt a = .ok c → c * c = a := fun hs => Fp2.sqrt_ok hs
  revert h
  -- `unfold` and `delta` make the kernel time out here when `Fp` is in Montgomery form.
  rw [simpleSwu]
  unfold swuG
  generalize (Fp2.sqrt : Fp2 → Except BlsError Fp2) = sqrtFn at hsqrt ⊢
  cases h1 : sqrtFn _ with
  | ok y1 =>
    simp (config := { zeta := false, iota := false, beta := false }) only
      [simpleSwu.match_1.eq_1]
    rintro ⟨⟩
    dsimp only
    rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y1) y1]
    exact hsqrt h1
  | error _ =>
    simp (config := { zeta := false, iota := false, beta := false }) only
      [simpleSwu.match_1.eq_2]
    extract_lets x2
    cases h2 : sqrtFn (x2 * x2 * x2 + Aprime * x2 + Bprime) with
    | error _ => rintro ⟨⟩
    | ok y2 =>
      rintro ⟨⟩
      dsimp only
      rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y2) y2]
      exact hsqrt h2

end SwuComplete

end EthLib.Cryptography.Bls.HashToCurve

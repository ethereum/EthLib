module

public import EthLib.Cryptography.Bls.HashToCurve
public import EthLib.Cryptography.Proofs.Bls.Fp2

/-!
# Proofs: Simplified SWU map onto the 3-isogenous curve

Source: `RFC 9380 §6.6.2, §6.6.3 and §8.8.2`.

`simpleSwu` maps every `u : Fp2` onto the 3-isogenous curve `E' : y^2 = x^3 + A'*x + B'`.

`swuG_x2_eq` proves the algebraic SSWU relation `g(x2(u)) = (Z * u^2)^3 * g(x1(u))` when `Z^2 * u^4 + Z * u^2 != 0`.

Because `p = 3 mod 4`, an element `a : Fp2` is a square whenever its `Fp` norm `N(a)` is a square in `Fp`.

`N(Z) = 5` is a quadratic non-residue in `Fp`, with `-N(Z)` a square.

Therefore at least one of `N(g(x1(u)))` or `N(g(x2(u)))` is a square in `Fp`.

At the exceptional denominator `Z^2 * u^4 + Z * u^2 = 0`, `g(B' / (Z * A'))` has a square norm in `Fp` directly.

Hence `Fp2.sqrt` succeeds on `gx1` or `gx2` for every `u : Fp2`.

The fallback `panic!` branch in `simpleSwu` is unreachable, and `(simpleSwu u).2^2 = swuG (simpleSwu u).1` holds unconditionally.
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
  intro h
  have := congrArg Fp2.c1 h
  revert this; decide

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
    swuX1 u = (-Bprime * Aprime.inverse) * (Fp2.one + ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse) := by
  unfold swuX1
  dsimp only
  rw [hdenom]
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
  have ha_inv : Aprime * Aprime.inverse = 1 := Fp2.mul_inverse_cancel aprime_ne_zero
  unfold swuG swuX2
  rw [swuX1_non_zero_denom u hdenom, Fp2.one_eq_one]
  exact swuG_x2_aux (Z * (u * u)) Aprime Bprime Aprime.inverse
    ((Z * (u * u)) * (Z * (u * u)) + Z * (u * u)).inverse hd_inv ha_inv

private theorem sq_ite_neg (P : Prop) [Decidable P] (y : Fp2) :
    (if P then y else -y) * (if P then y else -y) = y * y := by
  by_cases h : P <;> simp [h]

section SwuComplete
open scoped EthLib.Cryptography.Bls.Fp

private theorem sq_pm_zmod {s n : ZMod Fp.modulus} (h : s * s = n * n) :
    s = n ∨ s = -n := by
  have hfac : (s - n) * (s + n) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

/-- Because `p = 3 mod 4`, `(x^((p + 1) / 4))^2` equals either `x` or `-x` in `Fp`. -/
private theorem sq_or_neg_sq_zmod (x : ZMod Fp.modulus) :
    let s := x ^ ((Fp.modulus + 1) / 4)
    s * s = x ∨ s * s = -x := by
  intro s
  by_cases hx : x = 0
  · left
    subst hx
    simp [s, zero_pow (by decide : (Fp.modulus + 1) / 4 ≠ 0)]
  · apply sq_pm_zmod
    change (x ^ ((Fp.modulus + 1) / 4) * x ^ ((Fp.modulus + 1) / 4)) *
      (x ^ ((Fp.modulus + 1) / 4) * x ^ ((Fp.modulus + 1) / 4)) = x * x
    rw [← pow_add, ← pow_add,
        show ((Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4) +
             ((Fp.modulus + 1) / 4 + (Fp.modulus + 1) / 4)
          = (Fp.modulus - 1) + 2 by decide,
        pow_add, ZMod.pow_card_sub_one_eq_one hx, one_mul, pow_two]

private theorem sq_or_neg_sq (a : Fp) :
    let s := Fp.powNat a ((Fp.modulus + 1) / 4)
    (s : ZMod Fp.modulus) * s = a ∨ (s : ZMod Fp.modulus) * s = (-a : Fp) := by
  dsimp only
  erw [Fp.powNat_eq_zmod_pow (a : ZMod Fp.modulus) ((Fp.modulus + 1) / 4)]
  exact sq_or_neg_sq_zmod (a : ZMod Fp.modulus)

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

-- Uses `Fp2.sqrt`'s generated matchers so `Fp2.sqrt` is definitionally `sqrtWith Fp.inverse (Fp.ofNat 2).inverse`.
set_option linter.auxLemma false in
private def sqrtWith (invFn : Fp → Fp) (twoInvVal : Fp) (a : Fp2) : Except BlsError Fp2 :=
  if a.c1.isZero = true then
    Fp2.sqrt.match_1 (fun _ => Except BlsError Fp2) a.c0.sqrt (fun s => Except.ok { c0 := s, c1 := Fp.zero }) fun _ =>
      Fp2.sqrt.match_1 (fun _ => Except BlsError Fp2) (-a.c0).sqrt (fun s => Except.ok { c0 := Fp.zero, c1 := s }) fun _ =>
        Except.error BlsError.notASquare
  else
    have n := a.c0 * a.c0 + a.c1 * a.c1
    Fp2.sqrt.match_3 (fun _ => Except BlsError Fp2) n.sqrt (fun _ => Except.error BlsError.notASquare) fun s =>
      have twoInv := twoInvVal
      have try1 := ((a.c0 + s) * twoInv).sqrt
      have c0Opt :=
        Fp2.sqrt.match_1 (fun _ => Except BlsError Fp) try1 (fun _ => try1) fun _ => ((a.c0 - s) * twoInv).sqrt
      Fp2.sqrt.match_3 (fun _ => Except BlsError Fp2) c0Opt (fun _ => Except.error BlsError.notASquare) fun c0Fp =>
        have c1Fp := a.c1 * invFn (Fp.ofNat 2 * c0Fp)
        Except.ok { c0 := c0Fp, c1 := c1Fp }

set_option linter.auxLemma false in
private theorem sqrtWith_of_norm_sq {invFn : Fp → Fp} {twoInv : Fp}
    (h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * (twoInv : ZMod Fp.modulus) = 1)
    {a : Fp2} {sn : Fp}
    (hsn : (sn : ZMod Fp.modulus) * sn = a.c0 * a.c0 + a.c1 * a.c1) :
    ∃ c, sqrtWith invFn twoInv a = .ok c := by
  unfold sqrtWith
  split
  · rcases sq_or_neg_sq a.c0 with hs1 | hs2
    · rw [Fp.sqrt_complete hs1]; exact ⟨_, rfl⟩
    · cases h1 : a.c0.sqrt with
      | ok s => exact ⟨_, rfl⟩
      | error _ => rw [Fp.sqrt_complete hs2]; exact ⟨_, rfl⟩
  · rename_i hc1nz
    have ha1 : (a.c1 : ZMod Fp.modulus) ≠ 0 := fun h0 => hc1nz (G1.isZero_iff.mpr h0)
    dsimp only
    have hsqrt_n := Fp.sqrt_complete hsn
    rw [hsqrt_n]
    dsimp only
    set s := Fp.powNat (a.c0 * a.c0 + a.c1 * a.c1) ((Fp.modulus + 1) / 4)
    have hs : (s : ZMod Fp.modulus) * s = a.c0 * a.c0 + a.c1 * a.c1 := Fp.sqrt_ok hsqrt_n
    rcases sq_or_neg_sq ((a.c0 + s) * twoInv) with htry1 | hneg1
    · rw [Fp.sqrt_complete htry1]; exact ⟨_, rfl⟩
    · cases h1 : ((a.c0 + s) * twoInv).sqrt with
      | ok s1 => exact ⟨_, rfl⟩
      | error _ =>
        dsimp only [Fp2.sqrt.match_1]
        set r := Fp.powNat ((a.c0 + s) * twoInv) ((Fp.modulus + 1) / 4)
        have hr_ne : (r : ZMod Fp.modulus) ≠ 0 :=
          r_ne_zero_of_neg_try1 ha1 h2inv hs hneg1
        have hrInv : (r : ZMod Fp.modulus) * (r.inverse : ZMod Fp.modulus) = 1 := by
          rw [Fp.inverse_eq_inv]
          exact mul_inv_cancel₀ hr_ne
        have htry2 : ((a.c1 * twoInv * r.inverse : Fp) : ZMod Fp.modulus) *
            (a.c1 * twoInv * r.inverse : Fp) = (a.c0 - s) * twoInv :=
          try_sub_sq_zmod hs hneg1 hrInv
        rw [Fp.sqrt_complete htry2]
        exact ⟨_, rfl⟩

/-- Any `a : Fp2` whose `Fp` norm is a square in `Fp` has a square root returned by `Fp2.sqrt`. -/
theorem sqrt_of_norm_sq {a : Fp2} {sn : Fp}
    (hsn : (sn : ZMod Fp.modulus) * sn = Fp2.norm a) :
    ∃ c, Fp2.sqrt a = .ok c := by
  have h2inv : (Fp.ofNat 2 : ZMod Fp.modulus) * ((Fp.ofNat 2).inverse : ZMod Fp.modulus) = 1 := by
    rw [Fp.inverse_eq_inv]
    exact mul_inv_cancel₀ (by decide)
  exact sqrtWith_of_norm_sq h2inv hsn

private def sqrtNegNormZ : Fp :=
  Fp.ofNat 0x186417302d5a65347a88b0f999ab2b504614aa5e2eebdeb1a014c40bceb7d2306c12a6d436befcf94d39c9db7b263cd4

private theorem sqrtNegNormZ_sq :
    (sqrtNegNormZ : ZMod Fp.modulus) * sqrtNegNormZ = (-Fp2.norm Z : Fp) := by
  decide

private def zaInv : Fp2 :=
  ⟨Fp.ofNat 0x1ab297833e723eac0fabc0aa0e7a110618a36faaa1445aed7798865356042fe7a49c1b4d2a1c369cbb8aeb851eb7fa5,
   Fp.ofNat 0x35652f067ce47d581f5781541cf4220c3146df554288b5daef310ca6ac085fcf4938369a54386d397715d70a3d6ff4a⟩

private theorem za_mul_zaInv : (Z * Aprime) * zaInv = 1 := by
  decide

private theorem za_ne_zero : Z * Aprime ≠ 0 := by
  intro h
  have := congrArg Fp2.c0 h
  revert this; decide

private theorem za_inverse_eq : (Z * Aprime).inverse = zaInv := by
  have h1 : (Z * Aprime) * (Z * Aprime).inverse = 1 := Fp2.mul_inverse_cancel za_ne_zero
  linear_combination zaInv * h1 - (Z * Aprime).inverse * za_mul_zaInv

private def sqrtNormGx1Zero : Fp :=
  Fp.ofNat 0x14bc2d072749c399567308a4ea62f9640737884f167efe5f0485541babeb2042e44ddf51fdf7a7164c1d372558051161

private theorem sqrtNormGx1Zero_sq :
    (sqrtNormGx1Zero : ZMod Fp.modulus) * sqrtNormGx1Zero = Fp2.norm (swuG (Bprime * zaInv)) := by
  decide

private theorem norm_gx2_sq_zmod {nz nu ng sz sg : ZMod Fp.modulus}
    (hsz : sz * sz = -nz) (hsg : sg * sg = -ng) :
    (sz * (nz * (nu * nu * nu)) * sg) * (sz * (nz * (nu * nu * nu)) * sg) =
      ((nz * (nu * nu)) * (nz * (nu * nu)) * (nz * (nu * nu))) * ng := by
  linear_combination
    nz * nz * nu ^ 6 * sg * sg * hsz
    - nz ^ 3 * nu ^ 6 * hsg

/-- For every `u : Fp2`, at least one of `g(x1(u))` or `g(x2(u))` has a square root in `Fp2`.

This proves that the `panic!` branch in `simpleSwu` is unreachable.
-/
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
      change Bprime * (Z * Aprime).inverse = Bprime * zaInv
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
      set w : Fp := sqrtNegNormZ * (Fp2.norm Z * (Fp2.norm u * Fp2.norm u * Fp2.norm u)) * s1
      have hnorm2 : Fp2.norm (swuG (swuX2 u)) =
          ((Fp2.norm Z * (Fp2.norm u * Fp2.norm u)) *
           (Fp2.norm Z * (Fp2.norm u * Fp2.norm u)) *
           (Fp2.norm Z * (Fp2.norm u * Fp2.norm u))) *
          Fp2.norm (swuG (swuX1 u)) := by
        rw [swuG_x2_eq u hdenom_f]
        simp only [Fp2.norm_mul]
      have hw_sq : (w : ZMod Fp.modulus) * w = Fp2.norm (swuG (swuX2 u)) := by
        rw [hnorm2]
        exact norm_gx2_sq_zmod sqrtNegNormZ_sq hs2
      exact sqrt_of_norm_sq hw_sq

/-- Soundness and totality of `simpleSwu` (`RFC 9380 §6.6.2 and §8.8.2`).

For every `u : Fp2`, `simpleSwu u` lies on the 3-isogenous curve `E' : y^2 = x^3 + A'*x + B'`.
-/
theorem simpleSwu_curve_eq (u : Fp2) :
    (simpleSwu u).2 * (simpleSwu u).2 = swuG (simpleSwu u).1 := by
  have hsqrt : ∀ {a c : Fp2}, Fp2.sqrt a = .ok c → c * c = a := fun hs => Fp2.sqrt_ok hs
  have hor := simpleSwu_sqrt_complete u
  revert hor
  unfold simpleSwu swuG swuX2 swuX1
  generalize Fp2.sqrt = sqrtFn at hsqrt ⊢
  rintro (⟨y1, hy1⟩ | ⟨y2, hy2⟩)
  · dsimp only
    rw [hy1]
    dsimp only
    rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y1) y1]
    exact hsqrt hy1
  · dsimp only
    cases h1 : sqrtFn _ with
    | ok y1 =>
      dsimp only
      rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y1) y1]
      exact hsqrt h1
    | error _ =>
      dsimp only
      rw [hy2]
      dsimp only
      rw [sq_ite_neg (sgn0Fp2 u = sgn0Fp2 y2) y2]
      exact hsqrt hy2

end SwuComplete

end EthLib.Cryptography.Bls.HashToCurve

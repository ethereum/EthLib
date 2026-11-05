module

public import EthLib.Cryptography.Proofs.AltBn128.Fp2
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Proofs: `Fp12` of alt_bn128

`Fp12` is `Fp[w] / (w^12 - 18 w^6 + 82)`, a field of `p^12` elements.

Sending `w` to a root of `X^12 - 18 X^6 + 82` maps `Fp12` into the quotient of `ZMod p[X]`.

That map is injective and keeps the product of the specification, so the ring laws hold.

In a quotient by a maximal ideal, the image of `w` is fixed by the `p^12`-th power.

It is not fixed by the `p^4`-th or the `p^6`-th power.

So that quotient has at least `p^12` elements, the ideal is zero, and `Fp12` is a field.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128.Fp12

open Polynomial

open scoped Fin.CommRing

/-- The polynomial `X^12 - 18 X^6 + 82` over `ZMod p`. -/
noncomputable def poly : (ZMod Fp.modulus)[X] := X ^ 12 - C 18 * X ^ 6 + C 82

/-- The map from `Fp` to the quotient by the polynomial. -/
noncomputable def ι : Fp →+* AdjoinRoot poly := (AdjoinRoot.of poly).comp Fp.toZMod.toRingHom

local notation "r" => AdjoinRoot.root poly

/-- The root `r` of the quotient satisfies `r^12 = 18 r^6 - 82`. -/
theorem root_pow_twelve : r ^ 12 = 18 * r ^ 6 - 82 := by
  have h : AdjoinRoot.mk poly (X ^ 12 - C 18 * X ^ 6 + C 82) = 0 := AdjoinRoot.mk_self
  rw [map_add, map_sub, map_mul, map_pow, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.mk_C, map_ofNat, map_ofNat] at h
  linear_combination h

/-- The value of an element at the root, `sum_k a_k r^k`. -/
noncomputable def toQuot (a : Fp12) : AdjoinRoot poly :=
  ∑ i ∈ Finset.range 12, ι a[i]! * r ^ i

/-- The value at the root, term by term. -/
theorem toQuot_eq_terms (a : Fp12) :
    toQuot a = ι a[0] + ι a[1] * r + ι a[2] * r ^ 2 + ι a[3] * r ^ 3 + ι a[4] * r ^ 4 +
    ι a[5] * r ^ 5 + ι a[6] * r ^ 6 + ι a[7] * r ^ 7 + ι a[8] * r ^ 8 + ι a[9] * r ^ 9 +
    ι a[10] * r ^ 10 + ι a[11] * r ^ 11 := by
  simp [toQuot, Finset.sum_range_succ, getElem!_pos]

/-- A value reduced modulo `p` has the value of the number at the root. -/
private theorem ι_ofNat (n : ℕ) : ι (Fin.ofNat Fp.modulus n) = n := by
  have h : Fp.toZMod (Fin.ofNat Fp.modulus n) = n := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast]
    rfl
  rw [ι, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, h,
    map_natCast]

/-- The value of an element of `Fp`, as a number, is its value at the root. -/
private theorem natCast_val (x : Fp) : ((x.val : ℕ) : AdjoinRoot poly) = ι x := by
  rw [ι, RingHom.comp_apply, ← map_natCast (AdjoinRoot.of poly), RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, ← ZMod.natCast_zmod_val (Fp.toZMod x)]
  rfl

/-- The product of the specification is the product in the quotient.

The two sides differ by a multiple of `r^12 - 18 r^6 + 82`, which is 0. -/
theorem toQuot_mul (a b : Fp12) : toQuot (a * b) = toQuot a * toQuot b := by
  change toQuot (mul a b) = _
  rw [toQuot_eq_terms, toQuot_eq_terms a, toQuot_eq_terms b]
  simp only [mul, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
    List.getElem_cons_zero, map_sub, ι_ofNat]
  push_cast
  simp only [natCast_val]
  -- The quotient of the product of the polynomials by `X^12 - 18 X^6 + 82`.
  linear_combination (-(
      (ι a[1] * ι b[11] + ι a[2] * ι b[10] + ι a[3] * ι b[9] + ι a[4] * ι b[8] + ι a[5] * ι b[7] +
        ι a[6] * ι b[6] + ι a[7] * ι b[5] + ι a[8] * ι b[4] + ι a[9] * ι b[3] + ι a[10] * ι b[2] +
        ι a[11] * ι b[1] + 18 * (ι a[7] * ι b[11] + ι a[8] * ι b[10] + ι a[9] * ι b[9] +
        ι a[10] * ι b[8] + ι a[11] * ι b[7])) * r ^ 0 +
      (ι a[2] * ι b[11] + ι a[3] * ι b[10] + ι a[4] * ι b[9] + ι a[5] * ι b[8] + ι a[6] * ι b[7] +
        ι a[7] * ι b[6] + ι a[8] * ι b[5] + ι a[9] * ι b[4] + ι a[10] * ι b[3] + ι a[11] * ι b[2] +
        18 * (ι a[8] * ι b[11] + ι a[9] * ι b[10] + ι a[10] * ι b[9] + ι a[11] * ι b[8])) * r ^ 1 +
      (ι a[3] * ι b[11] + ι a[4] * ι b[10] + ι a[5] * ι b[9] + ι a[6] * ι b[8] + ι a[7] * ι b[7] +
        ι a[8] * ι b[6] + ι a[9] * ι b[5] + ι a[10] * ι b[4] + ι a[11] * ι b[3] +
        18 * (ι a[9] * ι b[11] + ι a[10] * ι b[10] + ι a[11] * ι b[9])) * r ^ 2 +
      (ι a[4] * ι b[11] + ι a[5] * ι b[10] + ι a[6] * ι b[9] + ι a[7] * ι b[8] + ι a[8] * ι b[7] +
        ι a[9] * ι b[6] + ι a[10] * ι b[5] + ι a[11] * ι b[4] + 18 * (ι a[10] * ι b[11] +
        ι a[11] * ι b[10])) * r ^ 3 +
      (ι a[5] * ι b[11] + ι a[6] * ι b[10] + ι a[7] * ι b[9] + ι a[8] * ι b[8] + ι a[9] * ι b[7] +
        ι a[10] * ι b[6] + ι a[11] * ι b[5] + 18 * (ι a[11] * ι b[11])) * r ^ 4 +
      (ι a[6] * ι b[11] + ι a[7] * ι b[10] + ι a[8] * ι b[9] + ι a[9] * ι b[8] + ι a[10] * ι b[7] +
        ι a[11] * ι b[6]) * r ^ 5 +
      (ι a[7] * ι b[11] + ι a[8] * ι b[10] + ι a[9] * ι b[9] + ι a[10] * ι b[8] +
        ι a[11] * ι b[7]) * r ^ 6 +
      (ι a[8] * ι b[11] + ι a[9] * ι b[10] + ι a[10] * ι b[9] + ι a[11] * ι b[8]) * r ^ 7 +
      (ι a[9] * ι b[11] + ι a[10] * ι b[10] + ι a[11] * ι b[9]) * r ^ 8 +
      (ι a[10] * ι b[11] + ι a[11] * ι b[10]) * r ^ 9 +
      (ι a[11] * ι b[11]) * r ^ 10)) * root_pow_twelve

/-! ## The ring -/

instance : One Fp12 := ⟨one⟩

/-- `n` as an element of `Fp12`: the element `n` of `Fp`. -/
instance : NatCast Fp12 := ⟨fun n => ofFp n⟩

/-- `n` as an element of `Fp12`: the element `n` of `Fp`. -/
instance : IntCast Fp12 := ⟨fun n => ofFp n⟩

/-- The value of an element whose coefficients have the values `f i`. -/
theorem toQuot_eq_sum (a : Fp12) (f : ℕ → AdjoinRoot poly)
    (h : ∀ i (hi : i < 12), ι a[i] = f i) : toQuot a = ∑ i ∈ Finset.range 12, f i * r ^ i := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [getElem!_pos a i hi, h i hi]

theorem toQuot_add (a b : Fp12) : toQuot (a + b) = toQuot a + toQuot b := by
  rw [toQuot_eq_sum _ (fun i => ι a[i]! + ι b[i]!), toQuot, toQuot, ← Finset.sum_add_distrib]
  · simp only [add_mul]
  · intro i hi
    change ι (add a b)[i] = _
    simp [add, Fin.getElem_fin, getElem!_pos a i hi, getElem!_pos b i hi]

theorem toQuot_sub (a b : Fp12) : toQuot (a - b) = toQuot a - toQuot b := by
  rw [toQuot_eq_sum _ (fun i => ι a[i]! - ι b[i]!), toQuot, toQuot, ← Finset.sum_sub_distrib]
  · simp only [sub_mul]
  · intro i hi
    change ι (sub a b)[i] = _
    simp [sub, Fin.getElem_fin, getElem!_pos a i hi, getElem!_pos b i hi]

theorem toQuot_neg (a : Fp12) : toQuot (-a) = -toQuot a := by
  rw [toQuot_eq_sum _ (fun i => -ι a[i]!), toQuot, ← Finset.sum_neg_distrib]
  · simp only [neg_mul]
  · intro i hi
    simp [getElem!_pos a i hi]

theorem toQuot_zero : toQuot 0 = 0 := by
  rw [toQuot_eq_sum _ (fun _ => 0)]
  · simp
  · intro i hi
    simp

theorem toQuot_ofFp (x : Fp) : toQuot (ofFp x) = ι x := by
  rw [toQuot_eq_sum _ (fun i => if i = 0 then ι x else 0)]
  · simp
  · intro i hi
    by_cases h : i = 0 <;> simp [ofFp, h]

theorem toQuot_one : toQuot 1 = 1 := by
  rw [show (1 : Fp12) = ofFp 1 from rfl, toQuot_ofFp, map_one]

theorem toQuot_nsmul (n : ℕ) (a : Fp12) : toQuot (n • a) = n • toQuot a := by
  rw [toQuot_eq_sum _ (fun i => n • ι a[i]!), toQuot, Finset.smul_sum]
  · simp only [smul_mul_assoc]
  · intro i hi
    simp [getElem!_pos a i hi]

theorem toQuot_zsmul (n : ℤ) (a : Fp12) : toQuot (n • a) = n • toQuot a := by
  rw [toQuot_eq_sum _ (fun i => n • ι a[i]!), toQuot, Finset.smul_sum]
  · simp only [smul_mul_assoc]
  · intro i hi
    simp [getElem!_pos a i hi]

/-- An element as a polynomial of degree below 12. -/
noncomputable def toPoly (a : Fp12) : (ZMod Fp.modulus)[X] :=
  ∑ i ∈ Finset.range 12, C (Fp.toZMod a[i]!) * X ^ i

theorem coeff_toPoly (a : Fp12) (k : ℕ) :
    (toPoly a).coeff k = if k < 12 then Fp.toZMod a[k]! else 0 := by
  simp only [toPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem toQuot_eq_mk (a : Fp12) : toQuot a = AdjoinRoot.mk poly (toPoly a) := by
  simp only [toQuot, toPoly, map_sum, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

theorem degree_poly : poly.degree = 12 := by
  unfold poly
  compute_degree!

/-- The value at the root is injective, since the polynomial has degree 12. -/
theorem toQuot_injective : Function.Injective toQuot := by
  intro a b h
  rw [toQuot_eq_mk, toQuot_eq_mk, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero] at h
  have hz : toPoly a - toPoly b = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h ?_
    rw [degree_poly]
    refine (degree_lt_iff_coeff_zero _ 12).mpr fun m hm => ?_
    simp [coeff_toPoly, show ¬m < 12 by omega]
  apply Vector.ext
  intro i hi
  have hc := congrArg (fun q => q.coeff i) hz
  simp only [coeff_sub, coeff_toPoly, hi, ↓reduceIte, coeff_zero, sub_eq_zero] at hc
  rw [← getElem!_pos a i hi, ← getElem!_pos b i hi]
  exact hc

/-- The power by repeated products. -/
instance : Pow Fp12 ℕ := ⟨fun a n => npowRec n a⟩

theorem toQuot_pow (a : Fp12) (n : ℕ) : toQuot (a ^ n) = toQuot a ^ n := by
  induction n with
  | zero => exact toQuot_one
  | succ n ih =>
    change toQuot (npowRec n a * a) = _
    rw [toQuot_mul, pow_succ, ← ih]
    rfl

/-- The ring laws, carried back from the quotient. -/
noncomputable instance : CommRing Fp12 :=
  toQuot_injective.commRing toQuot toQuot_zero toQuot_one toQuot_add toQuot_mul toQuot_neg
    toQuot_sub toQuot_nsmul toQuot_zsmul toQuot_pow
    (fun n => (toQuot_ofFp _).trans (map_natCast ι n))
    (fun n => (toQuot_ofFp _).trans (map_intCast ι n))

/-- The product of the specification is the product of the ring. -/
@[simp] theorem mul_eq_mul (a b : Fp12) : mul a b = a * b := rfl

/-! ## Size -/

/-- An element is its 12 coefficients. -/
def equivFun : Fp12 ≃ (Fin 12 → Fp) where
  toFun a k := a[k]
  invFun := Vector.ofFn
  left_inv a := by
    apply Vector.ext
    intro i hi
    simp
  right_inv f := by
    funext k
    simp

noncomputable instance : Fintype Fp12 := Fintype.ofEquiv _ equivFun.symm

/-- `Fp12` has `p^12` elements. -/
theorem card_eq : Fintype.card Fp12 = Fp.modulus ^ 12 := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr equivFun, Nat.card_fun, Nat.card_fin,
    Nat.card_fin]

/-! ## The embeddings of `Fp` and `Fp2` -/

/-- The element of `Fp`, as a ring map. -/
noncomputable def ofFpHom : Fp →+* Fp12 where
  toFun := ofFp
  map_one' := rfl
  map_mul' x y := toQuot_injective (by rw [toQuot_mul, toQuot_ofFp, toQuot_ofFp,
    toQuot_ofFp, map_mul])
  map_zero' := toQuot_injective (by rw [toQuot_ofFp, map_zero, toQuot_zero])
  map_add' x y := toQuot_injective (by rw [toQuot_add, toQuot_ofFp, toQuot_ofFp,
    toQuot_ofFp, map_add])

theorem toQuot_ofFp2 (a : Fp2) : toQuot (ofFp2 a) = ι (a.c0 - 9 * a.c1) + ι a.c1 * r ^ 6 := by
  rw [toQuot_eq_sum _ (fun i => if i = 0 then ι (a.c0 - 9 * a.c1) else
    if i = 6 then ι a.c1 else 0)]
  · simp [Finset.sum_range_succ]
  · intro i hi
    by_cases h0 : i = 0
    · simp [ofFp2, h0]
    · by_cases h6 : i = 6 <;> simp [ofFp2, h0, h6]

/-- The element `a + b i` of `Fp2`, as the ring map to `(a - 9 b) + b w^6`. -/
noncomputable def ofFp2Hom : Fp2 →+* Fp12 where
  toFun := ofFp2
  map_one' := toQuot_injective (by
    rw [toQuot_ofFp2, toQuot_one, Fp2.one_c0, Fp2.one_c1]
    simp)
  map_mul' a b := toQuot_injective (by
    rw [toQuot_mul, toQuot_ofFp2, toQuot_ofFp2, toQuot_ofFp2, Fp2.mul_c0, Fp2.mul_c1]
    simp only [map_add, map_sub, map_mul, map_ofNat]
    linear_combination (-(ι a.c1 * ι b.c1)) * root_pow_twelve)
  map_zero' := toQuot_injective (by
    rw [toQuot_ofFp2, toQuot_zero, Fp2.zero_c0, Fp2.zero_c1]
    simp)
  map_add' a b := toQuot_injective (by
    rw [toQuot_add, toQuot_ofFp2, toQuot_ofFp2, toQuot_ofFp2, Fp2.add_c0, Fp2.add_c1]
    simp only [map_add, map_sub, map_mul]
    ring)

theorem toQuot_wPow (k : Fin 12) : toQuot (wPow k) = r ^ (k : ℕ) := by
  rw [toQuot_eq_sum _ (fun i => if i = k then 1 else 0)]
  · simp [Finset.sum_ite_eq', k.isLt]
  · intro i hi
    by_cases h : i = k <;> simp [wPow, h, Fin.ext_iff]

/-- `w^6 = 9 + i`. -/
theorem w_pow_six : wPow 1 ^ 6 = ofFp2Hom ⟨9, 1⟩ := by
  apply toQuot_injective
  rw [toQuot_pow, toQuot_wPow, ofFp2Hom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    toQuot_ofFp2, show (9 : Fp) - 9 * 1 = 0 by decide, map_zero, map_one]
  simp

/-! ## The field -/

instance : Nontrivial Fp12 :=
  ⟨⟨ofFpHom 0, ofFpHom 1, fun h => absurd (congrArg (fun v : Fp12 => v[0]) h) (by decide)⟩⟩

/-- `(9 + i)^((p^4 - 1) / 6)` is not 1, which the kernel computes. -/
theorem xi_pow_four_ne_one : (⟨9, 1⟩ : Fp2) ^ ((Fp.modulus ^ 4 - 1) / 6) ≠ 1 := by
  rw [← Fp2.powBits_eq_pow 1024 _ _ (by decide +kernel)]
  decide +kernel

/-- `(9 + i)^((p^6 - 1) / 6)` is not 1, which the kernel computes. -/
theorem xi_pow_six_ne_one : (⟨9, 1⟩ : Fp2) ^ ((Fp.modulus ^ 6 - 1) / 6) ≠ 1 := by
  rw [← Fp2.powBits_eq_pow 1536 _ _ (by decide +kernel)]
  decide +kernel

/-- `(9 + i)^((p^12 - 1) / 6)` is 1, which the kernel computes. -/
theorem xi_pow_twelve_eq_one : (⟨9, 1⟩ : Fp2) ^ ((Fp.modulus ^ 12 - 1) / 6) = 1 := by
  rw [← Fp2.powBits_eq_pow 3072 _ _ (by decide +kernel)]
  decide +kernel

/-- The quotient by a maximal ideal has `p^12` elements, so the quotient map is injective. -/
theorem mk_injective (M : Ideal Fp12) [M.IsMaximal] :
    Function.Injective (Ideal.Quotient.mk M) := by
  let _ : Field (Fp12 ⧸ M) := Ideal.Quotient.field M
  let _ : Fintype (Fp12 ⧸ M) := Fintype.ofFinite _
  set π := Ideal.Quotient.mk M
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  let κ : ZMod Fp.modulus →+* Fp12 ⧸ M := π.comp (ofFpHom.comp Fp.toZMod.symm.toRingHom)
  have : CharP (Fp12 ⧸ M) Fp.modulus := charP_of_injective_ringHom κ.injective Fp.modulus
  obtain ⟨n, -, hcard⟩ := FiniteField.card (Fp12 ⧸ M) Fp.modulus
  set α := π (wPow 1)
  set ψ := π.comp ofFp2Hom
  have hα6 : α ^ 6 = ψ ⟨9, 1⟩ := by
    rw [← map_pow, w_pow_six]
    rfl
  have hα : α ≠ 0 := by
    intro h
    have h6 := hα6
    rw [h, zero_pow (by decide), eq_comm, map_eq_zero_iff ψ ψ.injective] at h6
    exact absurd (congrArg Fp2.c1 h6) (by decide)
  -- `α^(p^k) = α` exactly when `(9 + i)^((p^k - 1) / 6) = 1`.
  have key (k : ℕ) (hk : (Fp.modulus ^ k - 1) % 6 = 0) :
      α ^ (Fp.modulus ^ k) = α ↔ (⟨9, 1⟩ : Fp2) ^ ((Fp.modulus ^ k - 1) / 6) = 1 := by
    have hpos : 0 < Fp.modulus ^ k := Nat.pow_pos (by decide)
    have hsplit : Fp.modulus ^ k = 6 * ((Fp.modulus ^ k - 1) / 6) + 1 := by omega
    rw [hsplit, pow_succ, pow_mul, hα6, ← map_pow, mul_eq_right₀ hα, ← hsplit,
      map_eq_one_iff ψ ψ.injective]
  have hper (k : ℕ) : Function.IsPeriodicPt (_root_.frobenius (Fp12 ⧸ M) Fp.modulus) k α ↔
      α ^ (Fp.modulus ^ k) = α := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, iterate_frobenius]
  have hn : Function.IsPeriodicPt (_root_.frobenius (Fp12 ⧸ M) Fp.modulus) n α := by
    rw [hper, ← hcard]
    exact FiniteField.pow_card α
  have h12 : Function.IsPeriodicPt (_root_.frobenius (Fp12 ⧸ M) Fp.modulus) 12 α :=
    (hper 12).mpr ((key 12 (by decide)).mpr xi_pow_twelve_eq_one)
  have hdvd : 12 ∣ (n : ℕ) := by
    have hg := hn.gcd h12
    have hg12 : Nat.gcd n 12 ∣ 12 := Nat.gcd_dvd_right _ _
    by_contra hne
    have hg' : Nat.gcd n 12 ≠ 12 := fun h => hne (h ▸ Nat.gcd_dvd_left _ _)
    -- A proper divisor of 12 divides 4 or 6.
    have h46 : Nat.gcd n 12 ∣ 4 ∨ Nat.gcd n 12 ∣ 6 := by
      have hle : Nat.gcd n 12 ≤ 12 := Nat.le_of_dvd (by decide) hg12
      interval_cases h : Nat.gcd n 12 <;> simp_all
    rcases h46 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have h4 := hg.mul_const c
      rw [← hc, hper, key 4 (by decide)] at h4
      exact xi_pow_four_ne_one h4
    · have h6 := hg.mul_const c
      rw [← hc, hper, key 6 (by decide)] at h6
      exact xi_pow_six_ne_one h6
  have hle : Fintype.card (Fp12 ⧸ M) ≤ Fintype.card Fp12 :=
    Fintype.card_le_of_surjective π hsurj
  have hge : Fintype.card Fp12 ≤ Fintype.card (Fp12 ⧸ M) := by
    rw [card_eq, hcard]
    exact Nat.pow_le_pow_right (by decide) (Nat.le_of_dvd n.pos hdvd)
  exact ((Fintype.bijective_iff_surjective_and_card π).mpr
    ⟨hsurj, (le_antisymm hle hge).symm⟩).1

instance : IsDomain Fp12 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Fp12
  exact Function.Injective.isDomain (Ideal.Quotient.mk M) (mk_injective M)

/-- A finite domain is a field. -/
noncomputable instance instField : Field Fp12 := Fintype.fieldOfDomain Fp12

/-- Every element is fixed by the `p^12`-th power. -/
theorem pow_card_pow (a : Fp12) : a ^ (Fp.modulus ^ 12) = a := by
  rw [← card_eq]
  exact FiniteField.pow_card a

instance : CharP Fp12 Fp.modulus :=
  charP_of_injective_ringHom (ofFpHom.comp Fp.toZMod.symm.toRingHom).injective Fp.modulus

/-- The `p`-th power, a ring map. -/
noncomputable def primeFrobenius : Fp12 →+* Fp12 := _root_.frobenius Fp12 Fp.modulus

theorem primeFrobenius_apply (a : Fp12) : primeFrobenius a = a ^ Fp.modulus :=
  frobenius_def _ a

/-- Square and multiply computes `a^e`, when `e < 2^fuel`. -/
theorem powBits_eq_pow (fuel : Nat) (a : Fp12) (e : Nat) (he : e < 2 ^ fuel) :
    powBits fuel a e = a ^ e := by
  induction fuel generalizing a e with
  | zero =>
    obtain rfl : e = 0 := by simpa using he
    rfl
  | succ fuel ih =>
    have h2 : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at he; omega
    rw [powBits, ih _ _ h2, ← pow_two, ← pow_mul]
    split <;> [rw [← pow_succ']; skip] <;> congr 1 <;> omega

/-! ## The polynomial -/

theorem monic_poly : poly.Monic := by
  unfold poly
  monicity!

theorem natDegree_poly : poly.natDegree = 12 :=
  natDegree_eq_of_degree_eq_some degree_poly

/-- The value at the root, as a ring map. -/
noncomputable def toQuotHom : Fp12 →+* AdjoinRoot poly where
  toFun := toQuot
  map_one' := toQuot_one
  map_mul' := toQuot_mul
  map_zero' := toQuot_zero
  map_add' := toQuot_add

/-- `X^12 - 18 X^6 + 82` is irreducible over `ZMod p`.

The value at the root is injective, and both sides have `p^12` elements. -/
theorem irreducible_poly : Irreducible poly := by
  let pb := AdjoinRoot.powerBasis' monic_poly
  let _ : Fintype (AdjoinRoot poly) := Module.fintypeOfFintype pb.basis
  have hcard : Fintype.card Fp12 = Fintype.card (AdjoinRoot poly) := by
    rw [card_eq, Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin,
      AdjoinRoot.powerBasis'_dim, natDegree_poly]
  have hbij : Function.Bijective toQuotHom :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨toQuot_injective, hcard⟩
  rw [← AdjoinRoot.isField_iff_irreducible]
  exact (RingEquiv.ofBijective toQuotHom hbij).symm.toMulEquiv.isField (Field.toIsField Fp12)

end EthLib.Cryptography.AltBn128.Fp12

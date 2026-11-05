module

public import EthLib.Cryptography.Proofs.AltBn128.Fp12

/-!
# Proofs: the final exponentiation of alt_bn128

The final exponentiation raises its argument to `(p^12 - 1) / q`.

It reaches that power with Frobenius maps, one inverse and powers by `u` and small numbers.

Each of these steps is a power of its argument, so the result is a power `f^n`.

The exponent `n` agrees with `(p^12 - 1) / q` modulo `p^12 - 1`, which the kernel checks.

`Fp12` has `p^12` elements, so both powers are equal.
-/

@[expose] public section

namespace EthLib.Cryptography.AltBn128

namespace Fp12

open Polynomial

open scoped Fin.CommRing

local notation "r" => AdjoinRoot.root poly

/-- Scaling by `c` is the product by the element `c` of `Fp`. -/
theorem scale_eq (c : Fp) (a : Fp12) : scale c a = ofFpHom c * a := by
  apply toQuot_injective
  rw [toQuot_mul, show ofFpHom c = ofFp c from rfl, toQuot_ofFp,
    toQuot_eq_sum _ (fun i => ι c * ι a[i]!), toQuot, Finset.mul_sum]
  · simp only [mul_assoc]
  · intro i hi
    simp [scale, Fin.getElem_fin, getElem!_pos a i hi]

/-- An element is the sum of its coefficients times the powers of `w`. -/
theorem eq_sum (a : Fp12) :
    a = ∑ k ∈ Finset.range 12, ofFpHom a[k]! * wPow 1 ^ k := by
  apply toQuot_injective
  change toQuot a = toQuotHom (∑ k ∈ Finset.range 12, ofFpHom a[k]! * wPow 1 ^ k)
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow]
  change _ = toQuot (ofFp _) * toQuot (wPow 1) ^ k
  rw [toQuot_ofFp, toQuot_wPow]
  simp

/-- The element `c` of `Fp` is fixed by the `p`-th power. -/
theorem ofFpHom_pow_modulus (c : Fp) : ofFpHom c ^ Fp.modulus = ofFpHom c := by
  rw [← map_pow]
  congr 1
  exact ZMod.pow_card (p := Fp.modulus) c

theorem frobeniusCoefficients_getElem {k : ℕ} (hk : k < 12) :
    frobeniusCoefficients[k]! = (wPow 1 ^ Fp.modulus) ^ k := by
  have hwp : powBits 256 (wPow 1) Fp.modulus = wPow 1 ^ Fp.modulus :=
    powBits_eq_pow 256 _ _ (by decide)
  unfold frobeniusCoefficients
  rw [hwp]
  generalize wPow 1 ^ Fp.modulus = wp
  -- After `s` steps, the array holds `wp^0, ..., wp^s`.
  have key (s : ℕ) : ∀ c : Array Fp12, c.size = 1 → c[0]! = 1 →
      ((List.range s).foldl (fun powers _ => powers.push (powers.back! * wp)) c).size = s + 1 ∧
      ∀ i ≤ s, ((List.range s).foldl (fun powers _ => powers.push (powers.back! * wp)) c)[i]! =
        wp ^ i := by
    intro c hc hc0
    induction s with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨hc, fun i hi => ?_⟩
      obtain rfl : i = 0 := by omega
      rw [hc0, pow_zero]
    | succ s ih =>
      obtain ⟨hsize, hval⟩ := ih
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set d := (List.range s).foldl (fun powers _ => powers.push (powers.back! * wp)) c
      refine ⟨by simp [hsize], fun i hi => ?_⟩
      have hback : d.back! = wp ^ s := by
        rw [Array.back!, hsize, Nat.add_sub_cancel, hval s le_rfl]
      rcases Nat.lt_or_ge i (s + 1) with h | h
      · rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos d i (by omega), hval i (by omega)]
      · obtain rfl : i = s + 1 := by omega
        rw [getElem!_pos _ _ (by simp [hsize]), Array.getElem_push]
        simp only [hsize, lt_irrefl, ↓reduceDIte, hback, pow_succ]
  exact (key 11 #[1] rfl rfl).2 k (by omega)

/-- The Frobenius map of the specification is the `p`-th power. -/
theorem frobenius_eq_pow (a : Fp12) : frobenius a = a ^ Fp.modulus := by
  have hsum : frobenius a =
      ∑ k ∈ Finset.range 12, ofFpHom a[k]! * (wPow 1 ^ Fp.modulus) ^ k := by
    unfold frobenius
    have h (n : ℕ) (hn : n ≤ 12) (x : Fp12) :
        (List.range n).foldl (fun acc k => acc + scale a[k]! frobeniusCoefficients[k]!) x =
          x + ∑ k ∈ Finset.range n, ofFpHom a[k]! * (wPow 1 ^ Fp.modulus) ^ k := by
      induction n generalizing x with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
          Finset.sum_range_succ, scale_eq, frobeniusCoefficients_getElem (by omega), add_assoc]
    rw [h 12 le_rfl, show ofFp 0 = ofFpHom 0 from rfl, map_zero, zero_add]
  rw [hsum]
  conv_rhs => rw [eq_sum a, ← primeFrobenius_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, primeFrobenius_apply, primeFrobenius_apply, ofFpHom_pow_modulus]

/-- `n` applications of the Frobenius map give the `p^n`-th power. -/
theorem frobeniusPow_eq_pow (n : ℕ) (a : Fp12) : frobeniusPow n a = a ^ Fp.modulus ^ n := by
  induction n generalizing a with
  | zero => simp [frobeniusPow]
  | succ n ih => rw [frobeniusPow, ih, frobenius_eq_pow, ← pow_mul, pow_succ']

/-- The element of `Fp` at coefficient 0 of an element of `Fp`. -/
theorem ofFpHom_getElem_zero (c : Fp) : (ofFpHom c)[0] = c := by
  change (ofFp c)[0] = c
  simp [ofFp]

/-- The inverse in `Fp` is the field inverse, carried into `Fp12`. -/
theorem ofFpHom_inv (c : Fp) : ofFpHom c.inv = (ofFpHom c)⁻¹ := by
  have h := map_inv₀ (ofFpHom.comp Fp.toZMod.symm.toRingHom) (Fp.toZMod c)
  rw [← Fp.toZMod_inv] at h
  exact h

/-- An element fixed by the `p`-th power lies in `Fp`. -/
theorem eq_ofFpHom_of_pow_eq {x : Fp12} (h : x ^ Fp.modulus = x) : x = ofFpHom x[0] := by
  have hbot := (Subfield.mem_bot_iff_pow_eq_self Fp12 Fp.modulus).mpr h
  rw [← ZMod.fieldRange_castHom_eq_bot Fp.modulus] at hbot
  obtain ⟨c, rfl⟩ := hbot
  have hc : ZMod.castHom (dvd_refl _) Fp12 = ofFpHom.comp Fp.toZMod.symm.toRingHom :=
    RingHom.ext_zmod _ _
  rw [hc]
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [ofFpHom_getElem_zero]

/-- The inverse of the specification is the field inverse. -/
theorem inverse_eq_inv (a : Fp12) : a.inverse = a⁻¹ := by
  -- After `s` steps, the loop holds `a^(p + ... + p^s)` and `a^(p^s)`.
  have hloop (s : ℕ) : (List.range s).foldl (fun (gc : Fp12 × Fp12) _ =>
      (gc.1 * frobenius gc.2, frobenius gc.2)) (1, a) =
        (∏ i ∈ Finset.range s, a ^ Fp.modulus ^ (i + 1), a ^ Fp.modulus ^ s) := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        Finset.prod_range_succ, frobenius_eq_pow, ← pow_mul, ← pow_succ]
  unfold inverse
  simp only
  rw [show (one, a) = ((1 : Fp12), a) from rfl, hloop 11]
  set g := ∏ i ∈ Finset.range 11, a ^ Fp.modulus ^ (i + 1)
  -- `a g = a^(1 + p + ... + p^11)` is fixed by the `p`-th power.
  have hnorm : (a * g) ^ Fp.modulus = a * g := by
    have hag : a * g = ∏ i ∈ Finset.range 12, a ^ Fp.modulus ^ i := by
      rw [Finset.prod_range_succ', pow_zero, pow_one, mul_comm]
    rw [hag, ← Finset.prod_pow, Finset.prod_range_succ, Finset.prod_range_succ' _ 11,
      ← pow_mul, ← pow_succ, pow_zero, pow_one, pow_card_pow]
    refine congrArg (· * a) (Finset.prod_congr rfl fun i _ => ?_)
    rw [← pow_mul, ← pow_succ]
  rw [scale_eq, mul_comm]
  by_cases ha : a = 0
  · subst ha
    have hg : g = 0 := Finset.prod_eq_zero (Finset.mem_range.mpr (by decide : 0 < 11))
      (zero_pow (pow_ne_zero _ (by decide)))
    rw [hg, zero_mul, inv_zero]
  · have hg : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ ha
    have hN := eq_ofFpHom_of_pow_eq hnorm
    have hinv : ofFpHom (a * g)[0].inv = (a * g)⁻¹ := by
      rw [ofFpHom_inv, ← hN]
    rw [hinv, mul_inv, mul_comm a⁻¹, ← mul_assoc, mul_inv_cancel₀ hg, one_mul]

/-- In a finite field the inverse is the power by the order minus two. -/
theorem inv_eq_pow (f : Fp12) : f⁻¹ = f ^ (Fp.modulus ^ 12 - 2) := by
  by_cases hf : f = 0
  · rw [hf, inv_zero, zero_pow (by decide)]
  · have h1 : f ^ (Fp.modulus ^ 12 - 2) * f = 1 := by
      rw [← pow_succ, show Fp.modulus ^ 12 - 2 + 1 = Fintype.card Fp12 - 1 by
        rw [card_eq]; decide]
      exact FiniteField.pow_card_sub_one_eq_one f hf
    exact (eq_inv_of_mul_eq_one_left h1).symm

/-- Two positive exponents that agree modulo `p^12 - 1` give the same power. -/
theorem pow_eq_pow_of_mod {f : Fp12} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m % (Fp.modulus ^ 12 - 1) = n % (Fp.modulus ^ 12 - 1)) : f ^ m = f ^ n := by
  by_cases hf : f = 0
  · rw [hf, zero_pow hm, zero_pow hn]
  · have h1 : f ^ (Fp.modulus ^ 12 - 1) = 1 := by
      rw [← card_eq]
      exact FiniteField.pow_card_sub_one_eq_one f hf
    rw [← Nat.div_add_mod m (Fp.modulus ^ 12 - 1), ← Nat.div_add_mod n (Fp.modulus ^ 12 - 1),
      pow_add, pow_add, pow_mul, pow_mul, h1, one_pow, one_pow, h]

end Fp12

/-- The final exponentiation raises its argument to `(p^12 - 1) / q`. -/
theorem finalExponentiation_eq_pow (f : Fp12) : finalExponentiation f = f ^ FINAL_EXPONENT := by
  have hu (a : Fp12) : Fp12.powBits 64 a BN_U = a ^ BN_U :=
    Fp12.powBits_eq_pow 64 a BN_U (by decide)
  have hs (a : Fp12) (e : ℕ) (he : e < 64) : Fp12.powBits 6 a e = a ^ e :=
    Fp12.powBits_eq_pow 6 a e he
  unfold finalExponentiation
  simp only [hu, hs _ 36 (by decide), hs _ 30 (by decide), hs _ 18 (by decide),
    hs _ 12 (by decide), hs _ 6 (by decide), hs _ 2 (by decide), Fp12.inverse_eq_inv,
    Fp12.inv_eq_pow, Fp12.frobeniusPow_eq_pow, Fp12.frobenius_eq_pow, ← pow_mul, ← pow_add]
  -- Both exponents are numbers; the kernel compares them modulo `p^12 - 1`.
  exact Fp12.pow_eq_pow_of_mod (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The final exponentiation is multiplicative. -/
theorem finalExponentiation_mul (a b : Fp12) :
    finalExponentiation (a * b) = finalExponentiation a * finalExponentiation b := by
  rw [finalExponentiation_eq_pow, finalExponentiation_eq_pow, finalExponentiation_eq_pow,
    mul_pow]

end EthLib.Cryptography.AltBn128

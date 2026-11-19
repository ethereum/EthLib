module

public import EthLib.Cryptography.BinaryField.GF64
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.ComputeDegree

/-!
# Proofs: the residue map of `GF(2^64)`

An element stands for the polynomial `b_0 + b_1 x + ... + b_63 x^63` over GF(2).

Here `b_i` is bit `i` of its word.

Its residue is the class of that polynomial modulo `f = x^64 + x^4 + x^3 + x + 1`.

- Two different elements have two different residues.
- The sum of two elements is the sum of their residues.
- The product of two elements is the product of their residues.
- The elements `0`, `1` and `g` have the residues `0`, `1` and the class of `x`.

Each result holds for all inputs.

The quotient is a field when `f` is irreducible, which this file does not prove.

Lidl and Niederreiter, Finite Fields, chapter 2, give this representation of `GF(2^n)`.
-/

@[expose] public section

namespace EthLib.Cryptography.BinaryField.GF64

open Polynomial

/-- The field polynomial `x^64 + x^4 + x^3 + x + 1`. -/
noncomputable def modulus : (ZMod 2)[X] := X ^ 64 + X ^ 4 + X ^ 3 + X + 1

/-- The polynomial of a word: bit `i` is the coefficient of `x^i`. -/
noncomputable def toPoly (a : GF64) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 64, if a.bits.toNat.testBit i then X ^ i else 0

/-- The residue of an element modulo the field polynomial. -/
noncomputable def residue (a : GF64) : AdjoinRoot modulus := AdjoinRoot.mk modulus (toPoly a)

/-! ## The polynomial of a word -/

/-- The coefficient of `x^k` is bit `k`, for `k < 64`, and 0 above. -/
theorem coeff_toPoly (a : GF64) (k : ℕ) :
    (toPoly a).coeff k = if k < 64 ∧ a.bits.toNat.testBit k then 1 else 0 := by
  simp only [toPoly, finsetSum_coeff, apply_ite (fun p : (ZMod 2)[X] => p.coeff k),
    coeff_X_pow, coeff_zero]
  by_cases hk : k < 64
  · -- Only the term `i = k` of the sum reaches `x^k`.
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)]
    · simp [hk]
    · intro i _ hik
      simp [Ne.symm hik]
  · -- Every term is a power below `x^64`.
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp [show k ≠ i by omega]

/-- A word has no bit from 64 up. -/
private theorem testBit_toNat_of_le (w : UInt64) {k : ℕ} (hk : 64 ≤ k) :
    w.toNat.testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le w.toNat_lt (Nat.pow_le_pow_right (by decide) hk))

/-- The coefficient of `x^k` is bit `k`, for every `k`. -/
private theorem coeff_toPoly_mk (w : UInt64) (k : ℕ) :
    (toPoly ⟨w⟩).coeff k = if w.toNat.testBit k then 1 else 0 := by
  rw [coeff_toPoly]
  by_cases hk : k < 64
  · simp [hk]
  · simp [hk, testBit_toNat_of_le w (show 64 ≤ k by omega)]

/-- The polynomial of a word has degree below 64. -/
theorem degree_toPoly_lt (a : GF64) : (toPoly a).degree < 64 := by
  rw [show (64 : WithBot ℕ) = ((64 : ℕ) : WithBot ℕ) from rfl, degree_lt_iff_coeff_zero]
  intro m hm
  simp [coeff_toPoly, show ¬ m < 64 by omega]

/-- The exclusive or of two words adds their polynomials, since the coefficients lie in GF(2). -/
private theorem toPoly_xor (u v : UInt64) : toPoly ⟨u ^^^ v⟩ = toPoly ⟨u⟩ + toPoly ⟨v⟩ := by
  ext k
  simp only [coeff_add, coeff_toPoly_mk, UInt64.toNat_xor, Nat.testBit_xor]
  cases u.toNat.testBit k <;> cases v.toNat.testBit k <;> simp
  decide

/-- The zero word has the zero polynomial. -/
private theorem toPoly_zero : toPoly ⟨0⟩ = 0 := by
  ext k
  simp [coeff_toPoly_mk]

/-- Bit `k` of a word shifted up by `t` places is bit `k - t`, below bit 64. -/
private theorem testBit_shiftLeft (w t : UInt64) (ht : t.toNat < 64) (k : ℕ) :
    (w <<< t).toNat.testBit k =
      (decide (k < 64) && decide (t.toNat ≤ k) && w.toNat.testBit (k - t.toNat)) := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt ht, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  cases decide (k < 64) <;> simp

/-- Bit `k` of a word shifted down by `t` places is bit `t + k`. -/
private theorem testBit_shiftRight (w t : UInt64) (ht : t.toNat < 64) (k : ℕ) :
    (w >>> t).toNat.testBit k = w.toNat.testBit (t.toNat + k) := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt ht, Nat.testBit_shiftRight]

/-- A shift up by no place keeps the polynomial. -/
private theorem toPoly_shiftLeft_zero (w t : UInt64) (ht : t.toNat = 0) :
    toPoly ⟨w <<< t⟩ = toPoly ⟨w⟩ := by
  ext k
  rw [coeff_toPoly_mk, coeff_toPoly_mk, testBit_shiftLeft w t (by omega), ht]
  by_cases hk : k < 64
  · simp [hk]
  · simp [hk, testBit_toNat_of_le w (show 64 ≤ k by omega)]

/-- A shift up by `t` places, with the top `t` bits in a high word, is the product by `x^t`.

It needs `t` from 1 to 63 and the high shift to be `64 - t`. -/
private theorem toPoly_shiftLeft_add (w t u : UInt64) {n : ℕ} (htn : t.toNat = n) (hn0 : 0 < n)
    (hn : n < 64) (hu : u.toNat = 64 - n) :
    toPoly ⟨w <<< t⟩ + X ^ 64 * toPoly ⟨w >>> u⟩ = X ^ n * toPoly ⟨w⟩ := by
  subst htn
  have ht := hn
  ext k
  simp only [coeff_add, coeff_X_pow_mul', coeff_toPoly_mk, testBit_shiftLeft w t ht,
    testBit_shiftRight w u (by omega), hu]
  by_cases hk : k < 64
  · by_cases htk : t.toNat ≤ k
    · simp [hk, htk, show ¬ 64 ≤ k by omega]
    · simp [hk, htk, show ¬ 64 ≤ k by omega]
  · rw [show 64 - t.toNat + (k - 64) = k - t.toNat by omega]
    simp [hk, show t.toNat ≤ k by omega, show 64 ≤ k by omega]

/-! ## The carry-less product -/

/-- A shift count below 64 keeps its value as a word. -/
private theorem toNat_toUInt64 {i : ℕ} (hi : i < 64) : i.toUInt64.toNat = i := by
  simp only [Nat.toUInt64_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by decide))

/-- The step of the product tests bit `i` of `b`. -/
private theorem shiftRight_and_one_eq_one (b : UInt64) {i : ℕ} (hi : i < 64) :
    (b >>> i.toUInt64) &&& 1 = 1 ↔ b.toNat.testBit i = true := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one,
    toNat_toUInt64 hi,
    Nat.mod_eq_of_lt hi, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

/-- A fold over `0, ..., n - 1` that adds `x^i` times `a` at each set bit `i` of `b`.

It needs each step below 64 to add that term to `lo + x^64 hi`, from `(0, 0)`. -/
private theorem toPoly_foldl {F : UInt64 × UInt64 → ℕ → UInt64 × UInt64} (a b : UInt64)
    (hF : ∀ s i, i < 64 → toPoly ⟨(F s i).2⟩ + X ^ 64 * toPoly ⟨(F s i).1⟩ =
      toPoly ⟨s.2⟩ + X ^ 64 * toPoly ⟨s.1⟩ +
        if b.toNat.testBit i then X ^ i * toPoly ⟨a⟩ else 0)
    (n : ℕ) (hn : n ≤ 64) :
    toPoly ⟨((List.range n).foldl F (0, 0)).2⟩ +
        X ^ 64 * toPoly ⟨((List.range n).foldl F (0, 0)).1⟩ =
      ∑ i ∈ Finset.range n, if b.toNat.testBit i then X ^ i * toPoly ⟨a⟩ else 0 := by
  induction n with
  | zero => simp [toPoly_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hF _ n (by omega),
      ih (by omega), Finset.sum_range_succ]

/-- The carry-less product of two words is the product of their polynomials. -/
private theorem toPoly_clmul (a b : UInt64) :
    toPoly ⟨(clmul a b).2⟩ + X ^ 64 * toPoly ⟨(clmul a b).1⟩ = toPoly ⟨a⟩ * toPoly ⟨b⟩ := by
  refine (toPoly_foldl a b ?_ 64 le_rfl).trans ?_
  · rintro ⟨hi, lo⟩ i hi64
    have hti := toNat_toUInt64 hi64
    dsimp only
    split
    · rename_i hbit
      simp only [(shiftRight_and_one_eq_one b hi64).mp hbit, ↓reduceIte]
      split
      · rename_i h0
        subst h0
        rw [toPoly_xor, toPoly_shiftLeft_zero a _ hti]
        ring
      · rename_i h0
        rw [toPoly_xor, toPoly_xor, ← toPoly_shiftLeft_add a i.toUInt64 (64 - i).toUInt64 hti
          (by omega) hi64 (toNat_toUInt64 (by omega))]
        ring
    · rename_i hbit
      have hb : b.toNat.testBit i = false := by
        cases h : b.toNat.testBit i
        · rfl
        · exact absurd ((shiftRight_and_one_eq_one b hi64).mpr h) hbit
      simp only [hb, Bool.false_eq_true, ↓reduceIte, add_zero]
  · rw [toPoly.eq_1 ⟨b⟩, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split <;> simp [mul_comm]

/-! ## The reduction -/

/-- The spill of the reduction has no bit from 4 up. -/
private theorem testBit_spill (hi : UInt64) {m : ℕ} (hm : 4 ≤ m) :
    ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)).toNat.testBit m = false := by
  rw [UInt64.toNat_xor, UInt64.toNat_xor, Nat.testBit_xor, Nat.testBit_xor,
    testBit_shiftRight hi 63 (by decide), testBit_shiftRight hi 61 (by decide),
    testBit_shiftRight hi 60 (by decide), show (63 : UInt64).toNat = 63 from rfl,
    show (61 : UInt64).toNat = 61 from rfl, show (60 : UInt64).toNat = 60 from rfl,
    testBit_toNat_of_le hi (show 64 ≤ 63 + m by omega),
    testBit_toNat_of_le hi (show 64 ≤ 61 + m by omega),
    testBit_toNat_of_le hi (show 64 ≤ 60 + m by omega)]
  rfl

/-- Shifting `hi` plus the spill down by at least 60 places sees only `hi`.

It needs `v` to be `hi` plus the spill, and a shift from 60 to 63. -/
private theorem toPoly_spill_shiftRight {hi v : UInt64} (t : UInt64)
    (hv : v = hi ^^^ ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60))) (ht : 60 ≤ t.toNat)
    (ht64 : t.toNat < 64) : toPoly ⟨v >>> t⟩ = toPoly ⟨hi >>> t⟩ := by
  ext k
  rw [coeff_toPoly_mk, coeff_toPoly_mk, testBit_shiftRight v t ht64, testBit_shiftRight hi t ht64,
    hv, UInt64.toNat_xor, Nat.testBit_xor, testBit_spill hi (by omega), Bool.xor_false]

/-- The reduction keeps the residue of `lo + x^64 hi`. -/
private theorem mk_reduce (hi lo : UInt64) :
    AdjoinRoot.mk modulus (toPoly ⟨lo⟩ + X ^ 64 * toPoly ⟨hi⟩) =
      AdjoinRoot.mk modulus (toPoly ⟨reduce hi lo⟩) := by
  obtain ⟨s, hs⟩ : ∃ s, s = (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = hi ^^^ s := ⟨_, rfl⟩
  have hred : reduce hi lo = lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4) := by
    rw [hv, hs]
    rfl
  -- Each shift of `v` is `x^t v`, plus the bits that pass `x^63`.
  have e1 := CharTwo.add_eq_iff_eq_add.mp
    (toPoly_shiftLeft_add v 1 63 (n := 1) (by decide) (by decide) (by decide) (by decide))
  have e3 := CharTwo.add_eq_iff_eq_add.mp
    (toPoly_shiftLeft_add v 3 61 (n := 3) (by decide) (by decide) (by decide) (by decide))
  have e4 := CharTwo.add_eq_iff_eq_add.mp
    (toPoly_shiftLeft_add v 4 60 (n := 4) (by decide) (by decide) (by decide) (by decide))
  -- Those bits are the spill, since `v` and `hi` agree from bit 4 up.
  rw [hs] at hv
  rw [toPoly_spill_shiftRight 63 hv (by decide) (by decide)] at e1
  rw [toPoly_spill_shiftRight 61 hv (by decide) (by decide)] at e3
  rw [toPoly_spill_shiftRight 60 hv (by decide) (by decide)] at e4
  -- The rest is `f` times `hi + spill`.
  rw [hred, toPoly_xor, toPoly_xor, toPoly_xor, toPoly_xor, e1, e3, e4, hv, AdjoinRoot.mk_eq_mk]
  simp only [toPoly_xor]
  refine ⟨toPoly ⟨hi⟩ + toPoly ⟨hi >>> 63⟩ + toPoly ⟨hi >>> 61⟩ + toPoly ⟨hi >>> 60⟩, ?_⟩
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
  rw [modulus]
  linear_combination (-(X ^ 64 * (toPoly ⟨hi >>> 63⟩ + toPoly ⟨hi >>> 61⟩ +
    toPoly ⟨hi >>> 60⟩) + (X ^ 4 + X ^ 3 + X + 1) * (toPoly ⟨hi⟩ + toPoly ⟨hi >>> 63⟩ +
      toPoly ⟨hi >>> 61⟩ + toPoly ⟨hi >>> 60⟩))) * h2

/-! ## The residue map -/

/-- The field polynomial has degree 64, as a `WithBot ℕ` degree. -/
private theorem degree_modulus : modulus.degree = 64 := by
  unfold modulus
  compute_degree!

/-- The field polynomial has degree 64. -/
theorem natDegree_modulus : modulus.natDegree = 64 := by
  unfold modulus
  compute_degree!

/-- The field polynomial is monic. -/
theorem monic_modulus : modulus.Monic := by
  unfold modulus
  monicity!

/-- `MODULUS_LOW` holds the terms of the field polynomial below `x^64`. -/
theorem modulus_eq_MODULUS_LOW : modulus = X ^ 64 + toPoly ⟨MODULUS_LOW⟩ := by
  have hlow : toPoly ⟨MODULUS_LOW⟩ = X ^ 4 + X ^ 3 + X + 1 := by
    ext k
    rw [coeff_toPoly_mk]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    rcases Nat.lt_or_ge k 5 with hk | hk
    · interval_cases k <;> decide
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : MODULUS_LOW.toNat < 2 ^ 5)
        (Nat.pow_le_pow_right (by decide) hk))]
      simp [show k ≠ 4 by omega, show k ≠ 3 by omega, show 1 ≠ k by omega, show k ≠ 0 by omega]
  rw [hlow, modulus]
  ring

/-- Two different elements have two different residues. -/
theorem residue_injective : Function.Injective residue := by
  rintro ⟨u⟩ ⟨w⟩ h
  rw [residue, residue, AdjoinRoot.mk_eq_mk] at h
  -- A multiple of the field polynomial of degree below 64 is zero.
  have hdeg : (toPoly ⟨u⟩ - toPoly ⟨w⟩).degree < modulus.degree := by
    rw [degree_modulus]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_toPoly_lt _) (degree_toPoly_lt _))
  have hp : toPoly ⟨u⟩ = toPoly ⟨w⟩ := by
    by_contra hne
    exact monic_modulus.not_dvd_of_degree_lt (sub_ne_zero.mpr hne) hdeg h
  -- Equal polynomials have equal bits.
  congr 1
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  have hc := congrArg (fun p => p.coeff i) hp
  simp only [coeff_toPoly_mk] at hc
  cases hu : u.toNat.testBit i <;> cases hw : w.toNat.testBit i <;> simp_all

/-- The sum of two elements is the sum of their residues. -/
theorem residue_add (a b : GF64) : residue (a + b) = residue a + residue b := by
  rw [residue, show a + b = ⟨a.bits ^^^ b.bits⟩ from rfl, toPoly_xor, map_add]
  rfl

/-- The product of two elements is the product of their residues. -/
theorem residue_mul (a b : GF64) : residue (a * b) = residue a * residue b := by
  have hc := toPoly_clmul a.bits b.bits
  rcases h : clmul a.bits b.bits with ⟨hi, lo⟩
  rw [h] at hc
  have hab : a * b = ⟨reduce hi lo⟩ := by
    show mul a b = _
    simp only [mul, h]
  rw [hab, residue, ← mk_reduce, hc, map_mul]
  rfl

/-- The zero element has the residue 0. -/
theorem residue_zero : residue 0 = 0 := by
  rw [residue, show (0 : GF64) = ⟨0⟩ from rfl, toPoly_zero, map_zero]

/-- The element `1` has the residue 1. -/
theorem residue_one : residue 1 = 1 := by
  have h : toPoly ⟨1⟩ = 1 := by
    ext k
    rw [coeff_toPoly_mk, show (1 : UInt64).toNat = 2 ^ 0 from rfl, Nat.testBit_two_pow, coeff_one]
    rcases k with _ | k <;> simp
  rw [residue, show (1 : GF64) = ⟨1⟩ from rfl, h, map_one]

/-- The generator has the residue of `x`. -/
theorem residue_g : residue g = AdjoinRoot.root modulus := by
  have h : toPoly ⟨2⟩ = X := by
    ext k
    rw [coeff_toPoly_mk, show (2 : UInt64).toNat = 2 ^ 1 from rfl, Nat.testBit_two_pow, coeff_X]
    by_cases hk : 1 = k <;> simp [hk]
  rw [residue, show g = ⟨2⟩ from rfl, h, AdjoinRoot.mk_X]

end EthLib.Cryptography.BinaryField.GF64

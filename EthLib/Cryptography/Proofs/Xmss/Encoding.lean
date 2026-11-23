module

public import EthLib.Cryptography.Xmss.Encoding
public import EthLib.Cryptography.Proofs.Xmss.Words
public import EthLib.Cryptography.Proofs.Wots.TargetSum
public import Mathlib.Tactic

/-!
# Proofs: the leanXMSS target-sum code

What a codeword is, and what it guarantees.

- Its 58 digits sum to the target `T = 106`.
- Its digits determine the digest: no two digests share a codeword.
- Two distinct codewords are incomparable: each has a digit below the other's.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {d d' : Digest} {x y : Vector (Fin CHAIN_LENGTH) V}

/-! ## Unfolding a codeword -/

/-- A lane shifted by `k < 64` bits, modulo 4, is its integer's base-4 digit at bit `k`. -/
private theorem toNat_shiftRight_mod_four (x : UInt64) (k : Nat) (hk : k < 64) :
    ((x >>> k.toUInt64) % 4).toNat = x.toNat / 2 ^ k % 4 := by
  rw [UInt64.toNat_mod, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  congr 3
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow]
  omega

/-- Digit `i` of `lo + 2^64 hi`: digit `i` of `lo` below 32, and digit `i - 32` of `hi` above. -/
private theorem digit_lanes (lo hi i : Nat) (hlo : lo < 2 ^ 64) :
    (lo + 2 ^ 64 * hi) / 4 ^ i % 4 =
      if i < 32 then lo / 4 ^ i % 4 else hi / 4 ^ (i - 32) % 4 := by
  split
  · next hi32 =>
    -- `4^i` divides `2^64`, and leaves a multiple of 4 for the high lane.
    have h : 2 ^ 64 * hi = 4 ^ i * (4 * (4 ^ (31 - i) * hi)) := by
      have : (2 : Nat) ^ 64 = 4 ^ i * (4 * 4 ^ (31 - i)) := by
        rw [← pow_succ', ← pow_add, show i + (31 - i + 1) = 32 by omega]
        norm_num
      rw [this]
      ring
    rw [h, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  · next hi32 =>
    -- `4^i` is `2^64` times `4^(i - 32)`, and the low lane is below `2^64`.
    rw [show 4 ^ i = 2 ^ 64 * 4 ^ (i - 32) by
      rw [show i = 32 + (i - 32) by omega, Nat.pow_add, Nat.add_sub_cancel_left]; norm_num,
      ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hlo, Nat.zero_add]

/-- Digit `i` read from its lane is base-4 digit `i` of the digest's integer. -/
theorem digit_val (d : Digest) (i : Fin DIGITS) :
    (Internal.digit d i).val = d.toNat / 4 ^ i.val % 4 := by
  have hi := i.isLt
  simp only [DIGITS] at hi
  simp only [Internal.digit, Hash.Keccak.Lanes2.toNat, digit_lanes _ _ _ d.lo.toNat_lt]
  split
  · next h => rw [toNat_shiftRight_mod_four _ _ (by omega), Nat.pow_mul, Nat.mod_eq_of_lt h]
  · next h =>
    rw [toNat_shiftRight_mod_four _ _ (by omega), Nat.pow_mul,
      Nat.mod_eq_sub_mod (Nat.le_of_not_lt h), Nat.mod_eq_of_lt (show i.val - 32 < 32 by omega)]

/-- Digit `i` of a digest's vector of digits, as a number. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < DIGITS) :
    ((Internal.digits d)[i]'hi).val = d.toNat / 4 ^ i % 4 := by
  simp only [Internal.digits, Vector.getElem_ofFn, digit_val]

/-- The digits read from the lanes are the base-4 digits of the digest's bytes. -/
theorem digits_eq_digits4 : Internal.digits = fun d => Wots.digits4 d.bytes := by
  funext d
  refine Vector.ext fun i hi => Fin.ext ?_
  have h := Vector.getElem_ofFn (i := i) (by simpa only [DIGITS] using hi)
    (f := fun k : Fin 64 =>
      (⟨bytesToUint d.bytes / 4 ^ k.val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4))
  rw [digits_getElem_val, ← Hash.Keccak.Lanes2.bytesToUint_bytes]
  exact (congrArg Fin.val h).symm

/-- The codeword test is the form that builds all 64 digits, then tests the tail and the sum. -/
theorem codeword?_eq_digits (d : Digest) :
    codeword? d =
      let x := Internal.digits d
      let chains : Vector (Fin CHAIN_LENGTH) V :=
        Vector.ofFn fun i => x[i.val]'(by have := i.isLt; simp only [V, DIGITS] at *; omega)
      if (x.toList.drop V).all (·.val == 0) && Internal.digitSum chains == TARGET_SUM then
        some chains
      else none := by
  -- The 6 digits the test reads are the tail of the vector.
  have htail : (Internal.digits d).toList.drop V = (List.finRange (DIGITS - V)).map fun j =>
      Internal.digit d ⟨V + j.val, by have := j.isLt; simp only [V, DIGITS] at *; omega⟩ := by
    refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
    simp [Internal.digits, List.getElem_drop]
  simp only [codeword?, htail, List.all_map]
  split <;> simp_all [Function.comp_def]

/--
A codeword holds the digest's first 58 digits.

Its other 6 digits are zero, and it sums to `T`.
-/
theorem codeword?_eq_some (h : codeword? d = some x) :
    (∀ i : Fin V, (x[i] : Nat) = d.toNat / 4 ^ i.val % 4) ∧
      (∀ i, V ≤ i → i < DIGITS → d.toNat / 4 ^ i % 4 = 0) ∧
      Internal.digitSum x = TARGET_SUM := by
  simp only [codeword?_eq_digits] at h
  obtain ⟨hcond, hx⟩ := Option.ite_none_right_eq_some.mp h
  obtain ⟨htail, hsum⟩ := Bool.and_eq_true _ _ |>.mp hcond
  -- The accepting branch returns the first 58 digits.
  rw [← Option.some_inj.mp hx]
  refine ⟨fun i => by simp only [Fin.getElem_fin, Vector.getElem_ofFn, digits_getElem_val],
    fun i hlo hhi => ?_, beq_iff_eq.mp hsum⟩
  -- Digit `i >= 58` is entry `i - 58` of the dropped tail, which is all zero.
  rw [List.all_eq_true] at htail
  have hzero := htail (((Internal.digits d).toList.drop V)[i - V]'(by
    simp only [List.length_drop, Vector.length_toList]; omega)) (List.getElem_mem _)
  simp only [List.getElem_drop, Vector.getElem_toList, Nat.add_sub_cancel' hlo,
    digits_getElem_val, beq_iff_eq] at hzero
  exact hzero

/-! ## Digit sums -/

/-- The digit sum the specification folds is the sum over indices. -/
theorem digitSum_eq_sum (x : Vector (Fin CHAIN_LENGTH) V) :
    Internal.digitSum x = ∑ i : Fin V, (x[i] : Nat) := by
  -- A vector fold is a fold over its list.
  have h1 : x.foldl (fun sum d => sum + d.val) 0
      = x.toList.foldl (fun sum d => sum + d.val) 0 := by
    obtain ⟨arr, harr⟩ := x
    simp [Array.foldl_toList]
  -- Adding the digit values is summing the mapped list.
  have h2 : x.toList.foldl (fun sum d => sum + d.val) 0
      = (x.toList.map Fin.val).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
  -- A vector is the tabulation of its entries, so that list sum is indexed.
  have h3 : (x.toList.map Fin.val).sum = ∑ i : Fin V, (x[i] : Nat) := by
    conv_lhs => rw [← Vector.ofFn_getElem (xs := x)]
    rw [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [Internal.digitSum, h1, h2, h3]

/-- A codeword's digits sum to the target, so the verifier's step count is fixed. -/
theorem sum_of_codeword (h : codeword? d = some x) : ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
  rw [← digitSum_eq_sum]
  exact (codeword?_eq_some h).2.2

/-! ## Digits determine the digest -/

/-- A codeword's digest is the base-4 number its 58 digits spell.

```text
    LE^-1(D) = sum_{i < 58} x_i 4^i
```
-/
theorem toNat_of_codeword (h : codeword? d = some x) :
    d.toNat = ∑ i : Fin V, (x[i] : Nat) * 4 ^ i.val := by
  obtain ⟨hx, htail, -⟩ := codeword?_eq_some h
  -- Two lanes make a number below `2^128 = 4^64`, so its 64 digits spell it.
  have hlt : d.toNat < 4 ^ DIGITS := by
    have := Hash.Keccak.Lanes2.toNat_lt d
    simpa [DIGITS] using this
  have hall := Wots.sum_base_digits_eq_mod 4 (d.toNat) DIGITS
  rw [Nat.mod_eq_of_lt hlt] at hall
  -- Digits 58 to 63 are zero, so only the first 58 contribute.
  have hsplit : ∑ r ∈ Finset.range DIGITS, d.toNat / 4 ^ r % 4 * 4 ^ r
      = ∑ r ∈ Finset.range V, d.toNat / 4 ^ r % 4 * 4 ^ r := by
    rw [show DIGITS = V + (DIGITS - V) by decide, Finset.sum_range_add]
    simp only [add_eq_left]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [htail (V + r) (by omega) (by simp only [DIGITS, V] at *; omega), zero_mul]
  rw [← hall, hsplit, ← Fin.sum_univ_eq_sum_range (fun r => d.toNat / 4 ^ r % 4 * 4 ^ r)]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- No two digests share a codeword. -/
theorem eq_of_codeword (h : codeword? d = some x) (h' : codeword? d' = some x) : d = d' := by
  -- Both digests spell the same number, and two lanes are their number.
  have := (toNat_of_codeword h).trans (toNat_of_codeword h').symm
  exact Hash.Keccak.Lanes2.toNat_injective this

/-! ## Incomparability

A signature reveals chain `i` at position `x_i`.

So a signature for one codeword reaches another only if that one dominates it.

A constant digit sum rules that out. -/

/-- Two distinct codewords are incomparable: each has a digit below the other's.

Neither can be reached from the other by walking chains forward. -/
theorem codeword_incomparable (hx : codeword? d = some x) (hy : codeword? d' = some y)
    (hne : x ≠ y) :
    (∃ i : Fin V, (x[i] : Nat) < (y[i] : Nat)) ∧ (∃ i : Fin V, (y[i] : Nat) < (x[i] : Nat)) :=
  -- Both sums are the target, so they agree.
  Wots.incomparable_of_sum_eq ((sum_of_codeword hx).trans (sum_of_codeword hy).symm) hne

end EthLib.Cryptography.Xmss

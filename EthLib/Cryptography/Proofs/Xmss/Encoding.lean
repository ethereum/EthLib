import EthLib.Cryptography.Xmss.Encoding
import EthLib.Cryptography.Proofs.Xmss.Types
import Mathlib.Tactic

/-!
# Proofs: `Xmss.Encoding`

What a codeword is, and what it guarantees.

- Its 58 digits sum to the target `T = 106`.
- Its digits determine the digest: no two digests share a codeword.
- Two distinct codewords are incomparable: each has a digit below the other's.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {d d' : Digest} {x y : Vector (Fin CHAIN_LENGTH) V}

/-! ## Unfolding a codeword -/

/-- Digit `i` of a digest, as a number. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < DIGITS) :
    ((Internal.digits d)[i]'hi).val = fromLittleEndian d / 4 ^ i % 4 := by
  simp [Internal.digits, CHAIN_LENGTH]

/-- A codeword holds the digest's first 58 digits, its other 6 digits are zero, and it sums to `T`. -/
theorem codeword?_eq_some (h : codeword? d = some x) :
    (∀ i : Fin V, (x[i] : Nat) = fromLittleEndian d / 4 ^ i.val % 4) ∧
      (∀ i, V ≤ i → i < DIGITS → fromLittleEndian d / 4 ^ i % 4 = 0) ∧
      Internal.digitSum x = TARGET_SUM := by
  simp only [codeword?] at h
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

/-- The low `k` base-`b` digits of a number reconstruct it modulo `b ^ k`. -/
theorem sum_base_digits_eq_mod (b n : Nat) : ∀ k : Nat,
    ∑ r ∈ Finset.range k, n / b ^ r % b * b ^ r = n % b ^ k := by
  intro k
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    -- One more digit is one more factor of the base in the modulus.
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ring

/-- A codeword's digest is the base-4 number its 58 digits spell.

```text
    LE^-1(D) = sum_{i < 58} x_i 4^i
```
-/
theorem fromLittleEndian_of_codeword (h : codeword? d = some x) :
    fromLittleEndian d = ∑ i : Fin V, (x[i] : Nat) * 4 ^ i.val := by
  obtain ⟨hx, htail, -⟩ := codeword?_eq_some h
  -- A 16-byte number is below `256^16 = 4^64`, so its 64 digits spell it.
  have hlt : fromLittleEndian d < 4 ^ DIGITS := by
    have := fromLittleEndian_lt d
    simpa [DIGEST_LEN, DIGITS] using this
  have hall := sum_base_digits_eq_mod 4 (fromLittleEndian d) DIGITS
  rw [Nat.mod_eq_of_lt hlt] at hall
  -- Digits 58 to 63 are zero, so only the first 58 contribute.
  have hsplit : ∑ r ∈ Finset.range DIGITS, fromLittleEndian d / 4 ^ r % 4 * 4 ^ r
      = ∑ r ∈ Finset.range V, fromLittleEndian d / 4 ^ r % 4 * 4 ^ r := by
    rw [show DIGITS = V + (DIGITS - V) by decide, Finset.sum_range_add]
    simp only [add_eq_left]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [htail (V + r) (by omega) (by simp only [DIGITS, V] at *; omega), zero_mul]
  rw [← hall, hsplit, ← Fin.sum_univ_eq_sum_range (fun r => fromLittleEndian d / 4 ^ r % 4 * 4 ^ r)]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- No two digests share a codeword. -/
theorem eq_of_codeword (h : codeword? d = some x) (h' : codeword? d' = some x) : d = d' := by
  -- Both digests spell the same number, and a digest is its little-endian bytes.
  have := (fromLittleEndian_of_codeword h).trans (fromLittleEndian_of_codeword h').symm
  rw [← littleEndian_fromLittleEndian d, ← littleEndian_fromLittleEndian d', this]

/-! ## Incomparability

A signature reveals chain `i` at position `x_i`.

So a signature for one codeword reaches another only if that one dominates it.

A constant digit sum rules that out. -/

/-- Pointwise domination with equal sums forces equality. -/
theorem eq_of_le_of_sum_eq
    (hle : ∀ i : Fin V, (x[i] : Nat) ≤ (y[i] : Nat))
    (hsum : ∑ i : Fin V, (x[i] : Nat) = ∑ i : Fin V, (y[i] : Nat)) : x = y := by
  by_contra hne
  -- Unequal vectors differ at some index.
  obtain ⟨j, hj⟩ : ∃ j : Fin V, (x[j] : Nat) ≠ (y[j] : Nat) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (Vector.ext fun i hi => Fin.val_inj.mp (hall ⟨i, hi⟩))
  -- One strict index among weak ones makes the whole sum strict.
  have hlt : ∑ i : Fin V, (x[i] : Nat) < ∑ i : Fin V, (y[i] : Nat) :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hle j) hj⟩
  omega

/-- Two distinct codewords are incomparable: each has a digit below the other's.

Neither can be reached from the other by walking chains forward. -/
theorem codeword_incomparable (hx : codeword? d = some x) (hy : codeword? d' = some y)
    (hne : x ≠ y) :
    (∃ i : Fin V, (x[i] : Nat) < (y[i] : Nat)) ∧ (∃ i : Fin V, (y[i] : Nat) < (x[i] : Nat)) := by
  -- Both sums are the target, so they agree.
  have sx := sum_of_codeword hx
  have sy := sum_of_codeword hy
  constructor
  -- Were one never to exceed the other, equal sums would make them equal.
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno (sy.trans sx.symm)).symm
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno (sx.trans sy.symm))

end EthLib.Cryptography.Xmss

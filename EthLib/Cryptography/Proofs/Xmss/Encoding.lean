module

public import EthLib.Cryptography.Xmss.Encoding
public import EthLib.Cryptography.Proofs.Xmss.Types
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

/-- Digit `i` of a digest, as a number. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < DIGITS) :
    ((Internal.digits d)[i]'hi).val = bytesToUint d / 4 ^ i % 4 := by
  simp [Internal.digits, CHAIN_LENGTH]

/--
A codeword holds the digest's first 58 digits.

Its other 6 digits are zero, and it sums to `T`.
-/
theorem codeword?_eq_some (h : codeword? d = some x) :
    (∀ i : Fin V, (x[i] : Nat) = bytesToUint d / 4 ^ i.val % 4) ∧
      (∀ i, V ≤ i → i < DIGITS → bytesToUint d / 4 ^ i % 4 = 0) ∧
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

/-- A codeword's digest is the base-4 number its 58 digits spell.

```text
    LE^-1(D) = sum_{i < 58} x_i 4^i
```
-/
theorem bytesToUint_of_codeword (h : codeword? d = some x) :
    bytesToUint d = ∑ i : Fin V, (x[i] : Nat) * 4 ^ i.val := by
  obtain ⟨hx, htail, -⟩ := codeword?_eq_some h
  -- A 16-byte number is below `256^16 = 4^64`, so its 64 digits spell it.
  have hlt : bytesToUint d < 4 ^ DIGITS := by
    have := Base.bytesToUint_lt d
    simpa [DIGEST_LEN, DIGITS] using this
  have hall := Wots.sum_base_digits_eq_mod 4 (bytesToUint d) DIGITS
  rw [Nat.mod_eq_of_lt hlt] at hall
  -- Digits 58 to 63 are zero, so only the first 58 contribute.
  have hsplit : ∑ r ∈ Finset.range DIGITS, bytesToUint d / 4 ^ r % 4 * 4 ^ r
      = ∑ r ∈ Finset.range V, bytesToUint d / 4 ^ r % 4 * 4 ^ r := by
    rw [show DIGITS = V + (DIGITS - V) by decide, Finset.sum_range_add]
    simp only [add_eq_left]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [htail (V + r) (by omega) (by simp only [DIGITS, V] at *; omega), zero_mul]
  rw [← hall, hsplit, ← Fin.sum_univ_eq_sum_range (fun r => bytesToUint d / 4 ^ r % 4 * 4 ^ r)]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- No two digests share a codeword. -/
theorem eq_of_codeword (h : codeword? d = some x) (h' : codeword? d' = some x) : d = d' := by
  -- Both digests spell the same number, and a digest is its little-endian bytes.
  have := (bytesToUint_of_codeword h).trans (bytesToUint_of_codeword h').symm
  rw [← Base.uintToBytes_bytesToUint d, ← Base.uintToBytes_bytesToUint d', this]

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

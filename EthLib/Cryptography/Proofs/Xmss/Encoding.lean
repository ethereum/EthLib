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

/-- Byte `j` of a digest is base-256 digit `j` of its integer. -/
private theorem toNat_getElem_digest (d : Digest) (j : Nat) (hj : j < DIGEST_LEN) :
    (d[j]'hj).toNat = bytesToUint d / 256 ^ j % 256 := by
  conv_lhs => rw [← Base.uintToBytes_bytesToUint d]
  simp [Base.uintToBytes_eq_div]

/-- The two bits at offset `2r` of a byte are base-4 digit `4j + r` of the integer. -/
private theorem byte_digit (n j r : Nat) (hr : r < 4) :
    (n / 256 ^ j % 256) >>> (2 * r) % 4 = n / 4 ^ (4 * j + r) % 4 := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul, show (2 : Nat) ^ 2 = 4 by norm_num, pow_add, pow_mul,
    show (4 : Nat) ^ 4 = 256 by norm_num, ← Nat.div_div_eq_div_mul]
  generalize n / 256 ^ j = m
  interval_cases r <;> simp only [pow_zero, pow_one, Nat.reducePow] <;> omega

/-- Digit `i` read from its byte is base-4 digit `i` of the digest's integer. -/
theorem digit_val (d : Digest) (i : Fin DIGITS) :
    (Internal.digit d i).val = bytesToUint d / 4 ^ i.val % 4 := by
  simp only [Internal.digit, CHAIN_LENGTH]
  rw [toNat_getElem_digest, byte_digit _ _ _ (Nat.mod_lt _ (by norm_num)), Nat.div_add_mod]

/-- Digit `i` of a digest's vector of digits, as a number. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < DIGITS) :
    ((Internal.digits d)[i]'hi).val = bytesToUint d / 4 ^ i % 4 := by
  simp only [Internal.digits, Vector.getElem_ofFn, digit_val]

/-- The digits read from the bytes are the base-4 digits of the digest's integer. -/
theorem digits_eq_digits4 : Internal.digits = Wots.digits4 := by
  funext d
  refine Vector.ext fun i hi => Fin.ext ?_
  have h := Vector.getElem_ofFn (i := i) (by simpa only [DIGITS] using hi)
    (f := fun k : Fin 64 => (⟨bytesToUint d / 4 ^ k.val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4))
  rw [digits_getElem_val]
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
    (∀ i : Fin V, (x[i] : Nat) = bytesToUint d / 4 ^ i.val % 4) ∧
      (∀ i, V ≤ i → i < DIGITS → bytesToUint d / 4 ^ i % 4 = 0) ∧
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

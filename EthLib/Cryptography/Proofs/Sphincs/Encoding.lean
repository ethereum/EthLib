import EthLib.Cryptography.Sphincs.Encoding
import EthLib.Cryptography.Proofs.Xmss.Encoding

/-!
# Proofs: `Sphincs.Encoding`

What a codeword is, and what it guarantees.

- Its 64 digits sum to the target `T = 128`.
- Its digits determine the digest: no two digests share a codeword.
- Two distinct codewords are incomparable: each has a digit below the other's.
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {d d' : Digest} {x y : Codeword}

/-! ## Unfolding a codeword -/

/-- Digit `i` of a digest, as a number. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < V) :
    ((Internal.digits d)[i]'hi).val = fromLittleEndian d / 4 ^ i % 4 := by
  unfold Internal.digits
  rw [Vector.getElem_ofFn]
  -- `CHAIN_LENGTH` is 4 by definition.
  rfl

/-- A codeword holds the digest's 64 digits, and they sum to `T`. -/
theorem codeword?_eq_some (h : codeword? d = some x) :
    (∀ i : Fin V, (x[i] : Nat) = fromLittleEndian d / 4 ^ i.val % 4) ∧
      Internal.digitSum x = TARGET_SUM := by
  simp only [codeword?] at h
  obtain ⟨hsum, hx⟩ := Option.ite_none_right_eq_some.mp h
  -- The accepting branch returns the digits themselves.
  rw [← Option.some_inj.mp hx]
  exact ⟨fun i => by simp only [Fin.getElem_fin, digits_getElem_val], beq_iff_eq.mp hsum⟩

/-- A digest is a codeword exactly when its digits sum to `T`. -/
theorem codeword?_isSome_iff :
    (codeword? d).isSome ↔ Internal.digitSum (Internal.digits d) = TARGET_SUM := by
  simp only [codeword?]
  split <;> simp_all

/-! ## Digit sums -/

/-- The digit sum the specification folds is the sum over indices. -/
theorem digitSum_eq_sum (x : Codeword) : Internal.digitSum x = ∑ i : Fin V, (x[i] : Nat) := by
  -- The leanXMSS fold is the same fold, over a vector of the same digits.
  obtain ⟨arr, harr⟩ := x
  -- A vector fold is a fold over its list.
  have h1 : (⟨arr, harr⟩ : Codeword).foldl (fun sum d => sum + d.val) 0
      = arr.toList.foldl (fun sum d => sum + d.val) 0 := by
    simp [Array.foldl_toList]
  -- Adding the digit values is summing the mapped list.
  have h2 : arr.toList.foldl (fun sum (d : Fin CHAIN_LENGTH) => sum + d.val) 0
      = (arr.toList.map Fin.val).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
  -- A vector is the tabulation of its entries, so that list sum is indexed.
  have h3 : (arr.toList.map Fin.val).sum = ∑ i : Fin V, ((⟨arr, harr⟩ : Codeword)[i] : Nat) := by
    have := Vector.ofFn_getElem (xs := (⟨arr, harr⟩ : Codeword))
    conv_lhs => rw [show arr.toList = (⟨arr, harr⟩ : Codeword).toList from rfl, ← this]
    rw [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn]
    rfl
  rw [Internal.digitSum, h1, h2, h3]

/-- A codeword's digits sum to the target, so the verifier's step count is fixed. -/
theorem sum_of_codeword (h : codeword? d = some x) : ∑ i : Fin V, (x[i] : Nat) = TARGET_SUM := by
  rw [← digitSum_eq_sum]
  exact (codeword?_eq_some h).2

/-! ## Digits determine the digest -/

/-- A codeword's digest is the base-4 number its 64 digits spell.

```text
    LE^-1(D) = sum_{i < 64} x_i 4^i
```
-/
theorem fromLittleEndian_of_codeword (h : codeword? d = some x) :
    fromLittleEndian d = ∑ i : Fin V, (x[i] : Nat) * 4 ^ i.val := by
  obtain ⟨hx, -⟩ := codeword?_eq_some h
  -- A 16-byte number is below `256^16 = 4^64`, so its 64 digits spell it.
  have hlt : fromLittleEndian d < 4 ^ V := by
    have := Xmss.fromLittleEndian_lt d
    simpa [N, V] using this
  have hall := Xmss.sum_base_digits_eq_mod 4 (fromLittleEndian d) V
  rw [Nat.mod_eq_of_lt hlt] at hall
  rw [← hall, ← Fin.sum_univ_eq_sum_range (fun r => fromLittleEndian d / 4 ^ r % 4 * 4 ^ r)]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- No two digests share a codeword. -/
theorem eq_of_codeword (h : codeword? d = some x) (h' : codeword? d' = some x) : d = d' := by
  -- Both digests spell the same number, and a digest is its little-endian bytes.
  have := (fromLittleEndian_of_codeword h).trans (fromLittleEndian_of_codeword h').symm
  rw [← Xmss.littleEndian_fromLittleEndian d, ← Xmss.littleEndian_fromLittleEndian d', this]

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

end EthLib.Cryptography.Sphincs

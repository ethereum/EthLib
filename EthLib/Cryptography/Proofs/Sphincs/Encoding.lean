module

public import EthLib.Cryptography.Sphincs.Encoding
public import EthLib.Cryptography.Proofs.Wots.TargetSum

/-!
# Proofs: the WOTS+C target-sum code

What a codeword is, and what it guarantees.

- Its 64 digits sum to the target `T = 128`.
- Its digits determine the digest: no two digests share a codeword.
- Two distinct codewords are incomparable: each has a digit below the other's.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {d d' : Digest} {x y : Codeword}

/-! ## Unfolding a codeword -/

/-- Digit `i` of a digest, as a number. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < V) :
    ((Internal.digits d)[i]'hi).val = bytesToUint d / 4 ^ i % 4 := by
  unfold Internal.digits
  rw [Vector.getElem_ofFn]
  -- The chain length is 4 by definition.
  rfl

/-- A codeword holds the digest's 64 digits, and they sum to `T`. -/
theorem codeword?_eq_some (h : codeword? d = some x) :
    (∀ i : Fin V, (x[i] : Nat) = bytesToUint d / 4 ^ i.val % 4) ∧
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
  obtain ⟨arr, harr⟩ := x
  -- A vector fold is a fold over its list.
  have h1 : (⟨arr, harr⟩ : Codeword).foldl (fun sum d => sum + d.val) 0
      = arr.toList.foldl (fun sum d => sum + d.val) 0 := by
    simp [Array.foldl_toList]
  -- The sum of the digit values is the sum of the mapped list.
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
theorem bytesToUint_of_codeword (h : codeword? d = some x) :
    bytesToUint d = ∑ i : Fin V, (x[i] : Nat) * 4 ^ i.val := by
  obtain ⟨hx, -⟩ := codeword?_eq_some h
  -- A 16-byte number is below `256^16 = 4^64`, so its 64 digits spell it.
  have hlt : bytesToUint d < 4 ^ V := by
    have := Base.bytesToUint_lt d
    simpa [N, V] using this
  have hall := Wots.sum_base_digits_eq_mod 4 (bytesToUint d) V
  rw [Nat.mod_eq_of_lt hlt] at hall
  rw [← hall, ← Fin.sum_univ_eq_sum_range (fun r => bytesToUint d / 4 ^ r % 4 * 4 ^ r)]
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

end EthLib.Cryptography.Sphincs

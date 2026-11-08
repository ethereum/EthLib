module

public import EthLib.Cryptography.Sphincs.Encoding
public import EthLib.Base.Proofs.BigEndian
public import EthLib.Cryptography.Proofs.Wots.TargetSum

/-!
# Proofs: the WOTS+C target-sum code

What a codeword is, and what it guarantees.

- Digit `i` of a digest is digit `63 - i` of its big-endian number in base 4, as `base_2b` reads it.
- Every string of 64 digits from 0 to 3 is the digits of exactly one digest.
- A codeword's 64 digits sum to the target `T = 128`.
- Its digits determine the digest: no two digests share a codeword.
- Two distinct codewords are incomparable: each has a digit below the other's.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

variable {d d' : Digest} {x y : Codeword}

/-! ## The bytes of a big-endian number -/

/-- Byte `j` of `k` bytes is digit `k - 1 - j` of their big-endian number, in base 256. -/
theorem toInt_div_pow_mod {k : Nat} (v : Vector UInt8 k) (j : Nat) (hj : j < k) :
    toInt v / 256 ^ (k - 1 - j) % 256 = (v[j]'hj).toNat := by
  -- Split the bytes into those before byte `j`, byte `j`, and those after it.
  have hlen : v.toList.length = k := v.length_toList
  have hsplit : v.toList = v.toList.take j ++ v[j] :: v.toList.drop (j + 1) := by
    rw [← Vector.getElem_toList (h := by omega),
      ← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  have hrest : (v.toList.drop (j + 1)).length = k - 1 - j := by
    rw [List.length_drop, hlen]
    omega
  have hlow := Base.bytesToNat_lt (v.toList.drop (j + 1))
  rw [hrest] at hlow
  have hval : toInt v = (Base.bytesToNat (v.toList.take j) * 256 + (v[j]'hj).toNat)
      * 256 ^ (k - 1 - j) + Base.bytesToNat (v.toList.drop (j + 1)) := by
    rw [toInt]
    conv_lhs => rw [hsplit]
    rw [Base.bytesToNat_append, Base.bytesToNat_cons, List.length_cons, hrest]
    ring
  -- The bytes after byte `j` are worth less than one unit of it.
  rw [hval, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero (by positivity)),
    Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hb := (v[j]'hj).toNat_lt
  omega

/-- Two bits of a byte, read from the number whose low byte it is. -/
private theorem digit_of_mod (X b r : Nat) (hb : X % 256 = b) (hr : r < 4) :
    X / 2 ^ (6 - 2 * r) % 4 = (b >>> (6 - 2 * r)) % 4 := by
  rw [Nat.shiftRight_eq_div_pow]
  -- The two bits sit below bit 8, so the higher bytes of `X` do not reach them.
  interval_cases r <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub] <;> omega

/-! ## Unfolding a codeword -/

/-- Digit `i` of a digest is two bits of byte `floor(i / 4)`, the top two for `i mod 4 = 0`. -/
@[simp] theorem digits_getElem_val (d : Digest) (i : Nat) (hi : i < V) :
    ((Internal.digits d)[i]'hi).val
      = ((d[i / 4]'(by simp only [V, N] at *; omega)).toNat >>> (6 - 2 * (i % 4))) % 4 := by
  unfold Internal.digits
  rw [Vector.getElem_ofFn]

/-- Digit `i` of a digest is digit `63 - i` of its big-endian number in base 4.

So the digits are the number's, most significant first, as FIPS 205's `base_2b` writes them. -/
theorem digits_getElem_val_toInt (d : Digest) (i : Nat) (hi : i < V) :
    ((Internal.digits d)[i]'hi).val = toInt d / 4 ^ (V - 1 - i) % 4 := by
  have hj : i / 4 < N := by simp only [V, N] at *; omega
  -- Digit `63 - i` in base 4 is two bits of digit `15 - floor(i / 4)` in base 256.
  have hpow : (4 : Nat) ^ (V - 1 - i) = 256 ^ (N - 1 - i / 4) * 2 ^ (6 - 2 * (i % 4)) := by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul, ← pow_mul,
      ← pow_add]
    congr 1
    simp only [V, N] at *
    omega
  rw [digits_getElem_val, hpow, ← Nat.div_div_eq_div_mul]
  exact (digit_of_mod _ _ _ (toInt_div_pow_mod d (i / 4) hj) (Nat.mod_lt _ (by decide))).symm

/-- Digit `i` of a digest is two bits of its little-endian number.

They are bit `8 floor(i / 4) + 6 - 2 (i mod 4)` and the bit above it. -/
theorem digits_getElem_val_bytesToUint (d : Digest) (i : Nat) (hi : i < V) :
    ((Internal.digits d)[i]'hi).val
      = Base.bytesToUint d / 2 ^ (8 * (i / 4) + 6 - 2 * (i % 4)) % 4 := by
  have hj : i / 4 < N := by simp only [V, N] at *; omega
  -- Byte `j` of a little-endian number is its digit `j` in base 256.
  have hbyte : Base.bytesToUint d / 256 ^ (i / 4) % 256 = (d[i / 4]'hj).toNat := by
    have h := congrArg (fun v : Digest => (v[i / 4]'hj).toNat) (Base.uintToBytes_bytesToUint d)
    simp only [Base.uintToBytes, Vector.getElem_ofFn] at h
    exact h
  have hpow : (2 : Nat) ^ (8 * (i / 4) + 6 - 2 * (i % 4))
      = 256 ^ (i / 4) * 2 ^ (6 - 2 * (i % 4)) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [digits_getElem_val, hpow, ← Nat.div_div_eq_div_mul]
  exact (digit_of_mod _ _ _ hbyte (Nat.mod_lt _ (by decide))).symm

/-! ## Digits determine the digest -/

/-- A digest's big-endian number is the base-4 number its 64 digits spell, digit 0 on top.

```text
    toInt(D) = sum_{i < 64} x_i 4^(63 - i)
```
-/
theorem toInt_eq_sum_digits (d : Digest) :
    toInt d = ∑ i : Fin V, ((Internal.digits d)[i] : Nat) * 4 ^ (V - 1 - i.val) := by
  -- A 16-byte number is below `256^16 = 4^64`, so its 64 digits spell it.
  have hlt : toInt d < 4 ^ V := by
    have h := Base.bytesToNat_lt d.toList
    rw [Vector.length_toList] at h
    exact lt_of_lt_of_eq h (by norm_num [N, V])
  have hall := Wots.sum_base_digits_eq_mod 4 (toInt d) V
  rw [Nat.mod_eq_of_lt hlt] at hall
  -- Count the digits from the top: digit `i` is the one of weight `4^(63 - i)`.
  rw [← Finset.sum_range_reflect] at hall
  rw [← Fin.sum_univ_eq_sum_range (fun r => toInt d / 4 ^ (V - 1 - r) % 4 * 4 ^ (V - 1 - r))]
    at hall
  rw [← hall]
  exact Finset.sum_congr rfl fun i _ => by rw [Fin.getElem_fin, digits_getElem_val_toInt]

/-- Distinct digests have distinct digits. -/
theorem digits_injective : Function.Injective Internal.digits := by
  intro d d' h
  -- Both digests write the same number on 16 bytes.
  have hval : toInt d = toInt d' := by rw [toInt_eq_sum_digits d, toInt_eq_sum_digits d', h]
  exact Vector.toList_inj.mp
    (Base.bytesToNat_inj (by simp only [Vector.length_toList]) hval)

/-- Every string of 64 digits from 0 to 3 is the digits of exactly one digest. -/
theorem digits_bijective : Function.Bijective Internal.digits := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨digits_injective, ?_⟩
  -- Both sides have `2^128 = 4^64` elements.
  rw [show Fintype.card Digest = 2 ^ 128 from Wots.card_bytes16,
    Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  norm_num [V, CHAIN_LENGTH]

/-! ## Codewords -/

/-- A digest is the codeword `x` exactly when `x` is its digits and they sum to `T`. -/
theorem codeword?_eq_some_iff :
    codeword? d = some x ↔ Internal.digits d = x ∧ Internal.digitSum x = TARGET_SUM := by
  simp only [codeword?]
  constructor
  · intro h
    obtain ⟨hsum, hx⟩ := Option.ite_none_right_eq_some.mp h
    -- The accepting branch returns the digits themselves.
    rw [← Option.some_inj.mp hx]
    exact ⟨rfl, beq_iff_eq.mp hsum⟩
  · rintro ⟨rfl, hsum⟩
    simp [hsum]

/-- A codeword holds the digest's 64 digits, most significant first, and they sum to `T`. -/
theorem codeword?_eq_some (h : codeword? d = some x) :
    (∀ i : Fin V, (x[i] : Nat) = toInt d / 4 ^ (V - 1 - i.val) % 4) ∧
      Internal.digitSum x = TARGET_SUM := by
  obtain ⟨rfl, hsum⟩ := codeword?_eq_some_iff.mp h
  exact ⟨fun i => by rw [Fin.getElem_fin, digits_getElem_val_toInt], hsum⟩

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

/-! ## A codeword determines its digest -/

/-- A codeword's digest writes the base-4 number its 64 digits spell, digit 0 on top.

```text
    toInt(D) = sum_{i < 64} x_i 4^(63 - i)
```
-/
theorem toInt_of_codeword (h : codeword? d = some x) :
    toInt d = ∑ i : Fin V, (x[i] : Nat) * 4 ^ (V - 1 - i.val) := by
  obtain ⟨rfl, -⟩ := codeword?_eq_some_iff.mp h
  exact toInt_eq_sum_digits d

/-- No two digests share a codeword. -/
theorem eq_of_codeword (h : codeword? d = some x) (h' : codeword? d' = some x) : d = d' :=
  -- Both digests have the digits `x`, and the digits determine the digest.
  digits_injective ((codeword?_eq_some_iff.mp h).1.trans (codeword?_eq_some_iff.mp h').1.symm)

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

import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Bytes
import EthLib.Cryptography.Proofs.Xmss.Encoding
import EthLib.Cryptography.Proofs.Xmss.Security.LeanXmss.Code

/-!
# Proofs: EthLib's codewords are the security proof's

A digest's digits are the base-4 digits of the integer its bytes encode, in both.

So a digest is a codeword for EthLib exactly when its bit vector is one for the proof.

The two then have the same digits.

The randomizer trials agree too.

EthLib adds `c` to the base's integer, and the proof adds it to the bit vector, both modulo `2^128`.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- The integer the bytes of a bit vector encode is the bit vector's. -/
theorem fromLittleEndian_ofBV (n : Nat) (x : BitVec (8 * n)) :
    fromLittleEndian (ofBV n x) = x.toNat := by
  rw [ofBV_eq_littleEndian, fromLittleEndian_littleEndian]
  -- The integer is below `2^(8n) = 256^n`, so the modulus does nothing.
  exact Nat.mod_eq_of_lt (by simpa [pow_mul] using x.isLt)

/-- A digest's integer is its bit vector's. -/
@[simp] theorem fromLittleEndian_ofDigest (x : LeanXmss.Digest) :
    fromLittleEndian (ofDigest x) = x.toNat :=
  fromLittleEndian_ofBV 16 x

/-- A randomizer's integer is its bit vector's. -/
@[simp] theorem fromLittleEndian_ofRandomizer (x : LeanXmss.Randomness) :
    fromLittleEndian (ofRandomizer x) = x.toNat :=
  fromLittleEndian_ofBV 16 x

/-! ## The six digits without a chain -/

/-- The 6 digits above the 58 chains are zero exactly when the integer is below `4^58 = 2^116`. -/
private theorem tail_zero_iff (z : Nat) (hz : z < 2 ^ 128) :
    (∀ i, V ≤ i → i < DIGITS → z / 4 ^ i % 4 = 0) ↔ z / 2 ^ (2 * 58) = 0 := by
  simp only [V, DIGITS]
  have h4 : (2 : Nat) ^ (2 * 58) = 4 ^ 58 := by rw [pow_mul]; norm_num
  rw [h4]
  constructor
  · intro h
    -- `z / 4^58` is below `4^6`, so it is the sum of its six base-4 digits, all zero.
    have hlt : z / 4 ^ 58 < 4 ^ 6 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc z < 2 ^ 128 := hz
        _ = 4 ^ 6 * 4 ^ 58 := by norm_num
    rw [← LeanXmss.Codeword.sum_digits_eq 4 (by decide) 6 _ hlt]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.div_div_eq_div_mul, ← pow_add, h (58 + j) (by omega) (by omega), zero_mul]
  · intro h i hi _
    -- Every digit above position 58 is a digit of `z / 4^58 = 0`.
    have : z / 4 ^ i = z / 4 ^ 58 / 4 ^ (i - 58) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_cancel' hi]
    rw [this, h, Nat.zero_div, Nat.zero_mod]

/-! ## Codewords -/

/-- A chain as the proof numbers it. -/
def chainOf (i : Fin V) : LeanXmss.ChainIndex := ⟨i.val, i.isLt⟩

/-- The proof's codeword, as EthLib's vector of 58 digits. -/
def ofEncoding (enc : LeanXmss.Encoding) : Vector (Fin CHAIN_LENGTH) V :=
  Vector.ofFn fun i => ⟨(enc (chainOf i)).val, (enc (chainOf i)).isLt⟩

/-- EthLib's codeword of a digest is the proof's, its digits as a vector. -/
theorem codeword?_ofDigest (x : LeanXmss.Digest) :
    codeword? (ofDigest x) = (LeanXmss.Codeword.decode x).map ofEncoding := by
  -- The 58 chain digits are the proof's encoding.
  have hchains : (Vector.ofFn fun i : Fin V => (Internal.digits (ofDigest x))[i.val]'(by
      have := i.isLt; simp only [V, DIGITS] at *; omega))
      = ofEncoding (LeanXmss.Codeword.encoding x) := by
    refine congrArg Vector.ofFn (funext fun i => Fin.ext ?_)
    rw [digits_getElem_val, fromLittleEndian_ofDigest]
    exact (LeanXmss.Codeword.digit_val x i.val).symm
  -- The six digits without a chain are zero exactly when the proof's high bits are.
  have htail : ((Internal.digits (ofDigest x)).toList.drop V).all (·.val == 0) = true ↔
      x.toNat / 2 ^ (LeanXmss.winternitzBits * LeanXmss.numChains) = 0 := by
    simp only [LeanXmss.winternitzBits, LeanXmss.numChains]
    rw [← tail_zero_iff x.toNat (by have := x.isLt; simpa [LeanXmss.digestBits] using this),
      List.all_eq_true]
    constructor
    · intro h i hlo hhi
      have := h (((Internal.digits (ofDigest x)).toList.drop V)[i - V]'(by
        simp only [List.length_drop, Vector.length_toList]; omega)) (List.getElem_mem _)
      simp only [List.getElem_drop, Vector.getElem_toList, Nat.add_sub_cancel' hlo,
        digits_getElem_val, fromLittleEndian_ofDigest, beq_iff_eq] at this
      exact this
    · intro h d hd
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      simp only [List.length_drop, Vector.length_toList] at hk
      simp only [List.getElem_drop, Vector.getElem_toList, digits_getElem_val,
        fromLittleEndian_ofDigest, beq_iff_eq]
      exact h (V + k) (by omega) (by simp only [V, DIGITS] at *; omega)
  -- The digit sums agree.
  have hsum : Internal.digitSum (ofEncoding (LeanXmss.Codeword.encoding x))
      = LeanXmss.Codeword.sum (LeanXmss.Codeword.encoding x) := by
    -- `rewrite`, not `rw`: closing the goal by `rfl` would unfold both sums.
    rewrite [digitSum_eq_sum, LeanXmss.Codeword.sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [ofEncoding, Fin.getElem_fin, Vector.getElem_ofFn]
      rfl
  -- EthLib's condition is the proof's `Valid`.
  have hcond : ((((Internal.digits (ofDigest x)).toList.drop V).all (·.val == 0) &&
      Internal.digitSum (ofEncoding (LeanXmss.Codeword.encoding x)) == TARGET_SUM) = true) ↔
      LeanXmss.Codeword.Valid x := by
    rw [Bool.and_eq_true, htail, beq_iff_eq, hsum, LeanXmss.Codeword.Valid]
    simp only [TARGET_SUM, LeanXmss.targetSum]
  unfold codeword?
  dsimp only
  rw [hchains, LeanXmss.Codeword.decode]
  split
  · rename_i h
    simp only [hcond.mp h, ↓reduceIte, Option.map_some]
  · rename_i h
    simp only [show ¬LeanXmss.Codeword.Valid x from fun hv => h (hcond.mpr hv), ↓reduceIte,
      Option.map_none]

/-! ## Randomizer trials -/

/-- Trial `c` of EthLib is the proof's `R0 + c`, as bytes. -/
theorem trialRandomizer_ofRandomizer (base : LeanXmss.Randomness) (c : Nat) :
    trialRandomizer (ofRandomizer base) c
      = ofRandomizer (base + BitVec.ofNat LeanXmss.digestBits c) := by
  -- Both sides are the bytes of `(R0 + c) mod 2^128`.
  show _ = ofBV RANDOMIZER_LEN _
  rw [trialRandomizer, fromLittleEndian_ofRandomizer, ofBV_eq_littleEndian, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  congr 1
  simp only [LeanXmss.digestBits]
  omega

end EthLib.Cryptography.Xmss.Unforgeability

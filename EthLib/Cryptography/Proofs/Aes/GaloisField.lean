module

public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Base.Proofs.BigEndian
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.ComputeDegree

/-!
# Proofs: the product of GCM blocks

SP 800-38D §6.3 reads a block `x_0 x_1 ... x_127` as a polynomial over GF(2).

The polynomial is `x_0 + x_1 u + ... + x_127 u^127`.

The reduction modulus is `1 + u + u^2 + u^7 + u^128`, the polynomial of `R || 1`.

- The product of two blocks by Algorithm 1 is the product of their residues modulo the modulus.
- The XOR of two blocks is the sum of their residues.
- Two different blocks have two different residues.
- One step of GHASH, §6.4, adds a block and multiplies by `H` in the same ring.
- So GHASH of `X_1 ... X_m` is `X_1 H^m + ... + X_m H` on residues, as §6.4 states.

The section calls this ring the field of `2^128` elements.

No theorem here proves that the modulus is irreducible, so none proves that the ring is a field.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

open Polynomial

/-- The reduction modulus `1 + u + u^2 + u^7 + u^128` of SP 800-38D §6.3. -/
noncomputable def modulus : (ZMod 2)[X] := X ^ 128 + X ^ 7 + X ^ 2 + X + 1

/-- The polynomial of a 128-bit integer.

Bit `x_i` of a block is bit `127 - i` of its integer, by §6.1.

It is the coefficient of `u^i`. -/
noncomputable def polyOfNat (n : Nat) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 128, if n.testBit (127 - i) then X ^ i else 0

/-- The residue of a block modulo the modulus, as §6.3 reads it. -/
noncomputable def residue (A : Block) : AdjoinRoot modulus :=
  AdjoinRoot.mk modulus (polyOfNat (blockToNat A))

/-! ## The polynomial of an integer -/

/-- The coefficient of `u^k` is bit `127 - k`, for `k < 128`, and 0 above. -/
theorem coeff_polyOfNat (n k : Nat) :
    (polyOfNat n).coeff k = if k < 128 ∧ n.testBit (127 - k) = true then 1 else 0 := by
  simp only [polyOfNat, finsetSum_coeff, apply_ite (fun p : (ZMod 2)[X] => p.coeff k),
    coeff_X_pow, coeff_zero]
  by_cases hk : k < 128
  · -- Only the term `i = k` of the sum reaches `u^k`.
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)]
    · simp [hk]
    · intro i _ hik
      simp [Ne.symm hik]
  · -- Every term is a power below `u^128`.
    rw [Finset.sum_eq_zero]
    · simp [hk]
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp [show k ≠ i by omega]

/-- XOR adds the polynomials, since the coefficients lie in GF(2). -/
theorem polyOfNat_xor (a b : Nat) : polyOfNat (a ^^^ b) = polyOfNat a + polyOfNat b := by
  ext k
  simp only [coeff_add, coeff_polyOfNat, Nat.testBit_xor]
  by_cases hk : k < 128
  · cases a.testBit (127 - k) <;> cases b.testBit (127 - k) <;> simp [hk]; decide
  · simp [hk]

/-- Halving moves each coefficient up one power of `u`, and the last one out to `u^128`. -/
theorem X_mul_polyOfNat {v : Nat} (hv : v < 2 ^ 128) :
    X * polyOfNat v = polyOfNat (v / 2) + if v.testBit 0 then X ^ 128 else 0 := by
  ext k
  rcases k with _ | k
  · -- Below `2^128`, bit 128 is clear, so `v / 2` has no constant coefficient.
    have h128 : v.testBit 128 = false := Nat.testBit_lt_two_pow hv
    simp [coeff_polyOfNat, Nat.testBit_div_two, h128, apply_ite (fun p : (ZMod 2)[X] => p.coeff 0)]
  · rw [coeff_X_mul, coeff_add, coeff_polyOfNat, coeff_polyOfNat, Nat.testBit_div_two,
      apply_ite (fun p : (ZMod 2)[X] => p.coeff (k + 1)), coeff_X_pow, coeff_zero]
    by_cases hk : k < 127
    · rw [show 127 - (k + 1) + 1 = 127 - k by omega]
      simp [show k < 128 by omega, show k + 1 < 128 by omega, show k + 1 ≠ 128 by omega]
    · by_cases h127 : k = 127
      · subst h127
        cases v.testBit 0 <;> simp
      · simp [show ¬ k < 128 by omega, show ¬ k + 1 < 128 by omega,
          show k + 1 ≠ 128 by omega]

/-- The polynomial of `R` is `1 + u + u^2 + u^7`. -/
theorem polyOfNat_R : polyOfNat R = X ^ 7 + X ^ 2 + X + 1 := by
  -- Of the first 128 coefficients, those of `1`, `u`, `u^2` and `u^7` are set.
  have bits : ∀ k < 128, R.testBit (127 - k) = (k = 0 || k = 1 || k = 2 || k = 7) := by
    decide +kernel
  ext k
  rw [coeff_polyOfNat]
  by_cases hk : k < 128
  · rw [bits k hk]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 7 ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 7) := by omega
    rcases cases with rfl | rfl | rfl | rfl | ⟨h0, h1, h2, h7⟩
    · simp
    · simp
    · simp
    · simp
    · simp [h0, h1, h2, h7, Ne.symm h1]
  · simp only [hk, false_and, ↓reduceIte, coeff_add, coeff_X_pow, coeff_X, coeff_one]
    simp [show k ≠ 7 by omega, show k ≠ 2 by omega, show k ≠ 0 by omega,
      show (1 : Nat) ≠ k by omega]

/-- The polynomial of an integer has degree below 128. -/
theorem degree_polyOfNat_lt (n : Nat) : (polyOfNat n).degree < 128 := by
  rw [show (128 : WithBot Nat) = ((128 : Nat) : WithBot Nat) from rfl, degree_lt_iff_coeff_zero]
  intro m hm
  simp [coeff_polyOfNat, show ¬ m < 128 by omega]

/-- Two integers below `2^128` with the same polynomial are equal. -/
theorem polyOfNat_injOn {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : polyOfNat a = polyOfNat b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 128
  · -- Bit `i` is the coefficient of `u^(127 - i)`.
    have hc := congrArg (fun p => p.coeff (127 - i)) h
    simp only [coeff_polyOfNat, show 127 - i < 128 by omega, true_and,
      show 127 - (127 - i) = i by omega] at hc
    cases hai : a.testBit i <;> cases hbi : b.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))]

/-! ## Residues -/

/-- The modulus has degree 128. -/
theorem degree_modulus : modulus.degree = 128 := by
  unfold modulus
  compute_degree!

/-- `u^128` is `1 + u + u^2 + u^7` modulo the modulus. -/
theorem mk_X_pow_128 : AdjoinRoot.mk modulus (X ^ 128) = AdjoinRoot.mk modulus (polyOfNat R) := by
  rw [polyOfNat_R, AdjoinRoot.mk_eq_mk]
  -- The difference is the modulus itself, since `-1 = 1` in GF(2).
  refine ⟨1, ?_⟩
  rw [mul_one, modulus, CharTwo.sub_eq_add]
  ring

/-- One step of `V` in Algorithm 1 multiplies its residue by `u`. -/
theorem mk_polyOfNat_step {v : Nat} (hv : v < 2 ^ 128) :
    AdjoinRoot.mk modulus (polyOfNat (if v % 2 = 0 then v / 2 else v / 2 ^^^ R))
      = AdjoinRoot.mk modulus (polyOfNat v) * AdjoinRoot.root modulus := by
  rw [mul_comm, ← AdjoinRoot.mk_X, ← map_mul, X_mul_polyOfNat hv]
  have hbit : v.testBit 0 = decide (v % 2 = 1) := by
    simp [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : v % 2 = 0
  · simp [h, hbit]
  · simp [hbit, show v % 2 = 1 by omega, polyOfNat_xor, map_add, mk_X_pow_128]

/-! ## Blocks as integers -/

/-- A block is worth less than `2^128`. -/
theorem blockToNat_lt (A : Block) : blockToNat A < 2 ^ 128 := by
  have h := Base.bytesToNat_lt A.toList
  rw [Vector.length_toList] at h
  exact lt_of_lt_of_eq h (by norm_num)

/-- Two blocks with the same integer are equal. -/
theorem blockToNat_injective : Function.Injective blockToNat := by
  intro A B h
  exact Vector.toList_inj.mp (Base.bytesToNat_inj (by simp) h)

/-- The bytes `z / 256^(n - 1 - i)`, for `i < n`, are `z` written on `n` bytes. -/
private theorem ofFn_toUInt8_eq_natToBytes (n z : Nat) :
    List.ofFn (fun i : Fin n => (z / 256 ^ (n - 1 - i.val)).toUInt8) = Base.natToBytes n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    -- The last byte is `z mod 256`, and the bytes before it write `z / 256`.
    rw [List.ofFn_succ_last, Base.natToBytes_succ, ← ih (z / 256)]
    congr 1
    · apply List.ofFn_inj.mpr
      funext i
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      simp only [Fin.val_castSucc]
      omega
    · simp only [Fin.val_last, List.cons.injEq, and_true]
      apply UInt8.toNat_inj.mp
      simp [Nat.toUInt8_eq]

/-- An integer below `2^128` survives the round trip through a block. -/
theorem blockToNat_blockOfNat {z : Nat} (hz : z < 2 ^ 128) : blockToNat (blockOfNat z) = z := by
  have h := ofFn_toUInt8_eq_natToBytes 16 z
  simp only [show ∀ i : Fin 16, 16 - 1 - i.val = 15 - i.val from fun _ => rfl] at h
  rw [blockToNat, blockOfNat, Vector.toList_ofFn, h]
  exact Base.bytesToNat_natToBytes_of_lt (lt_of_lt_of_eq hz (by norm_num))

/-- The XOR of two numbers, each split at bit `k`, is the XOR of each part. -/
private theorem xor_two_pow_mul_add {p q r s k : Nat} (hr : r < 2 ^ k) (hs : s < 2 ^ k) :
    (2 ^ k * p + r) ^^^ (2 ^ k * q + s) = 2 ^ k * (p ^^^ q) + (r ^^^ s) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hr, Nat.testBit_two_pow_mul_add _ hs,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hr hs)]
  split <;> simp [Nat.testBit_xor]

/-- XOR on bytes of one length is XOR on the numbers they write. -/
private theorem bytesToNat_zipWith_xor {a b : List UInt8} (h : a.length = b.length) :
    Base.bytesToNat (List.zipWith (· ^^^ ·) a b) = Base.bytesToNat a ^^^ Base.bytesToNat b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have ha := Base.bytesToNat_lt a
      have hb := Base.bytesToNat_lt b
      rw [h] at ha
      have hpow : (256 : Nat) ^ b.length = 2 ^ (8 * b.length) := by rw [Nat.pow_mul]
      rw [hpow] at ha hb
      -- The first byte sits above `8 * length` bits, where both rests stay below.
      rw [List.zipWith_cons_cons, Base.bytesToNat_cons, Base.bytesToNat_cons, Base.bytesToNat_cons,
        List.length_zipWith, h, Nat.min_self, ih h, UInt8.toNat_xor, hpow, Nat.mul_comm x.toNat,
        Nat.mul_comm y.toNat, Nat.mul_comm _ (2 ^ _)]
      exact (xor_two_pow_mul_add ha hb).symm

/-- The integer of the XOR of two blocks is the XOR of their integers. -/
theorem blockToNat_xorBlock (A B : Block) :
    blockToNat (xorBlock A B) = blockToNat A ^^^ blockToNat B := by
  simp only [blockToNat, xorBlock, Vector.toList_zipWith]
  exact bytesToNat_zipWith_xor (by simp)

/-! ## The ring of blocks -/

/-- Two different blocks have two different residues. -/
theorem residue_injective : Function.Injective residue := by
  intro A B h
  rw [residue, residue, AdjoinRoot.mk_eq_mk] at h
  -- A multiple of the modulus of degree below 128 is zero.
  have hdeg : (polyOfNat (blockToNat A) - polyOfNat (blockToNat B)).degree < modulus.degree := by
    rw [degree_modulus]
    exact lt_of_le_of_lt (degree_sub_le _ _)
      (max_lt (degree_polyOfNat_lt _) (degree_polyOfNat_lt _))
  have h0 := Polynomial.eq_zero_of_dvd_of_degree_lt h hdeg
  exact blockToNat_injective
    (polyOfNat_injOn (blockToNat_lt A) (blockToNat_lt B) (sub_eq_zero.mp h0))

/-- The XOR of two blocks is the sum of their residues. -/
theorem residue_xorBlock (A B : Block) : residue (xorBlock A B) = residue A + residue B := by
  rw [residue, blockToNat_xorBlock, polyOfNat_xor, map_add]
  rfl

/-- The residue of `x_i u^i`, the term of bit `x_i` of an integer. -/
noncomputable def bitTerm (x i : Nat) : AdjoinRoot modulus :=
  if x.testBit (127 - i) then AdjoinRoot.root modulus ^ i else 0

/-- The residue of an integer is the sum of the terms of its bits. -/
theorem mk_polyOfNat (x : Nat) :
    AdjoinRoot.mk modulus (polyOfNat x) = ∑ i ∈ Finset.range 128, bitTerm x i := by
  simp only [polyOfNat, map_sum, bitTerm, apply_ite (AdjoinRoot.mk modulus), map_pow,
    AdjoinRoot.mk_X, map_zero]

/-- After `n` steps of Algorithm 1, `V_n = u^n Y` and `Z_n = (x_0 + ... + x_(n-1) u^(n-1)) Y`.

Both stay below `2^128`. -/
theorem mul_loop_spec (x y : Nat) (hy : y < 2 ^ 128) (n : Nat) :
    let zv := (List.range n).foldl (fun (zv : Nat × Nat) (i : Nat) =>
      let z := if (x / 2 ^ (127 - i)) % 2 = 1 then zv.1 ^^^ zv.2 else zv.1
      let v := if zv.2 % 2 = 0 then zv.2 / 2 else zv.2 / 2 ^^^ R
      (z, v)) (0, y)
    zv.1 < 2 ^ 128 ∧ zv.2 < 2 ^ 128 ∧
      AdjoinRoot.mk modulus (polyOfNat zv.2)
        = AdjoinRoot.root modulus ^ n * AdjoinRoot.mk modulus (polyOfNat y) ∧
      AdjoinRoot.mk modulus (polyOfNat zv.1)
        = (∑ i ∈ Finset.range n, bitTerm x i) * AdjoinRoot.mk modulus (polyOfNat y) := by
  induction n with
  | zero =>
    -- `Z_0 = 0` and `V_0 = Y`.
    refine ⟨by simp, hy, by simp, ?_⟩
    have h0 : polyOfNat 0 = 0 := by simp [polyOfNat]
    simp [h0]
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl _ (0, y) = zv at ih ⊢
    obtain ⟨hz, hv, hV, hZ⟩ := ih
    have hR : R < 2 ^ 128 := by unfold R; norm_num
    refine ⟨?_, ?_, ?_, ?_⟩
    · split
      · exact Nat.xor_lt_two_pow hz hv
      · exact hz
    · split
      · exact lt_of_le_of_lt (Nat.div_le_self _ _) hv
      · exact Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) hv) hR
    · -- One step of `V` multiplies by `u`.
      rw [mk_polyOfNat_step hv, hV, pow_succ]
      ring
    · -- `Z` gains `x_n V_n = x_n u^n Y`.
      rw [Finset.sum_range_succ, add_mul, ← hZ, bitTerm, Nat.testBit_eq_decide_div_mod_eq]
      by_cases hx : x / 2 ^ (127 - n) % 2 = 1
      · simp only [hx, ↓reduceIte, decide_true, polyOfNat_xor, map_add, hV]
      · simp [hx]

/-- The product of Algorithm 1 is the product of the residues, SP 800-38D §6.3. -/
theorem residue_mul (A B : Block) : residue (mul A B) = residue A * residue B := by
  obtain ⟨hz, -, -, hZ⟩ := mul_loop_spec (blockToNat A) (blockToNat B) (blockToNat_lt B) 128
  rw [residue, mul, blockToNat_blockOfNat hz, hZ, ← mk_polyOfNat]
  rfl

/-- One step of GHASH, SP 800-38D §6.4: `Y_i = (Y_(i-1) + X_i) H`, on residues. -/
theorem residue_ghash_append (H : Block) (blocks : List Block) (B : Block) :
    residue (ghash H (blocks ++ [B])) = (residue (ghash H blocks) + residue B) * residue H := by
  rw [ghash, List.foldl_append, List.foldl_cons, List.foldl_nil, residue_mul, residue_xorBlock]
  rfl

/-- The zero block has residue 0. -/
theorem residue_zeroBlock : residue zeroBlock = 0 := by
  have h : blockToNat zeroBlock = 0 := rfl
  have h0 : polyOfNat 0 = 0 := by simp [polyOfNat]
  rw [residue, h, h0, map_zero]

/-- The closed form over the indices below the length, with a default past the end. -/
private theorem residue_ghash_range (H : Block) (blocks : List Block) :
    residue (ghash H blocks) = ∑ i ∈ Finset.range blocks.length,
      residue (blocks.getD i zeroBlock) * residue H ^ (blocks.length - i) := by
  induction blocks using List.reverseRecOn with
  | nil => simp [ghash, residue_zeroBlock]
  | append_singleton blocks B ih =>
    -- The last block takes `H^1`, and every earlier power gains one factor of `H`.
    rw [residue_ghash_append, ih, List.length_append, List.length_singleton,
      Finset.sum_range_succ, add_mul, Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi : i < blocks.length := Finset.mem_range.mp hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      rw [mul_assoc, ← pow_succ,
        show blocks.length + 1 - i = blocks.length - i + 1 by omega]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some,
        Nat.add_sub_cancel_left, pow_one]

/-- GHASH of `X_1 ... X_m` is `X_1 H^m + X_2 H^(m-1) + ... + X_m H` on residues, SP 800-38D §6.4.

Block `X_(i+1)` is `blocks[i]`, and it takes the power `H^(m - i)`. -/
theorem residue_ghash (H : Block) (blocks : List Block) :
    residue (ghash H blocks)
      = ∑ i : Fin blocks.length, residue blocks[i] * residue H ^ (blocks.length - i.val) := by
  rw [residue_ghash_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some,
    Fin.getElem_fin]

end EthLib.Cryptography.Aes.Gcm

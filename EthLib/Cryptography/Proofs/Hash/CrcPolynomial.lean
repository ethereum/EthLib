module

public import EthLib.Cryptography.Proofs.Hash.Crc
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Proofs: a 32-bit CRC is a remainder in GF(2)[X]

A 32-bit CRC is defined by a division of polynomials over GF(2).

The specification computes it with a 32-bit register, one coefficient at a time.

For every generator and every message, the register holds the remainder of that division.

A register of 32 bits is the polynomial whose coefficient of `x^i` is its bit `i`.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Crc

open Polynomial

variable (g : UInt32)

/-! ## Polynomials -/

/-- A bit as a coefficient of GF(2). -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The polynomial of a register: bit `i` is the coefficient of `x^i`. -/
noncomputable def toPoly (r : UInt32) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 32, C (bit (r.toBitVec.getLsbD i)) * X ^ i

/-- The generator `G(x)`, with its `x^32` term. -/
noncomputable def G : (ZMod 2)[X] := X ^ 32 + toPoly g

/--
The message polynomial `M(x)` of a run of bits: the first bit is the highest coefficient.

The bits of a message enter the division in that order.
-/
noncomputable def ofBits (bits : List Bool) : (ZMod 2)[X] :=
  bits.foldl (fun p b => X * p + C (bit b)) 0

/-- The message polynomial `M(x)` of the bytes of a message. -/
noncomputable def message (data : ByteArray) : (ZMod 2)[X] :=
  ofBits (data.data.toList.flatMap byteBits)

/-- `L(x) = x^31 + ... + x + 1`, the polynomial of 32 ones. -/
noncomputable def L : (ZMod 2)[X] := toPoly 0xffffffff

/-! ## Coefficients -/

/-- The coefficient of `x^i` is bit `i` of the register, and 0 from `x^32` on. -/
theorem coeff_toPoly (r : UInt32) (i : Nat) :
    (toPoly r).coeff i = if i < 32 then bit (r.toBitVec.getLsbD i) else 0 := by
  simp only [toPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]

/-- A register has degree below 32. -/
theorem degree_toPoly_lt (r : UInt32) : (toPoly r).degree < 32 := by
  show (toPoly r).degree < ((32 : ℕ) : WithBot ℕ)
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly]
  simp only [ite_eq_right_iff]
  omega

/-- `G(x)` is monic, so dividing by it is defined over any ring. -/
theorem monic_G : (G g).Monic :=
  (monic_X_pow 32).add_of_left (by rw [degree_X_pow]; exact degree_toPoly_lt _)

/-- `G(x)` has degree 32. -/
theorem degree_G : (G g).degree = 32 := by
  rw [G, degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_toPoly_lt _),
    degree_X_pow]
  rfl

/-! ## One division step -/

/-- Adding bits in GF(2) is XOR. -/
theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

/-- The XOR of two registers is the sum of their polynomials. -/
theorem toPoly_xor (r s : UInt32) : toPoly (r ^^^ s) = toPoly r + toPoly s := by
  ext i
  simp only [coeff_add, coeff_toPoly, UInt32.toBitVec_xor, BitVec.getLsbD_xor, bit_xor]
  split <;> simp

/-- Multiplying by `x` is the shift left, with the bit shifted out as the coefficient of `x^32`. -/
theorem X_mul_toPoly (r : UInt32) :
    X * toPoly r = toPoly (r <<< 1) + C (bit (r >>> 31 == 1)) * X ^ 32 := by
  ext i
  rw [top_eq_getLsbD, coeff_add, coeff_toPoly, coeff_C_mul, coeff_X_pow,
    UInt32.toBitVec_shiftLeft]
  rcases i with _ | i
  · simp [bit]
  · rw [coeff_X_mul, coeff_toPoly]
    rw [show (UInt32.toBitVec 1 % 32) = 1#32 from rfl, BitVec.shiftLeft_eq',
      BitVec.getLsbD_shiftLeft]
    by_cases h : i + 1 < 32
    · simp [h, show i < 32 by omega, show i + 1 ≠ 32 by omega]
    · by_cases h32 : i + 1 = 32
      · simp [show i = 31 by omega]
      · simp [h, h32, show ¬ i < 32 by omega]

/-- One division step is `(x R(x) + c x^32) mod G(x)`. -/
theorem toPoly_shift (r : UInt32) (c : Bool) :
    toPoly (shift g r c) = (X * toPoly r + C (bit c) * X ^ 32) %ₘ G g := by
  -- The register already has degree below 32, so it is its own remainder.
  rw [← (modByMonic_eq_self_iff (p := toPoly (shift g r c)) (monic_G g)).mpr
    (by rw [degree_G]; exact degree_toPoly_lt _)]
  apply modByMonic_eq_of_dvd_sub (monic_G g)
  -- The two differ by `G(x)` when the coefficient of `x^32` is 1, and by 0 otherwise.
  refine ⟨C (bit ((r >>> 31 == 1) ^^ c)), ?_⟩
  rw [shift_eq_feedback, toPoly_xor, X_mul_toPoly]
  generalize (r >>> 31 == 1) = t
  have h0 : toPoly 0 = 0 := by simp [toPoly, bit]
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    rw [show (2 : (ZMod 2)[X]) = C 2 from rfl, show (2 : ZMod 2) = 0 from rfl, C_0]
  cases t <;> cases c <;> simp only [feedback, h0, G, bit, Bool.xor_false, Bool.xor_true,
    Bool.not_true, Bool.not_false, ite_true, ite_false, Bool.false_eq_true, map_one, map_zero]
  -- What is left is a multiple of 2, which is 0 in GF(2).
  all_goals (ring_nf; try simp [h2])
  all_goals linear_combination (-(X ^ 32 : (ZMod 2)[X])) * h2

/-! ## The whole division -/

/-- Horner's rule from `p`: each bit multiplies what came before by `x`. -/
theorem foldl_ofBits (bits : List Bool) (p : (ZMod 2)[X]) :
    bits.foldl (fun p b => X * p + C (bit b)) p = X ^ bits.length * p + ofBits bits := by
  induction bits generalizing p with
  | nil => simp [ofBits]
  | cons b bits ih =>
    simp only [List.foldl_cons, ofBits] at ih ⊢
    rw [ih, ih (X * 0 + C (bit b)), List.length_cons, pow_succ]
    ring

/-- After `n` bits from the register `r`, it holds `(x^32 M(x) + x^n r(x)) mod G(x)`. -/
theorem toPoly_foldl_shift (bits : List Bool) (r : UInt32) :
    toPoly (bits.foldl (shift g) r)
      = (X ^ 32 * ofBits bits + X ^ bits.length * toPoly r) %ₘ G g := by
  induction bits generalizing r with
  | nil =>
    simp only [List.foldl_nil, ofBits, mul_zero, List.length_nil, pow_zero, one_mul, zero_add]
    exact ((modByMonic_eq_self_iff (monic_G g)).mpr
      (by rw [degree_G]; exact degree_toPoly_lt _)).symm
  | cons c bits ih =>
    rw [List.foldl_cons, ih, toPoly_shift]
    apply modByMonic_eq_of_dvd_sub (monic_G g)
    -- Replacing the remainder of the first step by its dividend changes a multiple of `G(x)`.
    have hc : ofBits (c :: bits) = X ^ bits.length * C (bit c) + ofBits bits := by
      rw [ofBits, List.foldl_cons, foldl_ofBits, mul_zero, zero_add]
    obtain ⟨q, hq⟩ := dvd_modByMonic_sub (X * toPoly r + C (bit c) * X ^ 32) (G g)
    refine ⟨X ^ bits.length * q, ?_⟩
    rw [hc, List.length_cons, pow_succ X bits.length]
    linear_combination X ^ bits.length * hq

/--
The register after a message is `(x^32 M(x) + x^n L(x)) mod G(x)`, for a message of `n` bits.

The term `x^n L(x)` comes from the register's start at `0xffffffff`.
-/
theorem toPoly_remainder (data : ByteArray) :
    toPoly (remainder g data) = (X ^ 32 * message data + X ^ (8 * data.size) * L) %ₘ G g := by
  -- Each byte enters as its eight bits.
  have hbits (l : List UInt8) : (l.flatMap byteBits).length = 8 * l.length := by
    induction l with
    | nil => rfl
    | cons b l ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
      simp only [byteBits, List.length_map, List.length_range]
      omega
  have hlen : (data.data.toList.flatMap byteBits).length = 8 * data.size := by
    rw [hbits, Array.length_toList, ByteArray.size_data]
  rw [remainder, foldl_shiftByte, toPoly_foldl_shift, hlen, message, L]

/--
The division that defines the CRC, for a message of at least 32 bits.

It complements the 32 highest coefficients of `M(x)`, multiplies by `x^32`, and divides by `G(x)`.
-/
theorem toPoly_remainder_complement (data : ByteArray) (long : 4 ≤ data.size) :
    toPoly (remainder g data)
      = (X ^ 32 * (message data + X ^ (8 * data.size - 32) * L)) %ₘ G g := by
  rw [toPoly_remainder, show 8 * data.size = (8 * data.size - 32) + 32 by omega, pow_add,
    show 8 * data.size - 32 + 32 - 32 = 8 * data.size - 32 by omega]
  ring_nf

/-! ## The digest -/

/-- Reversing a byte moves bit `7 - j` to bit `j`, checked on all 256 bytes. -/
theorem getLsbD_reverseBits_all :
    ∀ n, n < 256 → ∀ j, j < 8 →
      (reverseBits n.toUInt8).toBitVec.getLsbD j = n.toUInt8.toBitVec.getLsbD (7 - j) := by
  decide +kernel

/-- Reversing a byte moves bit `7 - j` to bit `j`. -/
theorem getLsbD_reverseBits (b : UInt8) {j : Nat} (hj : j < 8) :
    (reverseBits b).toBitVec.getLsbD j = b.toBitVec.getLsbD (7 - j) := by
  simpa using getLsbD_reverseBits_all b.toNat b.toNat_lt j hj

/-- Bit `j` of the low byte of a word is its bit `j`. -/
theorem getLsbD_toUInt8 (w : UInt32) {j : Nat} (hj : j < 8) :
    w.toUInt8.toBitVec.getLsbD j = w.toBitVec.getLsbD j := by
  simp [hj]

/-- Bit `j` of the low byte of `w >>> s` is bit `s + j` of `w`. -/
theorem getLsbD_toUInt8_shiftRight (w s : UInt32) (hs : s.toNat < 32) {j : Nat} (hj : j < 8) :
    (w >>> s).toUInt8.toBitVec.getLsbD j = w.toBitVec.getLsbD (s.toNat + j) := by
  simp [UInt32.toBitVec_shiftRight, BitVec.getLsbD_ushiftRight, Nat.mod_eq_of_lt hs, hj]

/-- Bit `i` of a complemented word, below 32. -/
theorem getLsbD_not (w : UInt32) {i : Nat} (hi : i < 32) :
    (~~~w).toBitVec.getLsbD i = !w.toBitVec.getLsbD i := by
  simp [hi]

/-- A coefficient of the register is 0 exactly when its bit is clear. -/
theorem coeff_toPoly_eq_zero (r : UInt32) {i : Nat} (hi : i < 32) :
    (toPoly r).coeff i = 0 ↔ r.toBitVec.getLsbD i = false := by
  simp only [coeff_toPoly, hi, ite_true]
  cases r.toBitVec.getLsbD i <;> decide

/--
The digest, bit by bit.

Bit `j` of byte `k` is the complement of the coefficient of `x^(31 - 8k - j)` in the remainder.

The value of bit `j` is `2^j`, so the highest power of a byte lands on its bit 0.
-/
theorem digest_eq_modByMonic (data : ByteArray) (k : Fin 4) {j : Nat} (hj : j < 8) :
    (digest g data)[k].toBitVec.getLsbD j
      = decide (((X ^ 32 * message data + X ^ (8 * data.size) * L) %ₘ G g).coeff
          (31 - 8 * k.val - j) = 0) := by
  rw [← toPoly_remainder]
  simp only [coeff_toPoly_eq_zero _ (show 31 - 8 * k.val - j < 32 by omega), Bool.decide_eq_false]
  -- Byte k holds the bits 31 - 8k down to 24 - 8k of the complemented remainder, reversed.
  have h7 : 7 - j < 8 := by omega
  fin_cases k
  · show (reverseBits (~~~remainder g data >>> 24).toUInt8).toBitVec.getLsbD j = _
    rw [getLsbD_reverseBits _ hj, getLsbD_toUInt8_shiftRight _ _ (by decide) h7,
      getLsbD_not _ (by simp; omega)]
    congr 2
    simp; omega
  · show (reverseBits (~~~remainder g data >>> 16).toUInt8).toBitVec.getLsbD j = _
    rw [getLsbD_reverseBits _ hj, getLsbD_toUInt8_shiftRight _ _ (by decide) h7,
      getLsbD_not _ (by simp; omega)]
    congr 2
    simp; omega
  · show (reverseBits (~~~remainder g data >>> 8).toUInt8).toBitVec.getLsbD j = _
    rw [getLsbD_reverseBits _ hj, getLsbD_toUInt8_shiftRight _ _ (by decide) h7,
      getLsbD_not _ (by simp; omega)]
    congr 2
    simp; omega
  · show (reverseBits (~~~remainder g data).toUInt8).toBitVec.getLsbD j = _
    rw [getLsbD_reverseBits _ hj, getLsbD_toUInt8 _ h7, getLsbD_not _ (by omega)]
    congr 2

end EthLib.Cryptography.Hash.Crc

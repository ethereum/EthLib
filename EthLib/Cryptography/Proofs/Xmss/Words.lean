module

public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Base.Proofs.LittleEndian
public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.Proofs.Hash.Keccak.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: randomizers as words

A randomizer and a digest are 16 bytes, which the search keeps as two 64-bit words.

The words and the bytes carry the same integer, so the search's randomizers are the sums it names.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-! ## Randomizers as words -/

namespace WordPair

/-- Byte `j` of two words is byte `j` of the low word, or byte `j - 8` of the high word. -/
theorem toNat_getElem_bytes (w : WordPair) (j : Nat) (hj : j < 16) :
    (w.bytes[j]).toNat =
      if j < 8 then w.lo.toNat / 2 ^ (8 * j) % 256 else w.hi.toNat / 2 ^ (8 * (j - 8)) % 256 := by
  interval_cases j <;>
    simp [bytes, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- The bytes of two words are the little-endian bytes of their integer. -/
theorem bytes_eq (w : WordPair) : w.bytes = uintToBytes 16 w.toNat := by
  have := w.lo.toNat_lt
  apply Vector.ext
  intro j hj
  apply UInt8.toNat_inj.mp
  rw [toNat_getElem_bytes _ _ hj]
  simp only [uintToBytes, toNat, Vector.getElem_ofFn, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  interval_cases j <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceLT, Nat.reduceSub, ite_true, ite_false] <;>
    omega

/-- Byte `j` of the bytes, read past the end as zero, is byte `j` of the vector. -/
private theorem byteAt_packBytes (v : Vector UInt8 16) {j : Nat} (hj : j < 16) :
    Base.byteAt (packBytes v) j = v[j] := by
  have : j < (packBytes v).size := by simpa using hj
  rw [Base.byteAt, dite_eq_left_of_eq_true (eq_true this)]
  rfl

/-- The low word of 16 bytes is the lane at their byte 0. -/
theorem lo_ofBytes (v : Vector UInt8 16) :
    (ofBytes v).lo = Hash.Keccak.Internal.laneAt (packBytes v) 0 :=
  rfl

/-- The high word of 16 bytes is the lane at their byte 8. -/
theorem hi_ofBytes (v : Vector UInt8 16) :
    (ofBytes v).hi = Hash.Keccak.Internal.laneAt (packBytes v) 8 :=
  rfl

/-- Bit `t` of byte `q` of a number is its bit `8q + t`. -/
private theorem testBit_byte (x q t : Nat) (ht : t < 8) :
    (x / 2 ^ (8 * q) % 256).testBit t = x.testBit (8 * q + t) := by
  rw [show (256 : Nat) = 2 ^ 8 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht, Nat.add_comm]

/-- Reading 16 bytes as words and back gives the same bytes. -/
@[simp] theorem bytes_ofBytes (v : Vector UInt8 16) : (ofBytes v).bytes = v := by
  apply Vector.ext
  intro j hj
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  rcases Nat.lt_or_ge t 8 with ht | ht
  · -- Bit `t` of byte `j` is bit `8 (j mod 8) + t` of the word that holds byte `j`.
    have hlane : ∀ (s : Nat) (x : UInt64), s + j % 8 = j →
        x = Hash.Keccak.Internal.laneAt (packBytes v) s →
        (x.toNat / 2 ^ (8 * (j % 8)) % 256).testBit t = v[j].toNat.testBit t := by
      intro s x hs hx
      rw [testBit_byte _ _ _ ht]
      have h64 : 8 * (j % 8) + t < 64 := by omega
      have := Hash.Keccak.Internal.laneAt_testBit (packBytes v) s _ h64
      rw [← hx] at this
      change x.toNat.testBit _ = _ at this
      have e1 : s + (8 * (j % 8) + t) / 8 = j := by omega
      have e2 : (8 * (j % 8) + t) % 8 = t := by omega
      rw [this, e1, e2, byteAt_packBytes _ hj]
    rw [toNat_getElem_bytes _ _ hj]
    split_ifs with hj8
    · have := hlane 0 _ (by omega) (lo_ofBytes v)
      rwa [Nat.mod_eq_of_lt hj8] at this
    · have := hlane 8 _ (by omega) (hi_ofBytes v)
      rwa [show j % 8 = j - 8 by omega] at this
  · -- Bytes have no bit from 8 on.
    have h1 : (ofBytes v).bytes[j].toNat < 2 ^ t :=
      lt_of_lt_of_le (UInt8.toNat_lt _) (Nat.pow_le_pow_right (by decide) ht)
    have h2 : v[j].toNat < 2 ^ t :=
      lt_of_lt_of_le (UInt8.toNat_lt _) (Nat.pow_le_pow_right (by decide) ht)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- The integer of the words of 16 bytes is their little-endian integer. -/
theorem toNat_ofBytes (v : Vector UInt8 16) : (ofBytes v).toNat = bytesToUint v := by
  have hlt : (ofBytes v).toNat < 2 ^ 128 := by
    have := (ofBytes v).lo.toNat_lt
    have := (ofBytes v).hi.toNat_lt
    unfold toNat
    omega
  have := congrArg bytesToUint (bytes_ofBytes v)
  rw [bytes_eq, Base.bytesToUint_uintToBytes, Nat.mod_eq_of_lt (by simpa using hlt)] at this
  exact this

end WordPair

/-- Trial `c`'s words make `R_0 + c mod 2^128`, with `R_0` the integer of the base's words. -/
theorem toNat_trialWords (w : WordPair) (c : Nat) :
    (trialWords w c).toNat = (w.toNat + c) % 2 ^ 128 := by
  have := w.lo.toNat_lt
  have := w.hi.toNat_lt
  simp only [trialWords, WordPair.toNat]
  split_ifs with h <;>
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_ofNat',
      Nat.shiftRight_eq_div_pow, UInt64.toNat_one, UInt64.toNat_zero] at h ⊢ <;>
    omega

end EthLib.Cryptography.Xmss

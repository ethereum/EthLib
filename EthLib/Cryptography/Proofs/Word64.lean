module

public import EthLib.Cryptography.Word64
public import EthLib.Cryptography.Montgomery
import all EthLib.Cryptography.Montgomery
import Mathlib.Tactic.Ring

/-!
# Proofs: integers of four 64-bit words

Four words determine their integer, and their integer determines them.

The bit that a shift and a mask read from the words is the bit of their integer.

Four words and the eight 32-bit limbs of the shared Montgomery field hold the same integer.

So a field on four words takes its laws from the shared field.
-/

@[expose] public section

namespace EthLib.Cryptography.Word64

open EthLib.Cryptography.Montgomery (Limbs)

/-- The integer of four words, as nested products by `2^64`. -/
private theorem Raw.val_nested (k : Raw) :
    k.val = 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * k.w3.toNat + k.w2.toNat) + k.w1.toNat) + k.w0.toNat := by
  simp only [Raw.val, Raw.words, lowValue, wordRadix]
  ring

/-- Distinct words have distinct values. -/
theorem Raw.val_injective : Function.Injective Raw.val := by
  intro x y h
  have hx0 := x.w0.toNat_lt
  have hx1 := x.w1.toNat_lt
  have hx2 := x.w2.toNat_lt
  have hx3 := x.w3.toNat_lt
  have hy0 := y.w0.toNat_lt
  have hy1 := y.w1.toNat_lt
  have hy2 := y.w2.toNat_lt
  have hy3 := y.w3.toNat_lt
  rw [Raw.val_nested, Raw.val_nested] at h
  have e0 : x.w0.toNat = y.w0.toNat := by omega
  have e1 : x.w1.toNat = y.w1.toNat := by omega
  have e2 : x.w2.toNat = y.w2.toNat := by omega
  have e3 : x.w3.toNat = y.w3.toNat := by omega
  cases x
  cases y
  simp only [Raw.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp e0, UInt64.toNat_inj.mp e1, UInt64.toNat_inj.mp e2,
    UInt64.toNat_inj.mp e3⟩

/-- Bit `r` of a word, by a shift and a mask, is bit `r` of its value. -/
private theorem wordBit (w : UInt64) (r : Nat) (hr : r < 64) :
    ((w >>> r.toUInt64) &&& 1 != 0) = w.toNat.testBit r := by
  have hr' : r.toUInt64.toNat % 64 = r := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  have h : ((w >>> r.toUInt64) &&& 1).toNat = (w.toNat >>> r) % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_one, Nat.and_one_is_mod, hr']
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    bne_iff_ne, ne_eq, decide_eq_true_iff, ← UInt64.toNat_inj, h, UInt64.toNat_zero]
  omega

/-- The bit read from four words is the bit of their value. -/
theorem Raw.bit_iff (k : Raw) (s : Nat) : k.bit s = true ↔ (k.val >>> s) % 2 = 1 := by
  have h0 := k.w0.toNat_lt
  have h1 := k.w1.toNat_lt
  have h2 := k.w2.toNat_lt
  have hb : ((k.val >>> s) % 2 = 1) ↔ k.val.testBit s = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, decide_eq_true_iff]
  rw [hb, Raw.val_nested, Nat.testBit_two_pow_mul_add _ h0]
  simp only [Raw.bit]
  split_ifs with c0 c1 c2 c3
  · rw [wordBit _ _ (by omega), Nat.mod_eq_of_lt c0]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_left (by omega), show s % 64 = s - 64 by omega,
      wordBit _ _ (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_right (by omega),
      Nat.testBit_two_pow_mul_add _ h2, ite_eq_left (by omega),
      show s % 64 = s - 64 - 64 by omega, wordBit _ _ (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_right (by omega),
      Nat.testBit_two_pow_mul_add _ h2, ite_eq_right (by omega),
      show s % 64 = s - 64 - 64 - 64 by omega, wordBit _ _ (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, ite_eq_right (by omega),
      Nat.testBit_two_pow_mul_add _ h2, ite_eq_right (by omega),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le k.w3.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega)))]
    simp only [UInt64.zero_shiftRight, UInt64.zero_and, bne_self_eq_false]

/-! ## Four words and eight limbs -/

/-- One word from two 32-bit limbs, the low one first. -/
def join (lo hi : UInt32) : UInt64 :=
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-- Four words from eight 32-bit limbs, with a zero carry word. -/
def wide (a : Cryptography.Montgomery.Limbs8) : Words64 :=
  ⟨join a.l0 a.l1, join a.l2 a.l3, join a.l4 a.l5, join a.l6 a.l7, 0⟩

/-- Eight 32-bit limbs from the four low words. -/
def narrow (p : Words64) : Cryptography.Montgomery.Limbs8 :=
  ⟨p.w0.toUInt32, (p.w0 >>> 32).toUInt32,
    p.w1.toUInt32, (p.w1 >>> 32).toUInt32,
    p.w2.toUInt32, (p.w2 >>> 32).toUInt32,
    p.w3.toUInt32, (p.w3 >>> 32).toUInt32⟩

/-- A joined word is worth its low limb plus `2^32` times its high limb. -/
private theorem join_value (lo hi : UInt32) : (join lo hi).toNat = lo.toNat + 2^32*hi.toNat := by
  have hhi : hi.toNat * 2^32 < 2^64 := Nat.mul_lt_mul_of_pos_right hi.toNat_lt (by decide)
  unfold join
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  change lo.toNat ||| (hi.toNat <<< 32) % 2^64 = _
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hhi, Nat.mul_comm hi.toNat, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt lo.toNat_lt, Nat.add_comm]

/-- The two 32-bit halves of a word give back its value. -/
private theorem split_value (w : UInt64) :
    w.toUInt32.toNat + 2^32*(w >>> 32).toUInt32.toNat = w.toNat := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  change w.toNat % 2^32 + 2^32*(w.toNat / 2^32 % 2^32) = w.toNat
  have h : w.toNat / 2^32 < 2^32 := Nat.div_lt_of_lt_mul w.toNat_lt
  rw [Nat.mod_eq_of_lt h, Nat.mod_add_div]

/-- The integer of eight 32-bit limbs, as a sum of powers of `2^32`. -/
private theorem limbs8_value (a : Cryptography.Montgomery.Limbs8) :
    Limbs.val (n := 8) a = a.l0.toNat + 2^32*a.l1.toNat + 2^64*a.l2.toNat +
      2^96*a.l3.toNat + 2^128*a.l4.toNat + 2^160*a.l5.toNat +
      2^192*a.l6.toNat + 2^224*a.l7.toNat := by
  change a.l0.toNat + 2^32*(a.l1.toNat + 2^32*(a.l2.toNat + 2^32*(a.l3.toNat +
    2^32*(a.l4.toNat + 2^32*(a.l5.toNat + 2^32*(a.l6.toNat + 2^32*(a.l7.toNat + 2^32*0))))))) = _
  omega

/-- Four words joined from eight limbs have the value of the limbs. -/
theorem value_wide (a : Cryptography.Montgomery.Limbs8) :
    value (wide a) = Limbs.val (n := 8) a := by
  simp only [value, lowValue, wide, join_value, limbs8_value, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero, wordRadix]
  omega

/-- Eight limbs split from four words, with no carry, have the value of the words. -/
theorem val_narrow (w : Words64) (h : w.top = 0) :
    Limbs.val (n := 8) (narrow w) = value w := by
  have h0 := split_value w.w0
  have h1 := split_value w.w1
  have h2 := split_value w.w2
  have h3 := split_value w.w3
  simp only [limbs8_value, narrow, value, lowValue, h, UInt64.toNat_zero,
    Nat.mul_zero, Nat.add_zero, wordRadix]
  omega

/-- Joining the two halves of a word gives the word. -/
private theorem join_split (w : UInt64) :
    join w.toUInt32 (w >>> 32).toUInt32 = w :=
  UInt64.toNat_inj.mp ((join_value _ _).trans (split_value w))

/-- Splitting four words into limbs and joining them back gives the words. -/
theorem wide_narrow (w : Words64) (h : w.top = 0) : wide (narrow w) = w := by
  cases w
  cases h
  simp only [wide, narrow, join_split]
  rfl

end EthLib.Cryptography.Word64

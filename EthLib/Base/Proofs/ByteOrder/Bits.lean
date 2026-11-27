module

public import EthLib.Base.Proofs.ByteOrder

/-!
# Proofs: the bits of a number whose bytes are read in the other order

Little-endian bytes read big-endian reverse the order of the bytes.

The bits keep their order in each byte.
-/

@[expose] public section

namespace EthLib.Base.ByteOrder

/-- Bit `i` of a big-endian integer is bit `i % 8` of its byte `i / 8` from the end. -/
theorem testBit_ofBE (l : List UInt8) : ∀ i : Nat, (ofBE l).testBit i =
    (decide (i < 8 * l.length) && (l.getD (l.length - 1 - i / 8) 0).toNat.testBit (i % 8)) := by
  intro i
  induction l generalizing i with
  | nil => simp [ofBE_eq_foldl]
  | cons x l ih =>
    have hlt : ofBE l < 2 ^ (8 * l.length) := by
      rw [Nat.pow_mul]
      exact ofBE_lt l
    rw [ofBE_cons, Nat.mul_comm, show (256 : Nat) ^ l.length = 2 ^ (8 * l.length) by
      rw [Nat.pow_mul], Nat.testBit_two_pow_mul_add _ hlt, List.length_cons]
    by_cases hi : i < 8 * l.length
    · -- The bit is in the bytes after the first.
      have h0 : l.length + 1 - 1 - i / 8 = (l.length - 1 - i / 8) + 1 := by omega
      simp only [hi, ↓reduceIte, ih, h0, List.getD_cons_succ]
      simp [show i < 8 * (l.length + 1) by omega]
    · simp only [hi, ↓reduceIte]
      by_cases hi' : i < 8 * (l.length + 1)
      · -- The bit is in the first byte.
        have h0 : l.length + 1 - 1 - i / 8 = 0 := by omega
        rw [h0, List.getD_cons_zero, show i - 8 * l.length = i % 8 by omega]
        simp [hi']
      · -- The bit is past the last byte.
        have hx : x.toNat < 2 ^ (i - 8 * l.length) :=
          Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
        simp [hi', Nat.testBit_lt_two_pow hx]

/-- Read big-endian, the `n` little-endian bytes of `e` put each byte of `e` in the mirrored place.

So bit `k` is bit `(n - 1 - k / 8) * 8 + k % 8` of `e`, and the bits from `8 n` on are 0. -/
theorem testBit_ofBE_toLE (n e k : Nat) :
    (ofBE (toLE n e).toList).testBit k =
      (decide (k < 8 * n) && e.testBit ((n - 1 - k / 8) * 8 + k % 8)) := by
  rw [testBit_ofBE, Vector.length_toList]
  by_cases hk : k < 8 * n
  · have hj : n - 1 - k / 8 < n := by omega
    simp only [hk, decide_true, Bool.true_and, toLE_eq_div, Vector.toList_ofFn,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj]
    simp only [dite_true, Option.getD_some, UInt8.toNat_ofNat', show (256 : Nat) = 2 ^ 8 from rfl,
      ← Nat.pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
      show k % 8 < 8 from Nat.mod_lt _ (by decide), decide_true, Bool.true_and]
    congr 1
    omega
  · simp [hk]

end EthLib.Base.ByteOrder

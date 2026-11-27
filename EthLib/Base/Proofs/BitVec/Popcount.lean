module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Proofs: the population count of a bit vector

The population count is the number of one bits, as the Lean core library defines it.

- It is the sum of the bits, and it is 0 only for the zero vector.
- Its bound by the width is in the core library.
- It grows with the set of one bits, and adds over vectors with no common one bit.
- The counts of the or and the and of two vectors add up to their two counts.
- The Hamming distance, the count of the exclusive or, is the sum less twice the count of the and.
-/

@[expose] public section

namespace EthLib.Base.BitVec

open Finset

/-- The population count is the sum of the bits. -/
theorem toNat_cpop_eq_sum {w : Nat} (x : BitVec w) :
    x.cpop.toNat = ∑ i ∈ range w, (x.getLsbD i).toNat := by
  rw [BitVec.toNat_cpop]
  -- The count from bit `n` down to bit 0 is the sum of the bits below `n`.
  suffices h : ∀ n acc, x.cpopNatRec n acc = acc + ∑ i ∈ range n, (x.getLsbD i).toNat by
    simpa using h w 0
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro acc
    rw [BitVec.cpopNatRec_succ, ih, sum_range_succ]
    omega

/-- The population count is 0 exactly for the zero vector. -/
theorem toNat_cpop_eq_zero_iff {w : Nat} {x : BitVec w} : x.cpop.toNat = 0 ↔ x = 0#w := by
  rw [toNat_cpop_eq_sum, sum_eq_zero_iff]
  constructor
  · intro h
    refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
    have := h i (mem_range.mpr hi)
    cases hb : x.getLsbD i <;> simp_all
  · rintro rfl i _
    simp

/-- The population count of `x` is at most that of `y` when every one bit of `x` is in `y`. -/
theorem toNat_cpop_le_of_and_eq_left {w : Nat} {x y : BitVec w} (h : x &&& y = x) :
    x.cpop.toNat ≤ y.cpop.toNat := by
  conv_lhs => rw [← h]
  rw [toNat_cpop_eq_sum, toNat_cpop_eq_sum]
  refine sum_le_sum fun i _ => ?_
  rw [BitVec.getLsbD_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> decide

/-- The intersection has at most the one bits of its left side. -/
theorem toNat_cpop_and_le_left {w : Nat} (x y : BitVec w) :
    (x &&& y).cpop.toNat ≤ x.cpop.toNat :=
  toNat_cpop_le_of_and_eq_left (by rw [BitVec.and_assoc, BitVec.and_comm y, ← BitVec.and_assoc,
    BitVec.and_self])

/-- The intersection has at most the one bits of its right side. -/
theorem toNat_cpop_and_le_right {w : Nat} (x y : BitVec w) :
    (x &&& y).cpop.toNat ≤ y.cpop.toNat :=
  toNat_cpop_le_of_and_eq_left (by rw [BitVec.and_assoc, BitVec.and_self])

/-- The counts of the union and the intersection add up to the counts of the two vectors. -/
theorem toNat_cpop_or_add_toNat_cpop_and {w : Nat} (x y : BitVec w) :
    (x ||| y).cpop.toNat + (x &&& y).cpop.toNat = x.cpop.toNat + y.cpop.toNat := by
  simp only [toNat_cpop_eq_sum, ← sum_add_distrib, BitVec.getLsbD_or, BitVec.getLsbD_and]
  refine sum_congr rfl fun i _ => ?_
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

/-- The population count of two vectors with no common one bit adds over their union. -/
theorem toNat_cpop_or_of_and_eq_zero {w : Nat} {x y : BitVec w} (h : x &&& y = 0#w) :
    (x ||| y).cpop.toNat = x.cpop.toNat + y.cpop.toNat := by
  have := toNat_cpop_or_add_toNat_cpop_and x y
  rw [h, BitVec.cpop_zero, BitVec.toNat_zero] at this
  omega

/-- The count of the exclusive or, plus twice that of the intersection, is the sum of the counts. -/
theorem toNat_cpop_xor_add_two_mul_toNat_cpop_and {w : Nat} (x y : BitVec w) :
    (x ^^^ y).cpop.toNat + 2 * (x &&& y).cpop.toNat = x.cpop.toNat + y.cpop.toNat := by
  simp only [toNat_cpop_eq_sum, Nat.two_mul, ← sum_add_distrib, BitVec.getLsbD_xor,
    BitVec.getLsbD_and]
  refine sum_congr rfl fun i _ => ?_
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

end EthLib.Base.BitVec

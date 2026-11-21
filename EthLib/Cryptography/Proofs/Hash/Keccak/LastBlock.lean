module

public import EthLib.Cryptography.Proofs.Hash.Keccak.Hasher
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Set

/-!
# Proofs: one lane of the last block

Take two messages of one length that differ only in one lane of their last block.

The blocks before the last one are the same in both, so they absorb to the same state.

So the states before the last permutation differ only by the XOR of that lane.

A search that hashes many such messages builds that state once, and XORs one lane per message.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

open EthLib.Base (byteAt byteAt_append)
open Internal

/-- Eight zero bytes: one lane of zeros. -/
abbrev zeroLane : ByteArray :=
  ByteArray.mk (Array.replicate 8 0)

/-- A lane of zero bytes reads as zero. -/
theorem laneAt_zero {bytes : ByteArray} {s : Nat} (h : ∀ k < 8, byteAt bytes (s + k) = 0) :
    laneAt bytes s = 0 := by
  have h0 : byteAt bytes s = 0 := by simpa using h 0 (by omega)
  unfold laneAt
  rw [h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega), h 5 (by omega),
    h 6 (by omega), h 7 (by omega)]
  rfl

/-- The state before the last permutation, for a message with a lane `w` in its last block.

It is the state for the same message with that lane zero, with `w` XORed into its lane.

- The lane starts at byte `a.size`, a multiple of 8, so it is one lane of its block.
- The lane is in the last block: the message ends in the block where the lane starts. -/
theorem stateBeforeLastPermutation_append_lane (f : State → State) {rate : Nat} (hr : 0 < rate)
    (lanes : 8 ∣ rate) (a w b : ByteArray) (hw : w.size = 8) (ha : 8 ∣ a.size)
    (hlast : (a.size + 8 + b.size) / rate = a.size / rate) :
    stateBeforeLastPermutation f rate (a ++ w ++ b) =
      (stateBeforeLastPermutation f rate (a ++ zeroLane ++ b)).xorLane (a.size % rate / 8)
        (laneAt w 0) := by
  have hz : zeroLane.size = 8 := rfl
  have hsize : (a ++ w ++ b).size = (a ++ zeroLane ++ b).size := by
    simp only [ByteArray.size_append, hw, hz]
  -- The two padded messages: the same bytes, except the lane at `a.size`.
  set P₁ := pad rate (a ++ w ++ b) with hP₁
  set P₀ := pad rate (a ++ zeroLane ++ b) with hP₀
  have outside : ∀ j, (j < a.size ∨ a.size + 8 ≤ j) → byteAt P₁ j = byteAt P₀ j := by
    intro j hj
    rw [hP₁, hP₀, pad, pad, hsize]
    simp only [byteAt_append, ByteArray.size_append, hw, hz]
    split_ifs <;> first | rfl | omega
  have inside : ∀ k < 8, byteAt P₁ (a.size + k) = byteAt w k := by
    intro k hk
    rw [hP₁, pad]
    simp only [byteAt_append, ByteArray.size_append, hw]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    congr 1
    omega
  have zero : ∀ k < 8, byteAt P₀ (a.size + k) = 0 := by
    intro k hk
    rw [hP₀, pad]
    simp only [byteAt_append, ByteArray.size_append, hz]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    rw [EthLib.Base.byteAt_eq_getD]
    simp [hk]
  -- The blocks before the last one lie before the lane, so they are the same.
  have hq : blockCount rate (a ++ w ++ b).size - 1 = a.size / rate := by
    simp only [blockCount, ByteArray.size_append, hw, Nat.add_sub_cancel, hlast]
  have hq₀ : blockCount rate (a ++ zeroLane ++ b).size - 1 = a.size / rate := by
    rw [← hsize, hq]
  have hle : rate * (a.size / rate) ≤ a.size := Nat.mul_div_le _ _
  have before : absorbBlocks f rate P₁ (a.size / rate) 0 State.zero =
      absorbBlocks f rate P₀ (a.size / rate) 0 State.zero :=
    absorbBlocks_congr f lanes _ _ fun j hj => outside _ (by omega)
  rw [stateBeforeLastPermutation_eq_pad, stateBeforeLastPermutation_eq_pad, ← hP₁, ← hP₀, hq, hq₀,
    before]
  -- In the last block, lane `i` reads the bytes from `a.size + 8 (i - i₀)`.
  set i₀ := a.size % rate / 8 with hi₀
  have hstart : rate * (a.size / rate) + 8 * i₀ = a.size := by
    obtain ⟨r, hr'⟩ := lanes
    obtain ⟨s, hs⟩ := ha
    have h8 : 8 * i₀ = a.size % rate := by
      rw [hi₀, hs, hr', Nat.mul_mod_mul_left]
      omega
    have := Nat.div_add_mod a.size rate
    omega
  have hlane : ∀ i, blockLane rate P₁ (rate * (a.size / rate)) i =
      blockLane rate P₀ (rate * (a.size / rate)) i ^^^ if i = i₀ then laneAt w 0 else 0 := by
    intro i
    unfold blockLane
    by_cases hi : 8 * i + 8 ≤ rate
    · rw [ite_eq_left hi, ite_eq_left hi]
      by_cases hii : i = i₀
      · subst hii
        rw [ite_eq_left rfl, hstart, laneAt_zero zero, UInt64.zero_xor]
        exact laneAt_congr fun k hk => by rw [inside k hk, Nat.zero_add]
      · rw [ite_eq_right hii, UInt64.xor_zero]
        apply laneAt_congr
        intro k hk
        apply outside
        have : i < i₀ ∨ i₀ < i := by omega
        omega
    · have : i ≠ i₀ := by
        intro h
        apply hi
        rw [h, hi₀]
        have := Nat.mod_lt a.size hr
        omega
      rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right this, UInt64.xor_zero]
  unfold absorbBlock
  simp only [hlane]
  have key := absorbBlock_lanes_xor (absorbBlocks f rate P₀ (a.size / rate) 0 State.zero)
    (blockLane rate P₀ (rate * (a.size / rate))) i₀ (laneAt w 0)
  exact key

end EthLib.Cryptography.Hash.Keccak

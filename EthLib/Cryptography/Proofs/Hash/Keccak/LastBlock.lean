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

/-- An index of 25 or more names no lane. -/
theorem State.xorLane_of_le (A : State) {i : Nat} (h : 25 ≤ i) (v : UInt64) :
    A.xorLane i v = A := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 25 := ⟨i - 25, by omega⟩
  rfl

/-- XORing one word into lane `i` of a block XORs it into lane `i` of the absorbed state. -/
private theorem absorbBlock_lanes_xor (S : State) (g : Nat → UInt64) (i : Nat) (v : UInt64) :
    (⟨S.a0 ^^^ (g 0 ^^^ if 0 = i then v else 0), S.a1 ^^^ (g 1 ^^^ if 1 = i then v else 0),
      S.a2 ^^^ (g 2 ^^^ if 2 = i then v else 0), S.a3 ^^^ (g 3 ^^^ if 3 = i then v else 0),
      S.a4 ^^^ (g 4 ^^^ if 4 = i then v else 0), S.a5 ^^^ (g 5 ^^^ if 5 = i then v else 0),
      S.a6 ^^^ (g 6 ^^^ if 6 = i then v else 0), S.a7 ^^^ (g 7 ^^^ if 7 = i then v else 0),
      S.a8 ^^^ (g 8 ^^^ if 8 = i then v else 0), S.a9 ^^^ (g 9 ^^^ if 9 = i then v else 0),
      S.a10 ^^^ (g 10 ^^^ if 10 = i then v else 0), S.a11 ^^^ (g 11 ^^^ if 11 = i then v else 0),
      S.a12 ^^^ (g 12 ^^^ if 12 = i then v else 0), S.a13 ^^^ (g 13 ^^^ if 13 = i then v else 0),
      S.a14 ^^^ (g 14 ^^^ if 14 = i then v else 0), S.a15 ^^^ (g 15 ^^^ if 15 = i then v else 0),
      S.a16 ^^^ (g 16 ^^^ if 16 = i then v else 0), S.a17 ^^^ (g 17 ^^^ if 17 = i then v else 0),
      S.a18 ^^^ (g 18 ^^^ if 18 = i then v else 0), S.a19 ^^^ (g 19 ^^^ if 19 = i then v else 0),
      S.a20 ^^^ (g 20 ^^^ if 20 = i then v else 0), S.a21 ^^^ (g 21 ^^^ if 21 = i then v else 0),
      S.a22 ^^^ (g 22 ^^^ if 22 = i then v else 0), S.a23 ^^^ (g 23 ^^^ if 23 = i then v else 0),
      S.a24 ^^^ (g 24 ^^^ if 24 = i then v else 0)⟩ : State) =
    (⟨S.a0 ^^^ g 0, S.a1 ^^^ g 1, S.a2 ^^^ g 2, S.a3 ^^^ g 3, S.a4 ^^^ g 4, S.a5 ^^^ g 5,
      S.a6 ^^^ g 6, S.a7 ^^^ g 7, S.a8 ^^^ g 8, S.a9 ^^^ g 9, S.a10 ^^^ g 10, S.a11 ^^^ g 11,
      S.a12 ^^^ g 12, S.a13 ^^^ g 13, S.a14 ^^^ g 14, S.a15 ^^^ g 15, S.a16 ^^^ g 16,
      S.a17 ^^^ g 17, S.a18 ^^^ g 18, S.a19 ^^^ g 19, S.a20 ^^^ g 20, S.a21 ^^^ g 21,
      S.a22 ^^^ g 22, S.a23 ^^^ g 23, S.a24 ^^^ g 24⟩ : State).xorLane i v := by
  rcases Nat.lt_or_ge i 25 with h | h
  · interval_cases i <;> simp [State.xorLane, UInt64.xor_assoc]
  · rw [State.xorLane_of_le _ h]
    simp only [show ∀ j, j < 25 → (j = i) = False from fun j hj => eq_false (by omega),
      ite_false, UInt64.xor_zero, Nat.reduceLT]

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
  rw [stateBeforeLastPermutation, stateBeforeLastPermutation, ← hP₁, ← hP₀, hq, hq₀, before]
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
    by_cases hi : 8 * i < rate
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

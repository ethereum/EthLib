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

open Internal

/-! ## XOR into one lane -/

/-- XOR into lane `i` is XOR into every lane, of the word in lane `i` and of zero elsewhere. -/
theorem State.xorLane_eq (S : State) (i : Nat) (v : UInt64) :
    S.xorLane i v =
      ⟨S.a0 ^^^ (if 0 = i then v else 0), S.a1 ^^^ (if 1 = i then v else 0),
        S.a2 ^^^ (if 2 = i then v else 0), S.a3 ^^^ (if 3 = i then v else 0),
        S.a4 ^^^ (if 4 = i then v else 0), S.a5 ^^^ (if 5 = i then v else 0),
        S.a6 ^^^ (if 6 = i then v else 0), S.a7 ^^^ (if 7 = i then v else 0),
        S.a8 ^^^ (if 8 = i then v else 0), S.a9 ^^^ (if 9 = i then v else 0),
        S.a10 ^^^ (if 10 = i then v else 0), S.a11 ^^^ (if 11 = i then v else 0),
        S.a12 ^^^ (if 12 = i then v else 0), S.a13 ^^^ (if 13 = i then v else 0),
        S.a14 ^^^ (if 14 = i then v else 0), S.a15 ^^^ (if 15 = i then v else 0),
        S.a16 ^^^ (if 16 = i then v else 0), S.a17 ^^^ (if 17 = i then v else 0),
        S.a18 ^^^ (if 18 = i then v else 0), S.a19 ^^^ (if 19 = i then v else 0),
        S.a20 ^^^ (if 20 = i then v else 0), S.a21 ^^^ (if 21 = i then v else 0),
        S.a22 ^^^ (if 22 = i then v else 0), S.a23 ^^^ (if 23 = i then v else 0),
        S.a24 ^^^ (if 24 = i then v else 0)⟩ := by
  -- The block lemma with a zero block is this one.
  have h := absorbBlock_lanes_xor S (fun _ => 0) i v
  simp only [UInt64.zero_xor, UInt64.xor_zero] at h
  exact h.symm

/-- XORs into two lanes commute. -/
theorem State.xorLane_comm (S : State) (i j : Nat) (v w : UInt64) :
    (S.xorLane i v).xorLane j w = (S.xorLane j w).xorLane i v := by
  simp only [State.xorLane_eq, UInt64.xor_assoc, UInt64.xor_comm (if _ = i then v else 0)]

/-- A padding byte XORed in after a lane is the padding byte XORed in before it. -/
theorem xorBlockByte_xorLane (rate : Nat) (S : State) (p : Nat) (b : UInt8) (i : Nat)
    (v : UInt64) :
    xorBlockByte rate (S.xorLane i v) p b = (xorBlockByte rate S p b).xorLane i v := by
  unfold xorBlockByte
  split
  · exact State.xorLane_comm _ _ _ _ _
  · rfl

/-! ## One lane of the last block -/

/-- The state before the last permutation, for a message with a word `v` XORed into one lane.

It is the state for the message without it, with `v` XORed into that lane's place in the state.

- The lane starts at byte `p`, a multiple of 8.
- The lane is in the last block: `p / rate = len / rate`. -/
theorem stateBeforeLastPermutation_xorLane {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : State → m State) {rate : Nat} (hr : 0 < rate) (lanes : 8 ∣ rate) (len p : Nat)
    (read : Nat → UInt64) (v : UInt64) (hp : 8 ∣ p) (hlast : p / rate = len / rate) :
    stateBeforeLastPermutation f rate len (fun q => if q = p then read q ^^^ v else read q) =
      (·.xorLane (p % rate / 8) v) <$> stateBeforeLastPermutation f rate len read := by
  simp only [stateBeforeLastPermutation]
  -- The blocks before the last one lie before the lane, so they read the same lanes.
  have hle : rate * (len / rate) ≤ p := hlast ▸ Nat.mul_div_le p rate
  rw [absorbBlocks_congr_read f lanes _ _ (read' := read) (t := 0)
    (fun q hq _ => by simp only [Nat.zero_add]; rw [ite_eq_right (by omega)])]
  rw [map_bind]
  refine congrArg _ (funext fun S => ?_)
  rw [map_pure]
  refine congrArg pure ?_
  -- In the last block, the lane is lane `i₀` from the start of the block.
  set i₀ := p % rate / 8 with hi₀
  have hstart : rate * (len / rate) + 8 * i₀ = p := by
    obtain ⟨r, hr'⟩ := lanes
    obtain ⟨s, hs⟩ := hp
    have h8 : 8 * i₀ = p % rate := by
      rw [hi₀, hs, hr', Nat.mul_mod_mul_left]
      omega
    have := Nat.div_add_mod p rate
    rw [← hlast]
    omega
  have hin : 8 * i₀ + 8 ≤ rate := by
    obtain ⟨r, hr'⟩ := lanes
    obtain ⟨s, hs⟩ := hp
    have h8 : 8 * i₀ = p % rate := by
      rw [hi₀, hs, hr', Nat.mul_mod_mul_left]
      omega
    have : p % rate < rate := Nat.mod_lt p hr
    subst hr'
    omega
  have hlane : ∀ i, blockLane rate (fun q => if q = p then read q ^^^ v else read q)
      (rate * (len / rate)) i =
      blockLane rate read (rate * (len / rate)) i ^^^ if i = i₀ then v else 0 := by
    intro i
    unfold blockLane
    beta_reduce
    by_cases hi : 8 * i + 8 ≤ rate
    · rw [ite_eq_left hi, ite_eq_left hi]
      by_cases hii : i = i₀
      · subst hii
        rw [ite_eq_left hstart, ite_eq_left rfl, hstart]
      · rw [ite_eq_right (by omega), ite_eq_right hii, UInt64.xor_zero]
    · have : i ≠ i₀ := fun h => hi (h ▸ hin)
      rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right this, UInt64.xor_zero]
  have hblock : absorbBlock rate S (fun q => if q = p then read q ^^^ v else read q)
      (rate * (len / rate)) = (absorbBlock rate S read (rate * (len / rate))).xorLane i₀ v := by
    unfold absorbBlock
    simp only [hlane]
    exact absorbBlock_lanes_xor S _ i₀ v
  rw [hblock, xorBlockByte_xorLane, xorBlockByte_xorLane]

end EthLib.Cryptography.Hash.Keccak

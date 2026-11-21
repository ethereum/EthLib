module

public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Hash.Keccak.LastBlock

/-!
# Proofs: randomizer trials on Keccak lanes

With Keccak-256, a trial XORs its randomizer into two lanes of a state built once per search.

Those trials give the codeword of hashing the trial's whole input.

So signing with them gives the bytes of signing with the hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Hash.Keccak (laneOfArray stateBeforeLastPermutation keccakF RATE_256)

/-- The lanes of a string with two lanes appended: its own, then the two, then zeros.

At each multiple of 8, it is the reader of the string alone, with the two lanes XORed in. -/
theorem laneOfArray_append_two (before : Array UInt64) (lo hi : UInt64) (q : Nat) (hq : 8 ∣ q) :
    laneOfArray (before ++ #[lo, hi]) q =
      if q = 8 * (before.size + 1) then
        (if q = 8 * before.size then laneOfArray before q ^^^ lo else laneOfArray before q) ^^^ hi
      else if q = 8 * before.size then laneOfArray before q ^^^ lo else laneOfArray before q := by
  obtain ⟨j, rfl⟩ := hq
  simp only [laneOfArray, Nat.mul_div_cancel_left _ (by decide : 0 < 8),
    Array.getD_eq_getD_getElem?, Array.getElem?_append]
  by_cases h1 : j < before.size
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
  · obtain ⟨k, rfl⟩ : ∃ k, j = before.size + k := ⟨j - before.size, by omega⟩
    have hn : before[before.size + k]? = none := Array.getElem?_eq_none (by omega)
    rw [ite_eq_right h1, hn, Option.getD_none, Nat.add_sub_cancel_left]
    rcases k with _ | _ | k
    · simp only [Nat.add_zero] at hn ⊢
      rw [ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp

/-- The Keccak-256 trials give the codeword of hashing each trial's input. -/
theorem keccakTrials_eq : keccakTrials = hashTrials hashId := by
  funext before
  unfold keccakTrials
  split
  · next hlast =>
    simp only [hashTrials, Trials.mk.injEq]
    funext rho
    -- The state of the whole input is the state of the fixed lanes, with the two lanes XORed in.
    have key : stateBeforeLastPermutation keccakF RATE_256 (8 * (before ++ rho.toArray).size)
        (laneOfArray (before ++ rho.toArray)) =
        ((stateBeforeLastPermutation keccakF RATE_256 (8 * (before.size + 2))
          (laneOfArray before)).xorLane ((8 * before.size) % RATE_256 / 8 + 1) rho.hi).xorLane
          ((8 * before.size) % RATE_256 / 8) rho.lo := by
      have hsize : (before ++ rho.toArray).size = before.size + 2 := by
        simp [Hash.Keccak.Lanes2.toArray]
      rw [hsize]
      simp only [Hash.Keccak.Lanes2.toArray]
      rw [Hash.Keccak.stateBeforeLastPermutation_congr _ Hash.Keccak.lanes_rate _
        (laneOfArray_append_two before rho.lo rho.hi),
        Hash.Keccak.stateBeforeLastPermutation_xorLane _ (by decide) Hash.Keccak.lanes_rate _ _ _
          _ ⟨before.size + 1, rfl⟩ (by simp only [RATE_256] at hlast ⊢; omega),
        Hash.Keccak.stateBeforeLastPermutation_xorLane _ (by decide) Hash.Keccak.lanes_rate _ _ _
          _ ⟨before.size, rfl⟩ (by simp only [RATE_256] at hlast ⊢; omega),
        Hash.Keccak.State.xorLane_comm]
      congr 2
      simp only [RATE_256] at hlast ⊢
      omega
    show _ = (pure (codeword? (halfOf 0 (hash (before ++ rho.toArray)))) : Id _)
    simp only [hash, Hash.Keccak.keccak256Lanes, Hash.Keccak.Internal.keccak256Read,
      Hash.Keccak.spongeAbsorb, key]
    rfl
  · rfl

end EthLib.Cryptography.Xmss

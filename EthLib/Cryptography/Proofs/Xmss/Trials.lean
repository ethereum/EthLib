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
open EthLib.Cryptography.Hash.Keccak (keccakF RATE_256)
open EthLib.Cryptography.Hash.Keccak.Internal (laneOfArray stateBeforeLastPermutation)

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
        (Hash.Keccak.laneOfArray_append_two before rho.lo rho.hi),
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
      Hash.Keccak.Internal.spongeAbsorb, key]
    rfl
  · rfl

end EthLib.Cryptography.Xmss

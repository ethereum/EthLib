module

public import EthLib.Cryptography.Xmss.Ots
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Hash.Keccak.LastBlock
public import EthLib.Cryptography.Proofs.Xmss.Words
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: randomizer trials on Keccak lanes

With Keccak-256, a trial XORs its randomizer into two lanes of a state built once per search.

Those trials give the codeword of hashing the trial's whole input.

So signing with them gives the bytes of signing with the hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- The first half of a squeezed digest is the two words of lanes 0 and 1. -/
theorem halfOf_squeeze256 (T : Hash.Keccak.State) :
    halfOf 0 (Hash.Keccak.Internal.squeeze256 T) = (⟨T.a0, T.a1⟩ : WordPair).bytes := by
  apply Vector.ext
  intro j hj
  simp only [halfOf, Vector.getElem_cast]
  simp only [DIGEST_LEN] at hj
  interval_cases j <;> simp [Hash.Keccak.Internal.squeeze256] <;> rfl

/-- The Keccak-256 trials give the codeword of hashing each trial's input. -/
theorem keccakTrials_eq : keccakTrials = hashTrials hashId := by
  funext before
  unfold keccakTrials
  split_ifs with h
  · obtain ⟨h8, hlast⟩ := h
    simp only [hashTrials, Trials.mk.injEq]
    funext rho
    change Vector UInt8 16 at rho
    -- The input is the fixed bytes, then the two lanes of the randomizer.
    set lo := (packBytes rho).extract 0 8
    set hi := (packBytes rho).extract 8 16
    have hsplit : packBytes rho = lo ++ (hi ++ .empty) := by
      have hs : (packBytes rho).size = 16 := by simp []
      apply Base.eq_of_byteAt
      · simp [lo, hi, hs]
      · intro i
        simp only [lo, hi, Base.byteAt_append, Base.byteAt_extract, ByteArray.size_extract, hs,
          Nat.sub_zero, Nat.zero_add, Nat.reduceSub, show min 8 16 = 8 from rfl, Nat.min_self]
        split_ifs <;> first
          | with_reducible rfl
          | omega
          | (congr 1; omega)
          | rw [Base.byteAt_of_size_le (by omega), Base.byteAt_of_size_le (by simp)]
    have hlo : Hash.Keccak.Internal.laneAt lo 0 = (WordPair.ofBytes rho).lo := by
      erw [WordPair.lo_ofBytes]
      exact Hash.Keccak.laneAt_congr fun k hk => by
        rw [Base.byteAt_extract, ite_eq_left (by simp []; omega)]
        simp only [Nat.zero_add]
    have hhi : Hash.Keccak.Internal.laneAt hi 0 = (WordPair.ofBytes rho).hi := by
      erw [WordPair.hi_ofBytes]
      exact Hash.Keccak.laneAt_congr fun k hk => by
        rw [Base.byteAt_extract, ite_eq_left (by simp []; omega)]
        simp only [Nat.zero_add]
    have hz : Hash.Keccak.zeroLane.size = 8 := rfl
    have hzeros : ByteArray.mk (Array.replicate 16 0) =
        Hash.Keccak.zeroLane ++ Hash.Keccak.zeroLane ++ .empty := rfl
    have key : Hash.Keccak.stateBeforeLastPermutation Hash.Keccak.keccakF Hash.Keccak.RATE_256
        (before ++ packBytes rho) =
        ((Hash.Keccak.stateBeforeLastPermutation Hash.Keccak.keccakF Hash.Keccak.RATE_256
          (before ++ ByteArray.mk (Array.replicate 16 0))).xorLane
            (before.size % Hash.Keccak.RATE_256 / 8 + 1) (WordPair.ofBytes rho).hi).xorLane
          (before.size % Hash.Keccak.RATE_256 / 8) (WordPair.ofBytes rho).lo := by
      rw [hsplit, ← ByteArray.append_assoc,
        Hash.Keccak.stateBeforeLastPermutation_append_lane _ (by decide) Hash.Keccak.lanes_rate
          before lo (hi ++ .empty) (by simp [lo]) (Nat.dvd_of_mod_eq_zero h8)
          (by simp [hi, Hash.Keccak.RATE_256] at hlast ⊢; omega),
        hlo, ← ByteArray.append_assoc,
        Hash.Keccak.stateBeforeLastPermutation_append_lane _ (by decide) Hash.Keccak.lanes_rate
          (before ++ Hash.Keccak.zeroLane) hi .empty (by simp [hi]) (by simp [hz]; omega)
          (by simp [hz, Hash.Keccak.RATE_256] at hlast ⊢; omega),
        hhi, hzeros]
      simp only [ByteArray.append_assoc]
      congr 2
      simp [hz, Hash.Keccak.RATE_256] at hlast ⊢
      omega
    show _ = (pure (codeword? (halfOf 0 (Hash.Keccak.Internal.squeeze256 (Hash.Keccak.keccakF
      (Hash.Keccak.stateBeforeLastPermutation Hash.Keccak.keccakF Hash.Keccak.RATE_256
        (before ++ packBytes rho)))))) : Id _)
    rw [key, halfOf_squeeze256]
  · rfl

end EthLib.Cryptography.Xmss

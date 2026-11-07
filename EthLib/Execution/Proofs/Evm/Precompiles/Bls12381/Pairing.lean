module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Pairing
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.Pairing`

- Before it charges gas, the pairing check rejects two kinds of input.
  They are an empty input, and a length that is not a whole number of 384-byte pairs.
- Take a whole number of pairs and enough gas.
  The check then succeeds exactly when every padding is zero and every point decodes.
- Each point is decoded with the subgroup check.
- It then returns the word of the pairing check of the decoded pairs.
- Every output is the 32-byte word 0 or 1.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bind_ok_iff)
open EthLib.Cryptography.Bls (pairingCheck)

/-- The pairing check rejects an empty input or a length that is not a whole number of pairs, whatever the gas. -/
theorem bls12Pairing_invalidInputLength {data : ByteArray}
    (hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0) (gas : Nat) :
    bls12Pairing data gas = .error (.invalidInputLength data.size) := by
  unfold bls12Pairing
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsize)]
  rfl

/-- The pairing check runs out of gas below its price. -/
theorem bls12Pairing_outOfGas {data : ByteArray} (hsize : ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0))
    {gas : Nat} (hgas : gas < bls12PairingGas (data.size / LENGTH_PER_PAIRING_PAIR)) :
    bls12Pairing data gas =
      .error (.outOfGas (bls12PairingGas (data.size / LENGTH_PER_PAIRING_PAIR)) gas) := by
  unfold bls12Pairing
  rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- The pairing check succeeds exactly on a nonzero number `k` of 384-byte pairs, with its gas.

The gas must be at least the price of `k` pairs.

The padding of every point must be zero, and every point must decode with the subgroup check.

The output is the word of the pairing check of the decoded pairs. -/
theorem bls12Pairing_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12Pairing data gas = .ok out ↔
      ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0) ∧
        bls12PairingGas (data.size / LENGTH_PER_PAIRING_PAIR) ≤ gas ∧
        ∃ rawPairs pairs,
          (chunks LENGTH_PER_PAIRING_PAIR (data.size / LENGTH_PER_PAIRING_PAIR)
              data.data.toList).mapM
              (fun pair => do return (← unpadG1 (pair.take 128), ← unpadG2 (pair.drop 128))) =
            .ok rawPairs ∧
          rawPairs.mapM (fun (rawG1, rawG2) => do
              return (← bytesToG1 rawG1 true, ← bytesToG2 rawG2 true)) = .ok pairs ∧
          out = ⟨(boolWord (pairingCheck pairs.toArray)).toArray⟩ := by
  by_cases hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0
  · rw [bls12Pairing_invalidInputLength hsize gas]
    exact iff_of_false (by simp) fun h => h.1 hsize
  · by_cases hgas : gas < bls12PairingGas (data.size / LENGTH_PER_PAIRING_PAIR)
    · rw [bls12Pairing_outOfGas hsize hgas]
      exact iff_of_false (by simp) fun h => absurd h.2.1 (Nat.not_le.mpr hgas)
    · unfold bls12Pairing
      rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
      dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false hgas)]
      simp only [hsize, not_false_eq_true, Nat.not_lt.mp hgas, true_and, bind, Except.bind]
      split
      · rename_i hm
        simp [hm]
      · rename_i rawPairs hm
        split
        · rename_i hq
          simp [hm, hq]
        · rename_i pairs hq
          simp only [pure, Except.pure, Except.ok.injEq] at hm hq ⊢
          constructor
          · rintro rfl
            exact ⟨rawPairs, pairs, hm, hq, rfl⟩
          · rintro ⟨rawPairs', pairs', hm', hq', rfl⟩
            rw [hm] at hm'
            cases hm'
            rw [hq] at hq'
            cases hq'
            rfl

/-- The words of the two booleans differ. -/
theorem boolWord_injective : Function.Injective boolWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolWord]

/-- Every output is the 32-byte word 0 or 1. -/
theorem bls12Pairing_ok {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12Pairing data gas = .ok out) :
    ∃ result, out = ⟨(boolWord result).toArray⟩ := by
  simp only [bls12Pairing, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨_, rfl⟩

/-- The word of a boolean has 32 bytes. -/
theorem length_boolWord (result : Bool) : (boolWord result).length = 32 := by
  simp [boolWord]

end EthLib.Execution.Evm.Precompiles.Bls12381

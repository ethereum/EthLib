module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Pairing
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.Pairing`

- The pairing check rejects an empty input or a length that is not a whole number of 384-byte pairs, before it charges gas.
- Every output is the 32-byte word 0 or 1.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

/-- The pairing check rejects an empty input or a length that is not a whole number of pairs, whatever the gas. -/
theorem bls12Pairing_invalidInputLength {data : ByteArray}
    (hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0) (gas : Nat) :
    bls12Pairing data gas = .error (.invalidInputLength data.size) := by
  unfold bls12Pairing
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsize)]
  rfl

/-- The pairing check runs out of gas below its price. -/
theorem bls12Pairing_outOfGas {data : ByteArray} (hsize : ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIRING_PAIR ≠ 0))
    {gas : Nat} (hgas : gas < pairingGas (data.size / LENGTH_PER_PAIRING_PAIR)) :
    bls12Pairing data gas = .error (.outOfGas (pairingGas (data.size / LENGTH_PER_PAIRING_PAIR)) gas) := by
  unfold bls12Pairing
  rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- Every output is the 32-byte word 0 or 1. -/
theorem bls12Pairing_ok {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12Pairing data gas = .ok out) :
    ∃ result, out = ⟨(boolWord result).toArray⟩ := by
  simp only [bls12Pairing, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  exact ⟨_, rfl⟩

/-- The word of a boolean has 32 bytes. -/
theorem length_boolWord (result : Bool) : (boolWord result).length = 32 := by
  simp [boolWord]

end EthLib.Execution.Evm.Precompiles.Bls12381

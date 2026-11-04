module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.G1`

- G1ADD rejects any length other than 256 bytes before it charges gas, and then runs out of gas below its price.
- Every encoded G1 point, and so every output of G1ADD and G1MSM, has 128 bytes.
- G1MSM rejects an empty input or a length that is not a whole number of 160-byte pairs.
- Its discount never raises the price above that of `k` separate products.
- MAP_FP_TO_G1 rejects any length other than 64 bytes before it charges gas, and every output has 128 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes_length)
open EthLib.Cryptography.Bls (G1)

/-- The raw bytes of a G1 point have 96 bytes, and its padded encoding 128. -/
theorem length_padG1_g1ToBytes (point : G1) : (padG1 (g1ToBytes point)).length = 128 := by
  simp [padG1, g1ToBytes, zeroPad, PAD_BYTES, natToBytes_length]

/-- G1ADD rejects any length other than 256 bytes, whatever the gas. -/
theorem bls12G1Add_invalidInputLength {data : ByteArray} (hsize : data.size ≠ 256) (gas : Nat) :
    bls12G1Add data gas = .error (.invalidInputLength data.size) := by
  simp [bls12G1Add, hsize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- G1ADD runs out of gas below its price. -/
theorem bls12G1Add_outOfGas {data : ByteArray} (hsize : data.size = 256) {gas : Nat}
    (hgas : gas < GAS_G1ADD) :
    bls12G1Add data gas = .error (.outOfGas GAS_G1ADD gas) := by
  simp [bls12G1Add, hsize, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Every output of G1ADD has 128 bytes. -/
theorem bls12G1Add_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G1Add data gas = .ok out) :
    out.size = 128 := by
  simp only [bls12G1Add, bind, throw, throwThe, MonadExceptOf.throw] at h
  -- Past the two checks, the output is the padded encoding of a sum.
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_padG1_g1ToBytes]

/-! ## G1MSM -/

/-- G1MSM rejects an empty input or a length that is not a whole number of pairs, whatever the gas. -/
theorem bls12G1Msm_invalidInputLength {data : ByteArray}
    (hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G1 ≠ 0) (gas : Nat) :
    bls12G1Msm data gas = .error (.invalidInputLength data.size) := by
  unfold bls12G1Msm
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsize)]
  rfl

/-- G1MSM runs out of gas below its price. -/
theorem bls12G1Msm_outOfGas {data : ByteArray} (hsize : ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G1 ≠ 0))
    {gas : Nat} (hgas : gas < msmGasG1 (data.size / LENGTH_PER_PAIR_G1)) :
    bls12G1Msm data gas = .error (.outOfGas (msmGasG1 (data.size / LENGTH_PER_PAIR_G1)) gas) := by
  unfold bls12G1Msm
  rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- Every output of G1MSM has 128 bytes. -/
theorem bls12G1Msm_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G1Msm data gas = .ok out) :
    out.size = 128 := by
  simp only [bls12G1Msm, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_padG1_g1ToBytes]

/-- Every entry of the discount table is at most 1000 thousandths. -/
theorem G1_K_DISCOUNT_le : ∀ i : Fin 128, G1_K_DISCOUNT[i] ≤ 1000 := by decide

/-- Every discount is at most 1000 thousandths. -/
theorem discountG1_le (k : Nat) : discountG1 k ≤ MULTIPLIER := by
  unfold discountG1
  split
  · rename_i h
    exact G1_K_DISCOUNT_le ⟨k - 1, by omega⟩
  · decide

/-- The price of `k` pairs is at most the price of `k` separate products. -/
theorem msmGasG1_le (k : Nat) : msmGasG1 k ≤ k * GAS_G1MUL := by
  unfold msmGasG1
  have := discountG1_le k
  calc k * GAS_G1MUL * discountG1 k / MULTIPLIER
      ≤ k * GAS_G1MUL * MULTIPLIER / MULTIPLIER := Nat.div_le_div_right (Nat.mul_le_mul_left _ this)
    _ = k * GAS_G1MUL := by simp [MULTIPLIER]

/-- Past 128 pairs, the discount stays at 519 thousandths. -/
theorem discountG1_of_lt {k : Nat} (hk : 128 < k) : discountG1 k = 519 := by
  simp [discountG1, G1_MAX_DISCOUNT]
  omega

/-! ## MAP_FP_TO_G1 -/

/-- MAP_FP_TO_G1 rejects any length other than 64 bytes, whatever the gas. -/
theorem bls12MapFpToG1_invalidInputLength {data : ByteArray} (hsize : data.size ≠ 64) (gas : Nat) :
    bls12MapFpToG1 data gas = .error (.invalidInputLength data.size) := by
  unfold bls12MapFpToG1
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsize)]
  rfl

/-- MAP_FP_TO_G1 runs out of gas below its price. -/
theorem bls12MapFpToG1_outOfGas {data : ByteArray} (hsize : data.size = 64) {gas : Nat} (hgas : gas < GAS_G1MAP) :
    bls12MapFpToG1 data gas = .error (.outOfGas GAS_G1MAP gas) := by
  unfold bls12MapFpToG1
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- Every output of MAP_FP_TO_G1 has 128 bytes. -/
theorem bls12MapFpToG1_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12MapFpToG1 data gas = .ok out) :
    out.size = 128 := by
  simp only [bls12MapFpToG1, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  repeat obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_padG1_g1ToBytes]

end EthLib.Execution.Evm.Precompiles.Bls12381

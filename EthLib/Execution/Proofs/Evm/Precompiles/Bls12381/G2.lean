module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G2
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.G2`

- G2ADD rejects any length other than 512 bytes before it charges gas, and then runs out of gas below its price.
- Every encoded G2 point, and so every output of G2ADD and G2MSM, has 256 bytes.
- G2MSM rejects an empty input or a length that is not a whole number of 288-byte pairs.
- Its discount never raises the price above that of `k` separate products.
- MAP_FP2_TO_G2 rejects any length other than 128 bytes before it charges gas, and every output has 256 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes_length)
open EthLib.Cryptography.Bls (G2)

/-- The raw bytes of a G2 point have 192 bytes, and its padded encoding 256. -/
theorem length_padG2_g2ToBytes (point : G2) : (padG2 (g2ToBytes point)).length = 256 := by
  simp [padG2, g2ToBytes, zeroPad, PAD_BYTES, natToBytes_length]

/-- G2ADD rejects any length other than 512 bytes, whatever the gas. -/
theorem bls12G2Add_invalidInputLength {data : ByteArray} (hsize : data.size ≠ 512) (gas : Nat) :
    bls12G2Add data gas = .error (.invalidInputLength data.size) := by
  simp [bls12G2Add, hsize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- G2ADD runs out of gas below its price. -/
theorem bls12G2Add_outOfGas {data : ByteArray} (hsize : data.size = 512) {gas : Nat}
    (hgas : gas < GAS_G2ADD) :
    bls12G2Add data gas = .error (.outOfGas GAS_G2ADD gas) := by
  simp [bls12G2Add, hsize, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Every output of G2ADD has 256 bytes. -/
theorem bls12G2Add_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G2Add data gas = .ok out) :
    out.size = 256 := by
  simp only [bls12G2Add, bind, throw, throwThe, MonadExceptOf.throw] at h
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
  simp [ByteArray.size, length_padG2_g2ToBytes]

/-! ## G2MSM -/

/-- G2MSM rejects an empty input or a length that is not a whole number of pairs, whatever the gas. -/
theorem bls12G2Msm_invalidInputLength {data : ByteArray}
    (hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G2 ≠ 0) (gas : Nat) :
    bls12G2Msm data gas = .error (.invalidInputLength data.size) := by
  unfold bls12G2Msm
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsize)]
  rfl

/-- G2MSM runs out of gas below its price. -/
theorem bls12G2Msm_outOfGas {data : ByteArray} (hsize : ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G2 ≠ 0))
    {gas : Nat} (hgas : gas < bls12G2MsmGas (data.size / LENGTH_PER_PAIR_G2)) :
    bls12G2Msm data gas =
      .error (.outOfGas (bls12G2MsmGas (data.size / LENGTH_PER_PAIR_G2)) gas) := by
  unfold bls12G2Msm
  rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- Every output of G2MSM has 256 bytes. -/
theorem bls12G2Msm_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G2Msm data gas = .ok out) :
    out.size = 256 := by
  simp only [bls12G2Msm, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_padG2_g2ToBytes]

/-- Every entry of the discount table is at most 1000 thousandths. -/
theorem G2_K_DISCOUNT_le : ∀ i : Fin 128, G2_K_DISCOUNT[i] ≤ 1000 := by decide

/-- Every discount is at most 1000 thousandths. -/
theorem discountG2_le (k : Nat) : discountG2 k ≤ MULTIPLIER := by
  unfold discountG2
  split
  · rename_i h
    exact G2_K_DISCOUNT_le ⟨k - 1, by omega⟩
  · decide

/-- The price of `k` pairs is at most the price of `k` separate products. -/
theorem bls12G2MsmGas_le (k : Nat) : bls12G2MsmGas k ≤ k * GAS_G2MUL := by
  unfold bls12G2MsmGas
  have := discountG2_le k
  calc k * GAS_G2MUL * discountG2 k / MULTIPLIER
      ≤ k * GAS_G2MUL * MULTIPLIER / MULTIPLIER := Nat.div_le_div_right (Nat.mul_le_mul_left _ this)
    _ = k * GAS_G2MUL := by simp [MULTIPLIER]

/-- Past 128 pairs, the discount stays at 524 thousandths. -/
theorem discountG2_of_lt {k : Nat} (hk : 128 < k) : discountG2 k = 524 := by
  simp [discountG2, G2_MAX_DISCOUNT]
  omega

/-! ## MAP_FP2_TO_G2 -/

/-- MAP_FP2_TO_G2 rejects any length other than 128 bytes, whatever the gas. -/
theorem bls12MapFp2ToG2_invalidInputLength {data : ByteArray} (hsize : data.size ≠ 128) (gas : Nat) :
    bls12MapFp2ToG2 data gas = .error (.invalidInputLength data.size) := by
  unfold bls12MapFp2ToG2
  rw [ite_eq_left_of_eq_true _ _ (eq_true hsize)]
  rfl

/-- MAP_FP2_TO_G2 runs out of gas below its price. -/
theorem bls12MapFp2ToG2_outOfGas {data : ByteArray} (hsize : data.size = 128) {gas : Nat} (hgas : gas < GAS_G2MAP) :
    bls12MapFp2ToG2 data gas = .error (.outOfGas GAS_G2MAP gas) := by
  unfold bls12MapFp2ToG2
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- Every output of MAP_FP2_TO_G2 has 256 bytes. -/
theorem bls12MapFp2ToG2_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12MapFp2ToG2 data gas = .ok out) :
    out.size = 256 := by
  simp only [bls12MapFp2ToG2, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  repeat obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_padG2_g2ToBytes]

end EthLib.Execution.Evm.Precompiles.Bls12381

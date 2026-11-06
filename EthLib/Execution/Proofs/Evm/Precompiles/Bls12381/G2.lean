module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G2
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.G2`

- G2ADD rejects any length other than 512 bytes before it charges gas, and then runs out of gas below its price.
- With enough gas, G2ADD succeeds exactly when both halves decode, and returns the encoded sum.
- Every encoded G2 point, and so every output of G2ADD and G2MSM, has 256 bytes.
- G2MSM rejects an empty input or a length that is not a whole number of 288-byte pairs.
- Its discount never raises the price above that of `k` separate products.
- MAP_FP2_TO_G2 rejects any length other than 128 bytes before it charges gas, and every output has 256 bytes.
- With enough gas, it succeeds exactly when the element of `Fp2` decodes and its map succeeds.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bind_ok_iff mapError_ok_iff natToBytes_length)
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

/-- G2ADD succeeds exactly on 512 bytes, with at least its price in gas.

Each 256-byte half must decode to a point, without the subgroup check.

The output is the padded encoding of the sum of the two points. -/
theorem bls12G2Add_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12G2Add data gas = .ok out ↔
      data.size = 512 ∧ GAS_G2ADD ≤ gas ∧
        ∃ raw0 raw1 p0 p1,
          unpadG2 (data.data.toList.take 256) = .ok raw0 ∧
          unpadG2 (data.data.toList.drop 256) = .ok raw1 ∧
          bytesToG2 raw0 false = .ok p0 ∧
          bytesToG2 raw1 false = .ok p1 ∧
          out = ⟨(padG2 (g2ToBytes (G2.add p0 p1))).toArray⟩ := by
  by_cases hsize : data.size ≠ 512
  · simp [bls12G2Add_invalidInputLength hsize gas, hsize]
  · have hsize' : data.size = 512 := Decidable.not_not.mp hsize
    by_cases hgas : gas < GAS_G2ADD
    · simp [bls12G2Add_outOfGas hsize' hgas, hsize', Nat.not_le.mpr hgas]
    · simp only [bls12G2Add, hsize', ne_eq, not_true_eq_false, ↓reduceIte, hgas,
        Nat.not_lt.mp hgas, true_and, bind, Except.bind, pure, Except.pure]
      cases hu0 : unpadG2 (data.data.toList.take 256) <;>
        cases hu1 : unpadG2 (data.data.toList.drop 256) <;> simp
      rename_i raw0 raw1
      cases hp0 : bytesToG2 raw0 false <;>
        cases hp1 : bytesToG2 raw1 false <;> simp [eq_comm]

/-- Every output of G2ADD has 256 bytes. -/
theorem bls12G2Add_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G2Add data gas = .ok out) :
    out.size = 256 := by
  obtain ⟨-, -, -, -, p0, p1, -, -, -, -, rfl⟩ := (bls12G2Add_eq_ok_iff data gas out).mp h
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

/-- G2MSM succeeds exactly on a whole, nonzero number `k` of 288-byte pairs, with its price in gas.

The padding of every point must be zero, and the sum of the pairs must succeed.

The output is the padded encoding of that sum. -/
theorem bls12G2Msm_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12G2Msm data gas = .ok out ↔
      ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G2 ≠ 0) ∧
        bls12G2MsmGas (data.size / LENGTH_PER_PAIR_G2) ≤ gas ∧
        ∃ pairs q,
          (chunks LENGTH_PER_PAIR_G2 (data.size / LENGTH_PER_PAIR_G2) data.data.toList).mapM
              (fun pair => do return (← unpadG2 (pair.take 256), pair.drop 256)) = .ok pairs ∧
            g2Msm pairs = .ok q ∧ out = ⟨(padG2 (g2ToBytes q)).toArray⟩ := by
  by_cases hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G2 ≠ 0
  · rw [bls12G2Msm_invalidInputLength hsize gas]
    exact iff_of_false (by simp) fun h => h.1 hsize
  · by_cases hgas : gas < bls12G2MsmGas (data.size / LENGTH_PER_PAIR_G2)
    · rw [bls12G2Msm_outOfGas hsize hgas]
      exact iff_of_false (by simp) fun h => absurd h.2.1 (Nat.not_le.mpr hgas)
    · unfold bls12G2Msm
      rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
      dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false hgas)]
      simp only [hsize, not_false_eq_true, Nat.not_lt.mp hgas, true_and, bind, Except.bind]
      split
      · rename_i hm
        simp [hm]
      · rename_i pairs hm
        split
        · rename_i hq
          simp [hm, hq]
        · rename_i q hq
          simp only [pure, Except.pure, Except.ok.injEq] at hm ⊢
          constructor
          · rintro rfl
            exact ⟨pairs, q, hm, hq, rfl⟩
          · rintro ⟨pairs', q', hm', hq', rfl⟩
            rw [hm] at hm'
            cases hm'
            rw [hq] at hq'
            cases hq'
            rfl

/-- Every output of G2MSM has 256 bytes. -/
theorem bls12G2Msm_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G2Msm data gas = .ok out) :
    out.size = 256 := by
  simp only [bls12G2Msm, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
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

/-- MAP_FP2_TO_G2 succeeds exactly on 128 bytes, with at least its price in gas.

Both paddings must be zero, and both field elements must be below the modulus.

The map of that element of `Fp2` to the twist must succeed.

The output is the padded encoding of the mapped point. -/
theorem bls12MapFp2ToG2_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12MapFp2ToG2 data gas = .ok out ↔
      data.size = 128 ∧ GAS_G2MAP ≤ gas ∧
        ∃ c0 c1 u P, unpadFp (data.data.toList.take 64) = .ok c0 ∧
          unpadFp (data.data.toList.drop 64) = .ok c1 ∧ bytesToFq2 (c0 ++ c1) = .ok u ∧
          Cryptography.Bls.MapToCurve.mapToG2 u = .ok P ∧
          out = ⟨(padG2 (g2ToBytes P)).toArray⟩ := by
  by_cases hsize : data.size ≠ 128
  · rw [bls12MapFp2ToG2_invalidInputLength hsize gas]
    exact iff_of_false (by simp) fun h => hsize h.1
  · have hsize' : data.size = 128 := Decidable.not_not.mp hsize
    by_cases hgas : gas < GAS_G2MAP
    · rw [bls12MapFp2ToG2_outOfGas hsize' hgas]
      exact iff_of_false (by simp) fun h => absurd h.2.1 (Nat.not_le.mpr hgas)
    · simp only [bls12MapFp2ToG2, hgas, ↓reduceIte, hsize', Nat.not_lt.mp hgas, true_and]
      constructor
      · intro h
        obtain ⟨c0, h0, h⟩ := bind_ok_iff.mp h
        obtain ⟨c1, h1, h⟩ := bind_ok_iff.mp h
        obtain ⟨u, hu, h⟩ := bind_ok_iff.mp h
        obtain ⟨P, hp, h⟩ := bind_ok_iff.mp h
        exact ⟨c0, c1, u, P, h0, h1, hu, mapError_ok_iff.mp hp, (Except.ok.inj h).symm⟩
      · rintro ⟨c0, c1, u, P, h0, h1, hu, hp, rfl⟩
        exact bind_ok_iff.mpr ⟨c0, h0, bind_ok_iff.mpr ⟨c1, h1, bind_ok_iff.mpr ⟨u, hu,
          bind_ok_iff.mpr ⟨P, mapError_ok_iff.mpr hp, rfl⟩⟩⟩⟩

/-- Every output of MAP_FP2_TO_G2 has 256 bytes. -/
theorem bls12MapFp2ToG2_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12MapFp2ToG2 data gas = .ok out) :
    out.size = 256 := by
  simp only [bls12MapFp2ToG2, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  repeat obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  simp [ByteArray.size, length_padG2_g2ToBytes]

end EthLib.Execution.Evm.Precompiles.Bls12381

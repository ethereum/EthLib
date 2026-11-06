module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding

/-!
# Proofs: `Evm.Precompiles.Bls12381.G1`

- G1ADD rejects any length other than 256 bytes before it charges gas, and then runs out of gas below its price.
- With enough gas, G1ADD succeeds exactly when both halves decode, and returns the encoded sum.
- Every encoded G1 point, and so every output of G1ADD and G1MSM, has 128 bytes.
- G1MSM rejects an empty input or a length that is not a whole number of 160-byte pairs.
- Its discount never raises the price above that of `k` separate products.
- MAP_FP_TO_G1 rejects any length other than 64 bytes before it charges gas, and every output has 128 bytes.
- With enough gas, it succeeds exactly when the field element decodes and its map succeeds.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bind_ok_iff mapError_ok_iff natToBytes_length)
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

/-- G1ADD succeeds exactly on 256 bytes, with at least its price in gas.

Each 128-byte half must decode to a point, without the subgroup check.

The output is the padded encoding of the sum of the two points. -/
theorem bls12G1Add_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12G1Add data gas = .ok out ↔
      data.size = 256 ∧ GAS_G1ADD ≤ gas ∧
        ∃ raw0 raw1 p0 p1,
          unpadG1 (data.data.toList.take 128) = .ok raw0 ∧
          unpadG1 (data.data.toList.drop 128) = .ok raw1 ∧
          bytesToG1 raw0 false = .ok p0 ∧
          bytesToG1 raw1 false = .ok p1 ∧
          out = ⟨(padG1 (g1ToBytes (G1.add p0 p1))).toArray⟩ := by
  by_cases hsize : data.size ≠ 256
  · simp [bls12G1Add_invalidInputLength hsize gas, hsize]
  · have hsize' : data.size = 256 := Decidable.not_not.mp hsize
    by_cases hgas : gas < GAS_G1ADD
    · simp [bls12G1Add_outOfGas hsize' hgas, hsize', Nat.not_le.mpr hgas]
    · simp only [bls12G1Add, hsize', ne_eq, not_true_eq_false, ↓reduceIte, hgas,
        Nat.not_lt.mp hgas, true_and, bind, Except.bind, pure, Except.pure]
      cases hu0 : unpadG1 (data.data.toList.take 128) <;>
        cases hu1 : unpadG1 (data.data.toList.drop 128) <;> simp
      rename_i raw0 raw1
      cases hp0 : bytesToG1 raw0 false <;>
        cases hp1 : bytesToG1 raw1 false <;> simp [eq_comm]

/-- Every output of G1ADD has 128 bytes. -/
theorem bls12G1Add_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G1Add data gas = .ok out) :
    out.size = 128 := by
  obtain ⟨-, -, -, -, p0, p1, -, -, -, -, rfl⟩ := (bls12G1Add_eq_ok_iff data gas out).mp h
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
    {gas : Nat} (hgas : gas < bls12G1MsmGas (data.size / LENGTH_PER_PAIR_G1)) :
    bls12G1Msm data gas =
      .error (.outOfGas (bls12G1MsmGas (data.size / LENGTH_PER_PAIR_G1)) gas) := by
  unfold bls12G1Msm
  rw [ite_eq_right_of_eq_false _ _ (eq_false hsize)]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true hgas)]
  rfl

/-- G1MSM succeeds exactly on a whole, nonzero number `k` of 160-byte pairs, with its price in gas.

The padding of every point must be zero, and the sum of the pairs must succeed.

The output is the padded encoding of that sum. -/
theorem bls12G1Msm_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12G1Msm data gas = .ok out ↔
      ¬(data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G1 ≠ 0) ∧
        bls12G1MsmGas (data.size / LENGTH_PER_PAIR_G1) ≤ gas ∧
        ∃ pairs q,
          (chunks LENGTH_PER_PAIR_G1 (data.size / LENGTH_PER_PAIR_G1) data.data.toList).mapM
              (fun pair => do return (← unpadG1 (pair.take 128), pair.drop 128)) = .ok pairs ∧
            g1Msm pairs = .ok q ∧ out = ⟨(padG1 (g1ToBytes q)).toArray⟩ := by
  by_cases hsize : data.size = 0 ∨ data.size % LENGTH_PER_PAIR_G1 ≠ 0
  · rw [bls12G1Msm_invalidInputLength hsize gas]
    exact iff_of_false (by simp) fun h => h.1 hsize
  · by_cases hgas : gas < bls12G1MsmGas (data.size / LENGTH_PER_PAIR_G1)
    · rw [bls12G1Msm_outOfGas hsize hgas]
      exact iff_of_false (by simp) fun h => absurd h.2.1 (Nat.not_le.mpr hgas)
    · unfold bls12G1Msm
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

/-- Every output of G1MSM has 128 bytes. -/
theorem bls12G1Msm_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12G1Msm data gas = .ok out) :
    out.size = 128 := by
  simp only [bls12G1Msm, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
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
theorem bls12G1MsmGas_le (k : Nat) : bls12G1MsmGas k ≤ k * GAS_G1MUL := by
  unfold bls12G1MsmGas
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

/-- MAP_FP_TO_G1 succeeds exactly on 64 bytes, with at least its price in gas.

The padding must be zero, and the field element must be below the modulus.

The map of that element to the curve must succeed.

The output is the padded encoding of the mapped point. -/
theorem bls12MapFpToG1_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12MapFpToG1 data gas = .ok out ↔
      data.size = 64 ∧ GAS_G1MAP ≤ gas ∧
        ∃ raw u P, unpadFp data.data.toList = .ok raw ∧ bytesToFieldElement raw = .ok u ∧
          Cryptography.Bls.MapToCurve.mapToG1 u = .ok P ∧
          out = ⟨(padG1 (g1ToBytes P)).toArray⟩ := by
  by_cases hsize : data.size ≠ 64
  · rw [bls12MapFpToG1_invalidInputLength hsize gas]
    exact iff_of_false (by simp) fun h => hsize h.1
  · have hsize' : data.size = 64 := Decidable.not_not.mp hsize
    by_cases hgas : gas < GAS_G1MAP
    · rw [bls12MapFpToG1_outOfGas hsize' hgas]
      exact iff_of_false (by simp) fun h => absurd h.2.1 (Nat.not_le.mpr hgas)
    · simp only [bls12MapFpToG1, hgas, ↓reduceIte, hsize', Nat.not_lt.mp hgas, true_and]
      constructor
      · intro h
        obtain ⟨raw, hr, h⟩ := bind_ok_iff.mp h
        obtain ⟨u, hu, h⟩ := bind_ok_iff.mp h
        obtain ⟨P, hp, h⟩ := bind_ok_iff.mp h
        exact ⟨raw, u, P, hr, hu, mapError_ok_iff.mp hp, (Except.ok.inj h).symm⟩
      · rintro ⟨raw, u, P, hr, hu, hp, rfl⟩
        exact bind_ok_iff.mpr ⟨raw, hr, bind_ok_iff.mpr ⟨u, hu,
          bind_ok_iff.mpr ⟨P, mapError_ok_iff.mpr hp, rfl⟩⟩⟩

/-- Every output of MAP_FP_TO_G1 has 128 bytes. -/
theorem bls12MapFpToG1_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : bls12MapFpToG1 data gas = .ok out) :
    out.size = 128 := by
  simp only [bls12MapFpToG1, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  repeat obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  simp [ByteArray.size, length_padG1_g1ToBytes]

end EthLib.Execution.Evm.Precompiles.Bls12381

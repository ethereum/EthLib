module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Evm.Precompiles.Bls12381.G2
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G1
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G2
import EthLib.Cryptography.Proofs.Bls.PairingCongr
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.RoundTrip

/-!
# Proofs: G1ADD and G2ADD of EIP-2537 compute group addition

- Every decoded point is on its curve, and passes the subgroup check when requested.
- G1ADD and G2ADD return the encoding of the sum of their two decoded points.
- Both succeed on the encodings of every two points on the curve, with enough gas.

The sum is taken in the full group of points of each curve, as Mathlib defines it.

Neither precompile checks that its inputs lie in the subgroup.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes_length)
open EthLib.Cryptography.Bls (Fp Fp2 G1 G2)

/-! ## Validity of decoded points -/

/-- A decoded G1 point is valid, and lies in the subgroup when the check is enabled. -/
theorem bytesToG1_valid {raw : List UInt8} {subgroupCheck : Bool} {p : G1}
    (h : bytesToG1 raw subgroupCheck = .ok p) :
    G1.Valid p ∧ (subgroupCheck = true → G1.inSubgroup p = true) := by
  simp only [bytesToG1, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  cases hx : bytesToFieldElement (raw.take 48) with
  | error => simp [hx] at h
  | ok x =>
    cases hy : bytesToFieldElement (raw.drop 48) with
    | error => simp [hx, hy] at h
    | ok y =>
      simp only [hx, hy] at h
      split at h
      · -- Both coordinates are zero: the point at infinity is valid and in the subgroup.
        cases h
        exact ⟨G1.valid_zero, fun _ =>
          (G1.inSubgroup_iff_modulus_smul_eq_zero G1.valid_zero).mpr
            (by rw [G1.toPoint_zero, nsmul_zero])⟩
      · split at h
        · cases h
        · rename_i hnot
          have hon : onCurveG1 x y = true := by
            cases hc : onCurveG1 x y
            · simp [hc] at hnot
            · rfl
          have heq : (y : ZMod Fp.modulus) * y = x * x * x + Fp.ofNat 4 :=
            beq_iff_eq.mp hon
          split at h
          · cases h
          · rename_i hsub
            cases h
            refine ⟨G1.valid_of_affine_eq heq, fun hc => ?_⟩
            cases hs : G1.inSubgroup ⟨x, y, Fp.one⟩
            · exfalso
              apply hsub
              rw [hc, hs]
              rfl
            · rfl

/-- A decoded G2 point is valid, and lies in the subgroup when the check is enabled. -/
theorem bytesToG2_valid {raw : List UInt8} {subgroupCheck : Bool} {p : G2}
    (h : bytesToG2 raw subgroupCheck = .ok p) :
    G2.Valid p ∧ (subgroupCheck = true → G2.inSubgroup p = true) := by
  simp only [bytesToG2, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  cases hx : bytesToFq2 (raw.take 96) with
  | error => simp [hx] at h
  | ok x =>
    cases hy : bytesToFq2 (raw.drop 96) with
    | error => simp [hx, hy] at h
    | ok y =>
      simp only [hx, hy] at h
      split at h
      · -- Every coordinate is zero: the point at infinity is valid and in the subgroup.
        cases h
        exact ⟨G2.valid_zero, fun _ =>
          (G2.inSubgroup_iff_modulus_smul_eq_zero G2.valid_zero).mpr
            (by rw [G2.toPoint_zero, nsmul_zero])⟩
      · split at h
        · cases h
        · rename_i hnot
          have hon : onCurveG2 x y = true := by
            cases hc : onCurveG2 x y
            · simp [hc] at hnot
            · rfl
          have heq : y * y = x * x * x + G2.bTwist :=
            beq_iff_eq.mp hon
          split at h
          · cases h
          · rename_i hsub
            cases h
            refine ⟨G2.valid_of_affine_equation heq, fun hc => ?_⟩
            cases hs : G2.inSubgroup ⟨x, y, Fp2.one⟩
            · exfalso
              apply hsub
              rw [hc, hs]
              rfl
            · rfl

/-! ## G1ADD and G2ADD -/

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

/-- A call of G1ADD that succeeds returns the encoding of the sum of its two decoded points.

That sum is valid, and it maps to the sum of their points on the curve. -/
theorem bls12G1Add_toPoint {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12G1Add data gas = .ok out) :
    data.size = 256 ∧ GAS_G1ADD ≤ gas ∧
      ∃ raw0 raw1 p0 p1,
        unpadG1 (data.data.toList.take 128) = .ok raw0 ∧
        unpadG1 (data.data.toList.drop 128) = .ok raw1 ∧
        bytesToG1 raw0 false = .ok p0 ∧
        bytesToG1 raw1 false = .ok p1 ∧
        out = ⟨(padG1 (g1ToBytes (G1.add p0 p1))).toArray⟩ ∧
        G1.Valid (G1.add p0 p1) ∧
        G1.toPoint (G1.add p0 p1) = G1.toPoint p0 + G1.toPoint p1 := by
  obtain ⟨hsize, hgas, raw0, raw1, p0, p1, hu0, hu1, hp0, hp1, hout⟩ :=
    (bls12G1Add_eq_ok_iff data gas out).mp h
  have hv0 := (bytesToG1_valid hp0).1
  have hv1 := (bytesToG1_valid hp1).1
  exact ⟨hsize, hgas, raw0, raw1, p0, p1, hu0, hu1, hp0, hp1, hout,
    G1.valid_add hv0 hv1, G1.toPoint_add hv0 hv1⟩

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

/-- A call of G2ADD that succeeds returns the encoding of the sum of its two decoded points.

That sum is valid, and it maps to the sum of their points on the curve. -/
theorem bls12G2Add_toPoint {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12G2Add data gas = .ok out) :
    data.size = 512 ∧ GAS_G2ADD ≤ gas ∧
      ∃ raw0 raw1 p0 p1,
        unpadG2 (data.data.toList.take 256) = .ok raw0 ∧
        unpadG2 (data.data.toList.drop 256) = .ok raw1 ∧
        bytesToG2 raw0 false = .ok p0 ∧
        bytesToG2 raw1 false = .ok p1 ∧
        out = ⟨(padG2 (g2ToBytes (G2.add p0 p1))).toArray⟩ ∧
        G2.Valid (G2.add p0 p1) ∧
        G2.toPoint (G2.add p0 p1) = G2.toPoint p0 + G2.toPoint p1 := by
  obtain ⟨hsize, hgas, raw0, raw1, p0, p1, hu0, hu1, hp0, hp1, hout⟩ :=
    (bls12G2Add_eq_ok_iff data gas out).mp h
  have hv0 := (bytesToG2_valid hp0).1
  have hv1 := (bytesToG2_valid hp1).1
  exact ⟨hsize, hgas, raw0, raw1, p0, p1, hu0, hu1, hp0, hp1, hout,
    G2.valid_add hv0 hv1, G2.toPoint_add hv0 hv1⟩

/-! ## Every two points on the curve -/

/-- G1ADD on the encodings of two valid points, with enough gas, returns the encoding of their sum.

Neither point needs to lie in the subgroup. -/
theorem bls12G1Add_g1ToBytes {p0 p1 : G1} (h0 : G1.Valid p0) (h1 : G1.Valid p1) {gas : Nat}
    (hgas : GAS_G1ADD ≤ gas) :
    bls12G1Add ⟨(padG1 (g1ToBytes p0) ++ padG1 (g1ToBytes p1)).toArray⟩ gas =
      .ok ⟨(padG1 (g1ToBytes (G1.add p0 p1))).toArray⟩ := by
  obtain ⟨q0, hq0, ht0⟩ := bytesToG1_g1ToBytes h0 (subgroupCheck := false) (fun h => by cases h)
  obtain ⟨q1, hq1, ht1⟩ := bytesToG1_g1ToBytes h1 (subgroupCheck := false) (fun h => by cases h)
  have hv0 := (bytesToG1_valid hq0).1
  have hv1 := (bytesToG1_valid hq1).1
  -- The decoded points may differ from the given ones, but their sums have one affine form.
  have hsum : g1ToBytes (G1.add q0 q1) = g1ToBytes (G1.add p0 p1) := by
    have h := (G1.toAffine_congr (G1.valid_add hv0 hv1) (G1.valid_add h0 h1)
      (by rw [G1.toPoint_add hv0 hv1, G1.toPoint_add h0 h1, ht0, ht1])).2
    unfold g1ToBytes
    rw [h]
  have hlen : (padG1 (g1ToBytes p0)).length = 128 := length_padG1_g1ToBytes p0
  have hraw (p : G1) : (g1ToBytes p).length = 96 := by simp [g1ToBytes, natToBytes_length]
  rw [← hsum]
  refine (bls12G1Add_eq_ok_iff _ _ _).mpr ⟨?_, hgas, g1ToBytes p0, g1ToBytes p1, q0, q1,
    ?_, ?_, hq0, hq1, rfl⟩
  · simp [ByteArray.size, hlen, length_padG1_g1ToBytes]
  · simpa [List.take_left' hlen] using unpadG1_padG1 (hraw p0)
  · simpa [List.drop_left' hlen] using unpadG1_padG1 (hraw p1)

/-- G2ADD on the encodings of two valid points, with enough gas, returns the encoding of their sum.

Neither point needs to lie in the subgroup. -/
theorem bls12G2Add_g2ToBytes {p0 p1 : G2} (h0 : G2.Valid p0) (h1 : G2.Valid p1) {gas : Nat}
    (hgas : GAS_G2ADD ≤ gas) :
    bls12G2Add ⟨(padG2 (g2ToBytes p0) ++ padG2 (g2ToBytes p1)).toArray⟩ gas =
      .ok ⟨(padG2 (g2ToBytes (G2.add p0 p1))).toArray⟩ := by
  obtain ⟨q0, hq0, ht0⟩ := bytesToG2_g2ToBytes h0 (subgroupCheck := false) (fun h => by cases h)
  obtain ⟨q1, hq1, ht1⟩ := bytesToG2_g2ToBytes h1 (subgroupCheck := false) (fun h => by cases h)
  have hv0 := (bytesToG2_valid hq0).1
  have hv1 := (bytesToG2_valid hq1).1
  -- The decoded points may differ from the given ones, but their sums have one affine form.
  have hsum : g2ToBytes (G2.add q0 q1) = g2ToBytes (G2.add p0 p1) := by
    have h := (G2.toAffine_congr (G2.valid_add hv0 hv1) (G2.valid_add h0 h1)
      (by rw [G2.toPoint_add hv0 hv1, G2.toPoint_add h0 h1, ht0, ht1])).2
    unfold g2ToBytes
    rw [h]
  have hlen : (padG2 (g2ToBytes p0)).length = 256 := length_padG2_g2ToBytes p0
  have hraw (p : G2) : (g2ToBytes p).length = 192 := by simp [g2ToBytes, natToBytes_length]
  rw [← hsum]
  refine (bls12G2Add_eq_ok_iff _ _ _).mpr ⟨?_, hgas, g2ToBytes p0, g2ToBytes p1, q0, q1,
    ?_, ?_, hq0, hq1, rfl⟩
  · simp [ByteArray.size, hlen, length_padG2_g2ToBytes]
  · simpa [List.take_left' hlen] using unpadG2_padG2 (hraw p0)
  · simpa [List.drop_left' hlen] using unpadG2_padG2 (hraw p1)

/-! ## The generators -/

/-- G1ADD succeeds on two copies of the G1 generator, with gas equal to its price.

Its output decodes to `g_1 + g_1`. -/
theorem exists_bls12G1Add_ok :
    let enc := padG1 (g1ToBytes G1.generator)
    let data : ByteArray := ⟨(enc ++ enc).toArray⟩
    ∃ out raw q,
      bls12G1Add data GAS_G1ADD = .ok out ∧
      unpadG1 out.data.toList = .ok raw ∧
      bytesToG1 raw false = .ok q ∧
      G1.toPoint q = G1.toPoint G1.generator + G1.toPoint G1.generator := by
  have hg := G1.valid_generator
  have hsum := G1.valid_add hg hg
  obtain ⟨q, hq, hqt⟩ := bytesToG1_g1ToBytes hsum (subgroupCheck := false) (fun h => by cases h)
  refine ⟨_, g1ToBytes (G1.add G1.generator G1.generator), q,
    bls12G1Add_g1ToBytes hg hg (Nat.le_refl _), ?_, hq, ?_⟩
  · exact unpadG1_padG1 (by simp [g1ToBytes, natToBytes_length])
  · rw [hqt, G1.toPoint_add hg hg]

/-- G2ADD succeeds on two copies of the G2 generator, with gas equal to its price.

Its output decodes to `g_2 + g_2`. -/
theorem exists_bls12G2Add_ok :
    let enc := padG2 (g2ToBytes G2.generator)
    let data : ByteArray := ⟨(enc ++ enc).toArray⟩
    ∃ out raw q,
      bls12G2Add data GAS_G2ADD = .ok out ∧
      unpadG2 out.data.toList = .ok raw ∧
      bytesToG2 raw false = .ok q ∧
      G2.toPoint q = G2.toPoint G2.generator + G2.toPoint G2.generator := by
  have hg := G2.valid_generator
  have hsum := G2.valid_add hg hg
  obtain ⟨q, hq, hqt⟩ := bytesToG2_g2ToBytes hsum (subgroupCheck := false) (fun h => by cases h)
  refine ⟨_, g2ToBytes (G2.add G2.generator G2.generator), q,
    bls12G2Add_g2ToBytes hg hg (Nat.le_refl _), ?_, hq, ?_⟩
  · exact unpadG2_padG2 (by simp [g2ToBytes, natToBytes_length])
  · rw [hqt, G2.toPoint_add hg hg]

end EthLib.Execution.Evm.Precompiles.Bls12381

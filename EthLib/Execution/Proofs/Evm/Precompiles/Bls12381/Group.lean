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

/-- A decoded G1 point is valid. -/
theorem valid_of_bytesToG1_eq_ok {raw : List UInt8} {subgroupCheck : Bool} {p : G1}
    (h : bytesToG1 raw subgroupCheck = .ok p) : G1.Valid p := by
  obtain ⟨x, y, -, -, ⟨-, -, rfl⟩ | ⟨hon, -, rfl⟩⟩ := bytesToG1_eq_ok_iff.mp h
  · exact G1.valid_zero
  · have heq : (y : ZMod Fp.modulus) * y = x * x * x + Fp.ofNat 4 := beq_iff_eq.mp hon
    exact G1.valid_of_affine_eq heq

/-- A G1 point decoded with the subgroup check lies in the subgroup. -/
theorem inSubgroup_of_bytesToG1_eq_ok {raw : List UInt8} {p : G1}
    (h : bytesToG1 raw true = .ok p) : G1.inSubgroup p = true := by
  obtain ⟨x, y, -, -, ⟨-, -, rfl⟩ | ⟨-, hsub, rfl⟩⟩ := bytesToG1_eq_ok_iff.mp h
  · -- The point at infinity is in the subgroup.
    exact (G1.inSubgroup_iff_modulus_smul_eq_zero G1.valid_zero).mpr
      (by rw [G1.toPoint_zero, nsmul_zero])
  · exact hsub rfl

/-- A decoded G2 point is valid. -/
theorem valid_of_bytesToG2_eq_ok {raw : List UInt8} {subgroupCheck : Bool} {p : G2}
    (h : bytesToG2 raw subgroupCheck = .ok p) : G2.Valid p := by
  obtain ⟨x, y, -, -, ⟨-, -, -, -, rfl⟩ | ⟨hon, -, rfl⟩⟩ := bytesToG2_eq_ok_iff.mp h
  · exact G2.valid_zero
  · have heq : y * y = x * x * x + G2.bTwist := beq_iff_eq.mp hon
    exact G2.valid_of_affine_equation heq

/-- A G2 point decoded with the subgroup check lies in the subgroup. -/
theorem inSubgroup_of_bytesToG2_eq_ok {raw : List UInt8} {p : G2}
    (h : bytesToG2 raw true = .ok p) : G2.inSubgroup p = true := by
  obtain ⟨x, y, -, -, ⟨-, -, -, -, rfl⟩ | ⟨-, hsub, rfl⟩⟩ := bytesToG2_eq_ok_iff.mp h
  · -- The point at infinity is in the subgroup.
    exact (G2.inSubgroup_iff_modulus_smul_eq_zero G2.valid_zero).mpr
      (by rw [G2.toPoint_zero, nsmul_zero])
  · exact hsub rfl

/-- A decoded G1 point is valid, and lies in the subgroup when the check is enabled. -/
@[deprecated valid_of_bytesToG1_eq_ok +typeChanged (since := "2026-11-06")]
theorem bytesToG1_valid {raw : List UInt8} {subgroupCheck : Bool} {p : G1}
    (h : bytesToG1 raw subgroupCheck = .ok p) :
    G1.Valid p ∧ (subgroupCheck = true → G1.inSubgroup p = true) :=
  ⟨valid_of_bytesToG1_eq_ok h, fun hc => inSubgroup_of_bytesToG1_eq_ok (hc ▸ h)⟩

/-- A decoded G2 point is valid, and lies in the subgroup when the check is enabled. -/
@[deprecated valid_of_bytesToG2_eq_ok +typeChanged (since := "2026-11-06")]
theorem bytesToG2_valid {raw : List UInt8} {subgroupCheck : Bool} {p : G2}
    (h : bytesToG2 raw subgroupCheck = .ok p) :
    G2.Valid p ∧ (subgroupCheck = true → G2.inSubgroup p = true) :=
  ⟨valid_of_bytesToG2_eq_ok h, fun hc => inSubgroup_of_bytesToG2_eq_ok (hc ▸ h)⟩

/-! ## G1ADD and G2ADD -/

/-- The sum of two decoded G1 points maps to the sum of their points on the curve.

G1ADD returns the encoding of that sum, so it computes group addition. -/
theorem toPoint_add_of_bytesToG1_eq_ok {raw0 raw1 : List UInt8} {check0 check1 : Bool}
    {p0 p1 : G1} (h0 : bytesToG1 raw0 check0 = .ok p0) (h1 : bytesToG1 raw1 check1 = .ok p1) :
    G1.toPoint (G1.add p0 p1) = G1.toPoint p0 + G1.toPoint p1 :=
  G1.toPoint_add (valid_of_bytesToG1_eq_ok h0) (valid_of_bytesToG1_eq_ok h1)

/-- The sum of two decoded G2 points maps to the sum of their points on the curve.

G2ADD returns the encoding of that sum, so it computes group addition. -/
theorem toPoint_add_of_bytesToG2_eq_ok {raw0 raw1 : List UInt8} {check0 check1 : Bool}
    {p0 p1 : G2} (h0 : bytesToG2 raw0 check0 = .ok p0) (h1 : bytesToG2 raw1 check1 = .ok p1) :
    G2.toPoint (G2.add p0 p1) = G2.toPoint p0 + G2.toPoint p1 :=
  G2.toPoint_add (valid_of_bytesToG2_eq_ok h0) (valid_of_bytesToG2_eq_ok h1)

/-- A call of G1ADD that succeeds returns the encoding of the sum of its two decoded points.

That sum is valid, and it maps to the sum of their points on the curve. -/
@[deprecated toPoint_add_of_bytesToG1_eq_ok +typeChanged (since := "2026-11-06")]
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
  exact ⟨hsize, hgas, raw0, raw1, p0, p1, hu0, hu1, hp0, hp1, hout,
    G1.valid_add (valid_of_bytesToG1_eq_ok hp0) (valid_of_bytesToG1_eq_ok hp1),
    toPoint_add_of_bytesToG1_eq_ok hp0 hp1⟩

/-- A call of G2ADD that succeeds returns the encoding of the sum of its two decoded points.

That sum is valid, and it maps to the sum of their points on the curve. -/
@[deprecated toPoint_add_of_bytesToG2_eq_ok +typeChanged (since := "2026-11-06")]
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
  exact ⟨hsize, hgas, raw0, raw1, p0, p1, hu0, hu1, hp0, hp1, hout,
    G2.valid_add (valid_of_bytesToG2_eq_ok hp0) (valid_of_bytesToG2_eq_ok hp1),
    toPoint_add_of_bytesToG2_eq_ok hp0 hp1⟩

/-! ## Every two points on the curve -/

/-- G1ADD on the encodings of two valid points, with enough gas, returns the encoding of their sum.

Neither point needs to lie in the subgroup. -/
theorem bls12G1Add_g1ToBytes {p0 p1 : G1} (h0 : G1.Valid p0) (h1 : G1.Valid p1) {gas : Nat}
    (hgas : GAS_G1ADD ≤ gas) :
    bls12G1Add ⟨(padG1 (g1ToBytes p0) ++ padG1 (g1ToBytes p1)).toArray⟩ gas =
      .ok ⟨(padG1 (g1ToBytes (G1.add p0 p1))).toArray⟩ := by
  obtain ⟨q0, hq0, ht0⟩ := bytesToG1_g1ToBytes h0 (subgroupCheck := false) (fun h => by cases h)
  obtain ⟨q1, hq1, ht1⟩ := bytesToG1_g1ToBytes h1 (subgroupCheck := false) (fun h => by cases h)
  have hv0 := valid_of_bytesToG1_eq_ok hq0
  have hv1 := valid_of_bytesToG1_eq_ok hq1
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
  have hv0 := valid_of_bytesToG2_eq_ok hq0
  have hv1 := valid_of_bytesToG2_eq_ok hq1
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

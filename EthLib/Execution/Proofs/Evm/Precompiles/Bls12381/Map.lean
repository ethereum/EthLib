module

public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G2
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.RoundTrip
public import EthLib.Cryptography.Proofs.Bls.MapToCurve

/-!
# Proofs: MAP_FP_TO_G1 and MAP_FP2_TO_G2 of EIP-2537 land in the subgroup

- The maps of RFC 9380 succeed on every field element.
- So take the right length and enough gas.
  Each precompile then succeeds exactly when its padded field element decodes.
- Every output encodes a valid point of the subgroup of order `r`.
- That output passes the point decoder of EIP-2537 with the subgroup check.
- The padded encoding of every field element is accepted.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes natToBytes_length)
open EthLib.Cryptography.Bls (Fp Fp2 G1 G2)

/-! ## MAP_FP_TO_G1 -/

/-- MAP_FP_TO_G1 succeeds exactly on 64 bytes, with at least its price in gas.

The padding must be zero, and the field element must be below the modulus. -/
theorem bls12MapFpToG1_isOk_iff (data : ByteArray) (gas : Nat) :
    (∃ out, bls12MapFpToG1 data gas = .ok out) ↔
      data.size = 64 ∧ GAS_G1MAP ≤ gas ∧
        ∃ raw u, unpadFp data.data.toList = .ok raw ∧ bytesToFieldElement raw = .ok u := by
  constructor
  · rintro ⟨out, h⟩
    obtain ⟨hsize, hgas, raw, u, -, hr, hu, -⟩ := (bls12MapFpToG1_eq_ok_iff data gas out).mp h
    exact ⟨hsize, hgas, raw, u, hr, hu⟩
  · rintro ⟨hsize, hgas, raw, u, hr, hu⟩
    obtain ⟨P, hP⟩ := Cryptography.Bls.MapToCurve.mapToG1_ok u
    exact ⟨_, (bls12MapFpToG1_eq_ok_iff data gas _).mpr ⟨hsize, hgas, raw, u, P, hr, hu, hP, rfl⟩⟩

/-- Every output of MAP_FP_TO_G1 is the padded encoding of a valid point of the subgroup. -/
theorem inSubgroup_of_bls12MapFpToG1_eq_ok {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12MapFpToG1 data gas = .ok out) :
    ∃ P, G1.Valid P ∧ G1.inSubgroup P = true ∧ out = ⟨(padG1 (g1ToBytes P)).toArray⟩ := by
  obtain ⟨-, -, _, _, P, -, -, hP, rfl⟩ := (bls12MapFpToG1_eq_ok_iff data gas out).mp h
  obtain ⟨hvalid, hsub⟩ := Cryptography.Bls.MapToCurve.mapToG1_inSubgroup hP
  exact ⟨P, hvalid, hsub, rfl⟩

/-- Every output of MAP_FP_TO_G1 decodes, with the subgroup check, to the point it encodes. -/
theorem bytesToG1_of_bls12MapFpToG1_eq_ok {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12MapFpToG1 data gas = .ok out) :
    ∃ P raw q, out = ⟨(padG1 (g1ToBytes P)).toArray⟩ ∧ unpadG1 out.data.toList = .ok raw ∧
      bytesToG1 raw true = .ok q ∧ G1.toPoint q = G1.toPoint P := by
  obtain ⟨P, hvalid, hsub, rfl⟩ := inSubgroup_of_bls12MapFpToG1_eq_ok h
  obtain ⟨q, hq, hqP⟩ := bytesToG1_g1ToBytes hvalid fun _ => hsub
  have hlength : (g1ToBytes P).length = 96 := by simp [g1ToBytes, natToBytes_length]
  exact ⟨P, _, q, rfl, by rw [List.toList_toArray, unpadG1_padG1 hlength], hq, hqP⟩

/-- MAP_FP_TO_G1 maps the padded encoding of every field element `u`, with enough gas. -/
theorem bls12MapFpToG1_pad (u : Fp) {gas : Nat} (hgas : GAS_G1MAP ≤ gas) :
    ∃ P, Cryptography.Bls.MapToCurve.mapToG1 u = .ok P ∧
      bls12MapFpToG1 ⟨(zeroPad ++ natToBytes 48 u.val).toArray⟩ gas =
        .ok ⟨(padG1 (g1ToBytes P)).toArray⟩ := by
  obtain ⟨P, hP⟩ := Cryptography.Bls.MapToCurve.mapToG1_ok u
  refine ⟨P, hP, (bls12MapFpToG1_eq_ok_iff _ gas _).mpr
    ⟨?_, hgas, _, u, P, unpadFp_pad _, bytesToFieldElement_natToBytes u, hP, rfl⟩⟩
  simp [ByteArray.size, zeroPad, PAD_BYTES, natToBytes_length]

/-! ## MAP_FP2_TO_G2 -/

/-- MAP_FP2_TO_G2 succeeds exactly on 128 bytes, with at least its price in gas.

Both paddings must be zero, and both field elements must be below the modulus. -/
theorem bls12MapFp2ToG2_isOk_iff (data : ByteArray) (gas : Nat) :
    (∃ out, bls12MapFp2ToG2 data gas = .ok out) ↔
      data.size = 128 ∧ GAS_G2MAP ≤ gas ∧
        ∃ c0 c1 u, unpadFp (data.data.toList.take 64) = .ok c0 ∧
          unpadFp (data.data.toList.drop 64) = .ok c1 ∧ bytesToFq2 (c0 ++ c1) = .ok u := by
  constructor
  · rintro ⟨out, h⟩
    obtain ⟨hsize, hgas, c0, c1, u, -, h0, h1, hu, -⟩ :=
      (bls12MapFp2ToG2_eq_ok_iff data gas out).mp h
    exact ⟨hsize, hgas, c0, c1, u, h0, h1, hu⟩
  · rintro ⟨hsize, hgas, c0, c1, u, h0, h1, hu⟩
    obtain ⟨P, hP⟩ := Cryptography.Bls.MapToCurve.mapToG2_ok u
    exact ⟨_, (bls12MapFp2ToG2_eq_ok_iff data gas _).mpr
      ⟨hsize, hgas, c0, c1, u, P, h0, h1, hu, hP, rfl⟩⟩

/-- Every output of MAP_FP2_TO_G2 is the padded encoding of a valid point of the subgroup. -/
theorem inSubgroup_of_bls12MapFp2ToG2_eq_ok {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12MapFp2ToG2 data gas = .ok out) :
    ∃ P, G2.Valid P ∧ G2.inSubgroup P = true ∧ out = ⟨(padG2 (g2ToBytes P)).toArray⟩ := by
  obtain ⟨-, -, _, _, _, P, -, -, -, hP, rfl⟩ := (bls12MapFp2ToG2_eq_ok_iff data gas out).mp h
  obtain ⟨hvalid, hsub⟩ := Cryptography.Bls.MapToCurve.mapToG2_inSubgroup hP
  exact ⟨P, hvalid, hsub, rfl⟩

/-- Every output of MAP_FP2_TO_G2 decodes, with the subgroup check, to the point it encodes. -/
theorem bytesToG2_of_bls12MapFp2ToG2_eq_ok {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12MapFp2ToG2 data gas = .ok out) :
    ∃ P raw q, out = ⟨(padG2 (g2ToBytes P)).toArray⟩ ∧ unpadG2 out.data.toList = .ok raw ∧
      bytesToG2 raw true = .ok q ∧ G2.toPoint q = G2.toPoint P := by
  obtain ⟨P, hvalid, hsub, rfl⟩ := inSubgroup_of_bls12MapFp2ToG2_eq_ok h
  obtain ⟨q, hq, hqP⟩ := bytesToG2_g2ToBytes hvalid fun _ => hsub
  have hlength : (g2ToBytes P).length = 192 := by simp [g2ToBytes, natToBytes_length]
  exact ⟨P, _, q, rfl, by rw [List.toList_toArray, unpadG2_padG2 hlength], hq, hqP⟩

/-- MAP_FP2_TO_G2 maps the padded encoding of every element `u` of `Fp2`, with enough gas.

The encoding puts `c0` first. -/
theorem bls12MapFp2ToG2_pad (u : Fp2) {gas : Nat} (hgas : GAS_G2MAP ≤ gas) :
    ∃ P, Cryptography.Bls.MapToCurve.mapToG2 u = .ok P ∧
      bls12MapFp2ToG2
          ⟨(zeroPad ++ natToBytes 48 u.c0.val ++ (zeroPad ++ natToBytes 48 u.c1.val)).toArray⟩ gas =
        .ok ⟨(padG2 (g2ToBytes P)).toArray⟩ := by
  obtain ⟨P, hP⟩ := Cryptography.Bls.MapToCurve.mapToG2_ok u
  have hlength : (zeroPad ++ natToBytes 48 u.c0.val).length = 64 := by
    simp [zeroPad, PAD_BYTES, natToBytes_length]
  have hfq2 : bytesToFq2 (natToBytes 48 u.c0.val ++ natToBytes 48 u.c1.val) = .ok u := by
    have h48 : (natToBytes 48 u.c0.val).length = 48 := natToBytes_length _ _
    simp only [bytesToFq2, List.take_left' h48, List.drop_left' h48,
      bytesToFieldElement_natToBytes]
    rfl
  refine ⟨P, hP, (bls12MapFp2ToG2_eq_ok_iff _ gas _).mpr
    ⟨?_, hgas, _, _, u, P, ?_, ?_, hfq2, hP, rfl⟩⟩
  · simp [ByteArray.size, zeroPad, PAD_BYTES, natToBytes_length]
  · rw [List.toList_toArray, List.take_left' hlength, unpadFp_pad]
  · rw [List.toList_toArray, List.drop_left' hlength, unpadFp_pad]

end EthLib.Execution.Evm.Precompiles.Bls12381

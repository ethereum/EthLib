module

public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Encoding
public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G1SubgroupSpan
public import EthLib.Cryptography.Proofs.Bls.G2Compress
public import EthLib.Cryptography.Proofs.Bls.G2Subgroup
public import EthLib.Cryptography.Proofs.Bls.G2Validity
public import EthLib.Cryptography.Proofs.Bls.KeyValidate

/-!
# Proofs: the point round trips of EIP-2537

A point has many Jacobian representatives `(X, Y, Z)`, and the encoding keeps only its affine form.

So decoding the encoding of a point on the curve gives a point equal to it in the group.

With the subgroup check, the same holds for a point of the subgroup.

A decoded G2 point encodes back to its bytes, so that encoding is canonical.

The group and the curve are those of Mathlib, so this file imports Mathlib.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (natToBytes)
open EthLib.Cryptography.Bls (Fp Fp2 G1 G2)

/-- Decoding the encoding of a G1 point on the curve gives the same group element.

With the subgroup check, the point must be in the subgroup. -/
theorem bytesToG1_g1ToBytes {p : G1} (hp : G1.Valid p) {subgroupCheck : Bool}
    (hsub : subgroupCheck = true → G1.inSubgroup p = true) :
    ∃ q, bytesToG1 (g1ToBytes p) subgroupCheck = .ok q ∧ G1.toPoint q = G1.toPoint p := by
  by_cases hinf : p.z.isZero = true
  · -- The point at infinity encodes as zeros, which decode as the point at infinity.
    refine ⟨G1.zero, by rw [g1ToBytes_of_isZero hinf]; exact bytesToG1_zeros _, ?_⟩
    rw [G1.toPoint_zero, (G1.isInfinity_eq_true_iff_toPoint_eq_zero hp).mp hinf]
  · rcases hpa : p.toAffine with ⟨x, y⟩
    -- The affine form is on the curve, and it is the same group element as `p`.
    have heq := G1.affine_sqrt_witness hp hinf
    rw [hpa] at heq
    have hq : G1.toPoint ⟨x, y, Fp.one⟩ = G1.toPoint p := by
      have := G1.toPoint_affine_normalize hinf
      rwa [hpa] at this
    have hvalid := G1.valid_of_affine_eq heq
    refine ⟨⟨x, y, Fp.one⟩, ?_, hq⟩
    have henc : g1ToBytes p = natToBytes 48 x.val ++ natToBytes 48 y.val := by
      simp [g1ToBytes, hpa]
    rw [henc]
    refine bytesToG1_affine (beq_iff_eq.mpr heq) fun hc => ?_
    -- Membership of the subgroup depends only on the group element.
    rw [G1.inSubgroup_iff_modulus_smul_eq_zero hvalid, hq,
      ← G1.inSubgroup_iff_modulus_smul_eq_zero hp]
    exact hsub hc

/-- Decoding the encoding of a G2 point on the twist gives the same group element.

With the subgroup check, the point must be in the subgroup. -/
theorem bytesToG2_g2ToBytes {p : G2} (hp : G2.Valid p) {subgroupCheck : Bool}
    (hsub : subgroupCheck = true → G2.inSubgroup p = true) :
    ∃ q, bytesToG2 (g2ToBytes p) subgroupCheck = .ok q ∧ G2.toPoint q = G2.toPoint p := by
  by_cases hinf : p.isInfinity = true
  · -- The point at infinity encodes as zeros, which decode as the point at infinity.
    refine ⟨G2.zero, by rw [g2ToBytes_of_isZero hinf]; exact bytesToG2_zeros _, ?_⟩
    rw [G2.toPoint_zero, (G2.isInfinity_eq_true_iff_toPoint_eq_zero hp).mp hinf]
  · rcases hpa : p.toAffine with ⟨x, y⟩
    -- The affine form is on the twist, and it is the same group element as `p`.
    have heq := G2.affine_sqrt_witness (G2.isOnTwist_of_valid hp) hinf
    rw [hpa] at heq
    have hvalid := G2.valid_of_affine_equation heq
    have hq : G2.toPoint ⟨x, y, Fp2.one⟩ = G2.toPoint p := by
      have := G2.projectiveEq_toAffine hinf
      rw [hpa] at this
      exact (G2.projectiveEq_eq_true_iff_toPoint_eq hvalid hp).mp this
    refine ⟨⟨x, y, Fp2.one⟩, ?_, hq⟩
    have henc : g2ToBytes p = (natToBytes 48 x.c0.val ++ natToBytes 48 x.c1.val) ++
        (natToBytes 48 y.c0.val ++ natToBytes 48 y.c1.val) := by
      simp [g2ToBytes, hpa]
    rw [henc]
    refine bytesToG2_affine (beq_iff_eq.mpr heq) fun hc => ?_
    -- Membership of the subgroup depends only on the group element.
    rw [G2.inSubgroup_iff_modulus_smul_eq_zero hvalid, hq,
      ← G2.inSubgroup_iff_modulus_smul_eq_zero hp]
    exact hsub hc

-- The kernel compares 192 bytes one by one, deeper than the default recursion limit.
set_option maxRecDepth 8000 in
/-- A decoded G2 point encodes back to the 192 bytes it came from: the encoding is canonical. -/
theorem g2ToBytes_bytesToG2 {raw : List UInt8} (hlength : raw.length = 192) {subgroupCheck : Bool}
    {p : G2} (h : bytesToG2 raw subgroupCheck = .ok p) : g2ToBytes p = raw := by
  obtain ⟨x, y, hx, hy, hcase⟩ := bytesToG2_eq_ok_iff.mp h
  have hxb := natToBytes_bytesToFq2 (by simp [hlength]) hx
  have hyb := natToBytes_bytesToFq2 (by simp [hlength]) hy
  rcases hcase with ⟨h0, h1, h2, h3, rfl⟩ | ⟨-, -, rfl⟩
  · -- Every coordinate is zero: the point at infinity, and the bytes are all zero.
    rw [g2ToBytes_of_isZero (by decide), ← List.take_append_drop 96 raw, ← hxb, ← hyb]
    rw [h0, h1, h2, h3]
    rfl
  · simp only [g2ToBytes, G2.toAffine_of_z_one]
    rw [List.append_assoc, hxb, hyb, List.take_append_drop]

end EthLib.Execution.Evm.Precompiles.Bls12381

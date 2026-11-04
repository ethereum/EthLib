module

public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128
public import EthLib.Cryptography.Proofs.AltBn128.Curve

/-!
# Proofs: ECADD and ECMUL compute the group operations

ECADD returns the sum of its two points in the group of the curve.

ECMUL returns its point times its scalar, read as a 32-byte integer and not reduced.

The group is the one of Mathlib on `y^2 = x^3 + 3`, so this file imports Mathlib.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Cryptography.AltBn128
open EthLib.Execution.Evm (bufferRead)

/-- A call of ECADD that succeeds returns the group sum of its two points. -/
theorem ecadd_toPoint {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecadd data gas = .ok out) :
    ∃ p0 p1, bytesToG1 (bufferRead data 0 64) = .ok p0 ∧
      bytesToG1 (bufferRead data 64 64) = .ok p1 ∧ out = ⟨(g1ToBytes (p0 + p1)).toArray⟩ ∧
      (p0 + p1).toPoint = p0.toPoint + p1.toPoint := by
  obtain ⟨-, p0, p1, h0, h1, hout⟩ := (ecadd_eq_ok_iff data gas out).mp h
  exact ⟨p0, p1, h0, h1, hout,
    Point.toPoint_add (bytesToG1_isOnCurve h0) (bytesToG1_isOnCurve h1)⟩

/-- A call of ECMUL that succeeds returns its point times its scalar in the group. -/
theorem ecmul_toPoint {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecmul data gas = .ok out) :
    let n := Base.bytesToNat (bufferRead data 64 32)
    ∃ p0, bytesToG1 (bufferRead data 0 64) = .ok p0 ∧
      out = ⟨(g1ToBytes (Point.mulBits 256 n p0)).toArray⟩ ∧
      (Point.mulBits 256 n p0).toPoint = n • p0.toPoint := by
  obtain ⟨-, p0, h0, hout⟩ := (ecmul_eq_ok_iff data gas out).mp h
  refine ⟨p0, h0, hout, Point.toPoint_mulBits 256 _ (bytesToG1_isOnCurve h0) ?_⟩
  -- A 32-byte scalar is below `256 ^ 32 = 2 ^ 256`.
  have hlt := Base.bytesToNat_lt (bufferRead data 64 32)
  rw [bufferRead_length] at hlt
  simpa using hlt

end EthLib.Execution.Evm.Precompiles.AltBn128

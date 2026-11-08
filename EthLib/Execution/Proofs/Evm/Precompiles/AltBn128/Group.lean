module

public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128.Basic
public import EthLib.Execution.Proofs.Evm.Precompiles.AltBn128.Encoding
public import EthLib.Cryptography.Proofs.AltBn128.Curve

/-!
# Proofs: ECADD and ECMUL compute the group operations

ECADD returns the sum of its two points in the group of the curve.

ECMUL returns its point times its scalar, read as a 32-byte integer and not reduced.

The output of each call decodes to that sum or that product.

So a later call accepts it as a point of `G_1`.

The group is the one of Mathlib on `y^2 = x^3 + 3`, so this file imports Mathlib.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Cryptography.AltBn128
open EthLib.Execution.Evm (bufferRead)

/-- A call of ECADD that succeeds returns the group sum of its two points. -/
theorem ecadd_toPoint {fork : EthLib.Base.Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecadd fork data gas = .ok out) :
    ∃ p0 p1, bytesToG1 (bufferRead data 0 64) = .ok p0 ∧
      bytesToG1 (bufferRead data 64 64) = .ok p1 ∧ out = ⟨(g1ToBytes (p0 + p1)).toArray⟩ ∧
      (p0 + p1).toPoint = p0.toPoint + p1.toPoint := by
  obtain ⟨-, p0, p1, h0, h1, hout⟩ := (ecadd_eq_ok_iff fork data gas out).mp h
  exact ⟨p0, p1, h0, h1, hout,
    Point.toPoint_add (bytesToG1_isOnCurve h0) (bytesToG1_isOnCurve h1)⟩

/-- A call of ECMUL that succeeds returns its point times its scalar in the group. -/
theorem ecmul_toPoint {fork : EthLib.Base.Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecmul fork data gas = .ok out) :
    let n := Base.bytesToNat (bufferRead data 64 32)
    ∃ p0, bytesToG1 (bufferRead data 0 64) = .ok p0 ∧
      out = ⟨(g1ToBytes (Point.mulBits 256 n p0)).toArray⟩ ∧
      (Point.mulBits 256 n p0).toPoint = n • p0.toPoint := by
  obtain ⟨-, p0, h0, hout⟩ := (ecmul_eq_ok_iff fork data gas out).mp h
  refine ⟨p0, h0, hout, Point.toPoint_mulBits 256 _ (bytesToG1_isOnCurve h0) ?_⟩
  -- A 32-byte scalar is below `256 ^ 32 = 2 ^ 256`.
  have hlt := Base.bytesToNat_lt (bufferRead data 64 32)
  rw [bufferRead_length] at hlt
  simpa using hlt

/-! ## Each output is a point of `G_1` -/

/-- A read of the whole of a byte string from its start gives its bytes. -/
private theorem bufferRead_toArray (bytes : List UInt8) :
    bufferRead ⟨bytes.toArray⟩ 0 bytes.length = bytes := by
  simpa [ByteArray.size] using bufferRead_zero_size ⟨bytes.toArray⟩

/-- The output of a call of ECADD that succeeds, read as a point, is the sum of its two points. -/
theorem bytesToG1_ecadd {fork : EthLib.Base.Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    {p0 p1 : Point} (h : ecadd fork data gas = .ok out)
    (h0 : bytesToG1 (bufferRead data 0 64) = .ok p0)
    (h1 : bytesToG1 (bufferRead data 64 64) = .ok p1) :
    bytesToG1 (bufferRead out 0 64) = .ok (p0 + p1) := by
  obtain ⟨-, p0', p1', h0', h1', rfl⟩ := (ecadd_eq_ok_iff fork data gas out).mp h
  -- The decoder is a function, so the points of the call are the named ones.
  obtain rfl : p0' = p0 := Except.ok.inj (h0'.symm.trans h0)
  obtain rfl : p1' = p1 := Except.ok.inj (h1'.symm.trans h1)
  have hread := bufferRead_toArray (g1ToBytes (p0' + p1'))
  rw [length_g1ToBytes] at hread
  rw [hread]
  exact bytesToG1_g1ToBytes (Point.isOnCurve_add (bytesToG1_isOnCurve h0) (bytesToG1_isOnCurve h1))

/-- The output of a call of ECMUL that succeeds, read as a point, is its point times its scalar. -/
theorem bytesToG1_ecmul {fork : EthLib.Base.Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    {p0 : Point} (h : ecmul fork data gas = .ok out)
    (h0 : bytesToG1 (bufferRead data 0 64) = .ok p0) :
    bytesToG1 (bufferRead out 0 64) =
      .ok (Point.mulBits 256 (Base.bytesToNat (bufferRead data 64 32)) p0) := by
  obtain ⟨-, p0', h0', rfl⟩ := (ecmul_eq_ok_iff fork data gas out).mp h
  -- The decoder is a function, so the point of the call is the named one.
  obtain rfl : p0' = p0 := Except.ok.inj (h0'.symm.trans h0)
  have hread := bufferRead_toArray
    (g1ToBytes (Point.mulBits 256 (Base.bytesToNat (bufferRead data 64 32)) p0'))
  rw [length_g1ToBytes] at hread
  rw [hread]
  exact bytesToG1_g1ToBytes (Point.isOnCurve_mulBits _ _ (bytesToG1_isOnCurve h0))

end EthLib.Execution.Evm.Precompiles.AltBn128

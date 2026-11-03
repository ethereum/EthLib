module

public import EthLib.Execution.Evm.Precompiles.AltBn128
public import EthLib.Execution.Proofs.Evm.Memory
public import EthLib.Base.Proofs.BigEndian
public import EthLib.Serialization.Proofs.Rlp.Vectors

/-!
# Proofs: `Evm.Precompiles.AltBn128`

- ECADD and ECMUL fail exactly when the gas is below the price or a point is invalid.
- Every output has 64 bytes.
- The known answers pin the group: `G + G = 2 G`, `G + (-G) = O`, `q G = O`, `(q + 1) G = G`.

`2 G` and `3 G` are the points that py_ecc 8.0.0 computes, the library that execution-specs calls.

The other expected outputs follow from the group law and from `q`, the order of `G`.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Serialization.Rlp.Vectors (byteArrayOf)
open EthLib.Cryptography.AltBn128

/-- ECADD runs out of gas below its price. -/
theorem ecadd_outOfGas (data : ByteArray) {gas : Nat} (hgas : gas < GAS_ECADD) :
    ecadd data gas = .error (.outOfGas GAS_ECADD gas) := by
  simp [ecadd, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- ECMUL runs out of gas below its price. -/
theorem ecmul_outOfGas (data : ByteArray) {gas : Nat} (hgas : gas < GAS_ECMUL) :
    ecmul data gas = .error (.outOfGas GAS_ECMUL gas) := by
  simp [ecmul, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The 64 bytes of a point. -/
theorem length_g1ToBytes : (point : Point) → (g1ToBytes point).length = 64
  | .infinity => by simp [g1ToBytes]
  | .affine _ _ => by simp [g1ToBytes, EthLib.Base.natToBytes_length]

/-- A chain of steps that succeeds succeeded at its first step. -/
theorem bind_eq_ok {α β : Type} {x : Except AltBn128Error α} {f : α → Except AltBn128Error β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Every output of ECADD has 64 bytes. -/
theorem ecadd_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : ecadd data gas = .ok out) :
    out.size = 64 := by
  simp only [ecadd, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_g1ToBytes]

/-- Every output of ECMUL has 64 bytes. -/
theorem ecmul_size {data : ByteArray} {gas : Nat} {out : ByteArray} (h : ecmul data gas = .ok out) :
    out.size = 64 := by
  simp only [ecmul, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_g1ToBytes]

/-- A coordinate at or above `p` is rejected. -/
theorem bytesToG1_invalidFieldElement {raw : List UInt8}
    (hx : Fp.modulus ≤ EthLib.Base.bytesToNat (raw.take 32)) :
    bytesToG1 raw = .error .invalidFieldElement := by
  simp [bytesToG1, Nat.not_lt.mpr hx, throw, throwThe, MonadExceptOf.throw]

/-! ## Known answers -/

/-- A result that the kernel computes as the bytes `out` is `.ok out`. -/
theorem eq_ok_of_kernel {result : Except AltBn128Error ByteArray} {out : ByteArray}
    (h : (result.toOption.map fun bytes => bytes.data.toList) = some out.data.toList) : result = .ok out := by
  cases result with
  | error => simp [Except.toOption] at h
  | ok bytes =>
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at h
    cases bytes; cases out
    simp_all

/-- The error of a result, or `none` when it succeeds. -/
def errorOf (result : Except AltBn128Error ByteArray) : Option AltBn128Error :=
  match result with
  | .error e => some e
  | .ok _ => none

/-- A result whose error the kernel computes as `e` is `.error e`. -/
theorem eq_error_of_kernel {result : Except AltBn128Error ByteArray} {e : AltBn128Error}
    (h : errorOf result = some e) : result = .error e := by
  cases result <;> simp_all [errorOf]

/-- `G + G = 2 G`. -/
theorem ecadd_g_g : ecadd (byteArrayOf 128 0x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) 150 = .ok (byteArrayOf 64 0x030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `G + 2 G = 3 G`. -/
theorem ecadd_g_2g : ecadd (byteArrayOf 128 0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4) 150 = .ok (byteArrayOf 64 0x0769bf9ac56bea3ff40232bcb1b6bd159315d84715b8e679f2d355961915abf02ab799bee0489429554fdb7c8d086475319e63b40b9c5b57cdf1ff3dd9fe2261) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `G + (-G) = O`, written as 64 zero bytes. -/
theorem ecadd_g_neg_g : ecadd (byteArrayOf 128 0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000130644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd45) 150 = .ok (byteArrayOf 64 0) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `G + O = G`: the call data stops after `G`, and the rest reads as zeros. -/
theorem ecadd_g_short : ecadd (byteArrayOf 64 0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) 150 = .ok (byteArrayOf 64 0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `O + O = O`: empty call data reads as two points at infinity. -/
theorem ecadd_empty : ecadd .empty 150 = .ok (byteArrayOf 64 0) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `(1, 3)` is not on the curve, since `9 != 1 + 3`. -/
theorem ecadd_not_on_curve :
    ecadd (byteArrayOf 128 0x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) 150 = .error .notOnCurve :=
  eq_error_of_kernel (by decide +kernel)

/-- `x = p` is not a field element. -/
theorem ecadd_x_is_p :
    ecadd (byteArrayOf 128 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) 150 = .error .invalidFieldElement :=
  eq_error_of_kernel (by decide +kernel)

/-- One gas below the price runs out of gas. -/
theorem ecadd_149 : ecadd .empty 149 = .error (.outOfGas 150 149) := ecadd_outOfGas _ (by decide)

/-- `2 G`, as ECMUL computes it. -/
theorem ecmul_g_2 : ecmul (byteArrayOf 96 0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000002) 6000 = .ok (byteArrayOf 64 0x030644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd315ed738c0e0a7c92e7845f96b2ae9c0a68a6a449e3538fc7ff3ebf7a5a18a2c4) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `q G = O`: the order of `G` is `q`. -/
theorem ecmul_g_q : ecmul (byteArrayOf 96 0x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000230644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001) 6000 = .ok (byteArrayOf 64 0) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `(q + 1) G = G`: the scalar is not reduced, and the result still wraps around the group. -/
theorem ecmul_g_q_plus_1 : ecmul (byteArrayOf 96 0x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000230644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000002) 6000 = .ok (byteArrayOf 64 0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) :=
  eq_ok_of_kernel (by decide +kernel)

/-- `0 G = O`. -/
theorem ecmul_g_0 : ecmul (byteArrayOf 64 0x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002) 6000 = .ok (byteArrayOf 64 0) :=
  eq_ok_of_kernel (by decide +kernel)

/-- An invalid point fails, whatever the scalar. -/
theorem ecmul_not_on_curve :
    ecmul (byteArrayOf 96 0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000002) 6000 = .error .notOnCurve :=
  eq_error_of_kernel (by decide +kernel)

end EthLib.Execution.Evm.Precompiles.AltBn128

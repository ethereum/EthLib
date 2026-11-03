module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.AltBn128.Curve
public import EthLib.Execution.Evm.Memory

/-!
# `Evm.Precompiles.AltBn128`

The alt_bn128 precompiles of EIP-196 and EIP-197, which zkSNARK verifiers call.

- ECADD at `0x06` adds two points of `G_1`.
- ECMUL at `0x07` multiplies a point of `G_1` by a 32-byte scalar.

A point is its coordinates as two 32-byte big-endian integers, and `(0, 0)` is the point at infinity:

```text
ECADD input:  [ x1: 32 | y1: 32 | x2: 32 | y2: 32 ]
ECMUL input:  [ x: 32 | y: 32 | scalar: 32 ]
output:       [ x: 32 | y: 32 ]
```

The call data reads as if padded with zeros, so a short input is padded and bytes past the input are ignored.

Source: [`forks/istanbul/vm/precompiled_contracts/alt_bn128.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/istanbul/vm/precompiled_contracts/alt_bn128.py#L39-L192) of execution-specs at `2c0c8e7`.

Byzantium introduced the precompiles, and Istanbul lowered their prices with EIP-1108.

Every later fork there computes the same results with the same prices, up to Bogota.

An invalid point makes the source raise `OutOfGasError`, so the call fails and consumes all its gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Base (bytesToNat natToBytes)
open EthLib.Execution.Evm (bufferRead)
open EthLib.Cryptography.AltBn128

/-- The price of ECADD, `GasCosts.PRECOMPILE_ECADD` in [`forks/istanbul/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/istanbul/vm/gas.py#L72). -/
def GAS_ECADD : Nat := 150

/-- The price of ECMUL, `GasCosts.PRECOMPILE_ECMUL` in [`forks/istanbul/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/istanbul/vm/gas.py#L73). -/
def GAS_ECMUL : Nat := 6000

/-- Why an alt_bn128 call fails.

Every failure consumes all the gas, so the error only says why. -/
inductive AltBn128Error where
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  /-- A coordinate is not below the field modulus `p`. -/
  | invalidFieldElement
  /-- A point is not on its curve. -/
  | notOnCurve
  deriving Repr, DecidableEq

/-- `bytes_to_g1`: a point of `G_1` from 64 bytes, with `(0, 0)` for the point at infinity. -/
def bytesToG1 (raw : List UInt8) : Except AltBn128Error Point := do
  let x := bytesToNat (raw.take 32)
  let y := bytesToNat (raw.drop 32)
  if hx : x < Fp.modulus then
    if hy : y < Fp.modulus then
      if x = 0 ∧ y = 0 then
        return .infinity
      let point := Point.affine ⟨x, hx⟩ ⟨y, hy⟩
      if point.isOnCurve then return point else throw .notOnCurve
    else throw .invalidFieldElement
  else throw .invalidFieldElement

/-- The 64 bytes of a point: its coordinates as 32-byte words, and all zeros for the point at infinity. -/
def g1ToBytes : Point → List UInt8
  | .infinity => List.replicate 64 0
  | .affine x y => natToBytes 32 x.val ++ natToBytes 32 y.val

/-- `alt_bn128_add`: the sum of the two points in the call data. -/
def ecadd (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  if gas < GAS_ECADD then
    throw (.outOfGas GAS_ECADD gas)
  let p0 ← bytesToG1 (bufferRead data 0 64)
  let p1 ← bytesToG1 (bufferRead data 64 64)
  return ⟨(g1ToBytes (p0 + p1)).toArray⟩

/-- `alt_bn128_mul`: the point in the call data times the scalar after it.

The scalar is the full 32-byte integer, not reduced. -/
def ecmul (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  if gas < GAS_ECMUL then
    throw (.outOfGas GAS_ECMUL gas)
  let p0 ← bytesToG1 (bufferRead data 0 64)
  let n := bytesToNat (bufferRead data 64 32)
  -- A 32-byte scalar is below `2^256`, so 256 bits cover it.
  return ⟨(g1ToBytes (Point.mulBits 256 n p0)).toArray⟩

end EthLib.Execution.Evm.Precompiles.AltBn128

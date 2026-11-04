module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.AltBn128.Pairing
public import EthLib.Execution.Evm.Memory

/-!
# `Evm.Precompiles.AltBn128`

The alt_bn128 precompiles of EIP-196 and EIP-197, which zkSNARK verifiers call.

- ECADD at `0x06` adds two points of `G_1`.
- ECMUL at `0x07` multiplies a point of `G_1` by a 32-byte scalar.
- ECPAIRING at `0x08` checks that the product of the pairings of pairs of points is 1.

A point is its coordinates as two 32-byte big-endian integers, and `(0, 0)` is the point at infinity:

```text
ECADD input:  [ x1: 32 | y1: 32 | x2: 32 | y2: 32 ]
ECMUL input:  [ x: 32 | y: 32 | scalar: 32 ]
output:       [ x: 32 | y: 32 ]
ECPAIRING:    k pairs of [ G_1 point: 64 | G_2 point: 128 ], and 1 or 0 as a 32-byte word
G_2 point:    [ x.c1: 32 | x.c0: 32 | y.c1: 32 | y.c0: 32 ]
```

The call data reads as if padded with zeros, so a short input is padded and bytes past the input are ignored.

Sources: EIP-196 for addition and multiplication, and EIP-197 for the pairing check.

EIP-1108 sets the prices: <https://eips.ethereum.org/EIPS/eip-1108>.

Byzantium introduced the precompiles, and Istanbul lowered their prices with EIP-1108.

Every later fork computes the same results with the same prices.

An invalid point makes the call fail, and the call consumes all its gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Base (bytesToNat natToBytes)
open EthLib.Execution.Evm (bufferRead)
open EthLib.Cryptography.AltBn128

/-- The price of ECADD, from EIP-1108. -/
def GAS_ECADD : Nat := 150

/-- The price of ECMUL, from EIP-1108. -/
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
  /-- The call data of a pairing check is not a whole number of 192-byte pairs. -/
  | invalidInputLength (size : Nat)
  /-- A point is not in the group of order `q`. -/
  | notInSubgroup
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

/-- The price of every pairing check, from EIP-1108. -/
def GAS_ECPAIRING_BASE : Nat := 45000

/-- The price of each pair, from EIP-1108. -/
def GAS_ECPAIRING_PER_POINT : Nat := 34000

/-- The price of a pairing check on `size` bytes: one pair per whole 192 bytes. -/
def ecpairingGas (size : Nat) : Nat := GAS_ECPAIRING_PER_POINT * (size / 192) + GAS_ECPAIRING_BASE

/-- An element of `Fp` from 32 bytes. -/
def bytesToFp (raw : List UInt8) : Except AltBn128Error Fp :=
  let value := bytesToNat raw
  if h : value < Fp.modulus then .ok ⟨value, h⟩ else .error .invalidFieldElement

/-- `bytes_to_g2`: a point of the twist from 128 bytes, the `i` part of each coordinate first, with zeros for the point at infinity. -/
def bytesToG2 (raw : List UInt8) : Except AltBn128Error Point2 := do
  let x1 ← bytesToFp (raw.take 32)
  let x0 ← bytesToFp ((raw.drop 32).take 32)
  let y1 ← bytesToFp ((raw.drop 64).take 32)
  let y0 ← bytesToFp (raw.drop 96)
  let x : Fp2 := ⟨x0, x1⟩
  let y : Fp2 := ⟨y0, y1⟩
  if x = ⟨0, 0⟩ ∧ y = ⟨0, 0⟩ then
    return .infinity
  let point := Point2.affine x y
  if point.isOnCurve then return point else throw .notOnCurve

/-- One pair of the call data, decoded and checked to be in the groups of order `q`. -/
def decodePair (data : ByteArray) (index : Nat) : Except AltBn128Error (Point × Point2) := do
  let p ← bytesToG1 (bufferRead data (192 * index) 64)
  let q ← bytesToG2 (bufferRead data (192 * index + 64) 128)
  -- `q` has 254 bits, so 256 bits of the scalar cover it.
  if Point.mulBits 256 Fr.modulus p ≠ .infinity then
    throw .notInSubgroup
  if Point2.mulBits 256 Fr.modulus q ≠ .infinity then
    throw .notInSubgroup
  return (p, q)

/-- `alt_bn128_pairing_check`: 1 as a 32-byte word when the product of the pairings of the pairs is 1, and 0 otherwise.

The gas is charged before the length is checked. -/
def ecpairing (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  if gas < ecpairingGas data.size then
    throw (.outOfGas (ecpairingGas data.size) gas)
  if data.size % 192 ≠ 0 then
    throw (.invalidInputLength data.size)
  let pairs ← (List.range (data.size / 192)).mapM (decodePair data)
  return ⟨(List.replicate 31 (0 : UInt8) ++ [if pairingCheck pairs then 1 else 0]).toArray⟩

end EthLib.Execution.Evm.Precompiles.AltBn128

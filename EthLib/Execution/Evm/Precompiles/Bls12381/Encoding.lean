module

public import EthLib.Base.BigEndian
public import EthLib.Cryptography.Bls.Compress

/-!
# `Evm.Precompiles.Bls12381.Encoding`

How the BLS12-381 precompiles of EIP-2537 read and write field elements and points.

A field element takes 64 bytes: 16 zero bytes of padding, then its 48 bytes, big-endian.

A point takes its coordinates in order, and the point at infinity is all zeros:

```text
G1 point:  [ x: 64 | y: 64 ]
G2 point:  [ x.c0: 64 | x.c1: 64 | y.c0: 64 | y.c1: 64 ]
```

A G2 coordinate `c0 + c1 * i` is an element of `Fp2 = Fp[i] / (i^2 + 1)`.

Source: "Fine points and encoding of base elements" of EIP-2537, at
<https://eips.ethereum.org/EIPS/eip-2537>.

Prague introduced the precompiles, and its decoding rejects the same inputs, as the proofs show.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bytesToNat natToBytes)
open EthLib.Cryptography.Bls (Fp Fp2 G1 G2)

/-- The size of a field element without its padding. -/
def FP_BYTES : Nat := 48

/-- `ZERO_PAD`: the number of zero bytes in front of each field element. -/
def PAD_BYTES : Nat := 16

/-- The size of an encoded G1 point: two padded field elements. -/
def G1_BYTES : Nat := 128

/-- The size of an encoded G2 point: four padded field elements. -/
def G2_BYTES : Nat := 256

/-- Why a BLS12-381 precompile call fails.

Every failure consumes all the gas, so the error only says why. -/
inductive Bls12381Error where
  /-- The call data has a length that the precompile does not accept. -/
  | invalidInputLength (size : Nat)
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  /-- The 16 bytes in front of a field element are not all zero. -/
  | invalidPadding
  /-- A field element is not below the field modulus. -/
  | invalidFieldElement
  /-- A point is not on the curve. -/
  | notOnCurve
  /-- A point is not in the subgroup of prime order. -/
  | notInSubgroup
  /-- Neither candidate of the map of a field element to G1 has a square root.

  RFC 9380 §6.6.2 excludes this case, because `Z` is not a square. -/
  | notASquare
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Bls12381Error.code : Bls12381Error → UInt32
  | .invalidInputLength .. => 1
  | .outOfGas .. => 2
  | .invalidPadding => 3
  | .invalidFieldElement => 4
  | .notOnCurve => 5
  | .notInSubgroup => 6
  | .notASquare => 7

/-- `unpad_fp`: the 48 bytes of a padded field element, once its 16 leading bytes are checked to be zero. -/
def unpadFp (padded : List UInt8) : Except Bls12381Error (List UInt8) :=
  if padded.take PAD_BYTES = List.replicate PAD_BYTES 0 then .ok (padded.drop PAD_BYTES) else .error .invalidPadding

/-- `unpad_g1`: the 96 raw bytes of a padded G1 point. -/
def unpadG1 (padded : List UInt8) : Except Bls12381Error (List UInt8) := do
  let x ← unpadFp (padded.take 64)
  let y ← unpadFp ((padded.drop 64).take 64)
  return x ++ y

/-- `unpad_g2`: the 192 raw bytes of a padded G2 point. -/
def unpadG2 (padded : List UInt8) : Except Bls12381Error (List UInt8) := do
  let xc0 ← unpadFp (padded.take 64)
  let xc1 ← unpadFp ((padded.drop 64).take 64)
  let yc0 ← unpadFp ((padded.drop 128).take 64)
  let yc1 ← unpadFp ((padded.drop 192).take 64)
  return xc0 ++ xc1 ++ yc0 ++ yc1

/-- The zero bytes in front of a field element. -/
def zeroPad : List UInt8 := List.replicate PAD_BYTES 0

/-- `pad_g1`: a raw G1 point with 16 zero bytes in front of each coordinate. -/
def padG1 (raw : List UInt8) : List UInt8 :=
  zeroPad ++ raw.take 48 ++ zeroPad ++ raw.drop 48

/-- `pad_g2`: a raw G2 point with 16 zero bytes in front of each of its four field elements. -/
def padG2 (raw : List UInt8) : List UInt8 :=
  zeroPad ++ raw.take 48 ++ zeroPad ++ (raw.drop 48).take 48 ++
    zeroPad ++ (raw.drop 96).take 48 ++ zeroPad ++ raw.drop 144

/-- `bytes_to_field_element`: the big-endian integer of the bytes, if it is below the field modulus. -/
def bytesToFieldElement (raw : List UInt8) : Except Bls12381Error Fp :=
  let value := bytesToNat raw
  if h : value < Fp.modulus then .ok ⟨value, h⟩ else .error .invalidFieldElement

/-- `bytes_to_fq2`: `c0` from the first 48 bytes, then `c1` from the next 48. -/
def bytesToFq2 (raw : List UInt8) : Except Bls12381Error Fp2 := do
  let c0 ← bytesToFieldElement (raw.take 48)
  let c1 ← bytesToFieldElement (raw.drop 48)
  return ⟨c0, c1⟩

/-- Whether an affine G1 point is on `y^2 = x^3 + 4`. -/
def onCurveG1 (x y : Fp) : Bool :=
  y * y == x * x * x + Fp.ofNat 4

/-- Whether an affine G2 point is on `y^2 = x^3 + 4 * (1 + i)`. -/
def onCurveG2 (x y : Fp2) : Bool :=
  y * y == x * x * x + G2.bTwist

/-- `bytes_to_g1`: a G1 point from its 96 raw bytes.

- Both coordinates zero is the point at infinity.
- Any other point must be on the curve.
- With `subgroupCheck`, the point must also be in the subgroup of prime order. -/
def bytesToG1 (raw : List UInt8) (subgroupCheck : Bool) : Except Bls12381Error G1 := do
  let x ← bytesToFieldElement (raw.take 48)
  let y ← bytesToFieldElement (raw.drop 48)
  if x.val = 0 ∧ y.val = 0 then
    return G1.zero
  if !onCurveG1 x y then
    throw .notOnCurve
  let point : G1 := ⟨x, y, Fp.one⟩
  if subgroupCheck && !G1.inSubgroup point then
    throw .notInSubgroup
  return point

/-- `bytes_to_g2`: a G2 point from its 192 raw bytes, under the same rules as G1. -/
def bytesToG2 (raw : List UInt8) (subgroupCheck : Bool) : Except Bls12381Error G2 := do
  let x ← bytesToFq2 (raw.take 96)
  let y ← bytesToFq2 (raw.drop 96)
  if x.c0.val = 0 ∧ x.c1.val = 0 ∧ y.c0.val = 0 ∧ y.c1.val = 0 then
    return G2.zero
  if !onCurveG2 x y then
    throw .notOnCurve
  let point : G2 := ⟨x, y, Fp2.one⟩
  if subgroupCheck && !G2.inSubgroup point then
    throw .notInSubgroup
  return point

/-- `g1_to_bytes`: the 96 raw bytes of the affine coordinates, and all zeros for the point at infinity. -/
def g1ToBytes (point : G1) : List UInt8 :=
  let (x, y) := point.toAffine
  natToBytes 48 x.val ++ natToBytes 48 y.val

/-- `g2_to_bytes`: the 192 raw bytes of the affine coordinates, `c0` before `c1`. -/
def g2ToBytes (point : G2) : List UInt8 :=
  let (x, y) := point.toAffine
  natToBytes 48 x.c0.val ++ natToBytes 48 x.c1.val ++ natToBytes 48 y.c0.val ++ natToBytes 48 y.c1.val

/-- `MULTIPLIER`: the discounts of the multi-scalar multiplications are in thousandths. -/
def MULTIPLIER : Nat := 1000

/-- The call data cut into `count` pieces of `size` bytes, in order. -/
def chunks (size : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | count + 1, bytes => bytes.take size :: chunks size count (bytes.drop size)

end EthLib.Execution.Evm.Precompiles.Bls12381

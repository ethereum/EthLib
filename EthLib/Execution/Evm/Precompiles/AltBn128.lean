module

public import EthLib.Base.BigEndian
public import EthLib.Base.Fork
public import EthLib.Cryptography.AltBn128.Pairing
public import EthLib.Execution.Evm.Machine.Memory

/-!
# `Evm.Precompiles.AltBn128`

The alt_bn128 precompiles at `0x06` to `0x08`, from EIP-196 and EIP-197.

They add two points of `G_1`, multiply a point by a scalar, and check a product of pairings.

EIP-1108 lowers their prices from Istanbul, so each call takes the fork.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Base (Fork bytesToNat natToBytes)
open EthLib.Execution.Evm (bufferRead)
open EthLib.Cryptography.AltBn128

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

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def AltBn128Error.code : AltBn128Error → UInt32
  | .outOfGas .. => 1
  | .invalidFieldElement => 2
  | .notOnCurve => 3
  | .invalidInputLength .. => 4
  | .notInSubgroup => 5

/-- The price of an addition: 500 from EIP-196, and 150 from Istanbul by EIP-1108. -/
def ecaddGas (fork : Fork) : Nat := if fork ≥ .istanbul then 150 else 500

/-- The price of a multiplication: 40000 from EIP-196, and 6000 from Istanbul by EIP-1108. -/
def ecmulGas (fork : Fork) : Nat := if fork ≥ .istanbul then 6000 else 40000

/-- The price of a pairing check on `size` bytes, with one pair per whole 192 bytes.

EIP-197 charges 100000, plus 80000 per pair.

From Istanbul, EIP-1108 charges 45000, plus 34000 per pair. -/
def ecpairingGas (fork : Fork) (size : Nat) : Nat :=
  if fork ≥ .istanbul then 34000 * (size / 192) + 45000 else 80000 * (size / 192) + 100000

/-- A point of `G_1` from 64 bytes, with `(0, 0)` for the point at infinity. -/
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

/-- The 64 bytes of a point: its two coordinates, and all zeros for the point at infinity. -/
def g1ToBytes : Point → List UInt8
  | .infinity => List.replicate 64 0
  | .affine x y => natToBytes 32 x.val ++ natToBytes 32 y.val

/-- ECADD: the sum of the two points in the call data, once the gas is charged. -/
def ecadd (fork : Fork) (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  let cost := ecaddGas fork
  if gas < cost then
    throw (.outOfGas cost gas)
  let p0 ← bytesToG1 (bufferRead data 0 64)
  let p1 ← bytesToG1 (bufferRead data 64 64)
  return ⟨(g1ToBytes (p0 + p1)).toArray⟩

/-- ECMUL: the point in the call data times the scalar after it, once the gas is charged.

The scalar is the full 32-byte integer, not reduced. -/
def ecmul (fork : Fork) (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  let cost := ecmulGas fork
  if gas < cost then
    throw (.outOfGas cost gas)
  let p0 ← bytesToG1 (bufferRead data 0 64)
  let n := bytesToNat (bufferRead data 64 32)
  -- A 32-byte scalar is below `2^256`, so 256 bits cover it.
  return ⟨(g1ToBytes (Point.mulBits 256 n p0)).toArray⟩

/-- An element of `Fp` from 32 bytes. -/
def bytesToFp (raw : List UInt8) : Except AltBn128Error Fp :=
  let value := bytesToNat raw
  if h : value < Fp.modulus then .ok ⟨value, h⟩ else .error .invalidFieldElement

/-- A point of the twist from 128 bytes, with zeros for the point at infinity.

Each coordinate gives its `i` part first. -/
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

/-- ECPAIRING: the word 1 when the product of the pairings of the pairs is 1, and 0 otherwise.

The gas is charged before the length is checked.

EIP-197 does not order the two, so this module orders them. -/
def ecpairing (fork : Fork) (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  if gas < ecpairingGas fork data.size then
    throw (.outOfGas (ecpairingGas fork data.size) gas)
  if data.size % 192 ≠ 0 then
    throw (.invalidInputLength data.size)
  let pairs ← (List.range (data.size / 192)).mapM (decodePair data)
  return ⟨(List.replicate 31 (0 : UInt8) ++ [if pairingCheck pairs then 1 else 0]).toArray⟩

end EthLib.Execution.Evm.Precompiles.AltBn128

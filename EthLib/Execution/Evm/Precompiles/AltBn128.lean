module

public import EthLib.Execution.ErrorFormat
public import EthLib.Base.ByteOrder
public import EthLib.Base.Fork
public import EthLib.Cryptography.AltBn128.Pairing
public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Execution.Evm.Machine.Memory

/-!
# `Evm.Precompiles.AltBn128`

The alt_bn128 precompiles at `0x06` to `0x08`, from EIP-196 and EIP-197.

They add two points of `G_1`, multiply a point by a scalar, and check a product of pairings.

EIP-1108 lowers their prices from Istanbul, so each call takes the fork.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Base (Fork ByteOrder.ofBE ByteOrder.toBE)
open EthLib.Execution.Evm (bufferRead)
open EthLib.Cryptography.AltBn128

/-- Why an alt_bn128 call fails.

Every failure consumes all the gas, so the error only says why. -/
inductive AltBn128Error where
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  /-- A coordinate `value` is not below the field modulus `p`. -/
  | invalidFieldElement (value : Nat)
  /-- A point is not on its curve.

  It holds the bytes `point` read from the call data, with zeros past its end. -/
  | notOnCurve (point : ByteArray)
  /-- The call data of a pairing check has `size` bytes, not a whole number of 192-byte pairs. -/
  | invalidInputLength (size : Nat)
  /-- A point of the twist is not in the subgroup of order `q`.

  It holds the bytes `point` read from the call data, with zeros past its end. -/
  | notInSubgroup (point : ByteArray)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def altBn128ErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Evm.Precompiles.AltBn128.AltBn128Error." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named and each byte string in hex. -/
def AltBn128Error.reprPrec : AltBn128Error → Nat → Std.Format
  | .outOfGas cost gas, p =>
    altBn128ErrorFormat "outOfGas" [namedArg "cost" cost, namedArg "gas" gas] p
  | .invalidFieldElement value, p =>
    altBn128ErrorFormat "invalidFieldElement" [namedArg "value" value] p
  | .notOnCurve point, p => altBn128ErrorFormat "notOnCurve" [namedArg "point" point] p
  | .invalidInputLength size, p => altBn128ErrorFormat "invalidInputLength" [namedArg "size" size] p
  | .notInSubgroup point, p => altBn128ErrorFormat "notInSubgroup" [namedArg "point" point] p

instance : Repr AltBn128Error := ⟨AltBn128Error.reprPrec⟩

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def AltBn128Error.code : AltBn128Error → UInt32
  | .outOfGas .. => 1
  | .invalidFieldElement _ => 2
  | .notOnCurve _ => 3
  | .invalidInputLength .. => 4
  | .notInSubgroup _ => 5

/-- The price of an addition: 500 from EIP-196, and 150 from Istanbul by EIP-1108. -/
def ecaddGas (fork : Fork) : Nat :=
  (gasSchedule fork).PRECOMPILE_ECADD

/-- The price of a multiplication: 40000 from EIP-196, and 6000 from Istanbul by EIP-1108. -/
def ecmulGas (fork : Fork) : Nat :=
  (gasSchedule fork).PRECOMPILE_ECMUL

/-- The price of a pairing check on `size` bytes, with one pair per whole 192 bytes.

EIP-197 charges 100000, plus 80000 per pair.

From Istanbul, EIP-1108 charges 45000, plus 34000 per pair. -/
def ecpairingGas (fork : Fork) (size : Nat) : Nat :=
  -- EIP-197: `80 000 * k + 100 000`; EIP-1108: `34 000 * k + 45 000`, here from Istanbul.
  --
  -- `k` is the length of the input divided by 192, rounded down here, since the gas comes first.
  if fork ≥ .istanbul then 34000 * (size / 192) + 45000 else 80000 * (size / 192) + 100000

/-- A point of `G_1` from 64 bytes, with `(0, 0)` for the point at infinity. -/
def bytesToG1 (raw : List UInt8) : Except AltBn128Error Point := do
  -- EIP-196, Encoding: field elements are 32 byte big-endian numbers, a point is `(x, y)`.
  let x := ByteOrder.ofBE (raw.take 32)
  let y := ByteOrder.ofBE (raw.drop 32)
  -- Invalid input: a coordinate equal or larger than the field modulus `p`.
  if hx : x < Fp.modulus then
    if hy : y < Fp.modulus then
      -- The point at infinity is encoded as `(0, 0)`.
      if x = 0 ∧ y = 0 then
        return .infinity
      let point := Point.affine ⟨x, hx⟩ ⟨y, hy⟩
      -- Invalid input: a point that does not lie on the curve `Y^2 = X^3 + 3`.
      if point.isOnCurve then return point else throw (.notOnCurve ⟨raw.toArray⟩)
    else throw (.invalidFieldElement y)
  else throw (.invalidFieldElement x)

/-- The 64 bytes of a point: its two coordinates, and all zeros for the point at infinity. -/
def g1ToBytes : Point → List UInt8
  -- EIP-196, Encoding: the length of the returned data is always as specified, 64 bytes.
  | .infinity => List.replicate 64 0
  | .affine x y => (ByteOrder.toBE 32 x.val).toList ++ (ByteOrder.toBE 32 y.val).toList

/-- ECADD: the sum of the two points in the call data, once the gas is charged. -/
def ecadd (fork : Fork) (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  let cost := ecaddGas fork
  if gas < cost then
    throw (.outOfGas cost gas)
  -- ADD input: two curve points; a short input is padded with zeros, surplus bytes are ignored.
  let p0 ← bytesToG1 (bufferRead data 0 64)
  let p1 ← bytesToG1 (bufferRead data 64 64)
  -- Output: the curve point `x + y`.
  return ⟨(g1ToBytes (p0 + p1)).toArray⟩

/-- ECMUL: the point in the call data times the scalar after it, once the gas is charged.

The scalar is the full 32-byte integer, not reduced. -/
def ecmul (fork : Fork) (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  let cost := ecmulGas fork
  if gas < cost then
    throw (.outOfGas cost gas)
  -- MUL input: a curve point and a scalar `(x, s)`; a short input is padded with zeros.
  let p0 ← bytesToG1 (bufferRead data 0 64)
  -- The scalar can be any number between `0` and `2^256 - 1`.
  let n := ByteOrder.ofBE (bufferRead data 64 32)
  -- Output: the curve point `s * x`.
  --
  -- A 32-byte scalar is below `2^256`, so 256 bits cover it.
  return ⟨(g1ToBytes (Point.mulBits 256 n p0)).toArray⟩

/-- An element of `Fp` from 32 bytes. -/
def bytesToFp (raw : List UInt8) : Except AltBn128Error Fp :=
  -- EIP-197, Encoding: 32 byte big-endian numbers; an encoding value of `p` or larger is invalid.
  let value := ByteOrder.ofBE raw
  if h : value < Fp.modulus then .ok ⟨value, h⟩ else .error (.invalidFieldElement value)

/-- A point of the twist from 128 bytes, with zeros for the point at infinity.

Each coordinate gives its `i` part first. -/
def bytesToG2 (raw : List UInt8) : Except AltBn128Error Point2 := do
  -- Elements `a * i + b` of `F_p^2` are encoded as two elements of `F_p`, `(a, b)`.
  let x1 ← bytesToFp (raw.take 32)
  let x0 ← bytesToFp ((raw.drop 32).take 32)
  let y1 ← bytesToFp ((raw.drop 64).take 32)
  let y0 ← bytesToFp (raw.drop 96)
  let x : Fp2 := ⟨x0, x1⟩
  let y : Fp2 := ⟨y0, y1⟩
  -- The point at infinity is encoded as `(0, 0)`.
  if x = ⟨0, 0⟩ ∧ y = ⟨0, 0⟩ then
    return .infinity
  let point := Point2.affine x y
  -- Not an element of `G_2` if not on the curve `Y^2 = X^3 + 3/(i+9)`.
  if point.isOnCurve then return point else throw (.notOnCurve ⟨raw.toArray⟩)

/-- The 128 bytes of a point of the twist, with the `i` part of each coordinate first.

The point at infinity is 128 zero bytes.

No precompile returns a point of the twist; this encoding is the inverse of the decoder above. -/
def g2ToBytes : Point2 → List UInt8
  | .infinity => List.replicate 128 0
  | .affine x y =>
    (ByteOrder.toBE 32 x.c1.val).toList ++ (ByteOrder.toBE 32 x.c0.val).toList ++
      (ByteOrder.toBE 32 y.c1.val).toList ++ (ByteOrder.toBE 32 y.c0.val).toList

/-- One pair of the call data, decoded and checked to be in the groups of order `q`.

For `G_1`, the encoding and the curve equation, or the encoding of infinity, are enough.

So only the point of the twist has its order checked.

Source: [EIP-197][eip197], section Specification.

[eip197]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-197.md#specification
-/
def decodePair (data : ByteArray) (index : Nat) : Except AltBn128Error (Point × Point2) := do
  -- Input pair `(aj, bj)` of `(G_1 x G_2)^k`, 64 then 128 bytes.
  let p ← bytesToG1 (bufferRead data (192 * index) 64)
  let q ← bytesToG2 (bufferRead data (192 * index + 64) 128)
  -- For `G_2`, the order of the element has to be checked to be equal to the group order `q`.
  --
  -- Here the check is `q * Q = 0`: `q` is prime, so the order is 1 or `q`, and 1 is infinity.
  --
  -- The order has 254 bits, so 256 bits of the scalar cover it.
  if Point2.mulBits 256 Fr.modulus q ≠ .infinity then
    throw (.notInSubgroup ⟨(bufferRead data (192 * index + 64) 128).toArray⟩)
  return (p, q)

/-- The 32-byte word of a boolean: 31 zero bytes, then `1` for true and `0` for false. -/
def ecpairingWord (result : Bool) : List UInt8 :=
  -- EIP-197, Encoding: always exactly 32 bytes, a 32 byte big-endian number.
  List.replicate 31 0 ++ [if result then 1 else 0]

/-- ECPAIRING: the word 1 when the product of the pairings of the pairs is 1, and 0 otherwise.

The gas is charged before the length is checked.

EIP-197 does not order the two, so this module orders them. -/
def ecpairing (fork : Fork) (data : ByteArray) (gas : Nat) : Except AltBn128Error ByteArray := do
  if gas < ecpairingGas fork data.size then
    throw (.outOfGas (ecpairingGas fork data.size) gas)
  -- If the input length is not a multiple of `192`, the call fails.
  if data.size % 192 ≠ 0 then
    throw (.invalidInputLength data.size)
  -- `k` is the length of the input divided by `192`; empty input is valid.
  let pairs ← (List.range (data.size / 192)).mapM (decodePair data)
  -- One if `log_P1(a1) * log_P2(b1) + ... + log_P1(ak) * log_P2(bk) = 0` in `F_q`, else zero.
  --
  -- That holds exactly when the product of the pairings `e(aj, bj)` is 1.
  --
  -- The pairing is bilinear and non-degenerate, so `e(P1, P2)` has order `q`.
  return ⟨(ecpairingWord (pairingCheck pairs)).toArray⟩

end EthLib.Execution.Evm.Precompiles.AltBn128

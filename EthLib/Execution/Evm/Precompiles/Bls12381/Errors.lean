module

public import EthLib.Execution.ErrorFormat

/-!
# `Evm.Precompiles.Bls12381.Errors`

Why a call of a BLS12-381 precompile of EIP-2537 fails.

Every failure consumes all the gas of the call.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

/-- Why a BLS12-381 precompile call fails.

Every failure consumes all the gas, so the error only says why. -/
inductive Bls12381Error where
  /-- The call data has a length that the precompile does not accept. -/
  | invalidInputLength (size : Nat)
  /-- The gas given was below the price. -/
  | outOfGas (cost gas : Nat)
  /-- The 16 bytes `padding` in front of a field element are not all zero. -/
  | invalidPadding (padding : ByteArray)
  /-- A field element `value` is not below the field modulus. -/
  | invalidFieldElement (value : Nat)
  /-- A point, with the unpadded bytes `point`, is not on the curve. -/
  | notOnCurve (point : ByteArray)
  /-- A point, with the unpadded bytes `point`, is not in the subgroup of prime order. -/
  | notInSubgroup (point : ByteArray)
  /-- Neither candidate of the map of a field element to G1 has a square root.

  RFC 9380 §6.6.2 excludes this case, because `Z` is not a square. -/
  | notASquare
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def bls12381ErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Evm.Precompiles.Bls12381.Bls12381Error." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named and each byte string in hex. -/
def Bls12381Error.reprPrec : Bls12381Error → Nat → Std.Format
  | .invalidInputLength size, p => bls12381ErrorFormat "invalidInputLength" [namedArg "size" size] p
  | .outOfGas cost gas, p =>
    bls12381ErrorFormat "outOfGas" [namedArg "cost" cost, namedArg "gas" gas] p
  | .invalidPadding padding, p =>
    bls12381ErrorFormat "invalidPadding" [namedArg "padding" padding] p
  | .invalidFieldElement value, p =>
    bls12381ErrorFormat "invalidFieldElement" [namedArg "value" value] p
  | .notOnCurve point, p => bls12381ErrorFormat "notOnCurve" [namedArg "point" point] p
  | .notInSubgroup point, p => bls12381ErrorFormat "notInSubgroup" [namedArg "point" point] p
  | .notASquare, p => bls12381ErrorFormat "notASquare" [] p

instance : Repr Bls12381Error := ⟨Bls12381Error.reprPrec⟩

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Bls12381Error.code : Bls12381Error → UInt32
  | .invalidInputLength .. => 1
  | .outOfGas .. => 2
  | .invalidPadding _ => 3
  | .invalidFieldElement _ => 4
  | .notOnCurve _ => 5
  | .notInSubgroup _ => 6
  | .notASquare => 7

end EthLib.Execution.Evm.Precompiles.Bls12381

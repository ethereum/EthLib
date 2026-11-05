module

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

end EthLib.Execution.Evm.Precompiles.Bls12381

module

public import EthLib.Execution.Evm.Precompiles.Modexp.Constants

/-!
# `Modexp.Errors`

Typed failures of the MODEXP precompile.

Both failures end the call and consume all its gas.

They differ in when they happen:

- A length above the bound of EIP-7823 is an exceptional halt, raised before any gas is charged.
- A call whose gas is below the price runs out of gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

/-- The three length headers of the input. -/
inductive LengthField where
  | base
  | exponent
  | modulus
  deriving Repr, DecidableEq

/-- Every way a MODEXP call can fail. -/
inductive ModexpError where
  /-- A length header exceeded 1024 bytes.

  EIP-7823: "the precompile execution stops, returns an error, and consumes all gas". -/
  | lengthTooLarge (field : LengthField) (length : Nat)
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ModexpError.code : ModexpError → UInt32
  | .lengthTooLarge .. => 1
  | .outOfGas .. => 2

end EthLib.Execution.Evm.Precompiles.Modexp

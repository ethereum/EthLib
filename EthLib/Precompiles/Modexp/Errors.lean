module

public import EthLib.Precompiles.Modexp.Constants

/-!
# `Modexp.Errors`

Typed failures of the MODEXP precompile.

Both failures end the call and consume all its gas.

They differ in when they happen:

- A length above the bound of EIP-7823 is an exceptional halt, raised before any gas is charged.
- A call whose gas is below the price runs out of gas.
-/

@[expose] public section

namespace EthLib.Precompiles.Modexp

/-- The three length headers of the input. -/
inductive LengthField where
  | base
  | exponent
  | modulus
  deriving Repr, DecidableEq

/-- Every way a MODEXP call can fail. -/
inductive ModexpError where
  /-- A length header exceeded 1024 bytes.

  EIP-7823, Specification: "the precompile execution stops, returns an error, and consumes all gas".

  `ExceptionalHalt` in `forks/bpo2/vm/precompiled_contracts/modexp.py`. -/
  | lengthTooLarge (field : LengthField) (length : Nat)
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in `forks/bpo2/vm/gas.py`. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- Human-readable description of the failure. -/
def ModexpError.message : ModexpError → String
  | .lengthTooLarge .base length =>
      s!"base length {length} exceeds {Constants.MAX_LENGTH_BYTES}"
  | .lengthTooLarge .exponent length =>
      s!"exponent length {length} exceeds {Constants.MAX_LENGTH_BYTES}"
  | .lengthTooLarge .modulus length =>
      s!"modulus length {length} exceeds {Constants.MAX_LENGTH_BYTES}"
  | .outOfGas cost gas => s!"out of gas: price {cost}, gas {gas}"

end EthLib.Precompiles.Modexp

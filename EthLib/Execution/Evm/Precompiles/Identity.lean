module

public import EthLib.Execution.Evm.Words

/-!
# `Evm.Precompiles.Identity`

The IDENTITY precompile at address `0x04`, from Appendix E of the Yellow Paper.

It returns its call data unchanged, so contracts can copy memory cheaply.

The call fails only when the gas is below its price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

open EthLib.Execution.Evm (wordCount)

/-- The price of every call, from Appendix E of the Yellow Paper. -/
def GAS_BASE : Nat := 15

/-- The price of each word of call data, from Appendix E of the Yellow Paper. -/
def GAS_PER_WORD : Nat := 3

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- Why an IDENTITY call fails. -/
inductive IdentityError where
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def IdentityError.code : IdentityError → UInt32
  | .outOfGas .. => 1

/-- `identity`: the call data itself, once the gas covers the price. -/
def identity (data : ByteArray) (gas : Nat) : Except IdentityError ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok data

end EthLib.Execution.Evm.Precompiles.Identity

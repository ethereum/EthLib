module

public import EthLib.Execution.ErrorFormat
public import EthLib.Execution.Evm.Words

/-!
# `Evm.Precompiles.Identity`

The IDENTITY precompile at address `0x04`, from Appendix E of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

It returns its call data unchanged, so contracts can copy memory cheaply.

The call fails only when the gas is below its price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

open EthLib.Execution.Evm (wordPrice)

/-- The price of every call, from Appendix E of the Yellow Paper. -/
def GAS_BASE : Nat := 15

/-- The price of each word of call data, from Appendix E of the Yellow Paper. -/
def GAS_PER_WORD : Nat := 3

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat :=
  -- `g_r = 15 + 3 * ceil(||I_d|| / 32)`.
  wordPrice GAS_BASE GAS_PER_WORD size

/-- Why an IDENTITY call fails. -/
inductive IdentityError where
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def identityErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Evm.Precompiles.Identity.IdentityError." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named. -/
def IdentityError.reprPrec : IdentityError → Nat → Std.Format
  | .outOfGas cost gas, p =>
    identityErrorFormat "outOfGas" [namedArg "cost" cost, namedArg "gas" gas] p

instance : Repr IdentityError := ⟨IdentityError.reprPrec⟩

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def IdentityError.code : IdentityError → UInt32
  | .outOfGas .. => 1

/-- The call: the call data itself, once the gas covers the price. -/
def identity (data : ByteArray) (gas : Nat) : Except IdentityError ByteArray :=
  -- `g_r`, the price of the call.
  let cost := gasCost data.size
  -- Appendix E, `Xi_PRE`: `(empty, 0, A, ())` if `g < g_r`, else `(sigma, g - g_r, A, o)`.
  --
  -- Here the call returns an error or the output, and the call frame applies the rest.
  --
  -- `o = I_d`.
  if gas < cost then .error (.outOfGas cost gas) else .ok data

end EthLib.Execution.Evm.Precompiles.Identity

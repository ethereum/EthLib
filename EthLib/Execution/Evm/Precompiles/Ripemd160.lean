module

public import EthLib.Execution.ErrorFormat
public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Ripemd160
public import EthLib.Execution.Evm.Words

/-!
# `Evm.Precompiles.Ripemd160`

The RIPEMD-160 precompile at address `0x03`, from Appendix E of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

It returns the RIPEMD-160 digest of the call data, left-padded with zero bytes to 32 bytes.

The call fails only when the gas is below its price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Ripemd160

open EthLib.Execution.Evm (wordCount)

/-- The size of the output in bytes. -/
def OUTPUT_BYTES : Nat := 32

/-- The size of the RIPEMD-160 digest in bytes. -/
def DIGEST_BYTES : Nat := 20

/-- The output on the call data: the digest, left-padded with zero bytes to 32 bytes. -/
def output (data : ByteArray) : ByteArray :=
  -- `o[0..11] = 0` and `o[12..31] = RIPEMD160(I_d)`.
  ⟨Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0⟩ ++
    Base.packBytes (Cryptography.Hash.ripemd160 data)

/-- The price of every call, from Appendix E of the Yellow Paper. -/
def GAS_BASE : Nat := 600

/-- The price of each word of call data, from Appendix E of the Yellow Paper. -/
def GAS_PER_WORD : Nat := 120

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat :=
  -- `g_r = 600 + 120 * ceil(||I_d|| / 32)`.
  GAS_BASE + GAS_PER_WORD * wordCount size

/-- Why a RIPEMD-160 call fails. -/
inductive Ripemd160Error where
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving DecidableEq

/-- A constructor of the error, named in full, applied to its arguments. -/
def ripemd160ErrorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  constructorFormat ("EthLib.Execution.Evm.Precompiles.Ripemd160.Ripemd160Error." ++ name) args prec

/-- The form of the error in Lean syntax, with each value named. -/
def Ripemd160Error.reprPrec : Ripemd160Error → Nat → Std.Format
  | .outOfGas cost gas, p =>
    ripemd160ErrorFormat "outOfGas" [namedArg "cost" cost, namedArg "gas" gas] p

instance : Repr Ripemd160Error := ⟨Ripemd160Error.reprPrec⟩

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Ripemd160Error.code : Ripemd160Error → UInt32
  | .outOfGas .. => 1

/-- The call: the output on the call data, once the gas covers the price. -/
def ripemd160 (data : ByteArray) (gas : Nat) : Except Ripemd160Error ByteArray :=
  -- `g_r`, the price of the call.
  let cost := gasCost data.size
  -- Appendix E, `Xi_PRE`: `(empty, 0, A, ())` if `g < g_r`, else `(sigma, g - g_r, A, o)`.
  --
  -- Here the call returns an error or the output, and the call frame applies the rest.
  if gas < cost then .error (.outOfGas cost gas) else .ok (output data)

end EthLib.Execution.Evm.Precompiles.Ripemd160

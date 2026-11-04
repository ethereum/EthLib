module

public import EthLib.Cryptography.Hash.Ripemd160
public import EthLib.Execution.Evm.Words

/-!
# `Evm.Precompiles.Ripemd160`

The RIPEMD-160 precompile at address `0x03`, from Appendix E of the Yellow Paper.

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
  ⟨Array.replicate (OUTPUT_BYTES - DIGEST_BYTES) 0⟩ ++ Cryptography.Hash.ripemd160 data

/-- The price of every call, from Appendix E of the Yellow Paper. -/
def GAS_BASE : Nat := 600

/-- The price of each word of call data, from Appendix E of the Yellow Paper. -/
def GAS_PER_WORD : Nat := 120

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- Why a RIPEMD-160 call fails. -/
inductive Ripemd160Error where
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Ripemd160Error.code : Ripemd160Error → UInt32
  | .outOfGas .. => 1

/-- The call: the output on the call data, once the gas covers the price. -/
def ripemd160 (data : ByteArray) (gas : Nat) : Except Ripemd160Error ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok (output data)

end EthLib.Execution.Evm.Precompiles.Ripemd160

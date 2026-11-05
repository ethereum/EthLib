module

public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Execution.Evm.Machine.Words

/-!
# `Evm.Precompiles.Sha256`

The SHA-256 precompile at address `0x02`, from Appendix E of the Yellow Paper.

It charges 60 gas, plus 12 for each 32-byte word of call data, then hashes the whole call data.

The call fails only when the gas is below that price.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Sha256

open EthLib.Execution.Evm (wordCount)

/-- The size of the output in bytes: one SHA-256 digest. -/
def OUTPUT_BYTES : Nat := 32

/-- The price of every call, from Appendix E of the Yellow Paper. -/
def GAS_BASE : Nat := 60

/-- The price of each word of call data, from Appendix E of the Yellow Paper. -/
def GAS_PER_WORD : Nat := 12

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- The one way a SHA-256 call can fail. -/
inductive Sha256Error where
  /-- The gas given was below the price, so the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- The stable code of an error, one per constructor.

The code ignores the arguments of the constructor.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Sha256Error.code : Sha256Error → UInt32
  | .outOfGas .. => 1

/-- Run the precompile on the call data with `gas` available.

Returns the 32-byte digest, or the error that consumes all the gas.

The gas is charged first, then the whole call data is hashed. -/
def sha256 (data : ByteArray) (gas : Nat) : Except Sha256Error ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok (Cryptography.Hash.sha256 data)

end EthLib.Execution.Evm.Precompiles.Sha256

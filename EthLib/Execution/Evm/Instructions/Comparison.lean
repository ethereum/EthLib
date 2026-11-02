module

public import EthLib.Base.U256

/-!
# `Evm.Instructions.Comparison`

The comparison instructions of the EVM, from LT to ISZERO.

Source: [`forks/frontier/vm/instructions/comparison.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/instructions/comparison.py) of execution-specs at `2c0c8e7`.

Every later fork there computes the same results, up to Bogota.

Each pushes 1 when its condition holds, and 0 otherwise.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base

/-- `less_than`: whether `left < right`, as unsigned integers. -/
def lessThan (left right : U256) : U256 := if left.toNat < right.toNat then 1 else 0

/-- `signed_less_than`: whether `left < right`, in two's complement. -/
def signedLessThan (left right : U256) : U256 :=
  if U256.toSigned left < U256.toSigned right then 1 else 0

/-- `greater_than`: whether `left > right`, as unsigned integers. -/
def greaterThan (left right : U256) : U256 := if left.toNat > right.toNat then 1 else 0

/-- `signed_greater_than`: whether `left > right`, in two's complement. -/
def signedGreaterThan (left right : U256) : U256 :=
  if U256.toSigned left > U256.toSigned right then 1 else 0

/-- `equal`: whether `left = right`. -/
def equal (left right : U256) : U256 := if left = right then 1 else 0

/-- `is_zero`: whether `x = 0`. -/
def isZero (x : U256) : U256 := if x = 0 then 1 else 0

end EthLib.Execution.Evm.Instructions

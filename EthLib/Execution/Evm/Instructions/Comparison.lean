module

public import EthLib.Base.U256

/-!
# `Evm.Instructions.Comparison`

The comparison instructions of the EVM, from LT to ISZERO.

Source: Appendix H.2 of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

Every fork since Frontier computes the same results.

Each pushes 1 when its condition holds, and 0 otherwise.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- Whether `left < right`, as unsigned integers. -/
def lessThan (left right : U256) : U256 := if left.toNat < right.toNat then 1 else 0

/-- Whether `left < right`, in two's complement. -/
def signedLessThan (left right : U256) : U256 :=
  if U256.toSigned left < U256.toSigned right then 1 else 0

/-- Whether `left > right`, as unsigned integers. -/
def greaterThan (left right : U256) : U256 := if left.toNat > right.toNat then 1 else 0

/-- Whether `left > right`, in two's complement. -/
def signedGreaterThan (left right : U256) : U256 :=
  if U256.toSigned left > U256.toSigned right then 1 else 0

/-- Whether `left = right`. -/
def equal (left right : U256) : U256 := if left = right then 1 else 0

/-- Whether `x = 0`. -/
def isZero (x : U256) : U256 := if x = 0 then 1 else 0

end EthLib.Execution.Evm

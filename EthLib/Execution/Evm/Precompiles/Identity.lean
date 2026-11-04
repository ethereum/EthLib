module

public import EthLib.Execution.Evm.Words

/-!
# `Evm.Precompiles.Identity`

The IDENTITY precompile at address `0x04`: it returns its call data unchanged.

So contracts can copy memory cheaply.

```text
gas:     15 + 3 * ceil(len(data) / 32)
output:  data
```

Source: Appendix E of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

Every fork since Frontier computes the same result with the same prices.

The call fails only when it runs out of gas.
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

/-- `identity`: the call data itself, once the gas covers the price. -/
def identity (data : ByteArray) (gas : Nat) : Except IdentityError ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok data

end EthLib.Execution.Evm.Precompiles.Identity

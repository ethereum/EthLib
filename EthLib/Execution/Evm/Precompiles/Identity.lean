module

public import EthLib.Execution.Evm.Words

/-!
# `Evm.Precompiles.Identity`

The IDENTITY precompile at address `0x04`: it returns its call data unchanged, so contracts can copy memory cheaply.

```text
gas:     15 + 3 * ceil(len(data) / 32)
output:  data
```

Source: [`forks/frontier/vm/precompiled_contracts/identity.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/precompiled_contracts/identity.py#L22-L43) of execution-specs at `2c0c8e7`, function `identity`.

Every later fork there computes the same result with the same prices, up to Bogota.

The call fails only when it runs out of gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

open EthLib.Execution.Evm (wordCount)

/-- The price of every call, `GasCosts.PRECOMPILE_IDENTITY_BASE` in [`forks/frontier/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/gas.py#L70). -/
def GAS_BASE : Nat := 15

/-- The price of each word of call data, `GasCosts.PRECOMPILE_IDENTITY_PER_WORD` in [`forks/frontier/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/gas.py#L71). -/
def GAS_PER_WORD : Nat := 3

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- Why an IDENTITY call fails. -/
inductive IdentityError where
  /-- The gas given was below the price, so `charge_gas` raises `OutOfGasError` and the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- `identity`: the call data itself, once the gas covers the price. -/
def identity (data : ByteArray) (gas : Nat) : Except IdentityError ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok data

end EthLib.Execution.Evm.Precompiles.Identity

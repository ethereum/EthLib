module

public import EthLib.Execution.Evm.Words

/-!
# `EthLib.Execution.Evm.Precompiles.Identity`

The IDENTITY precompile at address `0x04`: its gas, its failure and its output.

The precompile charges a base price plus a price for each EVM word of call data.
Then it returns the call data unchanged.

```text
gas:     15 + 3 * ceil(len(data) / 32)
output:  data
```

The executable source is `identity` in `src/ethereum/forks/amsterdam/vm/precompiled_contracts/identity.py`.
The file is in `ethereum/execution-specs`, at commit `fd9298410ec7218838c8348f69c1eb633f1797dc`.
It charges `PRECOMPILE_IDENTITY_BASE + PRECOMPILE_IDENTITY_PER_WORD * word_count` with `charge_gas`, then sets `evm.output = data`.
The two prices are in `GasCosts`, in `src/ethereum/forks/amsterdam/vm/gas.py` at the same commit.
Amsterdam is the execution-layer fork of Glamsterdam, EIP-7773.

Frontier introduced the precompile.
At the same commit, every fork from Frontier to BPO5 has a byte-identical `identity.py`.
Amsterdam reads `evm.call_data` instead of `evm.message.data`, and wraps the price in `ExecutionGas`.
Neither change alters the output.
The `gas.py` files of Frontier and Amsterdam both set the prices to 15 and 3.

The only failure is a lack of gas.
`charge_gas` raises `OutOfGasError` when the execution gas left is strictly below the price.
So a call with exactly the price succeeds.
Here `gas` is that execution gas left, the `gas_left` of the gas meter of the frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Identity

/-- The price of every call, `GasCosts.PRECOMPILE_IDENTITY_BASE` in execution-specs. -/
def GAS_BASE : Nat := 15

/-- The price of each EVM word of call data, `GasCosts.PRECOMPILE_IDENTITY_PER_WORD` in execution-specs. -/
def GAS_PER_WORD : Nat := 3

/-- The gas that a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- The one way an IDENTITY call can fail. -/
inductive IdentityError where
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in `src/ethereum/forks/amsterdam/vm/gas.py`.

  The interpreter then refills the state gas of the frame to its baseline, with `restore_state_gas`.

  It sets the execution gas left to zero, with `forfeit_remaining_gas`, and the output to empty. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- Human-readable description of the failure. -/
def IdentityError.message : IdentityError → String
  | .outOfGas cost gas => s!"out of gas: price {cost}, gas {gas}"

/-- Run the precompile on the call data with `gas` available.

Returns the call data, or the error after which the interpreter consumes all the execution gas left.

`identity` in execution-specs: the gas is charged first, then the output is the call data. -/
def identity (data : ByteArray) (gas : Nat) : Except IdentityError ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok data

end EthLib.Execution.Evm.Precompiles.Identity

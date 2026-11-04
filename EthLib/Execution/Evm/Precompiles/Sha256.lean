module

public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Execution.Evm.Words

/-!
# `EthLib.Execution.Evm.Precompiles.Sha256`

The SHA-256 precompile at address `0x02`: its gas, its failure and its output.

The precompile charges a base price plus a price per 32-byte word of call data, then hashes the whole call data.

```text
gas:     60 + 12 * ceil(len(data) / 32)
output:  [ SHA-256(data): 32 ]
```

Source: [`forks/frontier/vm/precompiled_contracts/sha256.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/precompiled_contracts/sha256.py#L24-L45) of execution-specs at `2c0c8e7`, function `sha256`.

It charges `PRECOMPILE_SHA256_BASE + PRECOMPILE_SHA256_PER_WORD * word_count` with `charge_gas`, then returns `hashlib.sha256(data).digest()`.

Every later fork there computes the same result with the same prices, up to Bogota.

The call fails only when it runs out of gas.

`charge_gas` raises `OutOfGasError` when the gas left is strictly below the price, so a call with exactly the price succeeds.

The hash is `EthLib.Cryptography.Hash.sha256`, the FIPS 180-4 hash of the cryptography layer.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Sha256

open EthLib.Execution.Evm (wordCount)

/-- The size of the output in bytes: one SHA-256 digest. -/
def OUTPUT_BYTES : Nat := 32

/-- The price of every call, `GasCosts.PRECOMPILE_SHA256_BASE` in [`forks/frontier/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/gas.py#L66). -/
def GAS_BASE : Nat := 60

/-- The price of each word of call data, `GasCosts.PRECOMPILE_SHA256_PER_WORD` in [`forks/frontier/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/gas.py#L67). -/
def GAS_PER_WORD : Nat := 12

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- The one way a SHA-256 call can fail. -/
inductive Sha256Error where
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in [`forks/frontier/vm/gas.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/gas.py#L183-L198), and the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- Human-readable description of the failure. -/
def Sha256Error.message : Sha256Error → String
  | .outOfGas cost gas => s!"out of gas: price {cost}, gas {gas}"

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Sha256Error.code : Sha256Error → UInt32
  | .outOfGas .. => 1

/-- Run the precompile on the call data with `gas` available.

Returns the 32-byte digest, or the error that consumes all the gas.

`sha256` in execution-specs: the gas is charged first, then the whole call data is hashed. -/
def sha256 (data : ByteArray) (gas : Nat) : Except Sha256Error ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok (Cryptography.Hash.sha256 data)

end EthLib.Execution.Evm.Precompiles.Sha256

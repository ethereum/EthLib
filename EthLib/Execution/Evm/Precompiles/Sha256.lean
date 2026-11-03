module

public import EthLib.Cryptography.Hash.Sha256

/-!
# `EthLib.Execution.Evm.Precompiles.Sha256`

The SHA-256 precompile at address `0x02`: its gas, its failure and its output.

The precompile charges a base price plus a price per 32-byte word of call data, then hashes the whole call data.

```text
gas:     60 + 12 * ceil(len(data) / 32)
output:  [ SHA-256(data): 32 ]
```

The executable source is `src/ethereum/forks/amsterdam/vm/precompiled_contracts/sha256.py` in `ethereum/execution-specs`, at commit `fd9298410ec7218838c8348f69c1eb633f1797dc`.
It charges `PRECOMPILE_SHA256_BASE + PRECOMPILE_SHA256_PER_WORD * word_count` with `charge_gas`, then returns `hashlib.sha256(data).digest()`.
The two prices are in `GasCosts`, in `src/ethereum/forks/amsterdam/vm/gas.py` at the same commit.
Amsterdam is the execution-layer fork of Glamsterdam, EIP-7773.

The only failure is running out of gas.
`charge_gas` raises `OutOfGasError` when the execution gas left is strictly below the price, so a call with exactly the price succeeds.
Here `gas` is that execution gas left, the `gas_left` of the frame's gas meter.
The hash is `EthLib.Cryptography.Hash.sha256`, the FIPS 180-4 hash of the cryptography layer.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Sha256

/-- The size of the output in bytes: one SHA-256 digest. -/
def OUTPUT_BYTES : Nat := 32

/-- The size in bytes of the word the gas counts. -/
def WORD_BYTES : Nat := 32

/-- The price of every call, `GasCosts.PRECOMPILE_SHA256_BASE` in execution-specs. -/
def GAS_BASE : Nat := 60

/-- The price of each word of call data, `GasCosts.PRECOMPILE_SHA256_PER_WORD` in execution-specs. -/
def GAS_PER_WORD : Nat := 12

/-- The least multiple of 32 that is at least `value`, `ceil32` in `src/ethereum/utils/numeric.py` of execution-specs. -/
def ceil32 (value : Nat) : Nat :=
  if value % WORD_BYTES = 0 then value else value + WORD_BYTES - value % WORD_BYTES

/-- The number of 32-byte words that cover `size` bytes, `word_count` in `sha256` of execution-specs. -/
def wordCount (size : Nat) : Nat := ceil32 size / WORD_BYTES

/-- The gas a call with `size` bytes of call data is charged. -/
def gasCost (size : Nat) : Nat := GAS_BASE + GAS_PER_WORD * wordCount size

/-- The one way a SHA-256 call can fail. -/
inductive Sha256Error where
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in `src/ethereum/forks/amsterdam/vm/gas.py`, and the call consumes all its gas. -/
  | outOfGas (cost gas : Nat)
  deriving Repr, DecidableEq

/-- Human-readable description of the failure. -/
def Sha256Error.message : Sha256Error → String
  | .outOfGas cost gas => s!"out of gas: price {cost}, gas {gas}"

/-- Run the precompile on the call data with `gas` available.

Returns the 32-byte digest, or the error that consumes all the gas.

`sha256` in execution-specs: the gas is charged first, then the whole call data is hashed. -/
def sha256 (data : ByteArray) (gas : Nat) : Except Sha256Error ByteArray :=
  let cost := gasCost data.size
  if gas < cost then .error (.outOfGas cost gas) else .ok (Cryptography.Hash.sha256 data)

end EthLib.Execution.Evm.Precompiles.Sha256

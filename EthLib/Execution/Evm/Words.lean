module

/-!
# `EthLib.Execution.Evm.Words`

The number of 32-byte EVM words that cover a byte length.

Several prices of the EVM grow with each started EVM word of their input.
Execution-specs computes that count as `ceil32(length) // 32`.

`ceil32` is in `src/ethereum/utils/numeric.py` of `ethereum/execution-specs`, at commit `fd9298410ec7218838c8348f69c1eb633f1797dc`.
It returns its argument when the argument is a multiple of 32.
Otherwise it adds `32 - argument % 32`.

```text
length:     0   1  31  32  33  64  65
ceil32:     0  32  32  32  64  64  96
wordCount:  0   1   1   1   2   2   3
```
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- The size of one EVM word in bytes. -/
def WORD_BYTES : Nat := 32

/-- The least multiple of 32 that is at least `value`, `ceil32` in `src/ethereum/utils/numeric.py` of execution-specs. -/
def ceil32 (value : Nat) : Nat :=
  if value % WORD_BYTES = 0 then value else value + WORD_BYTES - value % WORD_BYTES

/-- The number of EVM words that cover `size` bytes, `ceil32(size) // 32` in execution-specs. -/
def wordCount (size : Nat) : Nat := ceil32 size / WORD_BYTES

end EthLib.Execution.Evm

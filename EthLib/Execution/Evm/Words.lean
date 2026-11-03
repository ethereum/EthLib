module

/-!
# `Evm.Words`

The EVM prices many operations per 32-byte word, so it rounds byte counts up to whole words.

For example, 33 bytes take 2 words, since the 33rd byte starts a second word.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- The size of an EVM word in bytes. -/
def WORD_BYTES : Nat := 32

/-- `ceil32`: the least multiple of 32 that is at least `value`.

Source: [`utils/numeric.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/utils/numeric.py#L43) of execution-specs at `2c0c8e7`. -/
def ceil32 (value : Nat) : Nat :=
  if value % WORD_BYTES = 0 then value else value + WORD_BYTES - value % WORD_BYTES

/-- The number of 32-byte words that cover `size` bytes: `ceil32(size) // 32` in execution-specs. -/
def wordCount (size : Nat) : Nat := ceil32 size / WORD_BYTES

end EthLib.Execution.Evm

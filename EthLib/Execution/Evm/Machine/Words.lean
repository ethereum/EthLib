module

/-!
# `Evm.Machine.Words`

The EVM prices many operations per 32-byte word, so it rounds byte counts up to whole words.

For example, 33 bytes take 2 words, since the 33rd byte starts a second word.
-/

@[expose] public section

namespace EthLib.Execution.Evm

/-- The size of an EVM word in bytes. -/
def WORD_BYTES : Nat := 32

/-- The least multiple of 32 that is at least `value`. -/
def ceil32 (value : Nat) : Nat :=
  if value % WORD_BYTES = 0 then value else value + WORD_BYTES - value % WORD_BYTES

/-- The number of 32-byte words that cover `size` bytes: `size` rounded up to 32, over 32. -/
def wordCount (size : Nat) : Nat := ceil32 size / WORD_BYTES

end EthLib.Execution.Evm

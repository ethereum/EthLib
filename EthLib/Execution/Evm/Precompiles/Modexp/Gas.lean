module

public import EthLib.Base.Fork
public import EthLib.Execution.Evm.Precompiles.Modexp.Constants

/-!
# `Modexp.Gas`

The gas charged by MODEXP, which Byzantium adds.

Three EIPs set the price, each from its fork:

- EIP-198, from Byzantium: the complexity times the iterations, over 20.
- EIP-2565, from Berlin: a new complexity, over 3, and at least 200.
- EIP-7883, from Fusaka: a higher complexity, twice the iterations per exponent byte, at least 500.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base (Fork)

/-- The multiplication complexity, set by the longer of the base and the modulus. -/
def complexity (fork : Fork) (baseLen modLen : Nat) : Nat :=
  let maxLength := max baseLen modLen
  -- The 8-byte words of the longer length, rounded up.
  let words := (maxLength + WORD_BYTES - 1) / WORD_BYTES
  if fork ≥ .fusaka then
    -- EIP-7883: a flat 16 up to 32 bytes, and twice the square of the words above.
    if maxLength > SMALL_LENGTH_BYTES then 2 * words ^ 2 else MIN_COMPLEXITY
  else if fork ≥ .berlin then
    -- EIP-2565: the square of the words.
    words ^ 2
  else
    -- EIP-198: a piecewise square of the length in bytes.
    if maxLength ≤ 64 then maxLength ^ 2
    else if maxLength ≤ 1024 then maxLength ^ 2 / 4 + 96 * maxLength - 3072
    else maxLength ^ 2 / 16 + 480 * maxLength - 199680

/-- The iteration count: the adjusted exponent length, at least 1.

EIP-198 defines it, and EIP-7883 doubles the count per exponent byte past the first 32. -/
def iterations (fork : Fork) (expLen expHead : Nat) : Nat :=
  -- `expHead` is the integer in the first `min 32 expLen` bytes of the exponent.
  --
  -- The index of its highest set bit is `Nat.log2 expHead`, and `0` when no bit is set.
  --
  -- So one formula covers both the zero and the non-zero head.
  --
  -- For example:
  --
  -- - a head of `0x10001` has its highest bit at 16
  -- - a head of 1 has its highest bit at 0
  -- - a head of 0 has no bit set, and counts as 0
  let bitsPart := Nat.log2 expHead
  -- Every exponent byte past the first 32 adds 16 iterations from Fusaka, and 8 before.
  let perByte := if fork ≥ .fusaka then ITERATIONS_PER_EXTRA_EXPONENT_BYTE else 8
  -- Where the sources read differently, this follows EIP-198.
  --
  -- EIP-198 takes the exponent bits from the first 32 bytes of the exponent.
  --
  -- It takes the index of the highest set bit in those 32 bytes.
  --
  -- When those 32 bytes are all zero, it gives exactly `8 * (expLen - 32)`.
  --
  -- EIP-7883 scales that 8 to 16.
  --
  -- Read literally, the EIP-7883 pseudocode differs in two ways for an exponent past 32 bytes:
  --
  -- - It takes `exponent mod 2^256`, the low 256 bits of the whole exponent.
  -- - When those bits are zero it adds the bit length of 0 minus 1, that is -1, one iteration less.
  --
  -- The EIP-2565 pseudocode is the same, with 8 in place of 16.
  let count :=
    if expLen ≤ EXPONENT_HEAD_BYTES then bitsPart
    else perByte * (expLen - EXPONENT_HEAD_BYTES) + bitsPart
  -- A zero exponent still costs one iteration.
  max count 1

/-- The gas of one call, from the three lengths and the exponent head. -/
def gasCost (fork : Fork) (baseLen modLen expLen expHead : Nat) : Nat :=
  let cost := complexity fork baseLen modLen * iterations fork expLen expHead
  -- EIP-7883 drops the division, and raises the least price to 500.
  if fork ≥ .fusaka then max MIN_GAS cost
  -- EIP-2565 divides by 3, and charges at least 200.
  else if fork ≥ .berlin then max 200 (cost / 3)
  -- EIP-198 divides by 20.
  else cost / 20

end EthLib.Execution.Evm.Precompiles.Modexp

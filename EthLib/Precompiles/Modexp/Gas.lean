module

public import EthLib.Precompiles.Modexp.Constants

/-!
# `Modexp.Gas`

The gas charged by MODEXP.

The rule is EIP-7883.

It replaced the pricing of EIP-2565, which replaced the pricing of EIP-198.

No older pricing is specified here.

The executable source is `complexity`, `iterations` and `gas_cost`.
They are in `forks/bpo2/vm/precompiled_contracts/modexp.py`, in execution-specs at `2c0c8e7`.

```text
    gas = max(500, complexity(len_base, len_mod) * iterations(len_exp, exp_head))
```

## Where the sources read differently

EIP-198 and execution-specs take the exponent bits from the first 32 bytes of `EXPONENT`.

EIP-198 says: "the index of the highest bit in the first 32 bytes of `EXPONENT`".

It adds: "If all of the first 32 bytes of `EXPONENT` are zero, return exactly `8 * (length_of_EXPONENT - 32)`".

EIP-7883 scales that 8 to 16.

The EIP-7883 pseudocode, read literally, differs in two ways for an exponent longer than 32 bytes:

- It writes `exponent & (2**256 - 1)`, the LOW 256 bits of the whole exponent.
- When those bits are zero it adds `(0).bit_length() - 1 = -1`, one iteration less.

The EIP-2565 pseudocode is the same, with 8 in place of 16.

This module follows EIP-198 and execution-specs, which agree with each other.
-/

@[expose] public section

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

/-- The multiplication complexity.

EIP-7883, Specification, `calculate_multiplication_complexity`.

`complexity` in execution-specs.

- Operands of at most 32 bytes cost a flat 16.
- Longer ones cost twice the square of their length in 8-byte words. -/
def complexity (baseLen modLen : Nat) : Nat :=
  -- The longer of the two operands sets the cost.
  let maxLength := max baseLen modLen
  -- `math.ceil(max_length / 8)`, in integers.
  let words := (maxLength + WORD_BYTES - 1) / WORD_BYTES
  if maxLength > SMALL_LENGTH_BYTES then 2 * words ^ 2 else MIN_COMPLEXITY

/-- The iteration count: the adjusted exponent length, at least 1.

EIP-7883, Specification, `calculate_iteration_count`, read as in EIP-198.

`iterations` in execution-specs.

`expHead` is the integer in the first `min 32 expLen` bytes of the exponent.

The index of its highest set bit is `Nat.log2 expHead`, and `0` when no bit is set.

So one formula covers both the zero and the non-zero head.

```text
    expHead = 0x10001   highest bit 16
    expHead = 1         highest bit 0
    expHead = 0         no bit set, counted as 0
``` -/
def iterations (expLen expHead : Nat) : Nat :=
  let bitsPart := Nat.log2 expHead
  let count :=
    if expLen ≤ EXPONENT_HEAD_BYTES then bitsPart
    -- Every exponent byte past the first 32 adds 16 iterations.
    else ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) + bitsPart
  -- A zero exponent still costs one iteration.
  max count 1

/-- The gas of one call, from the three lengths and the exponent head.

EIP-7883, Specification, `calculate_gas_cost`.

`gas_cost` in execution-specs.

EIP-7883 removed the division by 3 that EIP-2565 applied. -/
def gasCost (baseLen modLen expLen expHead : Nat) : Nat :=
  max MIN_GAS (complexity baseLen modLen * iterations expLen expHead)

end EthLib.Precompiles.Modexp

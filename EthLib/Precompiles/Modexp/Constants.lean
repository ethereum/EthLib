module

/-!
# `Modexp.Constants`

The fixed numbers of the MODEXP precompile at address `0x05`.

Every value is the one in force as of the BPO2 fork.

BPO2 is the latest fork activated on mainnet in `ethereum/execution-specs`.
The commit is `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.
BPO2 activated at timestamp 1767747671, on 2026-01-07.

BPO2 changes only blob parameters.
So MODEXP behaves as in Osaka, the fork that introduced EIP-7823 and EIP-7883.
-/

@[expose] public section

namespace EthLib.Precompiles.Modexp.Constants

/-- Width in bytes of each of the three length headers.

EIP-198, Specification: "every length is a 32-byte left-padded integer". -/
def LENGTH_HEADER_BYTES : Nat := 32

/-- Offset of `BASE` in the input.

It follows the three length headers.

EIP-198, Specification:
`<length_of_BASE> <length_of_EXPONENT> <length_of_MODULUS> <BASE> <EXPONENT> <MODULUS>`. -/
def BASE_OFFSET : Nat := 3 * LENGTH_HEADER_BYTES

/-- Largest accepted value of each length header, in bytes.

1024 bytes is 8192 bits.

EIP-7823, Specification. -/
def MAX_LENGTH_BYTES : Nat := 1024

/-- Number of leading exponent bytes that enter the gas formula.

EIP-198, Specification, `ADJUSTED_EXPONENT_LENGTH`: "the first 32 bytes of `EXPONENT`".

`iterations` in execution-specs reads the same 32 bytes. -/
def EXPONENT_HEAD_BYTES : Nat := 32

/-- Bytes per word in the multiplication complexity.

EIP-7883, Specification: `words = math.ceil(max_length / 8)`. -/
def WORD_BYTES : Nat := 8

/-- Largest operand length, in bytes, that is charged the flat complexity.

EIP-7883, Specification, `calculate_multiplication_complexity`. -/
def SMALL_LENGTH_BYTES : Nat := 32

/-- Multiplication complexity of operands of at most 32 bytes.

EIP-7883, Specification, `calculate_multiplication_complexity`. -/
def MIN_COMPLEXITY : Nat := 16

/-- Iterations charged per exponent byte beyond the first 32.

EIP-7883, Specification, `calculate_iteration_count`.

EIP-2565 charged 8, and EIP-7883 doubles it. -/
def ITERATIONS_PER_EXTRA_EXPONENT_BYTE : Nat := 16

/-- The least gas the precompile ever charges.

EIP-7883, Specification, `calculate_gas_cost`.

EIP-2565 charged at least 200. -/
def MIN_GAS : Nat := 500

end EthLib.Precompiles.Modexp.Constants

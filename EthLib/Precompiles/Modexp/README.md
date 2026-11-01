# MODEXP precompile

MODEXP is the precompiled contract at address `0x05`.
It computes `BASE ^ EXPONENT mod MODULUS` for integers of up to 1024 bytes each.
RSA verification and other number-theoretic checks use it, because the same work written in EVM code would cost far more gas.
Every client must return the same bytes and charge the same gas, or the chain splits.

For example, with `BASE = 3`, `EXPONENT = 5` and `MODULUS = 7`, the result is `3^5 mod 7 = 243 mod 7 = 5`, since `243 = 34 * 7 + 5`.

This page was written with the module, on top of EthLib commit `f46b990`.
Check it again when a definition it names changes.

## Source

The module follows the rules in force as of BPO2, the latest fork activated on mainnet.
Three EIPs define them:

- [EIP-198](https://eips.ethereum.org/EIPS/eip-198) defines the input layout, the output and the arithmetic.
- [EIP-7883](https://eips.ethereum.org/EIPS/eip-7883) defines the gas price.
- [EIP-7823](https://eips.ethereum.org/EIPS/eip-7823) bounds each length by 1024 bytes.

The executable source is `src/ethereum/forks/bpo2/vm/precompiled_contracts/modexp.py` in `ethereum/execution-specs`, at commit `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.
It is identical to the Osaka module, where EIP-7823 and EIP-7883 took effect.

The input starts with three 32-byte lengths, followed by the three numbers they describe:

```text
input:   [ len_base: 32 | len_exp: 32 | len_mod: 32 | BASE | EXPONENT | MODULUS ]
output:  BASE ^ EXPONENT mod MODULUS, on len_mod bytes
gas:     max(500, complexity(len_base, len_mod) * iterations(len_exp, exp_head))
```

The call data reads as if it were followed by infinitely many zero bytes, so a short input is padded with zeros, and data past the last field is ignored.

A zero modulus gives `len_mod` zero bytes.
EIP-198 does not say this, but execution-specs does.

### Where the sources read differently

For an exponent longer than 32 bytes, the EIP-7883 pseudocode, read literally, disagrees with EIP-198 and execution-specs in two places:

- It takes the bits from `exponent & (2**256 - 1)`, the low 256 bits of the whole exponent, while EIP-198 and execution-specs take them from the first 32 bytes.
- When those bits are zero, it adds `(0).bit_length() - 1 = -1`, while EIP-198 says to return exactly the length part, and execution-specs does so.

The EIP-2565 pseudocode has the same two differences, with 8 in place of 16.
This module follows EIP-198 and execution-specs, which agree with each other.
The theorem `iterations_long_zero_head` (`Proofs/Modexp/Gas.lean`) pins the second case.

## Operations

The exports are in `EthLib/Precompiles/Exports/Modexp.lean`.

| Lean | File | C export | Python |
| --- | --- | --- | --- |
| `modexp` | `Core.lean` | `eth_modexp` | `modexp.modexp` |
| `chargedGas` | `Core.lean` | `eth_modexp_gas_cost` | `modexp.gas_cost` |

In Python, a length above 1024 and a lack of gas both raise `ValueError`.

## Test vectors

`tests/` has no MODEXP vectors yet.
The proofs pin known answers instead, all checked by the kernel:

- the five worked inputs of EIP-198, run through the whole precompile;
- the smallest cases of `tests/byzantium/eip198_modexp_precompile/test_modexp.py` in execution-specs;
- the 15 `modexp_nagydani_*` prices of the EIP-7883 table;
- the five highest-bit examples of EIP-198.

## What is proved

The proofs are in `EthLib/Precompiles/Proofs/Modexp/`.

The arithmetic comes first.
The code computes the power by square-and-multiply, and that loop equals `b ^ e % m` for every modulus (`powMod_eq`, `PowMod.lean`).
So the output is `BASE ^ EXPONENT mod MODULUS`, or 0 for a zero modulus (`compute_eq_pow_mod`, `Core.lean`), and a successful call returns exactly `len_mod` bytes (`modexp_ok_size`, `Core.lean`).

The next statements, all in `Core.lean`, pin how the input is read.
Appending zero bytes to the input changes nothing (`modexp_append_zeros`), and neither does data past the last field (`modexp_append_excess`).
More generally, two inputs that agree on the bytes the lengths cover give the same result (`modexp_congr`).
Each length above the bound of EIP-7823 makes the call fail before any gas is charged, whatever the gas (`modexp_base_too_large`, `modexp_exponent_too_large`, `modexp_modulus_too_large`).

Then gas.
With every length in bounds, a call fails exactly when the gas is below the price (`modexp_out_of_gas`, `modexp_ok`, `Core.lean`).
The price is at least 500, and it does not fall when a length grows (`Gas.lean`).
It is at most 528449536, so it fits in 64 bits (`gasCost_le`, `Gas.lean`, and `chargedGas_le`, `Core.lean`).

## What is not proved

No theorem says that the module agrees with execution-specs on inputs other than the known answers.
The code follows `modexp.py` step by step, but no theorem relates the two.

Nothing is proved about the cost of computing the result, which the gas price is meant to cover.

## What the kernel cannot evaluate

Nothing in this module.
Every known answer uses `decide` or `decide +kernel`, and none uses `native_decide`.

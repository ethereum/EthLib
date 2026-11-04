# MODEXP precompile

MODEXP is the precompiled contract at address `0x05`.
It computes `BASE ^ EXPONENT mod MODULUS` for integers of up to 1024 bytes each.
RSA verification and other number-theoretic checks use it, because the same work written in EVM code would cost far more gas.
Every client must return the same bytes and charge the same gas, or the chain splits.

For example, with `BASE = 3`, `EXPONENT = 5` and `MODULUS = 7`, the result is `3^5 mod 7 = 243 mod 7 = 5`, since `243 = 34 * 7 + 5`.

This page was written with the module, on top of EthLib commit `f46b990`.
Check it again when a definition it names changes.

## Source

Byzantium adds MODEXP, and the module specifies it at every fork from there.
Four EIPs define it:

- [EIP-198](https://eips.ethereum.org/EIPS/eip-198) defines the input layout, the output and the arithmetic, and the first price.
- [EIP-2565](https://eips.ethereum.org/EIPS/eip-2565) replaces the price from Berlin.
- [EIP-7883](https://eips.ethereum.org/EIPS/eip-7883) replaces it again from Fusaka.
- [EIP-7823](https://eips.ethereum.org/EIPS/eip-7823) bounds each length by 1024 bytes, from Fusaka.

So each function takes the fork, and branches at Berlin and at Fusaka.
The gas formula below is the one of Fusaka.

The input starts with three 32-byte lengths, followed by the three numbers they describe:

```text
input:   [ len_base: 32 | len_exp: 32 | len_mod: 32 | BASE | EXPONENT | MODULUS ]
output:  BASE ^ EXPONENT mod MODULUS, on len_mod bytes
gas:     max(500, complexity(len_base, len_mod) * iterations(len_exp, exp_head))
```

The call data reads as if it were followed by infinitely many zero bytes, so a short input is padded with zeros, and data past the last field is ignored.

A zero modulus gives `len_mod` zero bytes.
EIP-198 does not say this, but Appendix E of the Yellow Paper takes `x mod 0` to be zero.

### Where the sources read differently

For an exponent longer than 32 bytes, the EIP-7883 pseudocode, read literally, differs from EIP-198.
It does so in two places:

- It takes the bits from `exponent & (2**256 - 1)`, the low 256 bits of the whole exponent.
  EIP-198 takes them from the first 32 bytes.
- When those bits are zero, it adds `(0).bit_length() - 1 = -1`.
  EIP-198 says to return exactly the length part.

The EIP-2565 pseudocode has the same two differences, with 8 in place of 16.
This module follows EIP-198.
The theorem `iterations_long_zero_head` (`EthLib/Execution/Proofs/Evm/Precompiles/Modexp/Gas.lean`) pins the second case.

## Operations

The exports are in `EthLib/Execution/Exports/Modexp.lean`.

| Lean | File | C export | Python |
| --- | --- | --- | --- |
| `modexp` | `Core.lean` | `eth_modexp` | `modexp.modexp` |
| `chargedGas` | `Core.lean` | `eth_modexp_gas_cost` | `modexp.gas_cost` |

The exports run the rules of Fusaka, which hold through BPO2.
In Python, a length above 1024 and a lack of gas both raise `ValueError`.

## Test vectors

`bindings/python/tests/precompile/test_modexp.py` runs these cases through the bindings:

- The five worked inputs of EIP-198 run through the whole precompile.
- Four small inputs have an empty base and exponent, so the output is `1 mod MODULUS`, or 0 for a zero modulus.
- The 15 `modexp_nagydani_*` prices of the EIP-7883 table run through the price of Fusaka.
- The five highest-bit examples of EIP-198 run through the price.

## What is proved

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Modexp/`.

The arithmetic comes first.
The code computes the power by square-and-multiply, and that loop equals `b ^ e % m` for every modulus (`powMod_eq`, `EthLib/Execution/Proofs/Evm/PowMod.lean`).
So the output is `BASE ^ EXPONENT mod MODULUS`, or 0 for a zero modulus (`compute_eq_pow_mod`, `Core.lean`), and a successful call returns exactly `len_mod` bytes (`modexp_ok_size`, `Core.lean`).

The next statements, all in `Core.lean`, pin how the input is read.
Zero bytes appended to the input change nothing (`modexp_append_zeros`), and neither does data past the last field (`modexp_append_excess`).
More generally, two inputs that agree on the bytes the lengths cover give the same result (`modexp_congr`).
From Fusaka, each length above the bound of EIP-7823 makes the call fail before any gas is charged, whatever the gas (`modexp_base_too_large`, `modexp_exponent_too_large`, `modexp_modulus_too_large`).

Then gas.
With every length in bounds, a call fails exactly when the gas is below the price, at every fork (`modexp_out_of_gas`, `modexp_ok`, `Core.lean`).
From Fusaka, the price is at least 500, and it does not fall when a length grows (`Gas.lean`).
From Fusaka, it is at most 528449536, so it fits in 64 bits (`gasCost_le`, `Gas.lean`, and `chargedGas_le`, `Core.lean`).
The prices of EIP-198 and EIP-2565 have no theorem yet.

## What is not proved

No theorem relates the module to another implementation.
The test vectors check the agreement only on their own inputs.

Nothing is proved about the cost of computing the result, which the gas price is meant to cover.

## What the kernel cannot evaluate

Nothing in this module.

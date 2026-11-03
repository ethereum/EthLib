# ECRECOVER precompile

ECRECOVER is the precompiled contract at address `0x01`.
Given a 32-byte hash and a secp256k1 ECDSA signature of it, it returns the address of the signer.
A contract can thus check a signature for 3000 gas.
Since the result decides what a contract does, every client must return the same bytes, or the chain splits.

## Source

The executable source is `src/ethereum/forks/bpo2/vm/precompiled_contracts/ecrecover.py` in `ethereum/execution-specs`, at commit `b758df2bcaaa95c04d31e25c94fbfb8d6de756e7`.
It is identical to the Osaka module.

That source calls a library for the cryptography, so the curve, the recovery and the address follow their own standards instead:

- the recovery follows SEC 1 v2 §4.1.6, in `EthLib/Cryptography/Secp256k1/Recovery.lean`;
- the address follows Appendix F of the Yellow Paper, in `EthLib/Cryptography/Secp256k1/Address.lean`.

The call reads four 32-byte words and returns one:

```text
input:   [ hash: 32 | v: 32 | r: 32 | s: 32 ]
output:  [ 12 zero bytes | address: 20 ], or empty
gas:     3000
```

The call data reads as if it were followed by infinitely many zero bytes, so a short input is padded with zeros, and data past 128 bytes is ignored.

The output is empty when `v` is neither 27 nor 28, when `r` or `s` is not in `[1, n - 1]`, or when no key is recovered.
An empty output still counts as a successful call, and its gas is still paid.
A high `s` is accepted, because the low-s rule of EIP-2 applies to transactions only.

## Operations

| Lean | File | C export | Python |
| --- | --- | --- | --- |
| `ecrecover` | `Core.lean` | `eth_ecrecover` | `ecrecover.ecrecover` |

In Python, a lack of gas raises `ValueError`.

## Test vectors

`bindings/python/tests/ecrecover/` runs all 52 cases of `test_precompiles` in `tests/frontier/precompiles/test_ecrecover.py` of execution-specs, at the same commit.
Eight of them also run in the kernel, at the end of `EthLib/Execution/Proofs/Evm/Precompiles/Ecrecover/Core.lean`.

## What is proved

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Ecrecover/Core.lean`.

The first statement is about shape: the output is either empty or 32 bytes long (`compute_size`).

The next three say that the precompile returns the right address.
A nonempty output is the address of a key that verifies the signature (`output_verify`).
Conversely, when `r + n >= p`, every key that verifies a signature has its address returned for `v = 27` or for `v = 28` (`output_of_verify`).
And a signature made with a private key returns that key's address (`output_sign`).

ECDSA signatures come in pairs: `(v, r, s)` and `(55 - v, r, n - s)` give the same output (`output_neg_s`).
Since `v` is 27 or 28, the map `v -> 55 - v` swaps the two values.

Each documented cause of an empty output does give one: a bad `v`, an `r` or `s` out of range, and a failed recovery (`output_of_bad_v`, `output_of_range`, `output_of_recover_error`).
Only the first 128 bytes of the input count (`compute_congr`).
Lastly, a call fails exactly when the gas is below 3000 (`ecrecover_out_of_gas`, `ecrecover_ok`).

## What is not proved

No theorem says that the module agrees with execution-specs on inputs other than the known answers.
No theorem says either that `secp256k1_recover` in execution-specs, which calls a C library, computes SEC 1 recovery.

One case falls outside the converse statement.
When `r < p - n`, the point `R` of a signature may have the x-coordinate `r + n` instead of `r`.
Only the recovery ids 2 and 3 reach such a point, and the precompile accepts only `v = 27` and `v = 28`.
So such a signature recovers some other key, or none.

## What the kernel cannot evaluate

Nothing in this module.

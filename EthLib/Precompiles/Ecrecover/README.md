# ECRECOVER precompile

ECRECOVER is the precompiled contract at address `0x01`.

It returns the address that signed a 32-byte hash with secp256k1 ECDSA, so a contract can check a signature in 3000 gas.

Every client must return the same bytes, or the chain splits.

## Source

The executable source is `src/ethereum/forks/bpo2/vm/precompiled_contracts/ecrecover.py` in `ethereum/execution-specs`, at commit `b758df2bcaaa95c04d31e25c94fbfb8d6de756e7`.

It is identical to the Osaka module.

Its recovery calls a library, so the curve, the recovery and the address follow their standards instead:

- SEC 1 v2 §4.1.6 for the recovery, in `EthLib/Cryptography/Secp256k1/Recovery.lean`;
- Appendix F of the Yellow Paper for the address, in `EthLib/Cryptography/Secp256k1/Address.lean`.

```text
input:   [ hash: 32 | v: 32 | r: 32 | s: 32 ]
output:  [ 12 zero bytes | address: 20 ], or empty
gas:     3000
```

The call data reads as if followed by infinitely many zero bytes, so a short input is padded.

Data past 128 bytes is ignored.

The output is empty when `v` is neither 27 nor 28, when `r` or `s` is not in `[1, n - 1]`, or when no key is recovered.

An empty output is still a successful call, and its gas is still paid.

A high `s` is accepted: the low-s rule of EIP-2 is for transactions only.

## Operations

```text
Lean       file          C export        Python
ecrecover  Core.lean     eth_ecrecover   ecrecover.ecrecover
```

A lack of gas raises `ValueError` in Python.

## Test vectors

`bindings/python/tests/ecrecover/` runs all 52 cases of `test_precompiles` in `tests/frontier/precompiles/test_ecrecover.py` of execution-specs, at the same commit.

Eight of them also run in the kernel, at the end of `EthLib/Precompiles/Proofs/Ecrecover/Core.lean`.

## What is proved

The proofs are in `EthLib/Precompiles/Proofs/Ecrecover/Core.lean`.

- The output is empty or 32 bytes (`compute_size`).
- A nonempty output is the address of a key that verifies the signature (`output_verify`).
- Every key that verifies a signature has its address returned for `v = 27` or `v = 28`, when `r + n >= p` (`output_of_verify`).
- `(v, r, s)` and `(55 - v, r, n - s)` give the same output (`output_neg_s`).
- A signature made with a private key returns that key's address (`output_sign`).
- Each documented cause of an empty output gives one: a bad `v`, an `r` or `s` out of range, a failed recovery (`output_of_bad_v`, `output_of_range`, `output_of_recover_error`).
- Only the first 128 bytes count (`compute_congr`).
- A call fails exactly when the gas is below 3000 (`ecrecover_out_of_gas`, `ecrecover_ok`).

## What is not proved

- That the module agrees with execution-specs on inputs other than the known answers.
- That `secp256k1_recover` in execution-specs, which calls a C library, computes SEC 1 recovery.

When `r < p - n`, a signature's point `R` may have `x = r + n`.

Only the recovery ids 2 and 3 reach it, and the precompile accepts only `v = 27` and `v = 28`.

So such a signature recovers some other key, or none.

## What the kernel cannot evaluate

Nothing in this module.

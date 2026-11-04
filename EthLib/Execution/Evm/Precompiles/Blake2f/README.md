# BLAKE2F precompile

BLAKE2F is the precompiled contract at address `0x09`.
It runs F, the compression function of the hash BLAKE2b, with as many rounds as the caller asks for.
F processes one 128-byte block of a message, so a contract that hashes a longer message calls it once per block, as RFC 7693 §3.3 does.

## Source

- [EIP-152](https://eips.ethereum.org/EIPS/eip-152) defines the input layout, the errors and the output.
- [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) §3.2 defines F itself.
- Neither fixes the order of the two checks, so the module checks the length before the flag.

## Layout

The input is the state of F, laid out field after field, and the output is the new state vector `h`:

```text
input:   [ rounds: 4 | h: 64 | m: 128 | t0: 8 | t1: 8 | f: 1 ]
output:  [ h: 64 ]
```

The rounds field is big-endian, while every 64-bit word of `h`, `m`, `t0` and `t1` is little-endian, as in BLAKE2b.
The flag byte `f` is `1` for true and `0` for false.

A call costs one gas per round, as EIP-152 sets.
A call fails on an input length other than 213 bytes, on too little gas, or on a flag byte other than `0` and `1`.
The call checks the length first, then the gas, then the flag byte.

The precompile table runs the call at address `0x09`, and the Python bindings reach it through that table.

## What is proved

The proofs are in `EthLib/Execution/Proofs/Evm/Precompiles/Blake2f.lean` and `EthLib/Cryptography/Proofs/Hash/Blake2b.lean`.

The main statement describes the whole precompile.
A call fails exactly on a wrong length, too little gas or a wrong flag byte, in that order.
Otherwise it returns F applied to the decoded fields.
Two further statements make sure the bytes are read and written correctly.
Every field is decoded with its own endianness, for every input, and the output words are encoded in the same way as the input words.

The remaining statements check the constants of F against their definitions in RFC 7693.
Each word of the initialization vector IV comes from the square root of its prime, as RFC 7693 §2.6 defines it.
Each row of the message schedule is a permutation of the 16 message words, and round `i` uses row `i mod 10` of the schedule.

## Test vectors

The Python tests in `bindings/python/tests/precompile/test_blake2f.py` run the precompile through the bindings.
They check test vectors 0 to 7 of EIP-152, and the rounds field of test vector 8.
They also check BLAKE2b-512 of the 128 bytes `0x00` to `0x7f`, and test vector 5 with `t1 = 1`.
An independent Python transcription of F confirms the last value, which no published vector gives.

## Not proved

No theorem relates F to another statement of RFC 7693 §3.2.
The code transcribes §3.2 line by line instead.

The output of test vector 8 is not checked, because it asks for `2^32 - 1` rounds.

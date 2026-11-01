# BLAKE2F precompile

BLAKE2F is the precompiled contract at address `0x09`.

It runs F, the compression function of BLAKE2b, with as many rounds as the caller asks for.

## Source

- [EIP-152](https://eips.ethereum.org/EIPS/eip-152): the input layout, the errors and the output.
- [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) §3.2: F itself.
- [`blake2f`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/bpo2/vm/precompiled_contracts/blake2f.py) in execution-specs: the order of the two checks.

## Layout

```text
input:   [ rounds: 4 | h: 64 | m: 128 | t0: 8 | t1: 8 | f: 1 ]
output:  [ h: 64 ]
```

- The rounds field is big-endian.
- Every word of `h`, `m`, `t0` and `t1` is 64 bits, little-endian.
- The flag byte is `1` for true and `0` for false.

A call fails when the input is not 213 bytes long.

It also fails when the flag byte is anything else.

The length is checked first.

The gas cost, one per round, is not part of the module.

Neither is a C export or a Python binding.

## What is proved

The proofs are in `EthLib/Precompiles/Proofs/Blake2f.lean` and `EthLib/Cryptography/Proofs/Hash/Blake2b.lean`.

- A call fails exactly on a wrong length or a wrong flag byte, and otherwise returns F on the fields.
- Every field is decoded with its endianness, for every input.
- The output words are encoded as the input words are.
- Each IV word comes from the square root of its prime, RFC 7693 §2.6.
- Each row of the message schedule is a permutation.
- Round `i` reuses row `i mod 10` of the schedule.

## Known answers

All are checked by the kernel:

- test vectors 0 to 7 of EIP-152, through the whole precompile;
- the rounds field of test vector 8;
- RFC 7693 Appendix A, on F;
- BLAKE2b-512 of the 128 bytes `0x00` to `0x7f`, on F and through the precompile;
- test vector 5 with `t1 = 1`.

## Not proved

- No theorem relates F to another statement of RFC 7693 §3.2.
  The code transcribes §3.2 line by line instead.
- The output of test vector 8, which asks for `2^32 - 1` rounds.
  The kernel cannot evaluate that many.

# BLAKE2F precompile

BLAKE2F is the precompiled contract at address `0x09`.

It runs F, the compression function of BLAKE2b, with as many rounds as the caller asks for.

EIP-152 adds it for interoperability with Zcash, whose Equihash proof of work takes 512 BLAKE2b hashes to verify, too costly with BLAKE2b written in Solidity.

## Source

- [EIP-152](https://eips.ethereum.org/EIPS/eip-152): the input layout, the errors and the output.
- [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) §3.2: F itself, which `EthLib/Cryptography/Hash/Blake2b.lean` transcribes.

The executable source is `src/ethereum/forks/bpo2/vm/precompiled_contracts/blake2f.py` in `ethereum/execution-specs`, at commit `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.

```text
input:   [ rounds: 4 | h: 64 | m: 128 | t0: 8 | t1: 8 | f: 1 ]
output:  [ h: 64 ]
```

`rounds` is the number of rounds, big-endian.

`h` is the state, 8 words, and `m` is the message block, 16 words.

`t0` and `t1` are the low and high words of the byte offset `t`.

Every word is 64 bits, little-endian.

`f` is the final block flag: the byte `1` is true, and the byte `0` is false.

A call fails when the input is not exactly 213 bytes long, or when its flag byte is anything else.

It checks the length first, as execution-specs does.

The gas price of EIP-152, one per round, is not part of the module, and neither is a C export or a Python binding.

## Test vectors

`tests/` has no BLAKE2F vectors yet.

The proofs pin known answers instead, all checked by the kernel:

- test vectors 0 to 7 of EIP-152, run through the whole precompile;
- the rounds field of test vector 8;
- RFC 7693 Appendix A, on F;
- BLAKE2b-512 of the 128 bytes `0x00` to `0x7f`, from `testvectors/blake2-kat.json` in [BLAKE2/BLAKE2 at `ed1974e`](https://github.com/BLAKE2/BLAKE2/blob/ed1974ea83433eba7b2d95c5dcd9ac33cb847913/testvectors/blake2-kat.json), on F and through the precompile;
- test vector 5 with `t1 = 1`, answered by execution-specs.

## What is proved

The proofs are in `EthLib/Precompiles/Proofs/Blake2f.lean` and `EthLib/Cryptography/Proofs/Hash/Blake2b.lean`.

- The errors.
  A call fails when the input is not 213 bytes long (`blake2f_invalidLength`), or when it is and its flag byte is above `1` (`blake2f_invalidFlag`).
  Any other call returns `compute` of its input (`blake2f_ok`).
- The constants.
  Each word `IV[i]` is the first 64 bits of the fractional part of the square root of the `(i + 1)`-th prime, as §2.6 defines it (`IV_sqrt`).
  Each row of `SIGMA` is a permutation of the word indices 0 to 15 (`SIGMA_perm`).

## What is not proved

- That the module agrees with execution-specs on inputs other than the known answers.
  The code follows §3.2 and `blake2f.py` step by step, but no theorem relates the two.

## What the kernel cannot evaluate

Test vector 8, which asks for 4294967295 rounds.

Compiled and run outside the repository, it returns the output that EIP-152 prints.

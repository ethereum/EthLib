# VRF tree

A verifiable random function (VRF) gives one random output per input, with a proof that anyone can check.

The VRF tree is a hash-based VRF over `2^32` indices.

Its holder commits to one 32-byte secret per index, as the leaves of a Merkle tree of height 32.

The root is public.

Opening index `i` reveals secret `i` and its path to the root.

The output at `i` is a hash of that secret.

The root fixes one output per index before any is opened, so the holder cannot choose its outputs.

## Source

The specification is the section "VRF tree" of the draft [EIP-CRYPTO](https://github.com/kevaundray/EIPs/blob/fd2c9c53994eb1e7705011e0e4c53327bd61bdcc/EIPS/eip-crypto.md), "Hash-Based Validator Cryptography", at commit `fd2c9c53994eb1e7705011e0e4c53327bd61bdcc`.

The hash is Keccak-256, [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) with Keccak's original padding (`EthLib/Cryptography/Hash/Keccak.lean`).

The properties proved are the ones that define a VRF in [Micali, Rabin and Vadhan, "Verifiable Random Functions", FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584).

## Operations

- `verify` (`Verify.lean`) is `vrf.Verify` of [EIP-8450](https://eips.ethereum.org/EIPS/eip-8450): it returns the output at an index, or nothing.
- `verifyBytes` (`Serialization.lean`) is `vrf_verify` of the draft: the same over bytes, rejecting a malformed root, opening or index.
- `root` and `opening` (`Tree.lean`) build the tree and open it, from any function giving the secret of each index.

How the holder derives its secrets is not part of the specification.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Vrf/`.

- Provability.
  The opening of an honest tree at index `i` verifies, with the output of secret `i` (`verify_opening`, `Verify.lean`).
- Uniqueness.
  Two openings that verify at one index under one root give one output, or Keccak-256 collides (`verify_unique`, `Verify.lean`).
  This holds for every root, including one the holder built to cheat.
  Against an honest tree, every valid opening gives the honest output, or Keccak-256 collides (`verify_root_unique`).
- What verification checks.
  An opening verifies exactly when its path leads from its leaf to the root, and the output is the hash of its secret (`verify_eq_some_iff`).
- Domain separation (`Hash.lean`).
  The leaf, node and output inputs are 43, 75 and 45 bytes, so no input of one is an input of another.
  Each input determines its arguments, and each prefix is the ASCII string the draft names.
- Serialization (`Serialization.lean`).
  Decoding succeeds exactly on 1056-byte strings, and encoding and decoding are inverse bijections there.
  Verification over bytes rejects a root that is not 32 bytes, an opening that is not 1056 bytes, and an index outside `[0, 2^32)`.
- Known answers (`KnownAnswerZero.lean`, `KnownAnswerLast.lean`).
  One opening at index 0 and one at index `2^32 - 1` verify, with their outputs.
  Each is rejected with a wrong secret, a wrong sibling, and at another index.
  The roots and outputs were computed outside EthLib, by the draft's own `vrf_verify`.

## What is not proved

- Pseudorandomness: that an output is unpredictable until opened.
  It rests on the preimage resistance of Keccak-256, which needs a model of the hash.
- Any bound on the cost of a Keccak-256 collision.
  Uniqueness turns a second output into a collision; how hard that is depends on the hash.

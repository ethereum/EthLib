# VRF tree

A verifiable random function (VRF) gives one random output per input, with a proof that anyone can check.

The VRF tree is a hash-based VRF over `2^32` indices.

Its holder commits to one 32-byte secret per index, as the leaves of a Merkle tree of height 32.

The root is public.

Opening index `i` reveals secret `i` and its path to the root.

The output at `i` is a hash of that secret.

The root fixes one output per index before any is opened, so the holder cannot choose its outputs.

## Source

This module is the specification of the VRF tree.

[EIP-8450](https://eips.ethereum.org/EIPS/eip-8450) registers its root and names its interface, `vrf.Verify`.

The hash is Keccak-256, [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) with Keccak's original padding (`EthLib/Cryptography/Hash/Keccak.lean`).

The properties proved are the ones that define a VRF in [Micali, Rabin and Vadhan, "Verifiable Random Functions", FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584).

## Operations

- `verify` (`Verify.lean`) is `vrf.Verify` of [EIP-8450](https://eips.ethereum.org/EIPS/eip-8450): it returns the output at an index, or nothing.
- `verifyBytes` (`Serialization.lean`) is the same over bytes, rejecting a malformed root, opening or index.
- `root` and `opening` (`KeyGen.lean`) build the tree and open it, from any function giving the secret of each index.
- `keyGen`, `prove` and `evaluate` (`KeyGen.lean`) do the same from one 32-byte seed.

The Merkle tree itself (`Tree.lean`) is generic in its nodes and its node hash, and knows nothing of the VRF.

Its proofs give the tree's two guarantees, completeness and binding, which the VRF's proofs build on.

## Key generation

The holder stores one seed, sampled as 32 uniformly random bytes and kept secret.

Each leaf secret derives from it:

```text
    s_i = keccak256(PQ_VRF_SECRET | seed | LE32(i))
```

Keccak-256, keyed by the seed and separated by its prefix, acts as a pseudorandom function of the index.

So the holder stores 32 bytes instead of `2^32` secrets, and recomputes a secret or a subtree when it opens an index.

Verification never reads the seed, so the derivation is not consensus-critical.

It is specified so that every implementation rebuilds the same tree from the same seed.

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
- Key generation (`KeyGen.lean`).
  The tree of a seed verifies at every index, with the output of that index's secret (`verify_prove`).
  Every valid opening of it gives that output, or Keccak-256 collides (`verify_keyGen_unique`).
- Domain separation (`Hash.lean`, `KeyGen.lean`).
  The secret, leaf, node and output inputs are 49, 43, 75 and 45 bytes, so no input of one is an input of another.
  Each input determines its arguments.
  Each prefix is the ASCII string of its name.
- Serialization (`Serialization.lean`).
  Decoding succeeds exactly on 1056-byte strings, and encoding and decoding are inverse bijections there.
  Verification over bytes rejects a root that is not 32 bytes, an opening that is not 1056 bytes, and an index outside `[0, 2^32)`.
- Known answers (`KnownAnswerZero.lean`, `KnownAnswerLast.lean`).
  One opening at index 0 and one at index `2^32 - 1` verify, with their outputs.
  Each is rejected with a wrong secret, a wrong sibling, and at another index.
  The roots and outputs were computed outside EthLib, by an independent implementation of this specification.
  One seed's secrets and outputs at the same two indices were computed outside EthLib too (`KnownAnswerSecret.lean`).

## What is not proved

- Pseudorandomness: that an output is unpredictable until opened.
  It rests on Keccak-256 being a pseudorandom function keyed by the seed, and on its preimage resistance, which need a model of the hash.
- Any bound on the cost of a Keccak-256 collision.
  Uniqueness turns a second output into a collision.
  How hard a collision is depends on the hash.

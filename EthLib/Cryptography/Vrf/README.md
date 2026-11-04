# VRF tree

A verifiable random function (VRF) gives one random-looking output per input, together with a proof that anyone can check.
What makes it useful is that the holder of the key cannot choose the outputs: each one is fixed before it is revealed.

The VRF tree is a hash-based VRF over `2^32` indices.
Its holder commits to one 32-byte secret per index, by placing the secrets as the leaves of a Merkle tree of height 32 and publishing the root.
Opening index `i` reveals secret `i` together with its path to the root, and the output at `i` is a hash of that secret.
Since the root fixes every leaf, it fixes one output per index before any index is opened.

## Source

This module is the specification of the VRF tree.
[EIP-8450](https://eips.ethereum.org/EIPS/eip-8450) registers its root and names its interface, `vrf.Verify`.
The hash is Keccak-256, as in [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) but with Keccak's original padding (`EthLib/Cryptography/Hash/Keccak.lean`).
The properties proved are the ones that define a VRF in [Micali, Rabin and Vadhan, "Verifiable Random Functions", FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584).

## Operations

The module offers four groups of operations:

- `verify` (`Verify.lean`) is `vrf.Verify` of [EIP-8450](https://eips.ethereum.org/EIPS/eip-8450): it returns the output at an index, or nothing.
- `verifyBytes` (`Serialization.lean`) does the same over bytes, and rejects a malformed root, opening or index.
- `root` and `opening` (`KeyGen.lean`) build the tree and open it, from any function that gives the secret of each index.
- `keyGen`, `prove` and `evaluate` (`KeyGen.lean`) do the same from one 32-byte seed.

The tree is the Merkle tree of [`EthLib.Cryptography.Merkle`](../Merkle/), with the VRF's node hash at every position.
Its two guarantees, completeness and binding, are proved there, and the proofs about the VRF build on them.

## Key generation

Storing `2^32` secrets of 32 bytes each would take 128 GiB, so the holder stores a single seed instead.
The seed is 32 uniformly random bytes, kept secret, and each leaf secret is derived from it:

```text
    s_i = keccak256(PQ_VRF_SECRET | seed | LE32(i))
```

Here `PQ_VRF_SECRET` is a fixed prefix and `LE32(i)` is the index on 4 bytes, little-endian.
Keyed by the seed and separated from the other hash inputs by its prefix, Keccak-256 acts as a pseudorandom function of the index.
The holder recomputes a secret, or a whole subtree, when it opens an index.

Verification never reads the seed, so this derivation is not consensus-critical.
It is specified anyway, so that every implementation rebuilds the same tree from the same seed.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Vrf/`.
The first three properties are those of Micali, Rabin and Vadhan.

*Provability* says that an honest holder can always convince a verifier.
The opening of an honest tree at index `i` verifies, and gives the output of secret `i` (`verify_opening`, `Verify.lean`).

*Uniqueness* says that the holder cannot convince a verifier of two different outputs.
Two openings that verify at one index under one root give the same output, or `findHashCollision` returns two different inputs with one Keccak-256 hash (`verify_unique`, `Verify.lean`).
Uniqueness holds for every root, including one the holder built to cheat.
Against an honest tree, every valid opening gives the honest output, or `findHashCollision` returns a collision with the honest opening (`verify_root_unique`).

Every hash with 32-byte outputs has collisions, so the theorem names the one these two openings hash.
The search reads only the index and the two openings.
It is an efficient algorithm, so the theorem is a security reduction: whoever finds two outputs at one index also finds a Keccak-256 collision.
The search makes at most 68 Keccak-256 calls, no more than verifying the two openings.
The count is read from the definitions, and no theorem proves it.

The third statement says exactly what verification checks.
An opening verifies if and only if its path leads from its leaf to the root, and its output is the hash of its secret (`verify_eq_some_iff`).

The same guarantees hold for a tree built from a seed (`KeyGen.lean`).
That tree verifies at every index, with the output of that index's secret (`verify_prove`).
Every valid opening of it gives that output, or `findHashCollision` returns a collision with the honest opening (`verify_keyGen_unique`).

Uniqueness turns two outputs into a collision only if no two different kinds of hash input can be confused.
The proofs establish this domain separation (`Hash.lean`, `KeyGen.lean`).
The secret, leaf, node and output inputs are 49, 43, 75 and 45 bytes long, so no input of one kind is an input of another.
Each input determines its arguments, and each prefix is the ASCII string of its name.

An opening also travels as bytes (`Serialization.lean`).
Decoding succeeds exactly on strings of 1056 bytes, and on those strings encoding and decoding are inverse bijections.
Verification over bytes rejects a root that is not 32 bytes, an opening that is not 1056 bytes, and an index outside `[0, 2^32)`.

Finally, known answers pin the definitions to concrete values (`KnownAnswerZero.lean`, `KnownAnswerLast.lean`).
One opening at index 0 and one at index `2^32 - 1` verify, with their outputs.
Each is rejected with a wrong secret, with a wrong sibling, and at another index.
The roots and outputs were computed outside EthLib, by an independent implementation of this specification.
The secrets and outputs of one seed at the same two indices were computed outside EthLib too (`KnownAnswerSecret.lean`).

## What is not proved

Pseudorandomness is not proved: that an output stays unpredictable until it is opened.
It rests on Keccak-256 being a pseudorandom function keyed by the seed, and on its preimage resistance, and both need a model of the hash.

No bound on the cost of a Keccak-256 collision is proved either.
Uniqueness turns a second output into a collision, but how hard a collision is to find depends on the hash.

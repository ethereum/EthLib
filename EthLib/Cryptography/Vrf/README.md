# VRF tree

A verifiable random function (VRF) gives one random-looking output per input, together with a proof that anyone can check.
What makes it useful is that each output is fixed before it is revealed, and the holder cannot change it afterwards.

The VRF tree is a hash-based VRF over `2^32` indices.
Its holder commits to one 32-byte secret per index, by placing the secrets as the leaves of a Merkle tree of height 32 and publishing the root.
Opening index `i` reveals secret `i` together with its path to the root, and the output at `i` is a hash of the index and that secret.
Since the root fixes every leaf, it fixes one output per index before any index is opened.

```text
    output_i = keccak256(PQ_VRF_OUTPUT | LE32(i) | s_i)
```

## Source

This module is the specification of the VRF tree.
The hash is Keccak-256, as in [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) but with Keccak's original padding (`EthLib/Cryptography/Hash/Keccak.lean`).
A VRF is defined in [Micali, Rabin and Vadhan, "Verifiable Random Functions", FOCS 1999](https://doi.org/10.1109/SFFCS.1999.814584) by three properties: provability, uniqueness and pseudorandomness.
The proofs here cover the first two.

## Use in EIP-8450

[EIP-8450](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#cryptographic-helpers) registers the root of a VRF tree for each validator.
It specifies the interface `vrf.Verify(root, index, opening)`, which returns the output at the index or nothing, and leaves its calls to a later fork.
It specifies that interface and the properties it relies on, not the construction, and this module keeps the interface.
Its rationale ([Two keys per validator](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#two-keys-per-validator)) says that the root fixes one output per index at registration, before the validator knows its inputs.
That holds, but the holder chose those outputs.
So a fork that selects with them must mix them, as [The holder chooses the outputs](#the-holder-chooses-the-outputs) explains.

## Operations

The module offers five groups of operations:

- `verify` (`Verify.lean`) returns the output at an index, or nothing.
- `verifyBytes` (`Serialization.lean`) does the same over bytes, and rejects a malformed root, opening or index.
- `root` and `opening` (`KeyGen.lean`) build the tree and open it, from any function that gives the secret of each index.
- `keyGen`, `prove` and `evaluate` (`KeyGen.lean`) do the same from one 32-byte seed.
- `mixOutput` (`Hash.lean`) mixes an output with randomness, for a selection (see [The holder chooses the outputs](#the-holder-chooses-the-outputs)).

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

## The holder chooses the outputs

Verification cannot tell a tree built from a seed from a tree whose secrets the holder chose.
So a dishonest holder can pick every secret before it registers the root, and keep only secrets whose output it likes.

The output hashes the index with the secret, so one secret gives a different output at each index, unless Keccak-256 collides.
Placing one secret at all `2^32` leaves still gives a valid tree: each level has one node value, so the tree costs 33 Keccak-256 calls, and every index opens.
But each index then has its own output.
If Keccak-256 behaves as a random oracle, a secret with a good output at one index is no better than any other at another index.
Without the index, one secret found in about 256 tries would make every output start with a zero byte.

Binding the index does not stop the holder from choosing, though: it only makes the holder choose index by index.
A threshold that one output in `2^k` passes costs about `2^k` tries per index, so about `2^(32 + k)` Keccak-256 calls make every index pass.
For a threshold of one in 256, that is about `2^40` calls, well within reach.
And a holder needs only the indices that its protocol will actually use.

So the outputs are fixed once the root is registered, but the holder chose them.
A protocol that compares outputs with a threshold, as a lottery does, must not use them alone.
It must compare the mixed value instead, which hashes the output with randomness `r` that becomes known only after the root is registered:

```text
    mixed = keccak256(PQ_VRF_MIX | output_i | r)
```

The holder cannot choose secrets for an `r` that it does not know yet, so each mixed value is a fresh random value for it.
`prEvent_selected_le` (`Proofs/Vrf/Selection.lean`) proves this in the random oracle model, for a holder that chose all its secrets.

The theorem draws `r` uniformly, independently of the holder.
A protocol must provide such randomness, and that is a property of the protocol, not of this module.
If `r` was already known when the root was registered, the holder can grind its secrets against it.
For example, randomness taken from the finalized checkpoint does not change while the chain does not finalize, so a holder could grind against it until it changes.
A protocol should therefore mix in randomness that is new for each duty.
That randomness must also be beyond the holder's influence.
Randomness that its last contributor can bias, for example by withholding its contribution, is outside the theorem.

The mix does not read the holder's identity either.
Two validators that register the same root have the same outputs and the same mixed values, so a fork must handle copied roots, as EIP-8450's security considerations ask.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Vrf/`.
Two of the three properties of Micali, Rabin and Vadhan are proved: provability and uniqueness.
The third, pseudorandomness, is not proved (see [What is not proved](#what-is-not-proved)).
A weaker property, unpredictability, is proved in the random oracle model.

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

A third statement, which is not one of those properties, says exactly what verification checks.
An opening verifies if and only if its path leads from its leaf to the root, and its output is the hash of its index and its secret (`verify_eq_some_iff`).

The output binds its index (`Verify.lean`).
Two outputs are equal only for one index and one secret, or their two output inputs, which differ, are a Keccak-256 collision (`outputHash_binding`).
So two openings that verify at two different indices, under any roots and even with one secret, give two different outputs, or their output inputs collide (`verify_index_binding`).

The same guarantees hold for a tree built from a seed (`KeyGen.lean`).
That tree verifies at every index, with the output of that index's secret (`verify_prove`).
Every valid opening of it gives that output, or `findHashCollision` returns a collision with the honest opening (`verify_keyGen_unique`).

Uniqueness turns two outputs into a collision only if no two different kinds of hash input can be confused.
The proofs establish this domain separation (`Hash.lean`, `KeyGen.lean`).
The leaf, node, output and mix inputs are 43, 75, 49 and 74 bytes long, so no input of one of these kinds is an input of another.
The secret inputs of key generation are 49 bytes too, like the output inputs, but they start with `PQ_VRF_SECRET` where an output input starts with `PQ_VRF_OUTPUT`.
So no input of one kind is an input of another.
Each input determines its arguments, and each prefix is the ASCII string of its name.

An opening also travels as bytes (`Serialization.lean`).
Decoding succeeds exactly on strings of 1056 bytes, and on those strings encoding and decoding are inverse bijections.
Verification over bytes rejects a root that is not 32 bytes, an opening that is not 1056 bytes, and an index outside `[0, 2^32)`.

*Unpredictability* says that no one without a secret can guess its output before it is opened.
Three theorems prove it, in three games.
The first theorem (`Unpredictability.lean`) takes the challenge secret uniform, not derived from a seed.
It is the residual unpredictability of Micali, Rabin and Vadhan, §3.2, in their definition of a verifiable unpredictable function.
The hash is a random oracle, the secret at the challenge index is uniform, and the other secrets are any fixed values.
The adversary gets the root, queries the hash `q_H` times, and asks for `q_O` openings at other indices.
Its guess of the output at the challenge index is right with probability at most `(1 + 2 Q) / 2^256`, where `Q = q_H + (q_O + 1) 2^33` (`prEvent_guess_le`).
With `q_H = 2^64` and `q_O = 2^32`, that is below `2^-189`.
The game computes the root and the openings with the tree of this module, with the hash as an oracle (`rootWith_hash`, `openingWith_hash`).

That theorem fixes the challenge index before the game, where Micali, Rabin and Vadhan let the adversary choose it.
A second theorem lets the adversary choose it (`prEvent_adaptiveGame_le`, `AdaptiveIndex.lean`).
There all `2^32` secrets are uniform, and the adversary may ask for the opening at any index.
It wins if it names an index whose opening it never asked for, and guesses the output there.
The proof splits a win by the index named, so its bound is `2^32` times the first: `2^32 (1 + 2 Q) / 2^256`.
With `q_H = 2^64` and `q_O = 2^32`, that is below `2^-157`.

A third theorem covers the secrets of key generation, derived from a uniform seed (`prEvent_seedGame_le`, `SeedSecrets.lean`).
Its game is the second one, with each secret the hash of its secret input under the seed.
The secrets act as independent uniform values until a hash query hits a secret input of the seed.
Such an input fixes the seed, so each hash query hits with probability at most `2^-256`.
The bound gains one term for it: `2^32 (1 + 2 Q) / 2^256 + Q / 2^256`.
With `q_H = 2^64` and `q_O = 2^32`, that is still below `2^-157`.
The game computes the root and the openings of the tree of a seed, with the hash as an oracle (`rootOf_secret`, `openingOf_secret`).

None of these theorems covers a holder who chooses its own secrets: such a holder can bias its outputs.

*A mixed selection* is what covers such a holder (`prEvent_selected_le`, `Selection.lean`).
The game is EthLib's own, and no paper defines it.
There the mix is a random oracle, and the tree hash is Keccak-256 itself.
With the mix of the specification in place of the oracle, the event is exactly the protocol's check (`selected_iff_mixOutput`).
The holder chooses every secret of its tree, and queries the mix at most `q` times before the randomness `r` is drawn.
Then `r` is uniform, and the holder opens any index of a set `I` fixed in advance, with any opening.
It is selected when the opening verifies and the mixed value of its output is in a target set `S`.
That happens with probability at most `|I| |S| / 2^256 + q / 2^256`, plus the chance that `findHashCollision` returns a collision with the honest opening at that index.
The first term is one fresh uniform value per allowed index, and the second is a mix query that already used `r`.
With one index, `|S| = 2^200` (a selection of one in `2^56`) and `q = 2^64`, the first two terms are below `2^-55`.
The theorem does not cover a holder that registers a root without knowing a tree under it.
Nor does it cover randomness that the holder knows at registration or can bias.

## Test vectors

`tests/cryptography/vrf/` has cases for `verify`, `secret`, `evaluate` and `mix`, which the Python suite checks through the bindings.
One opening at index 0 and one at index `2^32 - 1` verify, with their outputs.
Each is rejected with a wrong secret, with a wrong sibling, and at another index.
The roots and outputs were computed outside EthLib, by an independent implementation of this specification.
The secrets and outputs of one seed at the same two indices, and the mixed value of the output at index 0, were computed outside EthLib too.

## What is not proved

Pseudorandomness is not proved: that an output is indistinguishable from random until it is opened.
It rests on Keccak-256 being a pseudorandom function keyed by the seed, and on its preimage resistance, and both need a model of the hash.
It could hold only for a tree whose secrets the holder did not choose.

No bound on the cost of a Keccak-256 collision is proved either.
Uniqueness turns a second output into a collision, but how hard a collision is to find depends on the hash.
The generic cost of `2^128` hashes for a collision holds against a classical adversary.
A quantum search for collisions needs about `2^85` queries.

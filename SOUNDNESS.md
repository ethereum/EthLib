# Soundness

This document says what the proofs of EthLib establish, and what a user of EthLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem, and both are assumed to match something outside Lean: the source document the definition implements, the code that actually runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of s2n-bignum's [`SOUNDNESS.md`](https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md), adapted to a specification library.

This document describes the development tree that declares package version `0.3.0` in `pyproject.toml`.
It does not describe the tags `v0.1.0` and `v0.2.0`, which point to earlier commits.

The prose was reviewed by hand for that package version.
CI fails when `pyproject.toml` declares another version, so each version bump forces a new review of the document and an update of the line above.
The facts that change with the code, such as which theorems still use `native_decide`, are instead generated from the repository by `scripts/soundness_facts.py`.
CI fails when one of them is out of date, so they hold for every commit, not only for one version.

## Ways to use EthLib

Each way of using EthLib trusts a different set of things, so the summary table marks which risks apply to which use.
There are four uses:

- **P**, a Lean proof that imports the specification;
- **R**, a Lean program that runs the specification;
- **B**, a client that calls the Python bindings;
- **V**, a client that tests against the vectors in `tests/`.

## Summary

The risks fall into four gaps, one per link in the chain from source to client.
Gap A asks whether the definition says what the source and the client need.
Gap B asks whether the code that runs matches the definitions.
Gap C asks whether the proof itself is sound.
Gap D asks whether the use of EthLib holds together.

| ID | Risk | Mitigation in place | Applies to |
|----|------|---------------------|------------|
| A1 | A definition does not match its source | Definitions named and shaped after the source; vectors pinned to consensus-specs `v1.7.0-beta.4` and other upstream sources; consistency theorems on the constants | P R B V |
| A2 | A theorem holds only under a hypothesis | Each conditional theorem below lists its hypotheses | P |
| A3 | Timing reveals secret data | None: no constant-time claim | R B |
| A4 | A security theorem idealises a primitive | Each idealisation is listed in A4 | P |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | CI regenerates the vectors on every change, and the slow cases every week, then compares them with the committed ones | R B |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R B |
| B3 | Elaboration runs native code | None | P |
| B4 | The hand-written C boundary is wrong | The regeneration and comparison of B1 | B |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R B |
| B6 | The build or the published wheel differs from the source | Fresh build per wheel in CI, with a pinned elan. Each wheel runs the vector suites, and carries a build provenance attestation | B |
| C1 | The Lean kernel or its axioms are unsound | None: `lake exe check-decls` checks which axioms a theorem uses, not that the kernel or the axioms are sound | P |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any new use; the remaining ones are listed in C2 | P |
| C3 | A declaration reached the environment unchecked | leanchecker replays every declaration into the kernel every week, and on pushes to `master` | P |
| D1 | A client misuses an operation | Docstrings in Lean | R B |
| D2 | A dependency changes | Pinned in `lake-manifest.json` | P R B |
| D3 | The KZG trusted setup is not what it should be | Bytes match the consensus-specs setup | P R B V |
| D4 | The vectors are wrong | They match their pinned upstream sources, and CI checks their pinned digests | V |

The sections after the next one explain each row.

## What the proofs say

Before the risks, here is what is actually proved, primitive by primitive.
The list covers the main theorems and is not yet complete.

Most of these theorems are about correctness: an honest run gives the expected answer, or malformed input is rejected.

Some of them state a security property.
The unforgeability of leanXMSS holds for EthLib's own definitions.
The binding of an EIP-8450 proof of possession follows from it.
The unforgeability of leanSPHINCS holds for EthLib's own definitions too.
The unforgeability of BLS signatures holds for a scheme that EthLib's signing and verification compute.
The accountable safety and the plausible liveness of Casper FFG hold for an abstract model of votes.
The evaluation binding of single KZG proofs reduces to the strong Diffie–Hellman problem.
The binding of the batch check of KZG openings reduces to the same problem, or to a challenge that is a root of a nonzero polynomial.
The binding of the batch check of KZG cells reduces to the bilinear variant of that problem, or to such a root.
That reduction holds in a model of the target group of the pairing.

The binding of the batch check of blobs reduces to a challenge that is a root of a nonzero polynomial, or to recovery of the setup secret.
That reduction holds for algebraic adversaries, with the challenge hash modelled as a random oracle.
No theorem covers the code that runs, the C boundary, or timing.

### XMSS

The correctness theorem is `verify_keyGen_sign` (`Proofs/Xmss/Correctness.lean`).
If `keyGen seed` returns a key pair, and `sign` returns a signature for a message at a leaf index, then `verify` accepts that signature under that public key.
It says nothing about unforgeability.

In the random oracle model, signing fails with probability at most `2 exp(-4000)` (`prEvent_signWith_error_le`, `Proofs/Xmss/SignatureFailure.lean`).
The theorem assumes that the oracle's cache holds no trial input of the two keys that sign when signing starts, as an empty cache does.
It proves that the signer's own calls before each search add none.
The bound covers one signature from such a cache.
An earlier signature under the same key caches the trial inputs of its keys, and in the unforgeability game the adversary's queries can too.
So no theorem bounds the failure of a later signature, or of signing inside the game.

Unforgeability is `Unforgeability.unforgeable` (`Proofs/Xmss/Unforgeability.lean`).
In the random oracle model, an adversary whose experiment makes at most `q >= 1` hash calls forges a signature with probability at most `q / 2^127`.
Its game runs EthLib's `keyGenWith`, `signWith` and `verifyWith`, with the hash `H` a query to the random oracle.
`keyGen`, `sign` and `verify` are the same definitions with Keccak-256 as `H`.

The proof is adapted from leanerVM's, and `Proofs/Xmss/Security/README.md` lists what changed here.
It reasons over EthLib's algorithms.
Its model of the scheme with precomputed keys is a step of the proof, not a second statement.

The game follows the note's section "Security".
The adversary gets the public key, queries `H`, and requests signatures, never at the same leaf index twice.
It wins when its forgery verifies and no request for the forged message returned the forged signature.

The budget `q` counts every hash call of the game, including those of key generation, signing and the final verification.
It bounds every run, including the unlucky ones, so the bound is weaker than `2^-127` per adversary call:

- Key generation alone makes `K = 13,434,881` calls, about `2^23.7`, so the bound is never below about `2^-103.3`.
- A signing request can try up to `2^32` randomizers on each layer before one gives a codeword.
  So each signing request adds more than `2^33` to `q`, and an adversary with `n >= 1` requests gets a bound above `n * 2^-94`.
- An adversary that requests a signature at each of the `2^32` leaf indices has `q > 2^65`.
  So over the key's lifetime, the bound is above `2^-62`, about 62 bits, not 127.

The bound is classical: the adversary queries the oracle as a classical algorithm.
The statement is written with VCVio's oracle computations and probabilities, so their definitions are part of what it says.

### EIP-8450 proof of possession

A proof of possession is a leanXMSS signature, at leaf index 0, of a root that names a BLS key and the leanXMSS key.
Completeness is `isValidPqPossessionProof_sign` (`Consensus/Proofs/PqKeys/Possession.lean`): a key generated from a seed that signs its possession root at leaf 0 gives a proof that the check accepts.
`isValidPqPossessionProofWith_of_index_ne` shows that a proof at any other leaf index fails.

Binding is `possession_binding` (`Consensus/Proofs/PqKeys/PossessionBinding.lean`).
Its game is the leanXMSS game, except that the adversary returns a BLS key and a proof.
It wins when the check accepts the proof for that BLS key and the honest leanXMSS key.
And no signing request for their possession root returned that proof.
Such an adversary turns into a leanXMSS adversary with the same hash calls that wins whenever it wins, so the bound is again `q / 2^127`.
The game checks a proof as the specification does, and `possessionVerdict_eq` shows that the two verdicts agree for every hash.

The theorem says nothing about two BLS keys whose possession roots collide under SHA-256.
A proof that the key holder made for one of them is then valid for the other.
The game does not count that as a win.

### Merkle trees

leanXMSS, leanSPHINCS, the VRF tree and SSZ build their trees on one definition.
Two theorems in `Proofs/Merkle/Binding.lean` describe what a path binds, for every node hash.
The first is `climb_binding`, about two climbs from one position that reach one node.
They are equal, or `findCollision` returns a collision of the node hash at an ancestor of that position.
The second is `climb_binding_node`, about a climb that reaches an honest node but is not the honest climb.
Then `findSecondPreimage` returns a second preimage of an honest ancestor.

Both searches are explicit algorithms, proved to return valid answers.
Each can return nothing: on one climb compared with itself (`findCollision_self`), and on the honest climb (`findSecondPreimage_honest`).
So the statements say something, even though every compressing hash has collisions.

`Proofs/Merkle/RandomOracle.lean` bounds classical searches against an ideal random oracle with `N` outputs and an empty initial cache.
`prEvent_collision_le` bounds a collision among queried inputs by `q^2 / N` for at most `q` hash calls, and private uniform sampling is not counted.
This bound exceeds the standard birthday bound `q(q - 1) / (2N)` by the factor `2q / (q - 1)`: at most 4 for `q >= 2`, and close to 2 for large `q`.

`prEvent_secondPreimage_le` bounds by `q / N` a hit on a target digest fixed before the run, among queried inputs other than one honest input.
The theorem does not tie the target to the digest of the honest input.
Reading it as a second-preimage bound conditions on the honest digest and assumes that the other oracle answers stay independent and uniform.
That conditioning is a modelling step, not a proved one.

The Merkle applications model the tuple `(level, position, left, right)` as the oracle input.
They require an injective encoding of that tuple, for levels and positions inside the encodable range, not a hash that ignores the position.
The bounds run `findCollision` and `findSecondPreimage` themselves, with an oracle query as the node hash.
For paths and leaves fixed before the oracle is sampled, `prEvent_findCollision_queryNode_le` bounds the first search by `(2h)^2 / N`, where `h` is the shorter path length.
For the same fixed inputs, `prEvent_findSecondPreimage_queryNode_le` bounds the second by `Q^2 / N`, with `Q = secondPreimageQueries level path.length`.
Its budget counts every hash call, including repeated honest-node computations:

```text
Q(l, 0) = 0
Q(l, n+1) = 1 + 2*(2^l - 1) + (2^(l+1) - 1) + Q(l+1, n)
```

For a path of length `n` from level `l`, `Q` equals `2^(l+n+2) - 2^(l+2) - 2n`, while the search queries at most `2^(l+n) - 1 + n` distinct inputs.
The honest ancestors depend on oracle answers, so this search uses the birthday bound, not the bound for one fixed target.
The covered-event theorems also allow adaptive surrounding clients, provided their total budget includes the witness queries and honest-tree construction.
These statements do not bound attacks on a concrete hash or quantum queries.

The VRF's `verify_unique`, SSZ's `verifyMerkleProof_binding` and the leanXMSS unforgeability proof use `climb_binding`.
leanXMSS also states `fold_binding` with `climb_binding_node`, which its unforgeability proof does not use.

### SSZ

Four kinds of SSZ theorem say what a root binds, and each one reduces a conflict to a SHA-256 collision.
Each collision is two different 64-byte inputs with one digest, returned by an explicit search.

Branch binding is `verifyMerkleProof_binding` (`Proofs/Ssz/Merkle/Authentication.lean`).
Two accepted branches at one index and root open one leaf, or `findBranchCollision` returns a collision.
It rests on `climb_binding`, above.

Multiproof binding is `verifyMerkleMultiproof_binding` and `verifyMerkleMultiproof_overlap_binding` (`Proofs/Ssz/Merkle/MultiproofBinding.lean`).
Two accepted requests for one root agree on every position they both claim, or `findMessageCollision` returns a collision.
That search tries each input one verifier hashes against each input the other hashes.

Whole-value binding is `hashTreeRoot_binding` (`Proofs/Ssz/Codec/Binding.lean`).
Two values of one type with one root are equal, or `findMessageCollision` returns a collision between the hash inputs of the two root computations.
It has three hypotheses on each value.
The type is well formed, the value fits the type, and the value is `CommitmentSized`: every variable-size count in it is below `2^256`.
A larger count would be truncated in the 256-bit word mixed into the root, and the proof needs the exact count.
`hashTreeRootM_binding` states the same, with the same hypotheses, for any hash with 32-byte digests.
It computes the roots of the all-zero subtrees with that hash too.

Layout separation is `hashTreeRoot_progressiveContainer_layouts_separate` (`Proofs/Ssz/Codec/LayoutSeparation.lean`).
Two legal progressive containers with one root have one layout, or `findMixinCollision` returns the inputs of the two last hashes.

No theorem bounds the probability of finding a collision in a branch, a multiproof or a layout.

`Proofs/Ssz/RandomOracle.lean` bounds whole-value binding, with the node hash a random oracle.
The merkleization takes its hash in any monad, so the experiment runs the root of the specification with a hasher that queries the oracle.
That hasher also computes the roots of the all-zero subtrees with the oracle, one query per level.
The type is fixed before the run, and an adversary outputs two values of it.
The experiment computes both roots, then hashes every node of both expanded computations again with the oracle.
The adversary wins when the two values differ, fit the well-formed type, are `CommitmentSized`, and have one root.
`collision_of_extract` shows that every win leaves two different cached inputs with one answer.
Its proof finds them with `findMessageCollision`, run with a table that agrees with the cache.
`prEvent_wins_le` then bounds a win by `Q^2 / N` through `prEvent_collision_le`, and `prEvent_wins_le_two_pow` states it with `N = 2^256`.
`Q` counts every oracle call of the experiment, repeats included.
The extraction makes many: the expanded computations hash every node of the padded tree of each value, one query each.
So `Q` grows with the capacity of the type, not with the length of the values.
A list with a capacity of `2^38` nodes costs about `2^38` queries for each value, so about `2^39` for the two.
For an Electra beacon state the padded trees hold about `2^40.6` nodes for each value, so `Q` is at least about `2^41.6`, and with `Q = 2^42` the bound is `2^-172`.
A rehash that shares the all-zero subtrees would bring `Q` down to the size of the values, and is left for later.
`prEvent_secondValue_le_two_pow` fixes the first value as an honest one: its root is computed in the experiment, with the same oracle.
That is still the birthday bound, not a sharper fixed-target bound.
The bound needs no hypothesis that the cache covers the witnesses, since the experiment queries them itself.
One oracle answers inner nodes and mixed-in words alike, so a collision between any two inputs counts.

### leanSPHINCS

The correctness theorem is `verify_keyGen_sign` (`Proofs/Sphincs/Correctness.lean`).
If `keyGen seed` returns a key pair, and `sign` returns a signature for a message, then `verify` accepts that signature under that public key.

The Python suite checks one signature that an independent implementation computed, with its public key, through the bindings.

In the random oracle model, all `2^32` counters of one search miss the code with probability below `exp(-2^18)` (`prEvent_findCounter_none_le`, `Proofs/Sphincs/CodewordSearch.lean`).
The theorem assumes that the oracle's cache holds none of the counters' inputs when the search starts.

In the random oracle model, signing fails with probability at most `3 exp(-2^18)` (`prEvent_signWith_error_le`, `Proofs/Sphincs/SignatureFailure.lean`).
The theorem assumes that the oracle's cache holds no trial input of any key when signing starts, as an empty cache does.
It proves that the signer's own calls before each search add none of that layer's trial inputs.
The bound covers one signature from such a cache.
An earlier signature under the same key caches the trial inputs of its keys, and in the unforgeability game the adversary's queries can too.
So no theorem bounds the failure of a later signature, or of signing inside the game.

Unforgeability is `Unforgeability.Bridge.unforgeable` (`Proofs/Sphincs/Unforgeability.lean`).
Take an adversary whose experiment makes at most `q >= 1` hash calls and at most `2^30` signing requests.
In the random oracle model, it forges a signature with probability at most `q / 2^127`.
Its game runs EthLib's `keyGenWith`, `signWith` and `verifyWith`, with the hash `H` a query to the random oracle.
`keyGen`, `sign` and `verify` are the same definitions with Keccak-256 as `H`.

The proof is a port of leanVM's model of the scheme, and `Proofs/Sphincs/Security/README.md` lists what changed here.
The model comes from the commit that merged [leanVM#662](https://github.com/leanEthereum/leanVM/pull/662), which moves the scheme to the hash layout of FIPS 205.
The model signs the layers of the hypertree from the bottom up, as EthLib does.
The bridge in `Proofs/Sphincs/Unforgeability/Bridge/` connects the model to EthLib's algorithms.
An EthLib forgery is a model forgery of a translated adversary (`forgeAdvantage_le`).
Under every fixed answer of the oracle, a signing request costs the model at most what it costs EthLib (`hashCalls_sign_le`).
So the adversary's budget of `q` hash calls carries over unchanged, and the model's theorem `h26_layered` gives the bound.

### VRF tree

A VRF tree commits to secret outputs under one root, and later opens them one index at a time.
Two theorems in `Proofs/Vrf/Verify.lean` describe it.
`verify_unique` says that two openings that verify at one index under one root give one output, or `findHashCollision` returns a collision of Keccak-256.
That search reads only the index and the two openings.
The theorem holds for every root, including one built to cheat.
`verify_opening` says that the opening of an honest tree verifies, with the output of its secret.

Uniqueness is reduced to a collision, and no theorem bounds the cost of finding one.
In the random oracle model, `prEvent_guess_le` (`Proofs/Vrf/Unpredictability.lean`) bounds the chance of guessing an unopened output.
The secret at the guessed index is uniform, and the adversary sees the root, the hash and the openings at other indices.
It guesses right with probability at most `(1 + 2 Q) / 2^256`, where `Q = q_H + (q_O + 1) 2^33` counts its hash queries and requests.
The theorem fixes the index in advance, and does not cover a secret derived from a seed.
`prEvent_adaptiveGame_le` (`Proofs/Vrf/AdaptiveIndex.lean`) lets the adversary choose the index, with all secrets uniform.
Its bound is `2^32 (1 + 2 Q) / 2^256`, because the proof splits a win by the index named.
`prEvent_seedGame_le` (`Proofs/Vrf/SeedSecrets.lean`) does the same for secrets derived from a uniform seed, as key generation derives them.
One hidden-seed step adds `Q / 2^256` to its bound.
Verification accepts any tree, so a holder that chooses its secrets can bias every output.

The output hashes its index with its secret: `keccak256(PQ_VRF_OUTPUT | LE32(i) | s)`.
`outputHash_binding` (`Proofs/Vrf/Verify.lean`) says that two equal outputs come from one index and one secret, or their two output inputs, which differ, are a Keccak-256 collision.
`verify_index_binding` applies it to two openings that verify at two different indices, under any roots.
So one secret gives different outputs at different indices, unless Keccak-256 collides.
That two such outputs behave as independent values is a random-oracle heuristic, which no theorem states.
A holder can still grind index by index, at about `2^k` hashes per index for a threshold of one in `2^k`.

A selection therefore compares `mixOutput`, the hash of the output with randomness revealed after the root is registered.
`prEvent_selected_le` (`Proofs/Vrf/Selection.lean`) covers a holder that chooses every secret of its tree.
The mix is a random oracle, and the tree hash is Keccak-256 itself.
The holder makes at most `q` mix queries before the randomness is drawn, then opens any index of a set `I` fixed in advance.
The mixed value of its output lands in a target set `S` with probability at most `|I| |S| / 2^256 + q / 2^256`, plus the chance that `findHashCollision` returns a collision with the honest opening at that index.
No theorem bounds that last chance, as for uniqueness.
The theorem says nothing about a holder that registers a root without knowing a tree under it.
That case would need the tree hash as a random oracle too, and an extractor of the tree from the queries.
It says nothing either about randomness that the holder knows at registration, or can bias: the game draws it uniformly and independently of the holder.
The game is EthLib's own.
`selected_iff_mixOutput` shows that, with `mixOutput` in place of the oracle, its event is exactly the protocol's check.

[EIP-8450](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#cryptographic-helpers) specifies the interface `vrf.Verify` and the property of unique outputs, not the construction.
The index in the output keeps that interface, and changes every output of the construction that EthLib specified before.
The EIP's rationale ([Two keys per validator](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-8450.md#two-keys-per-validator)) says that the root fixes one output per index before the validator knows its inputs.
That does not stop a holder from choosing its outputs, so the fork that uses the root must select with the mix.

### BLS12-381

The BLS theorems check the constants, because a wrong digit in a modulus or in the generator would very likely make one of them fail.
`modulus_prime` (`Proofs/Bls/FpZMod.lean` and `Proofs/Bls/FrZMod.lean`) proves that both moduli are prime.
`seven_pow_card_sub_one` and `seven_pow_div_prime_ne_one` (`Proofs/Bls/FrZMod.lean`) prove that `7` generates the multiplicative group of the scalar field; `7` is also the KZG constant `PRIMITIVE_ROOT_OF_UNITY`.
`addOrderOf_toPoint_generator` (`Proofs/Bls/G1Order.lean`) proves that the G1 generator has order `r`.

`pairingBilinear` (`Proofs/Bls/PairingAte.lean`) proves that the pairing is bilinear on the multiples of the generators: `e(a g_1, b g_2) = e(g_1, g_2)^(a b)` for all `a` and `b` in `Fr`.
`orderOf_pairing_generators` (`Proofs/Bls/Nondegenerate.lean`) proves that the pairing of the two generators has order `r`, so it is not 1; the kernel evaluates that pairing.
`PairingLaws.of_bilinear` (`Proofs/Bls/PairingBilinear.lean`) derives `PairingLaws` from one smaller hypothesis, `PairingBilinear`: `e(a g_1, b g_2) = e(g_1, g_2)^(a b)` for all `a` and `b` in `Fr`.
`pairingBilinear` proves `PairingBilinear`.
`PairingLaws` (`Proofs/Bls/PairingLaws.lean`) states the consequence that verification needs, as one structure.
`pairingLaws` (`Proofs/Bls/PairingAte.lean`) proves `PairingLaws`.
Let `P_i` represent `a_i * g_1` and `Q_i` represent `b_i * g_2`, where a representative is any valid point with that group element.
Then the check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i * b_i = 0` in `Fr`.
The law holds when the check tests `prod_i e(P_i, Q_i) = 1` for any bilinear map `e` with `e(g_1, g_2) != 1` into a group of order `r`.
`pairingCheck_congr` (`Proofs/Bls/PairingCongr.lean`) proves that the check depends only on the group elements of valid points, so the law can quantify over representatives.
`TargetGroup.ofPairingLaws` (`Proofs/Bls/TargetGroup.lean`) builds a model of the target group from the proved law.
Its target is `Fp12` and its generator is `e(g_1, g_2)`.
In this model, `pairing P Q = e(g_1, g_2)^(a b)` when `P` represents `a * g_1` and `Q` represents `b * g_2`.
An element of the model represents `t` in `Fr` when it is `e(g_1, g_2)^t`.
The BLS signature, consensus, KZG, PeerDAS and EIP-2537 theorems use `pairingLaws` inside their proofs.
Only the lemmas of `Proofs/Bls/PairingLaws.lean`, which derive consequences of the law, take `PairingLaws` as a hypothesis.

`finalExponentiation_eq_pow` (`Proofs/Bls/FinalExponentiation.lean`) proves that the final exponentiation raises every element of `Fp12` to exactly `(p^12 - 1) / r`.
`millerDouble_snd` and `millerAdd_snd` (`Proofs/Bls/MillerLoop.lean`) prove that each step of the Miller loop multiplies by the line through the untwisted points, times `c w^3` for some `c` in `Fp2`.
The doubling step needs `T` finite with `Y ≠ 0`, and the addition step needs `T` finite with an `x` other than that of `Q`.
`finalExponentiation_fp2_mul_w_cube` proves that the final exponentiation sends `c w^3` to 1 when `c ≠ 0`.
`pairing_eq_finalExponentiation_loop` (`Proofs/Bls/MillerChain.lean`) chains these steps over the whole loop.
Take a valid `Q` of order dividing `r`, and a finite `P`.
Then the pairing is the final exponentiation of the conjugate of Miller's algorithm, run on `|x|` and the untwist of `Q`, at `P`.
Miller's algorithm (`Proofs/MillerFunction.lean`) multiplies the values at `P` of the functions `g_{T,S}` of Miller (J. Cryptology 17, 2004, Section 4.1, Definition 5).
`spanSingleton_lineRatioElem` (`Proofs/MillerDivisor.lean`) proves the fractional ideal of each `g_{T,S}`: the ideal of `T` times that of `S`, over that of `T + S`.
`loop_eq_linesValue` (`Proofs/MillerLines.lean`) proves that the loop computes a product of lines over a product of verticals, at every point.
`linesDivisor_lines` proves that the divisors assigned to these factors add up to `s (Q) - (s Q) - (s - 1) (O)`, the divisor of Miller's function `f_{s,Q}` (Lemma 2, equation (7)).
Only the affine part of each divisor is proved, through fractional ideals; no theorem checks the multiplicity at `O`.
`spanSingleton_millerElem` proves that the function has the fractional ideal of `Q` to the power `s`, over that of `s Q`.
`linesElem_mul_eq_of_linesDivisor` (`Proofs/MillerUnique.lean`) proves that two quotients of products of lines with the same divisor are equal, with no constant left.
The units of the coordinate ring are the nonzero constants, and every line has the leading coefficient 1 at `O` for the uniformizer `-x / y`.
`weil_reciprocity` (`Proofs/MillerReciprocity.lean`) proves Weil reciprocity for two quotients of products of lines whose lines share no finite point: `f(div g) = ε g(div f)`.
The sign `ε` is -1 to the product of the multiplicities of `O` in the divisors assigned to the lines.
Each function is taken as 1 at `O`.
`pow_ratioAt_add_left` and `pow_ratioAt_add_right` (`Proofs/MillerAte.lean`) prove the linearity of an ate-type pairing, on any curve and field.
The pairing evaluates a quotient of products of lines at `P`, then raises the value to a power `N`.
Let `pi` be the map `(x, y) -> (x^q, y^q)`, and let the quotient for `Q` have the divisor `sum_j c_j ((pi^j Q) - (O))`.
Let `z^(N n)` be 1 for every nonzero `z`, with `n = sum_j c_j q^j`.
Then the pairing is linear in a point `P` fixed by `pi`, when `N` is even, and linear in `Q`.
`Q` lies in a group that `pi` maps into itself, and where `pi` fixes only `O`.
`frobenius_of_mem` (`Proofs/Bls/AteFrobenius.lean`) applies these results to BLS12-381, where `pi` acts as the BLS parameter `x = -|x|` on the untwist of `G2`.
`eq_zero_of_frobenius_eq` proves that `pi` fixes only `O` there, because `r` does not divide `|x| + 1`.
`frobenius_iterate_seven` proves that `pi^7` acts as `|x|` there, because `r` divides `|x|^7 + |x|`.
`ratioDivisor_lines` proves that Miller's function of `|x|` and a point `Q` of the untwist of `G2` has the divisor `|x| ((Q) - (O)) - ((pi^7 Q) - (O))`.
`pow_ateExponent` proves that `z^(N (|x| - p^7))` is 1 for every nonzero `z` in `Fp12`, with `N = (p^12 - 1) / r`.
`ateValue_add_left` (`Proofs/Bls/PairingAte.lean`) proves that Miller's function of `|x|` and `Q`, at `P` and raised to `N`, is linear in a point `P` that `pi` fixes.
`ateValue_add_right` proves that it is linear in `Q` on the untwist of `G2`.
`pairing_eq_ateValue` proves that the pairing of a valid finite point `P` of `G1` and a valid point `Q` of the subgroup of `G2` is that value raised to `p^6`.
The alt_bn128 section lists the same application to alt_bn128.

The pairing of the two generators equals the value that [draft-irtf-cfrg-pairing-friendly-curves-11](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11) publishes in Appendix B.
The Python suite checks it through the bindings (`bindings/python/tests/bls/test_pairing.py`), with a few bilinearity checks.
This evidence tests the compiled code against the published value.

`keyValidatePoint_eq_ok_iff` (`Proofs/Bls/KeyValidate.lean`) proves that key validation accepts exactly the encodings of the nonzero points of order `r` in G1.
The G1 and G2 subgroup checks accept exactly the valid points that represent a multiple of the generator.
Every output of the maps to G1 and G2 is a valid point of that subgroup (`Proofs/Bls/MapToCurve.lean`).
`hashToG2_total_inSubgroup` (`Proofs/Bls/CofactorSubgroupLanding.lean`) proves that the hash to G2 succeeds on every input and returns a valid point of that subgroup.
`toPoint_clearCofactor_eq_hEff` (`Proofs/Bls/CofactorEffective.lean`) proves that the cofactor clearing of RFC 9380 Appendix G.3 is the multiplication by the `h_eff` of §8.8.2, on every valid point of the twist.
`hashToG2_eq_hEff_smul` proves that each output of the hash to G2 is `h_eff` times a valid point of the twist.
`expandMessageXmd_eq_spec` (`Proofs/Bls/ExpandMessage.lean`) proves that the message expansion is `expand_message_xmd` of RFC 9380 §5.3.1 with the FIPS 180-4 model of SHA-256.
It covers the shortened DST of §5.3.3.
It assumes a message shorter than 2^61 - 323 bytes and a DST shorter than 2^61 - 17 bytes.
`hashToFieldFp2_eq_spec` proves that the hash to `Fp2` is `hash_to_field` of §5.2 under the same bounds, with each coordinate read in `ZMod p`.
No theorem yet compares the SSWU map or the isogeny with a model of RFC 9380.

`sign_ok` and `popProve_ok` (`Proofs/Bls/Signatures.lean`) prove that BLS signing never fails.
An honest signature, an honest proof of possession and an aggregate of honest signatures verify (`verify_sign`, `popVerify_popProve`, `aggregateVerify_aggregate`, `Proofs/Bls/SignaturesCorrect.lean`).
For the fast aggregate verification on one message, `fastAggregateVerify_aggregate` also assumes that the secret keys do not sum to zero modulo `r`.
Otherwise the aggregate key is the point at infinity, and key validation rejects it.

A key and a message have at most one signature that verifies, byte for byte (`verify_unique`, `Proofs/Bls/SignaturesUnique.lean`).
From a victim's key alone, an attacker builds a second key and a signature that passes the fast aggregate verification for both (`fastAggregateVerify_rogue`).
So each key of that verification needs a verified proof of possession.

`forgeAdvantage_le` (`Proofs/Bls/Security/Reduction.lean`) states unforgeability in the random oracle model.
It follows Theorem 3.2 of [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), with the simple guessing reduction.
The scheme lives over two abstract groups, with keys `a • g1`, hashes in `G2` and signatures `a • H(m)`.
Its verification is a test of co-Diffie-Hellman tuples, and the theorem assumes that the test is sound.

Let every run of the game make at most `q` hash calls, counting signing and the final verification.
Then a forger wins at most `q` times as often as a named solver of a co-Diffie-Hellman problem.
That problem asks for `(a * c) • g2` from `a • g1`, `a • g2` and `c • g2`.
It is stronger than the co-CDH of the source's §2, which omits `a • g2`.
The source needs it when no computable map from `G1` to `G2` is known.

`forgeAdvantage_blsScheme_le` (`Proofs/Bls/Security/Refinement.lean`) applies the theorem to EthLib.
The groups are the multiples of the generators of G1 and G2, and the test is the pairing check.
The test is sound (`blsScheme_sound`).
`sign_eq` and `verify_iff_isDh` prove that EthLib's `sign` and `verify` compute the scheme.
There `H(m)` is the hash to G2 of `m` under the message tag.
Aggregation and proofs of possession lie outside that game.

A second game (`Proofs/Bls/Security/PopGame.lean`) states unforgeability of aggregates with proofs of possession, after §3.3 of [draft-irtf-cfrg-bls-signature-04](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3).
One key is honest; the adversary chooses the others.
It wins with an aggregate on a message it never asked to be signed, verifying under the sum of keys that include the honest one and all carry valid proofs.
The counts below include the calls of signing, of the honest proof and of verification.
`Pop.forgeAdvantage_le` (`Proofs/Bls/Security/PopBound.lean`) bounds a forger within `q` message and `qK` key hash calls by `q` times a named solver of the same problem, plus `(q + qK - 1) / |F|`.
It assumes the test is sound, every element of `G1` is a multiple of `g1`, and `qK` is at most the characteristic of the scalars.
Without the last, enough copies of the honest key sum to zero.
`Pop.byteForgeAdvantage_le_coCdhAdvantage` (`Proofs/Bls/Security/PopByteGame.lean`) carries the bound to EthLib's bytes.
The forger sees compressed keys, hashes, signatures and proofs, and returns bytes.
It must pass EthLib's proof verification for every key and EthLib's fast aggregate verification, each with the oracle's hash in place of the hash to G2 (`Proofs/Bls/Security/PopRefinement.lean`).
`byteVerify_eq_popVerify` and `byteFastAggregateVerify_hashPoint` show that with the real hashes these checks are `popVerify` and `fastAggregateVerify`, and `popProve_eq` that the honest proof is `popProve`.
The key hash of bytes that decode to a multiple of `g1` is the group oracle on the decoded element; other bytes get independent uniform answers.
The key-call count leaves those other bytes out, since verification never hashes them.
`LightClientForgery.forgeAdvantage_le` (`Consensus/Proofs/LightClient/Unforgeable.lean`) applies the bound to the light client.
One sync committee member is honest; the forger chooses the configuration, the store, the update and the clock, and gives a proof of possession for each signer.
It wins if `validateLightClientUpdate` accepts the update with the honest member's bit set, with the oracle's hash of the signing root, and the honest member never signed that root.
Its advantage is at most the byte bound above.
`validateLightClientUpdate_oracleChecks` shows that with the real hash of the signing root, the game's check is the light client's check with the BLS checks.
The light client theorems of `Authenticate.lean` still take `SignatureChecks.AggregateSound`, because they reason about one accepted update, not a probability.
The game requires a proof of possession that passes PopVerify, §3.3.3, under the key tag.
Ethereum registers a validator key with a deposit signature instead, a signature on a message that holds the key, under the message tag and the deposit domain.
The bound does not cover that form of proof.

`Security.byteForgeAdvantage_le` (`Proofs/Bls/Security/Refinement.lean`) turns a forger on byte encodings into a named group-element forger with at least the same advantage.
The byte forger receives a compressed key and compressed hash and signing answers, and returns arbitrary message and signature bytes.
The game runs EthLib's G2 decompression, signature subgroup check and key validation before the pairing check.
This step needs no pairing law, because the byte check and the group test pair the same group elements.
`encode_publicKey`, `encode_signature` with `sign_eq`, and `byteVerify_hashPoint` connect these operations to EthLib's public key, signing and verification when the oracle uses EthLib's hash.
The bound still models that hash as a random oracle, not as the concrete hash function.

Freshness is by message: a message submitted to signing cannot win with any signature bytes.
`decodeSignature_encode` and `encode_eq_of_decodeSignature` prove both encoding round trips, so two accepted encodings of the same subgroup element cannot differ.
The byte game keeps the group game's uniform scalar distribution, including zero, whose key validation rejects.
EthLib's secret keys exclude zero, and a zero key always loses.
`nonzeroByteForgeAdvantage_eq` (`Proofs/Bls/Security/Refinement.lean`) draws a uniform nonzero key instead.
Against that key, a forger wins exactly `r / (r - 1)` times its byte advantage.
`nonzeroByteForgeAdvantage_le_coCdhAdvantage` carries this factor into the co-CDH bound below.
`Security.byteForgeAdvantage_le_coCdhAdvantage` gives the same `q`-factor co-CDH bound when the decoded forger makes at most `q` hash calls.
`byteForgeAdvantage_le_coCdhAdvantage_of_byteHashCallBound` states the bound with the hash-call bound on the byte forger itself.
`byteHashCallBound_iff` proves that the two bounds are equivalent, because the encoding forwards each query once.

### secp256k1

The secp256k1 theorems are correctness statements.
`card_point` (`Proofs/Secp256k1/Order.lean`) proves that the group has `n` points, so the cofactor is 1.
`decode_eq_ok_iff` (`Proofs/Secp256k1/Encoding.lean`) proves that the decoder accepts exactly the encodings of the points other than `O`.
`verify_sign` (`Proofs/Secp256k1/Ecdsa.lean`) proves that a signature from the signing operation of SEC 1 verifies.
`verify_eq_true_iff` (`Proofs/Secp256k1/Recovery.lean`) states verification against a key in the group of the curve.
It is the verifying operation of SEC 1 v2 §4.1.4.
By it, a signature is valid exactly when `r` and `s` lie in `[1, n - 1]` and the key is a point of the curve other than `O`.
The point `(e / s) G + (r / s) Q` must also be other than `O`, with `x mod n = r`.
`verify_recover` and `recover_of_verify` (`Proofs/Secp256k1/Recovery.lean`) prove that a recovered key verifies the signature, and that every key that verifies one is recovered, when `r + n >= p`.
`recover_eq_ok_iff` states recovery in the group of the curve.
It is the public key recovery of SEC 1 v2 §4.1.6, with `x_R = r` only.
By it, recovery returns `Q` exactly when `r` and `s` lie in `[1, n - 1]` and `R = (r, y)` lies on the curve.
The parity of `y` must be the recovery id.
`Q` must be a point of the curve other than `O`, equal to `(s / r) R - (e / r) G`.
`verify_lowS_unique` (`Proofs/Secp256k1/Malleability.lean`) proves that two low-s signatures with one `r` that verify are equal, under the same bound.
`verify_iff_s_eq_or_neg` assumes the same bound and a valid signature `(r, s)`.
Under them, `(r, s')` verifies under the same key and hash exactly when `s'` is `s` or `n - s`.
`verify_and_isLowS_iff` adds that `s` is low, and then that signature is the only valid low-s one with that `r`.

The probability of forging a signature with a signing oracle has a bound in an idealised model, below, which rests on the discrete logarithm problem and on properties of the hash.
`Proofs/Secp256k1/Security/Game.lean` states the unforgeability game of GenDSA, the abstraction of ECDSA in [Fersch, Kiltz and Poettering](https://doi.org/10.1145/2976749.2978413), Definition 6, in their bijective random oracle model.
There, `verify_neg` shows that `(r, -s)` verifies whenever `(r, s)` does, when opposite points share their encoding, as `x` coordinates do.
So the game counts only messages that were never signed.
`forgeAdvantage_collision_pos` shows that a collision of the message hash wins that game with positive probability.
`Proofs/Secp256k1/Security/KeyOnly.lean` states the key-only game of the source's Definition 4, with no signing oracle.
`forgeAdvantage_toAdversary` proves that it is the chosen-message game of a forger that never asks for a signature.
`keyOnlyAdvantage_le_indep` replaces the bijection by independent uniform answers in that game.
It counts no win once a new answer repeats a cached value in the direction of its query.
The cost is at most `q (q + 1) / 2` over the size of the bijection's domain, for a forger with at most `q` queries to the bijection or its inverse.
That is the step from Game G0 to Game G1 of §4.2 of the source, in the proof of its Theorem 2, whose bound `Q² / 2^L` is at least as large.
The source draws the key from the nonzero scalars; the key-only game here draws it from all scalars, and the key `0` never verifies.
So its advantage is the source's times `(n - 1) / n`, where `n` is the number of scalars.
`keyOnlyIndepAdvantage_eq_outside` (`Proofs/Secp256k1/Security/KeyOnlyOutside.lean`) proves that the advantage with independent answers stays the same when each new forward answer is one query to an outside oracle with no input.
`forward_point_eq_answer_ne_of_mem_support_contextFork` proves that the two runs returned by a replay fork at the new forward query of the forgery's point share that point and got different answers there.
`le_prEvent_isSome_contextFork_keyOnlyOutsideRun` bounds the chance of the fork from below on each fixed key, in the form of Lemma 1 of the source.
`le_prEvent_isSome_contextFork_keyOnlyOutsideRun_uniform` gives the same bound with the key drawn uniformly, as Lemma 1 draws it at random.
Unlike Figure 2 of the source, the fork draws the coins after the fork point again.
`reduce_forward_eq_of_forkIndex_eq_some` (`Proofs/Secp256k1/Security/ForwardCase.lean`) proves that the check of a run with a fork index read the logged answer at that index, so `ψ` maps that answer to the forgery's `t`.
It rests on an invariant of the run: each logged pair stays cached, and while no flag is raised the cache is a partial bijection.
`forward_eq_of_mem_support_contextFork` (`Proofs/Secp256k1/Security/ForwardCase.lean`) gives, for both runs of the fork, the shared point and the two different answers, with `ψ` mapping each answer to the `t` of its forgery.
For a forger with at most `q` queries to the bijection or its inverse on every key, `keyOnlyIndepAdvantage_le_forkIndex_add_notMem` (`Proofs/Secp256k1/Security/KeyOnlyOutside.lean`) bounds its chance to win with independent answers, over a uniform key, by the chance of a fork index plus the chance that the check passes on a point that was not a new forward query.
`prEvent_inverse_le_dlog`, below, bounds the second chance.
`divisionAdvantage` (`Proofs/Secp256k1/Security/DivisionResistance.lean`) states the ψ-relative division resistance of the hash, Definition 5 of the source.
`prEvent_contextFork_div_eq_le_divisionAdvantage` bounds the fork whose two forgeries divide to the same scalar, the abort of line 10 of Figure 9, by `q + 1` times the advantage of the reduction of Figure 10.
The hash is fixed there, while §2.3 of the source draws a key for it, so the bound charges that named reduction and no adversary of division resistance in general.
`prEvent_contextFork_div_ne_le_dlog` (`Proofs/Secp256k1/Security/ForwardSolver.lean`) bounds the other forks by the advantage of the discrete-logarithm solver of Figure 9, which extracts the key from the two forgeries.
`redrawInverse_fst_evalDistEq` (`Proofs/Secp256k1/Security/Redraw.lean`) proves the step of lines 25 to 28 of Figure 7 of the source: a uniform answer that encodes a nonzero multiple of the base point, redrawn as the encoding of `a g` for a uniform nonzero `a`, is still uniform.
It assumes that the base point is nonzero, that `2` is nonzero in the scalars, that the encoding is semi-injective, and that opposite points share their encoding; the encoding is then exactly 2-to-1 on those points.
So it covers ECDSA, not the injective case of Definition 2 (b) of the source.
The redraw takes the test of the image as an argument, with a hypothesis that it agrees with a search of the encodings of the nonzero multiples of the base point; part (a) of Definition 2 asks that this test be efficient, which EthLib does not model.
`prEvent_inverse_le_dlog` (`Proofs/Secp256k1/Security/InverseCase.lean`) bounds, in the key-only run with independent answers and new forward answers asked outside, the chance that the check passes on a point that was not a new forward query.
The event does not require the flag of repeated answers to be clear, so with the fork index of the forward case it covers every run that wins.
The bound is the advantage of a discrete-logarithm solver, which runs the forger once with the same test of the image; this is the step from Game G2 to Game G3 of the source.
The solver's game is the discrete-logarithm game of the oracle framework, which draws the key from all scalars, while Definition 1 of the source draws it from the nonzero scalars.
The two advantages differ by at most `1 / n`, where `n` is the number of scalars; no theorem states it.
`keyOnlyAdvantage_le` (`Proofs/Secp256k1/Security/KeyOnlyBound.lean`) assembles these parts into the bound of Theorem 2 of the source, for a key-only forger with at most `q` queries to the bijection or its inverse on every key.
The bound charges three adversaries built from the forger: the two discrete-logarithm solvers and the reduction to division resistance.
It is a bound on the key-only game only.
`forgeAdvantage_le_noCollisionAdvantage_add_collisionAdvantage` (`Proofs/Secp256k1/Security/Collision.lean`) is the first step of Theorem 1 of the source, from Game G0 to Game G1 of Figure 4.
It charges a forgery on a new message with the hash of a signed one to a finder of collisions built from the forger, which samples the bijection lazily.
The hash is fixed, so the bound charges that named finder and no adversary against collisions in general.
`noCollisionAdvantage_le_programmed` (`Proofs/Secp256k1/Security/Programmed.lean`) is the step from Game G1 to Game G2 of Figure 5, where the signer programs the bijection; it costs the chance of a conflict, two pairs of the cache of the bijection that share a query or an answer.
`prEvent_programmedExperiment_conflict_le` (`Proofs/Secp256k1/Security/Conflict.lean`) bounds that chance, for a forger with at most `q_Π` queries to the bijection or its inverse and `q_S` signing queries on every key, when the base point is nonzero and the encoding semi-injective.
The signer tries up to `fuel` nonces per request where the source's tries one, so the source's `Q_s` programmed pairs become `fuel · q_S`; the check of the forgery may relay one more query, which Definition 4 of the source rules out, so its `Q_Π` becomes `q_Π + 1`.
`keylessExperiment_evalDistEq_programmedExperiment` (`Proofs/Secp256k1/Security/Keyless.lean`) is the step from Game G2 to Game G3 of Figure 5: the game with a signer that reads only the public key has the same law, forgery, check result and final states, when the base point is nonzero.
The source's claim that the forger wins as often in both games does not follow as written: its Game G2 records a pair of the bijection before its checks (line 14), while its Game G3 records one only when a nonce signs (line 40).
The signer without the key here records the pairs of failed nonces too.
`prEvent_keylessExperiment_win_le` (`Proofs/Secp256k1/Security/KeylessForger.lean`) charges a win of that game to two adversaries built from the forger: the key-only forger of Figure 6 of the source, which runs the game with its own bijection oracle, and a solver of the discrete logarithm.
The two checks agree unless the most recent pair at the forgery's point is one that the signer programmed; that case gives the key, and the solver tries each candidate and keeps the one that gives the public key.
Figure 6 of the source signs again at line 30 when the point is programmed, which may fail, so its claim that the key-only forger wins as often as Game G3 does not hold exactly; the bound here charges that case to the named solver instead, which adds one discrete-logarithm term to Theorem 1.
The solver runs the game itself, with a lazy bijection; no theorem states its running time or the forger's.
`forgeAdvantage_le_keyOnly` (`Proofs/Secp256k1/Security/ChosenMessageBound.lean`) assembles these steps into Theorem 1 of the source, for a forger with at most `q_Π` queries to the bijection or its inverse and `q_S` signing queries on every key: its advantage is at most the key-only forger's advantage, plus the advantage of the solver for a programmed point, plus the finder's advantage, plus the bound on a conflict.
`forgeAdvantage_le` (same file) bounds the key-only forger's advantage in turn by `keyOnlyAdvantage_le`, with `q = q_Π`, which gives a bound on the chosen-message game by three solvers of the discrete logarithm, a reduction to division resistance, a finder of collisions, and terms in the sizes of the bijection's domain and of the scalars.
It needs a nonzero base point, `2` nonzero in the scalars, a semi-injective encoding under which opposite points share their encoding, a normal form that keeps or negates `s`, and a test of the image that agrees with the search over the nonzero multiples of the base point; so it covers the case of Definition 2 (b) of the source with opposite points sharing their encoding, as for ECDSA, and not the injective case; the model's ECDSA scheme meets the hypotheses on the scheme by separate lemmas, and no theorem applies the bound to it.
It keeps the departures of its steps from Theorem 1, among them: the signing oracle answers a repeated message from its cache, as RFC 6979 does, the hash is fixed and the bound charges named reductions, no running times are stated, the key is drawn from all scalars, `Q_s` becomes `fuel · q_S` and `Q_Π` becomes `q_Π + 1` in the conflict bound, the signer without the key records the pairs of failed nonces, and the forgery at a programmed point is charged to a solver of the discrete logarithm, one term more than the source's bound.
The bound on a conflict keeps the three terms of the source's proof, in the form of its own module, before the source sums them into `3 Q Q_s / ((q - 1) / 2 - Q)`; no theorem compares the two.
The departures of the key-only bound from Theorem 2 are listed with it, above.
`ecdsa_verify_eq_verify_ecdsaScheme` (`Proofs/Secp256k1/Security/Refinement.lean`) proves that `verify` is the game's verification, with the bijection the identity, for `r` and `s` below `n`.
`exists_signNonce_of_sign` proves that every signature from `sign` is the game's signature for some nonzero nonce; that is correctness of signing, and says nothing about how RFC 6979 draws the nonces.
The game draws the bijection uniformly, so the bound on it applies to EthLib, where the bijection is the identity, only under the heuristic of the source that the identity behaves as a bijective random oracle.
It would also need the pseudorandomness of RFC 6979, which no theorem states, and it ignores the 16-nonce limit and the failure of `sign` when `x_R >= n`.
A forger of transactions only needs a key with the right address, so a bound for them also needs a term for the Keccak-256 hash of the key.
The low-s rule of transactions only restricts the forger, so it needs no term.
The model's encoding, the `x` coordinate as a 256-bit string, meets part (b) of Definition 2 of the source (`ecdsaScheme_semiInjective`), which their Lemma 2 proves.

`ecdh_eq_ok_iff` (`Proofs/Secp256k1/Ecdh.lean`) states ECDH in the group of the curve.
It is the Diffie-Hellman primitive of SEC 1 v2 §3.3.1, with no key derivation function.
By it, ECDH returns a secret exactly when the public key is a point of the curve other than `O` and the private key is nonzero.
The secret is then the `x` of their product, as 32 big-endian bytes.

### ENR "v4" records

`verifyV4_negS` (`Networking/Proofs/Enr/Security.lean`) proves that a record with a 64-byte signature verifies exactly when its copy with `n - s` does, and `negS_ne_of_verifyV4` that the two differ.
`ecdsaForgery_of_forgery` (`Networking/Proofs/Enr/Security.lean`) proves that a forged EIP-778 "v4" record gives a forgery of ECDSA with Keccak-256 on a fresh message.
The security of records then rests on the chosen-message security of that ECDSA, which EthLib assumes and does not prove; the bound on the chosen-message game above is proved only in the bijective random oracle model.

### alt_bn128

The alt_bn128 theorems check the constants and the group law of `G_1`, which the ECADD, ECMUL and ECPAIRING precompiles use.
`modulus_prime` (`Proofs/AltBn128/Field.lean`) proves that the base field modulus `p` and the group order `q` are prime.
`toPoint_add` and `toPoint_mulBits` (`Proofs/AltBn128/Curve.lean`) prove that addition and double and add agree with the group law of `y^2 = x^3 + 3` over `ZMod p`.
`card_point` (`Proofs/AltBn128/Order.lean`) proves that this group has `q` points, so the cofactor is 1.

`instField` (`Proofs/AltBn128/Fp2.lean`) proves that `Fp2` is a field, and `toPoint_add` (`Proofs/AltBn128/Twist.lean`) proves the group law of the twist that holds `G_2`.
`mulBits_order_eq_infinity_iff` proves that the `G_2` subgroup check of ECPAIRING accepts exactly the points `Q` on the twist with `q Q = O`.
`addOrderOf_generator` (`Proofs/AltBn128/G2Order.lean`) proves that the generator `P2` of EIP-197 lies on the twist and has order `q`.
`instField` (`Proofs/AltBn128/Fp12.lean`) proves that `Fp12`, where the pairing lands, is a field with the product of the specification.
`card_eq` proves that it has `p^12` elements, and `irreducible_poly` that `X^12 - 18 X^6 + 82` is irreducible over `ZMod p`.
`finalExponentiation_eq_pow` (`Proofs/AltBn128/FinalExponentiation.lean`) proves that the final exponentiation of the pairing check raises its argument to `(p^12 - 1) / q`.
`slopeLine_eq` and `verticalLine_eq` (`Proofs/AltBn128/Lines.lean`) prove that the lines of the Miller loop, written by their coefficients, are the textbook lines `l w (xt - x1 w^2) - (yt - y1 w^3)` and `xt - x1 w^2` in `Fp12`.
`pairing_eq_finalExponentiation_loop` (`Proofs/AltBn128/MillerChain.lean`) proves that the pairing of `P` and `Q` is the final exponentiation of three values at `P`.
Here `Q` lies on the twist with `q Q = O`, `Q'` is its untwist, and `pi` is the `p`-th power map.
The first value is Miller's algorithm (`Proofs/MillerFunction.lean`) for `6 u + 2` and `Q'`.
The others are the line through `(6 u + 2) Q'` and `pi(Q')`, and the line through their sum and `-pi(pi(Q'))`.
This is the optimal ate pairing of Beuchat et al. (ePrint 2010/354, §2).
`untwist_frobenius` proves that the Frobenius map of the specification is `pi` under the untwist.

`AltBn128.pairingBilinear` (`Proofs/AltBn128/PairingAte.lean`) proves that the pairing is bilinear on the multiples of the generators: `e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b` in `Fr`.
`orderOf_pairing_generators` (`Proofs/AltBn128/Nondegenerate.lean`) proves that the pairing of `P1` and `P2` has order `q`, so it is not 1; the kernel evaluates that pairing.
`pairingCheck_eq_true_iff` (`Proofs/AltBn128/PairingBilinear.lean`) proves that the check passes exactly when the product of the pairings of its pairs is 1.
The pairing law is stated as a structure, `AltBn128.PairingLaws` (`Proofs/AltBn128/PairingLaws.lean`), in the shape of the BLS one.
It states the check of EIP-197: the pairs `(a_i P1, b_i P2)` pass exactly when `sum_i a_i b_i = 0`.
`PairingLaws.of_bilinear` (`Proofs/AltBn128/PairingBilinear.lean`) derives it from one smaller hypothesis, `PairingBilinear`: `e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b` in `Fr`.
`AltBn128.pairingLaws` (`Proofs/AltBn128/PairingAte.lean`) proves `AltBn128.PairingLaws` from it.
`Ate.frobenius_generator` (`Proofs/AltBn128/PairingAte.lean`) proves, by a kernel computation on the twist, that the Frobenius map of the specification sends `P2` to `p P2`.
`Ate.frobenius_of_mem` proves that `pi` acts as `p` on the untwist of `G_2`.
`Ate.eq_zero_of_frobenius_eq` proves that `pi` fixes only `O` there, because `q` does not divide `p - 1`.
`Ate.ratioDivisor_ateLines` proves that the three values of the pairing, with the verticals through the two sums, have the divisor `s ((Q') - (O)) + ((pi Q') - (O)) + ((pi^8 Q') - (O)) - ((pi^9 Q') - (O))`, with `s = 6 u + 2`.
`Ate.pow_ateExponent` proves that `z^(N (s + p + p^8 - p^9))` is 1 for every nonzero `z` in `Fp12`, with `N = (p^12 - 1) / q`.
`Ate.ateValue_add_left` proves that these lines at `P`, raised to `N`, are linear in a point `P` that `pi` fixes.
`Ate.ateValue_add_right` proves that they are linear in `Q'` on the untwist of `G_2`.
`Ate.pairing_eq_ateValue` proves that the pairing of a finite `P` on the curve and a `Q` on the twist whose untwist lies in `G_2` is that value.
`Point2.nsmul_order_eq_zero_iff` (`Proofs/AltBn128/G2Torsion.lean`) proves that every point `Q` with `q Q = O` on the twist is a multiple of `P2`, as EIP-197 says.
`Point2.mulBits_order_eq_infinity_iff_exists` restates it for the subgroup check of ECPAIRING, and `Point.exists_eq_mulBits_generator` (`Proofs/AltBn128/Order.lean`) does the same for `P1`.
`exists_mulBits_generator_of_decodePair` (`Execution/Proofs/Evm/Precompiles/AltBn128/Pairing.lean`) combines them: every pair that ECPAIRING decodes is a pair of multiples of the generators, where the law above holds.
`exists_represents_of_decodePairs` and `exists_represents_of_ecpairing` (`Execution/Proofs/Evm/Precompiles/AltBn128/PairingProduct.lean`) lift this to lists of scalars `a_i` and `b_i` in `ZMod q`, for every successful decoding and every successful call.
`ecpairing_eq_one_iff` and `ecpairing_eq_zero_iff` apply `AltBn128.pairingLaws`, with no hypothesis on the pairing.
On a successful call, they prove that ECPAIRING returns the word 1 exactly when `sum_i a_i * b_i = 0`, and the word 0 otherwise.
`ecpairing_encodePairs` computes the output on the encodings of represented pairs, and `ecpairing_generators`, `ecpairing_generator_neg` and `ecpairing_empty` reach both outputs.

`ecadd_toPoint` and `ecmul_toPoint` (`Execution/Proofs/Evm/Precompiles/AltBn128/Group.lean`) carry this group law to the precompiles.
A call of ECADD that succeeds returns the sum of its two points, and a call of ECMUL returns its point times its 32-byte scalar.
`bytesToG1_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/AltBn128/Encoding.lean`) proves that the decoder of a point of `G_1` accepts 64 bytes exactly when they are the EIP-196 encoding of a point on the curve.
`bytesToG1_ecadd` and `bytesToG1_ecmul` (`Execution/Proofs/Evm/Precompiles/AltBn128/Group.lean`) prove that the output of a call of ECADD or ECMUL that succeeds decodes to that sum or that product.

`decodePair_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/AltBn128/Pairing.lean`) proves that a pair of ECPAIRING decodes exactly when its two points decode and `q Q = O` holds for its point `Q` of the twist.
`Point.mulBits_order` (`Proofs/AltBn128/Order.lean`) proves `q P = O` for every point `P` on the curve.
So the curve equation is enough for `G_1`, as EIP-197 says, and the decoder checks the order of the point of the twist only.

### secp256r1

The secp256r1 theorems are correctness statements, like those of secp256k1.
`modulus_prime` (`Proofs/Secp256r1/Field.lean`) proves that both moduli are prime.
`toPoint_add` (`Proofs/Secp256r1/Curve.lean`) proves that the addition of SEC 1 is the group law of the curve.
`card_point` (`Proofs/Secp256r1/Order.lean`) proves that the group has `n` points, so the cofactor is 1.
That proof needs one more fact than the proof for secp256k1: `x^3 - 3 x + b` has no root mod `p`.
The kernel checks it by an inverse of `X^p - X` modulo the cubic.

`verify_sign` (`Proofs/Secp256r1/Ecdsa.lean`) proves that a signature from the signing operation of SEC 1 verifies.
`verify_eq_true_iff` states verification as the verifying operation of SEC 1 v2 §4.1.4, read in the group of the curve.
By it, a signature is valid exactly when the conditions below all hold.
Both `r` and `s` lie in `[1, n - 1]`, and the key is a point of the curve other than `O`.
The point `(e / s) G + (r / s) Q` must also be other than `O`, with `x mod n = r`.
`verify_iff_s_eq_or_neg` describes the signatures that verify next to a valid one.
Take a valid signature `(r, s)` under a key and a message, with `r + n >= p`.
The signatures `(r, s')` that verify under the same key and message are then exactly those with `s' = s` or `s' = n - s`.
For P-256, `p - n` is about `2^126`, so the bound excludes only the values of `r` below it.
No theorem states unforgeability.

### AES

The AES theorems are correctness statements, except the bounds on GHASH over a uniform hash subkey.
No theorem bounds tag forgery or states a security property of the cipher.
`invCipher_cipher` and `ciphInv_ciph` (`Proofs/Aes/Block.lean`) prove that the inverse cipher of FIPS 197 undoes the cipher, for every key schedule and so for every key.
`sbox_eq` proves that each entry of the S-box table equals the inverse in GF(2^8) followed by the affine map of FIPS 197 §5.1.1.
`ciph_eq_spec` proves that AES-128 and AES-256 equal a model of FIPS 197, for every key and every block.
The model follows Algorithms 1 and 2 of FIPS 197 over the state `s[r, c]` of §3.4.
It multiplies bytes as polynomials modulo `m(x)`, and it builds its S-box from the inverse `b^254` and the affine map of §5.1.1.
So the model shares no table and no GF(2^8) arithmetic with the code.
`sbox_eq_spec` proves that each entry of the S-box table equals the S-box of the model.
`getElem_keyExpansion_of_lt` proves that the first `Nk` words of the key schedule are the words of the key.
`getElem_keyExpansion_of_le` proves that each later word follows the recurrence of Algorithm 2, for a key of at least one word.
EthLib has no AES-192, so no theorem covers it.
No theorem compares the inverse cipher with a model of Algorithm 3.
`ciphInv_spec_ciph` proves only that the inverse cipher undoes the cipher of the model.
`ctr_ctr` (`Proofs/Aes/Ctr.lean`) proves that CTR decryption of SP 800-38A returns the plaintext, for every forward cipher and initial counter.
`repeat_inc_injOn` proves that, for `m <= 128`, the first `2^m` counters that the standard increment gives from one block are distinct.
The CTR keystream applies one increment per block, so these are the counters of the first `2^m` blocks of a message, as Appendix B.1 states.
`ctr_block` states that link: block `j` of the output is block `j` of the data XORed with the cipher of the first counter incremented `j` times.
`repeat_inc_two_pow` proves that the counter after `2^m` increments is the first one again.
The Python tests (`bindings/python/tests/aes/test_aes.py`) check FIPS 197 Appendix B and the AES-128 and AES-256 vectors of its 2001 Appendix C.
They also check the CTR examples F.5.1, F.5.2, F.5.5 and F.5.6 of SP 800-38A.

`decrypt_encrypt` (`Proofs/Aes/Gcm.lean`) proves that GCM decryption of SP 800-38D returns the plaintext of an honest ciphertext and tag.
`decrypt_eq_ok` proves that decryption accepts no tag other than the honest one.
`decrypt_eq_ok_iff` proves that decryption returns `p` exactly when `p` encrypts to the given ciphertext and tag.
So every pair that decryption accepts is an honest encryption.
The three hold for every forward cipher.
`residue_mul` (`Proofs/Aes/GaloisField.lean`) proves that the block product of SP 800-38D §6.3, Algorithm 1, is the product of the two blocks read as polynomials over GF(2) modulo `1 + u + u^2 + u^7 + u^128`.
`residue_xorBlock` proves that XOR is their sum, and `residue_injective` that two different blocks have two different residues.
`residue_ghash` proves that GHASH of `X_1 ... X_m` is `X_1 H^m + ... + X_m H` on residues, the form that §6.4 states.
`irreducible_modulus` (`Proofs/Aes/Field.lean`) proves that the modulus is irreducible over GF(2), so the residues form a field, and `card_adjoinRoot_modulus` that this field has `2^128` elements.
The kernel checks a certificate of the test: 128 squarings by Algorithm 1 fix `u`, and a block inverts `u^(2^64) - u`.

`prEvent_xorBlock_ghash_eq_le` (`Proofs/Aes/Universal.lean`) takes two different lists of `m` blocks and a target block `c`.
It proves that a uniform hash subkey gives XOR `c` on their GHASH values with probability at most `m / 2^128`.
`prEvent_xorBlock_ghash_singleton_eq` proves that on distinct one-block inputs this probability is `1 / 2^128`.
`ghash_zeroBlock_cons` proves that a zero block in front does not change GHASH, so `[X]` and `[0, X]` agree for every key.
`prEvent_xorBlock_ghash_ghashInput_eq_le` proves the bound on GCM's padded input, for two different pairs of additional data and ciphertext with each string below `2^64` bits.
This is Lemma 2 of McGrew and Viega, [ePrint 2004/193](https://eprint.iacr.org/2004/193), Appendix A, without output truncation.
Its numerator `m` is the length of the longer of their two padded lists, the length block included.
The bound counts uniform hash subkeys; it does not bound tag forgery and says nothing about the cipher.

`gctr_inc_block` proves that GCM encrypts block `k` of the text under `J_0` incremented `k + 1` times.
`counter_ne_preCounter` and `counter_injOn` assume the length checks of §5.2.1.1.
Under them, the counters of the text differ from each other and from `J_0`, the counter of the tag.
`encrypt_shortTag` and `decrypt_shortTag` prove that both functions reject the 64-bit and 32-bit tags, which SP 800-38D Appendix C restricts.
The Python tests check seven test cases of the NIST CAVP file `gcmtestvectors.zip`, one of them a forged tag that decryption rejects.

### X25519 and ChaCha20-Poly1305

X25519 has no theorem: only the Python tests check it.
The ChaCha20-Poly1305 proofs cover output length, counter exhaustion and rejection of a wrong tag (`Proofs/ChaCha20Poly1305.lean`).
No theorem relates ChaCha20-Poly1305 to an independent model of RFC 8439.
The Python tests compare the bindings with the RFC 7748 and RFC 8439 vectors.
The million-iteration X25519 vector requires `ETHLIB_SLOW_VECTORS=1`.

### Noise XX and libp2p identities

`readLibp2p_authenticates` (`Networking/Proofs/Noise/Identity.lean`) says that the read of message 2 or 3 accepts only a payload whose signature verifies on the static key that the message carries.
The state then stores that remote, and completion returns it without reading a message or verifying the signature again.
`complete_ok` holds for any state: the returned remote is the stored one, its static key is the remote static key of the handshake, and the ciphers are those of that handshake.
`Produced.complete_authenticates` adds, for states that the libp2p initialize, write and read functions produce, that the signature verifies on that static key and that the public key decodes to the stored point.
A caller that edits the state can therefore complete with a remote whose signature does not verify.
`Produced.complete_isOk` says that completion of such a state after message 3 succeeds.
These are acceptance theorems, not a proof of protocol security, confidentiality or constant-time execution.
They relate the identity to the transport keys only through the shared handshake state.
No theorem says that the chaining key mixed a Diffie-Hellman output with the remote static key, and none covers the handshake hash.
Only the libp2p read verifies an identity, and completion checks that the stored remote has the remote static key of the handshake.
The raw transport split of an XX state checks neither.
The Python tests compare the raw XX handshake with a published test vector.
No published vector covers the libp2p payload, so its tests check the keys and signatures with independent code.

The bindings take explicit keys and state tuples.
Callers must use fresh ephemeral keys and use the returned state after each successful cipher call.
They must discard handshake state after an error.

### Engine API authentication

`Jwt.check_build_of_size` (`Engine/Proofs/Jwt.lean`) proves that a token built with a 32-byte secret passes with that secret at clocks within 60 seconds of its issued-at time.
The builder validates the JSON it generates, and `Jwt.build_eq_ok` proves that this validation never fails.
`Jwt.authenticate_eq_error_of_tag_ne` proves that a token whose tag differs from the HS256 tag of its parts is refused before any JSON is read.
Keeping a party without the secret away from the reader also assumes HMAC unforgeability, and a captured token can be replayed within its 60 seconds.
`Jwt.check_eq_false_of_algorithm_ne` proves rejection when the decoded algorithm differs from HS256.
The total JSON reader has no separate theorem of agreement with RFC 8259.
These theorems do not establish HMAC unforgeability or constant-time execution.

### ERC-2335 keystores

The keystore proofs show that a short intermediate key, a mismatched checksum, or a key derivation beyond the caller's limits prevents decryption (`Proofs/Keystore.lean`).
They do not prove Unicode normalization correct for every input, or prove the cryptographic security of the keystore.
The Python suite compares NFKD with Unicode 16.0.0's normalization tests and checks the two ERC-2335 vectors.
JSON text parsing stays in the export boundary; the specification consumes a `Lean.Json` value.
Before parsing, the export refuses deep nesting, long digit runs and large positive exponents, which could exhaust the parser's stack, time or memory.
Decryption takes the caller's limits on memory and work, and refuses a key derivation whose modeled memory or work exceeds them.
The model counts bytes of buffers and calls of 64-byte block functions; no theorem shows that it bounds the code.
The Python binding sets default limits.

### RIPEMD-160

`compress_toBitVec` (`Proofs/Hash/Ripemd160.lean`) proves that the compression of one block, read as 32-bit vectors, is the compression of a model of the authors' pseudo-code.
The statement holds for every chaining variable and every 64-byte block.
The model runs both lines in one loop, rotates 32-bit vectors, and reads each word least significant byte first.
It shares the constants, the word orders and the rotation amounts with the code.
`K_from_square_roots` and `K'_from_cube_roots` derive the constants from square and cube roots.
`r_groups_permute` and `r'_groups_permute` check only that each group of a word order reads every word once.
`hash_eq_spec` proves that the hash of every message is the hash of the model, with no bound on the length.
The model pads the message as MD4 does (RFC 1320 §3.1 and §3.2), with the low 64 bits of the bit length.
It runs the blocks from its own initial value, and its digest puts the least significant byte of each word first.
`pad_eq_spec` proves that the padding of the code is the padding of the model.
The Python tests (`bindings/python/tests/precompile/test_ripemd160.py`) check the hash against the test vectors on Bosselaers' RIPEMD-160 page.

### KZG

The KZG and PeerDAS proofs use `Bls.pairingLaws`, which proves the pairing law of the check.
Their theorems take no pairing-law hypothesis.

Blobs, cells, commitments, proofs and field elements are byte vectors with their length in the type.
`Proofs/Kzg/Core.lean` proves that parsing rejects bytes of any other length.
It and `Proofs/Kzg/Cells.lean` prove that the operations reject other malformed inputs.
An example is two lists of different lengths.

Each operation takes the trusted setup as an argument and returns `Except KzgError`, so the kernel can unfold it.
`computeCellsAndKzgProofs_blob_spec` and `recoverCellsAndKzgProofs_spec` (`Proofs/Kzg/Fk20Proofs.lean`) state the cells and proofs that two operations return.
They take two hypotheses on the setup.

- `setup.Valid`: every point of the setup is on its curve.
  For the embedded setup, `TrustedSetup.ofHex_valid` proves it if the setup decodes.
- `hsetup_tor`: the first 4032 monomial points of `G1` have an order that divides `r`.
  For the embedded setup, `TrustedSetup.ofHex_torsion` (`Proofs/Kzg/SetupTorsion/Embedded.lean`) proves it for all 4096 monomial points of `G1`, if the setup decodes.
  The kernel checks each point from its `x` coordinate.
  This is a recorded exception to the rule of a few seconds for concrete facts in [CONTRIBUTING.md](CONTRIBUTING.md#known-answers).
  It costs about 8 CPU-minutes per build and about as much per replay, in 16 modules.
  Each module takes 20 to 50 seconds and 1.9 GB to elaborate, and 2.4 GB to replay.
  No theorem proves that the embedded setup decodes, so that stays an assumption.
  The Python suite gives two checks of it, both on compiled code.
  Each KZG vector runs an operation that first decodes the embedded setup.
  `bindings/python/tests/kzg/test_trusted_setup.py` decodes each point of the setup, in `G1` and `G2`, and checks that it is in the subgroup.

`TrustedSetup.WellFormed.valid` and `TrustedSetup.WellFormed.torsion` derive both from a well-formed setup.
`computeCellsAndKzgProofs_blob_spec_ofHex` and `recoverCellsAndKzgProofs_spec_ofHex` state the two theorems for the embedded setup, with neither hypothesis.
Of the setup, they assume only that it decodes.

For a well-formed setup, `blobToKzgCommitment_represents` (`Proofs/Kzg/Commitment.lean`) proves that a blob's commitment holds its polynomial at the secret.
On a well-formed setup (assumption D3), `blobToKzgCommitment_binding` in the same file proves that two blobs whose decoded values differ share a commitment only when the secret is a root of `p - p'`.
Here `p` and `p'` are the interpolants: the polynomials of degree below 4096 that take each blob's decoded values on the domain.
The theorem also proves that `p - p'` is nonzero and has degree below 4096.
That proof needs no pairing law.
It is not computational binding: no theorem bounds the cost of finding two such blobs without the secret.
For a well-formed setup, honest KZG proofs and blob proofs verify (`verifyKzgProof_computeKzgProof`, `verifyBlobKzgProof_computeBlobKzgProof`, `Proofs/Kzg/Verify.lean`).
`verifyKzgProofImpl_iff` states when the check accepts: `c - y = w (τ - z)`, for decoded points representing `c` and `w`.
On a well-formed setup (assumption D3), `verifyBlobKzgProof_binding` (`Proofs/Kzg/BlobBinding.lean`) splits an accepted blob opening into three cases.
Let the validated commitment and proof represent `f(τ)` and `g(τ)` for polynomials `f` and `g` of degree below 4096.
Let `p` be the interpolant of the blob's decoded values, and let `z` be the evaluation challenge.
Then `f = p`; or `f ≠ p`, `f - p` has degree below 4096, and `z` is a root of `f - p`.
Or `h = f - p(z) - g (X - z)` is nonzero of degree at most 4096, and the secret `τ` is a root of `h`.
The cases can overlap.
They carry meaning only when an algebraic adversary outputs `f` and `g` over the setup's points, without `τ`.
This reading is the algebraic group model, an assumption.
For other choices, such as the constants that the points represent, the third case only restates the check.
For this single check, no theorem bounds the probability of the second or the third case.
It is not computational binding: no theorem bounds the cost of finding such polynomials without the secret.

`blobBindingAdvantage_le` (`Proofs/Kzg/BlobBindingAdvantage.lean`) bounds an accepted blob batch that contains a commitment different from its blob's computed commitment.
The game samples the setup secret uniformly in `Fr` and gives the algebraic adversary only the public setup powers.
The adversary supplies polynomial representations for the group encodings in its queries and output.
The theorem assumes that each representation of a valid encoding evaluates to its point at the secret, on every run.
This hypothesis stands for the algebraic group model, an assumption; nothing restricts how the adversary computes its representations.
The game rejects final batches above `n` blobs.
With at most `qBlob` individual challenge queries and `qBatch` batch challenge queries by the adversary, the bound is `(qBlob + n) 4095 / r + (qBatch + 1) (n - 1) / r` plus the success probability of `setupSecretReduction`.
Here `r` is the order of `Fr`.
The reduction runs the same experiment once and recovers `τ` from roots of representation differences or the final batch error.
The secret-recovery term is defined on the full setup powers.
Root search is noncomputable in the model; no theorem proves the reduction's running time.
`length_setupSecretCandidates_le_points` (`Proofs/Kzg/BlobBindingReduction.lean`) bounds the roots that the search tests by 4096 for each annotated point, plus 4096 for the final batch error.
No theorem relates the secret-recovery term to the discrete logarithm or the strong Diffie–Hellman problem.
`verifyBlobKzgProofBatch_ok_iff_symbolic` (`Proofs/Kzg/BlobBindingVerifier.lean`) connects the game's scalar acceptance equation to the concrete verifier at its concrete challenges.
`verifyBlobKzgProofBatch_ok_iff_game` specializes it to openings that match the submission, as every successful challenge loop gives: when each blob challenge is the concrete hash of its blob and commitment, those openings are the concrete batch.

`verifyKzgProofBatch_ok_iff_root` (`Proofs/Kzg/BatchBinding.lean`) states when the batch check of openings accepts, as an equivalence.
Let opening `i` have commitment `c_i`, value `y_i`, point `z_i` and proof `w_i`.
For a well-formed setup, its verdict is true exactly when its challenge `r` is a root of `P(X) = sum_i X^i (c_i - y_i - w_i (τ - z_i))`.
`P` is zero exactly when every opening satisfies the identity of the single check.
`verifyKzgProofBatch_exists_ok` shows that the batch check returns a verdict, with no error, when its six arrays have one size.
`verifyCellKzgProofBatchImpl_ok_iff_root` (`Proofs/Kzg/CellBatchBinding.lean`) states the same for the batch check of cells, as an equivalence.
For a well-formed setup and decoded points that represent `c` and `w`, its verdict is true exactly when the challenge is a root.
Let cell `k` have commitment `c_{i_k}` at commitment index `i_k`, proof `w_k`, coset shift `h_k`, and values that interpolate to `I_k` of degree below 64.
Then the challenge is a root of `sum_k X^k (c_{i_k} - I_k(τ) - w_k (τ^64 - h_k^64))`.
That polynomial is zero exactly when every cell is valid.
`prEvent_cellErrorPoly_root_le` bounds the root case by `(q + 1) (n - 1) / r`, for at most `n` cells.
Its game is the one of the openings below.
`verifyCellKzgProofBatchImpl_binding` (`Proofs/Kzg/CellBinding.lean`) is the binding of the batch check of cells.
Let an accepted batch hold two cells of 64 values at one cell index below 128, for commitments that represent one scalar.
Then the values agree, or the challenge is a root of a nonzero error polynomial.
Otherwise a search on the two cells returns a solution of the bilinear strong Diffie–Hellman problem.
The problem is Definition 2.4 of the extended KZG paper.
The solution is `(c, x)` with `x` the element `e(g_1, g_2)^(1 / (τ + c))` of the target group.
The theorem holds in any model of that group, `TargetGroup`.
`TargetGroup.ofPairingLaws` gives the model of the pairing itself.
`Proofs/Kzg/CellVerifier.lean` lifts these three results to the outer check, `verifyCellKzgProofBatch`, which the bindings call.
That check takes one commitment per cell, keeps the first copy of each, and runs the core check.
`verifyCellKzgProofBatch_valid_or_root` checks each cell against its own commitment.
`verifyCellKzgProofBatch_exists_ok` shows that the outer check returns a verdict, with no error, on well-formed input.
The input is well formed when the sizes agree, each cell index is below 128, each cell decodes, and each commitment and proof passes KZG validation.
`verifyCellKzgProofBatch_ok_iff_root` states that this verdict is true exactly when the challenge is a root.
`verifyCellKzgProofBatch_binding` concludes that the two cells are equal as bytes, or one of the two other cases holds.
`prEvent_cellInput_root_le` keeps the bound `(q + 1) (n - 1) / r`, where the adversary outputs the inputs of the outer check.
In `verifyCellKzgProofBatch_valid_or_root`, `verifyCellKzgProofBatch_ok_iff_root`, `verifyCellKzgProofBatch_binding` and `prEvent_cellInput_root_le`, the scalar of a commitment or a proof is a function of its bytes.
Wagner and Zapico, ePrint 2025/1683, Definition 1, write the bilinear strong Diffie–Hellman problem with `1 / (τ - c)`.
`isBsdhSolution_iff_sub` (`Proofs/Kzg/Arsdh.lean`) proves that this form and the one of the extended KZG paper differ only by the sign of `c`.
`IsArsdhSolution` in the same file is the winning condition of adaptive rational strong Diffie–Hellman, Definition 2 there.
These are winning conditions for a fixed secret.
The games below give the advantages.
`multiproof_batching` (`Proofs/Kzg/MultiproofBatching.lean`) proves Lemma 2 of 2025/1683, the multiproof batching lemma, over any field.
In place of the paper's cosets, it assumes that the vanishing polynomial of `S - S_j` is constant on each part `S_j`, and that the parts are nonempty.
`eval_nodal_cellNodes` (`Proofs/Kzg/CellBatching.lean`) is Lemma 1: on cell `i`, the vanishing polynomial of cell `j` takes the value `h_i^64 - h_j^64`.
`cell_multiproof_batching` in the same file applies Lemma 2 to a set of cells.
`code_binding` (`Proofs/Kzg/CodeBinding.lean`) is the deterministic core of Lemma 4, code-binding.
Let exactly 64 cells and one more cell satisfy the scalar equation of a valid cell for one commitment.
Then all 65 cells take the values of one polynomial of degree below 4096.
Otherwise a search returns a bilinear strong Diffie–Hellman solution, or a second search returns a `(4095, 64)`-ARSDH winning solution.
Both searches read only the setup, the commitment, the cells and the proofs.
`Proofs/Kzg/BlobVerifier.lean` lifts the batch check of openings to `verifyBlobKzgProofBatch`, which checks the blobs of a block and of a blob transaction before Fusaka.
`verifyBlobKzgProofBatch_exists_ok` shows that it returns a verdict, with no error, when the sizes match, each blob decodes, and each commitment and proof passes KZG validation.
Assume a well-formed setup and decoded points that represent the scalars `c` and `w` of their bytes.
Then `verifyBlobKzgProofBatch_ok_iff_root` states that this verdict is true exactly when the batch challenge is a root of the error polynomial of the blob batch.
`verifyBlobKzgProofBatch_valid_or_root` assumes the same and splits an accepted batch into two cases.
Every entry satisfies `c_i - y_i = w_i (τ - z_i)` and passes `verifyBlobKzgProof`, or the batch challenge is a root of a nonzero error polynomial.
`prEvent_blobInput_root_le` bounds the root case by `(q + 1) (n - 1) / r`, where the adversary outputs blobs, commitments and proofs.
Its game takes the hash of the batch challenge as a random oracle on the batch of openings that the check builds.
The adversary makes at most `q` queries, and its batch has at most `n` commitments.
In `verifyBlobKzgProofBatch_ok_iff_root`, `verifyBlobKzgProofBatch_valid_or_root` and `prEvent_blobInput_root_le`, the scalar of a commitment or a proof is a function of its bytes.
With `scalarOf`, the discrete logarithm of a validated point, this holds for every input, so it is no extra assumption.
The bound takes any such functions, fixed before the adversary runs.
The bound is tight at `q = 0` and `n = 2` (`exists_blobInput_adversary_prEvent_root_eq`).
There, an adversary that makes no query outputs two blobs whose error polynomial is `1 + X`, and the event has probability exactly `1 / r`.
`verifyBlobKzgProofBatch_of_blobOpeningValid` proves that the check accepts every batch of valid blob openings.
So it accepts the commitments and proofs that `blobToKzgCommitment` and `computeBlobKzgProof` return (`verifyBlobKzgProofBatch_computeBlobKzgProof`).

`Proofs/Kzg/PeerDasGames.lean` states Lemmas 3 and 4 of 2025/1683 as games, and proves them.
In each game, the secret `τ` is uniform in `Fr`.
Every adversary receives only `[τ^i]_1` for `i ≤ 4095` and `[τ^i]_2` for `i ≤ 64`, the input of Definitions 1 and 2 there.
`bsdhAdvantage` and `arsdhAdvantage` are the advantages of Definitions 1 and 2, with `(d, D) = (4095, 64)`.
The verifier of the games builds the full setup from these points and checks each cell alone with `verifyCellKzgProofBatch`.
The error polynomial of one cell is a constant, so `CellOpening.Verifies.valid` needs no random oracle.
The code is the Reed–Solomon code of §3.1 there: a codeword holds the values of a polynomial of degree below 4096 on the 128 cosets.
Each of its cells is the encoding of 64 values that the verifier decodes.
`computeCells_eq_codewordCell` (`Proofs/Kzg/PeerDasCodeword.lean`) shows that the cells that `computeCells` returns for a blob are this codeword.
The polynomial is that of the blob: it has degree below 4096 and takes the values of the blob on the blob domain (`eval_blobPolynomial`).
So openings of cells that `computeCells` returns for one blob never win code-binding (`not_codeBindingWins_of_computeCells`).
That theorem leaves the commitment and the proofs arbitrary, so it says nothing about whether the openings verify.
`positionBindingAdvantage_le` is Lemma 3, position-binding, Definition 4 there.
The advantage of every adversary is at most the BSDH advantage of one reduction.
2025/1683 cites Lemma 3 from Lemma 2 of §3.1 of Wagner and Zapico, ePrint 2024/1362, where the adversary also receives `[τ^i]_2` for `i ≤ 4095`.
`codeBindingAdvantage_le` is Lemma 4, code-binding, Definition 5 there.
The advantage of every adversary is at most the BSDH advantage of one reduction plus the ARSDH advantage of a second.
Each reduction runs the adversary once, then a deterministic search; their running times are not formalized.
The BSDH reductions work in any model of the target group, `TargetGroup`.
That BSDH and ARSDH are hard stays an informal hypothesis: no theorem assumes it, and the bounds hold for every adversary.
An adversary is any Lean function, so without a model of cost, hardness cannot be stated as a Lean hypothesis.
The BSDH advantage is relative to a model of the target group; `TargetGroup.ofPairingLaws` is the model of the real pairing.
These games check one cell per call.
`batchCodeBindingAdvantage_le` (`Proofs/Kzg/PeerDasBatchGames.lean`) states code-binding with one batch check of all opened cells of the commitment.
The hash of the challenge is a random oracle into `Fr` on the inputs of the core check, and the adversary makes at most `q` queries.
That idealises SHA-256 reduced modulo `r`, whose values are not exactly uniform.
The verifier accepts when the batch check returns a verdict and its challenge is a root of the error polynomial of the batch.
At the challenge of the hash, this is the batch check of cells (`CellBatchInput.acceptsAt_challenge_iff`); no theorem relates the two at another challenge.
The bound is the bound of Lemma 4 plus `(q + 1) 127 / r`, the root term of the random-oracle game, for at most 128 distinct cells.
The verifier accepts valid openings with every challenge (`CellBatchInput.acceptsAt_of_cellOpeningValid`).
A client that samples a column checks it in its own batch, with many commitments at one cell index.
That game does not model several such batches, each with its own challenge.
`Proofs/Kzg/PeerDasColumnGames.lean` models them.
There the adversary outputs a commitment, openings and `m` columns, and the verifier makes one oracle query per column.
A column holds an opening when one of its entries has the commitment, the cell and the proof of the opening, at the cell index of the column.
`verifyDataColumnSidecarKzgProofs_eq_verify` (`Consensus/Proofs/DataAvailability/Column.lean`) shows that the client's check of a sidecar is the batch check of such a column.
Let each column have at most `n` cells, and let the adversary make at most `q` queries.
`columnPositionBindingAdvantage_le` bounds position-binding by the advantage of a BSDH reduction plus `(q + m)(n - 1)/r`.
`columnCodeBindingAdvantage_le` bounds code-binding by the advantages of a BSDH reduction and an ARSDH reduction plus the same term.
Before Gloas, the type of the commitments of a sidecar allows at most `MAX_BLOB_COMMITMENTS_PER_BLOCK` of them.
So `n` equal to that limit covers every sidecar whose column the check accepts.
The term bounds the event that the challenge of some column is a root of a nonzero error polynomial (`prEvent_batchesRomRoot_le`).
Otherwise every opening that a column holds verifies alone, and the games of single cells apply.
The verifier accepts a column of cells and proofs of blobs with every challenge (`ColumnBatch.acceptsAt_computeCellsAndKzgProofs`).
`cellOpeningValid_computeCellsAndKzgProofs` (`Proofs/Kzg/HonestCells.lean`) is about the cells and proofs that the code computes for a blob.
Under every well-formed setup, they are valid openings for the commitment of the blob, so also under the setup that the games build.
A valid opening satisfies the scalar equation of a valid cell, with points that pass KZG validation.
`verifyCellKzgProofBatch_of_cellOpeningValid` proves that the batch check of cells accepts every batch of valid openings.
It assumes a well-formed setup, and the commitments of the batch may repeat.
So the batch check accepts the cells and proofs of blobs (`verifyCellKzgProofBatch_computeCellsAndKzgProofs`).
For one cell, `CellOpening.verifies_iff` shows that the verifier of the games accepts an opening exactly when it is valid.
`CellOpening.verifies_computeCellsAndKzgProofs` applies this to the setup that the games build: the openings of a blob verify there.
EthLib does not prove Theorem 1 of 2025/1683, that PeerDAS is a secure data-availability sampling scheme, and does not claim it.
That theorem is informal in the paper.
Its §3.2 explains how it follows from the two lemmas.
The steps are §3.2 of ePrint 2024/1362, for many blobs, and the framework of Hall-Andersen, Simkin and Wagner, ePrint 2023/1079.
2025/1683 does not prove these steps again, and EthLib does not formalize them.

`findSdh_valid_bytes` (`Proofs/Kzg/Binding.lean`) is the evaluation binding of single proofs.
Let the check accept one commitment at one point with two different values.
Then a search over the two openings returns a strong Diffie–Hellman solution for the secret.
It needs a well-formed setup and no model of a hash.

`verifyKzgProofBatch_binding` and `verifyKzgProofBatch_binding_single` (`Proofs/Kzg/BatchBinding.lean`) are the binding of the batch check of openings.
Let an accepted batch open one commitment at one point to two values, or let a single check accept a second value.
Then the values agree, or the search on the two openings returns a strong Diffie–Hellman solution, or the challenge is a root of a nonzero `P`.
They need a well-formed setup.
`prEvent_batchErrorPoly_root_le` (`Proofs/Kzg/BatchChallenge.lean`) bounds the last case.
Its game takes the hash of the challenge as a random oracle on the inputs of the batch.
The adversary makes at most `q` queries to that oracle, then outputs a batch of at most `n` openings.
The verifier then hashes that batch to its challenge.
So the adversary may hash many batches and keep one whose challenge is a root of its `P`.
The challenge is a root of a nonzero `P` with probability at most `(q + 1) (n - 1) / r`.
The one extra query is the verifier's.
The scalars `c_i` and `w_i` are functions of the batch, as the discrete logarithms of its points are.

`checksSufficient_of_subgroupChecks` (`Proofs/Kzg/CeremonyChecks.lean`) is about the ceremony that produced the trusted setup.
It proves that the ceremony's pairing checks force each G1 and G2 point of a contribution to represent the expected power of the trapdoor.
A point represents a scalar when its group element is that multiple of the generator, whatever its coordinates.
It holds under these hypotheses besides the checks themselves:

- Every point is valid and passes the subgroup check of its group.
- `previousTauNonzero`: the previous transcript's tau point is not at infinity.
- `pubkeyNonzero`: the contributor's public key is not at infinity.

`checksSufficient` states the same with the exponents of the points given, in `SubgroupExponents`.

### EVM instructions

Each instruction follows execution-specs, which computes with Python integers.
Lean core defines the same operations on `BitVec`, independently of EthLib.
The theorems in `Arithmetic.lean`, `Comparison.lean` and `Bitwise.lean` of `Execution/Proofs/Evm/Instructions/` prove that the two agree, apart from the divisor 0, where the EVM returns 0.
`sdiv_eq` covers the quotient of -2^255 by -1, the one signed quotient that does not fit in a word, and `bitwiseSar_eq` covers every shift up to 2^256 - 1.
The 38 test cases of EIP-145 pin SHL, SHR and SAR.

No theorem relates the definitions to the Yellow Paper.
The stack, the frame with its program counter and gas meter, and memory are modelled.
So are the instructions that read only the stack, memory, call data, code and return data.
They are in `Execution/Evm/Instructions/StackOnly.lean` and `Execution/Evm/Instructions/MemoryData.lean`.

A program logic over bytecode is in `Execution/Proofs/Evm/Logic/`.
Its first relation covers frames that send no message.
`Reaches S` is the chain of steps of a relation `S`.
`Step` is the relation of the steps that `step` gives, other than requests for a message and errors that abort the run.
`runFrame_of_reaches` proves that a frame that reaches a stopped frame runs to it in `runFrame`, for every bound on the gas of messages and every runner of messages.
`Triple S P Q` says that every frame of `P` reaches a frame of `Q` by the steps of `S`, and `Hoare fork` is `Triple` over `Step`.
`Spec fork P Q` is total correctness for such frames: every frame of `P` reaches a stopped frame of `Q`.
A run that ends out of gas ends in an exceptional halt, so a postcondition of a normal halt needs a precondition with enough gas.
`Logic.At` is a running frame of a code that names every field of the frame, its return data included.
`Logic/Rules.lean` gives rules for the opcodes that push bytes of the code, read call data and the caller, compare, jump, hash memory, read and write storage, and return or revert.
`Logic/Stack.lean` gives rules for POP, SWAP1 to SWAP16, EXP and the opcodes of three operands, at every fork with the one-counter meter.
The rules of `Logic/Rules.lean`, `Logic/Stack.lean`, `Logic/Copy.lean` and `Logic/Log.lean` keep the return data that `At` names.
`Logic/Rules.lean` gives the rule for DUP1 to DUP16, and the rule for DUP1 is its case at depth 0.
Every opcode whose instruction takes one, two or three operands runs by the matching rule, with its instruction from the fork.
DUPN, SWAPN and EXCHANGE of Glamsterdam have no rule yet.
`Logic/NatCode.lean` stores a code of `size` bytes as one natural number.
It states the size of the code, its bytes and the data of a PUSH from that number.
`NatCode.valid_of_walk` proves that a JUMPDEST is a valid jump destination when a walk along the opcodes from position 0 reaches it.
`decide +kernel` checks the walk.
`Logic/Steps.lean` defines the tactic `evm_step`, which applies the rule of the opcode at the program counter and proves the facts about the code by evaluation.
The tactic proves nothing on its own: each step it takes applies one of the rules above, and the kernel checks the result.
`Logic/Fault.lean` gives the postcondition `Faulted` of a frame that halts exceptionally: no output, the error, no gas with the one-counter meter, and the state and substate the frame had.
The caller discards that state; no theorem here states it.
`Logic.invalid` is the rule for a byte that is no opcode at the fork, such as `0xfe` at every fork.
`Logic.jump_invalid` and `Logic.jumpi_invalid` are the rules for a jump to a position that is not a valid jump destination.
`Logic.push_of_readFrame` is the rule for an opcode whose instruction pushes a word that the code, the message, the program counter and the memory fix.
`Logic.callvalue`, `Logic.address`, `Logic.origin`, `Logic.caller`, `Logic.calldatasize`, `Logic.codesize`, `Logic.pc_rule` and `Logic.msize` are its cases.
A size is pushed modulo 2^256, as the instruction pushes it.
`Logic.jumpi_of_eq_zero` is the rule for JUMPI on a condition proved equal to 0.
`Logic.Subroutine` is the specification of a block of code that a caller jumps to with a return address under its arguments.
It holds for every return address that is a JUMPDEST of the code, and every stack under it that leaves room for the block.
`Logic.callSubroutine` proves that a push of the address of the block and a JUMP reach the return address with the results.
It needs both addresses to be JUMPDESTs of the code, and room on the stack below 1024 words.
`Logic.KnownSubroutine` is the same specification over frames that know only the size of memory and some facts.
`Logic.callKnownSubroutine` proves its call, with the push and the jump keeping the size and every fact.
`Logic.stop` is the rule for STOP, which stops the frame with no error and an empty output.
`Logic.stop_of_size_le` is the rule for a frame at or past the end of its code, which stops the same way.
`Logic.sstore_of_account` restates the rule for SSTORE when the current account exists.
It gives a state that holds the new word in the slot, and that the frame reaches.
That state keeps every other slot, the original words and the accounts.
`recordStorageRead_recordStorageRead` proves that recording a storage read twice records it once.
`Logic.insert_insert_getD_self` proves that recording the access of a slot twice records it once.
`Logic.mem_insert_getD_self` proves that a slot whose access is recorded is warm.
`Logic.mem_insert_getD_of_ne` proves that the record leaves every other slot as cold or warm as it was.
`Logic.le_sloadCost` proves that from Berlin, SLOAD costs at least 100.
`Logic.gas_rule` is the rule for GAS, which pushes the gas left after its own price of 2.
`Logic.extcodesize` is the rule for EXTCODESIZE from Berlin to before Glamsterdam.
It charges the prices of EIP-2929, and needs the state to hold the code of the account.
`Logic.extcodesize_of_berlin_le` is the rule for EXTCODESIZE from Berlin, Glamsterdam included, at the price of the fork.
`Logic.mstore8` is the rule for MSTORE8, which writes the lowest byte of a word.
`Logic.mcopy` is the rule for MCOPY from Dencun, which grows memory for both ranges before it reads the source.
`Logic.copyWith` is the rule for a copy of a buffer of the frame to memory, with zeros past its end.
`Logic.calldatacopy` is its case for CALLDATACOPY.
`Logic.codecopy` is its case for CODECOPY.
`Logic.returndatacopy` is the rule for RETURNDATACOPY from Byzantium, for a range that ends within the return data.
`Logic.returndatasize` is the rule for RETURNDATASIZE from Byzantium, which pushes the size of the return data and keeps it.
`Logic.extcodecopy` is the rule for EXTCODECOPY from Berlin to before Glamsterdam.
It charges the prices of EIP-2929 and 3 gas a word, and needs the state to hold the code of the account.
`Logic.extcodecopy_of_berlin_le` is the rule for EXTCODECOPY from Berlin, Glamsterdam included, at the price of the fork.
`Logic.Holds` says that memory covers a range and that the range reads as given bytes.
`Logic.holds_memoryWrite` proves that a write within memory holds the written bytes.
`Logic.Holds.memoryWrite_of_disjoint` proves that such a write keeps every range it does not touch.
`Logic.Holds.memoryExtend` proves that growth keeps every range.
`Logic.Holds.append` proves that two adjacent ranges hold their bytes in order.
`Logic.Holds.left` proves that a range that holds two blocks holds the first from its start.
`Logic.Holds.right` proves that it holds the second after the first.
`Logic.Holds.loadWord` proves that a range that holds the bytes of a word reads as that word.
`Logic.extendMemory_of_le` proves that a range within memory grows nothing and costs nothing.
`Logic.extendMemory_of_lt` proves that a range of some bytes past memory grows it to the rounded end of the range.
It needs a size of memory that is a multiple of 32.
That growth costs the price of the new size minus the price of the old size.
`Logic.size_memoryExtend_extendMemory` proves that memory then has the greater of its old size and that rounded end.
`Logic.Known` is a running frame whose memory is named only by its size, a multiple of 32, and by facts that `Holds` states.
`Logic.Known.of_at` proves that a rule that keeps memory, for every memory, keeps the size and every fact.
`Logic.known_of_write` proves that after a write, memory holds the written fact and every fact apart from the write.
`Logic.Known.join` proves that the facts of two adjacent ranges join into one.
`Logic.mstore_known` gives MSTORE this form, with memory grown by the growth for its size.
`Logic.mstore8_known` gives MSTORE8 this form.
`Logic.mcopy_known` gives MCOPY this form, from Dencun, for a source that is the range of a fact.
`Logic.calldatacopy_known` gives CALLDATACOPY this form.
`Logic.codecopy_known` gives CODECOPY this form.
`Logic.returndatacopy_known` gives RETURNDATACOPY this form, from Byzantium, for a range within the return data.
`Logic.extcodecopy_known` gives EXTCODECOPY this form, from Berlin to before Glamsterdam.
These write rules ask for a range of some bytes.
`Logic.mload_known` proves that MLOAD of the range of a fact with a word pushes that word.
`Logic.return_known` proves that RETURN of the range of a fact returns the bytes of the fact.
`Logic.revert_known` proves the same for REVERT from Byzantium.
`memoryReadBytes_memoryWrite_eq_append` proves that a read that ends where a write ends gives the bytes before the write, then the value.
`Logic.staticcallWith` is the rule for STATICCALL from Berlin to before Glamsterdam.
Its message carries no value and is static.
`Logic.staticcall` is its case with empty ranges of input and output.
`Logic.callStep_child` gives the step of a call that sends no value of its own, for each kind of call.
`Logic.callKindWith` is the rule for such a call from Berlin to before Glamsterdam.
After the call, the return data is the output of the frame that ends the message.
`Logic.delegatecallWith` is the rule for DELEGATECALL from Berlin to before Glamsterdam.
Its message runs the code of the address on the current account, with the sender and the value of the current message.
`Logic.callcodeWith` is the rule for CALLCODE with no value from Berlin to before Glamsterdam.
Its message runs the code of the address on the current account, as its sender.
`Logic.createStep_child` gives the step of CREATE or CREATE2 that sends its message, from Berlin to before Glamsterdam.
It needs the new address to hold no code and a nonce of 0, as EIP-684 asks.
`Logic.createKindWith` is the rule for such a creation, under an assumption on the frame that ends it.
`Logic.createWith` is its case for CREATE.
`Logic.create2With` is its case for CREATE2.
`Logic.resumeCreate_eq` proves that the creator pushes the new address, or 0 when the frame that ends the creation has an error.
After a creation with no error the return data is empty, and otherwise it is the output of that frame.
`Logic.createMessageGas_of_tangerineWhistle` proves that from Tangerine Whistle a creation passes on all but one 64th of the gas left.
`Logic.depositCode_of_ok` proves that from Berlin to before Glamsterdam a frame with no error deposits its output as code, at 200 gas a byte.
It needs the output to hold at most 24576 bytes (EIP-170), and from London not to start with `0xEF` (EIP-3541).
`Logic.depositCode_of_prefix` proves that from London an output that starts with `0xEF` fails with all the gas taken, the state put back and no output.
`Logic.depositCode_of_outOfGas` proves that an output too long or too dear fails the same way, out of gas.
`Logic.processCreateMessage_eq_ok` proves that a creation with no value and no precompile ends as its init code ends, then deposits.
`Logic.meets_of_spec_create` proves that the runner of the interpreter meets `CreatesAs` for a specification of the init code.
`Logic.running_eq_false_of_sstore_of_isStatic` proves that in a static frame, a step at SSTORE stops the frame.
`sstoreStep_halts` proves that SSTORE never completes in a static frame, or when the current address has no account.
In that second case the write fails and aborts the run.
`Logic.running_eq_false_of_log_of_isStatic` proves the same for LOG0 to LOG4.
`memoryReadBytes_memoryWrite_of_disjoint` proves that a write within memory leaves a read of a disjoint range unchanged.
`memoryReadBytes_memoryWrite_memoryWrite` proves that a read across two adjacent writes gives both values in order.
`memoryWrite_comm_of_disjoint` proves that two writes within memory to disjoint ranges commute.
`memoryReadBytes_memoryWrite_memoryWrite_rev` proves the same read when the higher write comes first.
From Berlin, the rule for SLOAD takes as a hypothesis whether the slot is cold, and charges 2100 or 100 by EIP-2929.
`Logic.sstore` is the rule for SSTORE from Berlin, with one counter of gas, in a frame that may change the state and holds more than 2300 gas.
It charges `sstoreTotalCost`, the price and the state gas of the write, ignores the refill of state gas, and adds `sstoreRefund` to the refund counter, from the original, current and new words and whether the slot is cold.
It takes the state that the write gives as a hypothesis, since the write needs the account of the current address.
`Logic.log` (`Logic/Log.lean`) is the rule for LOG0 to LOG4, at every fork with the one-counter meter, in a frame that may change the state.
It appends one log of the current address with the topics and the range of memory.
It pays 375, 8 for each byte, 375 for each topic and the growth of memory.
It says nothing of the order of the logs of several frames, or of logs that a revert drops.
`Logic.branchTable` (`Logic/Branch.lean`) is the rule for a table of entries that branches on the top word of the stack.
It holds at every fork with the one-counter meter.
Each entry is DUP1, a push of a key of `n` bytes, EQ, a push of a destination of `m` bytes, and JUMPI.
The run jumps to the destination of the first entry whose key is the word, or goes on past the table.
It pays 22 gas for each entry it tests, and needs each destination to be a valid destination of a jump.
`Triple.loop` (`Logic/Loop.lean`) proves a loop from an invariant for each value of a natural measure.
A run of the loop then ends by the measure, not by the gas.
`Triple.loop_gas` proves a loop whose invariant carries the gas, with a price for each run that may depend on the runs left.
The loop then needs the sum of those prices and the price of its exit.
`Logic.holds_empty` proves that memory holds no bytes from an offset within it.
`Logic.Stored` is a running frame that knows ranges of memory, the facts of some slots, and the refund counter.
A fact of a slot gives its account, its key, its word before the transaction, its word now, and whether it is warm.
`Logic.Agrees` says that a state and its accessed keys agree with a base outside a list of slots and two lists of addresses.
There each word reads as in the base state, and each slot is warm exactly when the base keys hold it.
The words before the transaction and the block are those of the base state.
Outside the addresses of both lists each account is that of the base state.
Outside the second list, of remade addresses, an account exists exactly when it does in the base state.
There it also has the nonce, the code hash and the code of the base state.
A `Stored` frame agrees with its base outside the slots of its facts, and at every address.
`Logic.Agrees.trans` proves that agreement composes, outside both lists of slots and both lists of addresses of each kind.
`Logic.Agrees.getAccount` proves that outside both lists of addresses an account is that of the base state.
`Logic.Stored.of_known` proves that a rule that keeps the state and the substate keeps every fact.
`Logic.Stored.of_at` proves the same for a rule that also keeps memory.
`Logic.sload_stored` proves that from Berlin, SLOAD of the key of a fact of the frame's account pushes its word now.
It makes the slot warm.
`Logic.sstore_stored` proves that from Berlin to before Glamsterdam, SSTORE to the key of such a fact writes it and makes it warm.
It needs a frame that may change the state, more than 2300 gas, and the account of the frame in the base state.
It pays the price of EIP-2200 with the prices of EIP-2929 from the facts of the slot, and adds the refund of the write.
`Logic.StoppedStored.of_known` proves that a rule that halts and keeps the state and the substate keeps every fact.
`Logic.stop_stored` proves that STOP keeps every fact.
`Logic.returndatasize_stored` proves that from Byzantium RETURNDATASIZE pushes the size of the return data and keeps every fact.
`Logic.returndatacopy_stored` proves that from Byzantium RETURNDATACOPY of a range within the return data writes it as a fact of memory.
These frames say nothing of the logs, the accessed addresses and the other fields of the substate.
`Logic.AccountFact` gives the address, the nonce, the balance and the code of an account that exists.
`Logic.Change` names the slots that a message may touch and the addresses whose balances it may move.
It also names the addresses whose accounts it may remake, by a creation or a change of a nonce or a code.
It also names the facts of slots, the balances, the facts of accounts and the refund that the message gives on success.
`Logic.Effect` (`Logic/Effect.lean`) is the effect of a message on storage and accounts, from the frame that sends it.
Outside the slots and the addresses of its change, the state after agrees with the state before.
A failed message touches no slot, moves no balance and remakes no account.
A message that succeeds gives the facts of some slots, some balances and some accounts, and adds a refund.
`Logic.effects_rollbackOnError` proves that a callee whose stopped frame agrees with the state of its caller outside a change has its effect after the rollback.
`Logic.agrees_moveEther` proves that a move of a value that is not 0 between two accounts changes only their balances.
It needs the two accounts to exist and the sender to have a nonce or a code.
`Logic.agrees_modifyState` proves that a change of one account that keeps it alive changes only that account and keeps every code.
`Logic.CallMessage` is the message that a call sends when it sends no value of its own, by the kind of the call.
`Logic.callKind_stored` proves that from Berlin to before Glamsterdam, such a call keeps the facts of a `Stored` frame.
It keeps each fact of a slot that the effect of the callee does not touch.
It needs an input range that a fact of memory holds, an output range within memory, and the gas of a cold call.
It also needs an assumption that gives the effect of each frame that ends the message.
The assumption also gives the output of such a frame when it succeeds.
On success the frame gains the facts and the refund of the effect, and that output as its return data.
It also gains the fact of the start of that output in the output range.
On failure it keeps its facts of slots, and the assumption may rule a failure out.
The assumption may also describe the output of a frame that ends with an error, such as a revert.
On failure the return data of the frame is such an output.
Either way it keeps each fact of memory apart from the output range.
Its new base agrees with the old one outside the touched slots and the slots of the facts.
`Logic.call_stored` proves this for CALL with no value.
`Logic.staticcall_stored` proves this for STATICCALL.
`Logic.delegatecall_stored` proves this for DELEGATECALL.
`Logic.callcode_stored` proves this for CALLCODE with no value.
`Logic.ValueMessage` is the message that CALL sends with a value.
`Logic.callValue_stored` proves that from Berlin to before Glamsterdam, CALL with a value that is not 0 keeps the facts of a `Stored` frame in the same way.
It needs a frame that may change the state, and its account must hold the value in the base state.
It needs the gas of a cold call, 9000 for the value, and 25000 more when the callee is dead in the base state.
On success the new base also holds the balances and the facts of accounts of the effect.
The new base agrees with the old one outside the addresses whose balances the effect moves or whose accounts it remakes, too.
`Logic.CreateMessage` is the message that a creation sends, to run its init code at the new address.
`Logic.AfterCreate` is the frame after a creation from a `Stored` frame.
`Logic.createKind_stored` proves that from Berlin to before Glamsterdam, CREATE or CREATE2 keeps the facts of a `Stored` frame.
It needs init code that a fact of memory holds, and a frame that may change the state.
The creator must hold the value in the base state.
Its nonce in the base state must not be the greatest, and its depth must leave room for one more frame.
From Shanghai the init code must hold at most the greatest size of EIP-3860.
It needs the new address from the base state to hold no code and a nonce of 0, and the price of the creation.
It also needs an assumption that gives the effect of each frame that ends the creation.
On success the frame pushes the new address, gains the facts and the refund of the effect, and its return data is empty.
On success the new base holds the balances and the facts of accounts of the effect.
On failure the frame pushes 0 and keeps its facts of slots, and the assumption may rule a failure out.
Its return data is then an output that the assumption allows for a frame that ends with an error.
The new base gives the creator its grown nonce, unless the effect remakes the creator.
Its new base agrees with the old one outside the touched slots, the moved and remade addresses, and the creator.
`Logic.create_stored` proves this for CREATE.
`Logic.create2_stored` proves this for CREATE2.
`Logic.nonce_of_shape` proves that an account with the nonce and the code hash of an account that exists has its nonce.
`Entered` (`Execution/Proofs/Evm/Call/Run.lean`) gives the state and the substate that the frame of a message starts from, after the move of its value.
`Entered.of_not_transfers` proves that a message that moves no value starts from the start state and the substate of its caller.
`Logic.meets_runsAll` proves that the runner of the interpreter meets the specifications of a family of codes that call each other, at every bound.
Each specification is a triple under the assumption that the whole family runs as specified, so a callee may call its caller back.
Each specification holds from every frame that a message with its code enters, so a message may move a value.
The proof is an induction on the bound on the gas of messages.
`HoareUnder.of_exists` proves a triple from a precondition that gives a witness, with a triple for each witness.
`StepBy` (`Logic/Message.lean`) adds the steps that send a message, which a runner of messages ends with a frame.
`runFrame_eq_of_reaches` proves that `runFrame` runs a frame as it runs each frame that it reaches.
It holds for every relation whose steps `runFrame` runs alike at both ends, as `Step` and `StepBy` do.
A runner can also fail on a message, and then `runFrame` fails with the error of the runner.
`Meets callee runChild` says that each frame that the runner gives meets the assumption `callee`.
It also says that the runner fails only with an error that aborts the run, and asks nothing more of such a message.
`meets_process` proves that the runner of the code of a message meets the assumption that always holds, for every bound.
It rests on `aborts_of_process_eq_error` (`Execution/Proofs/Evm/Call/MessageCall.lean`), which proves that a message and a creation fail only with an error that aborts.
`meets_of_spec` (`Logic/Callee.lean`) proves that this runner meets a stronger assumption, `RunsAs`, for a callee code with a specification.
The specification is one with no message, from the frame that a message with that code starts, so the callee sends no message itself.
The assumption covers a message with that code and a target, with no value and no precompile.
Its frame starts from the state of the caller, with its target touched before Paris, as `processMessage` does.
The frame that ends the message is a stopped frame of the specification, rolled back on a failure.
`meets_of_specUnder` proves the same for a callee that sends messages, from a triple under an assumption `A` on its own messages.
It asks that the runner meet `A` at every bound.
`meets_of_spec` is its case with the assumption that always holds.
`processMessage_map_val` proves that a message that moves no value and has no precompile ends as the run of its code ends, for every lawful meter.
`processMessage_map_val_value` proves the same for a message that moves value, from the state after the transfer.
No theorem yet proves that this runner meets an assumption for a callee that sends value or is a precompile.
No theorem reasons about a callee that calls back into its caller and depends on the state that the caller wrote.
`SpecUnder fork callee P Q` holds under every runner that meets `callee`, and for every bound that holds the gas of the frame.
From every frame of `P`, the steps of `StepBy` reach a stopped frame of `Q`, or a frame whose runner fails on its message.
So `SpecUnder.runFrame` concludes that `runFrame` returns a stopped frame of `Q`, or fails with an error that aborts.
`hoareUnder_iff_triple` states each triple under an assumption as a `Triple` over `StepBy` under each runner that meets it, so the two share their rules.
The code that a message runs is arbitrary and may call the caller again.
So the assumption is all that a triple says about a frame that ends a message, and about the state after it.
`Logic.callWith` (`Logic/Call.lean`) is the rule for CALL with no value, a range of input and a range of output.
It pays the growth of memory for both ranges, and the message carries the bytes of the input range.
The caller writes the start of the output of the callee at the start of the output range, as far as both go.
`Logic.call` is its case with empty ranges.
It holds from Berlin to before Glamsterdam, with the one-counter meter.
It pays 2600 or 100 for the access to the address, by EIP-2929.
It passes on at most all but one 64th of the gas left, by EIP-150.
Its postcondition gives the state and substate that the frame that ends the message gives, and nothing more.
`meets_process_noCode` proves that the runner of the interpreter meets one more assumption.
That assumption says that a message with no code, to an account that is no precompile, ends with no error.
`Logic.callWith` and `Logic.call` also state that the message is static when the frame is.
`Logic.callValue` is the rule for CALL with a value that is not 0, from Berlin to before Glamsterdam.
The frame must be one that may change the state.
It pays the access of EIP-2929, 9000 for the value, 25000 more when the callee is dead by EIP-161, and the growth of memory.
The message gets the gas that EIP-150 allows and the stipend of 2300, and carries the value.
The message is not static.
`Logic.callValueLow` is the rule for such a CALL when the current account holds less than the value.
It sends no message, pushes 0, and gives back the gas it would pass on with the stipend.
Its return data is then empty.
`meets_paidNoCode` (`Logic/Callee.lean`) proves that the runner ends a message with value to no code with no error.
Its frame ends in the state that the move of the value gives.
No rule covers CREATE, DELEGATECALL or STATICCALL.

A triple under an assumption asks the runner to fail only with an error that aborts.
It does not say on which message the runner fails.
`HoareOn fork callee S P Q` (`Logic/FailsOn.lean`) asks nothing of the errors of the runner.
Instead it names the messages on which a run may stop because the runner fails.
`S` is a condition on the frame that the step hands to the runner, after it pays for the message, and on the message.
`MeetsOk callee runChild` says that each frame that the runner gives meets `callee`, and lets the runner fail on every message with an error of any kind.
`HoareOn` holds under every runner that meets `callee` in this sense, and for every bound that holds the gas of the frame.
From every frame of `P`, the steps of `StepBy` reach a frame of `Q`.
Or they reach a frame that sends a message of `S`, and the runner fails on that message.
`SpecOn` is its case whose postcondition is a stopped frame.
`hoareOn_true_iff` proves that `HoareOn` with the set of every message is `HoareUnder`.
`HoareUnder.toOn` replaces each error of a runner with one that aborts, which keeps the steps and the frames on which the runner fails.
With `HoareOn.toUnder` it gives `hoareOn_true_iff`.
So a triple under an assumption is the case of the full set, and a smaller set gives a stronger triple.
`HoareOn.toUnder` and `SpecOn.toUnder` prove that each such triple is a triple under the same assumption, for every set.
`hoareOn_iff_triple` proves that `HoareOn` is a `Triple` over the steps under each runner, as `hoareUnder_iff_triple` does with no set.
The rules of `HoareUnder` hold for `HoareOn` with the same set: `of_hoare`, `of_child`, `assumption`, `of_exists`, `seq`, `consequence`, `cases`, `loop_lt` and `loop`.
`HoareOn.of_child` asks that the message be in `S`.
`HoareOn.mono` and `SpecOn.mono` prove that a larger set of messages keeps a triple.
`SpecOn.seq`, `SpecOn.consequence` and `SpecOn.of_spec` prove the rules of sequence, consequence and no message for a triple to a stopped frame.
`SpecOn.runFrame` proves that `runFrame` returns a stopped frame of `Q`, or fails.
When it fails, a frame that the steps reach sends a message of `S`, and the runner fails on it.
Then `runFrame` fails with the same error.
`HoareOn.runFrame_of_ok` proves that a run that succeeds through such a triple goes on from a frame of `Q`, for a runner that meets the assumption.
That run ends where the run from that frame ends.
`Hoare.runFrame_of_ok` proves the same for a triple over the steps, under every runner.

From Pectra, a call to an account whose code is an EIP-7702 delegation indicator runs the code of the delegate.
`Logic.Routes fork state c route` (`Logic/Route.lean`) says which code a call to an account with the code `c` runs.
The route is the code of the address itself, or a delegate with the code that the state holds for it.
`Logic.Routes.congr` proves that the route depends on the state only through the code at each address.
`Logic.Routes.recordAccountRead` proves that a recorded read leaves the route unchanged.
`Logic.CallSends` gives the frame and the message of a call that sends no value of its own, along a route.
The message runs the code of the route; when delegated, its code address is the delegate and it runs no precompile.
`Logic.callStep_child_of_routes` proves that the step of such a call sends that message, for each kind of call.
It holds at every fork from Berlin, with the one-counter meter.
The call pays the access to the address, the access to the delegate, the growth of memory, and the gas it passes on.
`Logic.callKindRoute` proves the rule for such a call as a `HoareOn` triple.
Its set holds only the message of the call, so a run may stop because the runner fails only on that message.
`Logic.callRoute` proves its case for CALL.
Unlike `Logic.callWith`, neither rule asks that the code be no delegation, or that the fork come before Glamsterdam.
`Logic.callStep_child` and `Logic.callKindWith` are their cases with no delegation, so the step has one proof.
`Logic.callStep_fails_of_routes` (`Logic/CallSteps.lean`) proves that such a call fails, or halts the frame with an error, when its gas is below its price before the gas it passes on.
That price is the access to the address, the access to the delegate if any, and the growth of memory.
`Logic.callStep_deep_of_routes` proves that such a call at the greatest depth, with at least that price in gas, sends no message, pays only that price and pushes 0.
`Logic.callStep_fails_of_missing` proves that from Pectra such a call fails when the lookup of the code of the delegate fails.
Instead of failing, the step may halt the frame with an error.
Each holds for every kind of call with the one-counter meter: the first two from Berlin, the third from Pectra.

A triple says about the state after a message only what its assumption says, so a proof needs an assumption on what the callee does.
`Logic.KeepsOn runChild S R` (`Logic/Keeps.lean`) says that each message of `S` that the runner ends with no error keeps the relation `R`.
It is the assumption `Logic.MeetsOk` of a triple, for that condition on the frame that ends the message.
`R` holds from the state of the frame that sends the message to the state of the frame that ends it.
`Logic.KeepsOn.mono` proves that a smaller set of messages and a weaker relation keep the assumption.
`Logic.ReadsAs tx S` says that `tx` has the account, the storage and the transient storage of `S` at every address, and its code at every hash.
It leaves free the block before the transaction, the created accounts, the wiped storage and the read records.
`Logic.ReadsAs.recordAccountRead` proves that a record of an account read keeps this relation.
`Logic.ReadsAs.recordStorageRead` proves the same for a record of a storage read.
`Logic.ReadsAs.routeState` proves the same for the state once a call follows a route.
`Logic.Routes.of_readsAs` proves that a state that reads as `S` gives each code the route that `S` gives it.
`Logic.SentVia message S to` names the CALLs with no value from the current account of `message` to `to`, from a frame that reads as `S`.
Each such call runs the code that `to` holds in `S`, along its route, with any data, any gas and any reservoir.
`Logic.CallSends.sentVia` proves that the message of a CALL with no value along a route is such a call, via the state before the call.

`StepRules fork R` (`Execution/Proofs/Evm/Call/StepRules.lean`) lists the rules for a transitive relation `R` of two frames.
`R` must hold of each step that keeps the state up to the records of reads.
It must also hold of each write of storage, transient storage, a log or SELFDESTRUCT, of the rise of a nonce, and of a child taken in by its caller.
`StepRules.step` proves that such a relation holds of every successful step, given it for the frame that ends each message sent.
`StepRules.runFrame` proves the relation for a successful run of a frame.
`StepRules.processMessage` turns it into a fact of every call and creation, by induction on the gas of the message.

The block of a transaction state is the state before the block, with the writes of the block so far.
A rollback restores the storage of a snapshot only when both states have the same block.
`parentResult_step` (`Execution/Proofs/Evm/Call/Parent.lean`) proves that every successful step keeps the block of the state, at every fork.
A step that sends a message keeps it once the frame that ends the message has the block of its caller.
`KeepsParent runChild` says that the runner ends each message that succeeds with the block of the frame that sends it.
`parent_runFrame` proves that a successful run of a frame keeps the block, under a runner that meets `KeepsParent`.
`parent_processMessage` proves that a successful call keeps the block of the state it is sent from, at every fork.
`parent_processCreateMessage` proves the same for a successful creation.
`keepsParent_processRunner` (`Logic/Message.lean`) proves that the runner of the code of a message meets `KeepsParent`, for every bound.
`KeepsParent.keepsOn` (`Logic/Keeps.lean`) proves that such a runner keeps the block on every set of messages of `Logic.KeepsOn`.
`processMessage_sameOutside_of_error` proves that a call that ends with an error reads as the state it is sent from at every address, at every fork.
That covers the account, the storage and the transient storage, and `getStorage_processMessage_of_error` states it for one storage word.

From Cancun, `deletesCreated_processMessage` (`Execution/Proofs/Evm/Call/ToDelete.lean`) proves that a call marks for deletion only accounts already marked or created in the transaction.
From Paris, `touchedAccounts_processMessage` (`Execution/Proofs/Evm/Call/Touched.lean`) proves that a call touches no account beyond those of its substate.
`sameOutside_deleteAccounts` (`Execution/Proofs/Transactions/Deletion.lean`) proves that the deletions at the end of a transaction change only its accounts to delete and its touched accounts.
`sameOutside_deleteAccounts_of_dencun` proves that, from Cancun, the deletions after the settlement of gas change only the created accounts of the settled state, when its message starts from the substate of a transaction.
`runTransaction_deletes_created` states this for the run of a transaction, with each of its steps named; there the created accounts are those the transaction created.
Before Glamsterdam, `runTransaction_removes_marked` (`Execution/Proofs/Transactions/Deletion.lean`) proves that each account marked for deletion by a frame that no revert undoes is absent after the transaction, when its message ends without an error.
Before Cancun, `runTransaction_removes_selfdestructed` states it for the account that runs SELFDESTRUCT in such a frame.
`Visits` (`Execution/Proofs/Evm/Logic/Marks.lean`) names those frames: the frames that a run reaches, and those of the code of each message on the way that ends without an error.
`toDeleteLe_of_visits` proves that the frame that ends such a run, without an error, marks every account that a visited frame marks.

The facts of `Logic/GasMono.lean` and `Logic/LessGas.lean` are for the one-counter meter, the meter of every fork before Glamsterdam.
`Logic.addGas k` adds `k` to the gas of a frame.
`Logic.RunMono` says that an instruction, on each frame, fails or gives a frame `b`.
On that frame with `k` more gas, it then gives `b` with `k` more gas.
A frame that reverts counts as failed, so these facts say nothing of the gas of a run that reverts.
`Logic.GasMono` says the same of the step from every frame with less gas than a frame.
`Logic.HoareG` and `Logic.SpecG` are triples over the steps of `Step` from frames that are `GasMono`.
`Logic.HoareG.toHoare` proves that such a triple is a triple over `Step`.
`Logic.At.ruleG` is the rule of an opcode whose instruction is `RunMono`.
`Logic.invalidG` (`Logic/Fault.lean`) is the rule for a byte that is no opcode at the fork, and `Logic.invalid` follows from it.
`Logic.reaches_low` proves that these steps from a frame `l` with `k` more gas follow the run of `l`, when that run ends with no error.
`Logic.low_of_reaches` proves that a stopped frame these steps reach is then the end of the run of `l`, with `k` more gas.
Both hold for every bound on the gas of messages and every runner of messages.
`Logic.SpecG.low` proves that a specification from a frame with `k` more gas then holds of the end of the run with `k` more gas.
`Logic.SpecG.halted` proves that the run then ends in the normal halt of a specification from a frame of `At`, with `k` less gas.
`Logic.SpecG.not_ok` proves that the run does not end with no error when every frame of the postcondition has an error.
`Logic.halted_of_specG` takes a specification over `Logic.StepG` to a normal halt that pays `cost`, from a frame of `At` with every gas from some bound on.
The specification needs to hold only with at least `cost` gas.
It proves that every run of that frame that succeeds, with any gas, had at least `cost` gas.
That run ends in that halt with exactly `cost` less gas.
`Logic.no_ok_of_specG` proves that every frame that the loop runs a frame of `At` to, with any gas, has an error.
It assumes a specification over `Logic.StepG` to frames with an error, with every gas from some bound on.
`Logic.Stuck` is a running frame from which the step fails, and from it with any less gas.
`Logic.not_ok_of_reaches` proves that a run does not end with no error when these steps from the frame with `k` more gas reach a stuck frame.
`Logic.no_ok_stuck` proves the same for a frame of `At` that reaches a stuck frame with every gas from some bound on.
`Logic.no_ok_stuck_at` proves the same for a frame of `At` that reaches a stuck frame with its own gas.
GAS has no rule of this kind, since it pushes the gas left, and no theorem here covers a step that sends a message.
`Logic.At.ruleG_of_follows` is the rule of an opcode whose instruction, run on each frame of the rule with less gas, fails or gives its frame with less gas.
Each instruction that `Logic/RunMono.lean` covers is `RunMono`, such as `Logic.runMono_sstore` for SSTORE.
`Logic.follows_readFrame` proves that an instruction that pushes a word of the frame, run with less gas, fails or gives its frame with less gas.
It needs the word not to depend on the gas.
The opcode rules of `Logic/Rules.lean`, `Logic/Stack.lean` and `Logic/Log.lean` are proved over the steps from frames that are `GasMono`, such as `Logic.calldataloadG`.
Each such rule has the hypotheses and the conclusion of the rule over `Step` of the same opcode, which follows from it by `Logic.HoareG.toHoare` or `Logic.SpecG.toSpec`.
Of the opcode rules there, the one for GAS has no such form, since it pushes the gas left.
Those for EXTCODESIZE, a frame past the end of its code and `Logic.sstore_of_account` have none yet.
`Logic.branchTable` has no such form yet.
`Logic.At.stuck` proves that a frame is stuck at an opcode whose instruction fails on every frame with the same message, stack and state, and at most the same gas.
`Logic.sstore_stuck` proves that SSTORE is stuck in a static frame, or when the current address has no account.
`Logic.sstore_low_stuck` proves that from Istanbul SSTORE is stuck with 2300 gas or less, by EIP-2200.

The facts of `Logic/NoAbort.lean` are for the one-counter meter too.
`Logic.NoAbort` says that a result is no error that aborts the run.
An error of the state aborts, and so do an opcode with no instruction, an encoding error and a fork with no specification.
Each instruction of `Logic/RunMono.lean` except SSTORE never aborts, such as `Logic.noAbort_log` for LOG0 to LOG4.
`Logic.NoAbortLow` says that the step from every frame with less gas than a frame does not abort.
`Logic.HoareGA` and `Logic.SpecGA` are triples over the steps of `Logic.StepG` from frames that are `Logic.NoAbortLow`.
`Logic.HoareGA.toG` proves that such a triple is a triple over `Logic.StepG`.
`Logic.At.ruleGA_of_follows` is the rule of an opcode whose instruction never aborts.
Run with less gas on each frame of the rule, the instruction must fail or give its frame with less gas.
`Logic.At.ruleGA` is the same rule for an instruction that is `RunMono`.
Each opcode rule over `Logic.StepG` whose instruction never aborts is proved over `Logic.StepGA` first, such as `Logic.calldataloadGA`.
The rule over `Logic.StepG` of the same opcode follows from it by `Logic.HoareGA.toG` or `Logic.SpecGA.toG`.
`Logic.no_error_of_reaches` proves that the loop runs a frame `l` to a frame, never to an error.
It assumes that these steps reach a stopped frame from `l` with `k` more gas.
`Logic.no_error` proves that the loop runs a frame of `At` to a frame, with any gas.
It assumes a specification over these steps from that frame with every gas from some bound on.
Both hold for every bound on the gas of messages and every runner of messages.

`Logic/RunsOk.lean` says when a run succeeds, that is when the loop ends its frame in a frame with no error.
`Logic.RunsOk` is that condition, for any lawful meter.
`Logic.Spec.runsOk` proves that a specification to frames with no error gives a run that succeeds, under every runner.
`Logic.SpecOn.runsOk` proves the same for a specification whose runner may fail only on the messages that it names.
It assumes a runner that never fails on those messages.
`Logic.not_runsOk_of_lt` proves that no run with less gas than `cost` succeeds, from a specification to a halt that pays `cost`, as above.

### System contracts

The four modules under `Execution/Proofs/Blocks/SystemCall/` for beacon roots, historical block hashes, withdrawal requests and consolidation requests prove the effects of their deployed bytecode.
Their `systemCall_set` and `systemCall_dequeue` theorems hold from each contract's activation, with the gas meter of the fork, including the state gas meter from Glamsterdam.
They require the specified bytecode at the contract's address.
The queue theorems assume bounds on the storage counters, and the history theorem requires a block number from 1 to below `2^256`.

`Logic.Reaches.followsMeter` lifts a normal one-counter run to the state gas meter when its execution gas initially covers that counter.
The counter pays execution gas and state gas and ignores refills, so it gives a conservative budget.
`Logic.SupportedCode` checks each opcode, skipping PUSH data, against a fixed list of instructions.
The list leaves out GAS and every instruction that sends a message.
The lifted run has the same fields outside its meter, including its state and output.
`SystemContract.systemCall_of_writesStorage` applies this result to the actual system-call runner and its initial reservoir.

### SHA-256 precompile

The precompile reuses the SHA-256 of the cryptography layer, so its theorems are about the gas and the failure.
`sha256_eq_ok_iff` and `sha256_eq_error_iff` (`Execution/Proofs/Evm/Precompiles/Sha256.lean`) prove that a call succeeds exactly when the gas covers `60 + 12 * ceil(len / 32)`, and then returns the digest of the whole call data.
`le_wordCount` and `wordCount_le` prove that the word count is the least number of 32-byte words that covers the call data.
`sha256_ok_eq_spec` carries `hash_eq_spec` over to the output, so the output is the FIPS 180-4 hash when the call data is shorter than 2^61 bytes.
`sha256_ok_eq_spec_of_gas` drops that hypothesis for every call that succeeds with less than `60 + 12 * 2^56` gas.
`gasCost_lt_two_pow_64` proves that the price of call data shorter than 2^63 bytes fits in the 64 bits the C export returns.

No theorem relates the module to the execution-specs code it follows, which calls `hashlib.sha256`.

### MODEXP

These theorems state agreement with EIP-198 and EIP-7823.
`compute_eq_pow_mod` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) proves that the output is `BASE ^ EXPONENT mod MODULUS`, or 0 for a zero modulus.
It rests on `powMod_eq` (`Execution/Proofs/Evm/PowMod.lean`), which proves that the square-and-multiply loop equals `b ^ e % m`.
`modexp_outOfGas` and `modexp_ok` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) prove that, with every length within the EIP-7823 bound, a call fails exactly when the gas is below the price.
`modexp_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) proves that a call succeeds exactly when, from Fusaka, every length is within the EIP-7823 bound and the gas covers the price, and that it then returns the computed output.
`modexp_eq_error_iff` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) proves that a call fails exactly on the first oversized length, from Fusaka, in the order base, exponent, modulus, or else on gas below the price.

No theorem relates the module to the execution-specs code it follows.

### BLAKE2F

The theorems pin down the input format exactly, and state the compression function F against a model of RFC 7693.
`output_invalidInputLength`, `output_invalidFlag` and `output_ok` (`Execution/Proofs/Evm/Precompiles/Blake2f.lean`) prove that a call fails exactly when the input is not 213 bytes long, or its flag byte is neither `0` nor `1`.
Otherwise it returns `compute` of the input, which decodes the fields and runs F of RFC 7693 on them.
`blake2f_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/Blake2f.lean`) proves that a call succeeds exactly on a 213-byte input with enough gas and a flag byte of `0` or `1`, returning `compute` of the input with that flag.
`readWord_toNat`, `readRounds_toNat` and `writeState_word` state the encoding of EIP-152 for every input: the rounds field big-endian, every word little-endian, and the output in the encoding of the input.

`roundsFrom_bijective` (`Cryptography/Proofs/Hash/Blake2b.lean`) proves that the rounds of F permute the work vector.
The statement holds for every round count, message block and starting round.

`compress_toBitVec` (`Cryptography/Proofs/Hash/Blake2b.lean`) proves that F, read word by word as 64-bit vectors, is the F of a model of RFC 7693 §3.1 and §3.2.
The statement holds for every round count, state, message block, offset counter and flag.
The model rotates 64-bit vectors, and takes the offset counter as one 128-bit vector whose high word is `t1`.
It shares the IV and the message schedule with the code.
`IV_sqrt` derives the IV from square roots, and `SIGMA_perm` checks only that each row of the schedule is a permutation.

The output of F is also checked by the Python tests (`bindings/python/tests/precompile/test_blake2f.py`).
They run test vectors 0 to 7 of EIP-152, and read the rounds field of test vector 8.
They also run one full block of the BLAKE2 test vectors, and one call that sets `t1`.
Test vector 8 asks for `2^32 - 1` rounds, so no test checks its output.

### ECRECOVER

The ECRECOVER theorems rest on the secp256k1 ones, and all three are in `Execution/Proofs/Evm/Precompiles/Ecrecover.lean`.
`output_sign` proves that a signature made with a private key returns that key's address.
`output_verify` proves that a nonempty output is the address of a key that verifies the signature.
`output_of_verify` proves that every key that verifies a signature has its address returned for `v = 27` or `v = 28`, when `r + n >= p`.

No theorem relates the module to the execution-specs code it follows, which calls a C library to recover the key.

### P256VERIFY

The P256VERIFY theorems rest on the secp256r1 ones, and are in `Execution/Proofs/Evm/Precompiles/P256Verify.lean`.
`isValid_callData` proves that, on the 160-byte call data of EIP-7951 with an affine public key, the input check gives the result of ECDSA verification.
`p256Verify_callData_sign` proves that a signature from the signing operation of SEC 1 returns the word 1 under its public key, when the call has at least 6900 gas.
`p256Verify_callData_neg_s` proves that, for `s` in `(0, n)`, `(r, s)` and `(r, n - s)` give the same result at every gas limit.
Either both signatures are valid or neither is, so the call does not require a low `s`.
`exists_p256Verify_eq_ok_valid` proves that the valid output is reachable.
The witness signs the hash 0 with the private key 1 and the nonce 1.
So the public key and the point `R = k G` are both the base point.

No theorem checks the module against the EIP-7951 pseudocode line by line.
The Python test `bindings/python/tests/precompile/test_p256verify.py` runs it on the 781 test vectors of EIP-7951, 778 of which come from Wycheproof.

### EIP-2537 precompiles

The BLS12-381 precompiles read and write field elements and points in the encoding of EIP-2537.
`bytesToG1_g1ToBytes` and `bytesToG2_g2ToBytes` (`Execution/Proofs/Evm/Precompiles/Bls12381/RoundTrip.lean`) prove that decoding the encoding of a valid point gives the same group element.
With the subgroup check, the same holds for a point of the subgroup.
`g1ToBytes_bytesToG1` (`Execution/Proofs/Evm/Precompiles/Bls12381/Encoding.lean`) and `g2ToBytes_bytesToG2` prove the converse, so every decoded point has one encoding.
The same file proves the round trips of a field element, an element of `Fp2` and the padding.

`valid_of_bytesToG1_eq_ok` and `valid_of_bytesToG2_eq_ok` (`Execution/Proofs/Evm/Precompiles/Bls12381/Group.lean`) prove that every decoded point is valid.
`inSubgroup_of_bytesToG1_eq_ok` and `inSubgroup_of_bytesToG2_eq_ok` prove that a point decoded with the subgroup check lies in the subgroup.
`bls12G1Add_eq_ok_iff` and `bls12G2Add_eq_ok_iff` (`G1.lean` and `G2.lean` in the same directory) prove that G1ADD and G2ADD return the encoding of the sum of their two decoded points.
`toPoint_add_of_bytesToG1_eq_ok` and `toPoint_add_of_bytesToG2_eq_ok` prove that this sum maps to the sum of the two points on the curve.
`bls12G1Add_g1ToBytes` and `bls12G2Add_g2ToBytes` prove the converse: on the encodings of two valid points, with enough gas, both return the encoding of their sum.
Neither precompile checks that its inputs lie in the subgroup, as EIP-2537 specifies.
So the sum is taken in the full group of points of each curve.
`exists_bls12G1Add_ok` and `exists_bls12G2Add_ok` apply this to two copies of each generator.

`bls12G1Msm_eq_ok_iff` and `bls12G2Msm_eq_ok_iff` (`G1.lean` and `G2.lean`) prove that G1MSM and G2MSM return the encoding of the sum of their pairs.
`g1Msm_eq_ok_iff` and `g2Msm_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/Bls12381/Msm.lean`) prove that this sum succeeds exactly when every point decodes with the subgroup check.
`toPoint_of_g1Msm_eq_ok` and `toPoint_of_g2Msm_eq_ok` prove that it maps to the sum of `m_i • P_i` on the curve.
Each scalar `m_i` is the integer of its 32 bytes, not reduced modulo the subgroup order, as EIP-2537 allows.
`inSubgroup_of_mem_g1Msm` and `inSubgroup_of_mem_g2Msm` prove that every decoded point lies in the subgroup.
`toPoint_g1Msm_generator` and `toPoint_g2Msm_generator` apply this to the generator with any scalar.
`G1.lean` and `G2.lean` also bound the MSM discounts, so an MSM never costs more than its separate multiplications.

`bls12Pairing_eq_ok_iff` (`Pairing.lean` in the same directory) proves that the pairing check succeeds exactly when every padding is zero and every point decodes with the subgroup check.
It then returns the word of `pairingCheck` on the decoded pairs.
`exists_represents_of_decodePairs` (`PairingProduct.lean`) proves that each decoded `P_i` represents some `a_i • g_1`, and each `Q_i` some `b_i • g_2`.
`bls12Pairing_eq_one_iff` proves that the output is the word 1 exactly when `sum_i a_i * b_i = 0`, that is, when the product of the pairings is 1.
`bls12Pairing_encodePairs` computes the output on the encodings of any represented pairs.
`bls12Pairing_generators` and `bls12Pairing_generator_neg` apply it to reach both outputs: 0 for `(g_1, g_2)`, and 1 for `(g_1, g_2)` with `(-g_1, g_2)`.

`bls12MapFpToG1_eq_ok_iff` and `bls12MapFp2ToG2_eq_ok_iff` (`G1.lean` and `G2.lean`) prove that the two map precompiles return the encoding of the curve map of their decoded field element.
The curve maps of RFC 9380 never fail.
So `bls12MapFpToG1_isOk_iff` and `bls12MapFp2ToG2_isOk_iff` (`Map.lean`) prove that each map precompile succeeds exactly when the length and gas checks pass and its padded field element decodes.
`inSubgroup_of_bls12MapFpToG1_eq_ok` and `inSubgroup_of_bls12MapFp2ToG2_eq_ok` prove that every output encodes a valid point of the subgroup.
`bytesToG1_of_bls12MapFpToG1_eq_ok` and `bytesToG2_of_bls12MapFp2ToG2_eq_ok` prove that the point decoder, with the subgroup check, accepts that output.
`bls12MapFpToG1_pad` and `bls12MapFp2ToG2_pad` prove that the padded encoding of every field element succeeds with enough gas.

No theorem relates the module to the execution-specs code it follows.

### A transaction whose message fails

`Execution/Proofs/Transactions/Failed.lean` states what a transaction leaves when its message fails, before Hegotá.
Its first theorems bound the writes to the sender, the beneficiary and the authorities that the authorization signatures name.

`buyGas_sender` in `Settlement.lean` proves that buying gas raises the nonce of the sender by one and takes the fees from its balance.
`buyGas_keeps` proves that it changes no code hash of the sender, no word of storage and no code.
`settleGas_accounts` proves that the settlement refunds the sender and pays the priority fee to the beneficiary.
It changes no nonce, code hash or code.
Storage stays at the sender when its nonce is not 0, and at the beneficiary unless it is deleted.

`authority_applyAuthorization` in `Authorization.lean` proves that one accepted authorization in scope sets the code hash of its authority to that of the delegation code, and raises its nonce by one.
`foldlM_applyAuthorization_authority` unrolls the whole list for an authority whose code is empty or a delegation indicator.
`acceptedBy` lists the authorizations that such an authority accepts, in order: those in scope, signed by it, with its nonce at that point.
After the list, the authority has one more nonce for each of them and the code of the last one, and the rest of its account stays.
The hypothesis on the code matters: an authority with other code refuses every authorization.
`foldlM_applyAuthorization_keeps` covers such an authority, under the hypothesis that no authorization sets a code with its code hash.
`processMessageCall_of_halt` in `Process.lean` puts the state back to the state before the authorizations when the message halts before its first frame, as EIP-8037 asks.
`processMessageCall_reads_of_error` proves that a failed frame reads as the state of its first frame, so a failed call keeps its accepted authorizations, as EIP-7702 asks.

`runTransaction_values_of_error` combines these results for one gas meter.
It names the output of the message call.
It gives the nonce, the code hash and the balance of every address against the state before settlement.
It gives the storage of every address but a deleted beneficiary.
That state reads as the state after the gas purchase when the transaction creates a contract or its first frame never starts.
When the first frame of a call starts and fails, it reads as the state that the authorizations leave.
`processTransaction_values_of_error` gives the same conclusion for every fork before Hegotá, with the gas meter of that fork.
`processTransaction_authority_of_error` gives each authority whose code is empty or a delegation indicator its values after the transaction.
Its nonce is its nonce before the transaction, plus one for the sender, plus one per accepted authorization.
Its code hash is that of the code the last one sets.
From Glamsterdam it needs the first frame of the call to start, which `FirstFrameHalts` denies.
Up to BPO5 it needs nothing more, since `aborts_of_prepareFirstFrame_of_lt_glamsterdam` in `Process.lean` shows that a call halts before its first frame only with an error that aborts the run.
`processTransaction_authority_of_firstFrameHalts` covers the halt from Glamsterdam: every authority keeps its code hash and its nonce, plus one for the sender, as EIP-8037 asks.
`processTransaction_authority_keeps_of_error` covers an authority with other code, which refuses every authorization: its account and its storage stay.
It assumes that no authorization sets a code with the code hash of the authority.
No theorem yet gives the storage of an authority that takes a delegation.
From Paris, an authority left empty by an authorization to the zero address is deleted with its storage, so that claim needs a condition.
`processTransaction_selfAuthorization_of_error` in `Replay.lean` applies the first theorem to a sender that signs its only authorization with the nonce of the transaction plus one.
It ends two nonces above the transaction.
`block_of_output` proves that the block after the transaction reads as the state that the transaction leaves.

### Transaction gas

Four theorems in `Execution/Proofs/Transactions/Process.lean` give the gas used and the block gas of a transaction that runs, before Hegotá.
`processTransaction_gasUsed_of_lt_london` covers the forks before London, where the refund is at most half of the gas used before it.
`processTransaction_gasUsed_of_london_of_lt_pectra` covers London to Dencun, where EIP-3529 caps the refund at a fifth of the gas used before it.
`processTransaction_gasUsed` covers Pectra to BPO5, where EIP-7623 raises the gas used to the call data floor when that floor is larger.
`processTransaction_gasUsed_of_glamsterdam` covers Glamsterdam, where EIP-8037 splits the gas into execution gas and a reservoir.
Its gas left is the execution gas left plus the reservoir left, and it gives the two block gas counts of EIP-7778 and EIP-8037.
At Glamsterdam, a negative state gas used counts as 0 in both block gas counts, a case that EIP-8037 leaves open.
From Hegotá a run fails as not yet specified, so there is no gas used to state.

`prepareFirstFrame_of_applyAuthorizations` gives the first frame of a call that moves no ether, after its authorizations.
`prepareFirstFrame_of_applyAuthorizations_error` proves that an error of the authorizations is the error of the first frame.
`prepareFirstFrame_of_value_eq_zero` gives the first frame of a call that moves no ether and applies no authorization.

### The supply of ether

`Execution/Proofs/State/Supply.lean` defines the supply of a transaction state as the sum of the balances of all its accounts.
`Execution/Proofs/Evm/Call/Supply.lean` proves that no call or creation raises it, at every fork.
`processTransaction_supply_le` in `Execution/Proofs/Transactions/Supply.lean` proves that a transaction lowers it by at least its burned fees: the base fee times the gas used, and the blob fee.
It assumes that the gas limit covers the least gas and that the price per gas covers the base fee, which the checks of the block ensure.

The equality holds in two cases.
`processTransaction_supply_of_glamsterdam` gives it from Glamsterdam, where SELFDESTRUCT and the deletions keep every balance.
`processTransaction_supply_of_dencun` gives it from Cancun for a transaction that creates no account.

Before Cancun, a SELFDESTRUCT whose beneficiary is its own account burns that balance inside the message, and the deletions burn what a marked account received after it.
The same holds from Cancun until Glamsterdam for a transaction that creates an account.
`processTransaction_supply_eq` in `Execution/Proofs/Transactions/Burn.lean` gives the exact change for every transaction that runs, at every fork, these cases included.
The supply after the transaction, plus the burned fees, the burns of SELFDESTRUCT and the deleted balances, is the supply before.
The burns come from a certificate of the run of the message, `RunBurns` in `Execution/Proofs/Evm/Call/BurnRun.lean`.
Each rule of the certificate takes one equation of the interpreter: a step from a running frame, a halt, a stop, a resume, a failed resume, the choice of a precompile, the entry of a call, its rollback, or the deposit of code.
Its other premises are side conditions that the run implies, such as the block of the state it keeps.
So a certificate follows the run step by step.
`RunBurns.ended_eq` proves that two certificates from the same start end in the same frame, and `RunBurns.total_eq` that they have the same total.
The log of a certificate records each burn of SELFDESTRUCT, and a frame that rolls back, or a creation whose deposit of code fails, drops what it burned.
`RunBurns.counted` proves that each burn the log counts is the burn of a step that runs SELFDESTRUCT, above 0, in the account the burn is from.
That step starts from a running frame that the run reaches, as `RunReaches` follows the same rules as the certificate.
The deleted balances are read after the gas is settled and before any account is deleted, once for each account.
`processTransaction_transactionBurns` proves that every transaction that runs has a certificate, and `TransactionBurns.unique` proves that all its certificates give the same two amounts.
From Glamsterdam, `TransactionBurns.eq_zero_of_glamsterdam` proves that both amounts are 0.
`processTransaction_supply_eq` makes the same two assumptions as `processTransaction_supply_le`.

`Execution/Proofs/Blocks/Burn.lean` gives the exact change of the supply across a whole block, and `Execution/Proofs/Blocks/Supply.lean` derives the bound and the Glamsterdam equality from it.
The block creates the wei of its withdrawals from Shapella, by EIP-4895, and of its rewards before Paris.
The DAO transfer only moves wei.
`stateTransition_supply_le` proves that the supply after the block plus the burned fees is at most the supply before plus the created wei, at every fork that the transition runs; it fails from Hegotá.
`stateTransition_supply_of_glamsterdam` proves the equality from Glamsterdam.
`stateTransition_supply_le_of_lt_glamsterdam` writes the burned fees from the header before Glamsterdam: the gas used and the blob gas used, each at its base fee.
From Glamsterdam the gas used of the header is the larger of the execution gas before the refunds, by EIP-7778, and the state gas, by EIP-8037, so it does not give the burned fees.
There the theorems take the fees from the body that the transition runs.
`stateTransition_supply_eq` in `Execution/Proofs/Blocks/Burn.lean` gives the exact change at every fork that the transition accepts.
It adds the created wei and subtracts the burned fees, the surviving SELFDESTRUCT burns and the deleted balances.
`BodyBurns` certifies the system calls before the transactions, each transaction in order, and the calls that read requests.
The system calls also carry burn logs, since the theorem assumes no particular code at their addresses.
`BlockLosses.transactions` retains each transaction's burn log and deleted balances.
`BodyBurns.total_eq` shows that two certificates of the same body give the same total of losses, when the block has at most two ommers before Paris, as its checks enforce.
So the run fixes that total.
From Glamsterdam, `BodyBurns.total_eq_zero_of_glamsterdam` proves that the total of losses is 0.

### The authorizations of EIP-7702

`Execution/Proofs/Transactions/Authorization.lean` covers every case of one authorization, at every fork.
`applyAuthorization_cases` proves that an authorization that succeeds is skipped, refused, or accepted after it pays and delegates.
`applyAuthorization_of_accepts_of_pay` gives an accepted authorization from what its payment leaves.
`applyAuthorization_of_payAuthorization_error` proves that a failed payment stops the authorizations with its error.
`applyAuthorization_of_authorityAccepts_error` proves that an authority whose code cannot be read stops them with that error.
`payAuthorization_eq_ok_iff` proves that from Glamsterdam a payment succeeds exactly when its charge does.
`state_payAuthorization` proves that a payment keeps the state, the accesses and the refund.
`sameOutside_delegate` proves that a delegation changes no account, storage or transient storage but the authority's.
`getCode_delegate_of_ne` proves that a delegation keeps the code under every hash but the hash of the code it sets.
`getCode_delegate_self` proves that a delegation stores the code it sets under its hash, when that hash is not the hash of the empty code.

Real code is neither empty nor a delegation indicator.
`authorityAccepts_of_code` proves that an authority with real code refuses every authorization.
`foldlM_applyAuthorization_keeps` proves that the authorizations keep the account, storage, transient storage and code of an address with real code.
It assumes that no authorization of the list carries a code to set whose Keccak-256 hash is the code hash of that address.
When the state stores each code under its own hash, only a collision of Keccak-256 breaks this assumption.
`meter_foldlM_applyAuthorization_of_lt_glamsterdam` proves that up to BPO5 the authorizations keep the meter.

The two theorems below hold for any recovery of an authority.
Both assume that the state holds the code of every account.
`foldlM_applyAuthorization_isOk_of_lt_glamsterdam` proves that up to BPO5 the authorizations succeed over any meter.
`foldlM_applyAuthorization_isOk` proves that the authorizations succeed, and from Glamsterdam take at most 227790 execution gas times their number.
From Glamsterdam, it assumes that the meter holds that much gas for every authorization.
From Glamsterdam, it also assumes that the state holds the code of every account before the transaction.
From Glamsterdam, it also assumes that every charge within the gas left succeeds and takes at most its amount.

`chargesWithin_nat` proves this last condition for the meter up to BPO5.
`chargesWithin_stateGasMeter` proves it for the meter of EIP-8037.

### Merkle Patricia Trie

The trie commits to a map from byte keys to byte values under one 32-byte root.
Two theorems in `Execution/Proofs/Trie/Binding.lean` describe what the root binds, for every hash.

The first is `verifyProof_binding`, about two Merkle proofs of one key that verify against one root.
They are one proof and give the key one value.
Otherwise `findProofCollision` returns two different nodes of the proofs with one hash.
The second is `root_binding`, about two tries with one root.
They give every key one value, or `findCollision` returns such a collision in the proofs of that key.
Both searches are proved to return only collisions, and to return none for an input compared with itself.

`verifyProof_sound`, in the same file, compares a proof with the proof that the trie builds for the key.
The proof is that honest proof and gives the trie's value of the key.
Otherwise `findProofCollision` returns a collision between the two proofs.

A secured trie hashes each key into its path, so two of its keys can have one path.
`root_binding` and `verifyProof_sound` name that case too.
There `findPathCollision` returns two different keys of the trie with one hash.
It searches only a secured trie, and it is proved to return only collisions.
`findKeyCollision_of_nodup` proves that the key search returns none for keys with distinct hashes.

Both theorems assume that the keys of each trie are distinct, as the keys of a map are.
The variants `root_binding_foldl_trieSet` and `verifyProof_sound_foldl_trieSet` apply to tries built by setting any list of key-value pairs from an empty trie.
Later entries replace earlier values of the same key, and an empty value removes its key.
`nodup_keys_foldl_trieSet` proves that this construction gives distinct keys, as the trie of Yellow Paper Appendix D (Shanghai version) assumes, so callers need no distinctness hypothesis.
This construction is the path of Python `trie.root`, through `Execution/Exports/Trie.lean`.
`root_of_rootExport` (`Execution/Exports/Proofs/Trie.lean`) proves that the export returns the root of this trie, built from its decoded pairs.
`rootExport_of_root` proves the converse, so the two variants apply to the output of Python `trie.root`.
The state and storage roots in `Execution/State/Root.lean` build tries directly, and `stateEntries_nodup` and `storageEntries_nodup` (`Execution/Proofs/State/Root.lean`) supply their distinct keys.
`root_binding_secured` (`Execution/Proofs/Trie/Binding.lean`) applies `root_binding` to two secured tries with distinct keys and one root.
The two tries give every key one value, or `findSecuredCollision` returns a collision in the proofs of the key or among the keys.
`storageRoot_binding` proves that two storages with one root give every key the same word, `0` when unset.
Otherwise `findStorageCollision` returns a collision.
`stateRoot_binding` applies `root_binding_secured` to the state trie and then `storageRoot_binding` at each address with an account.
Two states with one state root give every address the same account, and at every address with an account every key the same word, or `findStateCollision` returns a collision.
Storage at an address without an account is outside `stateEntries`, and code is committed only through `codeHash`.
So the state root binds no storage at an address without an account, does not separate a key set to `0` from an unset key, and binds nothing in the code map beyond each account's `codeHash`.
The storage and state searches are proved to return only collisions, and none for an input compared with itself.
No theorem bounds the probability of finding two storages or two states with one root that differ.
The indexed roots in `Execution/Blocks/Roots.lean` also build tries directly, with the RLP encoding of each index as its key.
`indexedEntries_nodup` (`Execution/Proofs/Blocks/Roots.lean`) supplies their distinct keys, since the RLP decoder reads each index back from its encoding.
Applied to the plain tries of two lists with these distinct keys, `root_binding` shows that two lists with one root give every key one value.
Otherwise `findCollision` returns a collision in the proofs of that key.
The path searches return nothing there, since the trie is not secured.
`indexedRoot_binding` concludes that the two lists are equal, or `findIndexedCollision` returns a collision in the proofs of one index.
Two transactions, or two withdrawals, with the same bytes are equal, so `transactionsRoot_binding` and `withdrawalsRoot_binding` conclude the same for the lists themselves.
`receiptsRoot_binding` does so for receipts whose types are below `0xc0`, which holds for type 0 and for every type that a fork adds.
No theorem bounds the probability of the indexed-root search itself.
The bound below covers two tries that give one key two values.

`Execution/Proofs/Trie/RandomOracle.lean` turns this binding into a probability bound, with the hash a random oracle.
The trie definitions take their hash in any monad, so the experiment runs the root of the specification with a hash that queries the oracle.
An adversary outputs two tries and a key.
The experiment computes both roots and both proofs of the key, then queries the key, every key of both tries and every node of both proofs.
The adversary wins when the tries are both secured or both plain, each has distinct keys, and they have one root, yet give the key different values.
`collision_of_extract` shows that every win leaves two different cached inputs with one answer.
The searches `findCollision`, `findPathCollision` and `findLookupCollision` name them, run with a table that agrees with the cache.
`prEvent_wins_le` then bounds a win by `Q^2 / N` through `prEvent_collision_le`, where `Q` bounds the queries of the whole experiment.
`prEvent_wins_le_two_pow` states it with `N = 2^256`.
The bound needs no hypothesis that the cache covers the witnesses, since the experiment queries them itself.
One oracle answers keys and nodes alike, so a collision between a key and a node counts too.
The first trie may be fixed before the run, so the same bound covers a second trie with the root of a given one.
That bound is still `Q^2 / N`, not a sharper fixed-target bound.
`Q` counts every hash call of the experiment, repeats included, and the extraction makes many: each proof level rebuilds its subtree.

`verifyAccountRange_complete` and `verifyStorageRanges_complete` (`Execution/Proofs/Network/SnapRangeComplete.lean`) prove that honest snap answers from secured tries pass their checks, or `findCrossCollision` returns a Keccak-256 collision among proof nodes.
The keys are listed by increasing hash, and the proof contains the proofs of the start and the last entry.
That order assumes the keys of each trie have distinct Keccak-256 hashes; no search returns two keys with one hash.
The account theorem uses successful slim and full encodings of each account; `fullAccount_encode_slimAccount` proves that the conversion returns the full form.
The storage theorem assumes whole tries before the last range; every range starts at the requested hash for one account and at the zero hash for several.
`verifyAccountRange_complete_nil`, `verifyStorageRanges_complete_nil`, `verifyAccountRange_whole` and `verifyStorageRanges_whole` cover empty last ranges and whole tries; whole tries need no proof and no collision alternative.
An empty AccountRange with no proof is the empty reply `noState`, rather than a claim about the trie.
`findCrossCollision_self` shows that the search finds none when the sent proof is the honest one and holds no collision.
No theorem bounds the probability that `findCrossCollision` finds a collision.

An answer of `eth_getProof` (EIP-1186) is checked against a state root by `AccountProof.verify` (`Execution/State/AccountProof.lean`).
It checks the account proof, then each slot proof against the storage root of the answer.
`verifyAccount_sound` and `verifySlot_sound` (`Execution/Proofs/State/AccountProof.lean`) carry `verifyProof_sound` over to the fields of the answer.
Take a secured trie with distinct keys and its root.
When a check passes, the trie's value under the key decodes to the fields of the answer.
When the check reports absence, the trie holds no value under the key.
A slot reported absent also has the word 0 in the answer.
Otherwise a search returns a collision with the trie's own proof, or two keys with one hash.
`verifyAccount_sound_state` and `verifySlot_sound_storage` apply them to the tries of a state, whose keys are distinct.
`verifyAccount_getProof` and `verifySlot_getProof` prove that the trie's own proofs pass, with the fields that the trie holds.
A proof can show that the address has no account, or that a slot is not set.
The storage value of a slot that is not set is 0, so the answer must give that word.
EIP-1186 does not say which fields the answer holds for an address without an account.
So the check judges no field of an absent account, and reports the absence.

### Weak subjectivity

A node that starts from a recent checkpoint trusts it only for a limited time, the weak subjectivity period.
`Consensus/WeakSubjectivity.lean` computes the period with the rule of each fork: Phase 0 counts validators, Electra the churn of the balance, and Gloas three weighted churns.
The theorems in `Consensus/Proofs/WeakSubjectivity.lean` say what the 64-bit computation returns.

From Electra, `balanceChurnPeriod_eq_ok_iff` gives the period in closed form, the withdrawal delay plus `10 t / (200 c)` epochs for a total active balance `t` and a churn `c`.
It succeeds exactly when no product or sum reaches `2^64` and the churn is not zero.
In Phase 0, `phase0PeriodEpochs_eq_ok` shows that a computed period is one of the two expressions of the rule, on natural numbers.
`min_le_computeWeakSubjectivityPeriod` shows that, at every fork, the period is at least the withdrawal delay.

`computeWeakSubjectivityPeriodElectra_le` bounds the Electra period by a function of the parameters alone.
It assumes a positive churn quotient, and a minimum churn that is a positive whole number of increments.
At the mainnet parameters, `computeWeakSubjectivityPeriodElectra_le_mainnet` gives at most 3558 epochs, for every state.
`gloasWeightedChurn_eq_ok_iff` gives the Gloas weighted churn in closed form when its three churns and sums stay below `2^64`.
`computeWeakSubjectivityPeriodGloas_le` bounds the Gloas period by a function of the parameters alone when the activation floor covers the rounding losses.
At the mainnet parameters, `computeWeakSubjectivityPeriodGloas_le_mainnet` gives at most 1658 epochs, and a Python test reaches that bound.
Its state is not one that a chain can reach: one validator holds about 1.4 billion ether.
`computeWeakSubjectivityPeriodPhase0_le` bounds the Phase 0 period by the withdrawal delay plus the longer of two terms, `160 N / (600 delta)` and `230 N / (600 Delta)`.
Here `N` is the number of active validators, `delta` the churn of validators in one epoch and `Delta` the deposits that fit in one epoch.
The bound needs no condition beyond success of the computation.
It depends on the state through `N` and `delta`, so it gives no number for the parameters alone.

`isWithinWeakSubjectivityPeriod_eq_ok_iff` states when the check of a checkpoint succeeds and what it answers.
The state must hold the root of the checkpoint at its epoch and be at that epoch.
The answer is then whether the current epoch is at most the epoch of the checkpoint plus the period.
By `isWithinWeakSubjectivityPeriod_of_slot_le`, a checkpoint within its period at some slot is within it at every earlier slot.

From Electra, `accountable_safety_of_weakSubjectivityPeriod` (`Consensus/Proofs/Transition/WeakSubjectivitySafety.lean`) relates the period to the safety margin that the rule intends, under an assumption on the change of the validator sets.
The trusted set is the active validators of the state at the checkpoint, weighed by their effective balances, with at least one increment of stake.
Take two conflicting finalized checkpoints of the Casper FFG model.
The change of a set since the trusted set counts the stake that joined plus twice the stake that left.
Assume that the change of each justified set between their epochs is at most `3 c` for each of the `n` epochs of churn, the period less the withdrawal delay, with `c` the churn of the period.
Then the slashable validators hold at least `1/3 - SAFETY_DECAY/100` of the trusted stake, `7/30` with `SAFETY_DECAY` at 10.
The arithmetic is `safetyMargin_of_balanceChurnPeriod_eq_ok`, from `200 n c ≤ SAFETY_DECAY · t`.
In Electra an epoch adds at most the activation-exit churn `a ≤ c` and removes at most `c`, consolidation sources included, so its change is at most `a + 2 c ≤ 3 c`.
From Gloas an epoch changes the set by at most three times the weighted churn, plus 4 Gwei of rounding when the consolidation churn is zero.
The queues carry unused churn to later epochs, so the bound can hold over the window without holding in each epoch.
No theorem yet derives it from the state transition, and the model fixes the effective balances over the window.
The rule spends the withdrawal delay on keeping exits slashable and the other epochs of the period on churn, and the assumption takes the change over those epochs as given.
Activations have no such delay, and a validator outside the registry of the checkpoint weighs zero in the model.
The beacon chain weighs the votes of each epoch at the effective balances of that epoch.
Top-ups, the balance that a consolidation moves to its target, rewards and penalties all change those balances during the window.
The theorems weigh every vote at the balances of the checkpoint, so they reach a chain only once those changes are bounded, and no theorem bounds them yet.

From Phase 0 to Deneb, `accountable_safety_of_weakSubjectivityPeriod_of_lt_electra` covers the period in part.
The rule counts `N` active validators of average balance `t` ether, rounded down, a largest effective balance `T` ether, a churn of `delta` validators and `Delta` top-ups per epoch.
The theorem assumes each justified set gains and loses at most `delta` validators for each of the `n` epochs of churn, with `delta` the churn at the checkpoint.
It also assumes every effective balance at most `T`, with `T` a whole number of ether.
With large balances, `230 T < 320 t`, the rule's epochs for churn always satisfy `20 n delta T ≤ N t`, and so keep the margin.
`churn_le_of_phase0PeriodEpochs_eq_ok` gives that inequality for the epochs of the rule.
The rule takes the longer of those and its epochs for top-ups, so the theorem also assumes that the epochs for top-ups satisfy the same inequality.
Top-ups change a balance, which the model leaves out, and in the model a longer period only allows more churn.
The rule does not imply that hypothesis: with `N = 2^23` validators of 32 ether, `delta = 128` and `Delta = 512`, the rule takes 6280 epochs for top-ups, while the churn allows 3276.
Over 6280 epochs, the churn of validators alone lowers the bound of Gasper Theorem 8.3 to about 14% of the stake.
With small balances, `230 T ≥ 320 t`, no theorem relates the period to the margin.
The Python suite checks the periods against the three tables of the rule, except for the rows whose states take minutes to build.

### Fast confirmation rule

`Consensus/ForkChoice/FastConfirmation.lean` holds the fast confirmation rule of [arXiv 2405.00549v4](https://arxiv.org/abs/2405.00549v4).
The rule weighs the committees of a range of slots exactly.
Each active member of their union counts once, by its effective balance in the source of balances, and a range with a whole epoch weighs the total active balance.
An earlier form of the rule estimated that weight as an average per slot, which is not an upper bound on a given committee.
[A counterexample on #1458](https://github.com/ethereum/EthLib/issues/1458#issuecomment-6764027413) shows that the estimate lets the rule confirm a block that an attack then reorgs, under the assumptions of the paper.
The pinned fast confirmation vectors of consensus-specs `v1.7.0-beta.4` were generated with that estimate.
In 24 of them, five cases at several forks, the rule now confirms another block, and `tests/parity/disagreements.toml` lists them as expected failures.
The vendored fast confirmation cases in `tests/consensus/fork_choice` still pass.
From Gloas the discount for empty slots also counts the votes for the pending node of the parent, which the rule of consensus-specs `v1.7.0-beta.4` leaves out.
No pinned vector reaches that case, so review alone checks it until the vectors move to a release with it.

`stake_le_computeCommitteeWeightBetweenSlots` (`Consensus/Proofs/ForkChoice/FastConfirmationIndicators.lean`) shows that the weight covers the stake of the active members of the committees.
`stake_le_computeCommitteeWeightBetweenSlots_of_covered` shows that the weight of a range with a whole epoch covers the stake of every validator active in the source of balances.
`lt_two_mul_honest_support_of_isOneConfirmed` then gives Lemmas 4 and 3 of the paper for a block that the store confirms.
Twice its honest support, plus the discount for empty slots, exceeds the committee weight since its parent plus the boost.
It takes any set `W` of validators whose stake the committee weight of the range covers.
It assumes that the Byzantine validators hold at most the configured share of the stake of `W`.
That is Assumption 2 of the paper when `W` is the set of active members of the committees of the range.
It also assumes that no validator the store knows to equivocate is honest.
It also assumes that the effective balances of those validators are whole numbers of 100 Gwei, since the store rounds the weight down to 100 Gwei for its share of the adversary.
`lt_two_mul_honest_supportersOf_of_isOneConfirmed` (`Consensus/Proofs/ForkChoice/FastConfirmationSets.lean`) builds the supporters, the equivocators and the committee members from the store, and their stakes are the store's numbers.
It replaces that assumption with an invariant of the state: each effective balance of the source of balances is a whole number of increments.
It also assumes that the increment of the preset is a whole number of 100 Gwei, as 10^9 Gwei is.
No theorem yet derives that from the state transition.
The update of effective balances keeps it, but the other steps and the upgrades have no proof.
It also assumes that each supporter of the block is a member of the committees of the range.
No theorem yet proves that assumption.
The store checks a vote against the committees in the state of its target, while the rule reads them in the state of the head.
In a store with a forward clock, `Store.ForwardReachable.votesHaveOrigins` gives each latest vote the facts of its attestation.
From those facts, `VoteOrigin.exists_mem_committee` (`Consensus/Proofs/ForkChoice/VoteOrigins.lean`) places the voter in a committee of the slot of its attestation, in the state of its target.
`mem_getCommitteesBetweenSlots` (`Consensus/Proofs/ForkChoice/FastConfirmation.lean`) places each member of a committee of a slot of the range, in the state of the head, among the members that the rule reads.
What remains is that the slot of the vote lies in the range, and that the two states agree on the count and the committees of that slot.
They should agree when both states hold the same RANDAO mix of the epoch `MIN_SEED_LOOKAHEAD + 1` epochs before the epoch of the slot, two in both presets, and the same active validators in the epoch of the slot.
No theorem yet proves that.
For a range with part of an epoch that should hold when the head descends from the block, since the range then lies in the epoch of the block and the next one.
Both corollaries apply `lt_two_mul_honest_supportersOf_of_weighed`, which builds those sets for any `W` that holds the supporters and the active members of the committees, and whose stake the weight covers.
`lt_two_mul_honest_supportersOf_of_covered` drops that assumption when the range of the adversary holds a whole epoch.
Its set `W` is then every validator active in the source of balances, which holds each supporter.
Its Byzantine bound is Assumption 2 when every validator active in the source is a member of a committee of the range.
Otherwise it implies Assumption 2 when the validators that have left the committees are Byzantine, as Assumption 1 of the paper ensures.
With an honest one gone the two bounds are incomparable.
The tally of the source still counts the votes of validators that have left the committees, so the proof bounds their stake.
For a range with part of an epoch the assumption on the supporters stays.
Like the paper, the theorem takes a static set of validators, Assumption 1.
The honest support of the target of the current epoch takes the total active balance less the weight of the committees so far as the weight still to vote.
No theorem proves that, which rests on the shuffling of the head and its pulled-up state agreeing on the active validators of the epoch.
Each member of the committees must also be in the source of balances, or the rule fails; no theorem bounds the epochs between that source and the range.

### Honest validator duties

`Consensus/HonestValidator.lean` holds what an honest validator computes for its duties.
It finds the committee of a validator in an epoch, whether it proposes, and, from Altair, its sync committee seat and subnets.
It also signs each message that a validator sends, under the domain type and the epoch that the receivers check.
The theorems in `Consensus/Proofs/HonestValidator.lean` relate these duties to the checks of the transition and of gossip.

`isValidSignatureAtEpoch_of_signAtEpoch` shows that a duty signature passes the check of a signature at the same domain type and epoch, under the public key of the secret key.
`verifyBlockSignature_of_getBlockSignature` shows that a block signed by its proposer passes the check of the block signature.
`processRandao_ne_invalidRandaoReveal` shows that the RANDAO reveal of the proposer never fails the RANDAO check.
Both assume a block of the current epoch, and a proposer whose public key is that of the secret key.
The gossip checks of a selection proof and of an aggregate and proof read the target epoch, so their theorems assume it is the epoch of the slot.

`getCommitteeAssignment_sound` shows that an assignment is a committee of the epoch that holds the validator.
`getCommitteeAssignment_unique` shows that no other committee of the epoch holds it.
It assumes that the registry stays within its limit, and that the active validators times the committees of the epoch fit in 64 bits.
`getCommitteeAssignment_ne_none` shows that an active validator never gets the answer that it has no committee, under the hypotheses of `exists_mem_getBeaconCommittee`.
The search can still fail, for an epoch after the next one or a committee without a value.
It also fails for the epoch whose first slot plus the length of an epoch reaches 2^64.
There the 64-bit sum of the guide overflows, as `getCommitteeAssignment_eq_error_of_overflow` shows.

From Gloas, a validator also finds the slot of its payload timeliness committee and the slots it will propose.
`getPtcAssignment_sound` shows that an assignment is the first slot of the epoch whose committee holds the validator.
`not_mem_of_getPtcAssignment_none` shows that no committee of the epoch holds a validator without one, when an epoch has a slot.
`getUpcomingProposalSlots_spec` shows which slots are the upcoming proposal slots, in increasing order.
They are exactly the slots after the slot of the state whose proposer in the lookahead is the validator.
`validatePtcMessage_getPayloadAttestationMessageSignature` covers a payload attestation message for the current slot that its validator signed.
It shows that the message passes the wire checks of the fork choice: its slot and its signature.
No theorem covers the other checks of the handler: a known block, the slot of the state and a seat in the committee.
It rests on `fastAggregateVerify_sign`: an honest signature passes the fast aggregate verification under its one key.

`isAssignedToSyncCommittee_ok_iff` states when the sync committee seat check succeeds.
Its answer is then whether the validator's key is in the current or the next committee.
`computeSubnetsForSyncCommittee_ok` shows that its sync committee subnets come once each, in increasing order, from the seats of its key.
The Python suite checks each duty signature against py_ecc, on signing roots computed in the test, and each committee against the shuffle export.
It checks each payload timeliness assignment and the upcoming proposal slots against the window and the lookahead that it reads from a Gloas state.

### Honest aggregation

`Consensus/HonestAggregation.lean` holds the attestation data and the vote of an honest attester, and the aggregates that an honest aggregator builds from votes.
Before Electra the vote is an attestation with one bit, and from Electra it is a single attestation.
An aggregator joins the votes of one committee on the same data into one attestation.
From Altair, a sync aggregator joins the messages on one block root into the contribution of its subcommittee.
The construction theorems are in `Consensus/Proofs/HonestAggregation.lean`.
Each of them assumes only that the construction succeeds, except the theorem on signatures and the two that attestation data and the root of its target have a value.

An attester first builds attestation data from the head block and the state at its slot.
`getAttestationData_eq_ok_iff` states that data: its slot is the slot of the state, it votes for the root of the head block, its source is the current justified checkpoint and its target epoch is the current epoch.
`getEpochBoundaryBlockRoot_eq_ok_iff` states the root of the target.
At a slot that the length of an epoch divides, it is the root of the head block, and otherwise the root that the state records for the first slot of the epoch.
`target_epoch_eq_of_getAttestationData` shows that the target epoch is the epoch of the slot, which the processing of an attestation checks.
The index follows its fork: the committee index before Electra and zero from Electra (`attestationDataIndex_of_lt_pectra`, `attestationDataIndex_of_pectra_of_lt_glamsterdam`).
From Gloas it is zero for a head block of the slot, and otherwise 0 or 1 for an empty or a full payload, while a pending status fails (`attestationDataIndex_of_glamsterdam_of_eq`, `attestationDataIndex_of_glamsterdam_of_ne`).
`isValidDataIndex_of_attestationDataIndex` shows that from Electra the index passes the check of the index of a vote.
`exists_getAttestationData_eq_ok_iff` shows that the data has a value unless that index fails.
It assumes that the length of an epoch is positive and at most the number of recorded roots, and that the slot plus that number fits in 64 bits.
The data takes the head block and the status of its payload as arguments, since the fork choice computes them.
The slot of the data is the slot of the state, so the caller passes the state of the head block processed up to the slot of the duty, as the guide does.

`getAttestingIndices_constructAttestation` shows that the attestation of a validator has that validator as its only attester.
Before Electra, `getAttestingIndices_constructAttestation_getAttestationData` composes it with the data: the attestation names the committee of the slot at the index given, which holds the validator.
`mem_getAttestingIndices_constructAggregate` shows that the attesters of an aggregate are the attesters of its attestations with the same data.
From Electra, `mem_getAttestingIndices_constructAggregateOfSingleAttestations` shows that the attesters of an aggregate are the attesters of its single attestations with the same data and committee.
`getCommitteeIndices_constructAggregateOfSingleAttestations` shows that the committee bits of that aggregate name its one committee.
`constructSyncCommitteeContribution_spec` states the bits of a contribution.
The bit of a seat is set when its key is the key of the validator of a message on the slot and the root.
`fastAggregateVerify_getAggregateSignature` shows that honest signatures of attestations on one message aggregate to a signature that the fast aggregate verification accepts.
That theorem assumes that the secret keys do not sum to zero.
It verifies under the keys in the order of the attestations.

`isValidIndexedAttestation_constructAggregate` and `isValidIndexedAttestation_constructAggregateOfSingleAttestations` (`Consensus/Proofs/HonestAggregateSignatures.lean`) prove that successfully constructed honest aggregates have indexed forms that pass the signature check of an indexed attestation.
The selected signers must have distinct validator indices, use their registered keys and have a nonzero sum of secret keys.
From Gloas, their number must also fit the check's bound.
The proof derives the permutation from those signers to the sorted indices that the receiver reads.
The aggregate adds the signature of every vote, so a validator that votes twice counts twice in the signature but once in the keys.
The theorems avoid this case by requiring distinct signers.

`isValidContributionSignature_constructSyncCommitteeContribution` (`Consensus/Proofs/HonestContributionSignatures.lean`) proves that a contribution of honest matching messages passes its signature check.
The domain and signing root must compute successfully, and the messages must sign that root under their registered keys.
The sum of the secret keys for the selected seats must be nonzero.
A key counts once for each of its selected seats, and each seat takes the first matching message, so duplicate messages add nothing.
The gossip corollaries characterize acceptance of the aggregate's committee check and the contribution topic by their remaining conditions.
These include the checks of time, membership and the aggregator's signatures.
The corollaries assume that the head state of the receiver is the state of the construction.

The contribution takes the sync committee as an argument.
The caller passes the committee of the next slot, which gossip and the next block check.
The Python suite checks each vote and each aggregate against values worked out in the test from the guide, with py_ecc for the signatures.

### Honest proposer

`Consensus/HonestProposer.lean` holds what an honest validator computes to fill the block it proposes.
Before Heze it votes on the Eth1 data, and in Electra it counts the deposits of the deposit contract that the block holds.
It computes the state root of the block, and from Electra it joins the network aggregates of one vote and reads the requests of the execution layer from their bytes.
From Fulu it counts the custody groups of a node with validators.
The theorems are in `Consensus/Proofs/HonestProposer.lean`.

The Eth1 data of an Eth1 block is not specified, so the vote takes the timestamp and the Eth1 data of a block as functions, and every theorem about it holds for all of them.
`getEth1Vote_eq_or_candidate` shows that the vote is the data of the state or the data of a candidate block of the chain, and `depositCount_le_of_getEth1Vote` that its deposit count is never below that of the state.
`getEth1Vote_most_voted` shows that, when the state already holds a vote for a candidate, the vote is such a vote with the most copies.
`expectedDepositCount_eq_getEth1PendingDepositCount` shows that the pending deposit count of Electra is the count that block processing requires.
From Fulu that count is zero, as `expectedDepositCount_of_fusaka` shows, so the pending count is defined in Electra only.

`processBlock_stateRoot` shows that block processing never reads the state root of the block.
So `stateTransition_of_computeNewStateRoot` shows that a block that carries the new state root passes the full transition, checks included, and that the state after it has that root.
It assumes a signature that passes the block signature check.
`computeOnChainAggregate_spec` shows that the on-chain aggregate joins the network aggregates sorted by their first committee, and `committeeBits_computeOnChainAggregate` that its committee bits mark exactly those committees.
`getExecutionRequests_eq_ok_iff` shows that the requests read from a list are exactly the requests that give that list.
It rests on the canonical SSZ decoder and on the empty bytes being the only encoding of an empty list.
`signedHeader_eq_ok_iff` shows that the signed header of a block carries the root of its body, and `getValidatorsCustodyRequirement_bounds` that the custody requirement stays between its two bounds.
`totalEffectiveBalance_eq_ok_iff` shows that the balance behind that requirement is the sum of the effective balances of the validators, with a repeated index counted again.
From Altair, `processSyncCommitteeContributions_spec` states the bits of the sync aggregate of a block.
They are exactly the bits that its contributions set, each at the seat of its subcommittee.
It also shows that the contributions name distinct subcommittees below the number of subnets.

No theorem says that the on-chain aggregate verifies, which rests on BLS and on the disjoint committees of the network aggregates.
The Python suite checks the new state root against the state root of each valid sanity block case that the repository holds, at seven forks from Phase 0 to Heze.
It checks the Eth1 vote, the pending deposit count, the custody requirement, the on-chain aggregate, the sync aggregate and the execution requests.
The test works out the expected values from the guides, with py_ecc for the aggregate signatures.

### Payload preparation

`Engine/PreparePayload.lean` holds the forkchoice update that an honest proposer sends to the execution layer, from Bellatrix to Fulu.
The update names the parent of the payload as its head, and carries the payload attributes: the time of the slot, the RANDAO mix of its epoch and the suggested fee recipient.
From Capella the attributes add the withdrawals that the state expects, and from Deneb the root of the latest block header.
Before the merge the head is the terminal block of proof of work, which the proposer looks for in a chain that it is given as a list.
The module lives in the Engine layer because it builds the payload attributes of the Engine API from a beacon state.
The theorems are in `Engine/Proofs/PreparePayload.lean`.

The search for the terminal block reads the list in order, and finds a block by its own hash.
When two blocks share a hash it finds the first, and when two blocks are terminal it returns the first.
`getPowBlockAtTerminalTotalDifficulty_go_eq_ok_some` shows that a block it returns reaches the terminal total difficulty, and that its parent is the zero hash or a block of the chain below that difficulty.
`getPowBlockAtTerminalTotalDifficulty_go_eq_ok_none_iff` states exactly when it returns none, and `getPowBlockAtTerminalTotalDifficulty_go_eq_error` that it fails only on a block that reaches the difficulty with a parent the chain does not hold.
`prepareExecutionPayload_eq_ok_some` states each field of the update, and `prepareExecutionPayload_eq_ok_none_iff` when the proposer asks for nothing.
`payloadHeadBlockHash_of_merged`, `payloadHeadBlockHash_of_inactive` and `payloadHeadBlockHash_of_premerge` state the head before and after the merge.

The theorems that link the update to the checks of a block are the reason for the module.
`processBlockExecution_eq_error_of_prepareExecutionPayload` takes a block that passes the header step on the state of the proposer.
Its payload names the head of the update as its parent, and carries the mix, the timestamp and, from Capella, the withdrawals of the attributes.
The execution part of the block then fails only on the number of blobs, the execution layer, a hash or an accessor, and never on the parent, the mix, the time or the withdrawals.
It rests on `processExecutionPayload_eq_error_of_prepareExecutionPayload`, which assumes only that the checking state shares the slot, the genesis time, the RANDAO mixes and the latest payload header of the state of the proposer.
It also rests on `getExpectedWithdrawals_latestBlockHeader`, which shows that the expected withdrawals do not read the latest block header, and on `payloadInputs_processWithdrawals`.
From Deneb, `parentBeaconBlockRoot_newPayloadRequest_of_prepareExecutionPayload` shows that the request to the execution layer names the parent root of the attributes.

Before the merge, `validateMergeBlock_of_payloadHeadBlockHash_of_configured` and `validateMergeBlock_of_payloadHeadBlockHash_of_difficulty` show that the fork choice accepts a first payload on the head.
With a configured terminal block hash, the block must be of the slot of the state.
Without one, the fork choice must look blocks up in the same chain, its hashes must differ, and no block may name the zero hash as its parent.
The search of the guide accepts a terminal block whose parent is the zero hash, while the merge check of the fork choice looks that parent up, so the theorem leaves such blocks out.
No theorem covers the payload that the execution layer builds, or the safe and finalized blocks, which come from the fork choice.

The Python suite checks each case of the terminal block search, the configured terminal block hash, the withdrawals and the parent root against values worked out in the test from the guides.

From Gloas, `prepareExecutionPayloadGloas` reads the fork choice store and a head node.
The proposer builds on the full node of the head when the fork choice says so at the current slot.
It then applies the payload that the store holds for the head to a copy of the state, and reads the withdrawals of that copy.
Otherwise it keeps the state and the withdrawals that the state records.
From Heze it also reads the transactions of the inclusion lists of the slot before, which the payload attributes of the Engine API here do not carry.
`prepareExecutionPayloadGloas_eq_ok` states each field of the update.
`payloadParentGloas_eq_ok` states the two cases of the parent.

The theorems that link the update to a block assume that the bid of the block builds on the head of the update.
From a full parent the block must carry the requests of the payload that the store holds, and the two hashes of the latest bid must differ.
`slot_of_prepareExecutionPayloadGloas` shows that the state after the parent, header and withdrawal steps has the slot, the time and the mix of the attributes.
`parentRoot_of_prepareExecutionPayloadGloas` shows that the block names the parent root of the attributes.
`latestBlockHash_of_prepareExecutionPayloadGloas` also assumes that the latest block hash is the parent hash of the latest bid.
It shows that the state after those steps has the head as its latest block hash.
`payloadExpectedWithdrawals_of_prepareExecutionPayloadGloas` makes the same assumption.
It shows that this state records the withdrawals of the attributes.
It rests on `applyParentExecutionPayload_latestExecutionPayloadBid`, which shows that the payload of a parent keeps the latest bid.
`checkExecutionPayloadBid_of_prepareExecutionPayloadGloas` takes a bid built on the state of the proposer from a payload that follows the update.
It shows that the bid passes the checks of its parent hash, its parent root and its mix in the bid step.
It makes the assumptions of `latestBlockHash_of_prepareExecutionPayloadGloas`.
It also assumes that the state of the proposer records the root of its latest block header as the root of the slot before.
No theorem here covers the inclusion lists, which come from the store.

The Python suite builds the store of a fork choice case and checks the update on the full and the empty parent at Gloas and Heze.

### Honest builder

From Gloas, `Consensus/HonestBuilder.lean` holds the bid and the envelope of an honest builder, and the signatures on them.
The payload, its requests and the commitments of its blobs come from the execution layer.
The builder chooses the slot, the fee recipient and the value of its bid, and from Heze the bits of the inclusion lists.
`getExecutionPayloadBid` takes the parent hash, the block hash, the RANDAO mix and the gas limit of the bid from the payload.
Its parent root is the root of the latest block header of the state, and it asks for no payment on the execution layer.
`getSelfBuiltExecutionPayloadBid` gives the bid of a proposer that builds its own payload the reserved builder index, no value and the signature at infinity.
`getExecutionPayloadEnvelope` names the root of the block of the bid, the parent of that block and the builder of its bid.
The theorems are in `Consensus/Proofs/HonestBuilder.lean`.

`getExecutionPayloadBid_eq_ok_iff` states each field of a bid.
`getExecutionPayloadEnvelope_eq_ok_iff` states each field of an envelope.
`checkBidBuilder_of_getSelfBuiltExecutionPayloadBid` shows that a self-built bid passes the checks of the builder of a bid on every state.
`getExecutionPayloadEnvelope_checks` takes a block from Gloas that passes block processing, with a bid that a builder built from a payload.
The block must commit to the root of the state after it.
The theorem shows that the envelope of that payload passes the checks of the block root and of the parent root against that state.
It also shows that the envelope passes the checks of the builder, the mix, the gas limit, the block hash and the root of the requests.
It shows that the payload builds on the latest block hash, and that the slot of the bid is the slot of the state.
It assumes that the vectors whose length the preset sets have a positive length, as the root of the block needs.
It rests on `BeaconBlock.hashTreeRoot_header`, which shows that a block has the root of its header.
It also rests on `latestBlockHash_processBlock`, which shows that from Gloas the latest block hash after a block is the parent hash of the latest bid.
`latestExecutionPayloadBid_processBlock` shows that from Gloas a block leaves its own bid as the latest bid.
`latestBlockHeader_processBlock` shows that from Gloas a block leaves its header, with a zero state root, as the latest block header.
These rest on `PayloadInputs`, the fields that the checks of a payload and of a bid read.
From Gloas the parent, header, RANDAO and bid steps each change one of them, and the other steps keep them all.
No theorem covers the signature, the time or the withdrawals of the envelope, or the answer of the execution layer.

The Python suite builds the envelope of a fork choice case at Gloas and Heze from its block, payload and requests, and compares it with the envelope of the case.
It also builds the self-built bid of that block and compares it with the bid of the block.

### Slashing protection

`Consensus/SlashingProtection.lean` holds the slashing protection of a signer, and the interchange file of EIP-3076 that moves it between clients.
At the pinned text of the EIP its status is Last Call.
A signer checks a block against the first two conditions of the EIP, and a vote against the last three.
The theorems are in `Consensus/Proofs/SlashingProtection.lean`.

`checkBlockSigning_eq_ok_iff` and `checkAttestationSigning_eq_ok_iff` state exactly when each check passes.
`signBlocks` and `signAttestations` model a signer that checks each message against its record and then records it, from any starting file.
`signingRoot_eq_of_signAttestations` shows that two votes of such a signer that `isSlashableAttestationData` forbids together have the same signing root.
`signingRoot_eq_of_signBlocks` shows that two block headers of one slot that it signed have the same signing root.
`signingRoot_eq_of_processProposerSlashing` shows that the two headers of a valid proposer slashing, both signed by it, are different headers with one signing root.
These theorems hold for every function that gives the signing root of a message.
They assume only that every check of the signer passed.
So a slashable pair of signed messages needs a collision of the signing root, and no theorem bounds the chance of one.

`isSlashableWith_eq_false_of_signAttestations` shows that each signed vote is not slashable with a vote of the starting file, as a record sees it.
A record holds the epochs of a vote and maybe its signing root, not its data.
So that comparison reads a double vote through the signing root, and counts a record without a root as a different vote.

A file may also keep only the latest messages of a key, as the [minimal strategy](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#supporting-different-strategies) of the EIP does.
`lt_slot_of_signBlocks` shows that if each block of the file is after a slot, so is each block signed from it.
`processProposerSlashing_ne_ok_of_signBlocks` concludes that no valid proposer slashing pairs such an older block with a signed block, since both headers of one have the same slot.
`isSlashableAttestationData_eq_false_of_signAttestations` shows that no signed vote is slashable with a vote older than each vote of the file.
An older vote has a source at most, and a target before, those of each vote of the file.
Each of these theorems needs the file to hold one or more messages of its kind for the key.
A vote with the target of a kept vote is not older, so the theorem on votes says nothing about it.
The signer of these theorems records every message it signs, so a signer that prunes as it goes is not covered.
`mem_blocksOf` and `mem_attestationsOf` show that the messages of a key are those of its own entries.
The proofs read only conditions 2, 4 and 5, through `lt_slot_of_checkBlockSlot`, `le_sourceEpoch_of_checkSourceEpoch` and `lt_targetEpoch_of_checkTargetEpoch`.
No theorem says what conditions 2, 4 and 5 guarantee across two imported files.
The record merges both files, so its checks use the least slot and epochs over both, not those of the second file.
So a message in a gap between the two passes, though the EIP [says](https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3076.md#advice-for-complete-databases) that signing it violates conditions 2, 4 and 5.
A message that the key signed in such a gap, and that neither file keeps, is not older than all the kept ones, so these theorems do not cover it.

`readUInt64_uint64Json` and `readBytes_bytesJson` show that each integer and each byte string of a file reads back as written.
`ofJson_toJson` shows that a whole file reads back as itself from the document that `toJson` writes, whatever its records.
No theorem says what `ofJson` does on a document that another client wrote.

The Python suite checks each condition and each malformed field against cases worked out from the EIP.
With release archives enabled, it runs the 38 interchange tests of `eth-clients/slashing-protection-interchange-tests` as a signer that keeps every message.

### Optimistic sync

`Consensus/ForkChoice/OptimisticSync.lean` holds the optimistic sync from Bellatrix: the blocks that a node imports before the execution layer judges their payload.
An optimistic store keeps their roots beside the blocks of the node, and the rules read only that store.
The theorems are in `Consensus/Proofs/ForkChoice/OptimisticSync.lean`, and most assume only that their function succeeds.

`isOptimisticCandidateBlock_eq_ok_iff` states when a block may be imported optimistically: its known parent carries a payload, or its slot is far enough before the clock.
`latestVerifiedAncestor_spec` shows that, before Gloas, the latest verified ancestor of a block is reached through optimistic blocks only.
The same theorem shows that this ancestor is not optimistic, or has the zero parent root.
`onValidPayload_spec` shows that a valid payload removes exactly the roots of its payload chain from the optimistic set.
`onInvalidatedPayload_spec` shows that the first invalid block removes exactly the optimistic roots whose payload chain holds it.
`payloadChain_of_lt_glamsterdam` shows that before Gloas the payload chain of a block is its whole chain, so these are its known ancestors and descendants.
`isOptimisticRestrictedDomain_iff` lists the seven domain types under which an optimistic validator may not sign.

The rule of the latest valid hash in `Consensus/ForkChoice/Optimistic.lean` names the first invalid block.
The theorems here take that block as given.
No theorem relates the optimistic set to the blocks that the store of the fork choice removes.
A node is optimistic when its head is optimistic, or when invalid payloads left its block tree with no viable branch.
`isOptimisticNode_of_isHeadOptimistic` shows that, at every fork, the first case alone makes an optimistic node.
`isOptimisticNode_of_not_isHeadOptimistic` shows that, before Gloas, the second case needs a block that the fork choice dropped at or above the justified block.
So a tree that empties with nothing invalidated does not count.
This assumes that the optimistic store holds only blocks that the fork choice accepted.
The rule approximates the guide, which asks that every viable branch was invalidated: one invalidated block above the justified block is enough.
EthLib counts a dropped justified block as no viable branch, a choice of its own.
`hasNoViableBranch_eq_ok_true_iff` shows that, with the justified block known and the filter successful, no viable branch means that no leaf above it passes the viability filter.
`filterNodeTree_eq_nil_iff` gives the same fact for the filtered tree of any node.
The re-run of the merge block checks is not defined, nor the answer to an execution layer that fails to respond.

From Gloas a block carries a bid, and its payload arrives later in an envelope.
The optimistic sync guide has no Gloas text, and its tests stop before Gloas.
EthLib therefore reads the Bellatrix guide at Gloas, a choice of its own.
A root of the optimistic set then names a block whose payload was imported optimistically, as the Gloas gossip rules key a payload status by block root.
A block carries a payload when its bid names a nonzero block hash; `isExecutionBlock_of_glamsterdam` states it.
`payloadChain_of_glamsterdam` shows that the payload chain is the chain of the block, filtered by the block hashes that the bids name.
`payloadChain_links` shows that each root of a payload chain builds on the payload of the next one, as the fork choice sees a full parent.
`parentRoot_mem_payloadChain_iff` shows that the parent of a block is on its payload chain exactly when the fork choice sees the parent as full.
`payloadChain_suffix` and `mem_payloadChain_trans` show that the payload chain of a block holds the payload chain of each of its roots.
`payloadChain_of_find?_some` shows that the payload chain of a block goes on at the first ancestor whose bid names the parent block hash of its bid, with the chain and the payload chain of that ancestor found.
`payloadChain_of_find?_none` shows that it is the block alone when no ancestor is named.
So it reaches every payload that the block builds on among the known blocks of its chain, through any number of blocks, full or empty.
A payload that builds on an invalid payload in that way leaves the set.
A block built on its parent without the payload of the parent does not hold that payload on its payload chain.
So its own optimistic payload stays when only the payload of the parent is invalid.
From Gloas the head of the fork choice is a block with or without its payload, so the optimistic store keeps the status of the head.
A full head reads the payload of its block, an empty head the payload its block builds on, and a pending head both; `isHeadOptimistic_of_full`, `isHeadOptimistic_of_empty_of_named` and `isHeadOptimistic_of_pending_of_optimistic` and `isHeadOptimistic_of_pending_of_not_optimistic` state it.
The search of the head never stops at a pending node, so reading both for a pending head is a choice of EthLib, the cautious one.
`isHeadOptimistic_of_empty_of_unnamed` shows that an empty head whose bid names no known payload fails with `payloadNotVerified`.
That is the case of an empty first block of Gloas, whose bid builds on a payload of Fulu, which a store of one fork never holds.
The rule fails there rather than call that payload verified, so the head rule and the latest verified ancestor agree.
From Gloas the latest verified ancestor takes a node, and reads only the payloads that the node holds.
A full node holds every payload of its payload chain, and an empty or pending node holds all but its own.
`latestVerifiedAncestor_ne_root` shows that a node without its own payload is never its own verified ancestor.
So a pending node reads as full or empty for the head, and as empty for the ancestor: each reading is the cautious one.
The status of a node is an assumption: a full node must name a payload that the store holds, and the rules do not check it.
The optimistic store follows the fields of the guide, which do not record the payloads held; the search of the head returns a full node only for a held payload.
`latestVerifiedAncestor_of_glamsterdam` shows that the answer is the first of those payloads that is not optimistic, with every one before it optimistic.
`latestVerifiedAncestor_eq_error_of_optimistic` shows that it fails with `payloadNotVerified` when all of them are optimistic, or when there is none.
Before Gloas the walk returns an optimistic genesis block; from Gloas it never returns an optimistic payload, a choice of EthLib.
From Gloas the rule of the latest valid hash is not defined, and the second case of an optimistic node is not yet specified.
That case needs the removal of an invalid payload from the store of the fork choice, which is not defined from Gloas.
`isOptimisticNode_of_glamsterdam` shows that the rule then fails when the head is not optimistic.
`isOptimisticNode_of_isHeadOptimistic_error` shows that it fails as the optimism of the head does.
The store holds the blocks of one fork, so a payload chain does not cross from Gloas into Fulu.
From Heze the store also records whether a payload satisfies the inclusion lists of the slot before.
The Heze guide derives that answer from the status that the execution layer gives a payload.
The verdict of the execution layer follows from the same status.
`BlockSources.withPayloadStatus` puts the status into the sources that the handlers read.
For a payload not yet validated, its execution layer accepts every payload and the payload satisfies its lists.
For an invalidated one, it rejects every payload and the payload does not satisfy them.
`Store.isPayloadInclusionListSatisfied_of_notValidated` shows the answer `true` for an envelope that the handler accepts.
`Store.onExecutionPayloadEnvelope_ne_ok_of_invalidated` shows that an invalidated payload is never kept.
A status outside the three of the guide counts as invalidated, a choice of EthLib: such a payload is never kept.
The export rejects such a status before any step runs.
`Store.recordValidatedInclusionListSatisfaction_satisfied` shows that a payload that turns valid takes the answer that the execution layer gives with its verdict.
`Store.recordValidatedInclusionListSatisfaction_eq` shows that nothing else in the store changes, and `Store.recordValidatedInclusionListSatisfaction_other` that every other answer stays, those of its ancestors among them.
The store of the fork choice does not keep the status of a payload, but the optimistic store does.
`OptimisticStore.onValidatedPayload_ok` shows that the move to valid succeeds only for an optimistic payload, which then leaves the optimistic set as a valid payload does.
The Python suite checks each rule on Bellatrix blocks built in the test, with roots from the SSZ export.
At Gloas it checks the execution block, the candidate rule, the two payload answers and the latest verified ancestor.
It checks the optimistic head of each status on a pinned Gloas fork choice case, and that the second case is refused.
At Heze it checks the answer on the inclusion lists for each status, and once the payload turns valid, on a pinned Heze case.

### Light client

A light client accepts an update that the sync committee signed, and moves its store by it.
`Consensus/Proofs/LightClient/Authenticate.lean` states what an accepted update proves.

`validateLightClientUpdate_proves` lists the checks that an accepted update passed.
At least the minimum of bits of its aggregate are set.
The signature check accepts the keys of those members on the signing root of the attested header.
The finality branch and the branch of a carried next committee verify against the state root of that header.

`validateLightClientUpdate_finalized` takes any value whose root is that state root, such as the beacon state of the attested block.
Its node at the index of the finality branch is the root that the update proves.
That root is the root of the finalized beacon header, or zero at the genesis slot.
Otherwise the search `findBranchCollision` over the two climbs returns two different messages with one SHA-256 hash.
`validateLightClientUpdate_nextSyncCommittee` states the same for the root of the next committee.
`lightClientGindices_eq` shows that each index is the generalized index of the path of its field in the type of the beacon state, at every fork from Altair and at every preset.
It joins two theorems that name the ordinals of the fields.
From Altair to the forks before Gloas, `lightClientGindices_eq_of_lt` shows the same three indices.
From Gloas the state is a progressive container, and `lightClientGindices_eq_of_glamsterdam_le` shows them too.
On a state of any fork from Altair, `BeaconState.nodeRoot_finalizedCheckpoint_root` reads the finality node as `state.finalizedCheckpoint.root` itself, since a 32-byte value is its own root.
`BeaconState.nodeRoot_nextSyncCommittee` and `BeaconState.nodeRoot_currentSyncCommittee` read the committee nodes as the roots of those fields, which always exist.
These theorems take the lawful SSZ type of the state as an argument, and the committee theorems also take a nonempty committee.
Instance search finds that lawful type at the mainnet and minimal presets.
`validateLightClientUpdate_finalizedCheckpoint` joins the finality result to these nodes.
Take an accepted update, and a beacon state whose root is the attested state root.
The proved root is then the root in the finalized checkpoint of that state.
Otherwise `findBranchCollision` returns a SHA-256 collision.
`validateLightClientUpdate_nextSyncCommittee_state` states the same for the next committee.
Both assume that the index of the slot is the index of the state's own fork.
The client then reads the state with the layout of that fork.
`initializeLightClientStore_currentSyncCommittee` states the same for a new store.
The store keeps the committee that its bootstrap proves.
Its root is the root of the current committee of the trusted state, or the search returns a collision.
It makes the same assumption on the index, at the slot of the bootstrap header.
`stateForkAtSlot_gindices` discharges that assumption from the fork schedule.
Take a slot whose scheduled fork is from Altair, and a store of that fork or later.
The schedule must start Electra no later than Fulu, and Gloas no later than Heze.
The client then reads the three nodes at the indices of the fork of the slot, so at the deeper indices of Electra from Electra.

From Capella a header also carries the execution data of its block, which `Consensus/Proofs/LightClient/Execution.lean` binds to the block.
From Capella to Fulu, `isValidLightClientHeader_executionPayload` takes a valid header at a slot from Capella.
It also takes a body of a fork from Capella to Fulu whose root is the body root of the header.
The execution root of the header is then the root of the execution payload of that body, or `findBranchCollision` returns a SHA-256 collision.
`BeaconBlockBody.nodeRoot_executionPayload` reads node 25 of such a body as the root of its payload.
Like the state theorems, these take the lawful type of the body.
`ExecutionPayload.hashTreeRoot_header` shows that before Gloas the header of a payload has the root of the payload.
So `isValidLightClientHeader_execution_eq` takes the binding to the fields, for a body of the fork of the header, at a slot from Capella, and from Deneb for a header from Deneb.
The execution header of the light client header is then the header of the payload of the body, field by field.
Otherwise a search over the two branch climbs, or one over the hash inputs of the two header roots, names a SHA-256 collision.
From Deneb, `isValidLightClientHeader_blobGas` applies this to the blob gas used and the excess blob gas, at a slot from Deneb.
The schedule must start Capella no later than Deneb.
`isValidLightClientHeader_blobGas_zero` shows that a valid header of an earlier slot has zero for both.
From Gloas, `isValidLightClientHeader_parentBlockHash` binds the block hash of a header at a slot from Gloas to the parent block hash of the bid of a Gloas body.
`isValidLightClientHeader_executionBlockHash` binds it, for an earlier slot from Capella, to the block hash of the payload of a body from Capella to Fulu that is from Deneb exactly when the slot is.
The headers that the client checks are valid: `initializeLightClientStore_header_valid`, `validateLightClientUpdate_attestedHeader_valid`, and `validateLightClientUpdate_finalizedHeader_valid` after the genesis slot.
The index theorems `executionPayloadGindex_eq`, `payloadHeaderBlockHashGindex_eq`, `executionBlockHashGindex_eq` and `executionBlockHashGindexGloas_eq` hold at every preset.

The signature theorems assume `SignatureChecks.AggregateSound`, listed in A4.
Under it, `validateLightClientUpdate_signed` shows that every member whose bit is set signed the signing root.
`validateLightClientUpdate_signed_outside` adds that a set of keys holding fewer seats of the committee than there are signers leaves a signer outside the set.
`SignatureChecks.not_aggregateSound_acceptAll` shows that the assumption has content: the checks that accept every signature do not meet it.
`LightClientForgery.forgeAdvantage_le` bounds how often a forger makes the light client accept an aggregate with one designated honest member's bit set, on a root that member never signed.
It assumes the random oracle model, a proof of possession for every signer, and at most `q` and `qK` hash calls; the bound is small if co-CDH is hard and the solver built from the forger is efficient, which no theorem bounds.
It is not a proof of `AggregateSound`, and Ethereum's keys carry deposit signatures, not those proofs.
The bound protects that member's bit only.
Covering every honest member of a committee needs a guess among them, losing up to a factor of the number of honest seats; that step is not proved.
Updates signed by corrupted members alone are still accepted, so the safety of headers also needs an honest supermajority of the committee.
The reduction loses a factor `q`, the number of all message hash calls, and no theorem bounds its running time.
A deposit signature cannot simply count as a proof of possession here: it is a signature under the message hash, and Ristenpart and Yilek ([ePrint 2007/264](https://eprint.iacr.org/2007/264)) show that such proofs fail when the honest key signs chosen messages.
With the signing oracle of this game, the honest key's signature on the deposit message of a rogue key `x g1 - pk` gives that key a valid deposit signature.
The header slots of the store never move back.
`applyLightClientUpdate_finalizedSlot_le`, `processLightClientUpdate_finalizedSlot_le` and `processLightClientStoreForceUpdate_finalizedSlot_le` show that the finalized slot never decreases.
`applyLightClientUpdate_optimisticSlot_le`, `processLightClientUpdate_optimisticSlot_le` and `processLightClientStoreForceUpdate_optimisticSlot_le` show the same for the optimistic slot.
`applyLightClientUpdate_slot_order`, `processLightClientUpdate_slot_order` and `processLightClientStoreForceUpdate_slot_order` show that a finalized slot at or below the optimistic slot stays there.
`initializeLightClientStore_headers` shows that a new store starts with one header for both.
`LightClientStore.upgrade_beacon` shows that the upgrade of a store to a later fork keeps both beacon headers, so it keeps both slots too.
So every store that these four steps reach from a bootstrap keeps that order.
No theorem links an honest signer to the canonical chain; that is a property of the validators, not of the protocol text.

### Casper FFG

Casper FFG finalizes checkpoints, each a block with an epoch, from the votes of validators.
The model in `Consensus/Proofs/Models/Ffg/` follows Casper FFG §2 and Gasper §4 and §8.6.
Each checkpoint has its own validator set, as each block has in Gasper §8.6, and a link counts the stake of the set of its target.
A supermajority link weighs its voters with one stake for each validator, as Gasper §8.6 assumes.
A constant validator set then gives the model of Casper FFG and Gasper §4.

A slack link weakens a supermajority link by a second set for its target: the bound adds twice the stake of the target set outside that second set.
The beacon chain needs that slack, since it weighs the attesters of the previous epoch against the active balance of the current one.
A slack link also lets each checkpoint have a set of weights, each a stake for every validator, and holds when its bound holds under one of them.
A refinement from the beacon state puts in that set the effective balances of each state at the last slot of the epoch of the checkpoint or of the next one, when that state records the root of the checkpoint for its epoch.
So a balance may change from one checkpoint to the next, and two branches that justify one checkpoint from two states both fit, where one stake function could not.
Nothing excludes other weights from a set, and the zero weights make every ordered link a slack link, so the bounds say something only when every choice of weights in each set stays close to the reference weights.
`accountable_safety_dynamic_slack`, `accountable_safety_reference_slack` and `accountable_safety_of_change_slack` (`AccountableSafety.lean`) take slack links, with a validator set and a set of weights for each checkpoint.
They measure every stake under reference weights, and lose the slack of the two links that they find and the change from the reference weights to the weights under which those links hold.
In that change a gain of weight counts once, like an activation, and a loss twice, like an exit.
Nothing ties the second sets to the validator sets, so these bounds say something only when the slack is bounded, as the exit churn would bound it; no theorem states that bound yet.
The churn would not bound the change of weights alone: the inactivity leak, penalties and slashings lower effective balances outside any churn, so a bound over a window also needs a budget for those losses.

`accountable_safety_dynamic` (`AccountableSafety.lean`) is Gasper Theorem 8.3.
It takes two finalized checkpoints whose blocks conflict.
Then two justified checkpoints, with epochs between those of the two finalized ones, have the following property.
Validators of both their sets broke a slashing condition, and their stake is bounded below.
The bound is two thirds of the stake of one set, less one third of the stake of the other, less the stake that activated into the first set or exited from the second since any reference set.
Gasper states it with a maximum and divisions by three; the theorem states its two terms, multiplied by three, in natural numbers.
If one of the two sets has no stake, both bounds hold with no slashable validator.
The reader does not choose the two checkpoints, so the theorem says something only when every justified checkpoint between the two finalized epochs has a set with positive stake.

`accountable_safety_reference` (`AccountableSafety.lean`) restates the first bound against one fixed reference set `V₀`, such as the set of a trusted checkpoint.
The stake of `V₀` is at most three times the slashable stake, plus the change of each of the two sets since `V₀`.
The change of a set counts the stake that joined once and the stake that left twice.
`accountable_safety_of_change` assumes that the change of every justified set between the two finalized epochs is at most `b`, and bounds the stake of `V₀` by three times the slashable stake plus `2 b`.
`accountable_safety_of_steps` assumes that every justified checkpoint between the two finalized epochs has a set reached from `V₀` in at most `n` steps.
Each step changes the set by at most `d` in that measure, so the stake of `V₀` is at most three times the slashable stake plus `2 n d`.
As above, the reader does not choose the two checkpoints, so the hypothesis covers every justified checkpoint between the two finalized epochs.
For a step of one epoch, `d` bounds the stake that activates plus twice the stake that exits, the source of a consolidation included.
The churn queues carry unused churn to later epochs, so such a bound can fail in one epoch while the total over a window holds; `accountable_safety_of_change` takes that total.
The model does not follow withdrawals; the specification covers them with the withdrawability delay in the weak subjectivity period.
These theorems take one stake for each validator, so a top-up, a consolidation or a penalty of a validator that stays in the set is outside them; the slack forms above count it as a change of weights.
No theorem yet derives those steps from the beacon state.

`accountable_safety` (`AccountableSafety.lean`) takes one validator set for every vote, and follows from `accountable_safety_dynamic`.
Then validators with at least one third of the stake broke a slashing condition.
With a total stake of zero this holds for every set of votes, so the theorem says something only for positive stake.

`plausible_liveness` (`PlausibleLiveness.lean`) takes honest validators in every validator set, with at least two thirds of its stake.
The votes so far are finite, the stake of each set is positive, and no honest validator is slashable.
Each honest vote comes from a justified source.

Then there is a justified checkpoint with the following property.
For every block whose chain contains its block, the honest validators can add votes that finalize that block.
The block is finalized at an epoch above every justified epoch so far.
The new votes come from justified sources, and no honest validator becomes slashable.

A vote names the validator that signed it, so both theorems assume that no one forges a vote.
Below, the votes of the model come from the attestations that the blocks of a chain apply, but neither theorem is yet applied to them, so neither is yet about what a client runs.

These pieces of that link exist.
`FfgVotes.lean` relates the slashing conditions of the beacon chain to those of the model.
`justificationTest_iff_stake` (`Consensus/Proofs/Transition/FfgStake.lean`) reads the test of justification as a comparison of stakes.
There the stake of a validator is its effective balance, and the indices count as a set.
It needs an active stake of more than one and a half increments.
Up to that bound, the beacon chain can justify with no vote at all, since a total balance is never below one increment.
`processAttestationAltair_targetFlag` (`Consensus/Proofs/Transition/TargetFlags.lean`) covers one attestation from Altair.
A timely target flag that it sets belongs to an attester of an indexed attestation that passed the checks of the step.
With the BLS checks, the aggregate signature verifies under keys that include the key of that attester.
Reading this as a signature by that attester assumes that BLS aggregate signatures cannot be forged.
The source of that attestation is the justified checkpoint of the epoch of the flags.
Its target is the checkpoint of that epoch, with the block root that the state records for its first slot.
A vote is a pair of a validator and attestation data.
An attestation casts a vote for each validator that its bits show in its committees, with its data (`attestationVotes`, `Consensus/Proofs/Transition/TargetVotes.lean`).
A block casts the votes of its attestations, read in the committees of the state before the block (`blockVotes`).
`processBlock_attestationSplit` (`ActiveKept.lean`) shows that the block reads those same committees when it processes each attestation.
The steps before the attestations keep activity up to the current epoch and write only the RANDAO mix of the current epoch, which the seeds of the previous and current epochs do not read.
That needs more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes.
`voteFrame_processBlock` then shows that a block sets a target flag only from one of its votes, for the link of the epoch of the flag at the position of the flag.
The block keeps the slot, the block roots and the justified checkpoints.
So `TargetFlagsVoted.of_voteFrame` keeps each target flag backed by a vote for its link, from the earlier votes or those of the block.
`TargetFlagsVoted.of_advanceSlots` (`Consensus/Proofs/Transition/TargetSlots.lean`) carries the same fact across the slots, the epoch step included.
The slot step writes one block root, so the roots at the first slots of the current and previous epochs stay.
That needs at least one slot per epoch, and a buffer of roots that covers two epochs, as both presets do.
The epoch step moves the flags of the current epoch to the previous one, and justification moves the current justified checkpoint to the previous one.
Justification does not run in the first two epochs, so the theorem assumes the two justified checkpoints equal there, and the slots keep that.
The genesis state built from deposits has equal justified checkpoints, and the slots, the blocks and every upgrade keep that (`Consensus/Proofs/Transition/TargetUpgrades.lean`).
`TargetFlagsVoted.of_processUpgrades` carries the target-flag fact across the upgrades from Altair on.
Before Altair, `PendingVoted` (`Consensus/Proofs/Transition/TargetPending.lean`) says the same of each pending attestation of the two epochs, across attestations, blocks and slots.
It relies on the beacon committees of those epochs staying fixed while the epoch is recent (`Committees.lean`), which needs more than `MIN_SEED_LOOKAHEAD + 2` epochs of RANDAO mixes.
`TargetFlagsVoted.of_upgradeToAltair` (`TargetUpgrades.lean`) builds the target flags of the first Altair state from such pending attestations.
A vote of a block is evidence that its validator signed the data only with the BLS checks, and under the assumption that BLS aggregates with proofs of possession cannot be forged, since the block accepts the attestation only when the signature checks accept its aggregate signature.

`processJustificationAndFinalization_linkWithChurn` (`Consensus/Proofs/Transition/FfgJustification.lean`) refines one epoch step.
It takes the target-flag fact from Altair, the pending-attestation fact before Altair, and an active stake of more than one and a half increments.
The two facts are needed at the state after the slot step where justification runs; `advanceSlot_slackJustifiedCheckpoints` (`FfgSlack.lean`) reaches it from the state before the slot.
The validator set of a target is the active set of its epoch, as each checkpoint has its own set in Gasper §8.6.
Each validator weighs its effective balance in the state before the step.
The votes of the model must hold those of a set of votes from which the target flags and the pending attestations come.
The step keeps the current justified checkpoint, or replaces it by the checkpoint of the previous or the current epoch, whose test passes; the link goes from the justified checkpoint of that epoch to the new checkpoint.
Then twice the stake of the set of the target is at most three times the stake of the voters of the link, plus a term of churn.
The term is twice the stake of that set outside the active set of the current epoch, because the step divides by the active balance of the current epoch.
`linkWithChurn_of_test` gives the same bound for one epoch whose test passes, when each counted attester is active in that epoch and cast a vote of the set for its link.
`TargetFlagsVoted.attester` from Altair and `PendingVoted.attester` before it give that fact.
With them, `linkWithChurn_of_test` would give the bound for the previous epoch when both pass, whose bit the finalization rules read; no theorem states that yet.
For the current epoch the term is zero.
For the previous epoch, `exists_exitEpoch_eq_of_mem_sdiff_active` shows that it counts only validators that exit at the current epoch, when the registry stays within the limit of the preset.
The theorem reads the unchecked active indices, and the bound makes each index equal to its registry position.
The exit churn bounds that stake, but no theorem states that bound yet.
So one step gives the stake condition of a supermajority link of the model, up to that term.
The beacon chain leaves slashed attesters out, and the model counts them, so the converse does not hold.
The ancestry of the blocks of the link is not shown yet.

`processJustificationAndFinalization_slackJustifiedCheckpoints` (`Consensus/Proofs/Transition/FfgSlack.lean`) turns one step into a slack link of the model.
If the two justified checkpoints of the state before the step are slack-justified, so are those of the state after it.
A new current justified checkpoint must match the state of that step.
Its set is the active set of its epoch, its set of weights holds the effective balances, and each member of both of its sets is active in the current epoch.
In that single step, only the step that changes the current justified checkpoint reads them, so the effective balances may change before a later step.
Two branches can justify the same checkpoint in different states; its set of weights holds the balances of both, but its validator set must be the active set of its epoch in both states, and no theorem shows that yet.
That single step asks a match only for the new current justified checkpoint; the hypotheses of a chain step ask it for both recent epochs at each end of an epoch, since finalization also reads a previous target that the same step justifies.
The step also needs the previous justified epoch below the previous epoch once justification runs, and the source block of each recent link in the chain of its target block.
`slackJustifiedCheckpoints_of_chain` (`Consensus/Proofs/Transition/FfgSlackChain.lean`) carries these steps along a chain from the genesis state built from deposits, for a set of votes that holds the votes of each block step.
`slackJustifiedCheckpoints_activeSetAt_of_chainSteps` (`FfgSlackActive.lean`) takes the votes that the block steps of the run cast, the active sets and the effective balances.
Its step asks only the active stake, the order of the blocks and the preset.
The order of the blocks asks that the map from roots to blocks keeps in order the roots that a state records at two consecutive slots, and the zero root before the root of slot zero (`rootLinks`, `Consensus/Proofs/Transition/FfgRoots.lean`).
Two consecutive slots record the same root, or a block and its child, since the header check makes the parent root of a block the root recorded at the slot before it; no theorem states that yet.
Without a collision of header roots, such pairs order the roots by ancestry.
`RootsAbove.of_chainStep` then keeps each justified checkpoint below every root that the state records from its epoch on, which gives the source block of each recent link in the chain of its target block.
`slackJustifiedCheckpoints_chainRoot_of_chainSteps` (`FfgSlackActive.lean`) takes the roots themselves as the blocks of the model, ordered by the links of every state that genesis reaches (`ChainRoot`), so the order holds by construction and the step asks only the active stake.
That order does not depend on the last state, so two branches from one genesis share it.
It holds the links of every reachable state, so it also holds every collision of header roots among reachable headers, and such collisions exist by counting.
A collision of header roots makes two conflicting blocks comparable, so this order does not serve a safety theorem for two chains; that needs the order of the states of the given runs, with a named search for a collision.
`processJustificationAndFinalization_slackBits` and `advanceSlot_slackBits` (`Consensus/Proofs/Transition/FfgFinality.lean`) keep the finalized checkpoint slack-finalized through one step, by the four rules of finalization read as 1- or 2-finalization (Gasper Definition 4.9).
They carry two facts in the bits of justification: a set bit 0 gives a slack link from the previous to the current justified checkpoint, and a set bit 1 makes the checkpoint two epochs back slack-justified.
They need a buffer of roots of three epochs, which both presets have.
`slackFinalized_of_chainSteps`, `slackFinalized_activeSetAt_of_chainSteps` and `slackFinalized_chainRoot_of_chainSteps` (`FfgFinalityChain.lean`) carry this along a chain from the genesis state built from deposits, with the sets, weights and votes of the theorems on justified checkpoints.
The weights of a checkpoint then hold the effective balances of each state before a slot that ends its epoch or the next one, on a run between genesis and the last state, when that state records the root of the checkpoint for that epoch.
That genesis state exists only before Altair, so a chain whose genesis is later is out of scope.

### Engine API

The Engine API is the interface through which the consensus layer drives the execution layer.
`EthLib/Engine/` holds the checks of `engine_newPayload`, versions 1 to 5, and the choice of the head in `engine_forkchoiceUpdated`, versions 1 to 3.
It also holds the execution engine that the beacon chain calls.
The theorems are in `Engine/Proofs/`.

A payload and its block determine each other.
`ofBlock_toBlock` (`Proofs/Block.lean`) shows that a payload whose block hash is the hash of its header is the payload of its block.
`toBlock_ofBlock` shows that a block of the shape that a payload gives comes back from its payload.
`toBlock_shape` gives that shape: no ommers, a difficulty and a nonce of zero, and the RANDAO mix in place of the mix digest.

The checks of `engine_newPayload` answer by the version of the method and the fork of the payload.
`exists_acceptsFork_iff` (`Proofs/NewPayload.lean`) shows that some version takes a fork exactly when the fork is from Paris to Glamsterdam.
`status_of_checkNewPayload` shows that a payload that fails the checks is `INVALID`, or `INVALID_BLOCK_HASH` only at version 1, with no latest valid hash.
So `status_of_newPayloadWithoutState` shows that the method without the parent's state never answers `VALID`.
One C export runs that method, and a second runs the method on a chain that holds the parent's state.
With the state of a chain, `valid_iff_of_newPayloadOnChain` shows that the answer is `VALID` exactly when a block and a state come back.
`of_newPayloadOnChain_some` adds that such a block passed the checks and the state transition, to that state.
`newPayloadOnChain_of_stateTransition_ok` shows the converse for a block whose parent is the last block of the chain.

The JSON decoders read back the hex encoding of any bytes (`bytesOf_hexString`, `Proofs/Json.lean`).
An address decodes exactly from `0x` and two hex digits for each byte, in either case, whose lowercase forms encode the address (`address_eq_ok_iff_map_toLower`).
A 64-bit number decodes to `x` exactly when the number read with the bound `2^64` is `x` (`uint64_eq_ok_iff`).
A payload of version 4 decodes exactly when it holds the fields of version 4 and each part decodes (`payloadV4_eq_ok_iff`).
A field that appears at a fork decodes exactly when it is present from that fork on and absent before (`exists_since_iff`, `Proofs/ExecutionEngine.lean`).
So a decoded payload takes a fork exactly when its version is that of the fork (`exists_atFork_iff_of_anyPayload`).
Version 1 takes the forks before Shapella, version 2 takes Shapella and version 3 takes the forks from Dencun.

The theorems about `engine_forkchoiceUpdated` are in `Proofs/ForkchoiceUpdated.lean`.
`forkchoiceUpdated_valid` shows that a valid answer selects a valid head that the execution layer holds, with its safe and finalized blocks on its chain.
The exception is step 2 of the method, which `forkchoiceUpdated_of_belowFinalized` covers.
A valid head below the finalized block that the execution layer knows is `VALID` there, and the head does not change.
`forkchoiceUpdated_of_invalid` gives the answer for an invalid head, and `latestValid_eq_some_iff` with `getElem?_succ_chainOf` shows that its latest valid hash is the valid ancestor nearest the head.
In version 4, custody columns that decode never change the answer (`forkchoiceUpdatedCall_custody`), and without payload attributes every version gives the same answer (`forkchoiceUpdatedCall_of_null`).
The model has no timestamps, so it checks neither the fork of the payload attributes nor that their timestamp is above the head's.
For the same reason, version 2 takes both structures of the attributes at any time.
When the update applies a valid head, attributes whose fields fit no structure of the version give `-38003` (`forkchoiceUpdatedCall_eq_error_of_attributes`, with `payloadAttributesOfVersion_eq_error_iff` and `payloadAttributesOfJson_wrong_fields`), and when it applies none they are not read (`forkchoiceUpdatedCall_of_no_head`).
Version 1 names no code for a wrong structure, and the model gives it `-38003`, the answer of its step 9 for invalid attributes.
The OpenRPC description of the method makes the payload attributes optional, but the model asks for them, as `null` when there are none.

`executionEngine_accepts_iff` (`Proofs/ExecutionEngine.lean`) states when the execution engine accepts a payload request of the beacon chain.
The request lists must be well formed, and the payload must have a block at the active fork of the chain, which must be before Glamsterdam.
From Deneb, the blob transactions of that block must carry the versioned hashes of the request.
The block must pass the state transition.

No payload build is specified, so `engine_getPayload` has no definition, and the export refuses payload attributes on a new valid head.
The tree of known payloads and the known finalized block are inputs of each call, not state that the model keeps between calls.

### What cannot be proved yet

Some definitions cannot be unfolded by the kernel, so the kernel cannot evaluate them, and their intended computational properties remain unproved.
They come in three kinds.
A `partial` definition is defined by `partial` recursion.
An `opaque` one is an opaque constant.
A `reaches-opaque` one unfolds to an opaque constant, such as `Loop.forIn`, which `while` compiles to.

`lake exe check-decls` reports each one, and `scripts/check_decls_baseline.txt` lists those that remain, with the reason for each group.
The list below is generated from that file, and it is empty when none remains.

<!-- generated: unfoldable -->
<!-- end generated -->

## Gap A: does the definition say what the source and the client need?

### A1. A wrong definition

A definition can differ from its source while every theorem about it holds, because the theorems are proved about the definition, not about the source.
Three things guard against that.
Each definition is named and shaped after its source, so that a reader can compare them line by line.
The KZG and BLS vectors in `tests/cryptography/` match consensus-specs `v1.7.0-alpha.12` and `ethereum/bls12-381-tests` `v0.1.2` byte for byte, and EthLib produced none of them.
Finally, the consistency theorems on the constants, listed under BLS12-381, catch a wrong digit.

Two definitions also do what their sources do not.
The PeerDAS custody search fails after `2^16` node IDs in the export, where its source loops on, and no theorem bounds the steps it needs.
BLS key generation fails after 16 attempts, a bound that EthLib chose.
[The IRTF BLS draft, version 4, §2.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.3) and `HKDF_mod_r` of [ERC-2333](https://github.com/ethereum/ERCs/blob/be307c948f28897adb8f25afcc253c2c909de35d/ERCS/erc-2333.md#hkdf_mod_r) loop until the key is not zero.
The ERC-2333 master and child derivations reuse key generation, so they share the bound.
An attempt fails only when its 48-byte output is a multiple of `r`.

A run of slots of the consensus state transition divides by constants of the preset and of the configuration, such as the slots of an epoch, the increment of an effective balance and the quotient of the churn limit.
Python's integer division and remainder raise an error on a zero divisor, so the specification fails there.
In Lean a division of 64-bit integers by zero returns zero and a remainder returns the dividend, so with such constants a step can succeed in EthLib where the specification fails.
`Preset.DivisorsPositive` and `Config.DivisorsPositive` (`Proofs/Transition/Totality/Bound.lean`) name the presets and configurations whose divisors in a run of slots are positive, and the mainnet and minimal ones are proved to be such.
Block processing divides by further constants, such as the quotients of the slashing penalty and of the whistleblower reward, which these predicates do not list.
A theorem that a step succeeds takes a predicate only where its proof needs a positive divisor.
For a preset or configuration with a zero divisor, any theorem about a step that divides by it describes EthLib's transition, not the specification's.

The accessor that lists the active validators keeps a result where the specification fails.
The specification lists the active validators of an epoch by their indices, and builds each index as a `ValidatorIndex`, a 64-bit integer.
That construction rejects a value of `2^64` or more, so the specification fails when a validator at a registry position of `2^64` or more is active.
`getActiveValidatorIndices` returns a plain list and never fails; at such a position it would take the position modulo `2^64`.
Before Gloas the type of the registry bounds it by the limit of the preset, a 64-bit integer (`2^40` in the mainnet and minimal presets), so no position reaches `2^64`.
From Gloas the type of the registry has no length limit ([EIP-7688](https://eips.ethereum.org/EIPS/eip-7688#converted-types)).
A new validator still gets the size of the registry as its index, and that index must be below `2^64` (`getIndexForNewValidator_ok_iff`).
So a transition never adds a validator at a position of `2^64` or more, and only a starting state built outside the transition can hold one.

`getActiveValidatorIndicesChecked_eq_ok_iff` in `Consensus/Proofs/Accessors.lean` states the divergence exactly.
The checked read converts each active position as the specification does, and it gives EthLib's list exactly when every active position is below `2^64`.
The specification also converts the number of active validators to a 64-bit integer, and rejects a count of `2^64`, which a registry of `2^64` positions allows.
Such a registry can arise through the transition from Gloas, at least in principle.

The transition reads the active validators through `getActiveValidatorIndicesChecked`, which fails at an active position of `2^64` or more, as the specification does.
The shuffle of the beacon committees and the committee count of an attestation also fail at `2^64` active validators, so the transition agrees with the specification on the count of committees.
The churn limit of validators before Electra and the Phase 0 weak subjectivity period still convert the count of the pure list without a check.
Both run only before Electra, where the type of the registry keeps it within the limit of the preset (`BeaconState.registryWithinLimit_of_lt`).
There the count is below `2^64` (`length_getActiveValidatorIndices_lt`), so the conversion keeps its value (`toNat_length_getActiveValidatorIndices`) and agrees with the specification.
The genesis validity check, fork choice, gossip and the honest-validator duties call the pure list directly, and keep the difference.

Some official vectors expect more than a source says.
The transaction tests of ethereum/tests reject 43 results whose gas limit is `2^64`, or whose gas limit times gas price exceeds `2^256 - 1`.
No rule of the Yellow Paper rejects such a transaction alone, and EIP-7825 caps the gas limit only from Fusaka on.
EthLib accepts them, and the suite asserts that it does, as `tests/execution/ethereum_tests/README.md` explains.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
The ceremony theorem `checksSufficient_of_subgroupChecks` is one, and its hypotheses are listed under KZG.
Only the lemmas in `Proofs/Bls/PairingLaws.lean` and `Proofs/AltBn128/PairingLaws.lean` take `PairingLaws` as a hypothesis.
The BLS signature, consensus, KZG, PeerDAS, EIP-2537 and EIP-197 theorems need no such hypothesis.
`PairingLaws` is a `Prop`, never an axiom, so `lake exe check-decls` still sees only the standard axioms.
`pairingLaws` proves the law for BLS12-381, and `AltBn128.pairingLaws` proves it for alt_bn128.

The theorems in `Proofs/Transition/Totality/` show that the steps of a run of slots succeed, and each takes hypotheses that the specification does not state.
Each hypothesis narrows the states, presets or runs that the result covers.
Justification and finalization need two slots an epoch and a buffer of block roots that reaches the epoch before (`Preset.RootsReachPreviousEpoch`).
With one slot an epoch the specification itself can fail there.
Before Altair they also assume that the committees of the pending attestations can be computed (`PendingResolved`), which a block checked when it included them.
From Altair the rewards and penalties need `RewardsFit`, a set of bounds on the preset, the configuration, a budget of Gwei and a bound on the inactivity scores that the step reads.
They also need each effective balance at most the largest cap, the finalized epoch at most the previous epoch, and each balance and the sum of the effective balances within the budget.
The inactivity penalty multiplies an effective balance by an inactivity score, and a score grows by at most the score bias in each epoch.
So the bound on the scores limits the length of the run that the theorems cover.
On mainnet the bounds hold for a budget of `2^57` Gwei, about `1.44 * 10^8` ETH, and scores up to `2^23`.
From a score of zero, a score reaches `2^23` only after `2^21` epochs of missed targets, about 25 years at 32 slots of 12 seconds an epoch.
The specification itself overflows there: at 2048 ETH the product fails once a score passes about `9.0 * 10^6`.
The bound on the reward of a flag does not use the square root of the total active balance.
The validators that set a flag in the previous epoch include those whose exit epoch is the current epoch.
So their effective balance can exceed the total active balance of the current epoch, and only the budget bounds it.
The budget of `2^57` Gwei is about 84% of the largest that this bound allows.
Before Altair the rewards and penalties need `RewardsFitBeforeAltair`, a set of bounds on the preset, a budget of Gwei and a bound on the current epoch.
They read the root of the block at the slot of each vote that matches the target.
So they assume that each recent pending attestation is as inclusion in a block stored it (`PendingWellFormed`).
Its slot is then in the epoch of its list, its inclusion delay is not zero, and its proposer is a validator of the registry.
No theorem yet shows that this holds along a run: the preservation must be stated over the slot advance and block processing, and the nonzero delay needs a least inclusion delay of one slot, as mainnet and minimal have.
The inactivity penalty before Altair multiplies an effective balance by the delay of finality, which is at most the current epoch.
So the bound on the current epoch limits the length of the run that the theorem covers.
A proposer can earn a share of the base reward of each signer that it included.
So the bound on its reward is the bound on base rewards at the whole budget, as the effective balances of its signers sum to at most that.
On mainnet and minimal these bounds hold for a budget of `2^57` Gwei and `2^21` epochs.
The bound on the current epoch multiplies it by the largest cap at any fork, 2048 ETH, so it is conservative before Altair, where the cap is 32 ETH.

The builder payments of Gloas carry four hypotheses and one restriction.
`chainSteps_paysQuorum` proves that along a chain through the last slot of an epoch, each payment of the previous epoch that reaches its quorum is paid exactly once.
Paid means that the withdrawal of the payment joins the queue of the withdrawals of the builders.
The last slot of the epoch queues the withdrawals of exactly those payments.
A run of slots and blocks over the whole chain (`PaymentChain`) releases each of them, and releases no payment twice.
The withdrawals of such a run are fixed by the states that each step computes.
Its payments are fixed too, up to their order: a slot lists only payments that reach the quorum, and a block only the payment of its parent.
`paymentChain_of_chainSteps` proves that every chain inside one fork is such a run, and `PaymentChain.nodup` gives "at most once" for any such run.
The facts on the payments must hold at the first state, as `paymentFacts_upgradeToGloas` proves for the upgrade to Gloas.
These theorems also take a positive payment quorum (`PaymentQuorumPositive`), at least two slots in an epoch, and at most 2^40 entries in each registry at the last state.
`paymentQuorumPositive_presets` and `twoSlotsPerEpoch_presets` prove the first two for the mainnet and minimal presets.
For the validators, 2^40 is `VALIDATOR_REGISTRY_LIMIT`.
The registry of the builders has no limit in the specification, so for it the bound is an assumption, which matches `BUILDER_INDEX_FLAG`.
No theorem proves either bound along a chain.
The chain must stay inside one fork, from Gloas on, so a chain across the upgrade to Heze is not covered.
A run of payment steps relates two states of one fork, and carrying open payments through that upgrade needs a run across forks.
The four facts that the runs assume do hold through that upgrade, by `PaymentFacts.upgradeToHeze`.
The "at least once" half is stated for a chain split at the epoch step, which fixes the step that pays.
The quorum is read on the state that the epoch transition reaches before its step of the payments.
A bid whose payment a slashing cancels may still be paid by the late path of the bid, and then the run releases it once.

Whatever those hypotheses leave unproved is part of what a reader trusts.

### A3. Side channels

EthLib makes no constant-time claim.
`Hash/Keccak.lean` says it "is not intended to be constant-time", and the field arithmetic uses Lean's `Nat`, which gives no timing guarantee.
This matters where secret data is handled.

XMSS and leanSPHINCS `keyGen` and `sign` handle secret data.
The Python bindings expose all four, as `key_gen` and `sign` in each module, which take the secret seed.
BLS key generation, signing and the proof of possession handle secret data, and the Python bindings expose all three.
The bindings `derive_master_sk`, `derive_child_sk` and `derive_path` handle secret seeds or keys.
HMAC-SHA-256, HKDF and the Concatenation KDF take a secret key, input keying material or shared secret.
The Python bindings expose them as `hmac_sha256`, `hkdf_extract`, `hkdf` and `concat_kdf`.
PBKDF2 and scrypt take a secret password, and the bindings expose them as `pbkdf2` and `scrypt`.
The steps of scrypt take values derived from the password, and the bindings expose them as `salsa208`, `scrypt_block_mix` and `scrypt_romix`.

ROMix, the memory-hard step of scrypt, reads its table at indices that depend on the password, as AES reads its S-box below.
Its memory use depends on its parameters, and D1 says what a caller must bound.

Every AES function that takes a key handles secret data.
Its S-box is a table, and the cipher reads it at indices that depend on the key.
The Python bindings expose the block cipher, CTR and GCM, as `encrypt_block`, `decrypt_block`, `ctr`, `gcm_encrypt` and `gcm_decrypt`.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
Each such theorem of EthLib rests on the idealisations listed below, and on any hypothesis that its statement names.
The two theorems of Casper FFG share one bullet, as do the signature theorems of the light client.
The binding of a proof of possession shares the bullet of leanXMSS, and the codeword searches of each scheme share the bullet of that scheme:

- leanXMSS: the hash `H`, Keccak-256, is a random oracle on byte strings.
  The theorem says nothing about an attack that uses the structure of Keccak.
  The binding of an EIP-8450 proof of possession rests on the same oracle.
  So do the failure bounds of the codeword searches of leanXMSS.
- leanSPHINCS: the hash `H`, Keccak-256, is a random oracle on byte strings, as for leanXMSS.
  The unforgeability theorem says nothing about an attack that uses the structure of Keccak.
  It counts classical queries only, so it says nothing about a quantum adversary.
  The failure bounds of the codeword searches of leanSPHINCS rest on the same oracle.
- Merkle search bounds: each new `(level, position, left, right)` input receives an independent uniform answer from a finite nonempty range.
  Repeated inputs receive the same answer, and the initial cache is empty.
  The fixed-target bound excludes one honest input from the oracle domain and fixes the target before the run.
  Reading it as a second-preimage bound conditions on the honest digest, a modelling step that no theorem proves.
  Only classical queries are counted.
  No SHA-256, Keccak or quantum security claim follows from this model.
- SSZ root bound: the SHA-256 node hash is a random oracle on byte strings, shared by every node of the tree.
  The roots of the all-zero subtrees, constants of the specification, are oracle answers in the model.
  The type is fixed before the run.
  Each new input receives 32 independent uniform bytes, repeated inputs receive the same answer, and the initial cache is empty.
  Only classical queries are counted, and the adversary's private sampling is not.
  The bound says nothing about an attack that uses the structure of SHA-256.
- Trie root bound: Keccak-256 is a random oracle on byte strings, shared by the keys and the nodes of the trie.
  Each new input receives 32 independent uniform bytes, repeated inputs receive the same answer, and the initial cache is empty.
  Only classical queries are counted, and the adversary's private sampling is not.
  The bound says nothing about an attack that uses the structure of Keccak.
- VRF unpredictability: Keccak-256 is a random oracle on byte strings, as for leanXMSS.
  The bound says nothing about an attack that uses the structure of Keccak.
  It counts classical queries only, so it says nothing about a quantum adversary.
- VRF mixed selection: Keccak-256 on the 74-byte inputs that start with `PQ_VRF_MIX` is a uniformly random function of the output and the randomness, independent of the tree hash.
  That is the random-oracle assumption for the domain of the mix, and the tree hash stays Keccak-256 itself.
  The holder can still compute Keccak-256 on mix inputs, and the model ignores those values.
  No other input of the VRF has 74 bytes, so the mix shares no input with the tree; that is necessary for the assumption, not a proof of it.
  The randomness is uniform, drawn after the holder registers its tree, and independent of the holder.
  The bound counts classical mix queries only, and says nothing about an attack that uses the structure of Keccak.
- BLS: the hash to G2 under the message tag is a random oracle onto the multiples of `g2`, and the hash under the key tag of the proof-of-possession scheme is an independent random oracle onto the same group.
  The two tags differ, as §3.3.1 of the BLS draft requires.
  [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), §3, calls its `hash_to_curve` suitable where a random oracle onto the group is needed, and §8.8.2 gives the suite that encoding.
  Nothing in EthLib proves that the hash behaves as such an oracle.
- Light client: an aggregate signature check accepts a message only if every key in its set signed it (`SignatureChecks.AggregateSound`).
  BLS signatures with proofs of possession are meant to give this, except with small probability, and EthLib proves only the bound below.
  `Pop.byteForgeAdvantage_le_coCdhAdvantage` bounds the forger of such aggregates on EthLib's bytes, with both hashes as random oracles.
  That is the draft's scheme, whose proofs of possession hash the key under the key tag.
  Ethereum registers keys with deposit signatures under the message tag instead, which that game does not model.
  `LightClientForgery.forgeAdvantage_le` bounds the probability that the light client accepts a forged signature of one designated honest member, when every signer carries a proof of possession that passes PopVerify, §3.3.3.
  The theorems on one accepted update say nothing about a forged aggregate signature; the bound gives its probability.
- ECDSA: the bijection in the middle of the conversion `x_R mod n` is a uniform permutation, which the adversary evaluates in both directions.
  In ECDSA that bijection is the identity on integers below `2^256`, so the model idealises the conversion, as §4 of [Fersch, Kiltz and Poettering](https://doi.org/10.1145/2976749.2978413) does.
  The model draws the deterministic nonces of RFC 6979 as a random function of the message, so each message has one signature.
  [RFC 6979 §3.2](https://www.rfc-editor.org/rfc/rfc6979#section-3.2) computes them with HMAC_DRBG, whose seed holds the private key; the model assumes that output is pseudorandom, and no theorem proves it.
  The hash of messages is a fixed public function, so a bound on this game must charge its collisions to a named reduction.
  `Proofs/Secp256k1/Security/Game.lean` states that game; `forgeAdvantage_le` (`Proofs/Secp256k1/Security/ChosenMessageBound.lean`) bounds its advantage by named reductions.
- Casper FFG: a vote names its signer, so no one can forge a vote.
  The theorems of accountable safety and plausible liveness say nothing about an attack on the signatures.
- KZG batch checks: the challenge hash `Fr.hashToBlsField` is a random oracle from the inputs of the batch onto `Fr`.
  That hash reduces a SHA-256 digest modulo `r`, so it is not exactly uniform even if SHA-256 is a random oracle.
  Then each value has probability at most `3 / 2^256`, which is below `1.36 / r`, and the bounds grow by that factor.
  The real hash reads an encoding of those inputs.
  The encoding is injective on the batches that the checks accept: their arrays have matching lengths, and each cell has 64 values.
  In `prEvent_batchErrorPoly_root_le`, `prEvent_cellErrorPoly_root_le`, `prEvent_cellInput_root_le` and `prEvent_blobInput_root_le`, the adversary queries that oracle at most `q` times.
  In `prEvent_blobInput_root_le`, the evaluation challenges `computeChallenge` are a fixed function of the blobs and commitments, not part of the oracle.
  Their hash input starts with a different 16-byte domain tag from that of the batch challenge, so the two hashes never read the same bytes.
  So the bound `(q + 1) (n - 1) / r` covers grinding, where the adversary hashes many batches and keeps one whose challenge is a root.
  `blobBindingAdvantage_le` instead models both individual and batch challenges with one shared cache and uniform answers in `Fr`.
  Its typed keys erase polynomial annotations and stand for the two domain-separated byte encodings; no theorem proves those encodings jointly injective.
  That theorem also assumes correct representations from the adversary, a reading of the algebraic group model.
  The theorems say nothing about an attack that uses the structure of SHA-256.

## Gap B: does the code that runs match the definitions?

s2n-bignum proves its theorems about the object code, so a compiler bug cannot invalidate them.
EthLib is the other way round.
Its theorems are about the Lean definitions, and everything between them and the running code is trusted.
The sketch shows where each gap sits.

```text
 source document --A-- Lean definition == proof == theorem
                            |
                            B
                            |
        compiled code, C boundary, wheel --D-- client

 C: is the proof itself sound?
```

### B1. The compilers and the runtime

The Lean compiler turns the definitions into C, a C compiler turns that into machine code, and the Lean runtime runs it.
No theorem covers that path.

The vectors can test it end to end, but only through a comparison.
The Python suite regenerates every vector through the bindings and writes it over the committed one.
For most operations it does not compare the result with an expected answer, so a passing run proves nothing on its own.
The check is that the regenerated files are identical to the committed ones, which match consensus-specs `v1.7.0-alpha.12`.
`uv run --no-project --python 3.12 python tests/cryptography/check_vectors.py` makes that comparison against the pinned digests.

On every change, CI regenerates the vectors through the bindings.
It fails when a file under `tests/cryptography` then differs from the committed one.
That run skips the key generation and signing cases of leanXMSS and leanSPHINCS, which take minutes each.
Every Monday, the `vectors-slow` workflow regenerates all cases, these included.
It fails when a test file then differs from the committed one, or when a pinned digest does not match.
So between two weekly runs, a change can alter the compiled key generation or signing of those two schemes unnoticed.

### B2. Lean core's own implementations

Lean core implements `Array.forIn'`, `foldlM`, `foldrM`, `mapM` and `anyM` with `@[implemented_by]`, and the `Nat`, `ByteArray` and `Array` primitives with `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.
Any loop or fold over an array reaches them, so Lean core is a declared trusted baseline, and `lake exe check-decls` does not report it.

### B3. Native code during elaboration

The `EthLib` and `Exports` libraries set `precompileModules := true`.
So `#eval`, or a tactic that evaluates, in any module that imports them runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The C boundary

Between the Lean exports and Python sits a layer of hand-written C.

<!-- generated: exports -->
Lean exports 380 operations and 49 size constants.
The Python extension calls 380 of the operations and 49 of the constants.
<!-- end generated -->

<!-- generated: c-lines -->
9888 lines of hand-written C sit between them and Python: `aes.c` (119), `blocks.c` (364), `bls.c` (426), `chacha20_poly1305.c` (75), `chain.c` (45), `consensus.c` (1791), `crc32.c` (34), `crc32c.c` (34), `deposit_tree.c` (84), `devp2p.c` (59), `discv4.c` (78), `discv5.c` (303), `engine.c` (113), `enr.c` (177), `era.c` (12), `era1.c` (12), `eth.c` (225), `ethash.c` (65), `evm.c` (109), `fees.c` (56), `forkid.c` (101), `gossip.c` (80), `hmac.c` (102), `keccak.c` (85), `keystore.c` (30), `kzg.c` (511), `libp2p.c` (102), `module.c` (1401), `noise.c` (111), `password_kdf.c` (105), `pow.c` (73), `precompile.c` (85), `pyvalue.c` (421), `reqresp.c` (130), `rlp.c` (156), `rlpx.c` (184), `secp256k1.c` (169), `secp256r1.c` (42), `sha256.c` (38), `snap.c` (140), `snappy.c` (146), `sphincs.c` (85), `ssz.c` (47), `state.c` (108), `transactions.c` (181), `trie.c` (115), `vrf.c` (141), `wrappers.h` (663), `x25519.c` (21), `xmss.c` (134).
<!-- end generated -->

That C converts arguments, owns and frees Lean objects, and turns errors into Python exceptions.
The vectors test this layer only through the regeneration and comparison of B1.

An export that can fail returns the code and the message of its typed Lean error.
The C layer raises them as an exception of `ethlib.errors`, one class for each primitive.
C reads the code from the pair that the export returns.
A wrong field offset in C would give a wrong code, and no theorem covers that read.
Some wrong argument sizes are caught in C first, and raise `ValueError` with no code.

One generic converter in `pyvalue.c` passes typed values between Python and Lean.
It knows the constructors of one Lean type of Python values, and the type of no export.
Such an export needs only a short C wrapper that passes its Lean function and its arity to the generic caller, and no byte format of its own.
The C code repeats the order of the constructors of the Lean type, and no theorem checks it.
A change to that order needs the same change in C.

On the Lean side, every typed export requires a theorem for the type of its result.
That theorem says that reading back the value of a result gives that result, so two results never become one value of the Lean type.
The converter refuses a Lean `dict` with a repeated key, which would drop a value.
It counts the parts and the bytes of each call from Python, and refuses more than a million parts or 512 MiB.
However much a call shares between its lists, the converter then builds at most a million parts and 512 MiB.
A property test sends random nested values through Lean and back, with integers of thousands of bits.
A separate test passes a value at the deepest level allowed.
Another property test sends values that the converter must refuse, and checks that each raises `TypeError` or `ValueError`, never a crash.
The converter refuses an `int` wider than 65536 bits, so that each call holds the GIL for a short time.
Lean reads and writes the digits of a large `int` by halves, in time about `d log d` for `d` digits.
Each export that moves to typed values removes its own C, and the line count above shows it.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust, but the code that runs is still not the definition a reader reads.

The repository has none of the three today.
`lake exe check-decls` reports any of them, and fails on one that is not in its baseline.

### B6. The build and its publication

`setup.py` runs `lake build Exports`, and links the objects under `.lake/build/ir/EthLib/` with `libleanshared`, `libgmp` and `libuv`.
`.github/workflows/publish.yml` builds the wheels with `cibuildwheel`, cleans the build before each wheel, and publishes them to PyPI.

The workflow installs elan and the Lean toolchain that `lean-toolchain` names from pinned releases, and checks the SHA-256 digest of each archive first.
Each wheel runs the vector suites and the check of the pinned vectors before it is published.
A build provenance attestation records which workflow run, at which commit, built each wheel and the sdist.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set; a theorem may use fewer.

`lake exe check-decls` checks dependencies: no declaration may depend on an axiom outside that set, apart from those in its baseline.
It does not check the kernel, and it does not show that the axioms are consistent.
That rests on Lean's own design and review.
The replay of C3 uses Lean's own kernel, so no independent type checker covers EthLib yet.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

`CONTRIBUTING.md` does not allow these tactics, and a new use fails `lake exe check-decls`.

<!-- generated: native -->
No theorem uses them.
<!-- end generated -->

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
The `replay` workflow catches such a declaration with leanchecker.
leanchecker replays every declaration of EthLib into Lean's kernel, proof bodies included.
First, the workflow checks that leanchecker rejects a fixture theorem of `False` that the kernel never checked.
The replay uses Lean's own kernel, so it does not protect against a bug in that kernel (C1).

The workflow runs every Monday and on each push to `master`, but a newer push cancels a replay still in progress.
So only the weekly run is sure to finish.

## Gap D: does the use of EthLib hold together?

### D1. The client's obligations

A client chooses the right operation for its fork, passes inputs of the right form, and handles errors.

XMSS adds one more obligation: never sign two different messages at one leaf index with one secret key.
Each leaf index names a one-time signing key, and nothing in EthLib records which leaf indices were used, so the caller must prevent reuse.
The Lean and Python docstrings of `sign` both say so.

leanSPHINCS adds another.
Never sign more than `2^30` messages with one secret key.
Nothing in EthLib counts signatures, so the caller must.
The Lean and Python docstrings of `sign` both say so.

Password derivations add bounds on memory and time.
The ROMix table of scrypt has a payload of `128 * r * N` bytes, and the expanded password and the mixed blocks take at least `128 * r * p` bytes each.
The key itself, of either derivation, can be up to `(2^32 - 1) * 32` bytes, about 128 GiB.
Parameters within the bounds of RFC 7914 can ask for more memory than any machine has.
For example, `N = 2^40` and `r = 8` pass the check on the cost and ask for a table of `2^50` bytes, one pebibyte.
Likewise, `r = 1` and `p = 2^30 - 1` pass the check on `p` and ask for about 128 GiB per buffer.
No error is returned then: the Lean runtime aborts the process, or the operating system kills it.
The work of scrypt grows with `N * r * p` and with the key length.
The work of PBKDF2 grows with `c` times the number of 32-byte blocks of the key.
So a hostile parameter can also make a call run for an impractical time.
A keystore file gives `N`, `r` and `p`, or `c`, and the key length `dklen`.
So a caller that reads one must bound `r * N`, `r * p`, `c` and `dklen` before it calls the derivation.
The Lean docstrings of `pbkdf2`, `scrypt` and `romix` say so.
Keystore decryption does this itself with a model of the cost, against limits that its caller chooses.

### D2. Dependencies

`lake-manifest.json` pins every dependency.

<!-- generated: pins -->
The specification requires no package.
The package requires Mathlib, at `v4.35.0`, commit `56a0058`.
The package requires VCVio, at `bbf05ee`.
Only the proofs import them.
The Lean toolchain is `leanprover/lean4:v4.35.0`.
<!-- end generated -->

### D3. The KZG trusted setup

The setup raises three separate assumptions, and each use of KZG relies on a different subset of them.

- Provenance: the embedded bytes are the ceremony's output.
  They match consensus-specs `presets/mainnet/trusted_setups/trusted_setup_4096.json` byte for byte, and `Kzg/TrustedSetupData.lean` records that source, the commit it comes from and its sha256.
- Algebraic consistency: the bytes decode to valid points, the monomial points are powers of one secret, and the Lagrange points are the matching basis.
  For the embedded bytes, the first part is proved only in part, the third is proved if the bytes decode, and the second is not.
  `TrustedSetup.ofHex_valid` (`Proofs/Kzg/TrustedSetup.lean`) proves that, if they decode, each point is on its curve.
  No theorem says that they decode.
  If they decode, `TrustedSetup.ofHex_torsion` proves that each monomial point of `G1` has an order that divides `r`.
  No theorem says this of the Lagrange points or of the points of `G2`.
  If they decode, `TrustedSetup.ofHex_lagrangeOfMonomial` (`Proofs/Kzg/SetupLagrange/Embedded.lean`) proves that each Lagrange point of `G1` is the sum of the monomial points times the coefficients of its basis polynomial.
  So the Lagrange points are the matching basis of whatever secret the monomial points hold.
  The kernel checks this on the embedded data, in three rounds of 256 transforms of size 16.
  It also checks that each of the 8192 strings of `G1` encodes its table point, so decompression gives that point.
  The kernel computes no square root: each table point is a certificate that it checks with three products.
  Compiled code computes two tables of intermediate points when the files are built, and the repository holds no copy of them.
  A wrong table only makes a kernel check fail.
  This is a second recorded exception to the rule of a few seconds for concrete facts in [CONTRIBUTING.md](CONTRIBUTING.md#known-answers).
  It costs about 20 CPU-minutes per replay, measured one module at a time, in 56 modules, and about as much per build.
  Each module takes 14 to 29 seconds and at most 3.3 GB to replay.
  The Python suite checks for every point that it decodes and lies in the subgroup (`bindings/python/tests/kzg/test_trusted_setup.py`).
  `checksSufficient` covers the ceremony's monomial points, under its hypotheses.
  `TrustedSetup.WellFormed s τ` (`Proofs/Kzg/Commitment.lean`) states the consistency of a setup `s` with a secret `τ`.
  The theorems on commitments and on honest proofs take it as a hypothesis.
  For the embedded setup, `TrustedSetup.ofHex_wellFormed` reduces it to the monomial points.
  If the setup decodes and its monomial points of `G1` and `G2` represent the powers of `τ`, it is well formed at `τ`.
  That some `τ` makes the monomial points represent its powers is an assumption, and no theorem proves it.
- Secrecy: no one knows the secret, which holds if at least one ceremony participant was honest.
  Only binding, a security property, needs it; a theorem about parsing, or that an honest proof verifies, does not.

### D4. The vectors

A client that tests against the vectors trusts whatever produced their expected values.
The KZG vectors and the `eth_*` BLS vectors match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte.
The other BLS vectors match `ethereum/bls12-381-tests` `v0.1.2`, and the hash-to-curve vectors come from RFC 9380.
`v1.7.0-alpha.12` was the last release before consensus-specs removed its KZG specification, in ethereum/consensus-specs#5398.

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

No theorem states binding for the batch check of blobs.
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
This bound exceeds the standard birthday bound `q(q - 1) / (2N)` by the factor `2q / (q - 1)`, a little over 2.

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

Layout separation is `hashTreeRoot_progressiveContainer_layouts_separate` (`Proofs/Ssz/Codec/LayoutSeparation.lean`).
Two legal progressive containers with one root have one layout, or `findMixinCollision` returns the inputs of the two last hashes.

No theorem bounds the probability of finding any of these collisions.

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
The ported model signs the layers of the hypertree from the bottom up, as EthLib and leanVM's Rust signer do.
The published model signed them from the top down, and its author confirmed in [leanVM#720](https://github.com/leanEthereum/leanVM/issues/720) that this order is a bug.
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

### BLS12-381

The BLS theorems check the constants, because a wrong digit in a modulus or in the generator would very likely make one of them fail.
`modulus_prime` (`Proofs/Bls/FpZMod.lean` and `Proofs/Bls/FrZMod.lean`) proves that both moduli are prime.
`seven_pow_card_sub_one` and `seven_pow_div_prime_ne_one` (`Proofs/Bls/FrZMod.lean`) prove that `7` generates the multiplicative group of the scalar field; `7` is also the KZG constant `PRIMITIVE_ROOT_OF_UNITY`.
`addOrderOf_toPoint_generator` (`Proofs/Bls/G1Order.lean`) proves that the G1 generator has order `r`.

No theorem proves that `pairingCheck` computes a bilinear pairing.
`orderOf_pairing_generators` (`Proofs/Bls/Nondegenerate.lean`) proves that the pairing of the two generators has order `r`, so it is not 1; the kernel evaluates that pairing.
`PairingLaws.of_bilinear` (`Proofs/Bls/PairingBilinear.lean`) derives `PairingLaws` from one smaller hypothesis, `PairingBilinear`: `e(a g_1, b g_2) = e(g_1, g_2)^(a b)` for all `a` and `b` in `Fr`.
No theorem proves `PairingBilinear` yet.
`PairingLaws` (`Proofs/Bls/PairingLaws.lean`) states the consequence that verification needs, as one hypothesis.
Let `P_i` represent `a_i * g_1` and `Q_i` represent `b_i * g_2`, where a representative is any valid point with that group element.
Then the check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i * b_i = 0` in `Fr`.
The law holds when the check tests `prod_i e(P_i, Q_i) = 1` for any bilinear map `e` with `e(g_1, g_2) != 1` into a group of order `r`.
`pairingCheck_congr` (`Proofs/Bls/PairingCongr.lean`) proves that the check depends only on the group elements of valid points, so the law can quantify over representatives.
`TargetGroup.ofPairingLaws` (`Proofs/Bls/TargetGroup.lean`) builds a model of the target group from `PairingLaws`.
Its target is `Fp12` and its generator is `e(g_1, g_2)`.
Under the law, `pairing P Q = e(g_1, g_2)^(a b)` when `P` represents `a * g_1` and `Q` represents `b * g_2`.
An element of the model represents `t` in `Fr` when it is `e(g_1, g_2)^t`.
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
No theorem yet applies these results to BLS12-381 or alt_bn128, so no theorem yet proves their bilinearity.

The pairing of the two generators equals the value that [draft-irtf-cfrg-pairing-friendly-curves-11](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11) publishes in Appendix B.
The Python suite checks it through the bindings (`bindings/python/tests/bls/test_pairing.py`), with a few bilinearity checks.
This evidence supports the pairing law but does not prove it.

`keyValidatePoint_eq_ok_iff` (`Proofs/Bls/KeyValidate.lean`) proves that key validation accepts exactly the encodings of the nonzero points of order `r` in G1.
The G1 and G2 subgroup checks accept exactly the valid points that represent a multiple of the generator.
Every output of the maps to G1 and G2 is a valid point of that subgroup (`Proofs/Bls/MapToCurve.lean`).

`sign_ok` and `popProve_ok` (`Proofs/Bls/Signatures.lean`) prove that BLS signing never fails.
Under the pairing law, an honest signature, an honest proof of possession and an aggregate of honest signatures verify (`verify_sign`, `popVerify_popProve`, `aggregateVerify_aggregate`, `Proofs/Bls/SignaturesCorrect.lean`).
For the fast aggregate verification on one message, `fastAggregateVerify_aggregate` also assumes that the secret keys do not sum to zero modulo `r`.
Otherwise the aggregate key is the point at infinity, and key validation rejects it.

Under the pairing law, a key and a message have at most one signature that verifies, byte for byte (`verify_unique`, `Proofs/Bls/SignaturesUnique.lean`).
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
Under the pairing law, the test is sound (`blsScheme_sound`).
`sign_eq` and `verify_iff_isDh` prove that EthLib's `sign` and `verify` compute the scheme.
There `H(m)` is the hash to G2 of `m` under the message tag.
Aggregation and proofs of possession lie outside the game.

`byteForgeAdvantage_le` (`Proofs/Bls/Security/Refinement.lean`) turns a forger on byte encodings into a named group-element forger with at least the same advantage.
The byte forger receives a compressed key and compressed hash and signing answers, and returns arbitrary message and signature bytes.
The game runs EthLib's G2 decompression, signature subgroup check and key validation before the pairing check.
This step needs no pairing law, because the byte check and the group test pair the same group elements.
`encode_publicKey`, `encode_signature` with `sign_eq`, and `byteVerify_hashPoint` connect these operations to EthLib's public key, signing and verification when the oracle uses EthLib's hash.
The bound still models that hash as a random oracle, not as the concrete hash function.

Freshness is by message: a message submitted to signing cannot win with any signature bytes.
`decodeSignature_encode` and `encode_eq_of_decodeSignature` prove both encoding round trips, so two accepted encodings of the same subgroup element cannot differ.
The byte game keeps the group game's uniform scalar distribution, including zero, whose key validation rejects.
EthLib's secret keys exclude zero, and a zero key always loses.
So against nonzero keys, a forger wins at most `r / (r - 1)` times its byte advantage; no theorem states this factor.
Under the pairing law, `byteForgeAdvantage_le_coCdhAdvantage` gives the same `q`-factor co-CDH bound when the decoded forger makes at most `q` hash calls.
`byteForgeAdvantage_le_coCdhAdvantage_of_byteHashCallBound` states the bound with the hash-call bound on the byte forger itself.
`byteHashCallBound_iff` proves that the two bounds are equivalent, because the encoding forwards each query once.

### secp256k1

The secp256k1 theorems are correctness statements.
`card_point` (`Proofs/Secp256k1/Order.lean`) proves that the group has `n` points, so the cofactor is 1.
`decode_eq_ok_iff` (`Proofs/Secp256k1/Encoding.lean`) proves that the decoder accepts exactly the encodings of the points other than `O`.
`verify_sign` (`Proofs/Secp256k1/Ecdsa.lean`) proves that a signature from the signing operation of SEC 1 verifies.
`verify_recover` and `recover_of_verify` (`Proofs/Secp256k1/Recovery.lean`) prove that a recovered key verifies the signature, and that every key that verifies one is recovered, when `r + n >= p`.
`verify_lowS_unique` (`Proofs/Secp256k1/Malleability.lean`) proves that two low-s signatures with one `r` that verify are equal, under the same bound.

No theorem states unforgeability, which rests on the discrete logarithm problem.

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

No theorem proves that `pairingCheck` computes a bilinear pairing.
`orderOf_pairing_generators` (`Proofs/AltBn128/Nondegenerate.lean`) proves that the pairing of `P1` and `P2` has order `q`, so it is not 1; the kernel evaluates that pairing.
`pairingCheck_eq_true_iff` (`Proofs/AltBn128/PairingBilinear.lean`) proves that the check passes exactly when the product of the pairings of its pairs is 1.
The pairing law is a hypothesis, `AltBn128.PairingLaws` (`Proofs/AltBn128/PairingLaws.lean`), in the shape of the BLS one.
It states the check of EIP-197: the pairs `(a_i P1, b_i P2)` pass exactly when `sum_i a_i b_i = 0`.
`PairingLaws.of_bilinear` (`Proofs/AltBn128/PairingBilinear.lean`) derives it from one smaller hypothesis, `PairingBilinear`: `e(a P1, b P2) = e(P1, P2)^(a b)` for all `a` and `b` in `Fr`.
No theorem proves `PairingBilinear` yet.

`ecadd_toPoint` and `ecmul_toPoint` (`Execution/Proofs/Evm/Precompiles/AltBn128/Group.lean`) carry this group law to the precompiles.
A call of ECADD that succeeds returns the sum of its two points, and a call of ECMUL returns its point times its 32-byte scalar.
`bytesToG1_eq_ok_iff` (`Execution/Proofs/Evm/Precompiles/AltBn128/Encoding.lean`) proves that the decoder of a point of `G_1` accepts 64 bytes exactly when they are the EIP-196 encoding of a point on the curve.

### secp256r1

The secp256r1 theorems are correctness statements, like those of secp256k1.
`modulus_prime` (`Proofs/Secp256r1/Field.lean`) proves that both moduli are prime.
`toPoint_add` (`Proofs/Secp256r1/Curve.lean`) proves that the addition of SEC 1 is the group law of the curve.
`card_point` (`Proofs/Secp256r1/Order.lean`) proves that the group has `n` points, so the cofactor is 1.
That proof needs one more fact than the proof for secp256k1: `x^3 - 3 x + b` has no root mod `p`.
The kernel checks it by an inverse of `X^p - X` modulo the cubic.

`verify_sign` (`Proofs/Secp256r1/Ecdsa.lean`) proves that a signature from the signing operation of SEC 1 verifies.
No theorem states unforgeability.

### AES

The AES theorems are correctness statements, and none states a security property.
`invCipher_cipher` and `ciphInv_ciph` (`Proofs/Aes/Block.lean`) prove that the inverse cipher of FIPS 197 undoes the cipher, for every key schedule and so for every key.
`sbox_eq` proves that each entry of the S-box table equals the inverse in GF(2^8) followed by the affine map of FIPS 197 §5.1.1.
`ctr_ctr` (`Proofs/Aes/Ctr.lean`) proves that CTR decryption of SP 800-38A returns the plaintext, for every forward cipher and initial counter.
The Python tests (`bindings/python/tests/aes/test_aes.py`) check FIPS 197 Appendix B and the AES-128 and AES-256 vectors of its 2001 Appendix C.
They also check the CTR examples F.5.1, F.5.2, F.5.5 and F.5.6 of SP 800-38A.

`decrypt_encrypt` (`Proofs/Aes/Gcm.lean`) proves that GCM decryption of SP 800-38D returns the plaintext of an honest ciphertext and tag.
`decrypt_eq_ok` proves that decryption accepts no tag other than the honest one.
Both hold for every forward cipher.
`encrypt_shortTag` and `decrypt_shortTag` prove that both functions reject the 64-bit and 32-bit tags, which SP 800-38D Appendix C restricts.
The Python tests check seven test cases of the NIST CAVP file `gcmtestvectors.zip`, one of them a forged tag that decryption rejects.

### KZG

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
Under the pairing law and for a well-formed setup, honest KZG proofs and blob proofs verify (`verifyKzgProof_computeKzgProof`, `verifyBlobKzgProof_computeBlobKzgProof`, `Proofs/Kzg/Verify.lean`).
`verifyKzgProofImpl_iff` states when the check accepts: `c - y = w (τ - z)`, for decoded points representing `c` and `w`.
`verifyKzgProofBatch_ok_iff_root` (`Proofs/Kzg/BatchBinding.lean`) states when the batch check of openings accepts, as an equivalence.
Let opening `i` have commitment `c_i`, value `y_i`, point `z_i` and proof `w_i`.
Under `PairingLaws` and a well-formed setup, its verdict is true exactly when its challenge `r` is a root of `P(X) = sum_i X^i (c_i - y_i - w_i (τ - z_i))`.
`P` is zero exactly when every opening satisfies the identity of the single check.
`verifyKzgProofBatch_exists_ok` shows that the batch check returns a verdict, with no error, when its six arrays have one size.
`verifyCellKzgProofBatchImpl_ok_iff_root` (`Proofs/Kzg/CellBatchBinding.lean`) states the same for the batch check of cells, as an equivalence.
Under `PairingLaws`, a well-formed setup, and decoded points that represent `c` and `w`, its verdict is true exactly when the challenge is a root.
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
The theorem holds in any model of that group, `TargetGroup`, such as the pairing itself under `PairingLaws`.
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
Assume `PairingLaws`, a well-formed setup, and decoded points that represent the scalars `c` and `w` of their bytes.
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
Both theorems assume the pairing law, `PairingLaws`, and the BSDH reductions work in any model of the target group, `TargetGroup`.
That BSDH and ARSDH are hard stays an informal hypothesis: no theorem assumes it, and the bounds hold for every adversary.
An adversary is any Lean function, so without a model of cost, hardness cannot be stated as a Lean hypothesis.
The BSDH advantage is relative to a model of the target group; `TargetGroup.ofPairingLaws` is the model of the real pairing.
These games check one cell per call.
`batchCodeBindingAdvantage_le` (`Proofs/Kzg/PeerDasBatchGames.lean`) states code-binding with one batch check of all opened cells of the commitment.
The hash of the challenge is a random oracle into `Fr` on the inputs of the core check, and the adversary makes at most `q` queries.
That idealises SHA-256 reduced modulo `r`, whose values are not exactly uniform.
The verifier accepts when the batch check returns a verdict and its challenge is a root of the error polynomial of the batch.
At the challenge of the hash, and under `PairingLaws`, this is the batch check of cells (`CellBatchInput.acceptsAt_challenge_iff`); no theorem relates the two at another challenge.
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
It assumes `PairingLaws` and a well-formed setup, and the commitments of the batch may repeat.
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
It needs the pairing law and a well-formed setup, and no model of a hash.

`verifyKzgProofBatch_binding` and `verifyKzgProofBatch_binding_single` (`Proofs/Kzg/BatchBinding.lean`) are the binding of the batch check of openings.
Let an accepted batch open one commitment at one point to two values, or let a single check accept a second value.
Then the values agree, or the search on the two openings returns a strong Diffie–Hellman solution, or the challenge is a root of a nonzero `P`.
They need the pairing law and a well-formed setup.
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

- `PairingLaws`, the pairing law of A2.
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

No theorem relates the module to the execution-specs code it follows.

### BLAKE2F

The theorems pin down the input format exactly, and leave the compression function F to test vectors.
`output_invalidInputLength`, `output_invalidFlag` and `output_ok` (`Execution/Proofs/Evm/Precompiles/Blake2f.lean`) prove that a call fails exactly when the input is not 213 bytes long, or its flag byte is neither `0` nor `1`.
Otherwise it returns `compute` of the input, which decodes the fields and runs F of RFC 7693 on them.
`readWord_toNat`, `readRounds_toNat` and `writeState_word` state the encoding of EIP-152 for every input: the rounds field big-endian, every word little-endian, and the output in the encoding of the input.

F itself is checked by the Python tests only (`bindings/python/tests/precompile/test_blake2f.py`).
They run test vectors 0 to 7 of EIP-152, and read the rounds field of test vector 8.
They also run one full block of the BLAKE2 test vectors, and one call that sets `t1`.
Test vector 8 asks for `2^32 - 1` rounds, so nothing checks its output.

### ECRECOVER

The ECRECOVER theorems rest on the secp256k1 ones, and all three are in `Execution/Proofs/Evm/Precompiles/Ecrecover.lean`.
`output_sign` proves that a signature made with a private key returns that key's address.
`output_verify` proves that a nonempty output is the address of a key that verifies the signature.
`output_of_verify` proves that every key that verifies a signature has its address returned for `v = 27` or `v = 28`, when `r + n >= p`.

No theorem relates the module to the execution-specs code it follows, which calls a C library to recover the key.

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
It assumes `PairingLaws`, which EthLib states but does not prove for its Miller loop.
`bls12Pairing_encodePairs` computes the output on the encodings of any represented pairs.
`bls12Pairing_generators` and `bls12Pairing_generator_neg` apply it to reach both outputs: 0 for `(g_1, g_2)`, and 1 for `(g_1, g_2)` with `(-g_1, g_2)`.

`bls12MapFpToG1_eq_ok_iff` and `bls12MapFp2ToG2_eq_ok_iff` (`G1.lean` and `G2.lean`) prove that the two map precompiles return the encoding of the curve map of their decoded field element.
The curve maps of RFC 9380 never fail.
So `bls12MapFpToG1_isOk_iff` and `bls12MapFp2ToG2_isOk_iff` (`Map.lean`) prove that each map precompile succeeds exactly when the length and gas checks pass and its padded field element decodes.
`inSubgroup_of_bls12MapFpToG1_eq_ok` and `inSubgroup_of_bls12MapFp2ToG2_eq_ok` prove that every output encodes a valid point of the subgroup.
`bytesToG1_of_bls12MapFpToG1_eq_ok` and `bytesToG2_of_bls12MapFp2ToG2_eq_ok` prove that the point decoder, with the subgroup check, accepts that output.
`bls12MapFpToG1_pad` and `bls12MapFp2ToG2_pad` prove that the padded encoding of every field element succeeds with enough gas.

No theorem relates the module to the execution-specs code it follows.

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
The state and storage roots in `Execution/State/Root.lean` build tries directly, and `stateEntries_nodup` and `storageEntries_nodup` supply their distinct keys.
The indexed roots in `Execution/Blocks/Roots.lean` also build tries directly, with the RLP encoding of each index as its key.
`indexedEntries_nodup` (`Execution/Proofs/Blocks/Roots.lean`) supplies their distinct keys, since the RLP decoder reads each index back from its encoding.
With these distinct keys, `indexedRoot_binding_key` shows that two lists with one root give every key one value.
Otherwise `findCollision` returns a collision in the proofs of that key.
`indexedRoot_binding` concludes that the two lists are equal, or `findIndexedCollision` returns a collision in the proofs of one index.
Two transactions, or two withdrawals, with the same bytes are equal, so `transactionsRoot_binding` and `withdrawalsRoot_binding` conclude the same for the lists themselves.
`receiptsRoot_binding` does so for receipts whose types are 0 or types that the fork has, as the receipt decoder requires.
No theorem bounds the probability of finding a collision.

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
`lightClientGindices_eq` shows that each index is the generalized index of the path of its field in the type of the beacon state, at every fork from Altair, for the mainnet and minimal presets.
At the Altair fork, `lightClientGindices_altair_eq` shows the same three indices for every preset.
On a state of that fork, `BeaconState.nodeRoot_finalizedCheckpoint_root_altair` reads the finality node as the root of `state.finalizedCheckpoint.root`.
`BeaconState.nodeRoot_nextSyncCommittee_altair` and `BeaconState.nodeRoot_currentSyncCommittee_altair` read the committee nodes as the roots of those fields.
These three take the lawful SSZ type of the state as an argument, and they name the root of the field, which always exists.
Instance search does not yet find that lawful type at the mainnet or minimal preset, so a caller supplies it.
The node results for every fork after Altair remain open, as do the statements that join them to the update validators.

The signature theorems assume `SignatureChecks.AggregateSound`, listed in A4.
Under it, `validateLightClientUpdate_signed` shows that every member whose bit is set signed the signing root.
`validateLightClientUpdate_signed_outside` adds that a set of keys holding fewer seats of the committee than there are signers leaves a signer outside the set.
`SignatureChecks.not_aggregateSound_acceptAll` shows that the assumption has content: the checks that accept every signature do not meet it.
No theorem links an honest signer to the canonical chain; that is a property of the validators, not of the protocol text.

### Casper FFG

Casper FFG finalizes checkpoints, each a block with an epoch, from the votes of validators.
The model in `Consensus/Proofs/Models/Ffg/` follows Casper FFG §2 and Gasper §4.
It fixes one validator set and one stake for each validator, for every vote.

`accountable_safety` (`AccountableSafety.lean`) takes two finalized checkpoints whose blocks conflict.
Then validators with at least one third of the stake broke a slashing condition.
With a total stake of zero this holds for every set of votes, so the theorem says something only for positive stake.

`plausible_liveness` (`PlausibleLiveness.lean`) takes honest validators with at least two thirds of the stake.
The votes so far are finite, the total stake is positive, and no honest validator is slashable.
Each honest vote comes from a justified source.

Then there is a justified checkpoint with the following property.
For every block whose chain contains its block, the honest validators can add votes that finalize that block.
The block is finalized at an epoch above every justified epoch so far.
The new votes come from justified sources, and no honest validator becomes slashable.

A vote names the validator that signed it, so both theorems assume that no one forges a vote.
No theorem links the model to the beacon chain, so neither theorem is yet about what a client runs.

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

One definition also does what its source does not.
The PeerDAS custody search fails after `2^16` node IDs in the export, where its source loops on, and no theorem bounds the steps it needs.

Some official vectors expect more than a source says.
The transaction tests of ethereum/tests reject 43 results whose gas limit is `2^64`, or whose gas limit times gas price exceeds `2^256 - 1`.
No rule of the Yellow Paper rejects such a transaction alone, and EIP-7825 caps the gas limit only from Fusaka on.
EthLib accepts them, and the suite asserts that it does, as `tests/execution/ethereum_tests/README.md` explains.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
The ceremony theorem `checksSufficient_of_subgroupChecks` is one, and its hypotheses are listed under KZG.
`PairingLaws`, listed under BLS12-381 and alt_bn128, is the hypothesis of every theorem about the result of a pairing check.
It is a `Prop` passed as an explicit argument, never an axiom, so `lake exe check-decls` still sees only the standard axioms.
If it were false, every theorem that assumes it would hold vacuously.
Whatever those hypotheses leave unproved is part of what a reader trusts.

### A3. Side channels

EthLib makes no constant-time claim.
`Hash/Keccak.lean` says it "is not intended to be constant-time", and the field arithmetic uses Lean's `Nat`, which gives no timing guarantee.
This matters where secret data is handled.

XMSS and leanSPHINCS `keyGen` and `sign` handle secret data.
The Python bindings expose all four, as `key_gen` and `sign` in each module, which take the secret seed.
BLS key generation, signing and the proof of possession handle secret data, and the Python bindings expose all three.
HMAC-SHA-256, HKDF and the Concatenation KDF take a secret key, input keying material or shared secret.
The Python bindings expose them as `hmac_sha256`, `hkdf_extract`, `hkdf` and `concat_kdf`.

Every AES function that takes a key handles secret data.
Its S-box is a table, and the cipher reads it at indices that depend on the key.
The Python bindings expose the block cipher, CTR and GCM, as `encrypt_block`, `decrypt_block`, `ctr`, `gcm_encrypt` and `gcm_decrypt`.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
Each such theorem of EthLib rests on one idealisation, listed below.
The two theorems of Casper FFG share one bullet, as do the signature theorems of the light client, and the binding of a proof of possession and the codeword searches share that of leanXMSS:

- leanXMSS: the hash `H`, Keccak-256, is a random oracle on byte strings.
  The theorem says nothing about an attack that uses the structure of Keccak.
  The binding of an EIP-8450 proof of possession rests on the same oracle.
  So do the failure bounds of the codeword searches of leanXMSS and leanSPHINCS.
- Merkle search bounds: each new `(level, position, left, right)` input receives an independent uniform answer from a finite nonempty range.
  Repeated inputs receive the same answer, and the initial cache is empty.
  The fixed-target bound excludes one honest input from the oracle domain and fixes the target before the run.
  Reading it as a second-preimage bound conditions on the honest digest, a modelling step that no theorem proves.
  Only classical queries are counted.
  No SHA-256, Keccak or quantum security claim follows from this model.
- VRF unpredictability: Keccak-256 is a random oracle on byte strings, as for leanXMSS.
  The bound says nothing about an attack that uses the structure of Keccak.
  It counts classical queries only, so it says nothing about a quantum adversary.
- BLS: the hash to G2 under the message tag is a random oracle onto the multiples of `g2`.
  [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), §3, calls its `hash_to_curve` suitable where a random oracle onto the group is needed, and §8.8.2 gives the suite that encoding.
  Nothing in EthLib proves that the hash behaves as such an oracle.
- Light client: an aggregate signature check accepts a message only if every key in its set signed it (`SignatureChecks.AggregateSound`).
  BLS signatures with proofs of possession are meant to give this, except with negligible probability, and EthLib proves no such bound.
  The theorems say nothing about a forged aggregate signature.
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
Lean exports 233 operations and 35 size constants.
The Python extension calls 233 of the operations and 26 of the constants.
Exported constants it does not call: `eth_sphincs_const_chains`, `eth_sphincs_const_n`, `eth_sphincs_const_public_param_len`, `eth_sphincs_const_randomizer_len`, `eth_xmss_const_chains`, `eth_xmss_const_digest_len`, `eth_xmss_const_layer_height`, `eth_xmss_const_public_param_len`, `eth_xmss_const_randomizer_len`.
<!-- end generated -->

<!-- generated: c-lines -->
7888 lines of hand-written C sit between them and Python: `aes.c` (119), `blocks.c` (432), `bls.c` (378), `chain.c` (50), `consensus.c` (1396), `crc32.c` (38), `crc32c.c` (38), `devp2p.c` (59), `discv4.c` (78), `discv5.c` (223), `engine.c` (84), `enr.c` (146), `eth.c` (225), `ethash.c` (112), `evm.c` (140), `fees.c` (101), `forkid.c` (90), `gossip.c` (66), `hmac.c` (102), `keccak.c` (85), `kzg.c` (511), `module.c` (951), `pow.c` (105), `precompile.c` (95), `reqresp.c` (85), `rlp.c` (162), `rlpx.c` (194), `secp256k1.c` (169), `secp256r1.c` (42), `sha256.c` (38), `snap.c` (114), `snappy.c` (131), `sphincs.c` (85), `ssz.c` (88), `state.c` (108), `transactions.c` (251), `trie.c` (96), `vrf.c` (119), `wrappers.h` (448), `xmss.c` (134).
<!-- end generated -->

That C converts arguments, owns and frees Lean objects, and turns errors into Python exceptions.
The vectors test this layer only through the regeneration and comparison of B1.

An export that can fail returns the code and the message of its typed Lean error.
The C layer raises them as an exception of `ethlib.errors`, one class for each primitive.
C reads the code from the pair that the export returns.
A wrong field offset in C would give a wrong code, and no theorem covers that read.
Some wrong argument sizes are caught in C first, and raise `ValueError` with no code.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust, but the code that runs is still not the definition a reader reads.

The repository has none of the three today.
`lake exe check-decls` reports any of them, and fails on one that is not in its baseline.

### B6. The build and its publication

`setup.py` runs `lake build Exports`, and links the objects under `.lake/build/ir/EthLib/` with `libleanshared`, `libgmp` and `libuv`.
`.github/workflows/publish.yml` builds the wheels with `cibuildwheel`, cleans the build before each wheel, and publishes them to PyPI.

The workflow installs elan from a pinned release, and checks the SHA-256 digest of the archive first.
Then elan installs the Lean toolchain that `lean-toolchain` names.
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

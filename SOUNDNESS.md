# Soundness

This document says what the proofs of EthLib establish, and what a user of EthLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem, and both are assumed to match something outside Lean: the source document the definition implements, the code that actually runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of s2n-bignum's [`SOUNDNESS.md`](https://github.com/awslabs/s2n-bignum/blob/main/SOUNDNESS.md), adapted to a specification library.

This document describes the development tree that declares package version `0.2.0` in `pyproject.toml`.
It does not describe the tag `v0.2.0`, which points to an earlier commit, without the declaration check or the exports library.

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
| A1 | A definition does not match its source | Definitions named and shaped after the source; vectors pinned to consensus-specs `v1.7.0-alpha.12`; consistency theorems on the constants | P R B V |
| A2 | A theorem holds only under a hypothesis | Each conditional theorem below lists its hypotheses | P |
| A3 | Timing reveals secret data | None: no constant-time claim | R B |
| A4 | A security theorem idealises a primitive | Each idealisation is listed in A4 | P |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | Regenerating the vectors locally, then checking them against their pinned digests | R B |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R B |
| B3 | Elaboration runs native code | None | P |
| B4 | The hand-written C boundary is wrong | Regenerating the vectors locally, then checking them against their pinned digests | B |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R B |
| B6 | The build or the published wheel differs from the source | Fresh build per wheel in CI | B |
| C1 | The Lean kernel or its axioms are unsound | None: `lake exe check-decls` checks which axioms a theorem uses, not that the kernel or the axioms are sound | P |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any new use; the remaining ones are listed in C2 | P |
| C3 | A declaration reached the environment unchecked | None yet | P |
| D1 | A client misuses an operation | Docstrings in Lean | R B |
| D2 | A dependency changes | Pinned in `lake-manifest.json` | P R B |
| D3 | The KZG trusted setup is not what it should be | Bytes match the consensus-specs setup | P R B V |
| D4 | The vectors are wrong | They match consensus-specs `v1.7.0-alpha.12`, and CI checks their pinned digests | V |

The sections after the next one explain each row.

## What the proofs say

Before the risks, here is what is actually proved, primitive by primitive.
The list covers the main theorems and is not yet complete.

Most of these theorems are about correctness: an honest run gives the expected answer, or malformed input is rejected.
Only one states a security property, the unforgeability of leanXMSS, for EthLib's own definitions.
No theorem states unforgeability for leanSPHINCS or BLS, or binding for KZG.
No theorem covers the code that runs, the C boundary, or timing.

### XMSS

The correctness theorem is `verify_keyGen_sign` (`Proofs/Xmss/Correctness.lean`).
If `keyGen seed` returns a key pair, and `sign` returns a signature for a message at a leaf index, then `verify` accepts that signature under that public key.
It says nothing about unforgeability.

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
It bounds every run, including the unlucky ones, so the bound is weaker than `2^-127` per adversary call, in two ways:

- Key generation alone makes `K = 13,434,881` calls, about `2^23.7`, so the bound is never below about `2^-103.3`.
- A signing request can try up to `2^32` randomizers on each layer before one gives a codeword.
  So each signing request adds more than `2^33` to `q`, and an adversary with `n >= 1` requests gets a bound above `n * 2^-94`.

The bound is classical: the adversary queries the oracle as a classical algorithm.
The statement is written with VCVio's oracle computations and probabilities, so their definitions are part of what it says.

### Merkle trees

leanXMSS, leanSPHINCS, the VRF tree and SSZ build their trees on one definition.
Two theorems in `Proofs/Merkle/Binding.lean` describe what a path binds, for every node hash.
The first is `climb_binding`, about two climbs from one position that reach one node.
They are equal, or `findCollision` returns a collision of the node hash at an ancestor of that position.
The second is `climb_binding_node`, about a climb that reaches an honest node but is not the honest climb.
Then `findSecondPreimage` returns a second preimage of an honest ancestor.

Both searches are explicit algorithms, proved to return valid answers.
So the statements say something, even though every compressing hash has collisions.
No theorem bounds the probability of finding a collision or a second preimage.

The VRF's `verify_unique` and the leanXMSS unforgeability proof use `climb_binding`.
leanXMSS also states `fold_binding` with `climb_binding_node`, which its unforgeability proof does not use.
SSZ uses neither.

### leanSPHINCS

The correctness theorem is `verify_keyGen_sign` (`Proofs/Sphincs/Correctness.lean`).
If `keyGen seed` returns a key pair, and `sign` returns a signature for a message, then `verify` accepts that signature under that public key.

`verify_known_answer` (`Proofs/Sphincs/KnownAnswerVerify.lean`) checks one pinned signature's bytes against one pinned public key's bytes.
The kernel evaluates every one of the 492 permutations.

`all_counters_fail_probability` (`Proofs/Sphincs/CodeSize.lean`) bounds a number: if digests were uniform, signing would fail with probability below `exp(-2^18)`.
That digests are uniform is not proved.

The 127-bit unforgeability bound of the configuration is a theorem about the specification's own Lean model, outside EthLib.
No theorem links that model to this module.

### VRF tree

A VRF tree commits to secret outputs under one root, and later opens them one index at a time.
Two theorems in `Proofs/Vrf/Verify.lean` describe it.
`verify_unique` says that two openings that verify at one index under one root give one output, or Keccak-256 collides.
It holds for every root, including one built to cheat.
`verify_opening` says that the opening of an honest tree verifies, with the output of its secret.

Uniqueness is reduced to a collision, and no theorem bounds the cost of finding one.
No theorem says that an output is unpredictable before it is opened.

### BLS12-381

The BLS theorems check the constants, because a wrong digit in a modulus or in the generator would very likely make one of them fail.
`modulus_prime` (`Proofs/Bls/FpZMod.lean` and `Proofs/Bls/FrZMod.lean`) proves that both moduli are prime.
`seven_pow_card_sub_one` and `seven_pow_div_prime_ne_one` (`Proofs/Bls/FrZMod.lean`) prove that `7` generates the multiplicative group of the scalar field; `7` is also the KZG constant `PRIMITIVE_ROOT_OF_UNITY`.
`addOrderOf_toPoint_generator` (`Proofs/Bls/G1Order.lean`) proves that the G1 generator has order `r`.

No theorem proves that `pairingCheck` computes a bilinear, non-degenerate pairing.
`PairingLaws` (`Proofs/Bls/PairingLaws.lean`) states the consequence that verification needs, as one hypothesis.
Let `P_i` represent `a_i * g_1` and `Q_i` represent `b_i * g_2`, where a representative is any valid point with that group element.
Then the check of the pairs `(P_i, Q_i)` passes exactly when `sum_i a_i * b_i = 0` in `Fr`.
The law holds when the check tests `prod_i e(P_i, Q_i) = 1` for any bilinear map `e` with `e(g_1, g_2) != 1` into a group of order `r`.
`pairingCheck_congr` (`Proofs/Bls/PairingCongr.lean`) proves that the check depends only on the group elements of valid points, so the law can quantify over representatives.

The kernel computes the pairing of the two generators and finds the value that [draft-irtf-cfrg-pairing-friendly-curves-11](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-11) publishes in Appendix B (`pairing_generators`, `Proofs/Bls/PairingKnownAnswer.lean`).
This known answer supports the pairing law but does not prove it.

`keyValidatePoint_eq_ok_iff` (`Proofs/Bls/KeyValidate.lean`) proves that key validation accepts exactly the encodings of the nonzero points of order `r` in G1.
The G1 and G2 subgroup checks accept exactly the valid points that represent a multiple of the generator.
Every output of the map to G2 is a valid point of that subgroup (`Proofs/Bls/MapToCurve.lean`).

`sign_ok` and `popProve_ok` (`Proofs/Bls/Signatures.lean`) prove that BLS signing never fails.
Under the pairing law, an honest signature, an honest proof of possession and an aggregate of honest signatures verify (`verify_sign`, `popVerify_popProve`, `aggregateVerify_aggregate`, `Proofs/Bls/SignaturesCorrect.lean`).
For the fast aggregate verification on one message, `fastAggregateVerify_aggregate` also assumes that the secret keys do not sum to zero modulo `r`.
Otherwise the aggregate key is the point at infinity, and key validation rejects it.

Under the pairing law, a key and a message have at most one signature that verifies, byte for byte (`verify_unique`, `Proofs/Bls/SignaturesUnique.lean`).
From a victim's key alone, an attacker builds a second key and a signature that passes the fast aggregate verification for both (`fastAggregateVerify_rogue`).
So each key of that verification needs a verified proof of possession.

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

The pairing law is a hypothesis, `AltBn128.PairingLaws` (`Proofs/AltBn128/PairingLaws.lean`), in the shape of the BLS one.
It states the check of EIP-197: the pairs `(a_i P1, b_i g2)` pass exactly when `sum_i a_i b_i = 0`.
No theorem proves it.

`ecadd_toPoint` and `ecmul_toPoint` (`Execution/Proofs/Evm/Precompiles/AltBn128Group.lean`) carry this group law to the precompiles.
A call of ECADD that succeeds returns the sum of its two points, and a call of ECMUL returns its point times its 32-byte scalar.

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
The kernel checks FIPS 197 Appendix B and the AES-128 and AES-256 vectors of its 2001 Appendix C.
It also checks the first two blocks of the CTR examples F.5.1 and F.5.5 of SP 800-38A.

`decrypt_encrypt` (`Proofs/Aes/Gcm.lean`) proves that GCM decryption of SP 800-38D returns the plaintext of an honest ciphertext and tag.
`decrypt_eq_ok` proves that decryption accepts no tag other than the honest one.
Both hold for every forward cipher.
`encrypt_shortTag` and `decrypt_shortTag` prove that both functions reject the 64-bit and 32-bit tags, which SP 800-38D Appendix C restricts.
The kernel checks seven test cases of the NIST CAVP file `gcmtestvectors.zip`, one of them a forged tag that decryption rejects.

### KZG

`Proofs/Kzg/Core.lean` proves that the public operations reject malformed inputs, such as a wrong size or lists of different lengths.
Each operation takes the trusted setup as an argument and returns `Except KzgError`, so the kernel can unfold it.
`computeCellsAndKzgProofs_blob_spec` and `recoverCellsAndKzgProofs_spec` (`Proofs/Kzg/Fk20Proofs.lean`) state the cells and proofs that two operations return, under hypotheses on the setup.
No theorem states what a verification operation returns on accepted input.

`checksSufficient` (`Proofs/Kzg/CeremonyChecks.lean`) is about the ceremony that produced the trusted setup.
It proves that the ceremony's pairing checks force each G1 and G2 point of a contribution to be the expected power of the trapdoor.
It holds under four hypotheses besides the checks themselves:

- `ConcreteBlsLaws`, one law the repository does not prove yet, `pairingEq_mul_iff`: on multiples of the generators, the concrete pairing check holds exactly when the scalar products agree, which is bilinearity and non-degeneracy;
- `SubgroupExponents`, exponents witnessing that every point involved is a multiple of its group's generator, which stands in for the subgroup checks;
- `previousTauNonzero`, that the previous transcript's tau point is not at infinity;
- `pubkeyNonzero`, that the contributor's public key is not at infinity.

`ConcreteBlsLaws` follows from the pairing law `PairingLaws` (`PairingLaws.concrete`).
`checksSufficient_of_pairingLaws` states the same theorem with `PairingLaws` in its place.

### EVM instructions

Each instruction follows execution-specs, which computes with Python integers.
Lean core defines the same operations on `BitVec`, independently of EthLib.
The theorems in `Execution/Proofs/Evm/Instructions/` prove that the two agree, apart from the divisor 0, where the EVM returns 0.
`sdiv_eq` covers the quotient of -2^255 by -1, the one signed quotient that does not fit in a word, and `bitwiseSar_eq` covers every shift up to 2^256 - 1.
The 38 test cases of EIP-145 pin SHL, SHR and SAR.

No theorem relates the definitions to the Yellow Paper, and the stack, gas and program counter are not modelled yet.

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
`modexp_out_of_gas` and `modexp_ok` (`Execution/Proofs/Evm/Precompiles/Modexp/Core.lean`) prove that, with every length within the EIP-7823 bound, a call fails exactly when the gas is below the price.

No theorem relates the module to the execution-specs code it follows.

### BLAKE2F

The theorems pin down the input format exactly, and leave the compression function F to known answers.
`blake2f_invalidLength`, `blake2f_invalidFlag` and `blake2f_ok` (`Execution/Proofs/Evm/Precompiles/Blake2f.lean`) prove that a call fails exactly when the input is not 213 bytes long, or its flag byte is neither `0` nor `1`.
Otherwise it returns `compute` of the input, which decodes the fields and runs F of RFC 7693 on them.
`readWord_toNat`, `readRounds_toNat` and `writeState_word` state the encoding of EIP-152 for every input: the rounds field big-endian, every word little-endian, and the output in the encoding of the input.

F itself is checked by known answers only (`Cryptography/Proofs/Hash/Blake2b.lean` and `Execution/Proofs/Evm/Precompiles/Blake2f.lean`).
They are RFC 7693 Appendix A, one full block of the BLAKE2 test vectors, test vectors 4 to 7 of EIP-152, the rounds field of test vector 8, and one call that sets `t1`.
No theorem states the output of test vector 8, which asks for `2^32 - 1` rounds.

### ECRECOVER

The ECRECOVER theorems rest on the secp256k1 ones, and all three are in `Execution/Proofs/Evm/Precompiles/Ecrecover/Core.lean`.
`output_sign` proves that a signature made with a private key returns that key's address.
`output_verify` proves that a nonempty output is the address of a key that verifies the signature.
`output_of_verify` proves that every key that verifies a signature has its address returned for `v = 27` or `v = 28`, when `r + n >= p`.

No theorem relates the module to the execution-specs code it follows, which calls a C library to recover the key.

### EIP-2537 encodings

The BLS12-381 precompiles read and write field elements and points in the encoding of EIP-2537.
`bytesToG1_g1ToBytes` and `bytesToG2_g2ToBytes` (`Execution/Proofs/Evm/Precompiles/Bls12381/RoundTrip.lean`) prove that decoding the encoding of a valid point gives the same group element.
With the subgroup check, the same holds for a point of the subgroup.
`g1ToBytes_bytesToG1` (`Execution/Proofs/Evm/Precompiles/Bls12381/Encoding.lean`) and `g2ToBytes_bytesToG2` prove the converse, so every decoded point has one encoding.
The same file proves the round trips of a field element, an element of `Fp2` and the padding.

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

`root_binding` and `verifyProof_sound` assume that the keys of each trie have distinct paths.
A secured trie hashes each key into its path, so there the assumption is that no two of its keys have one hash.
No theorem bounds the probability of finding a collision.

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

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
`checksSufficient` is the main one today, and its four hypotheses are listed under KZG.
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

Every AES function that takes a key handles secret data.
Its S-box is a table, and the cipher reads it at indices that depend on the key.
No binding exposes AES.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
EthLib has one such theorem, and one idealisation:

- leanXMSS: the hash `H`, Keccak-256, is a random oracle on byte strings.
  The theorem says nothing about an attack that uses the structure of Keccak.

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

CI runs that check on the committed vectors on every change, but it does not regenerate them, which takes hours.
So for B1 and B4 the regeneration is a local step, and only the check after it shows that the bindings still produce the committed answers.

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
Lean exports 48 operations and 38 size constants.
The Python extension calls 48 of the operations and 29 of the constants.
Exported constants it does not call: `eth_sphincs_const_chains`, `eth_sphincs_const_n`, `eth_sphincs_const_public_param_len`, `eth_sphincs_const_randomizer_len`, `eth_xmss_const_chains`, `eth_xmss_const_digest_len`, `eth_xmss_const_layer_height`, `eth_xmss_const_public_param_len`, `eth_xmss_const_randomizer_len`.
<!-- end generated -->

<!-- generated: c-lines -->
2427 lines of hand-written C sit between them and Python: `bls.c` (332), `ecrecover.c` (34), `enr.c` (91), `keccak.c` (38), `kzg.c` (533), `modexp.c` (61), `module.c` (595), `precompile.c` (43), `ripemd160.c` (36), `secp256k1.c` (94), `secp256r1.c` (42), `sha256.c` (38), `sha256_precompile.c` (62), `sphincs.c` (94), `wrappers.h` (191), `xmss.c` (143).
<!-- end generated -->

That C converts arguments, owns and frees Lean objects, and turns errors into Python exceptions.
The vectors test this layer only through the regeneration and comparison of B1.
Each typed Lean error becomes a `RuntimeError` with the operation's name, and the Lean message is dropped.
A wrong argument size is caught in C first, and raises `ValueError`.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust, but the code that runs is still not the definition a reader reads.

The repository has none of the three today.
`lake exe check-decls` reports any of them, and fails on one that is not in its baseline.

### B6. The build and its publication

`setup.py` runs `lake build Exports`, and links the objects under `.lake/build/ir/EthLib/` with `libleanshared`, `libgmp` and `libuv`.
`.github/workflows/publish.yml` builds the wheels with `cibuildwheel`, cleans the build before each wheel, and publishes them to PyPI.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set; a theorem may use fewer.

`lake exe check-decls` checks dependencies: no declaration may depend on an axiom outside that set, apart from those in its baseline.
It does not check the kernel, and it does not show that the axioms are consistent.
That rests on Lean's own design and review, and no independent checker replays the environment yet (C3).

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
An independent checker that replays the environment, such as `lean4checker`, would catch it, but none runs yet.

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
  For the embedded bytes, only the first part is proved, and only in part.
  `TrustedSetup.ofHex_valid` (`Proofs/Kzg/TrustedSetup.lean`) proves that, if they decode, each point is on its curve.
  No theorem says that they decode, or that the points lie in the subgroup.
  `checksSufficient` covers the ceremony's monomial points, under its hypotheses.
- Secrecy: no one knows the secret, which holds if at least one ceremony participant was honest.
  Only binding, a security property, needs it; a theorem about parsing, or that an honest proof verifies, does not.

### D4. The vectors

A client that tests against the vectors trusts whatever produced their expected values.
The KZG vectors and the `eth_*` BLS vectors match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte.
The other BLS vectors match `ethereum/bls12-381-tests` `v0.1.2`, and the hash-to-curve vectors come from RFC 9380.
`v1.7.0-alpha.12` was the last release before consensus-specs removed its KZG specification, in ethereum/consensus-specs#5398.

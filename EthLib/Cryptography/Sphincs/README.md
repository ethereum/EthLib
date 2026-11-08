# leanSPHINCS signatures

leanSPHINCS is a stateless hash-based signature scheme, proposed for post-quantum transaction signatures on Ethereum.
It is SLH-DSA of [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205) on Keccak-256, with WOTS+C as its one-time signature and a hypertree whose layers have different heights.

This module specifies one configuration: Keccak-256, FORS, and a layered key for `2^30` signatures.

- The few-time signature is FORS: 24 trees of 1024 leaves, whose roots `T_k` hashes into the FORS public key.
- The one-time signature is WOTS+C: 64 chains of 4 positions, codewords of digit sum 128.
- The hypertree has three layers of heights 8, 8 and 10, from the bottom.

A message's digest picks a bottom leaf `idx`, and so one FORS instance, and one leaf in each FORS tree.
The FORS openings sign the digest.
The bottom one-time key signs the FORS public key, the middle key signs the bottom tree's root, and the top key signs the middle tree's root.
The top tree's root is `PK.root`.

A public key is `PK.seed | PK.root`, 32 bytes, and a signature is 7740 bytes.
Verification costs a constant 515 Keccak-f[1600] permutations.

## Source

The specification is the note [`doc/lean_sphincs/main.tex`](https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex) of `leanEthereum/leanVM`, at commit `5e3ade21d339a45e1b3b0dba97ad9300ab50e49b`.
That commit merged leanVM pull request [#662](https://github.com/leanEthereum/leanVM/pull/662), "leanSphincs closer to FIPS205", into `main`.

The note follows FIPS 205 except where its §1 lists a difference.
It fixes every byte: the hash inputs, the address encoding of its Appendix A, the digest layout and the signature layout.
leanVM's Rust implementation of the note, [`crates/signatures/src/lean_sphincs/`](https://github.com/leanEthereum/leanVM/tree/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/crates/signatures/src/lean_sphincs) at the same commit, implements the note.
Its known answer is a test vector here, as [Test vectors](#test-vectors) describes, and not a source of rules.
The note's Lean model, [`formal/lean_sphincs/`](https://github.com/leanEthereum/leanVM/tree/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/formal/lean_sphincs) at the same commit, proves the security bound of its §7 for 1,182,000,000 signatures, about `2^30.14`.

Each file cites the parts of the note and of FIPS 205 that it follows:

- `Constants.lean`: the parameter table of §2, and the sizes and costs of §6.4.
- `Types.lean`: `toInt` and `toByte` of FIPS 205 (Algorithms 2 and 3), and the keys `K_l(idx)` of §4.
- `Address.lean`: the address of Appendix A, which is FIPS 205's (§4.2) with one more type.
- `TweakableHash.lean`: `Th` and `PRF` of §2, as FIPS 205's SHAKE instances lay them out (§11.1).
- `Encoding.lean`: the encoding of §3, and WOTS+C from [ePrint 2022/778](https://eprint.iacr.org/2022/778).
- `Ots.lean`: WOTS+C of §3, hashed as WOTS+ of FIPS 205 §5.
- `Tree.lean`: the hypertree of §4, built on the shared [Merkle trees](../Merkle/).
- `Fors.lean`: FORS of §5, which is FORS of FIPS 205 §8, on the same Merkle trees.
- `Digest.lean`: `PRF_msg` and `H_msg` of §2, and the digest of §5, split as FIPS 205 Algorithm 19 does.
- `KeyGen.lean`: the keys of §2 and key generation of §6.1.
- `Sign.lean`: signing of §6.2.
- `Verify.lean`: verification of §6.3, and its cost in §6.4.
- `Serialization.lean`: the serialization of §6.4.

Keccak-256 is [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) with Keccak's original padding (`EthLib/Cryptography/Hash/Keccak.lean`).
Every integer on the wire is big-endian, as in FIPS 205: the address words, the counters of `H_msg` and of the encoding, and the digest fields.

## Choices this module makes

The secret key is `SK.seed`, and the exports of key generation and signing take it alone.
So the signer rebuilds `PK.root`, which `H_msg` hashes, with the definition that key generation uses.
It builds the top tree once for `PK.root` and once for the top key's path.
It builds each lower tree once for its root and once for the path.
It builds each FORS tree once for the FORS public key and once for the opening.
leanVM's Rust signer keeps the levels of each tree and builds it once.
The values are the same, so the signatures are the same.

The trees are built depth first by the shared Merkle definitions, where the Rust builds them level by level.
The nodes, and so the outputs, are the same.

Every chain start and every FORS secret is `PRF(PK.seed, SK.seed, ADRS)`, and the definitions that need one take the PRF as an argument.
A security proof can then replace these derivations as a whole, without reading `SK.seed`.

The key expansion hashes for `PK.seed` first and for `SK.prf` second, as the note's Lean model does.
The order changes no value.

## Operations

| Lean | File | C export | Python |
| --- | --- | --- | --- |
| `keyGen` | `KeyGen.lean` | `eth_sphincs_key_gen` | `sphincs.key_gen` |
| `sign` | `Sign.lean` | `eth_sphincs_sign` | `sphincs.sign` |
| `verify` | `Verify.lean` | `eth_sphincs_verify` | `sphincs.verify` |

The secret key is the 32-byte `SK.seed`, and everything else derives from it.
So the exports of `keyGen` and `sign` take the seed and rebuild what they need on each call.
`keyGen` builds the top tree, which means `2^10` one-time keys and 271,361 Keccak-f[1600] permutations, as §6.4 of the note counts them.
`sign` builds the top tree, the FORS instance and both lower trees, and searches three counters.
Since it builds each tree twice, it makes about twice the `5.25 * 10^5` permutations that §6.4 counts for one signature.
`verify` makes 515 Keccak-f[1600] permutations.

Never sign more than `2^30` messages with one key.
The digest picks a FORS instance at random, so instances are reused, and each signature from an instance weakens it.
Nothing in EthLib counts signatures, so the caller must.

## Test vectors

`tests/cryptography/sphincs/` has cases for `key_gen`, `sign` and `verify`.

The `key_gen_known_answer` and `sign_known_answer` cases are the known answer of leanVM's Rust implementation, `crates/signatures/src/lean_sphincs/known_answer.hex` at the pinned commit.
The key is that of `SK.seed[i] = 37 i + 11 mod 256`, and the signature signs `M[i] = 7 i + 3`.
The Python suite checks both cases against those bytes on every run, and again when it regenerates them.
So the two cases fix every hash that key generation, signing and verification make.
A test also checks `PK.seed`, the first 16 bytes of the key, through the Keccak-256 binding rather than through key generation.
Two cases reject the known-answer signature with a zeroed FORS secret and with a zeroed top sibling.
The other cases come from the code under test.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Sphincs/`.

Every definition that hashes takes the hash as an argument, as leanXMSS's definitions do.
`keyGen`, `sign` and `verify` pass Keccak-256.
Each theorem about such a definition holds for every hash function, run in the identity monad.
Keccak-256 is one such function, so the theorems cover the specification as it runs.
Definitions that derive a secret take the derivation function as an argument too, and their theorems hold for every such function.

- Correctness.
  A key from `keyGen` verifies every signature that `sign` makes with it (`verify_keyGen_sign`, `Correctness.lean`).
- What verification checks.
  `verify` accepts exactly when the three layers, from the recovered FORS public key up, lead to the key's root (`verify_iff`, `Verify.lean`).
- Signing.
  The counter search returns the least counter whose encoding is a codeword (`findFirst_spec`).
  leanXMSS shares that search and the hash chains, in [`Wots.lean`](../Wots.lean).
  Signing fails only when a one-time key finds no codeword (`sign_error`, `Sign.lean`).
- FORS (`Fors.lean`).
  An honest opening recovers its tree's root (`treeRecover_treeOpen`).
  Honest openings recover the instance's FORS public key, the hash `T_k` of the 24 roots (`forsRecover_forsSign`).
- The hypertree (`Tree.lean`, `Correctness.lean`).
  An honest path leads from a key's leaf to its tree's root (`fold_path_root`).
  A tree hashes only at its own levels, so every node address names the true level (`path_eq_of_agree`, `fold_eq_of_agree`).
  A FORS node at height `z` depends only on the node hash at heights 1 to `z`, so its root on heights 1 to 10 (`forsNode_eq_of_agree`, `forsRoot_eq_of_agree`).
  An opened path holds nodes below height 10, so it depends only on heights 1 to 9 (`treeOpen_path_eq_of_agree`).
  Each higher key signs the root of the tree its index names on the layer below (`OtsKey.ofIndex_child`).
- The digest (`Digest.lean`).
  The digest is the first 34 bytes of two Keccak-256 calls, split as FIPS 205's Algorithm 19 splits it.
  Read as a big-endian number, its top 240 bits are the 24 leaves of 10 bits, and its low 26 bits are the index (`digest_fields`).
  The 6 bits between them are not read, and two digests with the same index and leaves agree on all 266 bits that are read (`digest_fields_inj`).
- The code (`Encoding.lean`, `CodeSize.lean`).
  The digits of a digest are FIPS 205's `base_2b` with `b = 2`, most significant first (`digits_getElem_val_toInt`).
  They are a bijection from digests onto strings of 64 digits (`digits_bijective`).
  A codeword's digits sum to `T = 128` (`sum_of_codeword`).
  No two digests share a codeword (`eq_of_codeword`).
  Two distinct codewords are incomparable: each has a digit below the other's (`codeword_incomparable`).
  The code has `23195210617839120199658819909693679` words, counted two ways (`card_digitStrings_code`, `inclusion_exclusion_code`).
  So one counter succeeds with probability `2^-13.84`, if digests were uniform (`code_probability`).
  Then all `2^32` counters fail with probability below `exp(-2^18)` (`all_counters_fail_probability`).
  Exactly `|C|` of the `2^128` digests are codewords (`card_codeword`, `CodewordSearch.lean`).
- The counter search in the random oracle model (`CodewordSearch.lean`).
  All `2^32` counters of one search miss the code with probability exactly `(1 - |C| / 2^128)^(2^32)`, below `exp(-2^18)` (`prEvent_findCounter_none`, `prEvent_findCounter_none_le`).
  The theorem assumes that the oracle's cache holds none of the counters' inputs when the search starts, as an empty cache does.
- A whole signature in the random oracle model (`SignatureFailure.lean`).
  Signing fails with probability at most `3 exp(-2^18)`, one `exp(-2^18)` for each layer's search (`prEvent_signWith_error_le`).
  A trial input of a key is an input at the key's encoding address whose payload has the trial size.
  On every layer that size is 20 bytes: a 16-byte message and a 4-byte counter, so a trial input has 68 bytes.
  Before a key's search, the signer hashes no trial input of that key's layer.
  Its other calls are derivations, encodings on lower layers and hashes at addresses of other types.
  The inputs without an address have other lengths: 44 bytes for the key expansion, 93 for `PRF_msg` and 84 for `H_msg`.
  The theorem assumes that the cache holds no trial input of any key when signing starts, as an empty cache does (`prEvent_signWith_error_le_empty`).
- Domain separation (`Address.lean`, `TweakableHash.lean`).
  An address determines all six of its fields: the layer, the tree, the type and the three words that follow (`encodeAdrs_inj`).
  The eight address types have eight codes, 0 to 7 (`AdrsType.code_injective`).
  Each address of a key or a FORS instance determines its own arguments (`keyAdrs_inj`, `adrsNode_inj`, `adrsFors_forsTreeIndex_inj` and the others).
  A FORS node's tree index counts across the 24 trees, so it names its tree and node only for a node index below `2^(10 - z)` at height `z` (`adrsFors_forsTreeIndex_inj`).
  A hash input determines its `PK.seed`, address and payload (`thInput_inj`).
- Verification's hash calls (`Unforgeability/VerifyQueries.lean`).
  Verification makes at most 491 calls, with any hash that makes at most one oracle call (`verifyWith_isTotalQueryBound`, `verifyCalls_eq`).
  A signature that verifies is checked with exactly 491 calls (`length_verifyQueries_of_verify`).
  When a fixed function answers the oracle, verification computes EthLib's verification with that function as its hash (`evalWithAnswerFn_verifyWith`).
  Two answer functions that agree on the inputs verification hashes give the same verdict (`verifyWith_congr`).
- The hash calls of key generation and signing (`Unforgeability/HonestQueries.lean`).
  Key generation, signing and verification commute with every map of monads that keeps `pure` and `bind` (`keyGenWith_map_monad`, `signWith_map_monad`).
  Outside the derivations from the seed and the two calls of `H_msg`, every call hashes at an address of another type, with a payload of at least 16 bytes (`signDerived_isQueryBoundP_zero`, `publicKeyOf_isQueryBoundP_zero`, `verifyWith_isQueryBoundP_zero`).
  The lemmas for one layer take each key's encodings as a separate hypothesis, since a key's search queries its own (`EncodingAvoids`).
  So in the game, key generation and each signing request make at most two 44-byte queries, those of the key expansion of `SK.seed` (`keyGenWith_H_isQueryBoundP_seedLength`, `signWith_H_isQueryBoundP_seedLength`, `size_expandInput`).
- Unforgeability in the random oracle model (`Unforgeability.lean`).
  Take an adversary that makes at most `2^30` signing requests and whose experiment makes at most `q >= 1` hash calls.
  The count `q` includes the calls of key generation, of every signing request and of the final verification.
  The adversary forges with probability at most `q / 2^127` (`unforgeable`).
  The game is stated in `Unforgeability/Bridge/Statement.lean`.
- The security proof (`Security/`).
  It is a ported model of the scheme with its theorem for this configuration (`h26_layered`): 127 bits, up to 1,182,000,000 signatures.
  Its README gives the provenance and every change to the ported text.
  The model signs its layers from the bottom up, as EthLib and leanVM's Rust signer do.
  The version that EthLib ported first signed them from the top down, and its author confirmed in [leanVM#720](https://github.com/leanEthereum/leanVM/issues/720) that this order is a bug.
  At the pinned commit the model signs from the bottom up itself.
- The bridge to the model (`Unforgeability/Bridge/`).
  EthLib's bytes, addresses, keys and signatures translate to the model's and back.
  Key generation and verification make the model's calls, call for call (`keyGenWith_queryH`, `verifyWith_queryH`).
  Under every fixed answer of the oracle, the signer gives the model's signature under the model's key from the same seed, and both fail together (`signWith_answers`).
  So an EthLib forgery is a model forgery of a translated adversary (`forgeAdvantage_le`).
  Under every fixed answer of the oracle, a signing request costs the model at most what it costs EthLib (`hashCalls_sign_le`).
  Both signers stop at the same failing layer, and their counter searches and paths make the same number of calls.
  Before the layers, EthLib makes 337636 calls: it expands the key, rebuilds the top tree, derives the randomizer, hashes the message and opens FORS.
  The model makes 73709 calls there.
  Below the top layer, the model recovers the layer's root from the signature with 74 calls, and EthLib computes each layer's message with at least 66047.
  So a budget of `q` hash calls against EthLib is a budget of `q` against the model (`hasHashQueryBound_translate_self`).
- Serialization (`Serialization.lean`).
  Decoding succeeds exactly on strings of the declared length, and encoding and decoding are inverse bijections there.

## What is not proved

- Security for more than one key, or for more than `2^30` signing requests.
- A bound for the game of `Unforgeability/Game.lean`.
  Its budget counts only the adversary's own queries and requests, and it has no signing limit.
- That a later signature, or a signature inside the unforgeability game, fails with small probability.
  The failure bound assumes a starting cache with no trial input of any key.
  An earlier signature under the same key caches the trial inputs of its keys, and in the game the adversary's queries can too.

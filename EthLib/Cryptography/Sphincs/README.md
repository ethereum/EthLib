# leanSPHINCS signatures

leanSPHINCS is a stateless hash-based signature scheme, proposed for post-quantum transaction signatures on Ethereum.

This module specifies one configuration: Keccak-256, FORS, and a layered key for `2^30` signatures.

- The few-time signature is FORS: 24 trees of 1024 leaves, with no root hash.
- The one-time signature is WOTS+C: 64 chains of 4 positions, codewords of digit sum 128.
- The hypertree has three layers of heights 10, 8 and 8, top first.

A message's digest picks a bottom leaf `idx`, and so one FORS instance, and one leaf in each FORS tree.

The FORS openings sign the message.

The bottom one-time key signs the FORS key, the middle key signs the bottom tree's root, and the top key signs the middle tree's root.

The top tree's root is the public key.

A public key is 32 bytes and a signature 7740 bytes.

Verification costs a constant 492 Keccak-f[1600] permutations.

## Source

The specification is the note [`leanSPHINCS.tex`](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex) and its Lean model [`formal/sphincs/FORS/Scheme.lean`](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean), both at commit `1538d0a97845c3b771088f09561ddf7607b560a1` of `TomWambsgans/sphincs.art`.

The configuration is the layered key of `2^30` in §1 of the note.

In the model it is `Params.layered 26 3 8 24 10`, with the signature limit 1,182,000,000, about `2^30.14`.

The note fixes the parameters and the costs.

The model fixes every byte: addresses, hash inputs, the digest layout and the signature layout.

Each file cites the definitions it follows:

- `Constants.lean`: §1 of the note, and `Params.layered`.
- `Address.lean`: `fieldBytes`, `hashDomainFields` and `keygenDomainFields`.
- `TweakableHash.lean`: `tweakableHashInput`, `truncateHash` and `hashHalf`.
- `Encoding.lean`: `TargetSum.digestEncoding`, and WOTS+C from [ePrint 2022/778](https://eprint.iacr.org/2022/778).
- `Ots.lean`: `otsSecrets`, `chainWalk`, `encode`, `otsSign` and `otsLeaf`.
- `Tree.lean`: `Seeded.treeNode`, `Seeded.treePath` and `treeFold`.
- `Fors.lean`: `forsNode`, `forsKey`, `treeOpen`, `treeRecover` and `forsRecover`, and FORS from [FIPS 205](https://doi.org/10.6028/NIST.FIPS.205) §8.
- `Digest.lean`: `deriveRandomizer`, `messageDigest`, `digestIndex` and `digestLeaves`.
- `KeyGen.lean`: `keygenFromSeed`.
- `Sign.lean`: `Seeded.sign`.
- `Verify.lean`: `Concrete.verify`.
- `Serialization.lean`: `serializeSignature` in [`FORS/Scheme/Layout.lean`](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme/Layout.lean).

Keccak-256 is [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) with Keccak's original padding (`EthLib/Cryptography/Hash/Keccak.lean`).

The model's hash outputs are bit vectors.

This module reads a 32-byte output as a little-endian number, so its first 16 bytes are the model's low 128 bits.

## Choices this module makes

The secret key is the 32-byte seed, used as the model's `keygenFromSeed` uses it.

No hash of the configuration comes first.

So one seed must never serve two configurations, or their one-time keys would coincide.

Every index lands in the key, so the signer keeps the first randomizer `R_0`.

The walk `R_0 + i * delta` of the model is never needed, and it is not computed.

A FORS node of level 1 derives its pair of secrets once in the model, and once per leaf here.

The values are the same, so the signatures are the same.

## Operations

```text
Lean       file
keyGen     KeyGen.lean
sign       Sign.lean
verify     Verify.lean
```

The secret key is the seed, and everything else derives from it.

- `keyGen` builds the top tree: `2^10` one-time keys, about 231,000 hashes.
- `sign` builds the FORS key and openings, both lower trees and the top tree's path, and searches three counters: about half a million Keccak-f[1600] permutations.
- `verify` makes 492 Keccak-f[1600] permutations.

Never sign more than `2^30` messages with one key.

Nothing in EthLib counts signatures, so the caller must.

There are no C exports or Python bindings yet.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Sphincs/`.

- Correctness.
  A key from `keyGen` verifies every signature that `sign` makes with it (`verify_keyGen_sign`, `Correctness.lean`).
- What verification checks.
  `verify` accepts exactly when the three layers, from the recovered FORS key up, lead to the key's root (`verify_iff`, `Verify.lean`).
- Signing.
  The counter search returns the least counter whose encoding is a codeword (`findCounter_spec`, `Ots.lean`).
  Signing fails only when a one-time key finds no codeword (`sign_error`, `Sign.lean`).
- FORS (`Fors.lean`).
  An honest opening recovers its tree's two level-9 nodes, in order (`treeRecover_treeOpen`).
  Honest openings recover the instance's FORS key (`forsRecover_forsSign`).
- The hypertree (`Tree.lean`, `Correctness.lean`).
  An honest path leads from a key's leaf to its tree's root (`fold_path_root`).
  Each higher key signs the root of the tree its index names on the layer below (`OtsKey.ofIndex_child`).
- The digest (`Digest.lean`).
  The digest is two Keccak-256 calls, and the index and the 24 leaves are exactly its low 266 bits (`digest_fields`).
  The two calls have distinct addresses (`addrMsg_inj`).
- The code (`Encoding.lean`, `CodeSize.lean`).
  A codeword's digits sum to `T = 128` (`sum_of_codeword`).
  No two digests share a codeword (`eq_of_codeword`).
  Two distinct codewords are incomparable: each has a digit below the other's (`codeword_incomparable`).
  The code has `23195210617839120199658819909693679` words, counted two ways (`card_digitStrings_code`, `inclusion_exclusion_code`).
  So one counter succeeds with probability `2^-13.84`, if digests were uniform (`code_probability`).
  Then all `2^32` counters fail with probability below `exp(-2^18)` (`all_counters_fail_probability`).
- Domain separation (`Address.lean`, `TweakableHash.lean`).
  An address determines all six of its fields (`encodeAddress_inj`).
  The eleven address types have eleven codes (`AddressType.code_injective`).
  Each address of a key or a FORS instance determines its own arguments (`keyAddress_inj`, `addrNode_inj`, `addrForsNode_inj` and the others).
  A hash input determines its public parameter, address and payload (`thInput_inj`).
- Serialization (`Serialization.lean`).
  Decoding succeeds exactly on strings of the declared length, and encoding and decoding are inverse bijections there.
- Known answer (`KnownAnswer*.lean`).
  One key, from the seed `S[i] = 37 i + 11`, and one signature of the message `m[i] = 7 i + 3`, are pinned byte for byte.
  The public parameter, from the seed, matches the public key (`publicParam_known_answer`).
  The signature's bytes verify under the public key's bytes (`verify_known_answer`).
  A changed FORS secret and a changed top sibling each reject (`verify_tampered_fors_secret`, `verify_tampered_top_path`).

## What is not proved

- Any security property, such as unforgeability.
  The 127-bit bound, up to 1,182,000,000 signatures, is the theorem `h26_layered` of the model's [`FORS/Main.lean`](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Main.lean), about the model, not about this module.
- That this module and the model compute the same bytes.
  The definitions follow the model line by line, but no theorem links the two.
- That signing fails with small probability.
  `all_counters_fail_probability` bounds the number, assuming uniform digests, which is the random-oracle assumption.
- That every codeword is the codeword of some digest.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems above.

The kernel checks the known answer itself, with no `native_decide`.

One verification is too large for one kernel check, so it is checked in pieces: the digest, the FORS trees a few at a time, and for each layer the codeword, the chains, the leaf and the path.

The pieces run over a record form of Keccak-f, with the hash inputs as lists, which the kernel evaluates far faster than the specification's vectors and arrays.

`Proofs/Hash/KeccakKernel.lean` proves the record form equal to Keccak-f for every state, and `Proofs/Sphincs/Kernel.lean` carries that through the chains, the paths and the FORS climbs.

The public key from the seed needs the whole top tree, `2^10` one-time keys, which is beyond the kernel.

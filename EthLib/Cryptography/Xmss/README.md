# XMSS signatures

XMSS is a hash-based signature scheme, proposed to replace BLS on a post-quantum consensus layer for Ethereum.

A key covers a range of epochs, and each epoch signs at most one message, ever.

This instance has 32-byte public keys and 1208-byte signatures, small enough for one 1280-byte IPv6 datagram.

This page was checked against EthLib commit `a0838f3`.
Check it again when a definition it names changes.

## Source

EthLib's issue #29 names three sources:

- the specification note `doc/xmss/main.tex` in `leanEthereum/leanVM`;
- the implementation `crates/xmss` in the same repository, which this module is meant to stay byte-compatible with;
- the paper with the construction and its security analysis, [ePrint 2025/055](https://eprint.iacr.org/2025/055).

[leanEthereum/leanVM#640](https://github.com/leanEthereum/leanVM/pull/640) removed the note and the crate.
Their last text is at leanVM commit `a0ca7858f2533ce51abdc20bb635c007e19b26b3`, the parent of that removal:

- [`doc/xmss/main.tex`](https://github.com/leanEthereum/leanVM/blob/a0ca7858f2533ce51abdc20bb635c007e19b26b3/doc/xmss/main.tex);
- [`crates/xmss`](https://github.com/leanEthereum/leanVM/tree/a0ca7858f2533ce51abdc20bb635c007e19b26b3/crates/xmss).

leanVM now specifies a different scheme, in `doc/lean_xmss/main.tex`.
This module does not implement it.

Every constant in `Constants.lean` agrees with the crate at that commit, except the trial cap.
`MAX_RANDOMIZER_TRIALS` is `2^23` here, and `2^32` in the note and the crate.
Signing takes the first randomizer that encodes, so the two agree whenever one of the first `2^23` trials succeeds.
When all of them fail, this module returns an error, where the crate keeps trying.
The docstring of `MAX_RANDOMIZER_TRIALS` gives the reason for the smaller cap: each trial enters the security bound.

The byte layout of a signature differs too.
The note and the crate serialize the chain values first, then the randomizer, then the path.
This module puts the randomizer first, the order of the note's signature tuple `(rho, sigma_OTS, path)`:

```text
note and crate:  [ 42 chain values: 672 | randomizer: 24 | 32 siblings: 512 ]
this module:     [ randomizer: 24 | 42 chain values: 672 | 32 siblings: 512 ]
```

Both are 1208 bytes, so a length check cannot tell them apart.
A signature encoded by one decodes to different fields in the other.

The public key has the same layout in all three: the root, then the public parameter.

The code cites two more sources:

- the WOTS+C encoding, [ePrint 2022/778](https://eprint.iacr.org/2022/778) (`Encoding.lean`);
- BLAKE2s-256, [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) (`EthLib/Cryptography/Hash/Blake2s.lean`).

Keys and signatures encode as their fields concatenated, each at a fixed offset (`Serialization.lean`).

## Operations

```text
Lean       file            C export            Python
keyGen     KeyGen.lean     eth_xmss_key_gen    xmss.key_gen
sign       Sign.lean       eth_xmss_sign       xmss.sign
verify     Verify.lean     eth_xmss_verify     xmss.verify
```

The secret key is the seed and the epoch range, and everything else is derived from the seed.
So the exports of `keyGen` and `sign` take the seed and the range, and rebuild the key on each call.

Never sign two different messages at one epoch with one key.
Nothing in EthLib records which epochs a key has signed, so the caller must prevent reuse.

## Test vectors

`tests/cryptography/` has no XMSS vectors yet.

The proofs pin one public key and one signature instead.
The key covers epochs 6 to 8 and grows from the seed `0, 1, ..., 31`, and the signature is that key's at epoch 7.
The pull requests that added them, #40 and #42, say that `crates/xmss` produced them.
They do not record which commit of the crate.

The known answers compare structured keys and signatures, not their bytes.
So they do not show that the serialized forms agree, and for signatures the layouts above differ.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Xmss/`.

- Correctness.
  A key from `keyGen` verifies every signature that `sign` makes with it (`verify_keyGen_sign`, `Correctness.lean`).
- What verification checks.
  `verify` accepts exactly when the message encodes under the signature's randomizer, and the leaf recovered from the chain elements climbs the path to the key's root (`verify_iff`, `Verify.lean`).
- Errors.
  Key generation fails exactly when the epoch range is empty (`keyGen_eq_error_iff`, `KeyGen.lean`).
  Signing fails with `epochOutOfRange` exactly when the epoch is outside the key's range (`sign_eq_error_epochOutOfRange`, `Sign.lean`).
- The randomizer.
  Signing returns the first trial whose randomizer encodes (`findRandomness_first`, `Sign.lean`).
  The target-sum code is at least a `2^-15` share of all `2^128` digests (`code_probability`, `CodeSize.lean`).
  Reading that share as one trial's chance of success is part of the completeness argument, not of the theorem.
- The encoding (`Encoding.lean`).
  Two different valid encodings are incomparable: each has a digit smaller than the other's (`wotsEncode_incomparable`).
- Domain separation (`TweakHash.lean`, `Encoding.lean`).
  The input of a tweakable hash determines its tweak type, positions, public parameter and payload (`tweakInput_injective`).
  Inputs of different tweak types never coincide (`tweakInput_ne_of_type_ne`).
  No query of key generation equals the query that encodes a message (`keyGen_query_ne_encoding_query`).
- The trees.
  Walking revealed chain elements to the end recovers the one-time public key (`otsRecover_otsReveal`, `Ots.lean`).
  For an epoch in the key's range, its authentication path climbs from its leaf to the root (`computeRoot_authPath`, `Merkle.lean`).
- Serialization (`Serialization.lean`).
  Decoding a signature succeeds exactly on `SIG_SIZE` bytes, and encoding the result returns those bytes (`decodeSignature_success_iff`, `encodeSignature_decodeSignature`).
  The same holds for public keys.
- Known answers.
  `keyGen_known_answer` and `sign_known_answer` reproduce the key and the signature above.
  `verify_known_answer` accepts the signature, and `verify_wrong_epoch` and `verify_tampered_path` reject it at another epoch and with a changed path.
- BLAKE2s (`Proofs/Hash/Blake2s.lean`).
  The kernel checks six known answers, among them the RFC 7693 Appendix B example.

## What is not proved

- Any security property, such as unforgeability, or the security bound of the note and the paper.
- That signing fails with small probability.
  `code_probability` bounds the fraction of digests that belong to the code.
  Turning that fraction into a chance that signing succeeds needs further probabilistic assumptions.
  The bound for all `2^23` trials is only argued in the docstring of `MAX_RANDOMIZER_TRIALS`.
- That this module and `crates/xmss` compute the same keys and signatures on any input other than the known answers.
- Anything about BLAKE2s beyond its known answers and facts about its blocks and words.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems above.

The kernel checks `verify_known_answer`, `verify_wrong_epoch` and `verify_tampered_path` itself.

`keyGen_known_answer` and `sign_known_answer` use `native_decide` instead.
For the key, a root over three leaves is too deep for the kernel's evaluator, and for the signature, grinding takes thousands of attempts.
`native_decide` trusts the compiled code, and `scripts/check_decls_baseline.txt` lists both as `native`.

# leanXMSS signatures

leanXMSS is a hash-based signature scheme, proposed to replace BLS on a post-quantum consensus layer for Ethereum.

A key is two layers of Merkle trees of height 16, whose leaves are WOTS+C one-time keys.

The top layer is one tree, and its root is the public key.

The bottom layer is `2^16` trees, and key `b` of the top tree signs the root of bottom tree `b`.

So a key signs at `2^32` leaf indices, each one at most once, ever.

```text
                      top tree               root = public key
                     /   ...   \
           top key b signs the root of bottom tree b
                         |
     ... bottom tree b-1 | bottom tree b | bottom tree b+1 ...
                              |
              bottom key idx signs the message
```

A public key is 32 bytes and a signature 2404 bytes.

## Source

The specification is the note "leanXMSS for Ethereum PQ-Consensus, specification draft", [`doc/lean_xmss/main.tex`](https://github.com/leanEthereum/leanVM/blob/55f8b0389c6cceab02dee82a003e40f7d80d0699/doc/lean_xmss/main.tex) at commit `55f8b0389c6cceab02dee82a003e40f7d80d0699`.

Its hash `H` is BLAKE2s-256 (RFC 7693) at that commit.

Each module cites the section it implements:

```text
Constants.lean        Hashing and parameters
Address.lean          Address encoding
TweakableHash.lean    Hashing and parameters
Encoding.lean         WOTS+C, Codewords
Ots.lean              WOTS+C
Tree.lean             Trees
KeyGen.lean           The scheme, Key generation
Sign.lean             The scheme, Signing
Verify.lean           The scheme, Verification
Serialization.lean    The scheme, Serialization
```

The names follow the note: `Th` is `th`, `Ots.sign` is `otsSign`, `Tree.fold` is `fold`.

The code cites two more sources:

- the target-sum code of WOTS+C, [ePrint 2022/778](https://eprint.iacr.org/2022/778) (`Encoding.lean`);
- BLAKE2s-256, [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) (`EthLib/Cryptography/Hash/Blake2s.lean`).

One step computes a value of the note another way.

To sign, the note's top key signs the root `X^0_{16,b}` of bottom tree `b`.

`sign` computes that root by folding the bottom key's leaf up its own path, 16 hashes, instead of the whole tree.

`fold_path` proves the two equal, and `verify_sign` uses it.

## Operations

```text
Lean       file            C export            Python
keyGen     KeyGen.lean     eth_xmss_key_gen    xmss.key_gen
sign       Sign.lean       eth_xmss_sign       xmss.sign
verify     Verify.lean     eth_xmss_verify     xmss.verify
```

The secret key is the 32-byte seed, and everything else derives from it.

So the exports of `keyGen` and `sign` take the seed and rebuild what they need on each call.

- `keyGen` builds the top tree: `2^16` one-time keys.
- `sign` builds the paths of both keys: about one tree on each layer.

Never sign two different messages at one leaf index with one key.

Nothing in EthLib records which leaf indices a key has signed, so the caller must prevent reuse.

## Test vectors

`tests/cryptography/` has no leanXMSS vectors yet.

The proofs pin one full key and one signature instead (`Proofs/Xmss/KnownAnswer*.lean`).

The key grows from the seed `S_0[i] = 37 i + 11 mod 256`, and the signature signs `m[i] = 7 i + 3` at leaf index `0xA5C37E19`.

The public key and the signature bytes were computed outside EthLib, by an independent implementation of the note.

The compiled `keyGen` and `sign` reproduce both, byte for byte.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Xmss/`.

- Correctness.
  A key from `keyGen` verifies every signature that `sign` makes with it (`verify_keyGen_sign`, `Correctness.lean`).
- What verification checks.
  `verify` accepts exactly when the bottom layer leads to some root, and the top layer, signing that root, leads to the key's root (`verify_iff`, `Verify.lean`).
- Signing.
  Grinding returns the least trial whose digest is a codeword (`findCodeword_spec`, `Ots.lean`).
  Signing fails only when a one-time key finds no codeword (`sign_error`, `Sign.lean`).
- The code (`Encoding.lean`, `CodeSize.lean`).
  A codeword's digits sum to `T = 106` (`sum_of_codeword`).
  No two digests share a codeword (`eq_of_codeword`).
  Two distinct codewords are incomparable: each has a digit below the other's (`codeword_incomparable`).
  The code has `323504418562481994618807509487594` words, so one trial succeeds with probability `2^-20.0045` (`card_onTarget`, `code_probability`).
- Domain separation (`Address.lean`, `TweakableHash.lean`).
  An address determines its type, its position and both fields (`encodeAddress_inj`).
  The two layers never share an address (`layerHi_inj`).
  Each address of a key determines its own arguments (`addrPrf_inj` and the five like it).
  A hash input determines its public parameter, address and payload (`thInput_inj`).
- The one-time signature and the trees.
  An honest one-time signature leads back to its key's leaf (`otsLeaf_otsSign`, `Ots.lean`).
  An honest path leads from a key's leaf to its tree's root (`fold_path`, `Tree.lean`).
- Serialization (`Serialization.lean`).
  Decoding succeeds exactly on strings of the declared length, and encoding and decoding are inverse bijections there.
- Known answers.
  The signature verifies under the public key (`verify_known_answer`).
  It rejects with a changed message, the neighbouring leaf index, or a changed path (`verify_wrong_message`, `verify_wrong_leafIndex`, `verify_tampered_path`).
  The scheme seed, the public parameter and both keys' leaves, computed from the seed, match the key and the signature (`KnownAnswer.lean`, `KnownAnswerKeyBottom.lean`, `KnownAnswerKeyTop.lean`).

## What is not proved

- Any security property, such as unforgeability, or the `q / 2^127` bound of the note.
- That signing fails with small probability.
  `code_probability` gives one trial's chance, if digests were uniform.
  That all `2^32` trials fail with probability below `exp(-2^11)` is only argued in the docstring of `MAX_RANDOMIZER_TRIALS`.
- That every codeword is the codeword of some digest.
  `eq_of_codeword` shows at most one digest per codeword, so at most `|C|` digests are codewords.
- That this module and any other implementation compute the same keys and signatures on inputs other than the known answer.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems above.

The kernel checks every known answer itself, with no `native_decide`.

A whole verification is too large for one kernel check, so the known answer checks it in pieces: each layer's codeword, a few chains at a time, the leaf and the path.

The pieces run over the fast form of BLAKE2s, with its hash inputs as lists, which the kernel evaluates far faster than the specification's arrays.
`Proofs/Xmss/Kernel.lean` proves each rewrite equal to the specification.

The public key from the seed needs the whole top tree, `2^16` one-time keys, which is beyond the kernel.

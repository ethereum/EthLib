# leanXMSS signatures

BLS signatures rest on elliptic curves, and a large enough quantum computer would break them.
leanXMSS is a hash-based signature scheme, proposed to replace BLS on a post-quantum consensus layer for Ethereum.
Its security rests only on the hash function.

The price is that each one-time key may sign only once, so a key is a large structure of many one-time keys.
A leanXMSS key is two layers of Merkle trees of height 16, whose leaves are WOTS+C one-time keys.
The top layer is a single tree, and its root is the public key.
The bottom layer is `2^16` trees, and key `b` of the top tree signs the root of bottom tree `b`.
A message is then signed by a key of a bottom tree, so a key signs at `2^32` leaf indices, each one at most once, ever.

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

The specification is the note "leanXMSS for Ethereum PQ-Consensus, specification draft", [`doc/lean_xmss/main.tex`](https://github.com/leanEthereum/leanVM/blob/4af2cdddd7cd41b9df2cc7e123e314a91b0b4462/doc/lean_xmss/main.tex) at commit `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`.
Its hash `H` is Keccak-256, Ethereum's hash.
Each module cites the section of the note it implements:

| File | Section of the note |
| --- | --- |
| `Constants.lean` | Hashing and parameters |
| `Address.lean` | Address encoding |
| `TweakableHash.lean` | Hashing and parameters |
| `Encoding.lean` | WOTS+C, Codewords |
| `Ots.lean` | WOTS+C |
| `Tree.lean` | Trees |
| `KeyGen.lean` | The scheme, Key generation |
| `Sign.lean` | The scheme, Signing |
| `Verify.lean` | The scheme, Verification |
| `Serialization.lean` | The scheme, Serialization |

The names follow the note: `Th` is `th`, `Ots.sign` is `otsSign`, `Tree.fold` is `fold`.
The code cites two more sources: [ePrint 2022/778](https://eprint.iacr.org/2022/778) for the target-sum code of WOTS+C (`Encoding.lean`), and [FIPS 202](https://csrc.nist.gov/pubs/fips/202/final) with Keccak's original padding for Keccak-256 (`EthLib/Cryptography/Hash/Keccak.lean`).

## The hash as an argument

The note proves its security theorem in the random oracle model, where `H` is an ideal random function that the adversary can only query.
For a proof in that model to be about the code that runs, the code must not fix its hash.
So every definition that hashes takes the hash `H` as an argument, a function that runs in a monad.
`keyGen`, `sign` and `verify` run them in the identity monad with Keccak-256 (`hashId`), and a security proof passes a query to the oracle as `H` instead.

The oracle sees every hash call, in the order the code makes them.
So the code makes its calls as the note defines them, one by one and in a fixed order:

- a vector of hashes is computed entry 0 first (`ofFnInOrder`);
- a node computes its left subtree, then its right subtree, then its own hash;
- `sign` builds the root `X^0_{16,b}` of bottom tree `b` from the whole tree, as the note defines it.

## Operations

| Lean | File | C export | Python |
| --- | --- | --- | --- |
| `keyGen` | `KeyGen.lean` | `eth_xmss_key_gen` | `xmss.key_gen` |
| `sign` | `Sign.lean` | `eth_xmss_sign` | `xmss.sign` |
| `verify` | `Verify.lean` | `eth_xmss_verify` | `xmss.verify` |
| `signatureIndex` | `Serialization.lean` | `eth_xmss_signature_index` | `xmss.signature_index` |

The secret key is the 32-byte seed, and everything else derives from it.
So the exports of `keyGen` and `sign` take the seed and rebuild what they need on each call.
`keyGen` builds the top tree, which means `2^16` one-time keys.
`sign` builds the paths of both keys and the root of the bottom tree, which costs about two trees on the bottom layer and one on the top.

Never sign two different messages at one leaf index with one key.
A one-time key that signs two different messages can reveal enough chain values for a forgery, and nothing in EthLib records which leaf indices a key has signed, so the caller must prevent reuse.

`signatureIndex` reads the leaf index a signature carries, its first 4 bytes, without verifying it.
A caller can use it to require a given leaf before verifying, such as leaf 0 for a proof of possession.

## Test vectors

`tests/cryptography/xmss/` has cases for `key_gen`, `sign`, `verify` and `signature_index`.

The proofs also pin one full key and one signature (`Proofs/Xmss/KnownAnswer*.lean`).
The key grows from the seed `S_0[i] = 37 i + 11 mod 256`, and the signature signs `m[i] = 7 i + 3` at leaf index `0xA5C37E19`.
The public key and the signature bytes were computed outside EthLib, by an independent implementation of the note.
The `key_gen_known_answer` and `sign_known_answer` cases hold the same bytes.
The other cases are EthLib's own: nothing outside EthLib has checked them yet.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Xmss/`.

**Correctness.**
The first thing a signature scheme must do is accept honest signatures.
A key from `keyGen` verifies every signature that `sign` makes with it (`verify_keyGen_sign`, `Correctness.lean`).
Because the hash is an argument, the same holds for every hash function, not only Keccak-256 (`verifyWith_keyGenWith_signWith`).

**What verification checks.**
`verify` accepts exactly when the bottom layer leads to some root, and the top layer, signing that root, leads to the key's root (`verify_iff`, `Verify.lean`).
This turns the code of `verify` into a statement a reader can check against the note at a glance.

**Signing.**
To sign, WOTS+C tries randomizers one after another until the digest of the message is a codeword, a step called grinding.
Grinding returns the least trial whose digest is a codeword (`findCodeword_spec`, `Ots.lean`), and signing fails only when a one-time key finds no codeword (`sign_error`, `Sign.lean`).

**The code.**
A codeword is a vector of digits whose sum is a fixed target, and the proofs establish the properties the security argument needs (`Encoding.lean`, `CodeSize.lean`).
A codeword's digits sum to `T = 106` (`sum_of_codeword`), and no two digests share a codeword (`eq_of_codeword`).
Two distinct codewords are incomparable: each has a digit below the other's (`codeword_incomparable`).
Incomparability is what stops a forger: to sign a different codeword from a signature, they would have to walk some chain backwards, which means inverting the hash.
The code has `323504418562481994618807509487594` words, so one trial succeeds with probability `2^-20.0045` (`card_onTarget`, `code_probability`).

**Domain separation.**
Every hash call carries an address that says where in the key it happens, so that two calls never hash the same input by accident (`Address.lean`, `TweakableHash.lean`).
An address determines its type, its position and both fields (`encodeAddress_inj`), and the two layers never share an address (`layerHi_inj`).
Each address of a key determines its own arguments (`addrPrf_inj` and the five like it).
Finally, a hash input determines its public parameter, address and payload (`thInput_inj`).

**The one-time signature and the trees.**
An honest one-time signature leads back to its key's leaf (`otsLeaf_otsSign`, `Ots.lean`), and an honest path leads from a key's leaf to its tree's root (`fold_path`, `Tree.lean`).
Another path that reaches that root exposes a second preimage of `Th` under the address of an ancestor (`fold_binding`, `Tree.lean`).
Both statements specialize theorems proved for every tree in [`Merkle`](../Merkle/).

**Serialization.**
Decoding succeeds exactly on strings of the declared length, and on those strings encoding and decoding are inverse bijections (`Serialization.lean`).
The leaf index read alone is the first 4 bytes, as a little-endian integer (`signatureIndex_eq_bytes`), and it agrees with full decoding (`signatureIndex_eq_decodeSignature`).
A signature from `sign` reads back the index it was signed at (`signatureIndex_sign`, `Sign.lean`).

**Unforgeability.**
In the random oracle model, an adversary whose experiment makes at most `q >= 1` hash calls forges with probability at most `q / 2^127` (`unforgeable`, `Unforgeability.lean`).
`q` counts every hash call of the experiment, key generation and signing included, so it is never below about `2^23.7`, plus more than `2^33` per signing request (`SOUNDNESS.md`).
The game is the note's section "Security", run on `keyGenWith`, `signWith` and `verifyWith` with `H` a query to the oracle.
The proof, adapted from leanerVM's, reasons over these same definitions (`Proofs/Xmss/Security/`).

**Known answers.**
The pinned signature verifies under the pinned public key (`verify_known_answer`).
It is rejected with a changed message, the neighbouring leaf index, or a changed path (`verify_wrong_message`, `verify_wrong_leafIndex`, `verify_tampered_path`).
The scheme seed, the public parameter and both keys' leaves, computed from the seed, match the key and the signature (`KnownAnswer.lean`, `KnownAnswerKeyBottom.lean`, `KnownAnswerKeyTop.lean`).

## What is not proved

- No security property is proved beyond the random oracle model, so the theorem says nothing about an attack that uses the structure of Keccak-256.
- Security against a quantum adversary is not proved.
- No theorem says that signing fails with small probability.
  `code_probability` gives one trial's chance, if digests were uniform, and the claim that all `2^32` trials fail with probability below `exp(-2^11)` is only argued in the docstring of `MAX_RANDOMIZER_TRIALS`.
- No theorem says that every codeword is the codeword of some digest.
  `eq_of_codeword` shows at most one digest per codeword, so at most `|C|` digests are codewords.
- No theorem says that this module and any other implementation compute the same keys and signatures on inputs other than the known answer.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems in the previous section.

The kernel checks every known answer itself, with no `native_decide`.
A whole verification is too large for one kernel check, so the known answer checks it in pieces: each layer's codeword, a few chains at a time, the leaf and the path.
The pieces run over a record form of Keccak-f, with the hash inputs as lists, which the kernel evaluates far faster than the specification's vectors and arrays.
`Proofs/Hash/KeccakKernel.lean` proves the record form equal to Keccak-f for every state, and `Proofs/Xmss/Kernel.lean` carries that through the chains and the paths.

The public key from the seed needs the whole top tree, `2^16` one-time keys, which is beyond the kernel.

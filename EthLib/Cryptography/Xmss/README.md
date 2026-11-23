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

Every object the scheme hashes is 16 or 32 bytes, and the scheme's name is 8 bytes.
So the code holds every value as Keccak lanes, the 64-bit words of FIPS 202 §3.1.2, with the byte order of its Appendix B.1.
`H` takes a string of lanes and returns the four lanes of its digest, which Keccak-256 absorbs and squeezes without moving a byte.
Bytes appear only in the encodings of keys and signatures.
In the random oracle model, the scheme queries the byte oracle at the bytes of its lanes, and the adversary queries it at any byte string.
A string of lanes and its bytes determine each other, so the scheme queries only byte strings whose length is a multiple of 8.
The security theorems are therefore about the byte oracle that the note defines.

The oracle sees every hash call, in the order the code makes them.
So the code makes its calls as the note defines them, one by one and in a fixed order:

- a vector of hashes is computed entry 0 first (`ofFnInOrder`);
- a node computes its left subtree, then its right subtree, then its own hash;
- signing builds the root `X^0_{16,b}` of bottom tree `b` from the whole tree, as the note defines it, unless the key keeps that tree.

Every secret derives from the scheme seed `S = H("leanXMSS" | S_0)`, and so does the public parameter, which the public key publishes.
These derivations are the public parameter, the chain starts and the randomizer bases.
Each of these values is a half of a hash `H(P | A | S | suffix)`, with `P = 0^128` for the public parameter itself.
The suffix is empty, except for a randomizer base, whose suffix is the message.
The definitions take the derivations as one function argument of type `SeedPrf`, as they take `H`.
`keyGen` and `sign` pass `seedPrf`, the derivations from `S`, so a security proof can replace the derivations as a whole without reading the seed.

## Operations

| Lean | File | C export | Python |
| --- | --- | --- | --- |
| `keyGen` | `KeyGen.lean` | `eth_xmss_key_gen` | `xmss.key_gen` |
| `sign` | `Sign.lean` | `eth_xmss_sign` | `xmss.sign` |
| `verify` | `Verify.lean` | `eth_xmss_verify` | `xmss.verify` |
| `signatureIndex` | `Serialization.lean` | `eth_xmss_signature_index` | `xmss.signature_index` |

The note's secret key is the 32-byte seed, and everything else derives from it.
Here the secret key also keeps what signing reads: the scheme seed, the public parameter, the top tree, and the bottom trees it signed in last.
`keyGen` builds the top tree to compute the public key, `2^16` one-time keys, so the key keeps that tree at no extra cost.
`sign` returns the signature and an updated key.
A signature at leaf index `idx` needs bottom tree `b = floor(idx / 2^16)` and the signature of its root by top key `b`.
That top signature is the same for all `2^16` indices of the tree.
So the key keeps up to 8 bottom trees, each with that top signature, and drops the one it used longest ago.
A signature in a kept tree costs one one-time signature; otherwise it costs one bottom tree and the top key's search.
Signing never rebuilds the top tree.

The C extension keeps the secret key of the last 2 seeds it saw, so `xmss.key_gen(seed)` and `xmss.sign(seed, ...)` keep their Python signatures and still take only the seed.

Never sign two different messages at one leaf index with one key.
A one-time key that signs two different messages can reveal enough chain values for a forgery, and nothing in EthLib records which leaf indices a key has signed, so the caller must prevent reuse.

`signatureIndex` reads the leaf index a signature carries, its first 4 bytes, without verifying it.
A caller can use it to require a given leaf before verifying, such as leaf 0 for a proof of possession.

## Test vectors

`tests/cryptography/xmss/` has cases for `key_gen`, `sign`, `verify` and `signature_index`.

The `key_gen_known_answer` and `sign_known_answer` cases pin one full key and one signature.
The key grows from the seed `S_0[i] = 37 i + 11 mod 256`, and the signature signs `m[i] = 7 i + 3` at leaf index `0xA5C37E19`.
The public key and the signature bytes were computed outside EthLib, by an independent implementation of the note.
The `verify` cases check that this signature verifies, and that it fails with a changed message, leaf index, randomizer, chain value or sibling.
Twelve more `verify` cases keep its leaf, its path and its root, and sign one layer under a digest that is not a codeword.
The other cases are EthLib's own, and nothing outside EthLib checks them yet.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Xmss/`.

**The kept trees change no signature.**
The note's signer is stateless: it rebuilds every tree from the seed.
A key that `keyGen`, then any sequence of `sign` calls, gives is called reachable.
For every hash `H`, a key reached by `keyGenWith H`, then any sequence of `signWith H` calls, gives the note's signature, byte for byte, at every leaf index (`SecretKey.Reachable.signWith_fst`, `Sign.lean`).
`sign` is that signer over Keccak-256 (`sign_eq`).
That theorem writes the signature out: each layer's one-time signature, with the key's path computed from the seed.
Key generation gives the root of the top tree and the parameter `P` (`keyGenWith_fst`).

**Correctness.**
The first thing a signature scheme must do is accept honest signatures.
The public key of a seed verifies every signature that a reachable key of that seed makes (`verify_keyGen_sign`, `Correctness.lean`).
Because the hash is an argument, the same holds for every hash function, not only Keccak-256 (`verifyWith_keyGenWith_signWith`).

**What verification checks.**
`verify` accepts exactly when the bottom layer leads to some root, and the top layer, signing that root, leads to the key's root (`verify_iff`, `Verify.lean`).
This turns the code of `verify` into a statement a reader can check against the note at a glance.

**Signing.**
To sign, WOTS+C tries randomizers one after another until the digest of the message is a codeword, a step called grinding.
Grinding returns the least trial whose digest is a codeword (`findFirst_spec`), and signing with a reachable key fails only when a one-time key finds no codeword (`sign_error`, `Sign.lean`).
leanSPHINCS shares that search and the hash chains, in [`Wots.lean`](../Wots.lean).
With Keccak-256, the randomizer of a trial fills two lanes of the last block of the hash input.
So `sign` builds the state before the last permutation once per search, and each trial XORs its randomizer into it and permutes once.
Those trials give the codeword that hashing each trial gives (`keccakTrials_eq`, `Trials.lean`), so `sign` is the signer over Keccak-256 (`sign_eq`, `Sign.lean`).

**The code.**
A codeword is a vector of digits whose sum is a fixed target, and the proofs establish the properties the security argument needs (`Encoding.lean`, `CodeSize.lean`).
A codeword's digits sum to `T = 106` (`sum_of_codeword`), and no two digests share a codeword (`eq_of_codeword`).
Two distinct codewords are incomparable: each has a digit below the other's (`codeword_incomparable`).
Incomparability is what stops a forger: to sign a different codeword from a signature, they would have to walk some chain backwards, which means inverting the hash.
The code has `323504418562481994618807509487594` words, so one trial succeeds with probability `2^-20.0045` (`card_onTarget`, `code_probability`).
Exactly that many 16-byte digests are codewords (`card_codeword`, `CodewordSearch.lean`).

**The search rarely fails.**
In the random oracle model, all `2^32` trials of one search miss the code with probability exactly `(1 - |C| / 2^128)^(2^32)`, which is below `exp(-4000)` (`prEvent_findCodeword_none`, `prEvent_findCodeword_none_le`).
The theorem assumes that the oracle's cache holds none of the trial inputs when the search starts, as an empty cache does.

A whole signature fails with probability at most `2 exp(-4000)` (`prEvent_signWith_error_le`, `SignatureFailure.lean`).
A trial input of a key carries the key's message address and a payload of one length.
That length is 48 bytes on the bottom layer and 32 on the top.
Before a key's search, the signer hashes no such input.
Its other calls carry other addresses, and the input that grows the scheme seed has 40 bytes, too short to be a trial input.
The theorem assumes that the cache holds no trial input of the two keys when signing starts, as an empty cache does (`prEvent_signWith_error_le_empty`).
It also assumes that a bottom tree of that index, if the key keeps one, holds a top signature, not an error; a key from `keyGen` keeps no bottom tree.
Then the cache still holds none when each search starts, so each search fails with probability at most `exp(-4000)`.

**Domain separation.**
Every hash call carries an address that says where in the key it happens, so that two calls never hash the same input by accident (`Address.lean`, `TweakableHash.lean`).
An address determines its type, its position and both fields (`encodeAddress_inj`), and the two layers never share an address (`layerHi_inj`).
Two different call sites never share an address, whatever their kinds (`CallSite.encode_injective`).
So each address of a key determines its own arguments (`addrPrf_inj` and the five like it).
Finally, a hash input determines its public parameter, address and payload (`thInput_inj`).

**The scheme in bytes.**
The code holds its values as lanes, but the note writes every hash over bytes.
So for each hash the scheme makes, a theorem states the bytes that Keccak-256 hashes, in the note's order, and the bytes the scheme keeps (`Bytes.lean`).
They cover the tweakable hash (`th_bytes`), the scheme seed, the public parameter and the chain starts.
They also cover the randomizer base, a chain step, a one-time key's leaf, a trial's digest and a Merkle node.
The public key is the bytes of the top tree's root and of `P` (`encodePublicKey_keyGen`), and a signature's bytes are its fields in the note's order (`toList_encodeSignature`).
Given byte strings, verification accepts exactly when the key, the message and the signature they encode lead to the key's root (`verify_decode_iff`).

**The one-time signature and the trees.**
An honest one-time signature leads back to its key's leaf (`otsLeaf_otsSign`, `Ots.lean`), and an honest path leads from a key's leaf to its tree's root (`fold_path`, `Tree.lean`).
Another path that reaches that root lets `findSecondPreimage` compute a second preimage of `Th` under the address of an ancestor (`fold_binding`, `Tree.lean`).
Both statements specialize theorems proved for every tree in [`Merkle`](../Merkle/).

**Serialization.**
Decoding succeeds exactly on strings of the declared length, and on those strings encoding and decoding are inverse bijections (`Serialization.lean`).
The leaf index read alone is the first 4 bytes, as a little-endian integer (`signatureIndex_eq_bytes`), and it agrees with full decoding (`signatureIndex_eq_decodeSignature`).
A signature from `sign` reads back the index it was signed at (`signatureIndex_sign`, `Sign.lean`).

**Unforgeability.**
In the random oracle model, an adversary forges with probability at most `q / 2^127` (`unforgeable`, `Unforgeability.lean`).
The game is the note's section "Security", run on `keyGenWith`, `signWith` and `verifyWith` with `H` a query to the oracle, and its signer keeps its key across requests.
`q` bounds the hash calls of that game on every run, key generation and signing included, so it is never below about `2^23.7`, plus more than `2^32` per signing request (`SOUNDNESS.md`).
With all `2^32` leaf indices signed, `q` exceeds `2^64`, so over the key's lifetime the bound is above `2^-63`.
The proof, adapted from leanerVM's, reasons over these same definitions (`Proofs/Xmss/Security/`).

## What is not proved

- No security property is proved beyond the random oracle model, so the theorem says nothing about an attack that uses the structure of Keccak-256.
- Security against a quantum adversary is not proved.
- The failure bound of a whole signature assumes a starting cache with no trial input of its two keys.
  An earlier signature under the same top key caches that key's trial inputs, and in the unforgeability game the adversary's queries can too.
  So no theorem bounds the failure of a later signature, or of signing inside the game.
- No theorem says that this module and any other implementation compute the same keys and signatures.
  The test vectors check one key and one signature against an independent implementation.

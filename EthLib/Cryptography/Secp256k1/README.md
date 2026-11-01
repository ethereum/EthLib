# secp256k1

Every Ethereum transaction is signed with ECDSA over the curve secp256k1.
A transaction carries the signature but not the public key of its sender.
The verifier recovers that key from the signature, then hashes it into the sender's address.
This module specifies the three steps: verification, recovery, and the address.

## Source

Each part of the module follows the standard that defines it:

- The curve and its parameters come from [SEC 2 v2](https://www.secg.org/sec2-v2.pdf) §2.4.1.
- The group law, the point encodings and ECDSA come from [SEC 1 v2](https://www.secg.org/sec1-v2.pdf), §2.2.1, §2.3.3 to §2.3.8, §3.2.2.1, §4.1.3, §4.1.4 and §4.1.6.
- The low-s rule comes from [EIP-2](https://eips.ethereum.org/EIPS/eip-2).
- The recovery id and the address come from Appendix F of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

## Reading this module

The specification is written to be read rather than to be fast.
Points are in affine coordinates, as SEC 1 prints them, and inverses are computed by Fermat's little theorem.
The files build on one another in this order:

| File | Contents |
| --- | --- |
| `Field.lean` | the base field mod `p` and the scalar field mod `n` |
| `Curve.lean` | the points, and the addition rule of SEC 1 §2.2.1 |
| `Encoding.lean` | the 33-byte and 65-byte encodings, and their decoding |
| `Ecdsa.lean` | verification, and the low-s rule of EIP-2 |
| `Recovery.lean` | public key recovery |
| `Address.lean` | the address of a public key |

The proofs are in `EthLib/Cryptography/Proofs/Secp256k1/`, with one file for each of these, plus `Order.lean`.

## Operations

Three operations are exported to C, in `EthLib/Cryptography/Exports/Secp256k1.lean`, and from there to Python:

| Lean | C export | Python |
| --- | --- | --- |
| `Ecdsa.verify` | `eth_secp256k1_verify` | `secp256k1.verify` |
| `Ecdsa.isLowS` | `eth_secp256k1_is_low_s` | `secp256k1.is_low_s` |
| `Ecdsa.recover` | `eth_secp256k1_recover` | `secp256k1.recover` |

In Python, a malformed input raises `ValueError`.

## Test vectors

`tests/cryptography/secp256k1/` holds 818 pinned cases from the Wycheproof sets of `C2SP/wycheproof`, in the format each `format.md` describes.
The proofs also pin a few known answers, all checked by the kernel: both encodings of the generator `G`, from SEC 2; test 1 of the Wycheproof P1363 set; and the addresses of the private key 1 and of the two test keys of execution-specs.

## What is proved

The proofs start from the arithmetic.
The two moduli `p` and `n` are prime, which the proofs show with Pratt certificates, so both sets of residues are fields.
The inverse the code computes is the field inverse, and its square root succeeds exactly on the squares (`Field.lean`).

On top of the fields sits the group.
The addition rule of SEC 1 is the group law of the curve as Mathlib defines it, so every algebraic fact Mathlib knows about elliptic curves applies to the code.
The group has exactly `n` points.
Its cofactor is therefore 1, and every point is a multiple `k G` of the generator (`Curve.lean`, `Order.lean`).

A public key travels as bytes, so the encodings come next.
The decoder accepts exactly the two encodings, compressed and uncompressed, of the points other than the point at infinity `O`, and it returns the point that was encoded (`Encoding.lean`).

Verification is correct in the sense that matters to a signer: a signature produced by the signing operation of SEC 1 verifies (`Ecdsa.lean`).
ECDSA has a known malleability, which EIP-2 removes.
The proofs show that `(r, s)` and `(r, n - s)` are valid together, and that exactly one of the two has a low `s`.
So the low-s rule keeps one signature of each such pair and rejects the other.

Recovery is proved both ways (`Recovery.lean`).
A recovered key verifies the signature, and the signer's own key is among the keys recovered.
Conversely, when `r + n >= p`, every key that verifies a signature is recovered by id 0 or id 1.
The two ids give two different keys, and replacing `s` by `n - s` swaps them.

Finally, the address (`Address.lean`).
The bytes that are hashed are the uncompressed encoding of the key without its prefix byte, and every private key has an address.

## What is not proved

Three properties are outside the proofs.

- Unforgeability is not proved, because it rests on the hardness of the discrete logarithm problem, which no proof here assumes.
- Nothing is proved about timing: the specification is not constant-time, and it is not meant to sign with secret keys.
- Signing itself is out of scope, since it needs a nonce generator such as RFC 6979.

## What the kernel cannot evaluate

Nothing in this module.

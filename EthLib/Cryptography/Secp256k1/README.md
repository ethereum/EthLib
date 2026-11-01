# secp256k1

secp256k1 ECDSA signs every Ethereum transaction.

A transaction carries a signature and no public key: the key is recovered from the signature, and hashed into the sender's address.

## Source

- The curve and its parameters: [SEC 2 v2](https://www.secg.org/sec2-v2.pdf) §2.4.1.
- The group law, the point encodings and ECDSA: [SEC 1 v2](https://www.secg.org/sec1-v2.pdf), §2.2.1, §2.3.3 to §2.3.8, §3.2.2.1, §4.1.3, §4.1.4 and §4.1.6.
- The low-s rule: [EIP-2](https://eips.ethereum.org/EIPS/eip-2).
- The recovery id and the address: Appendix F of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

## Reading this module

```text
Field.lean      the base field mod p and the scalar field mod n
Curve.lean      the points, and the addition rule of SEC 1 §2.2.1
Encoding.lean   the 33-byte and 65-byte encodings, and their decoding
Ecdsa.lean      verification, and the low-s rule of EIP-2
Recovery.lean   public key recovery
Address.lean    the address of a public key
```

The proofs are in `EthLib/Cryptography/Proofs/Secp256k1/`, one file for each, plus `Order.lean`.

The specification is written to be read: affine coordinates, as SEC 1 prints them, and inverses by Fermat's little theorem.

## Operations

```text
Lean            C export                Python
Ecdsa.verify    eth_secp256k1_verify    secp256k1.verify
Ecdsa.isLowS    eth_secp256k1_is_low_s  secp256k1.is_low_s
Ecdsa.recover   eth_secp256k1_recover   secp256k1.recover
```

The exports are in `EthLib/Cryptography/Exports/Secp256k1.lean`.

A malformed input raises `ValueError` in Python.

## Test vectors

`tests/cryptography/secp256k1/` holds 818 pinned cases from the Wycheproof sets of `C2SP/wycheproof`, as each `format.md` describes.

The proofs also pin known answers, all checked by the kernel:

- both encodings of `G`, from SEC 2;
- test 1 of the Wycheproof P1363 set;
- the addresses of the private key 1 and of the two test keys of execution-specs.

## What is proved

- The fields (`Field.lean`).
  `p` and `n` are prime, by Pratt certificates.
  The inverse is the field inverse, and the square root succeeds exactly on squares.
- The group (`Curve.lean`, `Order.lean`).
  The addition rule of SEC 1 is the group law of the curve in Mathlib.
  The group has exactly `n` points, so the cofactor is 1, and every point is `k G`.
- The encodings (`Encoding.lean`).
  The decoder accepts exactly the two encodings of the points other than `O`, and returns the point encoded.
- Verification (`Ecdsa.lean`).
  A signature from the signing operation of SEC 1 verifies.
  `(r, s)` and `(r, n - s)` are valid together, and exactly one of them has a low `s`.
- Recovery (`Recovery.lean`).
  A recovered key verifies the signature, and the signer's key comes back.
  Every key that verifies a signature is recovered by id 0 or 1, when `r + n >= p`.
  The two ids give two different keys, and `n - s` swaps them.
- The address (`Address.lean`).
  The hashed bytes are the uncompressed encoding without its prefix, and every private key has an address.

## What is not proved

- Unforgeability: it rests on the discrete logarithm problem, which no proof here assumes.
- Anything about timing: the specification is not constant-time, and is not meant to sign with secret keys.
- Signing itself: a nonce generator, such as RFC 6979, is out of scope.

## What the kernel cannot evaluate

Nothing in this module.

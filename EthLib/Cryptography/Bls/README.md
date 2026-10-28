# BLS12-381 signatures

Ethereum's consensus layer signs with BLS signatures on the BLS12-381 curve.

Public keys are points of G1, in 48 bytes, and signatures are points of G2, in 96 bytes.

Many signatures over one message aggregate into one signature, which the aggregate of the signers' public keys verifies.

This page was checked against EthLib commit `a0838f3`.
Check it again when a definition it names changes.

## Source

The links below point to consensus-specs `v1.7.0-alpha.12`, commit `84454a9d57f4f49f74c78e9f375347baf30474f2`, the release the test vectors are pinned to.

- [`specs/phase0/beacon-chain.md`, "BLS signatures"](https://github.com/ethereum/consensus-specs/blob/84454a9d57f4f49f74c78e9f375347baf30474f2/specs/phase0/beacon-chain.md#bls-signatures) names the [IETF BLS signature draft, version 4](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04), with ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.
- [`specs/altair/bls.md`](https://github.com/ethereum/consensus-specs/blob/84454a9d57f4f49f74c78e9f375347baf30474f2/specs/altair/bls.md) defines the two Ethereum wrappers, `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`.

Since that release, `specs/altair/bls.md` has changed only in style: its string quotes, and `copy(x)` written as `x.copy()`.

Draft v4 references hash-to-curve draft 09, and FIPS 180-4 for SHA-256.

EthLib's implementation cites two standards, section by section:

- [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), the published version of the hash-to-curve drafts, with suite `BLS12381G2_XMD:SHA-256_SSWU_RO_` (`HashToCurve.lean`);
- FIPS 180-4, for SHA-256 (`EthLib/Cryptography/Hash/Sha256.lean`).

## Operations

```text
consensus-specs               Lean                       file              C export
eth_aggregate_pubkeys         ethAggregatePubkeys        Signatures.lean   eth_bls_aggregate_pubkeys
eth_fast_aggregate_verify     ethFastAggregateVerify     Signatures.lean   eth_bls_fast_aggregate_verify
```

They rest on these functions of the draft:

```text
draft                         Lean
KeyValidate                   G1.keyValidate             Compress.lean
FastAggregateVerify           fastAggregateVerify        Signatures.lean
CoreVerify                    coreVerify (private)       Signatures.lean
signature_subgroup_check      G2.inSubgroup              Compress.lean
hash_to_curve                 HashToCurve.hashToG2       HashToCurve.lean
```

EthLib has only this verification path.
It has no key generation, `Sign`, `Aggregate`, `Verify`, `AggregateVerify` or proof-of-possession functions.

The draft requires a proof of possession, verified with `PopVerify`, for every public key that `FastAggregateVerify` uses ([draft v4 §3.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3)).
`KeyValidate` does not check it, and nothing in EthLib does.
The caller must make sure that every public key passed to `ethFastAggregateVerify` has a verified proof of possession.

`ethFastAggregateVerify` takes a message of any length, as the draft's `FastAggregateVerify` does.
consensus-specs types the message as `Bytes32`, and nothing in EthLib checks that length.

## Test vectors

`tests/cryptography/bls/` holds 20 cases:

```text
handler                       cases
eth_aggregate_pubkeys             8
eth_fast_aggregate_verify        12
```

They match the consensus-specs `v1.7.0-alpha.12` general vectors byte for byte.
Their expected values come from the Python specification, not from EthLib.
`tests/cryptography/bls/SHA256SUMS` pins each one, and CI checks the pins.

[`tests/cryptography/README.md`](../../../tests/cryptography/README.md) explains the pins and the check against the upstream archive.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Bls/`.

They cover the fields and the group G1, not G2, the pairing or the signature functions.

A G1 point is valid when its representative is a nonsingular point of the curve.
Most statements below assume valid points.

- The fields.
  The moduli of `Fp` and `Fr` are prime (`modulus_prime`, `FpZMod.lean` and `FrZMod.lean`), and each type is a Mathlib field.
  7 generates the multiplicative group of `Fr`, of order `r - 1` (`isPrimitiveRoot_seven`, `FrZMod.lean`).
  KZG derives its roots of unity from that root.
- Square roots in `Fp` (`Compress.lean`).
  When `Fp.sqrt a` returns `c`, then `c * c = a` (`sqrt_ok`).
  When `a` has a square root, `Fp.sqrt a` returns `a^((p + 1) / 4)`, where `p` is the modulus of `Fp` (`sqrt_complete`).
- The group law of G1 (`G1Group.lean`).
  For valid `P` and `Q`, `add P Q` is valid and denotes the sum of the two curve points (`valid_add`, `toPoint_add`).
  For a valid `P`, `mul P s` denotes `s * P` (`toPoint_mul`).
- The generator (`G1Order.lean`).
  The G1 generator has order `r`, the modulus of `Fr` (`addOrderOf_toPoint_generator`).
- Multi-scalar multiplication (`G1Msm.lean`).
  Let `n` be the smaller of the two array lengths.
  When the first `n` points are valid, `msm` returns a valid point equal to `sum_{i < n} scalars_i * points_i` (`toPoint_msm`).
  For arrays of equal length, that sum covers every pair.
- Compression of G1 points (`Compress.lean`).
  For a valid `P`, decompressing `compress P` succeeds, and returns a point that denotes the same group element (`uncompress_compress`).
  The representation it returns may differ from that of `P`.

## What is not proved

- Anything about G2, the pairing, hash-to-curve or SHA-256.
- That `KeyValidate` and the subgroup checks accept exactly the points of the prime-order subgroups.
- What the signature functions return.
  In particular, no theorem says that an honest aggregate signature verifies.
- Any security property, such as unforgeability.
- `ConcreteBlsLaws`, the law of the pairing that the KZG ceremony theorem assumes: `pairingEq_mul_iff`, which is bilinearity with non-degeneracy.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems above.

`Fp2.powNat` and `Fp12.powNat` are `partial` definitions, which the kernel cannot unfold.
`scripts/check_decls_baseline.txt` lists both as `partial`.

`millerLoop` is declared `partial`, but it does not call itself, so Lean makes it an ordinary definition.
Its `while` loops reach `Loop.forIn`, which Lean core defines with `partial`.
The baseline lists it as `reaches-opaque`: it reaches an opaque constant when unfolded, but is not opaque itself.

The pairing check runs `millerLoop`, then raises the result to a power with `Fp12.powNat`.
Hash-to-curve clears the cofactor with constants computed by `Fp2.powNat`.
So the kernel cannot compute the result of `ethFastAggregateVerify` once its input reaches hash-to-curve and the pairing check.

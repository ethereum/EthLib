# BLS12-381 signatures

Ethereum's consensus layer has many validators sign the same message, and checking each signature on its own would cost one verification per signer.
So the protocol uses a scheme whose signatures add up.
A BLS signature lives on the BLS12-381 curve: a public key is a point of the group G1, encoded in 48 bytes, and a signature is a point of the group G2, encoded in 96 bytes.
Many signatures over one message aggregate into a single signature, and the aggregate of the signers' public keys verifies it with one check.

This page was checked against EthLib commit `a0838f3`.
Check it again when a definition it names changes.

## Source

The links below point to consensus-specs `v1.7.0-alpha.12`, commit `84454a9d57f4f49f74c78e9f375347baf30474f2`, the release the test vectors are pinned to.
Two documents there define what Ethereum means by a BLS signature:

- [`specs/phase0/beacon-chain.md`, "BLS signatures"](https://github.com/ethereum/consensus-specs/blob/84454a9d57f4f49f74c78e9f375347baf30474f2/specs/phase0/beacon-chain.md#bls-signatures) names the [IETF BLS signature draft, version 4](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04), with ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.
- [`specs/altair/bls.md`](https://github.com/ethereum/consensus-specs/blob/84454a9d57f4f49f74c78e9f375347baf30474f2/specs/altair/bls.md) defines the two Ethereum wrappers, `eth_aggregate_pubkeys` and `eth_fast_aggregate_verify`.

Since that release, `specs/altair/bls.md` has changed only in style: its string quotes, and `copy(x)` written as `x.copy()`.

Draft v4 in turn references hash-to-curve draft 09, and FIPS 180-4 for SHA-256.
EthLib's implementation cites the published versions of these, section by section: [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380), the final form of the hash-to-curve drafts, with suite `BLS12381G2_XMD:SHA-256_SSWU_RO_` (`HashToCurve.lean`), and FIPS 180-4 for SHA-256 (`EthLib/Cryptography/Hash/Sha256.lean`).

## Operations

A client calls the proof-of-possession scheme of the draft and the two Ethereum wrappers:

| Source | Lean | C export |
| --- | --- | --- |
| `Sign` | `sign` | `eth_bls_sign` |
| `Verify` | `verify` | `eth_bls_verify` |
| `Aggregate` | `aggregate` | `eth_bls_aggregate` |
| `AggregateVerify` | `aggregateVerify` | `eth_bls_aggregate_verify` |
| `FastAggregateVerify` | `fastAggregateVerify` | `eth_bls_fast_aggregate_verify_core` |
| `PopProve` | `popProve` | `eth_bls_pop_prove` |
| `PopVerify` | `popVerify` | `eth_bls_pop_verify` |
| `eth_aggregate_pubkeys` | `ethAggregatePubkeys` | `eth_bls_aggregate_pubkeys` |
| `eth_fast_aggregate_verify` | `ethFastAggregateVerify` | `eth_bls_fast_aggregate_verify` |

All of them live in `Signatures.lean`, on top of the core operations of the draft.
Key validation and the subgroup checks live in `Compress.lean`.

A secret key is an element of `Fr` other than zero, and the exports read it as 32 big-endian bytes.
EthLib has no key generation yet, and no function here runs in constant time.
As in the draft, aggregation does not check the subgroup of a signature.
Verification checks it.

Fast aggregate verification is safe only when no signer can choose a public key as a function of the others' keys, a so-called rogue-key attack.
The draft rules this out by requiring a proof of possession, verified with `PopVerify`, for every public key that `FastAggregateVerify` uses ([draft v4 §3.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3)).
`KeyValidate` does not check it, and the fast aggregate verifications do not call `PopVerify`.
The caller must make sure that every public key passed to `ethFastAggregateVerify` has a verified proof of possession.

The message length is also left to the caller.
`ethFastAggregateVerify` takes a message of any length, as the draft's `FastAggregateVerify` does, while consensus-specs types the message as `Bytes32`.
Nothing in EthLib checks that length.

## Test vectors

`tests/cryptography/bls/` holds 82 cases:

| Handler | Cases | Source |
| --- | ---: | --- |
| `eth_aggregate_pubkeys` | 8 | consensus-specs `v1.7.0-alpha.12` |
| `eth_fast_aggregate_verify` | 12 | consensus-specs `v1.7.0-alpha.12` |
| `sign` | 10 | `ethereum/bls12-381-tests` `v0.1.2` |
| `verify` | 29 | `ethereum/bls12-381-tests` `v0.1.2` |
| `aggregate` | 6 | `ethereum/bls12-381-tests` `v0.1.2` |
| `fast_aggregate_verify` | 12 | `ethereum/bls12-381-tests` `v0.1.2` |
| `aggregate_verify` | 5 | `ethereum/bls12-381-tests` `v0.1.2` |

Each case matches its source byte for byte, and no case's expected value comes from EthLib.
`tests/cryptography/hash_to_curve/` adds the hash to G2 and `expand_message_xmd` cases of RFC 9380.
Each directory has a `SHA256SUMS` that pins its cases, and CI checks the pins.
[`tests/cryptography/README.md`](../../../tests/cryptography/README.md) explains the pins and the check against the upstream archives.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Bls/`.
They cover the two fields and the group G1, which is what KZG commitments are built from.
They say nothing yet about G2 or the pairing.
Of the signature functions, they prove only that signing never fails.

Most statements concern valid points.
A G1 point is stored as a representative in coordinates, and it is *valid* when that representative is a nonsingular point of the curve.

**The fields.**
BLS12-381 uses two prime fields: `Fp`, over which the curve is defined, and `Fr`, whose order `r` is the order of the groups.
The proofs show that both moduli are prime (`modulus_prime`, in `FpZMod.lean` and `FrZMod.lean`), so each type is a Mathlib field and every lemma of field theory applies to it.
They also show that 7 generates the multiplicative group of `Fr`, which has order `r - 1` (`isPrimitiveRoot_seven`, `FrZMod.lean`).
KZG derives its roots of unity from that generator.

**Square roots in `Fp`.**
Decompressing a point means solving `y^2 = x^3 + 4` for `y`, so it needs a square root.
Two facts make `Fp.sqrt` trustworthy, both in `Compress.lean`.
It is sound: whenever it returns some `c`, then `c * c = a` (`sqrt_ok`).
It is complete: whenever `a` has a square root, `Fp.sqrt a` returns `a^((p + 1) / 4)`, where `p` is the modulus of `Fp` (`sqrt_complete`).

**The group law of G1.**
The code adds points with explicit coordinate formulas, and the proofs connect those formulas to the abstract group of curve points (`G1Group.lean`).
For valid `P` and `Q`, `add P Q` is again valid and denotes the sum of the two curve points (`valid_add`, `toPoint_add`).
For a valid `P`, `mul P s` denotes `s * P` (`toPoint_mul`).
Every later statement about sums of points rests on these three theorems.

**The generator.**
The G1 generator has order `r`, the modulus of `Fr` (`addOrderOf_toPoint_generator`, `G1Order.lean`).
This is why scalars can be taken modulo `r` without changing the point they produce.

**Multi-scalar multiplication.**
A KZG commitment is a sum `sum_i scalars_i * points_i`, computed by `msm` (`G1Msm.lean`).
Let `n` be the smaller of the two array lengths.
When the first `n` points are valid, `msm` returns a valid point equal to `sum_{i < n} scalars_i * points_i` (`toPoint_msm`).
For arrays of equal length, that sum covers every pair.

**Compression of G1 points.**
A public key travels as 48 bytes, the compressed form of a point.
For a valid `P`, decompressing `compress P` succeeds and returns a point that denotes the same group element (`uncompress_compress`, `Compress.lean`).
The theorem is about the group element, not the stored coordinates: the representation it returns may differ from that of `P`.

## What is not proved

- Nothing is proved about G2, the pairing, hash-to-curve or SHA-256.
- The map to G1 of EIP-2537 has no theorem: neither its validity nor its landing in the subgroup is proved.
- No theorem states what the signature functions return; in particular, none says that an honest aggregate signature verifies.
- No security property, such as unforgeability, is proved.
- `PairingLaws`, the law of the pairing check, is not proved: on representatives of `a_i * g_1` and `b_i * g_2`, the check passes exactly when `sum_i a_i * b_i = 0`.
  Theorems about the result of a pairing check take it as a hypothesis, and the KZG ceremony law `ConcreteBlsLaws` follows from it.

## What the kernel cannot evaluate

This is a limit on computing results inside Lean, separate from the missing theorems in the previous section.

`Fp2.powNat` and `Fp12.powNat` are `partial` definitions, which the kernel cannot unfold, and `scripts/check_decls_baseline.txt` lists both as `partial`.
`millerLoop` is a subtler case.
It is declared `partial`, but it does not call itself, so Lean makes it an ordinary definition.
Its `while` loops, however, reach `Loop.forIn`, which Lean core defines with `partial`.
The baseline therefore lists it as `reaches-opaque`: it reaches an opaque constant when unfolded, but is not opaque itself.

These three definitions sit on the verification path.
The pairing check runs `millerLoop`, then raises the result to a power with `Fp12.powNat`, and hash-to-curve clears the cofactor with constants computed by `Fp2.powNat`.
So the kernel cannot compute the result of `ethFastAggregateVerify` once its input reaches hash-to-curve and the pairing check.

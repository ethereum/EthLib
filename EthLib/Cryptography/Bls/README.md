# BLS12-381 signatures

Ethereum's consensus layer has many validators sign the same message.
Checking each signature on its own would cost one verification per signer.
So the protocol uses a scheme whose signatures add up.

A BLS signature lives on the BLS12-381 curve.
A public key is a point of the group G1, encoded in 48 bytes.
A signature is a point of the group G2, encoded in 96 bytes.
Many signatures over one message aggregate into a single signature.
The aggregate of the signers' public keys verifies it with one check.

This page was checked against EthLib commit `a0838f3`.
Check it again when a definition it names changes.

## Source

The scheme is the one of the [IETF BLS signature draft, version 4][draft-04].
Ethereum uses its proof-of-possession scheme, with the ciphersuite
`BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`.

Ethereum adds two wrappers around the draft.
The aggregation of public keys sums the validated keys, and it fails on an empty list.
The fast aggregate verification is the draft's, except that an empty key list passes exactly
with the signature of the point at infinity.

Draft v4 in turn references hash-to-curve draft 09, and FIPS 180-4 for SHA-256.
EthLib's implementation cites the published versions of these, section by section.
The hash to curve follows [RFC 9380][rfc9380], the final form of the hash-to-curve drafts.
Its suite is `BLS12381G2_XMD:SHA-256_SSWU_RO_` (`HashToCurve.lean`).
SHA-256 follows FIPS 180-4 (`EthLib/Cryptography/Hash/Sha256.lean`).

[draft-04]: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04
[rfc9380]: https://www.rfc-editor.org/rfc/rfc9380

## Operations

A client calls the proof-of-possession scheme of the draft and the two Ethereum wrappers:

| Source | Lean | C export |
| --- | --- | --- |
| `KeyGen` | `keyGen` | `eth_bls_key_gen` |
| `Sign` | `sign` | `eth_bls_sign` |
| `Verify` | `verify` | `eth_bls_verify` |
| `Aggregate` | `aggregate` | `eth_bls_aggregate` |
| `AggregateVerify` | `aggregateVerify` | `eth_bls_aggregate_verify` |
| `FastAggregateVerify` | `fastAggregateVerify` | `eth_bls_fast_aggregate_verify_core` |
| `PopProve` | `popProve` | `eth_bls_pop_prove` |
| `PopVerify` | `popVerify` | `eth_bls_pop_verify` |
| Ethereum key aggregation | `ethAggregatePubkeys` | `eth_bls_aggregate_pubkeys` |
| Ethereum fast aggregate verification | `ethFastAggregateVerify` | `eth_bls_fast_aggregate_verify` |

All of them but key generation live in `Signatures.lean`,
on top of the core operations of the draft.
Key validation and the subgroup checks live in `Compress.lean`.

A secret key is an element of `Fr` other than zero, and the exports read it as 32 big-endian bytes.
No function here runs in constant time.
Key generation, in `KeyGen.lean`, tries at most 16 salts.
It fails only if each salt gives a multiple of `r`.
As in the draft, aggregation does not check the subgroup of a signature.
Verification checks it.

Fast aggregate verification is safe only when no signer can choose a key from the others' keys.
Such a choice is a rogue-key attack.
The draft rules it out in §3.3: each key of `FastAggregateVerify` needs a proof of possession.
That proof is verified with `PopVerify`.

`KeyValidate` does not check it, and the fast aggregate verifications do not call `PopVerify`.
So each key passed to `ethFastAggregateVerify` needs a proof of possession that the caller verified.
`fastAggregateVerify_rogue` (`Proofs/Bls/SignaturesUnique.lean`) states the attack.
From a victim's key alone, an attacker builds a second key and one signature that passes for both.

The message length is also left to the caller.
`ethFastAggregateVerify` takes a message of any length, as the draft's `FastAggregateVerify` does.
Ethereum signs 32-byte roots, but nothing in EthLib checks that length.

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
Of the signature functions, they prove that signing never fails,
and that honest signatures verify under the pairing law.

Most statements concern valid points.
A G1 point is stored as a representative in coordinates,
and it is *valid* when that representative is a nonsingular point of the curve.

**The fields.**
BLS12-381 uses two prime fields: `Fp`, over which the curve is defined, and `Fr`,
whose order `r` is the order of the groups.
The proofs show that both moduli are prime (`modulus_prime`, in `FpZMod.lean` and `FrZMod.lean`),
so each type is a Mathlib field and every lemma of field theory applies to it.
They also show that 7 generates the multiplicative group of `Fr`,
which has order `r - 1` (`isPrimitiveRoot_seven`, `FrZMod.lean`).
KZG derives its roots of unity from that generator.

**Square roots in `Fp`.**
Decompressing a point means solving `y^2 = x^3 + 4` for `y`, so it needs a square root.
Two facts make `Fp.sqrt` trustworthy, both in `Compress.lean`.
It is sound: whenever it returns some `c`, then `c * c = a` (`sqrt_ok`).
It is complete: whenever `a` has a square root, `Fp.sqrt a` returns `a^((p + 1) / 4)`,
where `p` is the modulus of `Fp` (`sqrt_complete`).

**The group law of G1.**
The code adds points with explicit coordinate formulas,
and the proofs connect those formulas to the abstract group of curve points (`G1Group.lean`).
For valid `P` and `Q`, `add P Q` is again valid and denotes the sum of the two curve points
(`valid_add`, `toPoint_add`).
For a valid `P`, `mul P s` denotes `s * P` (`toPoint_mul`).
Every later statement about sums of points rests on these three theorems.

**The generator.**
The G1 generator has order `r`, the modulus of `Fr` (`addOrderOf_toPoint_generator`,
`G1Order.lean`).
So scalars can be taken modulo `r` without changing the point they produce.

**Multi-scalar multiplication.**
A KZG commitment is a sum `sum_i scalars_i * points_i`, computed by `msm` (`G1Msm.lean`).
Let `n` be the smaller of the two array lengths.
When the first `n` points are valid, `msm` returns a valid point equal to `sum_{i < n} scalars_i *
points_i` (`toPoint_msm`).
For arrays of equal length, that sum covers every pair.

**Compression of G1 points.**
A public key travels as 48 bytes, the compressed form of a point.
For a valid `P`, decompressing `compress P` succeeds and returns a point that denotes the same
group element (`uncompress_compress`, `Compress.lean`).
The theorem is about the group element, not the stored coordinates:
the representation it returns may differ from that of `P`.

## What is not proved

- Nothing is proved about G2, the pairing, hash-to-curve or SHA-256.
- The map to G1 of EIP-2537 has no theorem:
  neither its validity nor its landing in the subgroup is proved.
- No theorem says which signatures verification rejects, beyond malformed input.
- Unforgeability is proved only in the random oracle model, for a scheme over abstract groups.
  No theorem yet links that scheme to EthLib's own signing and verification.
  The proof rests on a co-Diffie-Hellman problem that no theorem proves hard.
- `PairingLaws`, the law of the pairing check, is not proved:
  on representatives of `a_i * g_1` and `b_i * g_2`,
  the check passes exactly when `sum_i a_i * b_i = 0`.
  Theorems about the result of a pairing check take it as a hypothesis,
  among them the theorem on the KZG ceremony checks.

## What the kernel cannot evaluate

This section is about a limit on computing results inside Lean,
separate from the missing theorems in the previous section.

`Fp2.powNat` and `Fp12.powNat` are `partial` definitions, which the kernel cannot unfold,
and `scripts/check_decls_baseline.txt` lists both as `partial`.
`millerLoop` is a subtler case.
It is declared `partial`, but it does not call itself, so Lean makes it an ordinary definition.
Its `while` loops, however, reach `Loop.forIn`, which Lean core defines with `partial`.
The baseline therefore lists it as `reaches-opaque`: it reaches an opaque constant when unfolded,
but is not opaque itself.

These three definitions sit on the verification path.
The pairing check runs `millerLoop`, then raises the result to a power with `Fp12.powNat`,
and hash-to-curve clears the cofactor with constants computed by `Fp2.powNat`.
So the kernel cannot compute the result of `ethFastAggregateVerify` once its input reaches
hash-to-curve and the pairing check.

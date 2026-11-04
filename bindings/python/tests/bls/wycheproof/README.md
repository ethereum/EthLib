# Wycheproof BLS test sets

The BLS signature and hash-to-G2 vectors of Wycheproof, copied byte for byte.

- Files: `testvectors_v1/bls_sig_g2_pop_verify_test.json`, `testvectors_v1/bls_hash_to_g2_test.json`
- Repository: [`C2SP/wycheproof`](https://github.com/C2SP/wycheproof)
- Commit: `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`
- Licence: Apache 2.0 (`LICENSE`)

`SHA256SUMS` pins the three files.

The verify set holds 26 cases for the proof-of-possession ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`, which Ethereum uses.
Its invalid cases include signatures under another ciphersuite, the identity point, a negated signature, points off the curve or outside the subgroup, bad flags and flipped bits.

The hash set holds 34 messages hashed to G2 under the test DST of RFC 9380, each with the compressed point.

The sets for the basic and the message-augmentation ciphersuites are not copied, because Ethereum signs under proof of possession only.

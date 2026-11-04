# Wycheproof HMAC-SHA-256 and HKDF-SHA-256 test sets

The HMAC-SHA-256 and HKDF-SHA-256 vectors of Wycheproof, copied byte for byte.

- Files: `testvectors_v1/hmac_sha256_test.json`, `testvectors_v1/hkdf_sha256_test.json`
- Repository: [`C2SP/wycheproof`](https://github.com/C2SP/wycheproof)
- Commit: `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`
- Licence: Apache 2.0 (`LICENSE`)

`SHA256SUMS` pins the three files.

The HMAC set holds 174 cases with keys of 16, 32 and 65 bytes, and tags of 16 or 32 bytes.
A 16-byte tag is the first half of the full tag.
Its invalid cases have a modified tag, which must differ from the tag that EthLib computes.

The HKDF set holds 86 cases, with empty salts and outputs up to the maximum of 8160 bytes.
Some cases have distinct inputs with the same output, because HMAC pads a short salt with zeros and hashes a long one.
Its invalid cases ask for 8161 bytes, which HKDF must reject.

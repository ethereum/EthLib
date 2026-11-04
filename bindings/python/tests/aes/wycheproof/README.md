# Wycheproof AES-GCM test set

`aes_gcm_test.json` is `testvectors_v1/aes_gcm_test.json` of [`C2SP/wycheproof`](https://github.com/C2SP/wycheproof) at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`, copied byte for byte.

The set holds 316 cases with AES-128, AES-192 and AES-256 keys.
Each case gives a key, an IV, the additional data, a message, its ciphertext and its 16-byte tag.
It also says whether a correct implementation accepts the case.
An invalid case has a modified tag, which decryption must reject, or an empty IV, which SP 800-38D forbids.
EthLib implements AES-128 and AES-256 only, so the test checks that the export rejects every AES-192 key.

The file is under the Apache License 2.0, in `LICENSE`.
`SHA256SUMS` pins both files.

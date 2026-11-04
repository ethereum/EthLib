# Test format: secp256r1 ECDSA verify

Verify an ECDSA signature on a 32-byte hash under a public key, by SEC 1 v2 §4.1.4.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  public_key: bytes -- x then y, 32 bytes each, big-endian
  msg_hash: bytes32 -- the hash the signature signs
  signature: bytes -- r then s, 32 bytes each, big-endian
output: bool or null -- true (VALID), false (INVALID), or null for a signature that is not 64 bytes
```

All byte fields are hexadecimal strings, prefixed with `0x`.

## Source

Each case is one test of `ecdsa_secp256r1_sha256_p1363_test.json` in `C2SP/wycheproof` at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`.

The case `verify_wycheproof_p1363_<tcId>` is the test `tcId`, and its expected output is Wycheproof's result.

`public_key` is the test's uncompressed key without its leading `0x04` byte.

`msg_hash` is the SHA-256 digest of the test's `msg`.

The cases keep Wycheproof's licence, the Apache License 2.0, in `LICENSE`.

# Test format: secp256k1 ECDSA verify with the low-s rule

Verify an ECDSA signature on a 32-byte hash under a public key, by SEC 1 v2 §4.1.4, and require `s <= n / 2`, the rule of EIP-2.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  public_key: bytes -- a SEC 1 encoded public key, 65 bytes uncompressed
  msg_hash: bytes32 -- the hash the signature signs
  signature: bytes64 -- r then s, 32 bytes each, big-endian
output: bool -- true when the signature is valid and its s is low
```

All byte fields are hexadecimal strings, prefixed with `0x`.

## Source

Each case is one test of `ecdsa_secp256k1_sha256_bitcoin_test.json` in `C2SP/wycheproof` at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`.

The case `verify_low_s_wycheproof_bitcoin_<tcId>` is the test `tcId`, and its expected output is Wycheproof's result.

That set encodes signatures in DER.
The 232 tests in strict DER appear here, converted to `r || s`.
The other 232 test DER parsing, not ECDSA: all are invalid, and none has a case here.

`msg_hash` is the SHA-256 digest of the test's `msg`.

The cases keep Wycheproof's licence, the Apache License 2.0, in `LICENSE`.

## Condition

The output is true exactly when ECDSA accepts the signature and `s <= n / 2`.

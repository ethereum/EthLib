# Test format: secp256k1 public key recovery

Recover the public key that signed a 32-byte hash, by SEC 1 v2 §4.1.6, for one recovery id.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  msg_hash: bytes32 -- the hash the signature signs
  signature: bytes64 -- r then s, 32 bytes each, big-endian
  recovery_id: int -- 0 or 1, the parity of the y of the signer's point R
output: bytes or null -- the 65-byte uncompressed public key, or null when that id recovers none
```

All byte fields are hexadecimal strings, prefixed with `0x`.

## Source

Each valid test of `ecdsa_secp256k1_sha256_p1363_test.json` in `C2SP/wycheproof` at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9` gives two cases, `recover_wycheproof_p1363_<tcId>_0` and `recover_wycheproof_p1363_<tcId>_1`.

`msg_hash` is the SHA-256 digest of the test's `msg`.

The expected keys come from EthLib.
The generator checks them against Wycheproof: one of the two ids returns the test's public key, and every key returned verifies the signature.

Tests 115 and 247 are the exception.
Their `R` has `x = r + n`, which only the ids 2 and 3 reach, and Ethereum uses only 0 and 1.
So neither id returns the test's key, and both outputs are other keys.

The cases keep Wycheproof's licence, the Apache License 2.0, in `LICENSE`.

## Condition

The recovered key, encoded uncompressed, must equal `output`.

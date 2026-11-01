# Test format: SHA-256 hash

Compute the SHA-256 digest of a given `message`.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  message: Message -- the message to hash
output: Digest -- the 32-byte digest
```

- `Message` is a byte string of any length, hexadecimal encoding, prefixed
  with `0x`.
- `Digest` is a 32-byte string, same encoding.

All byte(s) fields are encoded as strings, hexadecimal encoding, prefixed with
`0x`.

## Condition

The `hash` handler should compute the SHA-256 digest of `message` (FIPS 180-4).

The result should match the expected `output`.

The cases come from the NIST CAVP `SHA256ShortMsg.rsp` and `SHA256LongMsg.rsp` distributions.

Two more cases are the SHA-256 examples of FIPS 180-2, which NIST republishes on its example-values page.

SHA-256 accepts every byte string, so the suite has no invalid cases.

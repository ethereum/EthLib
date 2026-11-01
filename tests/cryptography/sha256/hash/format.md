# Test format: SHA-256 hash

Compute the SHA-256 digest of a message, as FIPS 180-4 §6.2 defines it.

## Test case format

The test data is declared in a `data.yaml` file:

```yaml
input:
  message: Message -- the message to hash
output: Digest -- the 32-byte digest
```

- `Message` is a byte string of any length, in hexadecimal, prefixed with `0x`.
- `Digest` is a 32-byte string, in the same encoding.

## Condition

The `hash` handler computes the digest of `message`.

The result must match `output`.

SHA-256 accepts every byte string, so the suite has no invalid cases.

## Sources

- 129 cases are the NIST CAVP files `SHA256ShortMsg.rsp` and `SHA256LongMsg.rsp`.
- 2 cases are the SHA-256 examples of FIPS 180-2, Appendix B.

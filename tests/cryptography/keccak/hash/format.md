# Test format: Keccak-256 hash

Compute the Keccak-256 digest of a message: Keccak[r = 1088, c = 512] of FIPS 202, with Keccak's original padding.

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

Keccak-256 accepts every byte string, so the suite has no invalid cases.

## Sources

256 cases are the byte-aligned cases of `ShortMsgKAT_256.txt` in the Keccak team's `KeccakKAT-3.zip`.
Two cases are the cases `Len = 2048` and `Len = 2552` of `LongMsgKAT_256.txt` in the same archive.
`bindings/python/tests/keccak/kat/README.md` gives the location and the digest of that archive.

The case `hash_case_abc` hashes the three ASCII bytes `abc`.
No file of the archive holds that message, so its digest does not come from the Keccak team.

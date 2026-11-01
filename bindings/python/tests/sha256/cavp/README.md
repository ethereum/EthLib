# Vendored NIST test vectors

`SHA256ShortMsg.rsp` and `SHA256LongMsg.rsp` are the byte-oriented
CAVS 11.0 files of the NIST CAVP secure-hashing distribution.

- Source: the secure-hashing test vectors of the Cryptographic Algorithm
  Validation Program, on `csrc.nist.gov`.
- Licence: NIST material is public domain.

`SHA256SUMS` pins the two files.
From this directory, verify them with:

```text
sha256sum -c SHA256SUMS
```

To re-fetch the originals, download the CAVP SHA-256 test-vector bundle
from the NIST CAVP page and compare the two `.rsp` files byte for byte.

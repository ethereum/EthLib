# Vendored NIST test vectors

The two `.rsp` files are the byte-oriented SHA-256 files of the NIST CAVP secure-hashing test vectors, CAVS 11.0.

- Source: [`shabytetestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip).
- Licence: NIST material is public domain.

The files are copied byte for byte.

`SHA256SUMS` pins them.

Check the pin from this directory:

```text
sha256sum -c SHA256SUMS
```

To check the copy against NIST, download the archive above and compare the two files byte for byte.

# Vendored NIST test vectors

The two `.rsp` files are the byte-oriented SHA-256 files of the NIST CAVP secure-hashing test vectors, CAVS 11.0.
CAVP is NIST's Cryptographic Algorithm Validation Program, and these files give, for each message, the digest a correct SHA-256 must return.

- Source: [`shabytetestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip).
- Licence: NIST material is public domain.

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The pin only shows that the files have not changed since they were copied.
To check the copy against NIST itself, download the archive above and compare the two files byte for byte.

# Vendored NIST test vectors

The byte-oriented SHA-256 files of the NIST CAVP secure-hashing test vectors, CAVS 11.0, copied byte for byte.

- Files: `SHA256ShortMsg.rsp`, `SHA256LongMsg.rsp`, `SHA256Monte.rsp`
- Archive: [`shabytetestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip)
- Licence: public domain (NIST material)

`SHA256SUMS` pins the files.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

CAVP is NIST's Cryptographic Algorithm Validation Program.
The short-message and long-message files give, for each message, the digest a correct SHA-256 must return.
The Monte Carlo file gives a seed and 100 checkpoints of the chain of hashes that Section 6.4 of the SHA Validation System (SHAVS) describes.

The pin only shows that the files have not changed since they were copied.
To check the copy against NIST itself, download the archive above and compare the files byte for byte.

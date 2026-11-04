# NIST CAVP AES known answers

The eight `.rsp` files are the ECB files of the NIST CAVP AES known-answer tests, for 128-bit and 256-bit keys.
CAVP is NIST's Cryptographic Algorithm Validation Program.
Section 6.2 of "The Advanced Encryption Standard Algorithm Validation Suite (AESAVS)" describes the four tests.
GFSbox and KeySbox fix one input and vary the other over chosen values.
VarKey and VarTxt set the leading bits of the key or of the plaintext, one more in each case.
Each file has an encrypt section and a decrypt section.

- Source: [`KAT_AES.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/aes/KAT_AES.zip), which had sha256 `a203b16c9246b2ebae31dee5de21a606be80cf78ceabaca37150236fa098eb60` when it was copied.
- Licence: NIST material is public domain.

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The archive also holds the AES-192 files and the CBC, CFB and OFB files.
EthLib implements none of these, so they are not copied.

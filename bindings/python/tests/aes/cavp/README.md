# NIST CAVP AES and GCM test vectors

Test vectors of NIST CAVP for AES and AES-GCM, with 128-bit and 256-bit keys, copied byte for byte.

- Files: `ECBGFSbox`, `ECBKeySbox`, `ECBVarKey` and `ECBVarTxt`, each for 128 and 256 bits
- Archive: [`KAT_AES.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/aes/KAT_AES.zip)
- Archive sha256 at the copy: `a203b16c9246b2ebae31dee5de21a606be80cf78ceabaca37150236fa098eb60`

- Files: `ECBMCT128.rsp`, `ECBMCT256.rsp`
- Archive: [`aesmct.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/aes/aesmct.zip)
- Archive sha256 at the copy: `6a2a72c00b1daacb9a7d20ab92617d322fa1c5dee493968660990e3f4571426b`

- Files: excerpts of `gcmEncryptExtIV128.rsp`, `gcmEncryptExtIV256.rsp`, `gcmDecrypt128.rsp`, `gcmDecrypt256.rsp`
- Archive: [`gcmtestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/gcmtestvectors.zip)
- Archive sha256 at the copy: `f9fc479e134cde2980b3bb7cddbcb567b2cd96fd753835243ed067699f26a023`

- Licence: public domain (NIST material)

`SHA256SUMS` pins the files.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

CAVP is NIST's Cryptographic Algorithm Validation Program.
Section 6.2 of "The Advanced Encryption Standard Algorithm Validation Suite (AESAVS)" describes the four known-answer tests.
GFSbox and KeySbox fix one input and vary the other over chosen values.
VarKey and VarTxt set the leading bits of the key or of the plaintext, one more in each case.
Section 6.4.1 describes the ECB Monte Carlo test: 100 checkpoints, each 1000 operations from the last.
Each of these files has an encrypt section and a decrypt section.

The GCM files hold 7875 cases each, in sections by the lengths of the IV, the text, the additional data and the tag.
A case of a decryption file either gives the plaintext or says FAIL, when the tag does not authenticate the input.

The whole GCM files take 11.8 MB, so this directory keeps an excerpt of each, `<name>.excerpt.rsp`.
An excerpt is the header of the file and 21 of its 525 sections, copied without change.
The sections have a 104-bit text, 160-bit additional data, each of the three IV lengths and each of the seven tag lengths.
`tests/sources.toml` pins the archive, and the weekly job reads it.
There, `test_cavp_gcm.py` runs every case of the four files, and checks that each excerpt is the same sections of its file.

The archives also hold the AES-192 files and the CBC, CFB and OFB files.
EthLib implements none of these, so they are not copied.

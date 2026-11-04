# Vendored Keccak team test vectors

The Keccak team's known answers for Keccak-256 and Keccak-512.
Keccak-256 is Keccak[r = 1088, c = 512] with 256 bits of output.
Keccak-512 is Keccak[r = 576, c = 1024] with 512 bits of output.

- Archive: [`KeccakKAT-3.zip`](https://keccak.team/obsolete/KeccakKAT-3.zip)
- Archive sha256: `af92d22d23527a0d168a6bbe70b28c840a43bba5bcea828a6d9a5e7ad79378ce`
- Files copied byte for byte: `KeccakKAT/ShortMsgKAT_256.txt`, `KeccakKAT/ShortMsgKAT_512.txt`, `KeccakKAT/MonteCarlo_256.txt`, `KeccakKAT/MonteCarlo_512.txt`, `KeccakKAT/KeccakPermutationIntermediateValues.txt`
- File excerpted: `KeccakKAT/LongMsgKAT_256.txt`, sha256 `9283c15fcf69f3d46d05309d098277d29bf0aeb072ee0466d81d9f6e432abe72`, as `LongMsgKAT_256_bytes.txt`
- File excerpted: `KeccakKAT/LongMsgKAT_512.txt`, sha256 `2182204b1aa75fd84629ab219707d46db32b878ec8b810100156ea7f9e3cb779`, as `LongMsgKAT_512_bytes.txt`
- Authors: the Keccak team, Guido Bertoni, Joan Daemen, Michaël Peeters and Gilles Van Assche
- Licence: the archive states none

`SHA256SUMS` pins the files.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The team submitted these files to the third round of the NIST SHA-3 competition, before FIPS 202 changed the padding of SHA3.

The `ShortMsgKAT` and `LongMsgKAT` files list messages by their length in bits.
The binding takes bytes, so the tests keep the lengths that are whole bytes.
Each `LongMsgKAT` file is over 2 MB, and only one case in eight is whole bytes.
So each `_bytes.txt` excerpt keeps the three header lines and those 65 cases, line for line.
This command makes the Keccak-256 excerpt again from the file in the archive, and the same command with 512 makes the other:

```text
awk 'NR <= 4 { print; next } /^Len = / { keep = ($3 % 8 == 0) } keep { print }' \
  LongMsgKAT_256.txt > LongMsgKAT_256_bytes.txt
```

Each `MonteCarlo` file gives a 128-byte seed and 100 checkpoints of a chain of hashes.

`KeccakPermutationIntermediateValues.txt` applies Keccak-f[1600] twice, first to the all-zero state and then to the first output.
The tests read the input and the output of each permutation, and skip the values after each step.

The archive also holds `ExtremelyLongMsgKAT_256.txt` and `ExtremelyLongMsgKAT_512.txt`, whose one case each hashes 1 GiB.
Each case is three short lines, so the test writes them out instead of copying the files.

# Vendored Keccak team test vectors

`ShortMsgKAT_256.txt` holds the Keccak team's known answers for Keccak[r = 1088, c = 512] with 256 bits of output, which is Keccak-256.
`ShortMsgKAT_512.txt` holds the known answers for Keccak[r = 576, c = 1024] with 512 bits of output, which is Keccak-512.
The team submitted both to the third round of the NIST SHA-3 competition, before FIPS 202 changed the padding of SHA3.
`KeccakPermutationIntermediateValues.txt` applies Keccak-f[1600] twice, first to the all-zero state and then to the first output.

- Source: `KeccakKAT/ShortMsgKAT_256.txt`, `KeccakKAT/ShortMsgKAT_512.txt` and `KeccakKAT/KeccakPermutationIntermediateValues.txt` in [`KeccakKAT-3.zip`](https://keccak.team/obsolete/KeccakKAT-3.zip), which has sha256 `af92d22d23527a0d168a6bbe70b28c840a43bba5bcea828a6d9a5e7ad79378ce`.
- Authors: the Keccak team, Guido Bertoni, Joan Daemen, Michaël Peeters and Gilles Van Assche.
- Licence: the archive states none.

The files are copied byte for byte, and `SHA256SUMS` pins them.
To check the pins, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The two `ShortMsgKAT` files list messages by their length in bits, and the tests keep the 256 lengths that are whole bytes.
The tests read the input and the output of each permutation in `KeccakPermutationIntermediateValues.txt`, and skip the values after each step.

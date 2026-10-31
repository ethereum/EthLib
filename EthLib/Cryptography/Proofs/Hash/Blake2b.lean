import EthLib.Cryptography.Hash.Blake2b

/-!
# Proofs: `Hash.Blake2b`

The constants and the function F of BLAKE2b, checked against RFC 7693 and the test vectors of BLAKE2.

- `IV` is what §2.6 derives from the square roots of the first eight primes.
- Each row of `SIGMA` is a permutation of the 16 word indices.
- F agrees with the example of Appendix A, and with the BLAKE2b answer for one full block.

`decide +kernel` has the kernel itself evaluate each claim, so no compiled code is trusted.
-/

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## The constants -/

/-- `IV[i]` is `floor(2^64 * frac(sqrt(p)))` for the `(i + 1)`-th prime `p`, RFC 7693 §2.6.

§2.6 lists the primes: 2, 3, 5, 7, 11, 13, 17 and 19.

Let `n = floor(sqrt(p))` and `s = 2^64 * n + IV[i]`.

Then `IV[i]` is right exactly when `s = floor(2^64 * sqrt(p))`, that is when `s^2 <= 2^128 * p < (s + 1)^2`.

`IV[i]` is below `2^64`, so the bounds hold for no `n` other than `floor(sqrt(p))`. -/
theorem IV_sqrt (i : Fin 8) :
    let p := #v[2, 3, 5, 7, 11, 13, 17, 19][i]
    let s := 2 ^ 64 * #v[1, 1, 2, 2, 3, 3, 4, 4][i] + IV[i].toNat
    s ^ 2 ≤ 2 ^ 128 * p ∧ 2 ^ 128 * p < (s + 1) ^ 2 := by
  revert i
  decide +kernel

/-- Each row of `SIGMA` is a permutation of the word indices 0 to 15, as RFC 7693 §2.7 calls them.

So each round of F reads every message word exactly once. -/
theorem SIGMA_perm (i : Fin 10) : SIGMA[i].toList.Perm (List.finRange 16) := by
  revert i
  decide +kernel

/-! ## RFC 7693 Appendix A

The appendix computes BLAKE2b-512 of the three bytes "abc".

The message fits in one block, so the hash is one call of F with 12 rounds (§3.3):

- `h` is the IV, with the parameter block `0x01010040` XORed into `h[0]`, for a 64-byte digest and no key (§2.5).
- `m` is the block, "abc" followed by zeros, as 16 little-endian words.
- `t` is 3, the number of message bytes.
- `f` is true, because it is the last block.

The appendix prints `m` and the new `h` as words, which are copied below as it prints them. -/

/-- F on the block of Appendix A gives the state that Appendix A prints. -/
theorem compress_abc :
    compress 12 (IV.set 0 (IV[0] ^^^ 0x01010040))
      #v[0x0000000000636261, 0x0000000000000000, 0x0000000000000000,
        0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        0x0000000000000000]
      3 0 true =
    #v[0x0D4D1C983FA580BA, 0xE9F6129FB697276A, 0xB7C45A68142F214C,
      0xD1A2FFDB6FBB124B, 0x2D79AB2A39C5877D, 0x95CC3345DED552C2,
      0x5A92F1DBA88AD318, 0x239900D4ED8623B9] := by
  decide +kernel

/-! ## One full block

Appendix A leaves 15 of the 16 words of `m` at zero, so it cannot tell those words apart.

Nor, then, can it tell the right order of a row of `SIGMA` from a wrong order that only swaps two of those words.

The official BLAKE2 implementations, github.com/BLAKE2/BLAKE2 at `ed1974e`, give known answers in `testvectors/blake2-kat.json`.

Its unkeyed BLAKE2b answer for the 128 bytes `0x00` to `0x7f` is again one call of F with 12 rounds:

- `h` is the IV with the parameter block of Appendix A.
- `m` is the block, as 16 little-endian words, all of them different.
- `t` is 128, the number of message bytes.
- `f` is true, because it is the last block.

The file prints the message and the digest as bytes, which are read below as little-endian words (§2.4). -/

/-- F on one full block gives the digest of the BLAKE2 test vectors. -/
theorem compress_fullBlock :
    compress 12 (IV.set 0 (IV[0] ^^^ 0x01010040))
      #v[0x0706050403020100, 0x0F0E0D0C0B0A0908, 0x1716151413121110, 0x1F1E1D1C1B1A1918,
        0x2726252423222120, 0x2F2E2D2C2B2A2928, 0x3736353433323130, 0x3F3E3D3C3B3A3938,
        0x4746454443424140, 0x4F4E4D4C4B4A4948, 0x5756555453525150, 0x5F5E5D5C5B5A5958,
        0x6766656463626160, 0x6F6E6D6C6B6A6968, 0x7776757473727170, 0x7F7E7D7C7B7A7978]
      128 0 true =
    #v[0xDAE2479C78E31923, 0xA1C2BE617F80FEA5, 0x32FF193FA07F53A6, 0x0E7E4BD6BFEC7EE8,
      0x043B33AC39F4CF8C, 0x611AD1DDC4B0190F, 0x39A0100FFEC14AE2, 0x15D1A30DCC5D6C80] := by
  decide +kernel

end EthLib.Cryptography.Hash.Blake2b

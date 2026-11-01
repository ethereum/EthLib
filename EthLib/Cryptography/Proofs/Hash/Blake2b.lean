module

public import EthLib.Cryptography.Hash.Blake2b

/-!
# Proofs: `Hash.Blake2b`

The constants, the rounds and two known answers of F, against [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693).

- The IV is what §2.6 derives from the square roots of the first eight primes.
- Each row of the message schedule is a permutation of the 16 word indices.
- Round `i` uses row `i mod 10`, and a run of rounds splits into two runs.
- F gives the state of Appendix A, and the BLAKE2b-512 digest of one full block.

`decide +kernel` has the kernel evaluate each known answer, so no compiled code is trusted.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## The constants -/

/-- Word `i` of the IV is `floor(2^64 * frac(sqrt(p)))`, for `p` the `(i + 1)`-th prime, RFC 7693 §2.6.

- The primes are 2, 3, 5, 7, 11, 13, 17 and 19.
- Let `n = floor(sqrt(p))` and `s = 2^64 * n + IV[i]`.
- The word is right exactly when `s = floor(2^64 * sqrt(p))`.
- That is `s^2 <= 2^128 * p < (s + 1)^2`. -/
theorem IV_sqrt (i : Fin 8) :
    let p := #v[2, 3, 5, 7, 11, 13, 17, 19][i]
    let s := 2 ^ 64 * #v[1, 1, 2, 2, 3, 3, 4, 4][i] + IV[i].toNat
    s ^ 2 ≤ 2 ^ 128 * p ∧ 2 ^ 128 * p < (s + 1) ^ 2 := by
  revert i
  decide +kernel

/-- Each row of the message schedule is a permutation of the indices 0 to 15, RFC 7693 §2.7.

So each round reads every message word exactly once. -/
theorem SIGMA_perm (i : Fin 10) : SIGMA[i].toList.Perm (List.finRange 16) := by
  revert i
  decide +kernel

/-! ## The rounds -/

/-- Round `i + 10` is round `i`, RFC 7693 §2.7.

The schedule has 10 rows, so rounds 10 and 11 of BLAKE2b reuse rows 0 and 1. -/
theorem round_add_ten (m v : Vector UInt64 16) (i : Nat) : round m (i + 10) v = round m i v := by
  simp only [round, Nat.add_mod_right]

/-- Running `a + b` rounds is running `a` rounds, then the `b` rounds after them. -/
theorem roundsFrom_add (m v : Vector UInt64 16) (start a b : Nat) :
    roundsFrom m start (a + b) v = roundsFrom m (start + a) b (roundsFrom m start a v) := by
  induction a generalizing start v with
  | zero => simp [roundsFrom]
  | succ a ih =>
    -- Peel the first round off both sides, then apply the induction hypothesis.
    rw [Nat.add_right_comm, roundsFrom, ih, roundsFrom]
    congr 1
    omega

/-! ## RFC 7693 Appendix A

The appendix computes BLAKE2b-512 of "abc", one call of F with 12 rounds (§3.3).

- `h` is the IV, with the parameter block `0x01010040` in its first word: a 64-byte digest, no key (§2.5).
- `m` is "abc" followed by zeros, as 16 little-endian words.
- `t` is 3, the number of message bytes.
- `f` is true, for the last block.

The words below are copied as the appendix prints them. -/

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

Appendix A leaves 15 of the 16 message words at zero.

So it cannot catch a schedule row that swaps two of them.

This answer has 16 different words: the unkeyed BLAKE2b-512 digest of the 128 bytes `0x00` to `0x7f`.

- Source: `testvectors/blake2-kat.json` of [BLAKE2/BLAKE2 at `ed1974e`](https://github.com/BLAKE2/BLAKE2/blob/ed1974ea83433eba7b2d95c5dcd9ac33cb847913/testvectors/blake2-kat.json).
- `h` is the IV with the parameter block of Appendix A.
- `t` is 128, the number of message bytes.
- `f` is true, for the last block.

The message and the digest are read as little-endian words (§2.4). -/

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

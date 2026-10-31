/-!
# `Hash.Blake2b`

The compression function F of BLAKE2b, as specified by RFC 7693.

BLAKE2b hashes a message by running F on each 128-byte block (§3.3).

F takes the state `h`, a block `m`, the offset counter `t` and the final block flag `f` (§3.2).

§2.2 defines `t` as the "message byte offset at the end of the current block", and `f` as the flag of the last block.

F computes on a local work vector `v` of 16 words: `h` and the IV, into which it mixes `t`, `f` and `m`.

It returns the new state.

BLAKE2b runs F with 12 rounds.

The precompile at address `0x09` lets the caller choose the number of rounds (EIP-152), so here it is an argument.

Each step of §2 and §3 that F uses is one definition:

```text
IV         §2.6   the initialization vector
SIGMA      §2.7   the message word schedule of each round
rotr       §2.3   rotation of a word to the right
mix        §3.1   the mixing function G
round      §3.2   one round of F: eight calls of G on the work vector
compress   §3.2   the compression function F, with a number of rounds
```

It is written as a direct transcription of the RFC, to be read against it.

It is not intended to be constant-time.
-/

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## Parameters

RFC 7693 §2.1 gives the parameters of BLAKE2b that F uses:

```text
bits in word     w = 64
rounds in F      r = 12
G rotations      (R1, R2, R3, R4) = (32, 24, 16, 63)
```

A word is a `UInt64`, so `+` is the addition `mod 2**w` that G writes out in §3.1.

The RFC's `^` is exclusive-or (§2.3), which Lean writes `^^^`. -/

/-- The initialization vector `IV[0..7]`, RFC 7693 §2.6.

`IV[i]` is `floor(2**w * frac(sqrt(prime(i+1))))`.

That is the first 64 bits of the fractional part of the square root of the `(i + 1)`-th prime.

The values are those of Appendix C, as §2.6 says, and they are also the IV of SHA-512.

The kernel checks the square roots in `Proofs/Hash/Blake2b.lean`. -/
def IV : Vector UInt64 8 := #v[
  0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
  0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- The message word schedule `SIGMA[0..9]`, RFC 7693 §2.7.

Round `i` of F reads the 16 message words in the order of row `i mod 10`.

So the rounds 10 and 11 of BLAKE2b reuse the rows 0 and 1, as §2.7 says.

Each row is a permutation of the word indices 0 to 15, which the kernel checks in `Proofs/Hash/Blake2b.lean`. -/
def SIGMA : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-! ## The mixing function G -/

/-- Rotation of a word to the right by `n` bits, `0 < n < 64`.

It is the RFC's `x >>> n`, defined in §2.3 as `(x >> n) ^ (x << (w - n))`.

In Lean `>>>` is the shift that the RFC writes `>>`, so the rotation is spelled out as the RFC defines it. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ^^^ (x <<< (64 - n))

/-- The mixing function G, RFC 7693 §3.1.

It mixes the two words `x` and `y` into the words at indices `a`, `b`, `c` and `d` of the work vector `v`.

The rotations are those of BLAKE2b, `(R1, R2, R3, R4) = (32, 24, 16, 63)`. -/
def mix (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) : Vector UInt64 16 :=
  let v := v.set a (v[a] + v[b] + x)
  let v := v.set d (rotr (v[d] ^^^ v[a]) 32)
  let v := v.set c (v[c] + v[d])
  let v := v.set b (rotr (v[b] ^^^ v[c]) 24)
  let v := v.set a (v[a] + v[b] + y)
  let v := v.set d (rotr (v[d] ^^^ v[a]) 16)
  let v := v.set c (v[c] + v[d])
  v.set b (rotr (v[b] ^^^ v[c]) 63)

/-! ## The compression function F -/

/-- Round `i` of F, RFC 7693 §3.2.

Read the 16 words of the work vector as a 4 x 4 matrix, row by row.

A column is then four words such as `v[0], v[4], v[8], v[12]`.

A diagonal is four words such as `v[0], v[5], v[10], v[15]`.

The round applies G to the four columns, then to the four diagonals.

The message words enter in the order of the schedule `s = SIGMA[i mod 10]`. -/
def round (m : Vector UInt64 16) (i : Nat) (v : Vector UInt64 16) : Vector UInt64 16 :=
  let s := SIGMA[i % 10]
  -- The four columns.
  let v := mix v 0 4  8 12 m[s[0]]  m[s[1]]
  let v := mix v 1 5  9 13 m[s[2]]  m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]]  m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]]  m[s[7]]
  -- The four diagonals.
  let v := mix v 0 5 10 15 m[s[8]]  m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7  8 13 m[s[12]] m[s[13]]
  mix v 3 4  9 14 m[s[14]] m[s[15]]

/-- The compression function F, RFC 7693 §3.2, with `rounds` rounds.

- `h` is the state vector.
- `m` is the message block, 16 words.
- `t0` and `t1` are the low and high words of the offset counter `t`, which has `2w = 128` bits.
- `f` is the final block indicator flag.

The result is the new state vector:

```text
v[0..7] := h[0..7]                        v[8..15] := IV[0..7]
v[12] := v[12] ^ (t mod 2**w)             v[13] := v[13] ^ (t >> w)
v[14] := v[14] ^ 0xFF..FF                 if f
v := round i v                            for i = 0 to rounds - 1
h[i] := h[i] ^ v[i] ^ v[i + 8]            for i = 0 to 7
```

With `rounds = 12` it is the F of BLAKE2b. -/
def compress (rounds : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16) (t0 t1 : UInt64)
    (f : Bool) : Vector UInt64 8 :=
  -- The first half of the work vector is the state, the second half the IV.
  let v : Vector UInt64 16 := h ++ IV
  -- The low word of the offset, then the high word.
  let v := v.set 12 (v[12] ^^^ t0)
  let v := v.set 13 (v[13] ^^^ t1)
  -- The last block inverts all bits of `v[14]`.
  let v := if f then v.set 14 (v[14] ^^^ 0xFFFFFFFFFFFFFFFF) else v
  -- The rounds `0` to `rounds - 1`, in order.
  let v := Nat.fold rounds (fun i _ v => round m i v) v
  -- XOR the two halves of the work vector into the state.
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

end EthLib.Cryptography.Hash.Blake2b

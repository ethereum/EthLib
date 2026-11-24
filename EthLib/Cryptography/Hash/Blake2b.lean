module

/-!
# The BLAKE2b compression function

The compression function F of BLAKE2b, [RFC 7693][rfc7693] §3.2.

BLAKE2b runs F once per 128-byte block, with 12 rounds (§3.3).

The BLAKE2F precompile lets the caller choose the number of rounds, so here it is an argument.

Each definition names its section of the RFC, and comments in the bodies quote the RFC's steps.

The code is a direct transcription of the RFC, not a constant-time implementation.

[rfc7693]: https://www.rfc-editor.org/rfc/rfc7693
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Blake2b

/-! ## Parameters

RFC 7693 §2.1 fixes the parameters of BLAKE2b: a word has `w = 64` bits, and F runs `r = 12` rounds.

G rotates by `(R1, R2, R3, R4) = (32, 24, 16, 63)`. -/

/-- The initialization vector, RFC 7693 §2.6.

Word `i` is `floor(2^64 * frac(sqrt(p)))`, where `p` is the `(i + 1)`-th prime.

These are also the initial hash values of SHA-512.

The kernel checks every word against its square root in the proofs. -/
def IV : Vector UInt64 8 := #v[
  0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
  0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- The message schedule, RFC 7693 §2.7.

Round `i` reads the 16 message words in the order of row `i mod 10`.

So rounds 10 and 11 of BLAKE2b reuse rows 0 and 1.

The kernel checks that each row is a permutation in the proofs. -/
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

/-- Rotation of a word right by `n` bits, for `0 < n < 64`, RFC 7693 §2.3.

The RFC defines it as `(x >> n) ^ (x << (w - n))`.

Lean's `>>>` is the RFC's shift `>>`, so the rotation is spelled out. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 :=
  -- The RFC's `^` is exclusive-or (§2.3), which Lean writes `^^^`.
  --
  -- RFC: `x >>> n = (x >> n) ^ (x << (w - n))`, with `w = 64`.
  (x >>> n) ^^^ (x <<< (64 - n))

/-- The mixing function G, RFC 7693 §3.1.

It mixes the message words `x` and `y` into the words `a`, `b`, `c` and `d` of the work vector.
-/
def mix (v : Vector UInt64 16) (a b c d : Fin 16) (x y : UInt64) : Vector UInt64 16 :=
  -- A word is a `UInt64`, so `+` is the addition modulo `2^64` of §3.1.
  --
  -- `v[a] := (v[a] + v[b] + x) mod 2**w`.
  let v := v.set a (v[a] + v[b] + x)
  -- `v[d] := (v[d] ^ v[a]) >>> R1`, with `R1 = 32`.
  let v := v.set d (rotr (v[d] ^^^ v[a]) 32)
  -- `v[c] := (v[c] + v[d]) mod 2**w`.
  let v := v.set c (v[c] + v[d])
  -- `v[b] := (v[b] ^ v[c]) >>> R2`, with `R2 = 24`.
  let v := v.set b (rotr (v[b] ^^^ v[c]) 24)
  -- `v[a] := (v[a] + v[b] + y) mod 2**w`.
  let v := v.set a (v[a] + v[b] + y)
  -- `v[d] := (v[d] ^ v[a]) >>> R3`, with `R3 = 16`.
  let v := v.set d (rotr (v[d] ^^^ v[a]) 16)
  -- `v[c] := (v[c] + v[d]) mod 2**w`.
  let v := v.set c (v[c] + v[d])
  -- `v[b] := (v[b] ^ v[c]) >>> R4`, with `R4 = 63`.
  v.set b (rotr (v[b] ^^^ v[c]) 63)

/-! ## The compression function F -/

/-- Round `i` of F, RFC 7693 §3.2.

Read the work vector as a 4 x 4 matrix, row by row.

The round mixes its columns, then its diagonals. -/
def round (m : Vector UInt64 16) (i : Nat) (v : Vector UInt64 16) : Vector UInt64 16 :=
  -- `s[0..15] := SIGMA[i mod 10][0..15]`.
  let s := SIGMA[i % 10]
  -- The four columns.
  --
  -- `v := G( v, 0, 4,  8, 12, m[s[ 0]], m[s[ 1]] )`.
  let v := mix v 0 4  8 12 m[s[0]]  m[s[1]]
  -- `v := G( v, 1, 5,  9, 13, m[s[ 2]], m[s[ 3]] )`.
  let v := mix v 1 5  9 13 m[s[2]]  m[s[3]]
  -- `v := G( v, 2, 6, 10, 14, m[s[ 4]], m[s[ 5]] )`.
  let v := mix v 2 6 10 14 m[s[4]]  m[s[5]]
  -- `v := G( v, 3, 7, 11, 15, m[s[ 6]], m[s[ 7]] )`.
  let v := mix v 3 7 11 15 m[s[6]]  m[s[7]]
  -- The four diagonals.
  --
  -- `v := G( v, 0, 5, 10, 15, m[s[ 8]], m[s[ 9]] )`.
  let v := mix v 0 5 10 15 m[s[8]]  m[s[9]]
  -- `v := G( v, 1, 6, 11, 12, m[s[10]], m[s[11]] )`.
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  -- `v := G( v, 2, 7,  8, 13, m[s[12]], m[s[13]] )`.
  let v := mix v 2 7  8 13 m[s[12]] m[s[13]]
  -- `v := G( v, 3, 4,  9, 14, m[s[14]], m[s[15]] )`.
  mix v 3 4  9 14 m[s[14]] m[s[15]]

/-- The rounds `start` to `start + count - 1` of F, in order.

It recurses on the count, so the kernel can unfold it.

It is a tail call, so it compiles to a loop, even for `2^32 - 1` rounds. -/
def roundsFrom (m : Vector UInt64 16) (start : Nat) : Nat → Vector UInt64 16 → Vector UInt64 16
  | 0, v => v
  | count + 1, v => roundsFrom m (start + 1) count (round m start v)

/-- The compression function F, RFC 7693 §3.2, with `rounds` rounds: it returns the new state.

With 12 rounds it is the F of BLAKE2b. -/
def compress (rounds : Nat) (h : Vector UInt64 8) (m : Vector UInt64 16) (t0 t1 : UInt64)
    (f : Bool) : Vector UInt64 8 :=
  -- The state `h` is 8 words, and the message block `m` is 16 words.
  --
  -- `v[0..7] := h[0..7]` and `v[8..15] := IV[0..7]`.
  let v : Vector UInt64 16 := h ++ IV
  -- `t0` and `t1` are the low and high words of the 128-bit offset counter `t`.
  --
  -- `v[12] := v[12] ^ (t mod 2**w)`, the low word of the offset, given as `t0`.
  let v := v.set 12 (v[12] ^^^ t0)
  -- `v[13] := v[13] ^ (t >> w)`, the high word, given as `t1`.
  let v := v.set 13 (v[13] ^^^ t1)
  -- `f` is the final block flag.
  --
  -- `IF f = TRUE THEN v[14] := v[14] ^ 0xFF..FF`.
  let v := if f then v.set 14 (v[14] ^^^ 0xFFFFFFFFFFFFFFFF) else v
  -- `FOR i = 0 TO r - 1 DO`, with `r` the given number of rounds.
  let v := roundsFrom m 0 rounds v
  -- `FOR i = 0 TO 7 DO h[i] := h[i] ^ v[i] ^ v[i + 8]`.
  Vector.ofFn fun i => h[i] ^^^ v[i] ^^^ v[i.val + 8]

end EthLib.Cryptography.Hash.Blake2b

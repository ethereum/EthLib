module

public import EthLib.Base.Bytes

/-!
# `Hash.Keccak`

The Keccak-f[1600] permutation and the Keccak-256 and Keccak-512 hashes, as in FIPS 202.

FIPS 202 §3.4 defines Keccak-f[1600] as Keccak-p[1600, 24]: 24 rounds over a 1600-bit state.

Both hashes are the sponge over that permutation with Keccak's original padding.

Keccak-256 has capacity 512 bits, and Keccak-512 has capacity 1024 bits.

Keccak-256 is Ethereum's hash, the function `KEC` of the Yellow Paper.

Keccak-512 is the function `KEC512` of Ethash, in Appendix J of the Yellow Paper.

Each definition follows a section of the standard, to be read against it.

The state is a record of 25 lanes, and each step mapping is written out lane by lane.

So the compiled code keeps the lanes in machine words, and allocates at most one state per round.

It is not intended to be constant-time.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

/-! ## The state

FIPS 202 §3.1.2 views the 1600-bit state as a 5 x 5 array of lanes, each of `w = 64` bits.

Lane `(x, y)` has the index `x + 5 * y`, so the 25 lanes run row by row.

Bit `z` of a lane is bit `z` of its 64-bit word.

That is the standard's own order: bit `64 * (x + 5y) + z` of the state string is `A[x, y, z]`.

So byte `k` of the state string is byte `k mod 8` of lane `k / 8`, least significant first.

FIPS 202 §3.1.3 and Appendix B.1 give that byte order.

The state is a record with one field per lane, so each step mapping below names its lanes.
-/

/-- Lanes in the state: 1600 bits of 64-bit lanes. -/
def LANES : Nat := 25

/-- Rounds in Keccak-f[1600].

FIPS 202 §3.4 sets `n_r = 12 + 2l`, with `l = 6` because `w = 2^6`. -/
def ROUNDS : Nat := 24

/-- The Keccak-f[1600] state: 25 lanes of 64 bits.

The field with the number `x + 5y` holds lane `(x, y)`. -/
structure State where
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 :
    UInt64)
  deriving DecidableEq

/-- The all-zero state, where every sponge starts (FIPS 202 §4, Algorithm 8, step 5). -/
def State.zero : State :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Rotate a lane towards its high bits by `n` positions, `n < 64`.

Bit `z` moves to bit `(z + n) mod 64`, which is what `rho` and `theta` ask of the bit index. -/
@[inline] def rotl (v : UInt64) (n : UInt64) : UInt64 :=
  -- The two shifts are disjoint and together move every bit once.
  -- At `n = 0` the right shift is by 64, which wraps to 0, and the result is still `v`.
  (v <<< n) ||| (v >>> (64 - n))

/-! ## The constants

FIPS 202 defines the round constants and the rotation offsets by two algorithms, transcribed here.

Its Table 2 lists the offsets before their reduction mod 64, and it lists no round constants.

The tables used by the permutation are proved equal to them in `Proofs/Hash/Keccak.lean`. -/

namespace Internal

/-- One step of the linear feedback shift register of FIPS 202 §3.2.5, Algorithm 5.

The register `R` is eight bits, `R[0]` in bit 0 of the number.

```text
    R := 0 || R                      prepend a zero: every bit moves one place up
    R[0], R[4], R[5], R[6] ^= R[8]   feed back the bit that moved out
    R := Trunc_8(R)                  drop bit 8
```
-/
def lfsrStep (r : Nat) : Nat :=
  -- Prepending a zero bit at index 0 shifts every bit one index up.
  let r := r <<< 1
  -- The bit pushed to index 8 is fed back into indices 0, 4, 5 and 6.
  -- 0x71 is 0111 0001 in binary: bits 0, 4, 5 and 6.
  let feedback := if (r >>> 8) % 2 = 1 then 0x71 else 0
  -- Truncation keeps indices 0 to 7.
  (r ^^^ feedback) % 256

/-- The bit `rc(t)` of FIPS 202 §3.2.5, Algorithm 5.

The register starts at `10000000`, that is `R[0] = 1`, and runs `t mod 255` steps.

The output is the bit `R[0]`. -/
def rc (t : Nat) : Bool :=
  -- The register has period 255, so only `t mod 255` steps matter.
  -- Algorithm 5 returns 1 at once when that count is zero, which zero steps also gives.
  (Nat.repeat lfsrStep (t % 255) 1) % 2 = 1

/-- The round constant of round `i_r`, by FIPS 202 §3.2.5, Algorithm 6.

For `j` from 0 to `l = 6`, bit `2^j - 1` of the lane is `rc(j + 7 * i_r)`.

All other bits are zero, so only bits 0, 1, 3, 7, 15, 31 and 63 can be set. -/
def roundConstant (ir : Nat) : UInt64 :=
  -- Seven candidate bits, one per `j`, each placed at position `2^j - 1`.
  (List.range 7).foldl
    (fun acc j => if rc (j + 7 * ir) then acc ||| ((1 : UInt64) <<< UInt64.ofNat (2 ^ j - 1)) else acc)
    0

/-- The rotation offsets of FIPS 202 §3.2.2, Algorithm 2, indexed like the state.

Lane `(0, 0)` is not rotated.

The walk starts at `(x, y) = (1, 0)` and visits the other 24 lanes once each:

```text
    step t:  offset of (x, y) is (t + 1)(t + 2)/2 mod 64
             then (x, y) := (y, (2x + 3y) mod 5)
```
-/
def rhoOffsets : Vector Nat LANES := Id.run do
  -- Every lane starts at offset 0, which is final for lane (0, 0).
  let mut offsets : Vector Nat LANES := Vector.replicate LANES 0
  let mut x := 1
  let mut y := 0
  for t in [:24] do
    -- Record the offset of the current lane, at index x + 5y.
    offsets := offsets.setIfInBounds (x + 5 * y) (((t + 1) * (t + 2) / 2) % 64)
    -- Move to the next lane of the walk.
    (x, y) := (y, (2 * x + 3 * y) % 5)
  return offsets

end Internal

/-- The 24 round constants `RC[i_r]` of iota.

Each equals the constant FIPS 202 §3.2.5, Algorithm 6 derives for its round.

The kernel checks this in `Proofs/Hash/Keccak.lean`. -/
def RC : Vector UInt64 ROUNDS := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offset of each lane in rho, indexed like the state.

Each equals the offset FIPS 202 §3.2.2, Algorithm 2 assigns to its lane.

The kernel checks this in `Proofs/Hash/Keccak.lean`.

```text
            x = 0   1   2   3   4
    y = 0       0   1  62  28  27
    y = 1      36  44   6  55  20
    y = 2       3  10  43  25  39
    y = 3      41  45  15  21   8
    y = 4      18   2  61  56  14
```
-/
def RHO : Vector UInt64 LANES := #v[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

/-! ## The step mappings

The five step mappings of FIPS 202 §3.2, each written out for the 25 lanes.

`A[x, y]` is lane `(x, y)` of the input, and the coordinates are taken mod 5 (§3.1.4).

`Proofs/Hash/Keccak.lean` proves that each mapping is the formula of the standard. -/

/-- Theta, FIPS 202 §3.2.1, Algorithm 1.

Each lane is XORed with the parities of two nearby columns.

The parity of column `x` is `C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4]`.

Lane `(x, y)` becomes `A[x, y] ^ D[x]`, with `D[x] = C[x - 1] ^ rot(C[x + 1], 1)`. -/
@[inline] def theta (A : State) : State :=
  -- Step 1: the parity of each column.
  let c0 := A.a0 ^^^ A.a5 ^^^ A.a10 ^^^ A.a15 ^^^ A.a20
  let c1 := A.a1 ^^^ A.a6 ^^^ A.a11 ^^^ A.a16 ^^^ A.a21
  let c2 := A.a2 ^^^ A.a7 ^^^ A.a12 ^^^ A.a17 ^^^ A.a22
  let c3 := A.a3 ^^^ A.a8 ^^^ A.a13 ^^^ A.a18 ^^^ A.a23
  let c4 := A.a4 ^^^ A.a9 ^^^ A.a14 ^^^ A.a19 ^^^ A.a24
  -- Step 2: `x - 1` is `x + 4` mod 5, and the bit shift `z - 1` is a rotation by 1.
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  -- Step 3: every lane of column `x` takes the same `D[x]`.
  ⟨A.a0 ^^^ d0, A.a1 ^^^ d1, A.a2 ^^^ d2, A.a3 ^^^ d3, A.a4 ^^^ d4,
   A.a5 ^^^ d0, A.a6 ^^^ d1, A.a7 ^^^ d2, A.a8 ^^^ d3, A.a9 ^^^ d4,
   A.a10 ^^^ d0, A.a11 ^^^ d1, A.a12 ^^^ d2, A.a13 ^^^ d3, A.a14 ^^^ d4,
   A.a15 ^^^ d0, A.a16 ^^^ d1, A.a17 ^^^ d2, A.a18 ^^^ d3, A.a19 ^^^ d4,
   A.a20 ^^^ d0, A.a21 ^^^ d1, A.a22 ^^^ d2, A.a23 ^^^ d3, A.a24 ^^^ d4⟩

/-- Rho, FIPS 202 §3.2.2, Algorithm 2.

Each lane is rotated by its own offset from the table above. -/
@[inline] def rho (A : State) : State :=
  ⟨rotl A.a0 RHO[0], rotl A.a1 RHO[1], rotl A.a2 RHO[2], rotl A.a3 RHO[3], rotl A.a4 RHO[4],
   rotl A.a5 RHO[5], rotl A.a6 RHO[6], rotl A.a7 RHO[7], rotl A.a8 RHO[8], rotl A.a9 RHO[9],
   rotl A.a10 RHO[10], rotl A.a11 RHO[11], rotl A.a12 RHO[12], rotl A.a13 RHO[13],
   rotl A.a14 RHO[14], rotl A.a15 RHO[15], rotl A.a16 RHO[16], rotl A.a17 RHO[17],
   rotl A.a18 RHO[18], rotl A.a19 RHO[19], rotl A.a20 RHO[20], rotl A.a21 RHO[21],
   rotl A.a22 RHO[22], rotl A.a23 RHO[23], rotl A.a24 RHO[24]⟩

/-- Pi, FIPS 202 §3.2.3, Algorithm 3.

The lanes are rearranged: `A'[x, y] = A[(x + 3y) mod 5, x]`. -/
@[inline] def pi (A : State) : State :=
  -- Output row `y` takes, for each `x`, lane `x` of input column `(x + 3y) mod 5`.
  ⟨A.a0, A.a6, A.a12, A.a18, A.a24,
   A.a3, A.a9, A.a10, A.a16, A.a22,
   A.a1, A.a7, A.a13, A.a19, A.a20,
   A.a4, A.a5, A.a11, A.a17, A.a23,
   A.a2, A.a8, A.a14, A.a15, A.a21⟩

/-- Chi, FIPS 202 §3.2.4, Algorithm 4.

The only nonlinear step: `A'[x, y] = A[x, y] ^ ((A[x + 1, y] ^ 1) & A[x + 2, y])`.

XOR with an all-ones lane is the complement. -/
@[inline] def chi (A : State) : State :=
  -- Each lane combines with the next two lanes of its row, which wraps around.
  ⟨A.a0 ^^^ (~~~A.a1 &&& A.a2), A.a1 ^^^ (~~~A.a2 &&& A.a3), A.a2 ^^^ (~~~A.a3 &&& A.a4),
   A.a3 ^^^ (~~~A.a4 &&& A.a0), A.a4 ^^^ (~~~A.a0 &&& A.a1),
   A.a5 ^^^ (~~~A.a6 &&& A.a7), A.a6 ^^^ (~~~A.a7 &&& A.a8), A.a7 ^^^ (~~~A.a8 &&& A.a9),
   A.a8 ^^^ (~~~A.a9 &&& A.a5), A.a9 ^^^ (~~~A.a5 &&& A.a6),
   A.a10 ^^^ (~~~A.a11 &&& A.a12), A.a11 ^^^ (~~~A.a12 &&& A.a13),
   A.a12 ^^^ (~~~A.a13 &&& A.a14), A.a13 ^^^ (~~~A.a14 &&& A.a10),
   A.a14 ^^^ (~~~A.a10 &&& A.a11),
   A.a15 ^^^ (~~~A.a16 &&& A.a17), A.a16 ^^^ (~~~A.a17 &&& A.a18),
   A.a17 ^^^ (~~~A.a18 &&& A.a19), A.a18 ^^^ (~~~A.a19 &&& A.a15),
   A.a19 ^^^ (~~~A.a15 &&& A.a16),
   A.a20 ^^^ (~~~A.a21 &&& A.a22), A.a21 ^^^ (~~~A.a22 &&& A.a23),
   A.a22 ^^^ (~~~A.a23 &&& A.a24), A.a23 ^^^ (~~~A.a24 &&& A.a20),
   A.a24 ^^^ (~~~A.a20 &&& A.a21)⟩

/-- Iota, FIPS 202 §3.2.5, Algorithm 6.

The round constant is XORed into lane `(0, 0)`, the only lane it touches. -/
@[inline] def iota (ir : Fin ROUNDS) (A : State) : State :=
  { A with a0 := A.a0 ^^^ RC[ir] }

/-! ## The permutation -/

/-- One round, FIPS 202 §3.3: `Rnd(A, i_r) = iota(chi(pi(rho(theta(A)))), i_r)`. -/
def round (ir : Fin ROUNDS) (A : State) : State :=
  iota ir (chi (pi (rho (theta A))))

/-- Keccak-f[1600], FIPS 202 §3.4: Keccak-p[1600, 24], rounds 0 to 23 in order.

With `n_r = 24 = 12 + 2l` the rounds run from `12 + 2l - n_r = 0` to `23` (§3.3, Algorithm 7). -/
def keccakF (A : State) : State :=
  roundsFrom 0 A
where
  /-- Rounds `i` to 23, in order. -/
  roundsFrom (i : Nat) (A : State) : State :=
    if h : i < ROUNDS then roundsFrom (i + 1) (round ⟨i, h⟩ A) else A
  termination_by ROUNDS - i

/-! ## The sponge

FIPS 202 §5.2 defines the Keccak family on byte strings `M` and output lengths `d`:

```text
    Keccak[c](M, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 - c](M, d)
```

Keccak-256 is `Keccak[512](M, 256)`, and Keccak-512 is `Keccak[1024](M, 512)`.

SHA3-256 is `Keccak[512](M || 01, 256)` (§6.1), so the two differ only in the two suffix bits.

In bytes, the first padding byte is `0x01` for Keccak-256 and `0x06` for SHA3-256.

The Keccak reference, version 3.0, calls Keccak-256 Keccak[r = 1088, c = 512].

It calls Keccak-512 Keccak[r = 576, c = 1024].

The padding and the absorbing below take the rate `r` in bytes. -/

/-- The rate of Keccak-256 in bytes: `r = 1600 - c = 1088` bits.

Each permutation absorbs this many message bytes. -/
def RATE : Nat := 136

/-- The digest length of Keccak-256 in bytes: `d = 256` bits. -/
def DIGEST_LEN : Nat := 32

/-- The rate of Keccak-512 in bytes: `r = 1600 - c = 576` bits. -/
def RATE_512 : Nat := 72

/-- The digest length of Keccak-512 in bytes: `d = 512` bits. -/
def DIGEST_LEN_512 : Nat := 64

/-- Byte `i` of the padding of a message of `len` bytes, at a rate of `rate` bytes.

- The first 1 bit of pad10*1 is bit 0 of the first padding byte.
- The final 1 bit is bit 7 of the last padding byte, and may share the first one's byte. -/
def paddingByte (rate len i : Nat) : UInt8 :=
  (if i = 0 then 0x01 else 0) ||| (if i + 1 = rate - len % rate then 0x80 else 0)

/-- The padding of a message of `len` bytes at a rate of `rate` bytes: pad10*1 of FIPS 202 §5.1.

The rule appends a 1 bit, then zeros, then a final 1 bit, so the total is a multiple of the rate.

At least two bits are appended.

So a whole block of padding is added when `len` is a multiple of the rate.

On byte strings the bits become bytes, least significant bit first (Appendix B.1):

```text
    k = rate - len mod rate bytes of padding, 1 <= k <= rate

    k = 1:   0x81                       the two 1 bits share one byte
    k >= 2:  0x01 0x00 ... 0x00 0x80    first bit 0 of the first byte, last bit 7 of the last
```
-/
def padding (rate len : Nat) : ByteArray :=
  -- The padding fills the block the message ends in, and a whole block when it ends exactly.
  ⟨Array.ofFn fun i : Fin (rate - len % rate) => paddingByte rate len i⟩

/-- The message followed by its padding: the string `P` of FIPS 202 §4, Algorithm 8, step 1. -/
def pad (rate : Nat) (msg : ByteArray) : ByteArray :=
  msg ++ padding rate msg.size

/-- The number of rate-sized blocks the padded message splits into: `n = len(P) / r`. -/
def blockCount (rate len : Nat) : Nat :=
  -- The padding brings the length up to the next multiple of the rate, strictly above `len`.
  len / rate + 1

namespace Internal

open EthLib.Base (byteAt)

/-- The lane that the 8 bytes from index `i` spell, the first byte least significant.

So byte `j` carries bits `8j` to `8j + 7` of the lane, as in FIPS 202 §3.1.2.

Bytes past the end of the string read as zero. -/
@[inline] def laneAt (bytes : ByteArray) (i : Nat) : UInt64 :=
  (byteAt bytes i).toUInt64 ||| (byteAt bytes (i + 1)).toUInt64 <<< 8 |||
    (byteAt bytes (i + 2)).toUInt64 <<< 16 ||| (byteAt bytes (i + 3)).toUInt64 <<< 24 |||
    (byteAt bytes (i + 4)).toUInt64 <<< 32 ||| (byteAt bytes (i + 5)).toUInt64 <<< 40 |||
    (byteAt bytes (i + 6)).toUInt64 <<< 48 ||| (byteAt bytes (i + 7)).toUInt64 <<< 56

/-- The 8 bytes of a lane, the least significant first. -/
def bytesOfLane (v : UInt64) : List UInt8 :=
  [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8,
    (v >>> 32).toUInt8, (v >>> 40).toUInt8, (v >>> 48).toUInt8, (v >>> 56).toUInt8]

/-- Lane `i` of the block of `rate` bytes from index `start`, or zero past the rate. -/
@[inline] def blockLane (rate : Nat) (bytes : ByteArray) (start i : Nat) : UInt64 :=
  if 8 * i < rate then laneAt bytes (start + 8 * i) else 0

/-- XOR the block of `rate` bytes from index `start` into the state, for a rate of at most 136.

This is `S ^ (P_i || 0^c)` of FIPS 202 §4, Algorithm 8, step 6.

A block of 136 bytes covers lanes 0 to 16, and a block of 72 bytes covers lanes 0 to 8.

The lanes past the block are XORed with zero, so they are left alone. -/
def absorbBlock (rate : Nat) (S : State) (bytes : ByteArray) (start : Nat) : State :=
  let lane := blockLane rate bytes start
  { S with
    a0 := S.a0 ^^^ lane 0, a1 := S.a1 ^^^ lane 1, a2 := S.a2 ^^^ lane 2,
    a3 := S.a3 ^^^ lane 3, a4 := S.a4 ^^^ lane 4, a5 := S.a5 ^^^ lane 5,
    a6 := S.a6 ^^^ lane 6, a7 := S.a7 ^^^ lane 7, a8 := S.a8 ^^^ lane 8,
    a9 := S.a9 ^^^ lane 9, a10 := S.a10 ^^^ lane 10, a11 := S.a11 ^^^ lane 11,
    a12 := S.a12 ^^^ lane 12, a13 := S.a13 ^^^ lane 13, a14 := S.a14 ^^^ lane 14,
    a15 := S.a15 ^^^ lane 15, a16 := S.a16 ^^^ lane 16 }

/-- The first `d = 256` bits of the state: `Trunc_d(S)` of FIPS 202 §4, Algorithm 8, step 9.

The digest fits in the first block of output, so no further permutation is needed.

Its 32 bytes are the bytes of lanes 0 to 3, in order. -/
def squeeze (S : State) : Vector UInt8 DIGEST_LEN :=
  ⟨(bytesOfLane S.a0 ++ bytesOfLane S.a1 ++ bytesOfLane S.a2 ++ bytesOfLane S.a3).toArray, rfl⟩

/-- The first `d = 512` bits of the state: `Trunc_d(S)` of FIPS 202 §4, Algorithm 8, step 9.

The digest fits in the first 72 bytes of output, so no further permutation is needed.

Its 64 bytes are the bytes of lanes 0 to 7, in order. -/
def squeeze512 (S : State) : Vector UInt8 DIGEST_LEN_512 :=
  ⟨(bytesOfLane S.a0 ++ bytesOfLane S.a1 ++ bytesOfLane S.a2 ++ bytesOfLane S.a3 ++
    bytesOfLane S.a4 ++ bytesOfLane S.a5 ++ bytesOfLane S.a6 ++ bytesOfLane S.a7).toArray, rfl⟩

/-- Absorb `n` blocks of `rate` bytes from index `start` on, in order, one permutation each.

This is FIPS 202 §4, Algorithm 8, step 6.

The blocks are read in place, so a long message is never copied block by block. -/
def absorbBlocks (f : State → State) (rate : Nat) (bytes : ByteArray) :
    Nat → Nat → State → State
  | 0, _, S => S
  | n + 1, start, S =>
    absorbBlocks f rate bytes n (start + rate) (f (absorbBlock rate S bytes start))

end Internal

/-- The absorbing phase of the sponge of FIPS 202 §4, Algorithm 8, at a rate of `rate` bytes.

The rate is at most 136 bytes, so each block fits in the lanes that it XORs.

```text
    P = M || pad10*1(r, len(M))              pad
    P = P_0 || ... || P_{n-1}                cut into blocks of r bits
    S = 0^1600                               start from the zero state
    for each block P_i:
        S = f(S ^ (P_i || 0^c))              absorb
```

FIPS 202 §4 defines the sponge for any permutation `f`, so the permutation is an argument. -/
def spongeAbsorb (f : State → State) (rate : Nat) (msg : ByteArray) : State :=
  -- Step 1: append the padding, so the length is a multiple of the rate.
  -- Steps 2 to 6: from the zero state, absorb the blocks in order, one permutation each.
  Internal.absorbBlocks f rate (pad rate msg) (blockCount rate msg.size) 0 State.zero

/-- Keccak-256 of a byte string: `Keccak[512](M, 256)` of FIPS 202 §5.2.

It absorbs at a rate of 136 bytes.

One block of output holds the 32 digest bytes, so no further permutation is needed. -/
def keccak256 (msg : ByteArray) : Vector UInt8 DIGEST_LEN :=
  Internal.squeeze (spongeAbsorb keccakF RATE msg)

/-- Keccak-512 of a byte string: `Keccak[1024](M, 512)` of FIPS 202 §5.2.

It absorbs at a rate of 72 bytes, with the same permutation as Keccak-256.

One block of output holds the 64 digest bytes, so no further permutation is needed. -/
def keccak512 (msg : ByteArray) : Vector UInt8 DIGEST_LEN_512 :=
  Internal.squeeze512 (spongeAbsorb keccakF RATE_512 msg)

/-! ## Incremental hashing

A hasher absorbs a message in pieces, for a digest of all the pieces so far.

It keeps the state after the whole blocks, and the bytes of the block not yet full.

The digest pads those bytes and absorbs the last block, without changing the hasher. -/

/-- A Keccak-256 hasher: the state after the whole blocks so far, and the bytes after them. -/
structure Hasher where
  /-- The state after every whole block so far. -/
  state : State
  /-- The bytes after the last whole block, fewer than the rate. -/
  pending : ByteArray

namespace Hasher

/-- The hasher of the empty message. -/
def empty : Hasher := ⟨State.zero, .empty⟩

/-- Absorb more bytes: every block they complete goes through the permutation. -/
def absorb (h : Hasher) (data : ByteArray) : Hasher :=
  let bytes := h.pending ++ data
  let count := bytes.size / RATE
  ⟨Internal.absorbBlocks keccakF RATE bytes count 0 h.state,
    bytes.extract (RATE * count) bytes.size⟩

/-- The Keccak-256 digest of every byte absorbed so far: pad the last block, absorb it, squeeze. -/
def digest (h : Hasher) : Vector UInt8 DIGEST_LEN :=
  let last := h.pending ++ padding RATE h.pending.size
  Internal.squeeze (Internal.absorbBlocks keccakF RATE last 1 0 h.state)

end Hasher

end EthLib.Cryptography.Hash.Keccak

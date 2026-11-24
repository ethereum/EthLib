module

public import EthLib.Base.Bytes

/-!
# `Hash.Keccak`

The Keccak-f[1600] permutation and the Keccak-256 and Keccak-512 hashes, as in FIPS 202.

Both hashes are the sponge over that permutation with Keccak's original padding.

Each definition follows a section of the standard, to be read against it.

It is not intended to be constant-time.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

/-! ## The state

FIPS 202 §3.1.2 views the 1600-bit state as a 5 x 5 array of lanes, each of `w = 64` bits.

Lane `(x, y)` has the index `x + 5 * y`, so the 25 lanes run row by row.
-/

/-- Lanes in the state: 1600 bits of 64-bit lanes. -/
def LANES : Nat := 25

/-- The parameter `l` of FIPS 202 §3.1, with lane width `w = 2^l = 64`. -/
def L : Nat := 6

/-- The lane width `w = 2^l` of FIPS 202 §3.1, in bits. -/
def W : Nat := 2 ^ L

/-- Rounds in Keccak-f[1600]: 24 rounds over a 1600-bit state.

FIPS 202 §3.4 sets `n_r = 12 + 2l`, with `l = 6` because `w = 2^6`. -/
def ROUNDS : Nat := 24

/-- The Keccak-f[1600] state: 25 lanes of 64 bits.

The field with the number `x + 5y` holds lane `(x, y)`, so each step mapping names its lanes.

Each step mapping is written out lane by lane, so compiled code keeps the lanes in machine words.

It also allocates at most one state per round. -/
structure State where
  -- Bit `z` of a lane is bit `z` of its 64-bit word.
  --
  -- That is the standard's own order: bit `64 * (x + 5y) + z` of the state string is `A[x, y, z]`.
  --
  -- So byte `k` of the state string is byte `k mod 8` of lane `k / 8`, least significant first.
  --
  -- FIPS 202 §3.1.3 and Appendix B.1 give that byte order.
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 :
    UInt64)
  deriving DecidableEq

/-- The all-zero state, where every sponge starts (FIPS 202 §4, Algorithm 8, step 5). -/
def State.zero : State :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- XOR a word into lane `i` of the state, the lane with the field number `i`.

An index of 25 or more names no lane, and leaves the state unchanged.

Absorbing a block XORs one such word into each lane of the rate. -/
def State.xorLane (A : State) (i : Nat) (v : UInt64) : State :=
  match i with
  | 0 => { A with a0 := A.a0 ^^^ v }
  | 1 => { A with a1 := A.a1 ^^^ v }
  | 2 => { A with a2 := A.a2 ^^^ v }
  | 3 => { A with a3 := A.a3 ^^^ v }
  | 4 => { A with a4 := A.a4 ^^^ v }
  | 5 => { A with a5 := A.a5 ^^^ v }
  | 6 => { A with a6 := A.a6 ^^^ v }
  | 7 => { A with a7 := A.a7 ^^^ v }
  | 8 => { A with a8 := A.a8 ^^^ v }
  | 9 => { A with a9 := A.a9 ^^^ v }
  | 10 => { A with a10 := A.a10 ^^^ v }
  | 11 => { A with a11 := A.a11 ^^^ v }
  | 12 => { A with a12 := A.a12 ^^^ v }
  | 13 => { A with a13 := A.a13 ^^^ v }
  | 14 => { A with a14 := A.a14 ^^^ v }
  | 15 => { A with a15 := A.a15 ^^^ v }
  | 16 => { A with a16 := A.a16 ^^^ v }
  | 17 => { A with a17 := A.a17 ^^^ v }
  | 18 => { A with a18 := A.a18 ^^^ v }
  | 19 => { A with a19 := A.a19 ^^^ v }
  | 20 => { A with a20 := A.a20 ^^^ v }
  | 21 => { A with a21 := A.a21 ^^^ v }
  | 22 => { A with a22 := A.a22 ^^^ v }
  | 23 => { A with a23 := A.a23 ^^^ v }
  | 24 => { A with a24 := A.a24 ^^^ v }
  | _ => A

/-- Rotate a lane towards its high bits by `n` positions, `n < 64`.

Bit `z` moves to bit `(z + n) mod 64`, which is what `rho` and `theta` ask of the bit index. -/
@[inline] def rotl (v : UInt64) (n : UInt64) : UInt64 :=
  -- The two shifts are disjoint and together move every bit once.
  -- At `n = 0` the right shift is by 64, which wraps to 0, and the result is still `v`.
  (v <<< n) ||| (v >>> (64 - n))

/-! ## The constants

FIPS 202 defines the round constants and the rotation offsets by two algorithms, transcribed here.

Its Table 2 lists the offsets before their reduction mod 64, and it lists no round constants. -/

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
  -- Algorithm 5 sets R[i] := R[i] ^ R[8] for i = 0, 4, 5, 6.
  -- - If R[8] = 1, it is one XOR with 0b01110001 = 2^6 + 2^5 + 2^4 + 2^0.
  -- - If R[8] = 0, it changes nothing, as x ^ 0 = x.
  let feedback := if (r >>> 8) % 2 = 1 then 0b01110001 else 0
  -- The remainder by 256 drops bit 8.
  (r ^^^ feedback) % 256

/-- The bit `rc(t)` of FIPS 202 §3.2.5, Algorithm 5.

The register starts at `10000000`, that is `R[0] = 1`, and runs `t mod 255` steps.

The output is the bit `R[0]`. -/
def rc (t : Nat) : Bool :=
  -- Step 1: when t mod 255 = 0, the output is 1.
  if t % 255 = 0 then true
  else
    -- Steps 2 and 3: start from R = 10000000, that is R[0] = 1, and run t mod 255 steps.
    let R := Nat.repeat lfsrStep (t % 255) 1
    -- Step 4: the output is R[0], bit 0 of the number.
    R.testBit 0

/-- The round constant of round `i_r`, by FIPS 202 §3.2.5, Algorithm 6, steps 2 and 3:

2. Let `RC = 0^w`.
3. For `j` from 0 to `l`, let `RC[2^j - 1] = rc(j + 7 * i_r)`.

Bit `z` of the lane is `RC[z]`, so only bits 0, 1, 3, 7, 15, 31 and 63 can be set. -/
def roundConstant (ir : Nat) : UInt64 :=
  -- Step 3, for one j: bit 2^j - 1 of the lane is rc(j + 7 * i_r).
  let bit (j : Nat) : UInt64 := if rc (j + 7 * ir) then 1 <<< UInt64.ofNat (2 ^ j - 1) else 0
  -- Step 2 starts from the zero lane, and step 3 sets the bits for j = 0 to l.
  -- The positions 2^j - 1 are distinct, so OR places each bit without touching the others.
  (List.range (L + 1)).foldl (fun RC j => RC ||| bit j) 0

/-- The rotation offsets of FIPS 202 §3.2.2, Algorithm 2, indexed like the state.

Algorithm 2 rotates each lane of `A` into `A'`.

This function keeps only the offsets: `(t + 1)(t + 2)/2 mod w` for lane `(x, y)`, 0 for `(0, 0)`. -/
def rhoOffsets : Vector Nat LANES := Id.run do
  -- Step 1: for all z, let A'[0, 0, z] = A[0, 0, z].
  --
  -- Lane (0, 0) is not rotated, so its offset stays 0.
  let mut offsets : Vector Nat LANES := Vector.replicate LANES 0
  -- Step 2: let (x, y) = (1, 0), so the walk starts at lane (1, 0).
  let mut x := 1
  let mut y := 0
  -- Step 3: for t from 0 to 23.
  for t in [:24] do
    -- Step 3a: let A'[x, y, z] = A[x, y, (z - (t + 1)(t + 2)/2) mod w] for all z.
    --
    -- Only the offset of lane (x, y) is kept, stored at index x + 5y.
    offsets := offsets.setIfInBounds (x + 5 * y) (((t + 1) * (t + 2) / 2) % W)
    -- Step 3b: let (x, y) = (y, (2x + 3y) mod 5), the next lane of the walk.
    (x, y) := (y, (2 * x + 3 * y) % 5)
  -- Step 4: return A'.
  --
  -- Here the output is the offsets of all 25 lanes.
  return offsets

end Internal

/-- The 24 round constants `RC[i_r]` of iota.

Each equals the constant FIPS 202 §3.2.5, Algorithm 6 derives for its round. -/
def RC : Vector UInt64 ROUNDS := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offset of each lane in rho, indexed like the state.

Each equals the offset FIPS 202 §3.2.2, Algorithm 2 assigns to its lane.

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

`Proofs/Hash/Keccak/Basic.lean` proves that each mapping is the formula of the standard. -/

/-- Theta, FIPS 202 §3.2.1, Algorithm 1, for all `x, y < 5` and `z < w`.

A lane holds its `w` bits `z` in one word, so each step runs on whole lanes. -/
@[inline] def theta (A : State) : State :=
  -- Step 1: let C[x, z] = A[x, 0, z] ^ A[x, 1, z] ^ A[x, 2, z] ^ A[x, 3, z] ^ A[x, 4, z].
  --
  -- On lanes: C[x] = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4], lane (x, y) at x + 5y.
  let c0 := A.a0 ^^^ A.a5 ^^^ A.a10 ^^^ A.a15 ^^^ A.a20
  let c1 := A.a1 ^^^ A.a6 ^^^ A.a11 ^^^ A.a16 ^^^ A.a21
  let c2 := A.a2 ^^^ A.a7 ^^^ A.a12 ^^^ A.a17 ^^^ A.a22
  let c3 := A.a3 ^^^ A.a8 ^^^ A.a13 ^^^ A.a18 ^^^ A.a23
  let c4 := A.a4 ^^^ A.a9 ^^^ A.a14 ^^^ A.a19 ^^^ A.a24
  -- Step 2: let D[x, z] = C[(x - 1) mod 5, z] ^ C[(x + 1) mod 5, (z - 1) mod w].
  --
  -- Reading bit (z - 1) mod w for bit z is a rotation by 1 towards the high bits.
  --
  -- On lanes: D[x] = C[(x - 1) mod 5] ^ rotl(C[(x + 1) mod 5], 1).
  let d0 := c4 ^^^ rotl c1 1
  let d1 := c0 ^^^ rotl c2 1
  let d2 := c1 ^^^ rotl c3 1
  let d3 := c2 ^^^ rotl c4 1
  let d4 := c3 ^^^ rotl c0 1
  -- Step 3: let A'[x, y, z] = A[x, y, z] ^ D[x, z].
  --
  -- Step 4: return A'.
  --
  -- On lanes, the output is A', where A'[x, y] = A[x, y] ^ D[x].
  ⟨A.a0 ^^^ d0, A.a1 ^^^ d1, A.a2 ^^^ d2, A.a3 ^^^ d3, A.a4 ^^^ d4,
   A.a5 ^^^ d0, A.a6 ^^^ d1, A.a7 ^^^ d2, A.a8 ^^^ d3, A.a9 ^^^ d4,
   A.a10 ^^^ d0, A.a11 ^^^ d1, A.a12 ^^^ d2, A.a13 ^^^ d3, A.a14 ^^^ d4,
   A.a15 ^^^ d0, A.a16 ^^^ d1, A.a17 ^^^ d2, A.a18 ^^^ d3, A.a19 ^^^ d4,
   A.a20 ^^^ d0, A.a21 ^^^ d1, A.a22 ^^^ d2, A.a23 ^^^ d3, A.a24 ^^^ d4⟩

/-- Rho, FIPS 202 §3.2.2, Algorithm 2, for all `z < w`.

The offsets are written as numbers, so that each rotation is by a constant.

The kernel checks that these numbers are the offset table, lane by lane. -/
@[inline] def rho (A : State) : State :=
  -- Step 1: let A'[0, 0, z] = A[0, 0, z].
  --
  -- Step 2: let (x, y) = (1, 0).
  --
  -- Step 3, for t from 0 to 23: let A'[x, y, z] = A[x, y, (z - (t + 1)(t + 2)/2) mod w].
  --
  -- Then, in the same step 3: let (x, y) = (y, (2x + 3y) mod 5).
  --
  -- Step 4: return A'.
  --
  -- Reading bit (z - d) mod w for bit z is a rotation of the lane by d towards the high bits.
  --
  -- So A'[x, y] = rotl(A[x, y], d), with d the offset of lane (x, y) in the offset table.
  --
  -- A'[x, y] = rotl(A[x, y], d), with d = (t + 1)(t + 2)/2 mod w for the step t reaching (x, y).
  -- y = 0
  ⟨rotl A.a0 0,     -- A'[0, 0]: step 1, d = 0
   rotl A.a1 1,     -- A'[1, 0]: t = 0, d = (1 * 2)/2 mod 64 = 1 mod 64 = 1
   rotl A.a2 62,    -- A'[2, 0]: t = 18, d = (19 * 20)/2 mod 64 = 190 mod 64 = 62
   rotl A.a3 28,    -- A'[3, 0]: t = 6, d = (7 * 8)/2 mod 64 = 28 mod 64 = 28
   rotl A.a4 27,    -- A'[4, 0]: t = 12, d = (13 * 14)/2 mod 64 = 91 mod 64 = 27
   -- y = 1
   rotl A.a5 36,    -- A'[0, 1]: t = 7, d = (8 * 9)/2 mod 64 = 36 mod 64 = 36
   rotl A.a6 44,    -- A'[1, 1]: t = 23, d = (24 * 25)/2 mod 64 = 300 mod 64 = 44
   rotl A.a7 6,     -- A'[2, 1]: t = 2, d = (3 * 4)/2 mod 64 = 6 mod 64 = 6
   rotl A.a8 55,    -- A'[3, 1]: t = 9, d = (10 * 11)/2 mod 64 = 55 mod 64 = 55
   rotl A.a9 20,    -- A'[4, 1]: t = 22, d = (23 * 24)/2 mod 64 = 276 mod 64 = 20
   -- y = 2
   rotl A.a10 3,    -- A'[0, 2]: t = 1, d = (2 * 3)/2 mod 64 = 3 mod 64 = 3
   rotl A.a11 10,   -- A'[1, 2]: t = 3, d = (4 * 5)/2 mod 64 = 10 mod 64 = 10
   rotl A.a12 43,   -- A'[2, 2]: t = 17, d = (18 * 19)/2 mod 64 = 171 mod 64 = 43
   rotl A.a13 25,   -- A'[3, 2]: t = 16, d = (17 * 18)/2 mod 64 = 153 mod 64 = 25
   rotl A.a14 39,   -- A'[4, 2]: t = 20, d = (21 * 22)/2 mod 64 = 231 mod 64 = 39
   -- y = 3
   rotl A.a15 41,   -- A'[0, 3]: t = 13, d = (14 * 15)/2 mod 64 = 105 mod 64 = 41
   rotl A.a16 45,   -- A'[1, 3]: t = 8, d = (9 * 10)/2 mod 64 = 45 mod 64 = 45
   rotl A.a17 15,   -- A'[2, 3]: t = 4, d = (5 * 6)/2 mod 64 = 15 mod 64 = 15
   rotl A.a18 21,   -- A'[3, 3]: t = 5, d = (6 * 7)/2 mod 64 = 21 mod 64 = 21
   rotl A.a19 8,    -- A'[4, 3]: t = 15, d = (16 * 17)/2 mod 64 = 136 mod 64 = 8
   -- y = 4
   rotl A.a20 18,   -- A'[0, 4]: t = 19, d = (20 * 21)/2 mod 64 = 210 mod 64 = 18
   rotl A.a21 2,    -- A'[1, 4]: t = 10, d = (11 * 12)/2 mod 64 = 66 mod 64 = 2
   rotl A.a22 61,   -- A'[2, 4]: t = 21, d = (22 * 23)/2 mod 64 = 253 mod 64 = 61
   rotl A.a23 56,   -- A'[3, 4]: t = 14, d = (15 * 16)/2 mod 64 = 120 mod 64 = 56
   rotl A.a24 14⟩   -- A'[4, 4]: t = 11, d = (12 * 13)/2 mod 64 = 78 mod 64 = 14

/-- Pi, FIPS 202 §3.2.3, Algorithm 3, for all `x, y < 5` and `z < w`:

1. Let `A'[x, y, z] = A[(x + 3y) mod 5, x, z]`.
2. Return `A'`.

The formula moves whole lanes, so `A'[x, y] = A[(x + 3y) mod 5, x]`. -/
@[inline] def pi (A : State) : State :=
  -- A'[x, y] = A[(x + 3y) mod 5, x], and lane (x, y) is at index x + 5y.
  -- y = 0
  ⟨A.a0,    -- A'[0, 0] = A[(0 + 0) mod 5, 0] = A[0, 0], index 0 + 5 * 0
   A.a6,    -- A'[1, 0] = A[(1 + 0) mod 5, 1] = A[1, 1], index 1 + 5 * 1
   A.a12,   -- A'[2, 0] = A[(2 + 0) mod 5, 2] = A[2, 2], index 2 + 5 * 2
   A.a18,   -- A'[3, 0] = A[(3 + 0) mod 5, 3] = A[3, 3], index 3 + 5 * 3
   A.a24,   -- A'[4, 0] = A[(4 + 0) mod 5, 4] = A[4, 4], index 4 + 5 * 4
   -- y = 1
   A.a3,    -- A'[0, 1] = A[(0 + 3) mod 5, 0] = A[3, 0], index 3 + 5 * 0
   A.a9,    -- A'[1, 1] = A[(1 + 3) mod 5, 1] = A[4, 1], index 4 + 5 * 1
   A.a10,   -- A'[2, 1] = A[(2 + 3) mod 5, 2] = A[0, 2], index 0 + 5 * 2
   A.a16,   -- A'[3, 1] = A[(3 + 3) mod 5, 3] = A[1, 3], index 1 + 5 * 3
   A.a22,   -- A'[4, 1] = A[(4 + 3) mod 5, 4] = A[2, 4], index 2 + 5 * 4
   -- y = 2
   A.a1,    -- A'[0, 2] = A[(0 + 6) mod 5, 0] = A[1, 0], index 1 + 5 * 0
   A.a7,    -- A'[1, 2] = A[(1 + 6) mod 5, 1] = A[2, 1], index 2 + 5 * 1
   A.a13,   -- A'[2, 2] = A[(2 + 6) mod 5, 2] = A[3, 2], index 3 + 5 * 2
   A.a19,   -- A'[3, 2] = A[(3 + 6) mod 5, 3] = A[4, 3], index 4 + 5 * 3
   A.a20,   -- A'[4, 2] = A[(4 + 6) mod 5, 4] = A[0, 4], index 0 + 5 * 4
   -- y = 3
   A.a4,    -- A'[0, 3] = A[(0 + 9) mod 5, 0] = A[4, 0], index 4 + 5 * 0
   A.a5,    -- A'[1, 3] = A[(1 + 9) mod 5, 1] = A[0, 1], index 0 + 5 * 1
   A.a11,   -- A'[2, 3] = A[(2 + 9) mod 5, 2] = A[1, 2], index 1 + 5 * 2
   A.a17,   -- A'[3, 3] = A[(3 + 9) mod 5, 3] = A[2, 3], index 2 + 5 * 3
   A.a23,   -- A'[4, 3] = A[(4 + 9) mod 5, 4] = A[3, 4], index 3 + 5 * 4
   -- y = 4
   A.a2,    -- A'[0, 4] = A[(0 + 12) mod 5, 0] = A[2, 0], index 2 + 5 * 0
   A.a8,    -- A'[1, 4] = A[(1 + 12) mod 5, 1] = A[3, 1], index 3 + 5 * 1
   A.a14,   -- A'[2, 4] = A[(2 + 12) mod 5, 2] = A[4, 2], index 4 + 5 * 2
   A.a15,   -- A'[3, 4] = A[(3 + 12) mod 5, 3] = A[0, 3], index 0 + 5 * 3
   A.a21⟩   -- A'[4, 4] = A[(4 + 12) mod 5, 4] = A[1, 4], index 1 + 5 * 4

/-- Chi, FIPS 202 §3.2.4, Algorithm 4, for all `x, y < 5` and `z < w`.

Here `&` is the product of bits, the AND, and makes chi the only nonlinear step. -/
@[inline] def chi (A : State) : State :=
  -- Step 1: A'[x, y, z] = A[x, y, z] ^ ((A[(x + 1) mod 5, y, z] ^ 1) & A[(x + 2) mod 5, y, z]).
  --
  -- Step 2: return A'.
  --
  -- The formula uses the same z on all sides, so it runs on whole lanes, with ^ 1 the complement.
  --
  -- On lanes, within row y: A'[x, y] = A[x, y] ^ (~A[(x + 1) mod 5, y] & A[(x + 2) mod 5, y]).
  --
  -- y = 0
  ⟨A.a0 ^^^ (~~~A.a1 &&& A.a2), A.a1 ^^^ (~~~A.a2 &&& A.a3), A.a2 ^^^ (~~~A.a3 &&& A.a4),
   A.a3 ^^^ (~~~A.a4 &&& A.a0), A.a4 ^^^ (~~~A.a0 &&& A.a1),
   -- y = 1
   A.a5 ^^^ (~~~A.a6 &&& A.a7), A.a6 ^^^ (~~~A.a7 &&& A.a8), A.a7 ^^^ (~~~A.a8 &&& A.a9),
   A.a8 ^^^ (~~~A.a9 &&& A.a5), A.a9 ^^^ (~~~A.a5 &&& A.a6),
   -- y = 2
   A.a10 ^^^ (~~~A.a11 &&& A.a12), A.a11 ^^^ (~~~A.a12 &&& A.a13),
   A.a12 ^^^ (~~~A.a13 &&& A.a14), A.a13 ^^^ (~~~A.a14 &&& A.a10),
   A.a14 ^^^ (~~~A.a10 &&& A.a11),
   -- y = 3
   A.a15 ^^^ (~~~A.a16 &&& A.a17), A.a16 ^^^ (~~~A.a17 &&& A.a18),
   A.a17 ^^^ (~~~A.a18 &&& A.a19), A.a18 ^^^ (~~~A.a19 &&& A.a15),
   A.a19 ^^^ (~~~A.a15 &&& A.a16),
   -- y = 4
   A.a20 ^^^ (~~~A.a21 &&& A.a22), A.a21 ^^^ (~~~A.a22 &&& A.a23),
   A.a22 ^^^ (~~~A.a23 &&& A.a24), A.a23 ^^^ (~~~A.a24 &&& A.a20),
   A.a24 ^^^ (~~~A.a20 &&& A.a21)⟩

/-- Iota, FIPS 202 §3.2.5, Algorithm 6, steps 1, 4 and 5.

The round constant is XORed into lane `(0, 0)`, the only lane it touches. -/
@[inline] def iota (ir : Fin ROUNDS) (A : State) : State :=
  { A with a0 := A.a0 ^^^ RC[ir] }

/-! ## The permutation -/

/-- One round, FIPS 202 §3.3: `Rnd(A, i_r) = iota(chi(pi(rho(theta(A)))), i_r)`. -/
@[inline] def round (ir : Fin ROUNDS) (A : State) : State :=
  iota ir (chi (pi (rho (theta A))))

/-- Keccak-f[1600], FIPS 202 §3.4: Keccak-p[1600, 24], rounds 0 to 23 in order.

With `n_r = 24 = 12 + 2l` the rounds run from `12 + 2l - n_r = 0` to `23` (§3.3, Algorithm 7). -/
def keccakF (A : State) : State :=
  -- FIPS 202 §3.4: 24 rounds over a 1600-bit state, from round 0.
  roundsFrom 0 A
where
  /-- Rounds `i` to 23, in order.

  A step runs eight rounds while eight remain, and one round otherwise.

  The compiled code then keeps the lanes in machine words across eight rounds. -/
  roundsFrom (i : Nat) (A : State) : State :=
    if h : i + 8 ≤ ROUNDS then
      -- Rounds i to i + 7, the first one innermost.
      roundsFrom (i + 8) (round ⟨i + 7, by omega⟩ (round ⟨i + 6, by omega⟩
        (round ⟨i + 5, by omega⟩ (round ⟨i + 4, by omega⟩ (round ⟨i + 3, by omega⟩
          (round ⟨i + 2, by omega⟩ (round ⟨i + 1, by omega⟩ (round ⟨i, by omega⟩ A))))))))
    else if h : i < ROUNDS then roundsFrom (i + 1) (round ⟨i, h⟩ A)
    else A
  termination_by ROUNDS - i

/-! ## The sponge

FIPS 202 §5.2 defines the Keccak family on bit strings `N` and output lengths `d`:

```text
    Keccak[c](N, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 - c](N, d)
```

Keccak-256 is `Keccak[512](N, 256)`, and Keccak-512 is `Keccak[1024](N, 512)`.

The padding and the absorbing below take the rate `r` in bytes. -/

/-- The rate of Keccak-256 in bytes: `r = 1600 - c = 1088` bits, with capacity `c = 512` bits.

Each permutation absorbs this many message bytes.

The Keccak reference, version 3.0, calls Keccak-256 Keccak[r = 1088, c = 512]. -/
def RATE_256 : Nat := 136

/-- The digest length of Keccak-256 in bytes: `d = 256` bits. -/
def DIGEST_LEN_256 : Nat := 32

/-- The rate of Keccak-512 in bytes: `r = 1600 - c = 576` bits, with capacity `c = 1024` bits.

The Keccak reference, version 3.0, calls Keccak-512 Keccak[r = 576, c = 1024]. -/
def RATE_512 : Nat := 72

/-- The digest length of Keccak-512 in bytes: `d = 512` bits. -/
def DIGEST_LEN_512 : Nat := 64

/-- Byte `i` of the padding of a message of `len` bytes, at a rate of `rate` bytes.

- The first 1 bit of pad10*1 is bit 0 of the first padding byte.
- The final 1 bit is bit 7 of the last padding byte, and may share the first one's byte. -/
def paddingByte (rate len i : Nat) : UInt8 :=
  -- The padding has k = rate - len mod rate bytes, numbered 0 to k - 1.
  let k := rate - len % rate
  -- Keccak-256 and Keccak-512 add no 01 suffix: they pad with 0x01, any zero bytes, then 0x80.
  --
  -- SHA3-256 instead pads with 0x06, any zero bytes, then 0x80 (FIPS 202 Appendix B.2, Table 6).
  --
  -- A single padding byte of SHA3-256 holds both, so it is 0x86.
  --
  -- The first 1 bit of pad10*1 is bit 0 of byte 0.
  let first : UInt8 := if i = 0 then 0b00000001 else 0
  -- The final 1 bit is bit 7 of the last byte, k - 1.
  let last : UInt8 := if i + 1 = k then 0b10000000 else 0
  -- When k = 1, both bits fall in byte 0, which is then 0b10000001.
  --
  -- So a single padding byte of Keccak holds both, and it is 0x81.
  first ||| last

/-- The pad10*1 padding of a `len`-byte message at a `rate`-byte rate, FIPS 202 §5.1, Algorithm 9.

The message is a byte string, so the padding fills whole bytes.

A whole block of padding is added when `len` is a multiple of the rate. -/
def padding (rate len : Nat) : ByteArray :=
  -- In bits, x = 8 * rate and m = 8 * len.
  --
  -- Step 1: let j = (-m - 2) mod x.
  --
  -- Step 2: return P = 1 || 0^j || 1.
  --
  -- P has j + 2 = 8k bits, with k = rate - len mod rate and 1 <= k <= rate.
  --
  -- P fills the rest of the last block: k = rate - len mod rate bytes.
  let k := rate - len % rate
  -- Only the first and the last padding bytes can be nonzero.
  --
  -- So the k bytes start as zeros, and then those two are set.
  let zeros : Array UInt8 := Array.replicate k 0
  -- In bytes, least significant bit first (Appendix B.1), byte i of P is the padding byte above.
  --
  -- Byte 0 gets the first 1 bit and byte k - 1 the final one: for k = 1, byte 0 is 0b10000001.
  -- For a zero rate there are no bytes, and both writes leave the empty array unchanged.
  ⟨(zeros.setIfInBounds 0 (paddingByte rate len 0)).setIfInBounds (k - 1)
    (paddingByte rate len (k - 1))⟩

/-- The message followed by its padding: the string `P` of FIPS 202 §4, Algorithm 8, step 1. -/
def pad (rate : Nat) (msg : ByteArray) : ByteArray :=
  msg ++ padding rate msg.size

/-- The number of rate-sized blocks the padded message splits into: `n = len(P) / r`. -/
def blockCount (rate len : Nat) : Nat :=
  -- The padding brings the length up to the next multiple of the rate, strictly above `len`.
  len / rate + 1

/-! ## Values as lanes

FIPS 202 §3.1.2 holds the state as lanes, and Appendix B.1 orders the bytes within a lane.

Byte `k` of a value is byte `k mod 8` of its lane `k / 8`, least significant first.

So a value of `8k` bytes is `k` lanes, read and written without moving a byte. -/

/-- A 16-byte value as two lanes, such as half of a Keccak-256 digest. -/
@[ext] structure Lanes2 where
  /-- Bytes 0 to 7. -/
  lo : UInt64
  /-- Bytes 8 to 15. -/
  hi : UInt64
  deriving DecidableEq, Inhabited

/-- A 32-byte value as four lanes: a Keccak-256 digest. -/
@[ext] structure Lanes4 where
  /-- Bytes 0 to 7. -/
  w0 : UInt64
  /-- Bytes 8 to 15. -/
  w1 : UInt64
  /-- Bytes 16 to 23. -/
  w2 : UInt64
  /-- Bytes 24 to 31. -/
  w3 : UInt64
  deriving DecidableEq, Inhabited

/-- The 16 bytes of two lanes, least significant first.

Byte `j`, for `j < 8`, is bits `8j` to `8j + 7` of the low lane.

Byte `8 + j` is the same bits of the high lane. -/
def Lanes2.bytes (w : Lanes2) : Vector UInt8 16 :=
  -- Byte j of a lane is its bits 8j to 8j + 7, so the lane shifted down by 8j.
  let b (v : UInt64) (j : UInt64) : UInt8 := (v >>> (8 * j)).toUInt8
  #v[b w.lo 0, b w.lo 1, b w.lo 2, b w.lo 3, b w.lo 4, b w.lo 5, b w.lo 6, b w.lo 7,
    b w.hi 0, b w.hi 1, b w.hi 2, b w.hi 3, b w.hi 4, b w.hi 5, b w.hi 6, b w.hi 7]

/-- The 32 bytes of four lanes, least significant first. -/
def Lanes4.bytes (w : Lanes4) : Vector UInt8 32 :=
  -- Byte j of a lane is its bits 8j to 8j + 7, so the lane shifted down by 8j.
  let b (v : UInt64) (j : UInt64) : UInt8 := (v >>> (8 * j)).toUInt8
  #v[-- Bytes 0 to 7: the first lane
    b w.w0 0, b w.w0 1, b w.w0 2, b w.w0 3, b w.w0 4, b w.w0 5, b w.w0 6, b w.w0 7,
    -- Bytes 8 to 15: the second lane
    b w.w1 0, b w.w1 1, b w.w1 2, b w.w1 3, b w.w1 4, b w.w1 5, b w.w1 6, b w.w1 7,
    -- Bytes 16 to 23: the third lane
    b w.w2 0, b w.w2 1, b w.w2 2, b w.w2 3, b w.w2 4, b w.w2 5, b w.w2 6, b w.w2 7,
    -- Bytes 24 to 31: the fourth lane
    b w.w3 0, b w.w3 1, b w.w3 2, b w.w3 3, b w.w3 4, b w.w3 5, b w.w3 6, b w.w3 7]

/-- The two lanes of a 16-byte value, the low one first. -/
@[inline] def Lanes2.toArray (w : Lanes2) : Array UInt64 :=
  #[w.lo, w.hi]

/-- The four lanes of a 32-byte value, in order. -/
@[inline] def Lanes4.toArray (w : Lanes4) : Array UInt64 :=
  #[w.w0, w.w1, w.w2, w.w3]

namespace Internal

/-- The lane of bytes `p` to `p + 7` of the value that an array of lanes holds.

The offset `p` must be a multiple of 8, so the lane is entry `p / 8` of the array.

Past the end of the array the lane is zero, as the sponge reads the bytes past a message. -/
@[inline] def laneOfArray (lanes : Array UInt64) (p : Nat) : UInt64 :=
  lanes.getD (p / 8) 0

open EthLib.Base (byteAt)

/-- The lane read from the 8 bytes at index `i`, least significant byte first:

`lane = B[i] + B[i + 1] * 2^8 + B[i + 2] * 2^16 + ... + B[i + 7] * 2^56`

So bit `z` of the lane is bit `z mod 8` of byte `i + z / 8`, by FIPS 202 §3.1.2 and Appendix B.1.

Bytes past the end of the string read as zero. -/
@[inline] def laneAt (bytes : ByteArray) (i : Nat) : UInt64 :=
  -- Byte i + j goes to bits 8j to 8j + 7, so it is shifted by 8j.
  -- The bit ranges are disjoint, so OR adds them without carries.
  (byteAt bytes i).toUInt64 |||                -- bits  0 to  7
  (byteAt bytes (i + 1)).toUInt64 <<< 8 |||    -- bits  8 to 15
  (byteAt bytes (i + 2)).toUInt64 <<< 16 |||   -- bits 16 to 23
  (byteAt bytes (i + 3)).toUInt64 <<< 24 |||   -- bits 24 to 31
  (byteAt bytes (i + 4)).toUInt64 <<< 32 |||   -- bits 32 to 39
  (byteAt bytes (i + 5)).toUInt64 <<< 40 |||   -- bits 40 to 47
  (byteAt bytes (i + 6)).toUInt64 <<< 48 |||   -- bits 48 to 55
  (byteAt bytes (i + 7)).toUInt64 <<< 56       -- bits 56 to 63

/-- The 8 bytes of a lane, least significant byte first, the inverse of reading a lane:

`B[j] = (lane / 2^(8j)) mod 2^8`, for `j = 0` to 7.

So byte `j` holds bits `8j` to `8j + 7` of the lane, by FIPS 202 §3.1.2 and Appendix B.1. -/
def bytesOfLane (v : UInt64) : List UInt8 :=
  -- Byte j is the lane shifted down by 8j, cut to its low 8 bits by the conversion to a byte.
  [v.toUInt8,                -- bits  0 to  7
    (v >>> 8).toUInt8,       -- bits  8 to 15
    (v >>> 16).toUInt8,      -- bits 16 to 23
    (v >>> 24).toUInt8,      -- bits 24 to 31
    (v >>> 32).toUInt8,      -- bits 32 to 39
    (v >>> 40).toUInt8,      -- bits 40 to 47
    (v >>> 48).toUInt8,      -- bits 48 to 55
    (v >>> 56).toUInt8]      -- bits 56 to 63

/-- Lane `i` of `P_i || 0^c`, FIPS 202 §4, Algorithm 8, step 6, with block `P_i` at `start`.

The message is read a lane at a time: `read p` is the lane of its bytes `p` to `p + 7`. -/
@[inline] def blockLane (rate : Nat) (read : Nat → UInt64) (start i : Nat) : UInt64 :=
  -- If 8i + 8 <= rate, the lane is bytes 8i to 8i + 7 of P_i.
  --
  -- A lane is read only when all 8 of its bytes lie in the block, so it never reads past the block.
  --
  -- Bytes 8i to 8i + 7 of P_i are at index start + 8i of the string.
  if 8 * i + 8 ≤ rate then read (start + 8 * i)
  -- Otherwise the lane is zero: past the rate, the lane is in the capacity 0^c.
  --
  -- When the rate is a multiple of 8 bytes, no lane straddles P_i and 0^c.
  --
  -- So every lane past the rate lies wholly in 0^c.
  else 0

/-- The XOR inside FIPS 202 §4, Algorithm 8, step 6, with block `P_i` of `rate` bytes at `start`.

This function returns `S ^ (P_i || 0^c)`, and the permutation `f` follows it.

All 25 lanes are XORed, so every positive rate below 200 bytes that is a multiple of 8 works. -/
@[specialize] def absorbBlock (rate : Nat) (S : State) (read : Nat → UInt64) (start : Nat) :
    State :=
  -- Step 6: for i from 0 to n - 1, let S = f(S ^ (P_i || 0^c)).
  --
  -- lane i is lane i of P_i || 0^c: bytes 8i to 8i + 7 of P_i, or 0 past the rate.
  let lane := blockLane rate read start
  -- Lane i of S, for i < 25, is XORed with lane i of P_i || 0^c.
  --
  -- A rate of 136 bytes fills lanes 0 to 16 with P_i, and lanes 17 to 24 are zero.
  --
  -- A rate of 72 bytes fills lanes 0 to 8, and lanes 9 to 24 are zero.
  --
  -- y = 0
  ⟨S.a0 ^^^ lane 0,     -- S[0, 0] ^ bytes 0 to 7 of P_i
   S.a1 ^^^ lane 1,     -- S[1, 0] ^ bytes 8 to 15 of P_i
   S.a2 ^^^ lane 2,     -- S[2, 0] ^ bytes 16 to 23 of P_i
   S.a3 ^^^ lane 3,     -- S[3, 0] ^ bytes 24 to 31 of P_i
   S.a4 ^^^ lane 4,     -- S[4, 0] ^ bytes 32 to 39 of P_i
   -- y = 1
   S.a5 ^^^ lane 5,     -- S[0, 1] ^ bytes 40 to 47 of P_i
   S.a6 ^^^ lane 6,     -- S[1, 1] ^ bytes 48 to 55 of P_i
   S.a7 ^^^ lane 7,     -- S[2, 1] ^ bytes 56 to 63 of P_i
   S.a8 ^^^ lane 8,     -- S[3, 1] ^ bytes 64 to 71 of P_i
   S.a9 ^^^ lane 9,     -- S[4, 1] ^ bytes 72 to 79 of P_i, or 0 at rate 72
   -- y = 2
   S.a10 ^^^ lane 10,   -- S[0, 2] ^ bytes 80 to 87 of P_i, or 0 at rate 72
   S.a11 ^^^ lane 11,   -- S[1, 2] ^ bytes 88 to 95 of P_i, or 0 at rate 72
   S.a12 ^^^ lane 12,   -- S[2, 2] ^ bytes 96 to 103 of P_i, or 0 at rate 72
   S.a13 ^^^ lane 13,   -- S[3, 2] ^ bytes 104 to 111 of P_i, or 0 at rate 72
   S.a14 ^^^ lane 14,   -- S[4, 2] ^ bytes 112 to 119 of P_i, or 0 at rate 72
   -- y = 3
   S.a15 ^^^ lane 15,   -- S[0, 3] ^ bytes 120 to 127 of P_i, or 0 at rate 72
   S.a16 ^^^ lane 16,   -- S[1, 3] ^ bytes 128 to 135 of P_i, or 0 at rate 72
   S.a17 ^^^ lane 17,   -- S[2, 3] ^ bytes 136 to 143 of P_i, or 0 at rates 72 and 136
   S.a18 ^^^ lane 18,   -- S[3, 3] ^ bytes 144 to 151 of P_i, or 0 at rates 72 and 136
   S.a19 ^^^ lane 19,   -- S[4, 3] ^ bytes 152 to 159 of P_i, or 0 at rates 72 and 136
   -- y = 4
   S.a20 ^^^ lane 20,   -- S[0, 4] ^ bytes 160 to 167 of P_i, or 0 at rates 72 and 136
   S.a21 ^^^ lane 21,   -- S[1, 4] ^ bytes 168 to 175 of P_i, or 0 at rates 72 and 136
   S.a22 ^^^ lane 22,   -- S[2, 4] ^ bytes 176 to 183 of P_i, or 0 at rates 72 and 136
   S.a23 ^^^ lane 23,   -- S[3, 4] ^ bytes 184 to 191 of P_i, or 0 at rates 72 and 136
   S.a24 ^^^ lane 24⟩   -- S[4, 4] ^ bytes 192 to 199 of P_i, or 0 at rates 72 and 136

/-- XOR the byte `b` into the state, at byte `p` of the block, if its lane is in the rate.

Byte `p` is byte `p mod 8` of lane `p / 8`, so `b` is shifted up by `8 * (p mod 8)` bits.

A byte whose lane is not wholly in the rate is not absorbed, as in a block.

At a rate that is a multiple of 8 bytes, every byte below the rate is absorbed. -/
def xorBlockByte (rate : Nat) (S : State) (p : Nat) (b : UInt8) : State :=
  if 8 * (p / 8) + 8 ≤ rate then S.xorLane (p / 8) (b.toUInt64 <<< (8 * (p % 8)).toUInt64)
  else S

/-- The output of FIPS 202 §4, Algorithm 8, steps 7 to 9, for `d = 256` bits.

The digest is `Trunc_256(S)`, lanes 0 to 3 of the state. -/
@[inline] def squeezeLanes256 (S : State) : Lanes4 :=
  -- Step 7: let Z be the empty string.
  --
  -- Step 8: let Z = Z || Trunc_r(S).
  --
  -- Step 9: if d ≤ |Z|, then return Trunc_d(Z); else continue.
  --
  -- Here d = 256 ≤ r = 1088, so step 9 returns at once, and step 10 never runs.
  --
  -- By FIPS 202 §3.1.2, lane (x, 0) holds bits 64x to 64x + 63 of S.
  --
  -- So lanes 0 to 3 hold bits 0 to 255.
  --
  -- Lanes S[0, 0], S[1, 0], S[2, 0] and S[3, 0]: bits 0 to 255 of S.
  ⟨S.a0, S.a1, S.a2, S.a3⟩

/-- The output of FIPS 202 §4, Algorithm 8, steps 7 to 9, for `d = 256` bits, as bytes.

It is the 32 bytes of lanes 0 to 3, least significant byte first. -/
def squeeze256 (S : State) : Vector UInt8 DIGEST_LEN_256 :=
  (squeezeLanes256 S).bytes

/-- The output of FIPS 202 §4, Algorithm 8, steps 7 to 9, for `d = 512` bits.

The digest is `Trunc_512(S)`, the 64 bytes of lanes 0 to 7, least significant byte first. -/
def squeeze512 (S : State) : Vector UInt8 DIGEST_LEN_512 :=
  -- Step 7: let Z be the empty string.
  --
  -- Step 8: let Z = Z || Trunc_r(S).
  --
  -- Step 9: if d ≤ |Z|, then return Trunc_d(Z); else continue.
  --
  -- Here d = 512 ≤ r = 576, so step 9 returns at once, and step 10 never runs.
  --
  -- Byte j of a lane is its bits 8j to 8j + 7, so the lane shifted down by 8j.
  let b (v : UInt64) (j : UInt64) : UInt8 := (v >>> (8 * j)).toUInt8
  #v[-- Bytes 0 to 7 of Z: lane S[0, 0], bits 0 to 63 of S
    b S.a0 0, b S.a0 1, b S.a0 2, b S.a0 3, b S.a0 4, b S.a0 5, b S.a0 6, b S.a0 7,
    -- Bytes 8 to 15 of Z: lane S[1, 0], bits 64 to 127 of S
    b S.a1 0, b S.a1 1, b S.a1 2, b S.a1 3, b S.a1 4, b S.a1 5, b S.a1 6, b S.a1 7,
    -- Bytes 16 to 23 of Z: lane S[2, 0], bits 128 to 191 of S
    b S.a2 0, b S.a2 1, b S.a2 2, b S.a2 3, b S.a2 4, b S.a2 5, b S.a2 6, b S.a2 7,
    -- Bytes 24 to 31 of Z: lane S[3, 0], bits 192 to 255 of S
    b S.a3 0, b S.a3 1, b S.a3 2, b S.a3 3, b S.a3 4, b S.a3 5, b S.a3 6, b S.a3 7,
    -- Bytes 32 to 39 of Z: lane S[4, 0], bits 256 to 319 of S
    b S.a4 0, b S.a4 1, b S.a4 2, b S.a4 3, b S.a4 4, b S.a4 5, b S.a4 6, b S.a4 7,
    -- Bytes 40 to 47 of Z: lane S[0, 1], bits 320 to 383 of S
    b S.a5 0, b S.a5 1, b S.a5 2, b S.a5 3, b S.a5 4, b S.a5 5, b S.a5 6, b S.a5 7,
    -- Bytes 48 to 55 of Z: lane S[1, 1], bits 384 to 447 of S
    b S.a6 0, b S.a6 1, b S.a6 2, b S.a6 3, b S.a6 4, b S.a6 5, b S.a6 6, b S.a6 7,
    -- Bytes 56 to 63 of Z: lane S[2, 1], bits 448 to 511 of S
    b S.a7 0, b S.a7 1, b S.a7 2, b S.a7 3, b S.a7 4, b S.a7 5, b S.a7 6, b S.a7 7]

/-- Absorb `n` blocks of `rate` bytes from index `start` on, in order, one permutation each.

This is FIPS 202 §4, Algorithm 8, step 6.

The blocks are read in place, so a long message is never copied block by block. -/
@[specialize] def absorbBlocks (f : State → State) (rate : Nat) (read : Nat → UInt64) :
    Nat → Nat → State → State
  | 0, _, S => S
  | n + 1, start, S =>
    absorbBlocks f rate read n (start + rate) (f (absorbBlock rate S read start))

end Internal

/-- The 16 bytes at an offset of a buffer, as two lanes; bytes past its end read as zero. -/
def Lanes2.read (bytes : ByteArray) (offset : Nat) : Lanes2 :=
  ⟨Internal.laneAt bytes offset, Internal.laneAt bytes (offset + 8)⟩

/-- The 32 bytes at an offset of a buffer, as four lanes; bytes past its end read as zero. -/
def Lanes4.read (bytes : ByteArray) (offset : Nat) : Lanes4 :=
  ⟨Internal.laneAt bytes offset, Internal.laneAt bytes (offset + 8),
    Internal.laneAt bytes (offset + 16), Internal.laneAt bytes (offset + 24)⟩

/-- Steps 1 to 6 of FIPS 202 §4, Algorithm 8, except that the last block is XORed in, not permuted.

The rate must be positive, below 200 bytes and a multiple of 8 bytes, as for the absorbing phase.

The message `N` has `len` bytes, and `read p` is its lane of bytes `p` to `p + 7`, for `8 ∣ p`.

Its bytes from `len` on must read as zero, as `P` holds the padding there. -/
@[specialize] def Internal.stateBeforeLastPermutation (f : State → State) (rate len : Nat)
    (read : Nat → UInt64) : State :=
  -- This is the absorbing phase up to its last permutation.
  --
  -- The state after the absorbing phase is f of this state.
  --
  -- A caller that hashes many messages differing only in their last block can share all the rest.
  --
  -- There are n - 1 = len(N) / r blocks before the last one, since n = len(N) / r + 1.
  --
  -- Steps 1 and 2: the k = n - 1 blocks of P = N || pad(r, len(N)) before the last are in N.
  let k := len / rate
  -- Steps 3 to 6 for i < n - 1: from S = 0^b, S = f(S ^ (P_i || 0^c)), with P_i read from N.
  let S := Internal.absorbBlocks f rate read k 0 State.zero
  -- The last block gives S ^ (P_{n-1} || 0^c), with no permutation after it.
  --
  -- The last block P_{n-1} starts with the rest of N, read in place; bytes past N read as zero.
  let S := Internal.absorbBlock rate S read (rate * k)
  -- The first 1 bit of the padding is bit 0 of byte len(N) mod r of the last block.
  let S := Internal.xorBlockByte rate S (len % rate) 0x01
  -- The final 1 bit is bit 7 of byte r - 1; with one padding byte, both bits share it.
  Internal.xorBlockByte rate S (rate - 1) 0x80

/-- The absorbing phase, FIPS 202 §4, Algorithm 8, steps 1 to 6, at a rate of `rate` bytes.

The rate must be positive and below 200 bytes: FIPS 202 §4 asks `0 < r < b`, and no other.

It must also be a multiple of 8 bytes, so that each lane lies wholly in `P_i` or in `0^c`.

The message `N` has `len` bytes, read a lane at a time, with zero bytes from `len` on. -/
@[specialize] def Internal.spongeAbsorb (f : State → State) (rate len : Nat)
    (read : Nat → UInt64) : State :=
  -- FIPS 202 §4 defines the sponge for any permutation f, so the permutation is an argument.
  --
  -- Here N is the message, b = 1600, and pad is pad10*1.
  --
  -- Step 1: let P = N || pad(r, len(N)).
  --
  -- Step 2: let n = len(P) / r.
  --
  -- Step 3: let c = b - r.
  --
  -- Step 4: let P_0, ..., P_{n-1} be the unique strings of length r with P = P_0 || ... || P_{n-1}.
  --
  -- Step 5: let S = 0^b.
  --
  -- Step 6: for i from 0 to n - 1, let S = f(S ^ (P_i || 0^c)).
  --
  -- The absorbing phase ends with the last permutation of step 6.
  --
  -- So it is that permutation applied to the state just before it.
  --
  -- Steps 1 to 6, up to the last block XORed in, then the last application of f.
  f (Internal.stateBeforeLastPermutation f rate len read)

/-- Keccak-256 of a message read a lane at a time, `KECCAK[512](N, 256)` of FIPS 202 §5.2.

The message has `len` bytes, and `read p` is its lane of bytes `p` to `p + 7`, for `8 ∣ p`.

Its bytes from `len` on must read as zero.

A reader that breaks those conditions gives no Keccak-256 digest, so this is internal. -/
@[inline] def Internal.keccak256Read (len : Nat) (read : Nat → UInt64) : Lanes4 :=
  -- KECCAK[c](N, d) = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 - c](N, d).
  --
  -- So c = 512, d = 256, and r = 1600 - c = 1088 bits, that is 136 bytes.
  --
  -- Unlike SHA3-256 of §6.1, the message N gets no 01 suffix before the padding.
  --
  -- Algorithm 8, steps 1 to 6: absorb N at r = 136 bytes, with f = KECCAK-p[1600, 24].
  --
  -- Steps 7 to 9: the digest is Trunc_256(S), as d = 256 ≤ r = 1088.
  --
  -- The digest is the four lanes of Trunc_256(S): lanes 0 to 3, bits 0 to 255 of the state.
  Internal.squeezeLanes256 (Internal.spongeAbsorb keccakF RATE_256 len read)

/-- Keccak-256 of a string of lanes: the message of 8 bytes a lane, and its digest as lanes.

The sponge reads its message a lane at a time, so a message held as lanes moves no byte. -/
@[inline] def keccak256Lanes (lanes : Array UInt64) : Lanes4 :=
  Internal.keccak256Read (8 * lanes.size) (Internal.laneOfArray lanes)

/-- Keccak-256 of a byte string, `KECCAK[512](N, 256)` of FIPS 202 §5.2.

The bytes are read a lane at a time, and the digest's lanes are written back as bytes. -/
def keccak256 (msg : ByteArray) : Vector UInt8 DIGEST_LEN_256 :=
  (Internal.keccak256Read msg.size (Internal.laneAt msg)).bytes

/-- Keccak-512 of a byte string, `KECCAK[1024](N, 512)` of FIPS 202 §5.2:

`KECCAK[c](N, d) = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600 - c](N, d)`

So `c = 1024`, `d = 512`, and `r = 1600 - c = 576` bits, that is 72 bytes.

Unlike SHA3-512 of §6.1, the message `N` gets no `01` suffix before the padding. -/
def keccak512 (msg : ByteArray) : Vector UInt8 DIGEST_LEN_512 :=
  -- Algorithm 8, steps 1 to 6: absorb N at r = 72 bytes, with f = KECCAK-p[1600, 24].
  --
  -- Steps 7 to 9: the digest is Trunc_512(S), as d = 512 ≤ r = 576.
  Internal.squeeze512 (Internal.spongeAbsorb keccakF RATE_512 msg.size (Internal.laneAt msg))

/-! ## Incremental hashing

A hasher absorbs a message in pieces, for a digest of all the pieces so far.

It keeps the state after the whole blocks, and the bytes of the block not yet full.

The digest pads those bytes and absorbs the last block, without changing the hasher. -/

/-- A Keccak-256 hasher: the state after the whole blocks so far, and the bytes after them. -/
structure Hasher256 where
  /-- The state after every whole block so far. -/
  state : State
  /-- The bytes after the last whole block, fewer than the rate. -/
  pending : ByteArray

namespace Hasher256

/-- The hasher of the empty message. -/
def empty : Hasher256 := ⟨State.zero, .empty⟩

/-- Absorb more bytes: FIPS 202 §4, Algorithm 8, step 6, on every block they complete.

Each whole block of `pending || data` goes through `S = f(S ^ (P_i || 0^c))`.

The rest, fewer than `r` bytes, waits for more bytes or for the digest.-/
def absorb (h : Hasher256) (data : ByteArray) : Hasher256 :=
  -- The bytes not yet absorbed: the previous rest, then the new data.
  let bytes := h.pending ++ data
  -- The number of whole blocks of r = 136 bytes among them.
  let count := bytes.size / RATE_256
  -- Step 6 on each whole block: S = f(S ^ (P_i || 0^c)).
  ⟨Internal.absorbBlocks keccakF RATE_256 (Internal.laneAt bytes) count 0 h.state,
    -- The rest, fewer than r bytes, waits.
    bytes.extract (RATE_256 * count) bytes.size⟩

/-- The Keccak-256 digest of every byte absorbed so far, FIPS 202 §4, Algorithm 8.

The hasher is not changed, so more bytes can still be absorbed after a digest. -/
def digest (h : Hasher256) : Vector UInt8 DIGEST_LEN_256 :=
  -- Step 1: the pending bytes followed by pad10*1 make the last block of P.
  --
  -- pad(r, len(N)) reads len(N) only mod r, which is the pending length.
  --
  -- The pending bytes are fewer than r, so the padding fills exactly one block.
  let last := h.pending ++ padding RATE_256 h.pending.size
  -- Step 6: that block goes through S = f(S ^ (P_{n-1} || 0^c)).
  --
  -- Steps 7 to 9: the digest is Trunc_256(S).
  Internal.squeeze256 (Internal.absorbBlocks keccakF RATE_256 (Internal.laneAt last) 1 0 h.state)

end Hasher256

end EthLib.Cryptography.Hash.Keccak

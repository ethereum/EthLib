/-!
# `Hash.Keccak`

The Keccak-f[1600] permutation, as specified by FIPS 202.

FIPS 202 §3.4 defines Keccak-f[1600] as Keccak-p[1600, 24]: 24 rounds over a 1600-bit state.

It is written as a direct transcription of the standard, to be read against it.

It is not intended to be constant-time.
-/

namespace EthLib.Cryptography.Hash.Keccak

/-! ## The state

FIPS 202 §3.1.2 views the 1600-bit state as a 5 x 5 array of lanes, each of `w = 64` bits.

Lane `(x, y)` is stored at index `x + 5 * y`, so the 25 lanes run row by row:

```text
    index   0   1   2   3   4 |  5   6   7   8   9 | ... | 20  21  22  23  24
    (x, y) 00  10  20  30  40 | 01  11  21  31  41 | ... | 04  14  24  34  44
```

Bit `z` of a lane is bit `z` of its 64-bit word.

That is the standard's own order: bit `64 * (x + 5y) + z` of the state string is `A[x, y, z]` (§3.1.2).

So byte `k` of the state string is byte `k mod 8` of lane `k / 8`, least significant first (§3.1.3 and Appendix B.1).
-/

/-- Lanes in the state: 1600 bits of 64-bit lanes. -/
def LANES : Nat := 25

/-- Rounds in Keccak-f[1600].

FIPS 202 §3.4 sets `n_r = 12 + 2l`, with `l = 6` because `w = 2^6`. -/
def ROUNDS : Nat := 24

/-- The Keccak-f[1600] state: 25 lanes of 64 bits, lane `(x, y)` at index `x + 5 * y`. -/
abbrev State := Vector UInt64 LANES

/-- The all-zero state, where every sponge starts (FIPS 202 §4, Algorithm 8, step 5). -/
def State.zero : State := Vector.replicate LANES 0

/-- Lane `(x, y)` of the state, the coordinates taken mod 5 as in FIPS 202 §3.1.4.

So `x - 1` can be written `x + 4`, and `x + 1` needs no wrap of its own. -/
@[inline] def lane (A : State) (x y : Nat) : UInt64 :=
  -- Row `y mod 5` starts at index `5 * (y mod 5)`, and `x mod 5` counts along it.
  A[x % 5 + 5 * (y % 5)]'(by simp only [LANES]; omega)

/-- Rotate a lane towards its high bits by `n` positions, `n < 64`.

Bit `z` moves to bit `(z + n) mod 64`, which is what `rho` and `theta` ask of the bit index. -/
@[inline] def rotl (v : UInt64) (n : UInt64) : UInt64 :=
  -- The two shifts are disjoint and together move every bit once.
  -- At `n = 0` the right shift is by 64, which wraps to 0, and the result is still `v`.
  (v <<< n) ||| (v >>> (64 - n))

/-! ## The constants

FIPS 202 does not list the round constants or the rotation offsets.

It defines them by two algorithms, transcribed here.

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

The theorem saying so is `roundConstants_eq` in `Proofs/Hash/Keccak.lean`. -/
def RC : Vector UInt64 ROUNDS := #v[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The rotation offset of each lane in rho, indexed like the state.

Each equals the offset FIPS 202 §3.2.2, Algorithm 2 assigns to its lane.

The theorem saying so is `rhoOffsets_eq` in `Proofs/Hash/Keccak.lean`.

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

The five step mappings of FIPS 202 §3.2, each on whole lanes.

Lane coordinates are taken mod 5, as the standard does (§3.1.4). -/

/-- Theta, FIPS 202 §3.2.1, Algorithm 1.

Each bit is XORed with the parities of two nearby columns.

```text
    C[x]       = A[x, 0] ^ A[x, 1] ^ A[x, 2] ^ A[x, 3] ^ A[x, 4]
    D[x]       = C[x - 1] ^ rot(C[x + 1], 1)
    A'[x, y]   = A[x, y] ^ D[x]
```
-/
def theta (A : State) : State :=
  -- Step 1: the parity of each column, one lane per x.
  let C : Vector UInt64 5 := Vector.ofFn fun x =>
    lane A x 0 ^^^ lane A x 1 ^^^ lane A x 2 ^^^ lane A x 3 ^^^ lane A x 4
  -- Step 2: x - 1 is x + 4 mod 5, and the bit shift z - 1 is a rotation by 1.
  let D : Vector UInt64 5 := Vector.ofFn fun x =>
    C[(x.val + 4) % 5]'(by omega) ^^^ rotl (C[(x.val + 1) % 5]'(by omega)) 1
  -- Step 3: lane x + 5y lies in column x, the index mod 5.
  Vector.ofFn fun i => A[i] ^^^ D[i.val % 5]'(by omega)

/-- Rho, FIPS 202 §3.2.2, Algorithm 2.

Each lane is rotated by its own offset. -/
def rho (A : State) : State :=
  Vector.ofFn fun i => rotl A[i] RHO[i]

/-- Pi, FIPS 202 §3.2.3, Algorithm 3.

The lanes are rearranged: `A'[x, y] = A[(x + 3y) mod 5, x]`. -/
def pi (A : State) : State :=
  -- The output lane at index i is lane (x, y) = (i mod 5, i / 5).
  Vector.ofFn fun i => lane A (i.val % 5 + 3 * (i.val / 5)) (i.val % 5)

/-- Chi, FIPS 202 §3.2.4, Algorithm 4.

The only nonlinear step: `A'[x, y] = A[x, y] ^ ((A[x + 1, y] ^ 1) & A[x + 2, y])`.

XOR with an all-ones lane is the complement. -/
def chi (A : State) : State :=
  -- Lane (x, y) at index i combines with the next two lanes of its row.
  Vector.ofFn fun i =>
    let x := i.val % 5
    let y := i.val / 5
    A[i] ^^^ (~~~lane A (x + 1) y &&& lane A (x + 2) y)

/-- Iota, FIPS 202 §3.2.5, Algorithm 6.

The round constant is XORed into lane `(0, 0)`, the only lane it touches. -/
def iota (ir : Fin ROUNDS) (A : State) : State :=
  A.set 0 (A[0] ^^^ RC[ir]) (by decide)

/-! ## The permutation -/

/-- One round, FIPS 202 §3.3: `Rnd(A, i_r) = iota(chi(pi(rho(theta(A)))), i_r)`. -/
def round (ir : Fin ROUNDS) (A : State) : State :=
  iota ir (chi (pi (rho (theta A))))

/-- Keccak-f[1600], FIPS 202 §3.4: Keccak-p[1600, 24], rounds 0 to 23 in order.

With `n_r = 24 = 12 + 2l` the rounds run from `12 + 2l - n_r = 0` to `23` (§3.3, Algorithm 7). -/
def keccakF (A : State) : State :=
  (List.finRange ROUNDS).foldl (fun A ir => round ir A) A

end EthLib.Cryptography.Hash.Keccak

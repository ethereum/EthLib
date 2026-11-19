module

public import EthLib.Cryptography.Hash.Keccak

/-!
# Keccak-f[1600] rounds on bits

The source is [FIPS 202](https://doi.org/10.6028/NIST.FIPS.202).

A state is 1600 bits, in the order of FIPS 202 §3.1.2.

Bit `z` of lane `i` sits at position `j = z + 64 i`, with `z < 64` the slice.

Lane `i = x + 5 y` lies in row `y = i / 5` and column `x = i % 5`.

That is the order of the lane state, whose field `a{x + 5y}` holds lane `(x, y)`.

The shift by `k` along a row moves `k` columns in the same row and keeps the slice:

```text
along(z + 64 i, k) = z + 64 (5 (i / 5) + (i % 5 + k) % 5)
```

Round `r` maps the bits `a` to the bits `a'`, with sums and products over GF(2):

```text
b     = L(a)
a'[j] = b[j] + (1 + b[along(j, 1)]) b[along(j, 2)] + [j < 64] RC[r]_j
```

Here `L` is theta, then rho, then pi (§3.2.1 to §3.2.3), and it is linear over GF(2).

The product term is chi (§3.2.4), and the last term is iota on lane 0 (§3.2.5).

The linear part reuses the lane step mappings, and iota reuses the table of round constants.
-/

@[expose] public section

namespace EthLib.Cryptography.LeanVm.KeccakGkr

open EthLib.Cryptography.Hash

/-- A bit position of the state: `j = z + 64 i`, slice `z`, lane `i`. -/
abbrev Pos := Fin 1600

/-- The 25 lanes of a state, lane `x + 5y` at index `x + 5y`. -/
def stateLanes (A : Keccak.State) : Vector UInt64 25 :=
  #v[A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, A.a6, A.a7, A.a8, A.a9, A.a10, A.a11, A.a12, A.a13,
    A.a14, A.a15, A.a16, A.a17, A.a18, A.a19, A.a20, A.a21, A.a22, A.a23, A.a24]

/-- The state with these lanes. -/
def stateOfLanes (v : Vector UInt64 25) : Keccak.State :=
  ⟨v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], v[12], v[13],
    v[14], v[15], v[16], v[17], v[18], v[19], v[20], v[21], v[22], v[23], v[24]⟩

/-- The bit at position `j`: bit `j % 64` of lane `j / 64`. -/
def bitsOf (A : Keccak.State) : Pos → Bool := fun j =>
  ((stateLanes A)[j.val / 64]'(by omega)).toBitVec.getLsbD (j.val % 64)

/-- The state whose bit `j` is `a j`. -/
def ofBits (a : Pos → Bool) : Keccak.State :=
  stateOfLanes (Vector.ofFn fun i : Fin 25 =>
    Fin.foldl 64 (fun lane z =>
      if a ⟨z.val + 64 * i.val, by omega⟩ then lane ||| (1 <<< z.val.toUInt64) else lane) 0)

/-- The position `k` columns along from `j`, same row and slice. -/
def along (j : Pos) (k : Fin 5) : Pos :=
  ⟨j.val % 64 + 64 * (5 * (j.val / 64 / 5) + (j.val / 64 % 5 + k.val) % 5), by omega⟩

/-- The linear part of a round on bits, `pi (rho (theta a))`, through EthLib's lane functions. -/
def linearBits (a : Pos → Bool) : Pos → Bool :=
  bitsOf (Keccak.pi (Keccak.rho (Keccak.theta (ofBits a))))

/-- Round `r`: the linear part, then chi written with `along`, then iota on lane 0. -/
def roundBits (r : Fin Keccak.ROUNDS) (a : Pos → Bool) : Pos → Bool := fun j =>
  let b := linearBits a
  b j ^^ (!b (along j 1) && b (along j 2)) ^^
    (j.val < 64 && ((Keccak.RC[r] >>> j.val.toUInt64) &&& 1) == 1)

/-- Rounds `r0, ..., r0 + n - 1` in order.

A round index past 23 leaves the bits unchanged. -/
def roundsBits (r0 n : Nat) (a : Pos → Bool) : Pos → Bool :=
  match n with
  | 0 => a
  | n + 1 => roundsBits (r0 + 1) n (if h : r0 < 24 then roundBits ⟨r0, h⟩ a else a)

end EthLib.Cryptography.LeanVm.KeccakGkr

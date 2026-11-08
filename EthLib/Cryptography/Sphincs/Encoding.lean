module

public import EthLib.Cryptography.Sphincs.TweakableHash

/-!
# The WOTS+C target-sum code

The target-sum code of WOTS+C (ePrint 2022/778).

A 16-byte digest `D` has 64 digits of 2 bits each, read most significant first:

```text
    x = base_2b(D, w, v),   x_i = floor(D_{floor(i / 4)} / 2^(6 - 2 (i mod 4))) mod 4
```

`D_j` is byte `j` of `D`, so digit 0 is the top two bits of byte 0.

`D` is a codeword when its 64 digits sum to `T = 128`.

Two distinct codewords are incomparable: each has a digit smaller than the other's.

So the chain values revealed for one codeword never sign another.

This replaces the Winternitz checksum.

Source: WOTS+C with target sum 128 of [leanSPHINCS.tex][note] §1.

It reads `D` as the `base_2b` of [FIPS 205][fips205] does.

WOTS+C is [ePrint 2022/778][wotsc].

[note]: https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex
[fips205]: https://doi.org/10.6028/NIST.FIPS.205
[wotsc]: https://eprint.iacr.org/2022/778
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

namespace Internal

/-- The 64 digits of a digest, codeword or not: `base_2b(D, w, v)` of FIPS 205 Algorithm 4.

Digit `i` is two bits of byte `floor(i / 4)`, the top two bits for `i mod 4 = 0`. -/
def digits (d : Digest) : Codeword :=
  -- Byte `floor(i / 4)` holds digits `4 floor(i / 4)` to `4 floor(i / 4) + 3`, the first on top.
  Vector.ofFn fun i =>
    ⟨((d[i.val / 4]'(by have := i.isLt; simp only [V, N] at *; omega)).toNat
        >>> (6 - 2 * (i.val % 4))) % 4, Nat.mod_lt _ (by decide)⟩

/-- The sum of the digits of a word. -/
def digitSum (x : Codeword) : Nat :=
  x.foldl (fun sum digit => sum + digit.val) 0

end Internal

/-- The codeword a digest is, as one position per chain.

Returns nothing when the digits do not sum to the target. -/
def codeword? (d : Digest) : Option Codeword :=
  let x := Internal.digits d
  if Internal.digitSum x == TARGET_SUM then some x else none

end EthLib.Cryptography.Sphincs

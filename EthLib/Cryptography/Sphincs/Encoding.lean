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

Source: the encoding of [main.tex][main] §3, which reads `D` as FIPS 205's `base_2b` does.

WOTS+C is [ePrint 2022/778][wotsc].

[main]: https://github.com/leanEthereum/leanVM/blob/5e3ade21d339a45e1b3b0dba97ad9300ab50e49b/doc/lean_sphincs/main.tex
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

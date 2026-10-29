import EthLib.Cryptography.Sphincs.TweakableHash

/-!
# `Sphincs.Encoding`

The target-sum code of WOTS+C (ePrint 2022/778).

A 16-byte digest `D` has 64 digits of 2 bits each:

```text
    x_i = floor(LE^-1(D) / 4^i) mod 4,   i < 64
```

`D` is a codeword when its 64 digits sum to `T = 128`.

Two distinct codewords are incomparable: each has a digit smaller than the other's.

So the chain values revealed for one codeword never sign another.

This replaces the Winternitz checksum.

Source: [ePrint 2022/778](https://eprint.iacr.org/2022/778) for WOTS+C, with `v = 64` and `T = 128` from [leanSPHINCS.tex](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/leanSPHINCS.tex) §1.

The digits follow `TargetSum.digestEncoding` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

namespace Internal

/-- The 64 digits of a digest, codeword or not. -/
def digits (d : Digest) : Codeword :=
  -- The digest is read once, as one 128-bit little-endian integer.
  let value := fromLittleEndian d
  -- Digit `i` is the base-4 digit of weight `4^i`: bits `2i` and `2i + 1`.
  Vector.ofFn fun i => ⟨value / 4 ^ i.val % CHAIN_LENGTH, Nat.mod_lt _ (by decide)⟩

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

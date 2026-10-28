import EthLib.Cryptography.Xmss.TweakableHash

/-!
# `Xmss.Encoding`

The target-sum code of WOTS+C (ePrint 2022/778).

A 16-byte digest `D` has 64 digits of 2 bits each:

```text
    x_i = floor(LE^-1(D) / 4^i) mod 4,   i < 64
```

`D` is a codeword when its last 6 digits are zero and its first 58 sum to `T = 106`.

Two distinct codewords are incomparable: each has a digit smaller than the other's.

So the chain values revealed for one codeword never sign another.

This replaces the Winternitz checksum.

Source: the leanXMSS specification draft, section "WOTS+C", paragraph "Codewords".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

namespace Internal

/-- The 64 digits of a digest, codeword or not. -/
def digits (d : Digest) : Vector (Fin CHAIN_LENGTH) DIGITS :=
  -- The digest is read once, as one 128-bit little-endian integer.
  let value := fromLittleEndian d
  -- Digit `i` is the base-4 digit of weight `4^i`.
  Vector.ofFn fun i => ⟨value / 4 ^ i.val % CHAIN_LENGTH, Nat.mod_lt _ (by decide)⟩

/-- The sum of the digits of a one-time key's chains. -/
def digitSum (x : Vector (Fin CHAIN_LENGTH) V) : Nat :=
  x.foldl (fun sum digit => sum + digit.val) 0

end Internal

/-- The codeword a digest is, as the digits of its 58 chains.

Returns nothing when the digest is not a codeword. -/
def codeword? (d : Digest) : Option (Vector (Fin CHAIN_LENGTH) V) :=
  let x := Internal.digits d
  -- The first 58 digits name a position on each chain.
  let chains : Vector (Fin CHAIN_LENGTH) V :=
    Vector.ofFn fun i => x[i.val]'(by have := i.isLt; simp only [V, DIGITS] at *; omega)
  -- Digits 58 to 63 have no chain, so a codeword sets them to zero.
  let tailZero := (x.toList.drop V).all (·.val == 0)
  if tailZero && Internal.digitSum chains == TARGET_SUM then some chains else none

end EthLib.Cryptography.Xmss

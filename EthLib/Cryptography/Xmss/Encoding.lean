module

public import EthLib.Cryptography.Xmss.TweakableHash

/-!
# The leanXMSS target-sum code

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

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

namespace Internal

/-- Digit `i` of a digest: the base-4 digit of weight `4^i` of its little-endian integer.

Byte `floor(i / 4)` holds digit `i`, in its bits `2 (i mod 4)` and `2 (i mod 4) + 1`. -/
def digit (d : Digest) (i : Fin DIGITS) : Fin CHAIN_LENGTH :=
  let byte := d[i.val / 4]'(by have := i.isLt; simp only [DIGITS, DIGEST_LEN] at *; omega)
  ⟨byte.toNat >>> (2 * (i.val % 4)) % CHAIN_LENGTH, Nat.mod_lt _ (by decide)⟩

/-- The 64 digits of a digest, codeword or not. -/
def digits (d : Digest) : Vector (Fin CHAIN_LENGTH) DIGITS :=
  Vector.ofFn (digit d)

/-- The sum of the digits of a one-time key's chains. -/
def digitSum (x : Vector (Fin CHAIN_LENGTH) V) : Nat :=
  x.foldl (fun sum digit => sum + digit.val) 0

end Internal

/-- The codeword a digest is, as the digits of its 58 chains.

Returns nothing when the digest is not a codeword. -/
def codeword? (d : Digest) : Option (Vector (Fin CHAIN_LENGTH) V) :=
  -- Digits 58 to 63 have no chain, so a codeword sets them to zero.
  let tailZero := (List.finRange (DIGITS - V)).all fun j =>
    (Internal.digit d ⟨V + j.val, by have := j.isLt; simp only [V, DIGITS] at *; omega⟩).val == 0
  -- Most digests fail that test, so the other 58 digits are read only after it.
  if tailZero then
    let x := Internal.digits d
    -- The first 58 digits name a position on each chain.
    let chains : Vector (Fin CHAIN_LENGTH) V :=
      Vector.ofFn fun i => x[i.val]'(by have := i.isLt; simp only [V, DIGITS] at *; omega)
    if Internal.digitSum chains == TARGET_SUM then some chains else none
  else none

end EthLib.Cryptography.Xmss

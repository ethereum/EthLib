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

The integer is `lo + 2^64 hi` for the digest's two lanes.

So digit `i` is bits `2i` and `2i + 1` of the low lane for `i < 32`.

From `i = 32` on, it is bits `2 (i - 32)` and `2 (i - 32) + 1` of the high lane. -/
def digit (d : Digest) (i : Fin DIGITS) : Fin CHAIN_LENGTH :=
  let lane := if i.val < 32 then d.lo >>> (2 * i.val).toUInt64 else
    d.hi >>> (2 * (i.val - 32)).toUInt64
  ⟨(lane &&& 3).toNat, by
    -- Two bits are below 4.
    have : (lane &&& 3).toNat ≤ 3 := by
      rw [UInt64.toNat_and]; exact Nat.and_le_right
    simp only [CHAIN_LENGTH]
    omega⟩

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

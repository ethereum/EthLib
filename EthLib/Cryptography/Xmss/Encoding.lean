module

public import EthLib.Cryptography.Xmss.TweakableHash

/-!
# The leanXMSS target-sum code

The codewords a WOTS+C one-time key signs, read as 64 base-4 digits of a 16-byte digest.

Source: the leanXMSS specification draft, section "WOTS+C", paragraph "Codewords".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

namespace Internal

/-- Digit `i` of a digest `D`: `x_i = floor(LE^-1(D) / 4^i) mod 4`, for `i < 64`. -/
def digit (d : Digest) (i : Fin DIGITS) : Fin CHAIN_LENGTH :=
  -- `LE^-1(D) = lo + 2^64 hi`, so digits 0 to 31 are in `lo` and digits 32 to 63 in `hi`.
  let lane := if i.val < 32 then d.lo else d.hi
  -- Digit `i` is `floor(lane / 4^(i mod 32)) mod 4`: a shift by `2 (i mod 32)` bits, then `mod 4`.
  ⟨((lane >>> (2 * (i.val % 32)).toUInt64) % 4).toNat, by
    simp only [CHAIN_LENGTH, UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide)⟩

/-- The 64 digits of a digest, codeword or not. -/
def digits (d : Digest) : Vector (Fin CHAIN_LENGTH) DIGITS :=
  Vector.ofFn (digit d)

/-- The sum of the digits of a one-time key's chains. -/
def digitSum (x : Vector (Fin CHAIN_LENGTH) V) : Nat :=
  -- `sum_{i<v} x_i`, which a codeword sets to `T = 106`.
  x.foldl (fun sum digit => sum + digit.val) 0

end Internal

/-- The codeword a digest is, as the digits of its 58 chains.

Returns nothing when the digest is not a codeword.

We use the target-sum code of Construction 6 of [ePrint 2025/055][hbms], §5.2.

[hbms]: https://eprint.iacr.org/2025/055
-/
def codeword? (d : Digest) : Option (Vector (Fin CHAIN_LENGTH) V) :=
  -- It is a codeword when `x_v = ... = x_63 = 0` and `sum_{i<v} x_i = T`.
  --
  -- Digits 58 to 63 have no chain, so a codeword sets them to zero.
  -- Construction 6 hashes to exactly 58 digits, so it has no such test.
  let tailZero := (List.finRange (DIGITS - V)).all fun j =>
    (Internal.digit d ⟨V + j.val, by have := j.isLt; simp only [V, DIGITS] at *; omega⟩).val == 0
  -- Most digests fail that test, so the other 58 digits are read only after it.
  if tailZero then
    let x := Internal.digits d
    -- The first 58 digits name a position on each chain.
    let chains : Vector (Fin CHAIN_LENGTH) V :=
      Vector.ofFn fun i => x[i.val]'(by have := i.isLt; simp only [V, DIGITS] at *; omega)
    -- Two distinct codewords are incomparable: each has a digit smaller than the other's.
    --
    -- So the chain values revealed for one codeword never sign another.
    if Internal.digitSum chains == TARGET_SUM then some chains else none
  else none

end EthLib.Cryptography.Xmss

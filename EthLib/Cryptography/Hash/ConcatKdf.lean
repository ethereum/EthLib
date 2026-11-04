module

public import EthLib.Cryptography.Hash.Sha256

/-!
# The Concatenation KDF with SHA-256

[SP 800-56C Rev. 2](https://doi.org/10.6028/NIST.SP.800-56Cr2) §4.1 defines it, with `H = SHA-256`.

[SP 800-56A Rev. 3](https://doi.org/10.6028/NIST.SP.800-56Ar3) §5.8.2.1.1 gives its input format.

The output length is in bytes, so `L` is a multiple of eight bits.

The shared secret `Z` is secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.ConcatKdf

/-- The output length `H_outputBits` of SHA-256, in bytes. -/
def HASH_LEN : Nat := 32

/-- Every way the derivation can reject its input, SP 800-56C Rev. 2 §4.1. -/
inductive ConcatKdfError where
  /-- The requested length was zero, step 1. -/
  | emptyOutput
  /-- The output needed more than `2^32 - 1` blocks, step 2. -/
  | outputTooLong (length : Nat)
  /-- `counter | Z | FixedInfo` was longer than the `2^64 - 1` bits SHA-256 admits, step 4. -/
  | inputTooLong
deriving DecidableEq, Repr

/-- The counter as four big-endian bytes. -/
def counterBytes (counter : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (counter >>> 24), UInt8.ofNat (counter >>> 16), UInt8.ofNat (counter >>> 8),
    UInt8.ofNat counter]⟩

/-- The blocks `K(i)` to `K(i + count - 1)` of step 6, each `H(counter | Z | FixedInfo)`. -/
def blocks (z fixedInfo : ByteArray) (i : Nat) : (count : Nat) → ByteArray
  | 0 => ByteArray.empty
  | count + 1 => Sha256.hash (counterBytes i ++ z ++ fixedInfo) ++ blocks z fixedInfo (i + 1) count

/--
The first `length` bytes of `K(1) | K(2) | ...`, SP 800-56C Rev. 2 §4.1.

The shared secret is secret, and this function makes no constant-time claim.
-/
def concatKdf (z fixedInfo : ByteArray) (length : Nat) : Except ConcatKdfError ByteArray :=
  -- `reps = ceil(L / H_outputBits)` blocks cover the output.
  let reps := (length + HASH_LEN - 1) / HASH_LEN
  if length = 0 then .error .emptyOutput
  else if 2 ^ 32 - 1 < reps then .error (.outputTooLong length)
  -- More than `2^64 - 1` bits is at least `2^61` bytes.
  else if 2 ^ 61 ≤ 4 + z.size + fixedInfo.size then .error .inputTooLong
  else .ok ((blocks z fixedInfo 1 reps).extract 0 length)

end EthLib.Cryptography.Hash.ConcatKdf

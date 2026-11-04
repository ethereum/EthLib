module

/-!
# `Base.BigEndian`

Big-endian integers: a list of bytes read as a number, and a number written back as bytes.

Appendix H of the Yellow Paper reads a word this way.

The first byte is the most significant one:

```text
    [0x01, 0x00]  reads as  1 * 256 + 0 = 256
```
-/

@[expose] public section

namespace EthLib.Base

/-- The integer that the bytes write, the first byte the most significant.

An empty list reads as 0. -/
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `n` as exactly `len` big-endian bytes, keeping only `n mod 256 ^ len`.

A number that does not fit loses its higher bytes.

The bytes are exact whenever `n < 256 ^ len`. -/
def natToBytes : Nat → Nat → List UInt8
  | 0, _ => []
  -- The higher bytes first, then the lowest byte last.
  | len + 1, n => natToBytes len (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Writing on `len` bytes gives exactly `len` bytes. -/
theorem natToBytes_length (len n : Nat) : (natToBytes len n).length = len := by
  induction len generalizing n with
  | zero => simp [natToBytes]
  | succ len ih => simp [natToBytes, ih]

end EthLib.Base

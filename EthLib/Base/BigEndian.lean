module

/-!
# `Base.BigEndian`

Big-endian integers: a list of bytes read as a number, and a number written back as bytes.

Execution-specs reads and writes them with Python's `int.from_bytes(buffer, "big")` and `int.to_bytes(length, "big")`.

In both, the first byte is the most significant one:

```text
    [0x01, 0x00]  reads as  1 * 256 + 0 = 256
```
-/

@[expose] public section

namespace EthLib.Base

/-- `int.from_bytes(bytes, "big")`: the integer the bytes write, the first byte the most significant.

An empty list reads as 0. -/
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `n.to_bytes(len, "big")`: `n` as exactly `len` big-endian bytes, keeping only `n mod 256 ^ len`.

Python raises an `OverflowError` when `n` does not fit, where this definition drops the higher bytes.

The two agree whenever `n < 256 ^ len`. -/
def natToBytes : Nat → Nat → List UInt8
  | 0, _ => []
  -- The higher bytes first, then the lowest byte last.
  | len + 1, n => natToBytes len (n / 256) ++ [UInt8.ofNat (n % 256)]

end EthLib.Base

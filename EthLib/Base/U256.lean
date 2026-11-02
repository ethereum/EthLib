module

/-!
# `Base.U256`

The 256-bit unsigned integer, the word of the EVM.

Source: `U256` in [`numeric.py`](https://github.com/ethereum/ethereum-types/blob/611140497c635262ac949b3ba0b080818d9404ac/src/ethereum_types/numeric.py#L690) of ethereum-types `v0.4.1`, the version execution-specs uses at `2c0c8e7`.

A `U256` is a `BitVec 256`, so `+`, `-` and `*` wrap modulo 2^256, as `wrapping_add`, `wrapping_sub` and `wrapping_mul` do.

The signed instructions of the EVM read a word in two's complement:

```text
    to_signed(w) = w if w < 2^255, else w - 2^256
```
-/

@[expose] public section

namespace EthLib.Base

/-- An unsigned integer below 2^256. -/
abbrev U256 := BitVec 256

namespace U256

/-- `to_signed`: the integer that a word encodes in two's complement, in `[-2^255, 2^255)`. -/
def toSigned (w : U256) : Int :=
  if w.toNat < 2 ^ 255 then w.toNat else w.toNat - 2 ^ 256

/-- `from_signed`: the word that encodes an integer in two's complement.

The source raises outside `[-2^255, 2^255)`, where this definition reduces modulo 2^256.

The instructions pass it only integers inside that range. -/
def fromSigned (v : Int) : U256 := BitVec.ofInt 256 v

end U256

end EthLib.Base

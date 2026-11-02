module

public import EthLib.Base.U256

/-!
# `Evm.Instructions.Bitwise`

The bitwise instructions of the EVM, from AND to SAR.

Source: [`forks/constantinople/vm/instructions/bitwise.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/constantinople/vm/instructions/bitwise.py) of execution-specs at `2c0c8e7`.

AND to BYTE date from Frontier, and the shifts from Constantinople, as in [EIP-145](https://eips.ethereum.org/EIPS/eip-145).

Every later fork there computes the same results, up to Bogota.

Each function takes the operands in the order the instruction pops them.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base

/-- `bitwise_and`: the bitwise AND. -/
def bitwiseAnd (x y : U256) : U256 := x &&& y

/-- `bitwise_or`: the bitwise OR. -/
def bitwiseOr (x y : U256) : U256 := x ||| y

/-- `bitwise_xor`: the bitwise XOR. -/
def bitwiseXor (x y : U256) : U256 := x ^^^ y

/-- `bitwise_not`: the bitwise complement. -/
def bitwiseNot (x : U256) : U256 := ~~~x

/-- `get_byte`: byte `byteIndex` of `word`, counted from the most significant end, or 0 from index 32 on. -/
def getByte (byteIndex word : U256) : U256 :=
  if byteIndex.toNat ≥ 32 then
    0
  else
    -- Drop the bytes to the right of the one asked for, then the bytes to its left.
    (word >>> ((31 - byteIndex.toNat) * 8)) &&& 0xff

/-- `bitwise_shl`: `value` shifted left by `shift` bits, or 0 from 256 bits on. -/
def bitwiseShl (shift value : U256) : U256 :=
  if shift.toNat < 256 then value <<< shift.toNat else 0

/-- `bitwise_shr`: `value` shifted right by `shift` bits, or 0 from 256 bits on. -/
def bitwiseShr (shift value : U256) : U256 :=
  if shift.toNat < 256 then value >>> shift.toNat else 0

/-- `bitwise_sar`: `value` in two's complement, shifted right by `shift` bits and rounded down.

From 256 bits on, the result is 0 for a nonnegative value and -1 for a negative one. -/
def bitwiseSar (shift value : U256) : U256 :=
  let signedValue := U256.toSigned value
  if shift.toNat < 256 then
    -- Python's `>>` on an `int` rounds down, as `>>>` on an `Int` does.
    U256.fromSigned (signedValue >>> shift.toNat)
  else if signedValue ≥ 0 then
    0
  else
    BitVec.allOnes 256

end EthLib.Execution.Evm.Instructions

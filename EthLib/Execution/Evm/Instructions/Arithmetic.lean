module

public import EthLib.Base.U256
public import EthLib.Execution.Precompiles.Modexp.Core

/-!
# `Evm.Instructions.Arithmetic`

The arithmetic instructions of the EVM, from ADD to SIGNEXTEND.

Source: [`forks/frontier/vm/instructions/arithmetic.py`](https://github.com/ethereum/execution-specs/blob/2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1/src/ethereum/forks/frontier/vm/instructions/arithmetic.py) of execution-specs at `2c0c8e7`.

Every later fork there computes the same results, up to Bogota.

Each function takes the operands in the order the instruction pops them.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Instructions

open EthLib.Base

/-- `add`: the sum, modulo 2^256. -/
def add (x y : U256) : U256 := x + y

/-- `sub`: the difference, modulo 2^256. -/
def sub (x y : U256) : U256 := x - y

/-- `mul`: the product, modulo 2^256. -/
def mul (x y : U256) : U256 := x * y

/-- `div`: the quotient, rounded down, or 0 for a divisor of 0. -/
def div (dividend divisor : U256) : U256 :=
  if divisor = 0 then 0 else BitVec.ofNat 256 (dividend.toNat / divisor.toNat)

/-- `sdiv`: the signed quotient, rounded toward 0, or 0 for a divisor of 0.

The quotient of -2^255 by -1 is 2^255, one above the largest signed word, so the source returns -2^255. -/
def sdiv (x y : U256) : U256 :=
  -- The operands, read in two's complement.
  let dividend := U256.toSigned x
  let divisor := U256.toSigned y
  if divisor = 0 then
    0
  else if dividend = -2 ^ 255 ∧ divisor = -1 then
    U256.fromSigned (-2 ^ 255)
  else
    -- `get_sign(dividend * divisor) * (abs(dividend) // abs(divisor))`
    U256.fromSigned ((dividend * divisor).sign * (dividend.natAbs / divisor.natAbs : Nat))

/-- `mod`: the remainder, or 0 for a divisor of 0. -/
def mod (x y : U256) : U256 :=
  if y = 0 then 0 else BitVec.ofNat 256 (x.toNat % y.toNat)

/-- `smod`: the signed remainder, with the sign of the dividend, or 0 for a divisor of 0. -/
def smod (x y : U256) : U256 :=
  -- The operands, read in two's complement.
  let dividend := U256.toSigned x
  let divisor := U256.toSigned y
  if divisor = 0 then
    0
  else
    -- `get_sign(x) * (abs(x) % abs(y))`
    U256.fromSigned (dividend.sign * (dividend.natAbs % divisor.natAbs : Nat))

/-- `addmod`: the sum modulo `z`, without wrapping first, or 0 for `z = 0`. -/
def addmod (x y z : U256) : U256 :=
  if z = 0 then 0 else BitVec.ofNat 256 ((x.toNat + y.toNat) % z.toNat)

/-- `mulmod`: the product modulo `z`, without wrapping first, or 0 for `z = 0`. -/
def mulmod (x y z : U256) : U256 :=
  if z = 0 then 0 else BitVec.ofNat 256 ((x.toNat * y.toNat) % z.toNat)

/-- `exp`: the power, modulo 2^256.

Square-and-multiply keeps every step below 2^512, where `base^exponent` alone can have 2^264 bits. -/
def exp (base exponent : U256) : U256 :=
  BitVec.ofNat 256 (Precompiles.Modexp.powMod base.toNat exponent.toNat (2 ^ 256))

/-- `signextend`: the low `byteNum + 1` bytes of `value`, read as a signed integer and widened to 32 bytes.

A `byteNum` above 31 leaves `value` as it is. -/
def signextend (byteNum value : U256) : U256 :=
  if byteNum.toNat > 31 then
    value
  else
    -- The low bytes that the source keeps, as a number below `2^width`.
    let width := 8 * (byteNum.toNat + 1)
    let low := value.toNat % 2 ^ width
    -- Their top bit is the sign bit.
    if low < 2 ^ (width - 1) then
      BitVec.ofNat 256 low
    else
      -- The source prepends `0xff` bytes up to 32 bytes.
      BitVec.ofNat 256 (2 ^ 256 - 2 ^ width + low)

end EthLib.Execution.Evm.Instructions

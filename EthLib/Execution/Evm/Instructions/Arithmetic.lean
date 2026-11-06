module

public import EthLib.Base.U256
public import EthLib.Execution.Evm.PowMod

/-!
# `Evm.Instructions.Arithmetic`

The arithmetic instructions of the EVM, from ADD to SIGNEXTEND.

Source: Appendix H.2 of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

Every fork since Frontier computes the same results.

Each function takes the operands in the order the instruction pops them.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- The sum, modulo 2^256. -/
def add (x y : U256) : U256 := x + y

/-- The difference, modulo 2^256. -/
def sub (x y : U256) : U256 := x - y

/-- The product, modulo 2^256. -/
def mul (x y : U256) : U256 := x * y

/-- The quotient, rounded down, or 0 for a divisor of 0. -/
def div (dividend divisor : U256) : U256 :=
  if divisor = 0 then 0 else BitVec.ofNat 256 (dividend.toNat / divisor.toNat)

/-- The signed quotient, rounded toward 0, or 0 for a divisor of 0.

The quotient of -2^255 by -1 is 2^255, one above the largest signed word.

So the Yellow Paper gives -2^255. -/
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

/-- The remainder, or 0 for a divisor of 0. -/
def mod (x y : U256) : U256 :=
  if y = 0 then 0 else BitVec.ofNat 256 (x.toNat % y.toNat)

/-- The signed remainder, with the sign of the dividend, or 0 for a divisor of 0. -/
def smod (x y : U256) : U256 :=
  -- The operands, read in two's complement.
  let dividend := U256.toSigned x
  let divisor := U256.toSigned y
  if divisor = 0 then
    0
  else
    -- `get_sign(x) * (abs(x) % abs(y))`
    U256.fromSigned (dividend.sign * (dividend.natAbs % divisor.natAbs : Nat))

/-- The sum modulo `z`, without wrapping first, or 0 for `z = 0`. -/
def addmod (x y z : U256) : U256 :=
  if z = 0 then 0 else BitVec.ofNat 256 ((x.toNat + y.toNat) % z.toNat)

/-- The product modulo `z`, without wrapping first, or 0 for `z = 0`. -/
def mulmod (x y z : U256) : U256 :=
  if z = 0 then 0 else BitVec.ofNat 256 ((x.toNat * y.toNat) % z.toNat)

/-- The power, modulo 2^256.

Square-and-multiply keeps every step below 2^512.

The power `base^exponent` alone can have 2^264 bits. -/
def exp (base exponent : U256) : U256 :=
  BitVec.ofNat 256 (powMod base.toNat exponent.toNat (2 ^ 256))

/-- The low `byteNum + 1` bytes of `value`, read as a signed integer, widened to 32 bytes.

A `byteNum` above 31 leaves `value` as it is. -/
def signextend (byteNum value : U256) : U256 :=
  if byteNum.toNat > 31 then
    value
  else
    -- The low bytes that the result keeps, as a number below `2^width`.
    let width := 8 * (byteNum.toNat + 1)
    let low := value.toNat % 2 ^ width
    -- Their top bit is the sign bit.
    if low < 2 ^ (width - 1) then
      BitVec.ofNat 256 low
    else
      -- Every bit above the sign bit copies it, so the high bytes are all `0xff`.
      BitVec.ofNat 256 (2 ^ 256 - 2 ^ width + low)

end EthLib.Execution.Evm

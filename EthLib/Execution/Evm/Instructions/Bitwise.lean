module

public import EthLib.Base.U256

/-!
# `Evm.Instructions.Bitwise`

The bitwise instructions of the EVM, from AND to CLZ.

Source: Appendix H.2 of the Yellow Paper, Shanghai version, in `Paper.tex`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>.

The instructions date from these forks:

- AND to BYTE from Frontier
- the shifts from Constantinople, as in [EIP-145](https://eips.ethereum.org/EIPS/eip-145)
- CLZ from Fusaka, as in [EIP-7939](https://eips.ethereum.org/EIPS/eip-7939#specification)

Every later fork computes the same results.

Each function takes the operands in the order the instruction pops them.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- The bitwise AND, that AND pushes: `mu'_s[0]_i = mu_s[0]_i ∧ mu_s[1]_i` for each bit `i`. -/
def bitwiseAnd (x y : U256) : U256 := x &&& y

/-- The bitwise OR, that OR pushes: `mu'_s[0]_i = mu_s[0]_i ∨ mu_s[1]_i` for each bit `i`. -/
def bitwiseOr (x y : U256) : U256 := x ||| y

/-- The bitwise XOR, that XOR pushes: `mu'_s[0]_i = mu_s[0]_i ⊕ mu_s[1]_i` for each bit `i`. -/
def bitwiseXor (x y : U256) : U256 := x ^^^ y

/-- The bitwise complement, that NOT pushes: `mu'_s[0]_i = 1` if `mu_s[0]_i = 0`, else 0. -/
def bitwiseNot (x : U256) : U256 := ~~~x

/-- Byte `byteIndex` of `word`, from the most significant end, or 0 from index 32 on. -/
def getByte (byteIndex word : U256) : U256 :=
  -- BYTE: `mu'_s[0]_i = mu_s[1]_(i - 248 + 8 mu_s[0])` for `i ≥ 248` and `mu_s[0] < 32`.
  --
  -- Every other bit is 0, with the bits counted from the most significant.
  if byteIndex.toNat ≥ 32 then
    0
  else
    -- Drop the bytes to the right of the one asked for, then the bytes to its left.
    (word >>> ((31 - byteIndex.toNat) * 8)) &&& 0xff

/-- `value` shifted left by `shift` bits, or 0 from 256 bits on. -/
def bitwiseShl (shift value : U256) : U256 :=
  -- SHL, Appendix H.2: `mu'_s[0] = (mu_s[1] × 2^mu_s[0]) mod 2^256`, which is 0 from 256 bits on.
  if shift.toNat < 256 then value <<< shift.toNat else 0

/-- `value` shifted right by `shift` bits, or 0 from 256 bits on. -/
def bitwiseShr (shift value : U256) : U256 :=
  -- SHR, Appendix H.2: `mu'_s[0] = floor(mu_s[1] / 2^mu_s[0])`, which is 0 from 256 bits on.
  if shift.toNat < 256 then value >>> shift.toNat else 0

/-- `value` in two's complement, shifted right by `shift` bits and rounded down.

From 256 bits on, the result is 0 for a nonnegative value and -1 for a negative one. -/
def bitwiseSar (shift value : U256) : U256 :=
  -- SAR, Appendix H.2: `mu'_s[0] = floor(mu_s[1] / 2^mu_s[0])`.
  --
  -- Both `mu'_s[0]` and `mu_s[1]` are read in two's complement.
  let signedValue := U256.toSigned value
  if shift.toNat < 256 then
    -- The shift of an `Int` rounds toward negative infinity, as the sign fill of EIP-145 does.
    U256.fromSigned (signedValue >>> shift.toNat)
  -- From 256 bits on, the floor is 0 for a nonnegative value and -1 for a negative one.
  else if signedValue ≥ 0 then
    0
  else
    BitVec.allOnes 256

/-- The number of bits of `n` without its leading zeros, which is 0 for 0. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- The count of leading zeros: the zero bits of `x` above its highest one bit, or 256 for 0.

EIP-7939 defines it as 256 minus the bit length of `x`. -/
def countLeadingZeros (x : U256) : U256 := BitVec.ofNat 256 (256 - bitLength x.toNat)

end EthLib.Execution.Evm

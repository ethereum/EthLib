module

/-!
# `Base.Uint64`

Checked arithmetic on 64-bit unsigned integers.

A result of `2^64` or more is an overflow, and a result below zero is an underflow.

Each checked operation returns an error there, never a value that wraps.
-/

@[expose] public section

namespace EthLib.Base

/-- The reason that an operation on `UInt64` has no result. -/
inductive ArithError where
  /-- The result is `2^64` or more. -/
  | overflow
  /-- The result is below zero. -/
  | underflow
  /-- The divisor is zero. -/
  | divisionByZero
  deriving DecidableEq, Repr

namespace Uint64

/-- `a + b`, an overflow if the sum is `2^64` or more. -/
def addChecked (a b : UInt64) : Except ArithError UInt64 :=
  if a.toNat + b.toNat < 2 ^ 64 then .ok (a + b) else .error .overflow

/-- `a - b`, an underflow if `b > a`. -/
def subChecked (a b : UInt64) : Except ArithError UInt64 :=
  if b ≤ a then .ok (a - b) else .error .underflow

/-- `a * b`, an overflow if the product is `2^64` or more. -/
def mulChecked (a b : UInt64) : Except ArithError UInt64 :=
  if a.toNat * b.toNat < 2 ^ 64 then .ok (a * b) else .error .overflow

/-- `a / b`, the quotient rounded down, an error if `b = 0`. -/
def divChecked (a b : UInt64) : Except ArithError UInt64 :=
  if b = 0 then .error .divisionByZero else .ok (a / b)

/-- `n` as a 64-bit integer, an overflow if `n` is `2^64` or more. -/
def ofNatChecked (n : Nat) : Except ArithError UInt64 :=
  if h : n < 2 ^ 64 then .ok (UInt64.ofNatLT n h) else .error .overflow

/-- `a - b`, or 0 when `b ≥ a`. -/
def saturatingSub (a b : UInt64) : UInt64 :=
  if b < a then a - b else 0

/-- The integer square root: the largest `x` with `x^2 ≤ n`.

The root is taken on `Nat`, so no step can overflow, even at `n = 2^64 - 1`. -/
def integerSquareroot (n : UInt64) : UInt64 :=
  UInt64.ofNat n.toNat.sqrt

end Uint64

end EthLib.Base

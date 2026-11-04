module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Constants
public import Mathlib.Data.Nat.Sqrt

/-!
# Proofs: constants of the beacon chain

The integer square root of the largest 64-bit unsigned integer is the constant that names it.
-/

@[expose] public section

namespace EthLib.Consensus

open EthLib.Base.Uint64 (integerSquareroot toNat_integerSquareroot)

/-- The constant is the integer square root of `2^64 - 1`, since `2^64 - 1 = s^2 + 2s` for it. -/
theorem UINT64_MAX_SQRT_eq : UINT64_MAX_SQRT = integerSquareroot UINT64_MAX := by
  apply UInt64.toNat_inj.mp
  rw [toNat_integerSquareroot]
  have h : UINT64_MAX.toNat = 4294967295 * 4294967295 + 2 * 4294967295 := by decide
  rw [h, Nat.sqrt_add_eq 4294967295 (by omega)]
  rfl

end EthLib.Consensus

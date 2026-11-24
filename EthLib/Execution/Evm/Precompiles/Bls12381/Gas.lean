module

/-!
# `Evm.Precompiles.Bls12381.Gas`

The price of a multi-scalar multiplication of EIP-2537, on G1 or on G2.

Source: [EIP-2537, Gas schedule](https://eips.ethereum.org/EIPS/eip-2537#gas-schedule).
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

/-- `MULTIPLIER`: the discounts of the multi-scalar multiplications are in thousandths. -/
def MULTIPLIER : Nat := 1000

/-- The discount for `k` pairs, read from the table of a group, in thousandths. -/
@[inline] def msmDiscount (table : Vector Nat 128) (maxDiscount k : Nat) : Nat :=
  -- Entry `k - 1` of the table covers `1 <= k <= 128`.
  --
  -- The maximum discount applies for `k > 128`.
  if h : 0 < k ∧ k ≤ 128 then table[k - 1] else maxDiscount

/-- The price of `k` pairs: `k * c * discount / 1000`, rounded down.

Here `c` is the price of one multiplication in the group. -/
@[inline] def msmGas (mulGas : Nat) (table : Vector Nat 128) (maxDiscount k : Nat) : Nat :=
  -- EIP-2537: `floor(k * c * discount(k) / 1000)`.
  k * mulGas * msmDiscount table maxDiscount k / MULTIPLIER

end EthLib.Execution.Evm.Precompiles.Bls12381

module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Gas

/-!
# Proofs: `Evm.Precompiles.Bls12381.Gas`

The discount never raises the price of `k` pairs above that of `k` separate multiplications.

Past 128 pairs, the discount is the maximum discount of the group.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

/-- A discount is at most 1000 thousandths when every entry and the maximum discount are. -/
theorem msmDiscount_le {table : Vector Nat 128} {maxDiscount : Nat}
    (htable : ∀ i : Fin 128, table[i] ≤ MULTIPLIER) (hmax : maxDiscount ≤ MULTIPLIER) (k : Nat) :
    msmDiscount table maxDiscount k ≤ MULTIPLIER := by
  unfold msmDiscount
  split
  · exact htable ⟨k - 1, by omega⟩
  · exact hmax

/-- The price of `k` pairs is at most that of `k` multiplications.

This holds when every entry and the maximum discount are at most 1000 thousandths. -/
theorem msmGas_le {table : Vector Nat 128} {maxDiscount : Nat}
    (htable : ∀ i : Fin 128, table[i] ≤ MULTIPLIER) (hmax : maxDiscount ≤ MULTIPLIER)
    (mulGas k : Nat) : msmGas mulGas table maxDiscount k ≤ k * mulGas := by
  unfold msmGas
  -- Raise the discount to 1000 thousandths, then divide by 1000.
  calc k * mulGas * msmDiscount table maxDiscount k / MULTIPLIER
      ≤ k * mulGas * MULTIPLIER / MULTIPLIER :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ (msmDiscount_le htable hmax k))
    _ = k * mulGas := by simp [MULTIPLIER]

/-- Past 128 pairs, the discount is the maximum discount. -/
theorem msmDiscount_of_lt (table : Vector Nat 128) (maxDiscount : Nat) {k : Nat} (hk : 128 < k) :
    msmDiscount table maxDiscount k = maxDiscount := by
  simp [msmDiscount]
  omega

end EthLib.Execution.Evm.Precompiles.Bls12381

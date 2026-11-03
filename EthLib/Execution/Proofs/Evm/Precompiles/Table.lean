module

public import EthLib.Execution.Evm.Precompiles.Table

/-!
# Proofs: `Evm.Precompiles.Table`

- The table lists 18 distinct addresses.
- A call runs a precompile exactly when its address is in that list.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles

/-- There are 18 precompiles, at distinct addresses. -/
theorem addresses_length : ADDRESSES.length = 18 ∧ ADDRESSES.Nodup := by
  decide

/-- A call runs a precompile exactly when its address is one of the 18. -/
theorem run_isSome_iff (address : Nat) (data : ByteArray) (gas : Nat) :
    (run address data gas).isSome ↔ address ∈ ADDRESSES := by
  unfold run
  split <;> simp_all [ADDRESSES]

end EthLib.Execution.Evm.Precompiles

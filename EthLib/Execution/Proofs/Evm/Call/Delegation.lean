module

public import EthLib.Execution.Evm.Call.Delegation

/-!
# Proofs: the delegation indicator

The indicator of an address is a valid indicator, and it gives that address back.

Empty code is not an indicator, so an account without code delegates to nothing.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base

/-- An indicator has the size of a marker and an address. -/
theorem size_delegationIndicator (address : Address) :
    (delegationIndicator address).size = DELEGATION_SIZE := by
  rw [delegationIndicator, ByteArray.size_append]
  show 3 + address.toArray.size = 23
  simp

/-- The indicator of an address is a valid indicator. -/
theorem isValidDelegation_delegationIndicator (address : Address) :
    isValidDelegation (delegationIndicator address) = true := by
  simp only [isValidDelegation, size_delegationIndicator, Bool.and_eq_true, decide_eq_true_eq,
    true_and]
  exact ByteArray.extract_append_eq_left rfl

/-- The indicator of an address gives that address back. -/
theorem delegatedAddress_delegationIndicator (address : Address) :
    delegatedAddress (delegationIndicator address) = some address := by
  simp only [delegatedAddress, isValidDelegation_delegationIndicator, ↓reduceIte,
    Option.some.injEq]
  apply Vector.ext
  intro i hi
  have hlt : 3 + i < (delegationIndicator address).size := by
    rw [size_delegationIndicator, DELEGATION_SIZE]; omega
  rw [Vector.getElem_ofFn]
  show (delegationIndicator address)[3 + i]! = address[i]
  rw [getElem!_pos (delegationIndicator address) (3 + i) hlt]
  simp only [delegationIndicator]
  rw [ByteArray.getElem_append_right (by show 3 ≤ 3 + i; omega)]
  simp only [DELEGATION_MARKER, ByteArray.size, Array.size, List.length, Nat.add_sub_cancel_left]
  rfl

/-- Empty code is not a delegation indicator. -/
theorem isValidDelegation_empty : isValidDelegation .empty = false := by
  decide

end EthLib.Execution.Evm

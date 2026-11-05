module

public import EthLib.Execution.Evm.MessageCall

/-!
# Proofs: `Evm.MessageCall`

A message that fails leaves the writes of the transaction as they were before the message.

Only the record of the created accounts may differ.

A message that succeeds appends its logs to those of the caller and adds its refund.

A message that fails passes on no log, no refund and no account to delete.

Its touches stay undone, except at the precompile 0x03 from Spurious Dragon to Paris.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The same writes as a snapshot, apart from the record of the created accounts. -/
structure SameWrites (tx snapshot : TransactionState) : Prop where
  accountWrites : tx.accountWrites = snapshot.accountWrites
  storageWrites : tx.storageWrites = snapshot.storageWrites
  codeWrites : tx.codeWrites = snapshot.codeWrites
  storageClears : tx.storageClears = snapshot.storageClears
  transientStorage : tx.transientStorage = snapshot.transientStorage

/-- A map that succeeds succeeded on a value that it maps to its result. -/
theorem except_map_eq_ok {ε α β : Type} {f : α → β} {x : Except ε α} {y : β}
    (h : Except.map f x = .ok y) : ∃ a, x = .ok a ∧ f a = y := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, by simpa [Except.map] using h⟩

/-- A restored snapshot has the writes of the snapshot. -/
theorem sameWrites_restoreTxState (tx snapshot : TransactionState) :
    SameWrites (tx.restoreTxState snapshot) snapshot :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A message that fails leaves the writes of the transaction as they were before it. -/
theorem processMessage_sameWrites_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {evm : Evm fork Meter}
    {used : GasMeter.gasLeft evm.gas ≤ message.gas}
    (h : processMessage fork message state substate = .ok ⟨evm, used⟩)
    (failed : evm.error.isSome) : SameWrites evm.state state := by
  rw [processMessage] at h
  obtain ⟨ended, -, rolled⟩ := except_map_eq_ok h
  have hval := congrArg Subtype.val rolled
  simp only at hval
  subst hval
  unfold rollbackOnError at failed ⊢
  split
  · exact sameWrites_restoreTxState _ _
  · simp_all

/-- A message that succeeds appends its logs and adds its refund. -/
theorem incorporateChild_of_success {caller child : Evm fork Meter} (ok : child.error = none) :
    (incorporateChild fork caller child).substate.logs =
        caller.substate.logs ++ child.substate.logs ∧
      (incorporateChild fork caller child).substate.refundCounter =
        caller.substate.refundCounter + child.substate.refundCounter := by
  simp [incorporateChild, ok]

/-- A message that fails passes on no log, no refund, no account to delete and no access. -/
theorem incorporateChild_of_error {caller child : Evm fork Meter} (failed : child.error.isSome) :
    let after := incorporateChild fork caller child
    after.substate.logs = caller.substate.logs ∧
      after.substate.refundCounter = caller.substate.refundCounter ∧
      after.substate.accountsToDelete = caller.substate.accountsToDelete ∧
      after.substate.accessedAddresses = caller.substate.accessedAddresses ∧
      after.substate.accessedStorageKeys = caller.substate.accessedStorageKeys := by
  have : child.error.isNone = false := by cases h : child.error <;> simp_all
  simp [incorporateChild, this]

omit [GasMeter Meter] in
/-- Outside Spurious Dragon to Paris, a failed message leaves the touched accounts alone. -/
theorem touchedOnError_of_outside {caller child : Evm fork Meter}
    (outside : fork < .spuriousDragon ∨ .paris ≤ fork) :
    touchedOnError fork caller child = caller.substate.touchedAccounts := by
  unfold touchedOnError
  split
  · rename_i h
    obtain ⟨h1, h2, -⟩ := h
    exfalso
    revert h1 h2 outside
    cases fork <;> decide
  · rfl

end EthLib.Execution.Evm

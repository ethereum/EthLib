module

public import EthLib.Execution.Evm.Call.MessageCall
public import EthLib.Execution.Proofs.Evm.Interpreter

/-!
# Proofs: `Evm.Call.MessageCall`

A message that fails leaves the writes of the transaction as they were before the message.

Only the record of the created accounts may differ.

Its state is a rollback to the state it started from, which keeps the reads of its last frame.

A message that succeeds appends its logs to those of the caller and adds its refund.

A message that fails passes on no log, no refund and no account to delete.

Its touches stay undone, except at the precompile 0x03 from Spurious Dragon to Paris.

A message ends with no more execution gas than it was given.

From Glamsterdam, a revert rolls the state gas of the frame back to its baseline.

A message and a creation fail only with an error that aborts the run.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork bind_eq_error)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The same writes as a snapshot, apart from the record of the created accounts. -/
structure SameWrites (tx snapshot : TransactionState) : Prop where
  accountWrites : tx.accountWrites = snapshot.accountWrites
  storageWrites : tx.storageWrites = snapshot.storageWrites
  codeWrites : tx.codeWrites = snapshot.codeWrites
  storageClears : tx.storageClears = snapshot.storageClears
  transientStorage : tx.transientStorage = snapshot.transientStorage

/-- A restored snapshot has the writes of the snapshot. -/
theorem sameWrites_restoreTxState (tx snapshot : TransactionState) :
    SameWrites (tx.restoreTxState snapshot) snapshot :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A message that fails leaves the writes of the transaction as they were before it. -/
theorem processMessage_sameWrites_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {evm : Evm fork Meter}
    {used : GasMeter.gasHeld evm.gas ≤ message.gas}
    (h : processMessage fork message state substate = .ok ⟨evm, used⟩)
    (failed : evm.error.isSome) : SameWrites evm.state state := by
  rw [processMessage] at h
  obtain ⟨ended, -, rolled⟩ := Base.map_ok_iff.mp h
  have hval := congrArg Subtype.val rolled
  simp only at hval
  subst hval
  unfold rollbackOnError at failed ⊢
  split
  · exact sameWrites_restoreTxState _ _
  · simp_all

/-- A message that fails ends with a state that rolls back to the state it started from.

It is a rollback, so it keeps the reads of the state that it rolls back. -/
theorem processMessage_state_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {evm : Evm fork Meter}
    {used : GasMeter.gasHeld evm.gas ≤ message.gas}
    (h : processMessage fork message state substate = .ok ⟨evm, used⟩)
    (failed : evm.error.isSome) :
    ∃ ended : TransactionState, evm.state = ended.restoreTxState state := by
  rw [processMessage] at h
  obtain ⟨ended, -, rolled⟩ := Base.map_ok_iff.mp h
  have hval := congrArg Subtype.val rolled
  simp only at hval
  subst hval
  unfold rollbackOnError at failed ⊢
  split
  · exact ⟨_, rfl⟩
  · simp_all

/-- A message ends with at most the execution gas it was given. -/
theorem gasLeft_processMessage_le [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (_ : processMessage fork message state substate = .ok ended) :
    GasMeter.gasLeft ended.val.gas ≤ message.gas :=
  Nat.le_trans (LawfulGasMeter.gasLeft_le_gasHeld _) ended.property

/-- A creation ends with at most the execution gas it was given. -/
theorem gasLeft_processCreateMessage_le [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (_ : processCreateMessage fork message state substate = .ok ended) :
    GasMeter.gasLeft ended.val.gas ≤ message.gas :=
  Nat.le_trans (LawfulGasMeter.gasLeft_le_gasHeld _) ended.property

/-- From Glamsterdam, a message that reverts rolls its state gas back to the baseline.

The spill goes back to the execution gas, and the reservoir becomes the baseline. -/
theorem rollbackOnError_of_revert {snapshot : TransactionState} {evm : Evm fork StateGasMeter}
    (reverted : evm.error = some .revert) :
    (rollbackOnError snapshot evm).gas = evm.gas.restore := by
  simp [rollbackOnError, reverted, GasMeter.rollback]

/-- An exceptional halt keeps the meter it halted with: that meter has already rolled back. -/
theorem rollbackOnError_of_halt {snapshot : TransactionState} {evm : Evm fork Meter}
    {error : EvmError} (halted : evm.error = some error) (notRevert : error ≠ .revert) :
    (rollbackOnError snapshot evm).gas = evm.gas := by
  simp [rollbackOnError, halted, notRevert]

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

/-- An error of the state aborts the run. -/
private theorem aborts_of_mapError_state {α : Type} {x : Except State.StateError α}
    {e : EvmError} (h : x.mapError EvmError.state = .error e) : e.aborts = true := by
  cases x <;> simp [Except.mapError] at h
  subst h
  rfl

/-- A message and a creation fail only with an error that aborts the run.

It is the induction on the gas of the message, as the messages of its code have less gas. -/
theorem aborts_of_process_eq_error [LawfulGasMeter Meter] (n : Nat) :
    ∀ message : Message fork, message.gas = n →
      (∀ state substate (meter : Meter) held e,
        processMessage fork message state substate meter held = .error e → e.aborts = true) ∧
      ∀ state substate (meter : Meter) held e,
        processCreateMessage fork message state substate meter held = .error e →
          e.aborts = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro message hn
    -- The messages of its code have less gas, so they fail only with an error that aborts.
    have runner : ∀ (caller : Evm fork Meter) (child : Message fork)
        (lt : child.gas < message.gas) e, (match child.target with
          | some _ => processMessage (Meter := Meter) fork child caller.state caller.substate.child
          | none => processCreateMessage (Meter := Meter) fork child caller.state
            caller.substate.child) = .error e → e.aborts = true := by
      intro caller child lt e h
      split at h
      · exact (ih child.gas (hn ▸ lt) child rfl).1 _ _ _ _ _ h
      · exact (ih child.gas (hn ▸ lt) child rfl).2 _ _ _ _ _ h
    have call : ∀ state substate (meter : Meter) held e,
        processMessage fork message state substate meter held = .error e → e.aborts = true := by
      intro state substate meter held e h
      rw [processMessage] at h
      simp only [Except.map] at h
      split at h
      · rename_i hdo
        cases h
        split at hdo
        all_goals
          rcases bind_eq_error hdo with hm | ⟨state1, -, hdo⟩
          · first
              | exact aborts_of_mapError_state hm
              | cases hm
          · repeat' split at hdo
            all_goals first
              | (cases hdo; done)
              | (rename_i hrun; cases hdo; exact aborts_of_runFrame_eq_error runner hrun)
      · cases h
    refine ⟨call, fun state substate meter held e h => ?_⟩
    rw [processCreateMessage] at h
    rcases bind_eq_error h with hp | ⟨prepared, -, h⟩
    · unfold prepareCreation at hp
      split at hp
      · exact aborts_of_mapError_state hp
      · cases hp
    · rcases bind_eq_error h with hm | ⟨⟨evm, used⟩, -, h⟩
      · exact call _ _ _ _ _ hm
      · split at h
        split at h
        · rename_i hdep
          cases h
          unfold depositCode at hdep
          dsimp only at hdep
          repeat' split at hdep
          all_goals first
            | (cases hdep; done)
            | (rcases bind_eq_error hdep with hm | ⟨_, -, hdep⟩
               · exact aborts_of_mapError_state hm
               · cases hdep)
        · cases h

end EthLib.Execution.Evm

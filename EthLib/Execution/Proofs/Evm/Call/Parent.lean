module

public import EthLib.Execution.Proofs.Evm.Call.StepRules

/-!
# Proofs: every message keeps the block of the state

The block of a transaction state is the state before the block, with the writes of the block so far.

Every successful step of every frame keeps the block, at every fork, static frame or not.

A successful run of a frame keeps it too, under a runner of messages that keeps it.

Such a runner ends each message that succeeds with the block of the frame that sends it.

Every successful call and creation keeps the block, by induction on the gas of the message.

A rollback to a snapshot of the same block gives back the storage of the snapshot.

So a call that ends with an error leaves every storage word of every address as it was.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes of the state -/

/-- A successful move of the balance of a destroyed account keeps the block of the state. -/
theorem parent_selfdestructTransfer {tx tx' : TransactionState} {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.parent = tx.parent := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (TransactionState.parent_setAccountBalance h).trans
        (TransactionState.parent_moveEther h1)
    · cases h
      exact TransactionState.parent_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (TransactionState.parent_setAccountBalance h).trans
      (TransactionState.parent_createEther h1)

/-- A successful preparation of a creation keeps the block of the state. -/
theorem parent_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : tx'.parent = tx.parent := by
  unfold prepareCreation at h
  split at h
  · exact (TransactionState.parent_incrementNonce (Base.mapError_ok_iff.mp h) :)
  · cases h
    rfl

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps the block of the state. -/
theorem parent_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact parent_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-! ## A step -/

/-- Each write of a step keeps the block of the state, static frame or not. -/
theorem stepRules_parent :
    StepRules fork (fun a b : Evm fork Meter => b.state.parent = a.state.parent) where
  trans hab hbc := hbc.trans hab
  static h := h.parent
  sstore _ _ _ _ _ _ h := TransactionState.parent_setStorage h
  tstore _ _ _ _ := rfl
  log _ hs _ _ _ := by rw [hs]
  selfdestruct _ _ h := parent_finishSelfdestruct h
  incrementNonce _ _ _ h := TransactionState.parent_incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-- A result of a step from `evm` that keeps the block of the state.

The next frame has the block of `evm`.

A child is sent from a frame with the block of `evm`.

The frame that resumes has it too, when the frame that ends the child has the caller's block. -/
abbrev ParentResult (evm : Evm fork Meter) : StepResult fork Meter → Prop :=
  StepResult.Keeps (fun a b => b.state.parent = a.state.parent)
    (fun caller _ child => child.state.parent = caller.state.parent) evm

/-- Every successful step of every frame keeps the block of the state, static frame or not. -/
theorem parentResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : ParentResult evm result :=
  stepRules_parent.step h

/-! ## A run of a frame -/

/-- A runner of messages that keeps the block of the state.

It ends each message that it runs successfully with the block of the frame that sends it. -/
def KeepsParent {bound : Nat} (runChild : MessageRunner fork Meter bound) : Prop :=
  RunnerEnsures (fun caller _ child => child.state.parent = caller.state.parent) runChild

/-- A successful run of a frame keeps the block of the state.

The runner of its messages must keep the block. -/
theorem parent_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} (runs : KeepsParent runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.state.parent = evm.state.parent :=
  stepRules_parent.runFrame runs h

/-! ## Messages -/

/-- A successful deposit of code keeps the block of the frame that ends the init code. -/
theorem parent_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.state.parent = evm.state.parent := by
  rcases (depositCode_cases h).2.2 with hs | hs | hs
  · rw [hs]
    rfl
  · rw [hs]
  · exact TransactionState.parent_setCode hs

/-- The state that a message starts its frame from has the block of the state it is sent from. -/
theorem parent_startState (message : Message fork) (state : TransactionState) :
    (startState fork message state).parent = state.parent := by
  unfold startState
  split
  · exact TransactionState.parent_touchAccount _ _
  · rfl

/-- The state that a message enters has the block of the state it is sent from. -/
theorem parent_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    entry.parent = state.parent := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
  · exact parent_startState _ _
  · exact (TransactionState.parent_moveEther moved).trans (parent_startState _ _)

/-- The rollback of a frame keeps the block of that frame. -/
theorem parent_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    (rollbackOnError snapshot evm).state.parent = evm.state.parent := by
  unfold rollbackOnError
  split <;> rfl

/-- The rollback of a frame keeps the message of that frame. -/
theorem message_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    (rollbackOnError snapshot evm).message = evm.message := by
  unfold rollbackOnError
  split <;> rfl

/-- A call ends with the rollback of the frame that ends it, to the state it is sent from. -/
theorem exists_rollbackOnError_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ∃ last : Evm fork Meter, ended.val = rollbackOnError state last := by
  rw [processMessage] at h
  obtain ⟨ended0, -, rolled⟩ := Base.map_ok_iff.mp h
  have hval := congrArg Subtype.val rolled
  simp only at hval
  exact ⟨ended0.val, hval.symm⟩

/-- Every successful call and creation keeps the block of the state, at every fork.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_parent [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ended.val.state.parent = state.parent) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ended.val.state.parent = state.parent) :=
  stepRules_parent.processMessage
    (M := fun _ state _ _ ended => ended.state.parent = state.parent)
    (fun {message state _ _ _ _ _} hentry hrun => by
      rw [parent_rollbackOnError]
      exact hrun.trans (parent_entered hentry))
    (fun hp hm hd => (parent_depositCode hd).trans (hm.trans (parent_prepareCreation hp)))
    (fun h => h) n

/-- A successful call keeps the block of the state it is sent from, at every fork. -/
theorem parent_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ended.val.state.parent = state.parent :=
  (processMessage_parent message.gas).1 message state substate meter held rfl ended h

/-- A successful creation keeps the block of the state it is sent from, at every fork. -/
theorem parent_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    ended.val.state.parent = state.parent :=
  (processMessage_parent message.gas).2 message state substate meter held rfl ended h

/-- A call that ends with an error reads as the state it is sent from, at every address.

That holds for the account, every word of storage and every word of transient storage.

It holds at every fork, whatever the code of the message. -/
theorem processMessage_sameOutside_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (herr : ended.val.error.isSome = true) :
    TransactionState.SameOutside [] state ended.val.state := by
  have hp := parent_processMessage h
  obtain ⟨last, hl⟩ := exists_rollbackOnError_processMessage h
  rw [hl] at herr hp ⊢
  unfold rollbackOnError at herr hp ⊢
  split at herr
  · simp only [‹last.error.isSome = true›, ↓reduceIte] at hp ⊢
    exact TransactionState.sameOutside_restoreTxState hp
  · exact absurd herr ‹_›

/-- A call that ends with an error leaves every storage word as it was in the state it is sent from.

That holds at every fork, at every address, whatever the code of the message. -/
theorem getStorage_processMessage_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (herr : ended.val.error.isSome = true) (address : Address) (key : Bytes32) :
    ended.val.state.getStorage address key = state.getStorage address key :=
  (processMessage_sameOutside_of_error h herr address List.not_mem_nil).2.1 key

end EthLib.Execution.Evm

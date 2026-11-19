module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.State.CodeAvailability

/-!
# Proofs: every message keeps the code of each account available

The code of an account is available when the state holds the code under its code hash.

A step writes storage, moves a balance or raises a nonce, and each keeps every code hash.

So every step keeps the code of each account available, and so does a run of a frame.

A creation then stores its code under the hash that the account receives.

A rollback goes back to a snapshot with the same block, which held its codes.

Every call and creation then keeps the codes, by induction on the gas of the message.

The same holds for the accounts before the transaction, whose code hashes stay.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Transactions (HasCodes HasPreCodes hasCodes_createEther
  hasCodes_incrementNonce hasCodes_moveEther hasCodes_of_getCode hasCodes_restoreTxState
  hasCodes_setAccountBalance hasCodes_setCode hasCodes_setStorage hasCodes_touchAccount
  hasPreCodes_modifyState hasPreCodes_moveEther hasPreCodes_of_getCode hasPreCodes_restoreTxState
  hasPreCodes_setCode hasPreCodes_setStorage hasPreCodes_touchAccount)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes of the state -/

/-- A successful move of the balance of a destroyed account keeps the code of each account. -/
private theorem hasCodes_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') (available : HasCodes tx) :
    HasCodes tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact hasCodes_setAccountBalance h (hasCodes_moveEther h1 available)
    · cases h
      exact hasCodes_moveEther h1 available
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact hasCodes_setAccountBalance h (hasCodes_createEther h1 available)

/-- A successful move of the balance of a destroyed account keeps every pre-transaction code. -/
private theorem hasPreCodes_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx')
    (available : HasPreCodes tx) : HasPreCodes tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact hasPreCodes_modifyState h (hasPreCodes_moveEther h1 available)
    · cases h
      exact hasPreCodes_moveEther h1 available
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact hasPreCodes_modifyState h (hasPreCodes_modifyState h1 available)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps the code of each account available.

That holds for the accounts of the state and for those before the transaction. -/
private theorem hasCodes_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    (HasCodes evm.state → HasCodes after.state) ∧
      (HasPreCodes evm.state → HasPreCodes after.state) := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ⟨hasCodes_selfdestructTransfer (Base.mapError_ok_iff.mp hst),
      hasPreCodes_selfdestructTransfer (Base.mapError_ok_iff.mp hst)⟩

/-! ## A step -/

/-- Each part of a step keeps the block, and keeps the code of each account available.

That holds for the accounts of the state and for those before the transaction. -/
theorem stepRules_hasCodes :
    StepRules fork (fun a b : Evm fork Meter => b.state.parent = a.state.parent ∧
      (HasCodes a.state → HasCodes b.state) ∧ (HasPreCodes a.state → HasPreCodes b.state)) where
  trans hab hbc := ⟨hbc.1.trans hab.1, fun h => hbc.2.1 (hab.2.1 h), fun h => hbc.2.2 (hab.2.2 h)⟩
  static h := ⟨h.tracker.parent,
    hasCodes_of_getCode h.tracker.getCode fun address => .inl (by rw [getAccount_of_staticStep h]),
    hasPreCodes_of_getCode h.tracker.getCode h.tracker.parent⟩
  sstore _ _ _ _ _ _ h := ⟨TransactionState.parent_setStorage h, hasCodes_setStorage h,
    hasPreCodes_setStorage h⟩
  tstore _ _ _ _ := ⟨rfl, fun h => h, fun h => h⟩
  log _ hs _ _ _ := by
    rw [hs]
    exact ⟨rfl, fun h => h, fun h => h⟩
  selfdestruct _ _ h := ⟨parent_finishSelfdestruct h, hasCodes_finishSelfdestruct h⟩
  incrementNonce _ _ _ _ h := ⟨TransactionState.parent_incrementNonce h,
    hasCodes_incrementNonce h, hasPreCodes_modifyState h⟩
  incorporate h := by
    rw [state_incorporateChild]
    exact h

/-! ## Messages -/

/-- The state that a message enters keeps the code of each account of the state it is sent from.

That holds for the accounts of the state and for those before the transaction. -/
private theorem hasCodes_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    (HasCodes state → HasCodes entry) ∧ (HasPreCodes state → HasPreCodes entry) := by
  have start : (HasCodes state → HasCodes (startState fork message state)) ∧
      (HasPreCodes state → HasPreCodes (startState fork message state)) := by
    unfold startState
    split
    · exact ⟨hasCodes_touchAccount _, hasPreCodes_touchAccount _⟩
    · exact ⟨fun h => h, fun h => h⟩
  rcases h with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
  · exact start
  · exact ⟨fun h => hasCodes_moveEther moved (start.1 h),
      fun h => hasPreCodes_moveEther moved (start.2 h)⟩

/-- The preparation of a creation keeps the code of each account available.

That holds for the accounts of the state and for those before the transaction. -/
private theorem hasCodes_prepareCreation {state prepared : TransactionState} {address : Address}
    (h : prepareCreation fork state address = .ok prepared) :
    (HasCodes state → HasCodes prepared) ∧ (HasPreCodes state → HasPreCodes prepared) := by
  have marked : (HasCodes state →
      HasCodes ((state.destroyStorage address).markAccountCreated address)) ∧
      (HasPreCodes state →
        HasPreCodes ((state.destroyStorage address).markAccountCreated address)) :=
    ⟨hasCodes_of_getCode (fun _ => rfl) fun _ => .inl rfl,
      hasPreCodes_of_getCode (fun _ => rfl) rfl⟩
  unfold prepareCreation at h
  split at h
  · have hn := Base.mapError_ok_iff.mp h
    exact ⟨fun h => hasCodes_incrementNonce hn (marked.1 h),
      fun h => hasPreCodes_modifyState hn (marked.2 h)⟩
  · cases h
    exact marked

omit [GasMeter Meter] in
/-- A rollback to a snapshot of the same block keeps the block and the codes of the snapshot.

The frame must keep the codes of the snapshot too.

That holds for the accounts of the state and for those before the transaction. -/
private theorem hasCodes_rollback {snapshot after : TransactionState} {evm : Evm fork Meter}
    (parent : evm.state.parent = snapshot.parent)
    (h : after = evm.state.restoreTxState snapshot ∨ after = evm.state)
    (codes : HasCodes snapshot → HasCodes evm.state)
    (preCodes : HasPreCodes snapshot → HasPreCodes evm.state) :
    after.parent = snapshot.parent ∧ (HasCodes snapshot → HasCodes after) ∧
      (HasPreCodes snapshot → HasPreCodes after) := by
  rcases h with rfl | rfl
  · exact ⟨parent, hasCodes_restoreTxState parent, hasPreCodes_restoreTxState parent⟩
  · exact ⟨parent, codes, preCodes⟩

/-- Every successful call and creation keeps the code of each account available.

That holds for the accounts of the state and for those before the transaction, at every fork.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_hasCodes [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        (HasCodes state → HasCodes ended.val.state) ∧
          (HasPreCodes state → HasPreCodes ended.val.state)) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        (HasCodes state → HasCodes ended.val.state) ∧
          (HasPreCodes state → HasPreCodes ended.val.state)) := by
  have keeps := (stepRules_hasCodes (fork := fork) (Meter := Meter)).processMessage
    (M := fun _ state _ _ ended => ended.state.parent = state.parent ∧
      (HasCodes state → HasCodes ended.state) ∧ (HasPreCodes state → HasPreCodes ended.state))
    (fun {message state _ _ _ _ _} hentry hrun => by
      obtain ⟨codes, preCodes⟩ := hasCodes_entered hentry
      have parent := hrun.1.trans (parent_entered hentry)
      unfold rollbackOnError
      split
      · exact hasCodes_rollback parent (.inl rfl) (fun h => hrun.2.1 (codes h))
          (fun h => hrun.2.2 (preCodes h))
      · exact hasCodes_rollback parent (.inr rfl) (fun h => hrun.2.1 (codes h))
          (fun h => hrun.2.2 (preCodes h)))
    (fun {message state _ _ _ _ _} hp hm hd => by
      obtain ⟨codes, preCodes⟩ := hasCodes_prepareCreation hp
      have parent := hm.1.trans (parent_prepareCreation hp)
      rcases (depositCode_cases hd).2.2 with hs | hs | hs
      · exact hasCodes_rollback parent (.inl hs) (fun h => hm.2.1 (codes h))
          (fun h => hm.2.2 (preCodes h))
      · exact hasCodes_rollback parent (.inr hs) (fun h => hm.2.1 (codes h))
          (fun h => hm.2.2 (preCodes h))
      · exact ⟨(TransactionState.parent_setCode hs).trans parent,
          fun h => hasCodes_setCode hs (hm.2.1 (codes h)),
          fun h => hasPreCodes_setCode hs (hm.2.2 (preCodes h))⟩)
    (fun h => h) n
  exact ⟨fun message state substate meter held hn ended h =>
      (keeps.1 message state substate meter held hn ended h).2,
    fun message state substate meter held hn ended h =>
      (keeps.2 message state substate meter held hn ended h).2⟩

/-- A successful call keeps the code of each account available. -/
theorem hasCodes_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (available : HasCodes state) : HasCodes ended.val.state :=
  ((processMessage_hasCodes message.gas).1 message state substate meter held rfl ended h).1
    available

/-- A successful call keeps the code of each account before the transaction available. -/
theorem hasPreCodes_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (available : HasPreCodes state) : HasPreCodes ended.val.state :=
  ((processMessage_hasCodes message.gas).1 message state substate meter held rfl ended h).2
    available

/-- A successful creation keeps the code of each account available. -/
theorem hasCodes_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (available : HasCodes state) : HasCodes ended.val.state :=
  ((processMessage_hasCodes message.gas).2 message state substate meter held rfl ended h).1
    available

/-- A successful creation keeps the code of each account before the transaction available. -/
theorem hasPreCodes_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (available : HasPreCodes state) : HasPreCodes ended.val.state :=
  ((processMessage_hasCodes message.gas).2 message state substate meter held rfl ended h).2
    available

end EthLib.Execution.Evm

module

public import EthLib.Execution.Proofs.Evm.Call.StepRules

/-!
# Proofs: from Cancun, a message marks for deletion only accounts created in its transaction

From Cancun, SELFDESTRUCT marks its account for deletion only when its transaction created it.

[EIP-6780][e6780] sets this rule.

The created accounts of a transaction only grow.

A creation adds its address, and a rollback keeps them.

So an account counts as created here even when the frame that created it failed.

A child that succeeds passes its accounts to delete to its caller.

A child that fails passes none, and its caller keeps its own.

Take a call or creation that returns a frame, with or without an error.

Each account that frame marks for deletion was marked before the message started.

Otherwise the transaction has created it by the end of the message.

The deletions at the end of a transaction are not part of a message, so they are not covered here.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The relation -/

/-- Every account created in the first state is created in the second. -/
def CreatedLe (tx tx' : TransactionState) : Prop :=
  ∀ address ∈ tx.createdAccounts, address ∈ tx'.createdAccounts

/-- From `evm` to `after`, the created accounts only grow.

Each account that `after` marks for deletion was marked by `evm`.

Otherwise it is among the created accounts of `after`. -/
def DeletesCreated (evm after : Evm fork Meter) : Prop :=
  CreatedLe evm.state after.state ∧
    ∀ address ∈ after.substate.accountsToDelete,
      address ∈ evm.substate.accountsToDelete ∨ address ∈ after.state.createdAccounts

omit [GasMeter Meter] in
/-- Two related steps make one. -/
theorem DeletesCreated.trans {a b c : Evm fork Meter} (hab : DeletesCreated a b)
    (hbc : DeletesCreated b c) : DeletesCreated a c :=
  ⟨fun x h => hbc.1 x (hab.1 x h), fun x h => (hbc.2 x h).elim
    (fun hb => (hab.2 x hb).elim .inl fun hc => .inr (hbc.1 x hc)) .inr⟩

omit [GasMeter Meter] in
/-- A step that keeps the created accounts and the accounts to delete keeps the relation. -/
theorem DeletesCreated.of_eq {a b : Evm fork Meter}
    (created : b.state.createdAccounts = a.state.createdAccounts)
    (toDelete : b.substate.accountsToDelete = a.substate.accountsToDelete) :
    DeletesCreated a b :=
  ⟨fun _ h => created ▸ h, fun _ h => .inl (toDelete ▸ h)⟩

omit [GasMeter Meter] in
/-- A static step keeps the relation. -/
theorem DeletesCreated.of_staticStep {a b : Evm fork Meter} (h : StaticStep a b) :
    DeletesCreated a b :=
  of_eq h.created h.toDelete

/-! ## The writes of the state -/

/-- A successful move of the balance of SELFDESTRUCT keeps the created accounts. -/
theorem createdAccounts_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (TransactionState.createdAccounts_modifyState h).trans
        (TransactionState.createdAccounts_moveEther h1)
    · cases h
      exact TransactionState.createdAccounts_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (TransactionState.createdAccounts_modifyState h).trans
      (TransactionState.createdAccounts_modifyState h1)

/-! ## The frames that keep the relation -/

/-- Taking in a child that is related to the caller keeps the relation from the caller.

A child that succeeds passes its accounts to delete, and one that fails passes none. -/
theorem deletesCreated_incorporateChild {caller child : Evm fork Meter}
    (h : DeletesCreated caller child) :
    DeletesCreated caller (incorporateChild fork caller child) := by
  unfold incorporateChild
  split
  · refine ⟨h.1, fun x hx => ?_⟩
    rw [Std.ExtTreeSet.mem_insertMany_list] at hx
    rcases hx with hx | hx
    · exact .inl hx
    · exact h.2 x (by simpa using hx)
  · exact ⟨h.1, fun _ hx => .inl hx⟩

omit [GasMeter Meter] in
/-- From Cancun, the end of a successful SELFDESTRUCT keeps the relation.

It marks for deletion only an account created in the transaction. -/
theorem deletesCreated_finishSelfdestruct (hfork : .dencun ≤ fork) {beneficiary : Address}
    {refund : Nat} {evm after : Evm fork Meter}
    (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    DeletesCreated evm after := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have hc := createdAccounts_selfdestructTransfer (Base.mapError_ok_iff.mp hst)
    refine ⟨fun x hx => hc ▸ hx, fun x hx => ?_⟩
    dsimp only at hx ⊢
    split at hx
    · rename_i hd
      rcases Std.ExtTreeSet.mem_insert.mp hx with heq | hx
      · cases Std.LawfulEqCmp.eq_of_compare heq
        exact .inr (hd.resolve_left (Nat.not_lt.mpr hfork))
      · exact .inl hx
    · exact .inl hx

/-! ## A step -/

/-- From Cancun, each write of a step keeps the relation. -/
theorem stepRules_deletesCreated (hfork : .dencun ≤ fork) :
    StepRules fork (DeletesCreated (fork := fork) (Meter := Meter)) where
  trans := DeletesCreated.trans
  static := .of_staticStep
  sstore _ _ _ _ _ _ h := .of_eq (TransactionState.createdAccounts_setStorage h) rfl
  tstore _ _ _ _ := .of_eq rfl rfl
  log _ hs hsub := .of_eq (by rw [hs]) (by rw [hsub])
  selfdestruct _ _ h := deletesCreated_finishSelfdestruct hfork h
  incrementNonce _ _ _ h := .of_eq (TransactionState.createdAccounts_modifyState h) rfl
  incorporate h := deletesCreated_incorporateChild h

/-- From Cancun, every successful step of every frame keeps the relation.

A message that the step sends must end in a frame related to its caller. -/
theorem deletesCreated_step (hfork : .dencun ≤ fork) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : step fork evm = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm :=
  (stepRules_deletesCreated hfork).step h

/-! ## Messages -/

/-- A successful preparation of a creation keeps every created account. -/
theorem createdLe_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : CreatedLe tx tx' := by
  unfold prepareCreation at h
  have h0 : CreatedLe tx ((tx.destroyStorage address).markAccountCreated address) :=
    fun _ hx => Std.ExtTreeSet.mem_insert.mpr (.inr hx)
  split at h
  · intro x hx
    rw [TransactionState.createdAccounts_modifyState (Base.mapError_ok_iff.mp h)]
    exact h0 x hx
  · cases h
    exact h0

/-- The state that a message starts its frame from has the created accounts of the state before. -/
theorem createdAccounts_startState (message : Message fork) (state : TransactionState) :
    (startState fork message state).createdAccounts = state.createdAccounts := by
  unfold startState
  split
  · exact TransactionState.createdAccounts_touchAccount _ _
  · rfl

/-- A rollback keeps the created accounts and the substate of the frame. -/
theorem createdAccounts_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    (rollbackOnError snapshot evm).state.createdAccounts = evm.state.createdAccounts ∧
      (rollbackOnError snapshot evm).substate = evm.substate := by
  unfold rollbackOnError
  split <;> exact ⟨rfl, rfl⟩

/-- A successful deposit of code keeps the created accounts and the substate of the frame. -/
theorem createdAccounts_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.state.createdAccounts = evm.state.createdAccounts ∧ after.substate = evm.substate := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  split at h
  · cases h
    split <;> exact ⟨rfl, rfl⟩
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨TransactionState.createdAccounts_setCode (Base.mapError_ok_iff.mp hst), rfl⟩

/-- From Cancun, every call and creation that returns a frame keeps the created accounts.

Each account it marks for deletion was marked before it started.

Otherwise the transaction has created it by the end of the message.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem deletesCreated_processMessage_induction [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CreatedLe state ended.val.state ∧
          ∀ address ∈ ended.val.substate.accountsToDelete,
            address ∈ substate.accountsToDelete ∨
              address ∈ ended.val.state.createdAccounts) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreatedLe state ended.val.state ∧
          ∀ address ∈ ended.val.substate.accountsToDelete,
            address ∈ substate.accountsToDelete ∨
              address ∈ ended.val.state.createdAccounts) :=
  (stepRules_deletesCreated hfork).processMessage
    (M := fun _ state substate _ ended => CreatedLe state ended.state ∧
      ∀ address ∈ ended.substate.accountsToDelete,
        address ∈ substate.accountsToDelete ∨ address ∈ ended.state.createdAccounts)
    (fun {message state state1 substate substate1 _ ended} hentry hd => by
      have h12 : state1.createdAccounts = state.createdAccounts ∧
          substate1.accountsToDelete = substate.accountsToDelete := by
        rcases hentry with ⟨-, rfl, rfl⟩ | ⟨-, hm, rfl⟩
        · exact ⟨createdAccounts_startState message state, rfl⟩
        · exact ⟨(TransactionState.createdAccounts_moveEther hm).trans
            (createdAccounts_startState message state), rfl⟩
      obtain ⟨hc, hs⟩ := createdAccounts_rollbackOnError state ended
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hc]
        exact hd.1 x (h12.1 ▸ hx)
      · rw [hs] at hx
        rw [hc]
        exact (hd.2 x hx).imp_left fun hx => h12.2 ▸ hx)
    (fun hp hm hd => by
      obtain ⟨hc, hs⟩ := createdAccounts_depositCode hd
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hc]
        exact hm.1 x (createdLe_prepareCreation hp x hx)
      · rw [hs] at hx
        rw [hc]
        exact hm.2 x hx)
    (fun h => h) n

/-- From Cancun, every call that returns a frame keeps the created accounts of its start.

Each account it marks for deletion was marked before it started.

Otherwise the transaction has created it by the end of the call.

That holds whether or not the call ends with an error. -/
theorem deletesCreated_processMessage [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    CreatedLe state ended.val.state ∧
      ∀ address ∈ ended.val.substate.accountsToDelete,
        address ∈ substate.accountsToDelete ∨ address ∈ ended.val.state.createdAccounts :=
  (deletesCreated_processMessage_induction hfork message.gas).1 message state substate meter held
    rfl ended h

/-- From Cancun, every creation that returns a frame keeps the created accounts of its start.

Each account it marks for deletion was marked before it started.

Otherwise the transaction has created it by the end of the creation.

That holds whether or not the creation ends with an error. -/
theorem deletesCreated_processCreateMessage [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    CreatedLe state ended.val.state ∧
      ∀ address ∈ ended.val.substate.accountsToDelete,
        address ∈ substate.accountsToDelete ∨ address ∈ ended.val.state.createdAccounts :=
  (deletesCreated_processMessage_induction hfork message.gas).2 message state substate meter held
    rfl ended h

/-- From Cancun, a call that starts with no account to delete marks only created accounts.

That holds whether or not the call ends with an error. -/
theorem mem_createdAccounts_of_processMessage [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (empty : ∀ address, address ∉ substate.accountsToDelete) :
    ∀ address ∈ ended.val.substate.accountsToDelete, address ∈ ended.val.state.createdAccounts :=
  fun address mem => ((deletesCreated_processMessage hfork h).2 address mem).resolve_left
    (empty address)

end EthLib.Execution.Evm

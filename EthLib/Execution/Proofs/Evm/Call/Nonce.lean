module

public import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# Proofs: no message lowers a nonce

Every successful step of every frame keeps or raises the nonce of every address, at every fork.

A creation raises the nonce of the creator, and from Spurious Dragon that of the new account.

A transfer of ether, a new code and a write of storage keep every nonce.

From Paris, a change that leaves an account empty deletes it, but that account had nonce 0.

A frame that fails rolls back to its snapshot, whose nonces are those at its start.

So a call or creation that returns a frame ends with no nonce below the nonce it started with.

That holds whether or not the frame ends with an error.

The deletions at the end of a transaction are not part of a message, so they are not covered here.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (Account StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The order of nonces -/

/-- Every address has in the second state a nonce at least its nonce in the first. -/
def NonceLe (tx tx' : TransactionState) : Prop :=
  ∀ address, (tx.getAccount address).nonce ≤ (tx'.getAccount address).nonce

/-- A state has every nonce of itself. -/
theorem NonceLe.refl (tx : TransactionState) : NonceLe tx tx := fun _ => Nat.le_refl _

/-- Two steps that each keep or raise every nonce keep or raise them together. -/
theorem NonceLe.trans {a b c : TransactionState} (hab : NonceLe a b) (hbc : NonceLe b c) :
    NonceLe a c :=
  fun address => Nat.le_trans (hab address) (hbc address)

/-- A state with the accounts of another has its nonces. -/
theorem NonceLe.of_getAccountOptional {tx tx' : TransactionState}
    (h : ∀ address, tx'.getAccountOptional address = tx.getAccountOptional address) :
    NonceLe tx tx' :=
  fun address => by unfold TransactionState.getAccount; rw [h]; exact Nat.le_refl _

/-- A state that reads as another at every address has its nonces. -/
theorem NonceLe.of_sameOutside {tx tx' : TransactionState}
    (h : TransactionState.SameOutside [] tx tx') : NonceLe tx tx' :=
  of_getAccountOptional fun address => (h address List.not_mem_nil).1

omit [GasMeter Meter] in
/-- A step that keeps the state up to the records of its reads lowers no nonce. -/
theorem StaticStep.nonceLe {a b : Evm fork Meter} (h : StaticStep a b) :
    NonceLe a.state b.state :=
  NonceLe.of_sameOutside h.state

/-- A rollback to a snapshot of the same block lowers no nonce of the snapshot. -/
theorem nonceLe_restoreTxState {tx snapshot : TransactionState}
    (h : tx.parent = snapshot.parent) : NonceLe snapshot (tx.restoreTxState snapshot) :=
  NonceLe.of_getAccountOptional (TransactionState.getAccountOptional_restoreTxState h)

/-! ## The writes of the state -/

/-- A change of one account that keeps or raises its nonce keeps or raises every nonce.

From Paris, the change may delete the account, but only when it leaves nonce 0. -/
theorem nonceLe_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ account account', f account = .ok account' → account.nonce ≤ account'.nonce)
    (h : tx.modifyState fork address f = .ok tx') : NonceLe tx tx' := by
  obtain ⟨account, hfa, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  intro other
  by_cases hne : other = address
  · subst hne
    rw [hself]
    exact hf _ _ hfa
  · rw [hother other hne]
    exact Nat.le_refl _

/-- A debit keeps the nonce. -/
theorem nonce_le_debit {address : Address} {amount : U256} {account account' : Account}
    (h : Account.debit address amount account = .ok account') :
    account.nonce ≤ account'.nonce := by
  unfold Account.debit at h
  split at h <;> cases h
  exact Nat.le_refl _

/-- A credit keeps the nonce. -/
theorem nonce_le_credit {address : Address} {amount : U256} {account account' : Account}
    (h : Account.credit address amount account = .ok account') :
    account.nonce ≤ account'.nonce := by
  unfold Account.credit at h
  split at h <;> cases h
  exact Nat.le_refl _

/-- A move of ether lowers no nonce. -/
theorem nonceLe_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    NonceLe tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (nonceLe_modifyState (fun _ _ => nonce_le_debit) h1).trans
    (nonceLe_modifyState (fun _ _ => nonce_le_credit) h2)

/-- A creation of ether lowers no nonce. -/
theorem nonceLe_createEther {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.createEther fork address amount = .ok tx') : NonceLe tx tx' :=
  nonceLe_modifyState (fun _ _ => nonce_le_credit) h

/-- A new balance lowers no nonce. -/
theorem nonceLe_setAccountBalance {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') : NonceLe tx tx' :=
  nonceLe_modifyState (fun _ _ hf => by cases hf; exact Nat.le_refl _) h

/-- A raise of one nonce keeps or raises every nonce. -/
theorem nonceLe_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : NonceLe tx tx' :=
  nonceLe_modifyState (fun _ _ hf => by cases hf; exact Nat.le_succ _) h

/-- A new code lowers no nonce. -/
theorem nonceLe_setCode {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (h : tx.setCode fork address code = .ok tx') : NonceLe tx tx' := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_setCode h
  intro other
  by_cases hne : other = address
  · subst hne
    rw [hself]
    exact Nat.le_refl _
  · unfold TransactionState.getAccount
    rw [hother other hne]
    exact Nat.le_refl _

/-- A write of storage lowers no nonce. -/
theorem nonceLe_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') : NonceLe tx tx' :=
  NonceLe.of_getAccountOptional fun _ => TransactionState.getAccountOptional_setStorage h

/-- A touch of an account lowers no nonce. -/
theorem nonceLe_touchAccount (tx : TransactionState) (address : Address) :
    NonceLe tx (tx.touchAccount address) := by
  intro other
  by_cases hne : other = address
  · subst hne
    rw [TransactionState.getAccount_touchAccount_self]
    exact Nat.le_refl _
  · rw [TransactionState.getAccount_touchAccount hne]
    exact Nat.le_refl _

/-- A successful move of the balance of a destroyed account lowers no nonce. -/
theorem nonceLe_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') : NonceLe tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (nonceLe_moveEther h1).trans (nonceLe_setAccountBalance h)
    · cases h
      exact nonceLe_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (nonceLe_createEther h1).trans (nonceLe_setAccountBalance h)

/-- A successful preparation of a creation keeps or raises every nonce. -/
theorem nonceLe_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : NonceLe tx tx' := by
  unfold prepareCreation at h
  have h0 : NonceLe tx ((tx.destroyStorage address).markAccountCreated address) :=
    NonceLe.of_getAccountOptional fun _ => rfl
  split at h
  · exact h0.trans (nonceLe_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact h0

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT lowers no nonce. -/
theorem nonceLe_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    NonceLe evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact nonceLe_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-! ## A step -/

/-- Each write of a step lowers no nonce, static frame or not. -/
theorem stepRules_nonceLe :
    StepRules fork (fun a b : Evm fork Meter => NonceLe a.state b.state) where
  trans := NonceLe.trans
  static h := h.nonceLe
  sstore _ _ _ _ _ _ h := nonceLe_setStorage h
  tstore _ _ _ _ := NonceLe.of_getAccountOptional fun _ => rfl
  log _ hs _ _ _ := by rw [hs]; exact NonceLe.refl _
  selfdestruct _ _ h := nonceLe_finishSelfdestruct h
  incrementNonce _ _ _ h := nonceLe_incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-- A result of a step from `evm` that keeps or raises every nonce.

The next frame has nonces at least those of `evm`.

A child is sent from a frame with nonces at least those of `evm`.

So has the frame that resumes, when the frame that ends the child has those of the caller. -/
abbrev NonceResult (evm : Evm fork Meter) : StepResult fork Meter → Prop :=
  StepResult.Keeps (fun a b => NonceLe a.state b.state)
    (fun caller _ child => NonceLe caller.state child.state) evm

/-- Every successful step of every frame keeps or raises every nonce, static frame or not. -/
theorem nonceResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : NonceResult evm result :=
  stepRules_nonceLe.step h

/-! ## A run of a frame -/

/-- A runner of messages that keeps or raises every nonce.

Each message that it runs successfully ends with nonces at least those of its sender. -/
def KeepsNonce {bound : Nat} (runChild : MessageRunner fork Meter bound) : Prop :=
  RunnerEnsures (fun caller _ child => NonceLe caller.state child.state) runChild

/-- A successful run of a frame keeps or raises every nonce.

The runner of its messages must keep or raise every nonce. -/
theorem nonceLe_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} (runs : KeepsNonce runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    NonceLe evm.state after.state :=
  stepRules_nonceLe.runFrame runs h

/-! ## Messages -/

/-- A successful deposit of code keeps or raises every nonce of the state before the creation.

The frame that ends the init code must have those nonces and the block of that state. -/
theorem nonceLe_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (hle : NonceLe snapshot evm.state) (hp : evm.state.parent = snapshot.parent)
    (h : depositCode fork snapshot evm = .ok after) : NonceLe snapshot after.state := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact nonceLe_restoreTxState hp
  split at h
  · cases h
    exact nonceLe_restoreTxState hp
  split at h
  · cases h
    exact nonceLe_restoreTxState hp
  split at h
  · cases h
    split
    · exact nonceLe_restoreTxState hp
    · exact hle
  split at h
  · cases h
    exact nonceLe_restoreTxState hp
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact hle.trans (nonceLe_setCode (Base.mapError_ok_iff.mp hst))

/-- The state that a message starts its frame from has every nonce of the state it is sent from. -/
theorem nonceLe_startState (message : Message fork) (state : TransactionState) :
    NonceLe state (startState fork message state) := by
  unfold startState
  split
  · exact nonceLe_touchAccount _ _
  · exact NonceLe.refl _

/-- A call that keeps or raises every nonce of the state it enters still does so after its rollback.

It must also keep the block of that state.

The call then keeps the block and lowers no nonce from the state it is sent from. -/
theorem nonceLe_rollbackOnError {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate} {ended : Evm fork Meter}
    (hentry : Entered fork message state substate entry entrySubstate)
    (hrun : NonceLe entry ended.state ∧ ended.state.parent = entry.parent) :
    NonceLe state (rollbackOnError state ended).state ∧
      (rollbackOnError state ended).state.parent = state.parent := by
  have h1 : NonceLe state entry ∧ entry.parent = state.parent := by
    rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
    · exact ⟨nonceLe_startState message state, parent_startState message state⟩
    · exact ⟨(nonceLe_startState message state).trans (nonceLe_moveEther hm),
        (TransactionState.parent_moveEther hm).trans (parent_startState message state)⟩
  obtain ⟨hle, hpar⟩ := hrun
  have hp : ended.state.parent = state.parent := hpar.trans h1.2
  refine ⟨?_, (parent_rollbackOnError state ended).trans hp⟩
  unfold rollbackOnError
  split
  · exact nonceLe_restoreTxState hp
  · exact h1.1.trans hle

/-- A creation whose init code keeps or raises every nonce does so after its deposit of code.

The init code must also keep the block of the state it runs from.

The creation then keeps the block and lowers no nonce from the state it is sent from. -/
theorem nonceLe_prepareCreation_depositCode {state prepared : TransactionState}
    {address : Address} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hm : NonceLe prepared evm.state ∧ evm.state.parent = prepared.parent)
    (hd : depositCode fork state evm = .ok after) :
    NonceLe state after.state ∧ after.state.parent = state.parent :=
  ⟨nonceLe_depositCode ((nonceLe_prepareCreation hp).trans hm.1)
      (hm.2.trans (parent_prepareCreation hp)) hd,
    (parent_depositCode hd).trans (hm.2.trans (parent_prepareCreation hp))⟩

/-- Every successful call and creation keeps or raises every nonce, at every fork.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_nonceLe [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        NonceLe state ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        NonceLe state ended.val.state) := by
  have both := (stepRules_nonceLe (fork := fork) (Meter := Meter)).and stepRules_parent
    |>.processMessage
    (M := fun _ state _ _ ended => NonceLe state ended.state ∧ ended.state.parent = state.parent)
    (fun hentry hrun => nonceLe_rollbackOnError hentry hrun)
    (fun hp hm hd => nonceLe_prepareCreation_depositCode hp hm hd)
    (fun h => h) n
  exact ⟨fun message state substate meter held hn ended h =>
      (both.1 message state substate meter held hn ended h).1,
    fun message state substate meter held hn ended h =>
      (both.2 message state substate meter held hn ended h).1⟩

/-- A call that returns a frame keeps or raises the nonce of every address, at every fork.

That holds whether or not the frame ends with an error. -/
theorem nonce_le_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) (address : Address) :
    (state.getAccount address).nonce ≤ (ended.val.state.getAccount address).nonce :=
  (processMessage_nonceLe message.gas).1 message state substate meter held rfl ended h address

/-- A creation that returns a frame keeps or raises the nonce of every address, at every fork.

That holds whether or not the frame ends with an error. -/
theorem nonce_le_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (address : Address) :
    (state.getAccount address).nonce ≤ (ended.val.state.getAccount address).nonce :=
  (processMessage_nonceLe message.gas).2 message state substate meter held rfl ended h address

end EthLib.Execution.Evm

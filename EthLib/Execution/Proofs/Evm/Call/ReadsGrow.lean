module

public import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# Proofs: a run never drops a read

A transaction state records the accounts and the storage keys that the transaction read.

Each step only adds to those records, whether it writes, halts or sends a message.

A rollback keeps the reads of the frame that it undoes, so a failed call keeps them too.

So every run of a frame, every call and every creation ends with every read it started with.

Source: [EIP-7928, Scope and Inclusion][eip7928], which asks the list to name every read.

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.State.TransactionState

open EthLib.Base (Address Bytes32)

/-- The second state holds every read of the first: each account and each storage key. -/
structure ReadsLe (tx tx' : TransactionState) : Prop where
  /-- Every account that the first state read is read in the second. -/
  accountReads : ∀ address, address ∈ tx.accountReads → address ∈ tx'.accountReads
  /-- Every storage key that the first state read is read in the second, at the same address. -/
  storageReads : ∀ address key, key ∈ tx.storageReads.getD address ∅ →
    key ∈ tx'.storageReads.getD address ∅

/-- Every state holds its own reads. -/
theorem ReadsLe.refl (tx : TransactionState) : tx.ReadsLe tx :=
  ⟨fun _ h => h, fun _ _ h => h⟩

/-- Holding the reads is transitive. -/
theorem ReadsLe.trans {a b c : TransactionState} (hab : a.ReadsLe b) (hbc : b.ReadsLe c) :
    a.ReadsLe c :=
  ⟨fun x h => hbc.accountReads x (hab.accountReads x h),
    fun x k h => hbc.storageReads x k (hab.storageReads x k h)⟩

/-- A state that only adds reads holds every earlier read. -/
theorem ReadsMore.readsLe {a b : TransactionState} (h : a.ReadsMore b) : a.ReadsLe b :=
  ⟨h.accountReads, h.storageReads⟩

end EthLib.Execution.State.TransactionState

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (Account StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes of the state -/

/-- A change of one account keeps every read. -/
theorem readsLe_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx.ReadsLe tx' := by
  obtain ⟨_, _, hacc, hst⟩ := TransactionState.reads_modifyState h
  refine ⟨fun x hx => ?_, fun x k hk => ?_⟩
  · rw [hacc]
    exact Std.ExtTreeSet.mem_insert.mpr (.inr hx)
  · rw [hst]
    split
    · exact TransactionState.mem_storageReads_destroyStorage_of_mem hk
    · exact hk

/-- A move of ether keeps every read. -/
private theorem readsLe_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx.ReadsLe tx' := by
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (readsLe_modifyState h1).trans (readsLe_modifyState h2)

/-- A write of code keeps every read. -/
theorem readsLe_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') : tx.ReadsLe tx' := by
  unfold TransactionState.setCode at h
  dsimp only at h
  split at h
  · exact readsLe_modifyState h
  · have := readsLe_modifyState h
    exact ⟨this.accountReads, this.storageReads⟩

/-- A write of storage keeps every read. -/
private theorem readsLe_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx.ReadsLe tx' := by
  obtain ⟨hacc, hst⟩ := TransactionState.reads_setStorage h
  refine ⟨fun x hx => ?_, fun x k hk => ?_⟩
  · rw [hacc]
    exact Std.ExtTreeSet.mem_insert.mpr (.inr hx)
  · rw [hst]
    exact hk

/-- A successful move of the balance of a destroyed account keeps every read. -/
private theorem readsLe_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') : tx.ReadsLe tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (readsLe_moveEther h1).trans (readsLe_modifyState h)
    · cases h
      exact readsLe_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (readsLe_modifyState h1).trans (readsLe_modifyState h)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps every read. -/
private theorem readsLe_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    evm.state.ReadsLe after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact readsLe_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-- Each write of a step keeps every read of the state. -/
theorem stepRules_readsLe :
    StepRules fork (fun a b : Evm fork Meter => a.state.ReadsLe b.state) where
  trans hab hbc := hab.trans hbc
  static h := h.tracker.readsLe
  sstore _ _ _ _ _ _ h := readsLe_setStorage h
  tstore _ _ _ _ := ⟨fun _ h => h, fun _ _ h => h⟩
  log _ hs _ _ _ := by rw [hs]; exact .refl _
  selfdestruct _ _ h := readsLe_finishSelfdestruct h
  incrementNonce _ _ _ _ h := readsLe_modifyState h
  incorporate h := by rw [state_incorporateChild]; exact h

/-- A successful run of a frame keeps every read of its state.

The runner of its messages must keep every read of the frame that sends each message. -/
theorem readsLe_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (runs : RunnerEnsures (fun caller _ child => caller.state.ReadsLe child.state) runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    evm.state.ReadsLe after.state :=
  stepRules_readsLe.runFrame runs h

/-! ## Messages -/

/-- A rollback keeps every read of the frame that it undoes. -/
theorem readsLe_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    evm.state.ReadsLe (rollbackOnError snapshot evm).state := by
  unfold rollbackOnError
  split
  · exact ⟨fun _ h => h, fun _ _ h => h⟩
  · exact .refl _

/-- The state that a message enters holds every read of the state it is sent from. -/
theorem readsLe_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) : state.ReadsLe entry := by
  have start : state.ReadsLe (startState fork message state) := by
    unfold startState
    split
    · obtain ⟨hacc, hst⟩ := TransactionState.reads_touchAccount state message.currentTarget
      exact ⟨fun x hx => hacc ▸ hx, fun x k hk => hst ▸ hk⟩
    · exact .refl _
  rcases h with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
  · exact start
  · exact start.trans (readsLe_moveEther moved)

/-- A successful preparation of a creation keeps every read. -/
theorem readsLe_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : tx.ReadsLe tx' := by
  have wiped : tx.ReadsLe ((tx.destroyStorage address).markAccountCreated address) :=
    ⟨fun _ h => h, fun _ _ h => TransactionState.mem_storageReads_destroyStorage_of_mem h⟩
  unfold prepareCreation at h
  split at h
  · exact wiped.trans (readsLe_modifyState (Base.mapError_ok_iff.mp h))
  · cases h
    exact wiped

/-- A successful deposit of code keeps every read of the frame that ends the init code. -/
theorem readsLe_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) : evm.state.ReadsLe after.state := by
  rcases (depositCode_cases h).2.2 with hs | hs | hs
  · rw [hs]
    exact ⟨fun _ h => h, fun _ _ h => h⟩
  · rw [hs]
    exact .refl _
  · exact readsLe_setCode hs

/-- Every successful call and creation keeps every read of the state it is sent from.

That holds at every fork, whether its frame ends with an error or not.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_readsLe [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        state.ReadsLe ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        state.ReadsLe ended.val.state) :=
  stepRules_readsLe.processMessage
    (M := fun _ state _ _ ended => state.ReadsLe ended.state)
    (fun hentry hrun => ((readsLe_entered hentry).trans hrun).trans (readsLe_rollbackOnError _ _))
    (fun hp hm hd => ((readsLe_prepareCreation hp).trans hm).trans (readsLe_depositCode hd))
    (fun h => h) n

/-- A call that ends keeps every read of the state it is sent from, even if its frame fails. -/
theorem readsLe_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    state.ReadsLe ended.val.state :=
  (processMessage_readsLe message.gas).1 message state substate meter held rfl ended h

/-- A creation that ends keeps every read of the state it is sent from, even if its frame fails. -/
theorem readsLe_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    state.ReadsLe ended.val.state :=
  (processMessage_readsLe message.gas).2 message state substate meter held rfl ended h

end EthLib.Execution.Evm

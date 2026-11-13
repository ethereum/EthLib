module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: every code hash comes from the block or from a write

A transaction state fetches the code of an account by its code hash.

So the code that a run fetches depends only on the block and on the codes that the run wrote.

Take a state where each account has no code, a written code, or its code hash in the block.

Every call and every creation keeps that, whether its frame ends with an error or not.

A step changes no code hash, and a rollback restores a snapshot with the same block.

A creation gives its address the hash of a code that it writes first.

The written codes never shrink, since a rollback restores those of its snapshot.

Source: [EIP-7928, Scope and Inclusion][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State
  (Account BlockState EMPTY_CODE_HASH StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A relation of states -/

/-- The second state has the block and every written code of the first.

Each account of the second has no code, a written code, or the code hash it had in the first. -/
def KeepsCodeOrigin (tx tx' : TransactionState) : Prop :=
  tx'.parent = tx.parent ∧ (∀ codeHash, codeHash ∈ tx.codeWrites → codeHash ∈ tx'.codeWrites) ∧
    ∀ address, (tx'.getAccount address).codeHash = EMPTY_CODE_HASH ∨
      (tx'.getAccount address).codeHash ∈ tx'.codeWrites ∨
      (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash

/-- Each account has no code, a written code, or the code hash it had in the block. -/
def CodeOrigin (block : BlockState) (tx : TransactionState) : Prop :=
  ∀ address, (tx.getAccount address).codeHash = EMPTY_CODE_HASH ∨
    (tx.getAccount address).codeHash ∈ tx.codeWrites ∨
    (tx.getAccount address).codeHash =
      ((TransactionState.ofBlock block).getAccount address).codeHash

/-- A state keeps the origin of its own code hashes. -/
theorem KeepsCodeOrigin.refl (tx : TransactionState) : KeepsCodeOrigin tx tx :=
  ⟨rfl, fun _ h => h, fun _ => .inr (.inr rfl)⟩

/-- Two states in a row that each keep the origin of the code hashes keep it together. -/
theorem KeepsCodeOrigin.trans {a b c : TransactionState} (hab : KeepsCodeOrigin a b)
    (hbc : KeepsCodeOrigin b c) : KeepsCodeOrigin a c := by
  refine ⟨hbc.1.trans hab.1, fun h hh => hbc.2.1 h (hab.2.1 h hh), fun x => ?_⟩
  rcases hbc.2.2 x with he | hw | heq
  · exact .inl he
  · exact .inr (.inl hw)
  · rw [heq]
    exact (hab.2.2 x).imp_right (Or.imp_left (hbc.2.1 _))

/-- The fresh state of a block has the code hashes of that block. -/
theorem CodeOrigin.ofBlock (block : BlockState) : CodeOrigin block (.ofBlock block) :=
  fun _ => .inr (.inr rfl)

/-- A later state that keeps the origin of the code hashes inherits it from an earlier state. -/
theorem CodeOrigin.of_keepsCodeOrigin {block : BlockState} {tx tx' : TransactionState}
    (hinv : CodeOrigin block tx) (hk : KeepsCodeOrigin tx tx') : CodeOrigin block tx' := by
  intro x
  rcases hk.2.2 x with he | hw | heq
  · exact .inl he
  · exact .inr (.inl hw)
  · rw [heq]
    exact (hinv x).imp_right (Or.imp_left (hk.2.1 _))

/-! ## Writes of a state -/

/-- A change of one account keeps the written codes. -/
private theorem codeWrites_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.codeWrites = tx.codeWrites := by
  obtain ⟨account, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
  split <;> rfl

/-- A change of one account keeps the origin of the code hashes when the new hash has one.

The new hash is the empty one, a written one, or the old one. -/
private theorem KeepsCodeOrigin.modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ updated, f (tx.getAccount address) = .ok updated →
      updated.codeHash = EMPTY_CODE_HASH ∨ updated.codeHash ∈ tx.codeWrites ∨
        updated.codeHash = (tx.getAccount address).codeHash)
    (h : tx.modifyState fork address f = .ok tx') : KeepsCodeOrigin tx tx' := by
  obtain ⟨updated, hupd, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  have hw := codeWrites_modifyState h
  refine ⟨TransactionState.parent_modifyState h, fun _ hc => hw ▸ hc, fun x => ?_⟩
  rw [hw]
  by_cases hx : x = address
  · subst hx
    rw [hself]
    exact hf updated hupd
  · rw [hother x hx]
    exact .inr (.inr rfl)

/-- A change of one account that keeps its code hash keeps the origin of the code hashes. -/
theorem KeepsCodeOrigin.modifyState_of_keeps {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (hf : ∀ account updated, f account = .ok updated → updated.codeHash = account.codeHash)
    (h : tx.modifyState fork address f = .ok tx') : KeepsCodeOrigin tx tx' :=
  .modifyState (fun _ hupd => .inr (.inr (hf _ _ hupd))) h

/-- A debit keeps the code hash of an account. -/
private theorem codeHash_debit {address : Address} {amount : U256} {account updated : Account}
    (h : Account.debit address amount account = .ok updated) :
    updated.codeHash = account.codeHash := by
  unfold Account.debit at h
  split at h <;> cases h
  rfl

/-- A credit keeps the code hash of an account. -/
private theorem codeHash_credit {address : Address} {amount : U256} {account updated : Account}
    (h : Account.credit address amount account = .ok updated) :
    updated.codeHash = account.codeHash := by
  unfold Account.credit at h
  split at h <;> cases h
  rfl

/-- A move of ether keeps the origin of the code hashes. -/
private theorem KeepsCodeOrigin.moveEther {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') : KeepsCodeOrigin tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (KeepsCodeOrigin.modifyState_of_keeps (fun _ _ hf => codeHash_debit hf) h1).trans
    (KeepsCodeOrigin.modifyState_of_keeps (fun _ _ hf => codeHash_credit hf) h2)

/-- A write of a balance keeps the origin of the code hashes. -/
private theorem KeepsCodeOrigin.setAccountBalance {tx tx' : TransactionState}
    {address : Address} {amount : U256}
    (h : tx.setAccountBalance fork address amount = .ok tx') : KeepsCodeOrigin tx tx' :=
  .modifyState_of_keeps (fun _ _ hf => by cases hf; rfl) h

/-- A rise of a nonce keeps the origin of the code hashes. -/
theorem KeepsCodeOrigin.incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : KeepsCodeOrigin tx tx' :=
  .modifyState_of_keeps (fun _ _ hf => by cases hf; rfl) h

/-- A successful move of the balance of a self-destructing account keeps the origin. -/
private theorem KeepsCodeOrigin.selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeepsCodeOrigin tx tx' := by
  unfold Evm.selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (KeepsCodeOrigin.moveEther h1).trans (KeepsCodeOrigin.setAccountBalance h)
    · cases h
      exact KeepsCodeOrigin.moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (KeepsCodeOrigin.modifyState_of_keeps (fun _ _ hf => codeHash_credit hf) h1).trans
      (KeepsCodeOrigin.setAccountBalance h)

/-- A write of storage keeps the origin of the code hashes. -/
private theorem KeepsCodeOrigin.setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    KeepsCodeOrigin tx tx' := by
  unfold TransactionState.setStorage at h
  split at h
  · cases h
  · cases h
    exact KeepsCodeOrigin.refl tx

/-- A write of code keeps the origin of the code hashes.

It first records the code, unless the code is empty. -/
theorem KeepsCodeOrigin.setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    KeepsCodeOrigin tx tx' := by
  dsimp only [TransactionState.setCode] at h
  split at h
  · exact .modifyState (fun _ hupd => by cases hupd; exact .inl (by assumption)) h
  · have hk := KeepsCodeOrigin.modifyState (h := h) fun _ hupd => by
      cases hupd
      exact .inr (.inl Std.ExtTreeMap.mem_insert_self)
    refine KeepsCodeOrigin.trans ?_ hk
    exact ⟨rfl, fun _ hx => Std.ExtTreeMap.mem_insert.mpr (.inr hx), fun _ => .inr (.inr rfl)⟩

/-- A rollback to a snapshot on the same block keeps the snapshot's origin of the code hashes. -/
private theorem KeepsCodeOrigin.restoreTxState {tx snapshot : TransactionState}
    (hp : tx.parent = snapshot.parent) :
    KeepsCodeOrigin snapshot (tx.restoreTxState snapshot) := by
  have hs := sameWrites_restoreTxState tx snapshot
  refine ⟨hp, fun _ hc => hs.codeWrites ▸ hc, fun x => .inr (.inr ?_)⟩
  rw [hs.getAccount hp x]

/-- A touch of an account keeps the origin of the code hashes. -/
private theorem KeepsCodeOrigin.touchAccount (tx : TransactionState) (address : Address) :
    KeepsCodeOrigin tx (tx.touchAccount address) := by
  have hw : (tx.touchAccount address).codeWrites = tx.codeWrites := by
    unfold TransactionState.touchAccount
    split <;> rfl
  refine ⟨TransactionState.parent_touchAccount tx address, fun _ hc => hw ▸ hc,
    fun x => .inr (.inr ?_)⟩
  by_cases hne : x = address
  · subst hne
    rw [TransactionState.getAccount_touchAccount_self]
  · rw [TransactionState.getAccount_touchAccount hne]

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps the origin of the code hashes. -/
private theorem keepsCodeOrigin_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    KeepsCodeOrigin evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact .selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-! ## Steps of a frame -/

/-- Each write of a step keeps the origin of the code hashes, in any frame. -/
theorem stepRules_keepsCodeOrigin :
    StepRules fork (fun a b : Evm fork Meter => KeepsCodeOrigin a.state b.state) where
  trans := KeepsCodeOrigin.trans
  static h := by
    have hw := h.tracker.rest
    refine ⟨h.parent, fun _ hc => ?_, fun x => .inr (.inr (by rw [getAccount_of_staticStep h x]))⟩
    rw [hw]
    exact hc
  sstore _ _ _ _ _ _ h := .setStorage h
  tstore _ _ _ _ := ⟨rfl, fun _ hx => hx, fun _ => .inr (.inr rfl)⟩
  log _ hs _ _ _ := by rw [hs]; exact .refl _
  selfdestruct _ _ h := keepsCodeOrigin_finishSelfdestruct h
  incrementNonce _ _ _ _ h := .incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-! ## Messages -/

/-- The state that a message enters keeps the origin of the code hashes of its sender state. -/
theorem keepsCodeOrigin_entered {message : Message fork}
    {state entry : TransactionState} {substate entrySubstate : Substate}
    (hentry : Entered fork message state substate entry entrySubstate) :
    KeepsCodeOrigin state entry := by
  have hstart : KeepsCodeOrigin state (startState fork message state) := by
    unfold startState
    split
    · exact .touchAccount state message.currentTarget
    · exact .refl state
  rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact hstart
  · exact hstart.trans (.moveEther hm)

/-- A rollback on error keeps the origin of the code hashes, when the frame keeps it. -/
private theorem keepsCodeOrigin_rollbackOnError {snapshot : TransactionState}
    {ended : Evm fork Meter} (hk : KeepsCodeOrigin snapshot ended.state) :
    KeepsCodeOrigin snapshot (rollbackOnError snapshot ended).state := by
  unfold rollbackOnError
  split
  · exact .restoreTxState hk.1
  · exact hk

/-- A preparation of a creation keeps the origin of the code hashes. -/
theorem keepsCodeOrigin_prepareCreation {state prepared : TransactionState}
    {address : Address} (hp : prepareCreation fork state address = .ok prepared) :
    KeepsCodeOrigin state prepared := by
  have hwipe :
      KeepsCodeOrigin state ((state.destroyStorage address).markAccountCreated address) :=
    ⟨rfl, fun _ hc => hc, fun _ => .inr (.inr rfl)⟩
  unfold prepareCreation at hp
  split at hp
  · exact hwipe.trans (.incrementNonce (Base.mapError_ok_iff.mp hp))
  · cases hp
    exact hwipe

/-- A deposit of code keeps the origin of the code hashes of the state before the creation. -/
private theorem keepsCodeOrigin_depositCode {state prepared : TransactionState}
    {address : Address} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hk : KeepsCodeOrigin prepared evm.state) (hd : depositCode fork state evm = .ok after) :
    KeepsCodeOrigin state after.state := by
  have hprep := keepsCodeOrigin_prepareCreation hp
  rcases (depositCode_cases hd).2.2 with hs | hs | hs
  · rw [hs]
    exact .restoreTxState (hk.1.trans hprep.1)
  · rw [hs]
    exact hprep.trans hk
  · exact (hprep.trans hk).trans (.setCode hs)

/-- By induction on gas, calls and creations keep the origin of the code hashes. -/
private theorem keepsCodeOrigin_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        KeepsCodeOrigin state ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        KeepsCodeOrigin state ended.val.state) :=
  stepRules_keepsCodeOrigin.processMessage
    (M := fun _ state _ _ ended => KeepsCodeOrigin state ended.state)
    (fun hentry hrun =>
      keepsCodeOrigin_rollbackOnError ((keepsCodeOrigin_entered hentry).trans hrun))
    (fun hp hm hd => keepsCodeOrigin_depositCode hp hm hd)
    (fun h => h) n

/-- A call that returns a frame keeps the origin of the code hashes of the state it starts from. -/
theorem keepsCodeOrigin_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended) :
    KeepsCodeOrigin state ended.val.state :=
  (keepsCodeOrigin_induction message.gas).1 message state substate meter held rfl ended h

/-- A creation that returns a frame keeps the origin of the code hashes of its start state. -/
theorem keepsCodeOrigin_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    KeepsCodeOrigin state ended.val.state :=
  (keepsCodeOrigin_induction message.gas).2 message state substate meter held rfl ended h

end EthLib.Execution.Evm

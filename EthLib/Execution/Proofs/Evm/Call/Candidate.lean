module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.State.Agreement
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: a message makes no new deployment candidate

A deployment candidate is an address with nonce 0 and no code, where a creation may deploy.

Whether a creation succeeds there depends on the account, so the block access list must name it.

Take a transaction state where every candidate was one in the block, or had its storage wiped.

Every call and every creation keeps that, whether its frame ends with an error or not.

A step never lowers a nonce, and gives code only to the address of a creation.

That address had its storage wiped when the creation started, and a rollback restores a snapshot.

So each write of a step keeps the candidates.

The shared rules for steps carry that to every step.

A call also keeps its message, so the deposit of code knows the address of its creation.

Source: [EIP-7928, Scope and Inclusion][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (Account BlockState EMPTY_CODE_HASH StateError TransactionState)
open EthLib.Execution.State.TransactionState (NoNewCandidate)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A relation of states -/

/-- The second state has the block of the first, and every address that the first wiped.

Each address with nonce 0 and no code in it had both in the first, or had its storage wiped. -/
def KeepsCandidates (tx tx' : TransactionState) : Prop :=
  tx'.parent = tx.parent ∧ (∀ address, address ∈ tx.storageClears → address ∈ tx'.storageClears) ∧
    ∀ address, (tx'.getAccount address).nonce = 0 →
      (tx'.getAccount address).codeHash = EMPTY_CODE_HASH →
      address ∈ tx'.storageClears ∨
        ((tx.getAccount address).nonce = 0 ∧ (tx.getAccount address).codeHash = EMPTY_CODE_HASH)

/-- A state keeps its own candidates. -/
theorem KeepsCandidates.refl (tx : TransactionState) : KeepsCandidates tx tx :=
  ⟨rfl, fun _ h => h, fun _ hn hc => .inr ⟨hn, hc⟩⟩

/-- Two states in a row that each keep the candidates keep them together. -/
theorem KeepsCandidates.trans {a b c : TransactionState} (hab : KeepsCandidates a b)
    (hbc : KeepsCandidates b c) : KeepsCandidates a c :=
  ⟨hbc.1.trans hab.1, fun x hx => hbc.2.1 x (hab.2.1 x hx), fun x hn hc =>
    (hbc.2.2 x hn hc).elim .inl fun ⟨hn', hc'⟩ => (hab.2.2 x hn' hc').imp_left (hbc.2.1 x)⟩

/-- A state with the writes and the block of another keeps its candidates. -/
private theorem KeepsCandidates.of_sameWrites {tx tx' : TransactionState} (h : SameWrites tx' tx)
    (hp : tx'.parent = tx.parent) : KeepsCandidates tx tx' :=
  ⟨hp, fun _ hx => h.storageClears ▸ hx, fun x hn hc => .inr (h.getAccount hp x ▸ ⟨hn, hc⟩)⟩

/-- A change of one account keeps the candidates when it makes none there.

The new account has a nonce or code, or the address was wiped, or the old account had neither. -/
private theorem KeepsCandidates.modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ updated, f (tx.getAccount address) = .ok updated → updated.nonce = 0 →
      updated.codeHash = EMPTY_CODE_HASH →
      address ∈ tx.storageClears ∨
        ((tx.getAccount address).nonce = 0 ∧ (tx.getAccount address).codeHash = EMPTY_CODE_HASH))
    (h : tx.modifyState fork address f = .ok tx') : KeepsCandidates tx tx' := by
  have hclears : ∀ x, x ∈ tx.storageClears → x ∈ tx'.storageClears := by
    obtain ⟨updated, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
    intro x hx
    split
    · simp [TransactionState.destroyAccount, TransactionState.destroyStorage,
        TransactionState.setAccount, TransactionState.recordAccountRead, hx]
    · exact hx
  obtain ⟨updated, hupd, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  refine ⟨TransactionState.parent_modifyState h, hclears, fun x hn hc => ?_⟩
  by_cases hx : x = address
  · subst hx
    rw [hself] at hn hc
    exact (hf updated hupd hn hc).imp_left (hclears x)
  · rw [hother x hx] at hn hc
    exact .inr ⟨hn, hc⟩

/-- A change of one account that keeps its nonce and its code keeps the candidates. -/
private theorem KeepsCandidates.modifyState_of_keeps {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (hf : ∀ account updated, f account = .ok updated →
      updated.nonce = account.nonce ∧ updated.codeHash = account.codeHash)
    (h : tx.modifyState fork address f = .ok tx') : KeepsCandidates tx tx' :=
  .modifyState (fun updated hupd hn hc => by
    obtain ⟨hn', hc'⟩ := hf _ _ hupd
    exact .inr ⟨hn' ▸ hn, hc' ▸ hc⟩) h

/-- A debit keeps the nonce and the code of an account. -/
private theorem debit_keeps {address : Address} {amount : U256} {account updated : Account}
    (h : Account.debit address amount account = .ok updated) :
    updated.nonce = account.nonce ∧ updated.codeHash = account.codeHash := by
  unfold Account.debit at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

/-- A credit keeps the nonce and the code of an account. -/
private theorem credit_keeps {address : Address} {amount : U256} {account updated : Account}
    (h : Account.credit address amount account = .ok updated) :
    updated.nonce = account.nonce ∧ updated.codeHash = account.codeHash := by
  unfold Account.credit at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

/-- A move of ether keeps the candidates. -/
private theorem KeepsCandidates.moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    KeepsCandidates tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (KeepsCandidates.modifyState_of_keeps (fun _ _ hf => debit_keeps hf) h1).trans
    (KeepsCandidates.modifyState_of_keeps (fun _ _ hf => credit_keeps hf) h2)

/-- A write of a balance keeps the candidates. -/
private theorem KeepsCandidates.setAccountBalance {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    KeepsCandidates tx tx' :=
  .modifyState_of_keeps (fun _ _ hf => by cases hf; exact ⟨rfl, rfl⟩) h

/-- A rise of a nonce keeps the candidates. -/
private theorem KeepsCandidates.incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : KeepsCandidates tx tx' :=
  .modifyState (fun _ hupd hn _ => by cases hupd; exact absurd hn (Nat.succ_ne_zero _)) h

/-- A successful move of the balance of a self-destructing account keeps the candidates. -/
private theorem KeepsCandidates.selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeepsCandidates tx tx' := by
  unfold Evm.selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (KeepsCandidates.moveEther h1).trans (KeepsCandidates.setAccountBalance h)
    · cases h
      exact KeepsCandidates.moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (KeepsCandidates.modifyState_of_keeps (fun _ _ hf => credit_keeps hf) h1).trans
      (KeepsCandidates.setAccountBalance h)

/-- A write of storage keeps the candidates. -/
private theorem KeepsCandidates.setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    KeepsCandidates tx tx' := by
  unfold TransactionState.setStorage at h
  split at h
  · cases h
  · cases h
    exact KeepsCandidates.refl tx

/-- A rollback to a snapshot on the same block keeps the candidates of the snapshot. -/
private theorem KeepsCandidates.restoreTxState {tx snapshot : TransactionState}
    (hp : tx.parent = snapshot.parent) : KeepsCandidates snapshot (tx.restoreTxState snapshot) :=
  .of_sameWrites (sameWrites_restoreTxState tx snapshot) hp

/-- A touch of an account keeps the candidates. -/
private theorem KeepsCandidates.touchAccount (tx : TransactionState) (address : Address) :
    KeepsCandidates tx (tx.touchAccount address) := by
  refine ⟨TransactionState.parent_touchAccount tx address, fun x hx => ?_, fun x hn hc => .inr ?_⟩
  · unfold TransactionState.touchAccount
    split
    · exact hx
    · exact hx
  · by_cases hne : x = address
    · subst hne
      rw [TransactionState.getAccount_touchAccount_self] at hn hc
      exact ⟨hn, hc⟩
    · rw [TransactionState.getAccount_touchAccount hne] at hn hc
      exact ⟨hn, hc⟩

/-- Under the condition on candidates, a state that keeps them meets it too. -/
theorem _root_.EthLib.Execution.State.TransactionState.NoNewCandidate.of_keepsCandidates
    {block : BlockState}
    {tx tx' : TransactionState} (hinv : NoNewCandidate block tx) (hk : KeepsCandidates tx tx') :
    NoNewCandidate block tx' := fun x hn hc =>
  (hk.2.2 x hn hc).elim .inl fun ⟨hn', hc'⟩ => (hinv x hn' hc').imp_left (hk.2.1 x)

/-! ## Starts, rollbacks and creations -/

/-- The state that a message enters keeps the candidates of the state it is sent from. -/
private theorem keepsCandidates_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (hentry : Entered fork message state substate entry entrySubstate) :
    KeepsCandidates state entry := by
  have hstart : KeepsCandidates state (startState fork message state) := by
    unfold startState
    split
    · exact .touchAccount state message.currentTarget
    · exact .refl state
  rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact hstart
  · exact hstart.trans (.moveEther hm)

/-- A rollback on error keeps the candidates of the snapshot, when the frame keeps them. -/
private theorem keepsCandidates_rollbackOnError {snapshot : TransactionState}
    {ended : Evm fork Meter} (hk : KeepsCandidates snapshot ended.state) :
    KeepsCandidates snapshot (rollbackOnError snapshot ended).state := by
  unfold rollbackOnError
  split
  · exact .restoreTxState hk.1
  · exact hk

/-- A preparation of a creation keeps the candidates, and wipes the storage of its address. -/
private theorem keepsCandidates_prepareCreation {state prepared : TransactionState}
    {address : Address} (hp : prepareCreation fork state address = .ok prepared) :
    KeepsCandidates state prepared ∧ address ∈ prepared.storageClears := by
  have hwipe : KeepsCandidates state ((state.destroyStorage address).markAccountCreated address) :=
    ⟨rfl, fun x hx => by simp [TransactionState.markAccountCreated,
      TransactionState.destroyStorage, hx], fun x hn hc => .inr ⟨hn, hc⟩⟩
  have hmem : address ∈ ((state.destroyStorage address).markAccountCreated address).storageClears :=
    by simp [TransactionState.markAccountCreated, TransactionState.destroyStorage]
  unfold prepareCreation at hp
  split at hp
  · have h := Base.mapError_ok_iff.mp hp
    have hk := KeepsCandidates.incrementNonce h
    exact ⟨hwipe.trans hk, hk.2.1 _ hmem⟩
  · cases hp
    exact ⟨hwipe, hmem⟩

/-- A write of code at a wiped address keeps the candidates. -/
private theorem keepsCandidates_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (hmem : address ∈ tx.storageClears)
    (h : tx.setCode fork address code = .ok tx') : KeepsCandidates tx tx' := by
  dsimp only [TransactionState.setCode] at h
  split at h
  · exact .modifyState (fun _ _ _ _ => .inl hmem) h
  · have hk := KeepsCandidates.modifyState (h := h) fun _ _ _ _ => .inl (by exact hmem)
    exact KeepsCandidates.trans ⟨rfl, fun _ hx => hx, fun _ hn hc => .inr ⟨hn, hc⟩⟩ hk

/-- A deposit of code keeps the candidates of the state before the creation.

The init code must keep those of the prepared state, and run at the address of the creation. -/
private theorem keepsCandidates_depositCode {state prepared : TransactionState} {address : Address}
    {evm after : Evm fork Meter} (hp : prepareCreation fork state address = .ok prepared)
    (hk : KeepsCandidates prepared evm.state) (ht : evm.message.currentTarget = address)
    (hd : depositCode fork state evm = .ok after) : KeepsCandidates state after.state := by
  obtain ⟨hprep, hmem⟩ := keepsCandidates_prepareCreation hp
  rcases (depositCode_cases hd).2.2 with hs | hs | hs
  · rw [hs]
    exact .restoreTxState (hk.1.trans hprep.1)
  · rw [hs]
    exact hprep.trans hk
  · exact (hprep.trans hk).trans (keepsCandidates_setCode (ht ▸ hk.2.1 _ hmem) hs)

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps the candidates. -/
private theorem keepsCandidates_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    KeepsCandidates evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact .selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-! ## Steps of a frame -/

/-- Each write of a step keeps the candidates, in any frame. -/
theorem stepRules_keepsCandidates :
    StepRules fork (fun a b : Evm fork Meter => KeepsCandidates a.state b.state) where
  trans := KeepsCandidates.trans
  static h := ⟨h.parent, fun _ hx => h.tracker.storageClears ▸ hx,
    fun x hn hc => .inr (getAccount_of_staticStep h x ▸ ⟨hn, hc⟩)⟩
  sstore _ _ _ _ _ _ h := .setStorage h
  tstore _ _ _ _ := ⟨rfl, fun _ hx => hx, fun _ hn hc => .inr ⟨hn, hc⟩⟩
  log _ hs _ _ _ := by rw [hs]; exact .refl _
  selfdestruct _ _ h := keepsCandidates_finishSelfdestruct h
  incrementNonce _ _ _ _ h := .incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-- A step that keeps the candidates, the message and the code. -/
def CandidateStep (a b : Evm fork Meter) : Prop :=
  KeepsCandidates a.state b.state ∧ b.message = a.message ∧ b.code = a.code

/-- A child ends in a state that keeps the candidates of its caller. -/
def CandidateChild (caller : Evm fork Meter) (_message : Message fork)
    (child : Evm fork Meter) : Prop :=
  KeepsCandidates caller.state child.state

/-- Each write of a step keeps the candidates, the message and the code. -/
private theorem stepRules_candidateStep :
    StepRules fork (CandidateStep (fork := fork) (Meter := Meter)) :=
  stepRules_keepsCandidates.and stepRules_messageCode

/-- A step keeps the candidates, its message and its code.

That needs the child it sends to keep the candidates. -/
theorem step_keepsCandidates {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : result.Keeps CandidateStep CandidateChild evm := by
  have r := stepRules_candidateStep.step h
  cases result with
  | next after => exact r
  | child caller message resume =>
    refine ⟨r.1, fun child after hres hc => ?_⟩
    have same := sameContext_of_step_eq_child h hres
    refine ⟨?_, ?_, ?_⟩
    · rw [same.state, state_incorporateChild]
      exact r.1.1.trans hc
    · rw [same.message, message_incorporateChild]
      exact r.1.2.1
    · rw [same.code, code_incorporateChild]
      exact r.1.2.2

/-! ## Messages -/

/-- What a call keeps: the candidates of the state it is sent from, and its message. -/
private def CallKeeps (message : Message fork) (state : TransactionState) (_substate : Substate)
    (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsCandidates state ended.state ∧ ended.message = message

/-- What a creation keeps: the candidates of the state it is sent from. -/
private def CreateKeeps (_message : Message fork) (state : TransactionState)
    (_substate : Substate) (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsCandidates state ended.state

/-- By induction on gas, calls and creations keep the candidates of the state they start from.

A call also keeps its message, so a creation knows where its init code ran. -/
private theorem keepsCandidates_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallKeeps message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreateKeeps message state substate meter ended.val) := by
  have T := stepRules_candidateStep (fork := fork) (Meter := Meter)
  refine processMessage_rel_byKind (R := CandidateStep) (Inv := fun _ => True)
    (Mcall := CallKeeps) (Mcreate := CreateKeeps) T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error)) ?_
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h)) ?_ ?_ n
  · intro evm result _ h
    refine (step_keepsCandidates h).of_child fun {caller message child} hc => ?_
    unfold ChildRelByKind ChildRel at hc
    rcases ht : message.target with _ | target
    · simp only [ht] at hc
      exact hc
    · simp only [ht] at hc
      exact hc.1
  · intro message state entry substate entrySubstate meter ended hentered hrun
    have hk := hrun trivial
    exact ⟨keepsCandidates_rollbackOnError ((keepsCandidates_entered hentered).trans hk.1),
      (message_rollbackOnError state ended).trans hk.2.1⟩
  · intro message state prepared substate meter evm after hprep hmcall hdep
    exact keepsCandidates_depositCode hprep hmcall.1 (congrArg (·.currentTarget) hmcall.2) hdep

/-- A call that returns a frame keeps the candidates of the state it starts from. -/
theorem keepsCandidates_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended) :
    KeepsCandidates state ended.val.state :=
  ((keepsCandidates_induction message.gas).1 message state substate meter held rfl ended h).1

/-- A creation that returns a frame keeps the candidates of the state it starts from. -/
theorem keepsCandidates_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    KeepsCandidates state ended.val.state :=
  (keepsCandidates_induction message.gas).2 message state substate meter held rfl ended h

/-- A call that returns a frame, from a state with no new candidate, ends with none.

A new candidate is still allowed at an address whose storage was wiped. -/
theorem processMessage_noNewCandidate [LawfulGasMeter Meter] {block : BlockState}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hinv : NoNewCandidate block state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    NoNewCandidate block ended.val.state :=
  hinv.of_keepsCandidates (keepsCandidates_processMessage h)

/-- A creation that returns a frame, from a state with no new candidate, ends with none.

A new candidate is still allowed at an address whose storage was wiped. -/
theorem processCreateMessage_noNewCandidate [LawfulGasMeter Meter] {block : BlockState}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hinv : NoNewCandidate block state)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    NoNewCandidate block ended.val.state :=
  hinv.of_keepsCandidates (keepsCandidates_processCreateMessage h)

end EthLib.Execution.Evm

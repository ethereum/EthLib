module

public import EthLib.Execution.Proofs.Evm.Call.Nonce

/-!
# Proofs: no message deletes an account that holds a nonce or code

An account is settled when it exists, and from Paris also holds a nonce or code.

Within a run, a change deletes an account only when it leaves it empty, and only from Paris.

No step lowers a nonce, and only the deposit of code changes a code hash.

That deposit goes to a new account, which from Spurious Dragon holds a nonce of at least 1.

A frame that fails rolls back to its snapshot, where every settled account of its start is settled.

So every settled account stays settled through every call and creation.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (Account EMPTY_CODE_HASH StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Whether an address has an account, which from Paris must also hold a nonce or code.

No call or creation deletes such an account. -/
def Settled (fork : Fork) (tx : TransactionState) (address : Address) : Prop :=
  ∃ account, tx.getAccountOptional address = some account ∧
    (fork < .paris ∨ account.nonce ≠ 0 ∨ account.codeHash ≠ EMPTY_CODE_HASH)

/-- Whether every address settled in the first state is settled in the second. -/
def SettledLe (fork : Fork) (tx tx' : TransactionState) : Prop :=
  ∀ address, Settled fork tx address → Settled fork tx' address

/-! ## The order of settled accounts -/

/-- A state has every settled account of itself. -/
theorem SettledLe.refl (tx : TransactionState) : SettledLe fork tx tx := fun _ h => h

/-- Two changes that each keep every settled account keep them together. -/
theorem SettledLe.trans {a b c : TransactionState} (hab : SettledLe fork a b)
    (hbc : SettledLe fork b c) : SettledLe fork a c :=
  fun address h => hbc address (hab address h)

/-- A state with the accounts of another has its settled accounts. -/
theorem SettledLe.of_getAccountOptional {tx tx' : TransactionState}
    (h : ∀ address, tx'.getAccountOptional address = tx.getAccountOptional address) :
    SettledLe fork tx tx' :=
  fun address ⟨account, ha, hp⟩ => ⟨account, (h address).trans ha, hp⟩

/-- An address whose account reads with a nonce or code is settled, at every fork. -/
theorem settled_of_getAccount {tx : TransactionState} {address : Address}
    (h : (tx.getAccount address).nonce ≠ 0 ∨
      (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH) : Settled fork tx address := by
  unfold TransactionState.getAccount at h
  cases ha : tx.getAccountOptional address with
  | none =>
    rw [ha] at h
    exact absurd h (by simp [State.EMPTY_ACCOUNT])
  | some account =>
    rw [ha] at h
    exact ⟨account, ha, .inr h⟩

/-- From Paris, a settled address has an account that holds a nonce or code. -/
theorem Settled.getAccount {tx : TransactionState} {address : Address}
    (h : Settled fork tx address) (hfork : .paris ≤ fork) :
    (tx.getAccount address).nonce ≠ 0 ∨ (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH := by
  obtain ⟨account, ha, hp⟩ := h
  unfold TransactionState.getAccount
  rw [ha]
  exact hp.resolve_left fun hlt => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hfork)

/-! ## The writes of the state -/

/-- A change of one account keeps every settled account when it keeps that account settled.

From Paris, the change must leave that account with a nonce or code if it was settled. -/
theorem settledLe_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ account', f (tx.getAccount address) = .ok account' → Settled fork tx address →
      .paris ≤ fork → account'.nonce ≠ 0 ∨ account'.codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.modifyState fork address f = .ok tx') : SettledLe fork tx tx' := by
  intro other hs
  by_cases hne : other = address
  · subst hne
    obtain ⟨account', hfa, hself, -⟩ := TransactionState.modifyState_eq_ok h
    rcases Nat.lt_or_ge fork.ctorIdx Fork.paris.ctorIdx with hlt | hge
    · exact ⟨account', TransactionState.getAccountOptional_modifyState hlt hfa h, .inl hlt⟩
    · apply settled_of_getAccount
      rw [hself]
      exact hf _ hfa hs hge
  · obtain ⟨account, ha, hp⟩ := hs
    exact ⟨account, (TransactionState.getAccountOptional_modifyState_of_ne h hne).trans ha, hp⟩

/-- A change of one account that keeps its code and lowers no nonce keeps every settled account. -/
theorem settledLe_modifyState_of_keeps {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ account account', f account = .ok account' →
      account.nonce ≤ account'.nonce ∧ account'.codeHash = account.codeHash)
    (h : tx.modifyState fork address f = .ok tx') : SettledLe fork tx tx' :=
  settledLe_modifyState (fun account' hfa hs hfork => by
    obtain ⟨hn, hc⟩ := hf _ _ hfa
    rcases hs.getAccount hfork with h0 | h0
    · exact .inl (by omega)
    · exact .inr (hc ▸ h0)) h

/-- A debit keeps the nonce and the code. -/
private theorem debit_keeps {address : Address} {amount : U256} {account account' : Account}
    (h : Account.debit address amount account = .ok account') :
    account.nonce ≤ account'.nonce ∧ account'.codeHash = account.codeHash := by
  unfold Account.debit at h
  split at h <;> cases h
  exact ⟨Nat.le_refl _, rfl⟩

/-- A credit keeps the nonce and the code. -/
private theorem credit_keeps {address : Address} {amount : U256} {account account' : Account}
    (h : Account.credit address amount account = .ok account') :
    account.nonce ≤ account'.nonce ∧ account'.codeHash = account.codeHash := by
  unfold Account.credit at h
  split at h <;> cases h
  exact ⟨Nat.le_refl _, rfl⟩

/-- A move of ether keeps every settled account. -/
theorem settledLe_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    SettledLe fork tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (settledLe_modifyState_of_keeps (fun _ _ => debit_keeps) h1).trans
    (settledLe_modifyState_of_keeps (fun _ _ => credit_keeps) h2)

/-- A creation of ether keeps every settled account. -/
theorem settledLe_createEther {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.createEther fork address amount = .ok tx') : SettledLe fork tx tx' :=
  settledLe_modifyState_of_keeps (fun _ _ => credit_keeps) h

/-- A new balance keeps every settled account. -/
theorem settledLe_setAccountBalance {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    SettledLe fork tx tx' :=
  settledLe_modifyState_of_keeps (fun _ _ hf => by cases hf; exact ⟨Nat.le_refl _, rfl⟩) h

/-- A raise of one nonce keeps every settled account. -/
theorem settledLe_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : SettledLe fork tx tx' :=
  settledLe_modifyState_of_keeps (fun _ _ hf => by cases hf; exact ⟨Nat.le_succ _, rfl⟩) h

/-- A new code keeps every settled account when, from Paris, its address has a nonce. -/
theorem settledLe_setCode {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (hn : .paris ≤ fork → (tx.getAccount address).nonce ≠ 0)
    (h : tx.setCode fork address code = .ok tx') : SettledLe fork tx tx' := by
  dsimp only [TransactionState.setCode] at h
  split at h <;>
  · have hk := settledLe_modifyState ?_ h
    · exact (SettledLe.of_getAccountOptional fun _ => rfl).trans hk
    · intro _ hfa _ hfork
      cases hfa
      exact .inl (hn hfork)

/-- A write of storage keeps every settled account. -/
theorem settledLe_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') : SettledLe fork tx tx' :=
  SettledLe.of_getAccountOptional fun _ => TransactionState.getAccountOptional_setStorage h

/-- A touch of an account keeps every settled account. -/
theorem settledLe_touchAccount (tx : TransactionState) (address : Address) :
    SettledLe fork tx (tx.touchAccount address) := by
  unfold TransactionState.touchAccount
  split
  · exact SettledLe.refl _
  · rename_i hnot
    intro other ⟨account, ha, hp⟩
    by_cases hne : other = address
    · subst hne
      simp [TransactionState.accountExists, ha] at hnot
    · exact ⟨account, (TransactionState.getAccountOptional_setAccount_of_ne _ _ hne).trans ha, hp⟩

/-- A rollback to a snapshot of the same block keeps every settled account of the snapshot. -/
theorem settledLe_restoreTxState {tx snapshot : TransactionState}
    (h : tx.parent = snapshot.parent) : SettledLe fork snapshot (tx.restoreTxState snapshot) :=
  SettledLe.of_getAccountOptional (TransactionState.getAccountOptional_restoreTxState h)

/-- A successful move of the balance of a destroyed account keeps every settled account. -/
theorem settledLe_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    SettledLe fork tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (settledLe_moveEther h1).trans (settledLe_setAccountBalance h)
    · cases h
      exact settledLe_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (settledLe_createEther h1).trans (settledLe_setAccountBalance h)

/-- A successful preparation of a creation keeps every settled account. -/
theorem settledLe_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : SettledLe fork tx tx' := by
  unfold prepareCreation at h
  have h0 : SettledLe fork tx ((tx.destroyStorage address).markAccountCreated address) :=
    SettledLe.of_getAccountOptional fun _ => rfl
  split at h
  · exact h0.trans (settledLe_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact h0

/-- From Spurious Dragon, a successful preparation of a creation gives the new address a nonce. -/
theorem nonce_ne_zero_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') (hfork : .spuriousDragon ≤ fork) :
    (tx'.getAccount address).nonce ≠ 0 := by
  unfold prepareCreation at h
  split at h
  · rw [(TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp h)).1]
    exact Nat.succ_ne_zero _
  · contradiction

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT keeps every settled account. -/
theorem settledLe_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    SettledLe fork evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact settledLe_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-! ## A step -/

/-- Each write of a step keeps every settled account, static frame or not. -/
theorem stepRules_settledLe :
    StepRules fork (fun a b : Evm fork Meter => SettledLe fork a.state b.state) where
  trans := SettledLe.trans
  static h := SettledLe.of_getAccountOptional fun address =>
    (h.state address List.not_mem_nil).1
  sstore _ _ _ _ _ _ h := settledLe_setStorage h
  tstore _ _ _ _ := SettledLe.of_getAccountOptional fun _ => rfl
  log _ hs _ _ _ := by rw [hs]; exact SettledLe.refl _
  selfdestruct _ _ h := settledLe_finishSelfdestruct h
  incrementNonce _ _ _ _ h := settledLe_incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-- Whether the second frame keeps the settled accounts, the nonces and the block of the first. -/
private abbrev SettledStep (a b : Evm fork Meter) : Prop :=
  (SettledLe fork a.state b.state ∧ NonceLe a.state b.state) ∧ b.state.parent = a.state.parent

/-- Each write of a step keeps the settled accounts, the nonces and the block of the state. -/
private theorem stepRules_settledStep :
    StepRules fork (SettledStep (fork := fork) (Meter := Meter)) :=
  (stepRules_settledLe.and stepRules_nonceLe).and stepRules_parent

/-! ## Messages -/

/-- What a creation keeps: the settled accounts, the nonces and the block of the state. -/
private def CreateSettled (_message : Message fork) (state : TransactionState)
    (_substate : Substate) (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  (SettledLe fork state ended.state ∧ NonceLe state ended.state) ∧
    ended.state.parent = state.parent

/-- What a call keeps: what a creation keeps, and its message. -/
private def CallSettled (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : Meter) (ended : Evm fork Meter) : Prop :=
  CreateSettled message state substate meter ended ∧ ended.message = message

/-- The state that a message starts its frame from keeps every settled account. -/
theorem settledLe_startState (message : Message fork) (state : TransactionState) :
    SettledLe fork state (startState fork message state) := by
  unfold startState
  split
  · exact settledLe_touchAccount _ _
  · exact SettledLe.refl _

/-- The state that a message enters keeps the settled accounts, the nonces and the block. -/
theorem settledLe_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    (SettledLe fork state entry ∧ NonceLe state entry) ∧ entry.parent = state.parent := by
  refine ⟨?_, parent_entered h⟩
  rcases h with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact ⟨settledLe_startState message state, nonceLe_startState message state⟩
  · exact ⟨(settledLe_startState message state).trans (settledLe_moveEther hm),
      (nonceLe_startState message state).trans (nonceLe_moveEther hm)⟩

/-- By induction on gas, calls and creations keep the settled accounts, the nonces and the block.

A call also keeps its message, so a creation knows where its init code ran. -/
private theorem processMessage_settled_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallSettled message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreateSettled message state substate meter ended.val) := by
  have T := (stepRules_settledStep (fork := fork) (Meter := Meter)).and stepRules_messageCode
  refine processMessage_rel_byKind
    (R := fun a b => SettledStep a b ∧ b.message = a.message ∧ b.code = a.code)
    (Inv := fun _ => True)
    (Mcall := CallSettled) (Mcreate := CreateSettled) T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error)) ?_
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h)) ?_ ?_ n
  · intro evm result _ h
    have r := T.step h
    cases result with
    | next after => exact r
    | child caller message resume =>
      refine ⟨r.1, fun child after hres hc => ?_⟩
      have same := sameContext_of_step_eq_child h hres
      have hk : CreateSettled message caller.state caller.substate.child
          (GasMeter.start message.gas message.reservoir) child := by
        unfold ChildRelByKind ChildRel at hc
        split at hc
        · exact hc.1
        · exact hc
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · rw [same.state, state_incorporateChild]
        exact r.1.1.1.1.trans hk.1.1
      · rw [same.state, state_incorporateChild]
        exact r.1.1.1.2.trans hk.1.2
      · rw [same.state, state_incorporateChild]
        exact hk.2.trans r.1.1.2
      · rw [same.message, message_incorporateChild]
        exact r.1.2.1
      · rw [same.code, code_incorporateChild]
        exact r.1.2.2
  · intro message state entry substate entrySubstate meter ended hentered hrun
    obtain ⟨⟨⟨hs, hn⟩, hp⟩, hm, -⟩ := hrun trivial
    obtain ⟨⟨hs0, hn0⟩, hp0⟩ := settledLe_entered hentered
    have hpar : ended.state.parent = state.parent := hp.trans hp0
    refine ⟨⟨⟨?_, ?_⟩, (parent_rollbackOnError state ended).trans hpar⟩,
      (message_rollbackOnError state ended).trans hm⟩
    · unfold rollbackOnError
      split
      · exact settledLe_restoreTxState hpar
      · exact hs0.trans hs
    · unfold rollbackOnError
      split
      · exact nonceLe_restoreTxState hpar
      · exact hn0.trans hn
  · intro message state prepared substate meter evm after hprep hmcall hdep
    obtain ⟨⟨⟨hs, hn⟩, hp⟩, hm⟩ := hmcall
    have hpar : evm.state.parent = state.parent := hp.trans (parent_prepareCreation hprep)
    have hn' := (nonceLe_prepareCreation hprep).trans hn
    refine ⟨⟨?_, nonceLe_depositCode hn' hpar hdep⟩, (parent_depositCode hdep).trans hpar⟩
    rcases (depositCode_cases hdep).2.2 with hst | hst | hst
    · rw [hst]
      exact settledLe_restoreTxState hpar
    · rw [hst]
      exact (settledLe_prepareCreation hprep).trans hs
    · refine ((settledLe_prepareCreation hprep).trans hs).trans (settledLe_setCode ?_ hst)
      intro hfork
      have h1 := nonce_ne_zero_prepareCreation hprep (Nat.le_trans (by decide) hfork)
      have h2 := hn message.currentTarget
      rw [hm]
      omega

/-- A call that returns a frame keeps every settled account, whether or not the frame fails. -/
theorem settledLe_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    SettledLe fork state ended.val.state :=
  ((processMessage_settled_induction message.gas).1 message state substate meter held rfl ended
    h).1.1.1

/-- A creation that returns a frame keeps every settled account, whether or not the frame fails. -/
theorem settledLe_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    SettledLe fork state ended.val.state :=
  ((processMessage_settled_induction message.gas).2 message state substate meter held rfl ended
    h).1.1

end EthLib.Execution.Evm

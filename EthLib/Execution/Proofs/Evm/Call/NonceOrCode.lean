module

public import EthLib.Execution.Proofs.Evm.Call.Rebuild

/-!
# Proofs: every message from Spurious Dragon keeps each nonce or code

An account has a nonce or code when its nonce is positive or it holds code.

A step lowers no nonce, and changes the code of no account.

A step deletes an account only when it is empty, so the account had no nonce and no code.

So every step keeps a nonce or code wherever there is one.

From Spurious Dragon, a creation raises the nonce of its address to 1 before it deposits code there.

So the code it deposits, even empty code, leaves a nonce at the address.

Before Spurious Dragon, empty code deposited at an address with code and nonce 0 leaves neither.

So the theorems below start at Spurious Dragon.

A rollback restores the accounts of a snapshot, which kept a nonce or code wherever it had one.

So from Spurious Dragon, every call and creation keeps a nonce or code wherever there is one.

That holds whatever the state, and whether or not the message ends with an error.

The rebuild property of the state is not needed.

[EIP-161][eip161] starts the nonce of a new account at 1.

[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (Account StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes of the state -/

/-- A state with the accounts of another keeps each nonce or code of it. -/
private theorem keepsNonceOrCode_of_getAccountOptional {tx tx' : TransactionState}
    (h : ∀ address, tx'.getAccountOptional address = tx.getAccountOptional address) :
    KeepsNonceOrCode tx tx' :=
  ⟨NonceLe.of_getAccountOptional h, fun address hc =>
    (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [h])).mpr hc⟩

/-- A change of an account that keeps its nonce and its code keeps each nonce or code.

From Paris, such a change may delete an empty account, which had no nonce and no code. -/
theorem keepsNonceOrCode_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.nonce = (tx.getAccount address).nonce ∧
        account.codeHash = (tx.getAccount address).codeHash) :
    KeepsNonceOrCode tx tx' := by
  obtain ⟨account, hf, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  obtain ⟨hn, hc⟩ := keeps account hf
  -- The changed account reads with the nonce and the code hash it had; the others are kept.
  have hacc : ∀ other, (tx'.getAccount other).nonce = (tx.getAccount other).nonce ∧
      (tx'.getAccount other).codeHash = (tx.getAccount other).codeHash := by
    intro other
    by_cases hne : other = address
    · subst hne
      rw [hself]
      exact ⟨hn, hc⟩
    · rw [hother other hne]
      exact ⟨rfl, rfl⟩
  refine ⟨fun other => (hacc other).1 ▸ Nat.le_refl _, fun other hnc => ?_⟩
  unfold HasNonceOrCode
  rw [(hacc other).1, (hacc other).2]
  exact hnc

/-- A move of ether keeps each nonce or code. -/
theorem keepsNonceOrCode_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    KeepsNonceOrCode tx tx' := by
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  -- The debit and the credit each keep the nonce and the code hash of the account they change.
  refine (keepsNonceOrCode_modifyState h1 fun account hf => ?_).trans
    (keepsNonceOrCode_modifyState h2 fun account hf => ?_)
  · unfold Account.debit at hf
    split at hf <;> cases hf
    exact ⟨rfl, rfl⟩
  · unfold Account.credit at hf
    split at hf <;> cases hf
    exact ⟨rfl, rfl⟩

/-- The move of the balance of an account by SELFDESTRUCT keeps each nonce or code. -/
theorem keepsNonceOrCode_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeepsNonceOrCode tx tx' := by
  -- A new balance keeps the nonce and the code hash of the account.
  have hbal : ∀ {s s' : TransactionState} {amount : U256},
      s.setAccountBalance fork originator amount = .ok s' → KeepsNonceOrCode s s' :=
    fun h => keepsNonceOrCode_modifyState h fun _ hf => by cases hf; exact ⟨rfl, rfl⟩
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (keepsNonceOrCode_moveEther h1).trans (hbal h)
    · cases h
      exact keepsNonceOrCode_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    -- A creation of ether is a credit, which keeps the nonce and the code hash.
    have k1 : KeepsNonceOrCode tx mid := keepsNonceOrCode_modifyState h1 fun account hf => by
      unfold Account.credit at hf
      split at hf <;> cases hf
      exact ⟨rfl, rfl⟩
    exact k1.trans (hbal h)

/-- The rise of a nonce keeps each nonce or code. -/
theorem keepsNonceOrCode_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : KeepsNonceOrCode tx tx' := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h
  refine ⟨nonceLe_incrementNonce h, fun other hnc => ?_⟩
  by_cases hne : other = address
  · -- The raised nonce is positive.
    subst hne
    left
    rw [hself]
    exact Nat.succ_le_of_lt (Nat.succ_pos _)
  · exact (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [hother other hne])).mpr
      hnc

/-- New code at an account with a nonce keeps each nonce or code. -/
theorem keepsNonceOrCode_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (hnonce : 1 ≤ (tx.getAccount address).nonce)
    (h : tx.setCode fork address code = .ok tx') : KeepsNonceOrCode tx tx' := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_setCode h
  refine ⟨nonceLe_setCode h, fun other hnc => ?_⟩
  by_cases hne : other = address
  · -- The account keeps its positive nonce.
    subst hne
    left
    rw [hself]
    exact hnonce
  · exact (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [hother other hne])).mpr
      hnc

/-- The start of a creation keeps each nonce or code. -/
theorem keepsNonceOrCode_prepareCreation {state prepared : TransactionState} {address : Address}
    (h : prepareCreation fork state address = .ok prepared) : KeepsNonceOrCode state prepared := by
  unfold prepareCreation at h
  -- The wipe of storage and the record of the creation keep every account.
  have h0 : KeepsNonceOrCode state ((state.destroyStorage address).markAccountCreated address) :=
    keepsNonceOrCode_of_getAccountOptional fun _ => rfl
  split at h
  · exact h0.trans (keepsNonceOrCode_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact h0

/-- The state that a message enters keeps each nonce or code of the state it is sent from. -/
theorem keepsNonceOrCode_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    KeepsNonceOrCode state entry := by
  -- The start state touches at most the target, which keeps every account.
  have hstart : KeepsNonceOrCode state (startState fork message state) := by
    unfold startState
    split
    · refine ⟨nonceLe_touchAccount _ _, fun other hnc => (HasNonceOrCode.congr ?_).mpr hnc⟩
      by_cases hne : other = message.currentTarget
      · subst hne
        exact TransactionState.getAccount_touchAccount_self _ _
      · exact TransactionState.getAccount_touchAccount hne
    · exact .refl _
  rcases h with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact hstart
  · exact hstart.trans (keepsNonceOrCode_moveEther hm)

/-! ## A step -/

/-- Each write of a step keeps each nonce or code, static frame or not. -/
theorem stepRules_keepsNonceOrCode :
    StepRules fork (fun a b : Evm fork Meter => KeepsNonceOrCode a.state b.state) where
  trans := KeepsNonceOrCode.trans
  static h := keepsNonceOrCode_of_getAccountOptional fun address =>
    (h.state address List.not_mem_nil).1
  sstore _ _ _ _ _ _ h := keepsNonceOrCode_of_getAccountOptional fun _ =>
    TransactionState.getAccountOptional_setStorage h
  tstore _ _ _ _ := keepsNonceOrCode_of_getAccountOptional fun _ => rfl
  log _ hs _ _ _ := by rw [hs]; exact .refl _
  selfdestruct _ _ h := by
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact keepsNonceOrCode_selfdestructTransfer (Base.mapError_ok_iff.mp hst)
  incrementNonce _ _ _ _ h := keepsNonceOrCode_incrementNonce h
  incorporate h := by rw [state_incorporateChild]; exact h

/-! ## Messages -/

/-- A rollback to a snapshot keeps each nonce or code of it, when the frame kept them.

The frame must keep the block of the state it entered, and that state the block of the snapshot. -/
private theorem keepsNonceOrCode_rollbackOnError {state entry : TransactionState}
    {ended : Evm fork Meter} (hentry : KeepsNonceOrCode state entry)
    (hpe : entry.parent = state.parent) (hrun : KeepsNonceOrCode entry ended.state)
    (hpr : ended.state.parent = entry.parent) :
    KeepsNonceOrCode state (rollbackOnError state ended).state := by
  unfold rollbackOnError
  split
  · -- The restored state has the accounts of the snapshot.
    exact (sameWrites_restoreTxState ended.state state).keepsNonceOrCode (hpr.trans hpe)
  · exact hentry.trans hrun

/-- From Spurious Dragon, a deposit of code keeps each nonce or code of the state before a creation.

The init code must run at the address of the creation.

It must keep each nonce or code and the block. -/
private theorem keepsNonceOrCode_depositCode (hfork : .spuriousDragon ≤ fork)
    {state prepared : TransactionState} {address : Address} {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hk : KeepsNonceOrCode prepared evm.state) (hpar : evm.state.parent = prepared.parent)
    (htarget : evm.message.currentTarget = address)
    (hd : depositCode fork state evm = .ok after) : KeepsNonceOrCode state after.state := by
  have k0 := keepsNonceOrCode_prepareCreation hp
  -- From Spurious Dragon, the address of the creation has a positive nonce once prepared.
  have hnonce : 1 ≤ (prepared.getAccount address).nonce := by
    unfold prepareCreation at hp
    simp only [show fork ≥ .spuriousDragon from hfork, ↓reduceIte] at hp
    rw [(TransactionState.getAccount_incrementNonce (Base.mapError_ok_iff.mp hp)).1]
    exact Nat.succ_le_of_lt (Nat.succ_pos _)
  rcases (depositCode_cases hd).2.2 with hs | hs | hs
  · -- The restored state has the accounts of the state before the creation.
    rw [hs]
    exact (sameWrites_restoreTxState evm.state state).keepsNonceOrCode
      (hpar.trans (parent_prepareCreation hp))
  · rw [hs]
    exact k0.trans hk
  · -- The code goes to the address of the creation, whose nonce stays positive.
    refine (k0.trans hk).trans (keepsNonceOrCode_setCode ?_ hs)
    rw [htarget]
    exact Nat.le_trans hnonce (hk.1 address)

/-- A frame that keeps each nonce or code and the block, with its message and code. -/
private abbrev KeepsFrame (a b : Evm fork Meter) : Prop :=
  (KeepsNonceOrCode a.state b.state ∧ b.state.parent = a.state.parent) ∧
    b.message = a.message ∧ b.code = a.code

/-- A call that keeps each nonce or code and the block, and ends with its own message. -/
private abbrev KeepsCall (message : Message fork) (state : TransactionState) (_ : Substate)
    (_ : Meter) (ended : Evm fork Meter) : Prop :=
  (KeepsNonceOrCode state ended.state ∧ ended.state.parent = state.parent) ∧
    ended.message = message

/-- A creation that keeps each nonce or code and the block. -/
private abbrev KeepsCreate (_ : Message fork) (state : TransactionState) (_ : Substate)
    (_ : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsNonceOrCode state ended.state ∧ ended.state.parent = state.parent

/-- A child, a call or a creation, keeps each nonce or code and the block of its caller. -/
private theorem keeps_of_childRelByKind {caller child : Evm fork Meter} {message : Message fork}
    (h : ChildRelByKind (Meter := Meter) KeepsCall KeepsCreate caller message child) :
    KeepsNonceOrCode caller.state child.state ∧ child.state.parent = caller.state.parent := by
  unfold ChildRelByKind ChildRel at h
  split at h
  · exact h.1
  · exact h

/-- A frame that resumes after a message keeps each nonce or code and the block of the frame before.

It also keeps its message and its code. -/
private theorem keepsFrame_resume {evm caller child after : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (resumed : resume child = .ok after)
    (hcaller : KeepsFrame evm caller)
    (hchild : ChildRelByKind (Meter := Meter) KeepsCall KeepsCreate caller message child) :
    KeepsFrame evm after := by
  have same := sameContext_of_step_eq_child h resumed
  obtain ⟨hk, hp⟩ := keeps_of_childRelByKind hchild
  -- The frame that resumes has the state of the child, and the message and code of the caller.
  have hs : after.state = child.state :=
    same.state.trans (state_incorporateChild caller child)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hs]
    exact hcaller.1.1.trans hk
  · rw [hs]
    exact hp.trans hcaller.1.2
  · rw [same.message, message_incorporateChild]
    exact hcaller.2.1
  · rw [same.code, code_incorporateChild]
    exact hcaller.2.2

/-- From Spurious Dragon, every call and creation keeps each nonce or code.

That holds whether or not the message ends with an error.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_keepsNonceOrCode_induction [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        KeepsNonceOrCode state ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        KeepsNonceOrCode state ended.val.state) := by
  have T := ((stepRules_keepsNonceOrCode (fork := fork) (Meter := Meter)).and
    stepRules_parent).and stepRules_messageCode
  -- Each step keeps the relation, a message it sends included.
  have steps : ∀ {evm : Evm fork Meter} {result : StepResult fork Meter}, True →
      step fork evm = .ok result →
      StepResult.Keeps KeepsFrame (ChildRelByKind KeepsCall KeepsCreate) evm result := by
    intro evm result _ h
    have r := T.step h
    cases result with
    | next after => exact r
    | child caller message resume =>
      exact ⟨r.1, fun child after hres hc => keepsFrame_resume h hres r.1 hc⟩
  have both := processMessage_rel_byKind (fork := fork) (Meter := Meter)
    (R := KeepsFrame) (Inv := fun _ => True) (Mcall := KeepsCall) (Mcreate := KeepsCreate)
    T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error))
    steps
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h))
    (fun {_ state _ _ _ _ ended} hentry hrun =>
      ⟨⟨keepsNonceOrCode_rollbackOnError (keepsNonceOrCode_entered hentry)
          (parent_entered hentry) (hrun trivial).1.1 (hrun trivial).1.2,
        (parent_rollbackOnError state ended).trans
          ((hrun trivial).1.2.trans (parent_entered hentry))⟩,
        (message_rollbackOnError state ended).trans (hrun trivial).2.1⟩)
    (fun hp hm hd => ⟨keepsNonceOrCode_depositCode hfork hp hm.1.1 hm.1.2
        (congrArg (·.currentTarget) hm.2) hd,
      (parent_depositCode hd).trans (hm.1.2.trans (parent_prepareCreation hp))⟩)
    n
  exact ⟨fun message state substate meter held hn ended h =>
      (both.1 message state substate meter held hn ended h).1.1,
    fun message state substate meter held hn ended h =>
      (both.2 message state substate meter held hn ended h).1⟩

/-- From Spurious Dragon, a call keeps each nonce or code.

It lowers no nonce, and keeps a nonce or code wherever there is one.

That holds whether or not it ends with an error. -/
theorem keepsNonceOrCode_processMessage [LawfulGasMeter Meter] (hfork : .spuriousDragon ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    KeepsNonceOrCode state ended.val.state :=
  (processMessage_keepsNonceOrCode_induction hfork message.gas).1 message state substate meter
    held rfl ended h

/-- From Spurious Dragon, a creation keeps each nonce or code.

It lowers no nonce, and keeps a nonce or code wherever there is one.

That holds whether or not it ends with an error. -/
theorem keepsNonceOrCode_processCreateMessage [LawfulGasMeter Meter]
    (hfork : .spuriousDragon ≤ fork) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    KeepsNonceOrCode state ended.val.state :=
  (processMessage_keepsNonceOrCode_induction hfork message.gas).2 message state substate meter
    held rfl ended h

end EthLib.Execution.Evm

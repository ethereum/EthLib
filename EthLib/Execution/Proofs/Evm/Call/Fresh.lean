module

public import EthLib.Execution.Proofs.Evm.Call.Nonce
public import EthLib.Execution.Proofs.Evm.Call.ToDelete

/-!
# Proofs: a message creates only accounts with nonce 0, and gives code only to those

Each write of a step keeps the created accounts of its transaction.

No step gives code to an account without code.

A creation adds its own address to the created accounts.

The step that sends a creation checks first that its address has nonce 0 and no code.

The deposit of code then gives code to that address only.

So an account that a message creates had nonce 0 when the message started.

The one exception is the address of a creation itself, which its sender checked before.

An account that a message does not create keeps an empty code.

No nonce drops, so an account with a nonce is never created by a message.

These facts hold at every fork, whether or not the message ends with an error.

The proofs about transactions use them for the sender, which has a nonce once it pays for gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A step -/

/-- The second state has the created accounts of the first.

It gives code to no account without code. -/
def NoNewCode (tx tx' : TransactionState) : Prop :=
  tx'.createdAccounts = tx.createdAccounts ∧
    ∀ address, (tx.getAccount address).codeHash = EMPTY_CODE_HASH →
      (tx'.getAccount address).codeHash = EMPTY_CODE_HASH

/-- A state keeps its created accounts and its accounts without code. -/
theorem NoNewCode.refl (tx : TransactionState) : NoNewCode tx tx :=
  ⟨rfl, fun _ h => h⟩

/-- Two steps that each keep the created accounts and give no code keep them together. -/
theorem NoNewCode.trans {a b c : TransactionState} (hab : NoNewCode a b) (hbc : NoNewCode b c) :
    NoNewCode a c :=
  ⟨hbc.1.trans hab.1, fun address h => hbc.2 address (hab.2 address h)⟩

/-- A state with the accounts and the created accounts of another gives no code. -/
private theorem NoNewCode.of_getAccount {tx tx' : TransactionState}
    (hc : tx'.createdAccounts = tx.createdAccounts)
    (h : ∀ address, tx'.getAccount address = tx.getAccount address) : NoNewCode tx tx' :=
  ⟨hc, fun address hcode => by rw [h address]; exact hcode⟩

/-- A write of storage gives no code. -/
private theorem noNewCode_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Base.Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    NoNewCode tx tx' :=
  .of_getAccount (TransactionState.createdAccounts_setStorage h) fun _ => by
    unfold TransactionState.getAccount
    rw [TransactionState.getAccountOptional_setStorage h]

/-- A change of one account that keeps its code hash gives no code. -/
private theorem noNewCode_modifyState {tx tx' : TransactionState} {address : Address}
    {f : State.Account → Except State.StateError State.Account}
    (hf : ∀ account account', f account = .ok account' → account'.codeHash = account.codeHash)
    (h : tx.modifyState fork address f = .ok tx') : NoNewCode tx tx' := by
  refine ⟨TransactionState.createdAccounts_modifyState h, fun other hcode => ?_⟩
  obtain ⟨account, hfa, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  by_cases hne : other = address
  · subst hne
    rw [hself, hf _ _ hfa]
    exact hcode
  · rw [hother other hne]
    exact hcode

/-- A move of ether gives no code. -/
private theorem noNewCode_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    NoNewCode tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  refine (noNewCode_modifyState (fun _ _ hf => ?_) h1).trans
    (noNewCode_modifyState (fun _ _ hf => ?_) h2)
  · unfold State.Account.debit at hf
    split at hf <;> cases hf
    rfl
  · unfold State.Account.credit at hf
    split at hf <;> cases hf
    rfl

/-- A successful move of the balance of a destroyed account gives no code. -/
private theorem noNewCode_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') : NoNewCode tx tx' := by
  have hset : ∀ {a b : TransactionState} {address : Address} {amount : U256},
      a.setAccountBalance fork address amount = .ok b → NoNewCode a b :=
    fun h => noNewCode_modifyState (fun _ _ hf => by cases hf; rfl) h
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (noNewCode_moveEther h1).trans (hset h)
    · cases h
      exact noNewCode_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    refine (noNewCode_modifyState (fun _ _ hf => ?_) h1).trans (hset h)
    unfold State.Account.credit at hf
    split at hf <;> cases hf
    rfl

omit [GasMeter Meter] in
/-- The end of a successful SELFDESTRUCT gives no code. -/
private theorem noNewCode_finishSelfdestruct {beneficiary : Address} {refund : Nat}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    NoNewCode evm.state after.state := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact noNewCode_selfdestructTransfer (Base.mapError_ok_iff.mp hst)

/-- Each write of a step keeps the created accounts, and gives code to no account. -/
theorem stepRules_noNewCode :
    StepRules fork (fun a b : Evm fork Meter => NoNewCode a.state b.state) where
  trans := NoNewCode.trans
  static h := .of_getAccount h.created (getAccount_of_staticStep h)
  sstore _ _ _ _ _ _ h := noNewCode_setStorage h
  tstore _ _ _ _ := ⟨rfl, fun _ h => h⟩
  log _ hs _ _ _ := by rw [hs]; exact NoNewCode.refl _
  selfdestruct _ _ h := noNewCode_finishSelfdestruct h
  incrementNonce _ _ _ h := noNewCode_modifyState (fun _ _ hf => by cases hf; rfl) h
  incorporate h := by rw [state_incorporateChild]; exact h

/-! ## The relation -/

/-- From the first state to the second, every account created is fresh or allowed.

No nonce drops, the block stays, and every account created in the first stays created.

Each account created in the second but not the first had nonce 0 in the first, or is `allowed`.

An account without code in the first has none in the second, unless the second created it. -/
structure CreatesFresh (allowed : Address → Prop) (tx tx' : TransactionState) : Prop where
  /-- No nonce drops. -/
  nonce : NonceLe tx tx'
  /-- The block stays. -/
  parent : tx'.parent = tx.parent
  /-- Every account created in the first state stays created. -/
  created : CreatedLe tx tx'
  /-- Each new created account had nonce 0, or is allowed. -/
  fresh : ∀ address ∈ tx'.createdAccounts, address ∉ tx.createdAccounts →
    (tx.getAccount address).nonce = 0 ∨ allowed address
  /-- An account without code gets none, unless it is created. -/
  code : ∀ address, address ∉ tx'.createdAccounts →
    (tx.getAccount address).codeHash = EMPTY_CODE_HASH →
      (tx'.getAccount address).codeHash = EMPTY_CODE_HASH

/-- A state creates nothing from itself. -/
theorem CreatesFresh.refl (allowed : Address → Prop) (tx : TransactionState) :
    CreatesFresh allowed tx tx :=
  ⟨NonceLe.refl tx, rfl, fun _ h => h, fun _ h hn => absurd h hn, fun _ _ h => h⟩

/-- Two runs that create fresh accounts make one.

An account that the second allows must have nonce 0 in the first state, or be allowed there. -/
theorem CreatesFresh.trans {allowed allowed' : Address → Prop} {a b c : TransactionState}
    (hab : CreatesFresh allowed a b) (hbc : CreatesFresh allowed' b c)
    (hallowed : ∀ address, allowed' address → (a.getAccount address).nonce = 0 ∨ allowed address) :
    CreatesFresh allowed a c where
  nonce := hab.nonce.trans hbc.nonce
  parent := hbc.parent.trans hab.parent
  created address h := hbc.created address (hab.created address h)
  fresh address hc ha := by
    by_cases hb : address ∈ b.createdAccounts
    · exact hab.fresh address hb ha
    · rcases hbc.fresh address hc hb with h | h
      · exact .inl (Nat.le_zero.mp (h ▸ hab.nonce address))
      · exact hallowed address h
  code address hc h :=
    hbc.code address hc (hab.code address (fun hb => hc (hbc.created address hb)) h)

/-- A run that keeps the created accounts and gives no code creates only fresh accounts. -/
theorem CreatesFresh.of_noNewCode {allowed : Address → Prop} {a b : TransactionState}
    (hn : NonceLe a b) (hp : b.parent = a.parent) (h : NoNewCode a b) :
    CreatesFresh allowed a b where
  nonce := hn
  parent := hp
  created address hx := by rw [h.1]; exact hx
  fresh address hx hnot := absurd (h.1 ▸ hx) hnot
  code address _ hc := h.2 address hc

/-- Each write of a step creates only fresh accounts. -/
theorem stepRules_createsFresh :
    StepRules fork (fun a b : Evm fork Meter => CreatesFresh (fun _ => False) a.state b.state) :=
  have T := ((stepRules_nonceLe (fork := fork) (Meter := Meter)).and stepRules_parent).and
    stepRules_noNewCode
  have conv : ∀ {a b : Evm fork Meter},
      (NonceLe a.state b.state ∧ b.state.parent = a.state.parent) ∧ NoNewCode a.state b.state →
        CreatesFresh (fun _ => False) a.state b.state :=
    fun h => .of_noNewCode h.1.1 h.1.2 h.2
  { trans := fun hab hbc => hab.trans hbc fun _ h => h.elim
    static := fun h => conv (T.static h)
    sstore := fun evm address key value state gain h =>
      conv (T.sstore evm address key value state gain h)
    tstore := fun evm address key value => conv (T.tstore evm address key value)
    log := fun log hs hsub hm hc => conv (T.log log hs hsub hm hc)
    selfdestruct := fun beneficiary refund h => conv (T.selfdestruct beneficiary refund h)
    incrementNonce := fun evm address state h => conv (T.incrementNonce evm address state h)
    incorporate := fun h => by rw [state_incorporateChild]; exact h }

/-! ## Messages -/

/-- The state that a message starts its frame from gives no code. -/
private theorem noNewCode_startState (message : Message fork) (state : TransactionState) :
    NoNewCode state (startState fork message state) := by
  refine .of_getAccount (createdAccounts_startState message state) fun address => ?_
  unfold startState
  split
  · by_cases hne : address = message.currentTarget
    · subst hne
      exact TransactionState.getAccount_touchAccount_self _ _
    · exact TransactionState.getAccount_touchAccount hne
  · rfl

/-- The state that a message enters creates nothing from the state it is sent from.

It has the created accounts of that state, and gives code to no account. -/
theorem createsFresh_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (hentry : Entered fork message state substate entry entrySubstate) :
    CreatesFresh (fun _ => False) state entry := by
  rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact .of_noNewCode (nonceLe_startState message state) (parent_startState message state)
      (noNewCode_startState message state)
  · exact .of_noNewCode ((nonceLe_startState message state).trans (nonceLe_moveEther hm))
      ((TransactionState.parent_moveEther hm).trans (parent_startState message state))
      ((noNewCode_startState message state).trans (noNewCode_moveEther hm))

/-- A call that creates only fresh accounts from the state it enters does so from its sender.

That holds after its rollback, whether or not it ends with an error. -/
theorem createsFresh_rollbackOnError {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate} {ended : Evm fork Meter}
    (hentry : Entered fork message state substate entry entrySubstate)
    (hrun : CreatesFresh (fun _ => False) entry ended.state) :
    CreatesFresh (fun _ => False) state (rollbackOnError state ended).state := by
  have h := (createsFresh_entered hentry).trans hrun fun _ h => h.elim
  obtain ⟨hn, hp⟩ := nonceLe_rollbackOnError hentry ⟨hrun.nonce, hrun.parent⟩
  have hc := (createdAccounts_rollbackOnError state ended).1
  refine ⟨hn, hp, fun x hx => hc ▸ h.created x hx, fun x hx hnot => h.fresh x (hc ▸ hx) hnot,
    fun x hx hcode => ?_⟩
  rw [hc] at hx
  unfold rollbackOnError
  split
  · unfold TransactionState.getAccount
    rw [TransactionState.getAccountOptional_restoreTxState h.parent]
    exact hcode
  · exact h.code x hx hcode

/-- A preparation of a creation adds its address to the created accounts.

It changes no other account. -/
private theorem prepareCreation_eq {state prepared : TransactionState} {address : Address}
    (hp : prepareCreation fork state address = .ok prepared) :
    prepared.createdAccounts = state.createdAccounts.insert address ∧
      ∀ other, other ≠ address → prepared.getAccount other = state.getAccount other := by
  unfold prepareCreation at hp
  split at hp
  · have h := Base.mapError_ok_iff.mp hp
    obtain ⟨_, -, -, hother⟩ := TransactionState.modifyState_eq_ok h
    exact ⟨TransactionState.createdAccounts_modifyState h,
      fun other hne => (hother other hne).trans rfl⟩
  · cases hp
    exact ⟨rfl, fun _ _ => rfl⟩

/-- A preparation of a creation creates only its own address.

It changes no other account. -/
theorem createsFresh_prepareCreation {state prepared : TransactionState} {address : Address}
    (hp : prepareCreation fork state address = .ok prepared) :
    CreatesFresh (· = address) state prepared ∧
      ∀ other, other ≠ address → prepared.getAccount other = state.getAccount other := by
  obtain ⟨hc, hother⟩ := prepareCreation_eq hp
  refine ⟨⟨nonceLe_prepareCreation hp, parent_prepareCreation hp, createdLe_prepareCreation hp,
    fun x hx hnot => ?_, fun x hx hcode => ?_⟩, hother⟩
  · rw [hc, Std.ExtTreeSet.mem_insert] at hx
    rcases hx with hx | hx
    · exact .inr (Std.LawfulEqCmp.eq_of_compare hx).symm
    · exact absurd hx hnot
  · have hne : x ≠ address := by
      rintro rfl
      exact hx (hc ▸ Std.ExtTreeSet.mem_insert_self)
    rw [hother x hne]
    exact hcode

/-- A deposit of code rolls back, keeps the state, or sets the code of the current target. -/
private theorem state_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.state = evm.state.restoreTxState snapshot ∨ after.state = evm.state ∨
      evm.state.setCode fork evm.message.currentTarget evm.output = .ok after.state := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact .inl rfl
  split at h
  · cases h
    exact .inl rfl
  split at h
  · cases h
    exact .inl rfl
  split at h
  · cases h
    split
    · exact .inl rfl
    · exact .inr (.inl rfl)
  split at h
  · cases h
    exact .inl rfl
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact .inr (.inr (Base.mapError_ok_iff.mp hst))

/-- A creation whose init code creates only fresh accounts does so, its own address aside.

The init code runs at the address of the creation.

That holds after its deposit of code, whether or not it ends with an error. -/
theorem createsFresh_depositCode {state prepared : TransactionState} {address : Address}
    {evm after : Evm fork Meter}
    (hp : prepareCreation fork state address = .ok prepared)
    (hm : CreatesFresh (fun _ => False) prepared evm.state)
    (htarget : evm.message.currentTarget = address)
    (hd : depositCode fork state evm = .ok after) :
    CreatesFresh (· = address) state after.state := by
  have h := (createsFresh_prepareCreation hp).1.trans hm fun _ h => h.elim
  obtain ⟨hn, hpar⟩ := nonceLe_prepareCreation_depositCode hp ⟨hm.nonce, hm.parent⟩ hd
  have hc := (createdAccounts_depositCode hd).1
  refine ⟨hn, hpar, fun x hx => hc ▸ h.created x hx, fun x hx hnot => h.fresh x (hc ▸ hx) hnot,
    fun x hx hcode => ?_⟩
  rw [hc] at hx
  rcases state_depositCode hd with hs | hs | hs
  · rw [hs]
    unfold TransactionState.getAccount
    rw [TransactionState.getAccountOptional_restoreTxState h.parent]
    exact hcode
  · rw [hs]
    exact h.code x hx hcode
  · have hne : x ≠ evm.message.currentTarget := by
      rintro rfl
      apply hx
      rw [htarget]
      exact hm.created _ ((prepareCreation_eq hp).1 ▸ Std.ExtTreeSet.mem_insert_self)
    unfold TransactionState.getAccount
    rw [(TransactionState.getAccount_setCode hs).2 x hne]
    exact h.code x hx hcode

/-- The frame that resumes after a message creates only fresh accounts from the frame that sends it.

The caller must do so, and the child from the caller, a creation apart from its own address.

The step that sends a creation checks that its address has nonce 0. -/
theorem createsFresh_resume {evm caller child after : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (resumed : resume child = .ok after)
    (hcaller : CreatesFresh (fun _ => False) evm.state caller.state)
    (hchild : ChildRelByKind (Meter := Meter)
      (fun _ state _ _ ended => CreatesFresh (fun _ => False) state ended.state)
      (fun message state _ _ ended => CreatesFresh (· = message.currentTarget) state ended.state)
      caller message child) :
    CreatesFresh (fun _ => False) evm.state after.state := by
  have hs : after.state = child.state :=
    (sameContext_of_step_eq_child h resumed).state.trans (state_incorporateChild caller child)
  rw [hs]
  unfold ChildRelByKind ChildRel at hchild
  rcases ht : message.target with _ | target
  · simp only [ht] at hchild
    refine hcaller.trans hchild fun address heq => .inl ?_
    subst heq
    exact TransactionState.nonce_eq_zero_of_accountDeployable (step_eq_child_deployable h ht)
  · simp only [ht] at hchild
    exact hcaller.trans hchild fun _ h => h.elim

/-- The frame that resumes after a message keeps the message and the code of the frame before.

It creates only fresh accounts from that frame, under the conditions of the theorem before. -/
theorem createsFresh_messageCode_resume {evm caller child after : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (resumed : resume child = .ok after)
    (hcaller : CreatesFresh (fun _ => False) evm.state caller.state ∧
      caller.message = evm.message ∧ caller.code = evm.code)
    (hchild : ChildRelByKind (Meter := Meter)
      (fun _ state _ _ ended => CreatesFresh (fun _ => False) state ended.state)
      (fun message state _ _ ended => CreatesFresh (· = message.currentTarget) state ended.state)
      caller message child) :
    CreatesFresh (fun _ => False) evm.state after.state ∧
      after.message = evm.message ∧ after.code = evm.code := by
  have same := sameContext_of_step_eq_child h resumed
  refine ⟨createsFresh_resume h resumed hcaller.1 hchild, ?_, ?_⟩
  · rw [same.message, message_incorporateChild]
    exact hcaller.2.1
  · rw [same.code, code_incorporateChild]
    exact hcaller.2.2

/-- Every call that returns a frame creates only fresh accounts, a creation also its own address.

That holds at every fork.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem createsFresh_processMessage_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CreatesFresh (fun _ => False) state ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreatesFresh (· = message.currentTarget) state ended.val.state) := by
  have T := (stepRules_createsFresh (fork := fork) (Meter := Meter)).and stepRules_messageCode
  have steps : ∀ {evm : Evm fork Meter} {result : StepResult fork Meter}, True →
      step fork evm = .ok result →
      StepResult.Keeps
        (fun a b => CreatesFresh (fun _ => False) a.state b.state ∧
          b.message = a.message ∧ b.code = a.code)
        (ChildRelByKind
          (fun message state _ _ ended =>
            CreatesFresh (fun _ => False) state ended.state ∧ ended.message = message)
          (fun message state _ _ ended =>
            CreatesFresh (· = message.currentTarget) state ended.state))
        evm result := by
    intro evm result _ h
    have r := T.step h
    cases result with
    | next after => exact r
    | child caller message resume =>
      exact ⟨r.1, fun child after hres hc => createsFresh_messageCode_resume h hres r.1
        (hc.mono (fun _ _ _ _ _ h => h.1) (fun _ _ _ _ _ h => h))⟩
  have both := processMessage_rel_byKind (fork := fork) (Meter := Meter)
    (R := fun a b => CreatesFresh (fun _ => False) a.state b.state ∧
      b.message = a.message ∧ b.code = a.code)
    (Inv := fun _ => True)
    (Mcall := fun message state _ _ ended =>
      CreatesFresh (fun _ => False) state ended.state ∧ ended.message = message)
    (Mcreate := fun message state _ _ ended =>
      CreatesFresh (· = message.currentTarget) state ended.state)
    T.refl T.trans (fun _ _ => trivial)
    (fun evm error _ => T.static (staticStep_exceptionalHalt evm error))
    steps
    (fun _ _ => T.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => T.static (staticStep_runPrecompile h))
    (fun {_ state _ _ _ _ ended} hentry hrun =>
      ⟨createsFresh_rollbackOnError hentry (hrun trivial).1,
        (message_rollbackOnError state ended).trans (hrun trivial).2.1⟩)
    (fun hp hm hd => createsFresh_depositCode hp hm.1 (congrArg (·.currentTarget) hm.2) hd)
    n
  exact ⟨fun message state substate meter held hn ended h =>
      (both.1 message state substate meter held hn ended h).1,
    both.2⟩

/-- A call that returns a frame creates only accounts with nonce 0 at its start.

An account without code at its start that it does not create has no code at its end.

That holds at every fork, whether or not the call ends with an error. -/
theorem createsFresh_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    CreatesFresh (fun _ => False) state ended.val.state :=
  (createsFresh_processMessage_induction message.gas).1 message state substate meter held rfl
    ended h

/-- A creation that returns a frame creates only its own address and accounts with nonce 0.

Those nonces are the ones at its start.

An account without code at its start that it does not create has no code at its end.

That holds at every fork, whether or not the creation ends with an error. -/
theorem createsFresh_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    CreatesFresh (· = message.currentTarget) state ended.val.state :=
  (createsFresh_processMessage_induction message.gas).2 message state substate meter held rfl
    ended h

end EthLib.Execution.Evm

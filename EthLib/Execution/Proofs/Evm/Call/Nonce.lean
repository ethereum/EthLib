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

omit [GasMeter Meter] in
/-- A step that keeps the state lowers no nonce. -/
theorem SameContext.nonceLe {a b : Evm fork Meter} (h : SameContext a b) :
    NonceLe a.state b.state := by
  rw [h.state]
  exact NonceLe.refl _

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

/-! ## The instructions that give the next frame -/

/-- A successful SSTORE lowers no nonce. -/
theorem nonceLe_sstoreStep {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    NonceLe evm.state after.state := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : StaticStep evm e2 :=
    StaticStep.of_sameContext ((popWord_sameContext h1).trans (popWord_sameContext h2))
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha :
        StaticStep evm (recordStorageRead e3 e2.message.currentTarget (U256.toBeBytes k)) := by
      have := staticStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
      rw [hpair] at this
      exact (c2.trans this).trans (staticStep_recordStorageRead _ _ _)
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : NonceLe evm.state e5.state := by
        rw [(chargeStateGas_sameContext h5).state, (chargeGas_sameContext h4).state]
        exact ha.nonceLe
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact m5.trans (nonceLe_setStorage (Base.mapError_ok_iff.mp hst))
    · exact (ha.trans (staticStep_exceptionalHalt _ _)).nonceLe

/-- A successful TSTORE lowers no nonce. -/
theorem nonceLe_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    NonceLe evm.state after.state := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact ((popWord_sameContext h1).trans ((popWord_sameContext h2).trans
      (chargeGas_sameContext h3))).nonceLe.trans (NonceLe.of_getAccountOptional fun _ => rfl)

/-- A successful SELFDESTRUCT lowers no nonce, static frame or not. -/
theorem nonceLe_selfdestructStep {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : NonceLe evm.state after.state := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c : StaticStep evm (recordAccountRead e2 (toAddressMasked w)) :=
    ((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (staticStep_recordAccountRead _ _)
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : NonceLe evm.state e4.state :=
      c.nonceLe.trans ((chargeGas_sameContext h3).trans (chargeStateGas_sameContext h4)).nonceLe
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact m4.trans (nonceLe_selfdestructTransfer (Base.mapError_ok_iff.mp hst))
  · exact (c.trans (staticStep_exceptionalHalt _ _)).nonceLe

/-- Each instruction that gives the next frame keeps or raises every nonce when it succeeds.

That holds in a static frame and in any other frame. -/
theorem nonceLe_instruction {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    NonceLe evm.state after.state := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact (stackOnlyStep_sameContext hf h).nonceLe
  rcases orElse_eq_some hrun with hf | hrun
  · exact (controlFlowStep_sameContext hf h).nonceLe
  rcases orElse_eq_some hrun with hf | hrun
  · exact (memoryDataStep_sameContext hf h).nonceLe
  rcases orElse_eq_some hrun with hf | hrun
  · exact (staticStep_returnOpStep hf h).nonceLe
  rcases orElse_eq_some hrun with hf | hrun
  · exact (environmentStep_sameContext hf h).nonceLe
  rcases orElse_eq_some hrun with hf | hrun
  · exact (staticStep_accountStep hf h).nonceLe
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact (staticStep_sloadStep h).nonceLe
    case sstore => subst hf; exact nonceLe_sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact (tloadStep_sameContext h).nonceLe
    · exact nonceLe_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, hs, -⟩ := logStep_eq_ok h
    rw [hs]
    exact NonceLe.refl _
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact nonceLe_selfdestructStep h

/-! ## The calls and the creations -/

/-- A result of a step from `evm` that keeps or raises every nonce.

The next frame has nonces at least those of `evm`.

A child is sent from a frame with nonces at least those of `evm`.

So has the frame that resumes, when the frame that ends the child has those of the caller. -/
def NonceResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => NonceLe evm.state after.state
  | .child caller _ resume => NonceLe evm.state caller.state ∧
      ∀ child after, resume child = .ok after → NonceLe caller.state child.state →
        NonceLe evm.state after.state

omit [GasMeter Meter] in
/-- A result that keeps the nonces of a frame keeps those of each frame with lower nonces. -/
theorem NonceResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : NonceLe evm.state evm'.state) (r : NonceResult evm' result) :
    NonceResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    obtain ⟨c, m⟩ := r
    exact ⟨h.trans c, fun child after hres p => h.trans (m child after hres p)⟩

/-- A successful send of a message lowers no nonce. -/
theorem nonceResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    NonceResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).nonceLe
  · cases h
    refine ⟨NonceLe.refl _, fun child after hres p => ?_⟩
    rw [state_resumeCall hres]
    exact p

/-- The successful end of a call instruction lowers no nonce. -/
theorem nonceResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    NonceResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).nonceLe
  · refine NonceResult.lift ?_ (nonceResult_genericCall h)
    exact NonceLe.of_getAccountOptional fun _ => rfl

/-- A successful step of a call instruction lowers no nonce. -/
theorem nonceResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    NonceResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := (staticStep_popCallOperands h1).1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : StaticStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (staticStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : StaticStep evm e4 := s3.trans (staticStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact NonceResult.lift (s4.trans (staticStep_payCall h5)).nonceLe
        (nonceResult_finishCall h)
    · exact (s4.trans (staticStep_exceptionalHalt _ _)).nonceLe
  · exact (s3.trans (staticStep_exceptionalHalt _ _)).nonceLe

/-- A successful launch of a creation keeps or raises every nonce. -/
theorem nonceResult_launchCreate {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) : NonceResult evm result := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).nonceLe
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : NonceLe evm.state (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2
      address).state :=
    (((staticStep_recordAccountRead { evm with returnData := .empty }
      evm.message.currentTarget).trans (staticStep_accessAddress _ address)).trans
      (staticStep_recordAccountRead _ address)).nonceLe
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have m2 : NonceLe evm.state e2.state := by
      rw [(chargeGas_sameContext h2).state, (chargeStateGas_sameContext h1).state]
      exact c0
    have ms : NonceLe evm.state state :=
      m2.trans (nonceLe_incrementNonce (Base.mapError_ok_iff.mp hst))
    split at hr
    · cases hr
      refine ⟨ms, fun child after hres p => ?_⟩
      rw [state_resumeCreate hres]
      exact ms.trans p
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact ms.trans (pushWord_sameContext h3).nonceLe
  · exact c0

/-- A successful step of CREATE or CREATE2 keeps or raises every nonce. -/
theorem nonceResult_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    NonceResult evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : e4.state = e3.state := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact (popWord_sameContext he).state
    · cases h4
      rfl
  have m5 : NonceLe evm.state e5.state := by
    rw [(chargeGasAndMemory_sameContext h5).state, m4, (popWord_sameContext h3).state,
      (popWord_sameContext h2).state, (popWord_sameContext h1).state]
    exact NonceLe.refl _
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact NonceResult.lift m5 (nonceResult_launchCreate h)

/-- A successful instruction that may send a message keeps or raises every nonce. -/
theorem nonceResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : NonceResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact nonceResult_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact nonceResult_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact nonceResult_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact nonceResult_createStep h
         · cases hrun)

/-- Every successful step of every frame keeps or raises every nonce, static frame or not. -/
theorem nonceResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : NonceResult evm result := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact nonceLe_instruction hop hr
      · split at h
        · rename_i hcall
          exact nonceResult_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact (controlFlowStep_sameContext (op := .stop) rfl rfl).nonceLe

/-! ## A run of a frame -/

/-- A runner of messages that keeps or raises every nonce.

Each message that it runs successfully ends with nonces at least those of its sender. -/
def KeepsNonce {bound : Nat} (runChild : MessageRunner fork Meter bound) : Prop :=
  ∀ caller message lt ended, runChild caller message lt = .ok ended →
    NonceLe caller.state ended.val.state

/-- A successful run of a frame keeps or raises every nonce.

The runner of its messages must keep or raise every nonce. -/
theorem nonceLe_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} (runs : KeepsNonce runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    NonceLe evm.state after.state := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 => cases h; exact NonceLe.refl _
  case case3 =>
    rename_i result _ ih
    exact (nonceResult_step result).trans (ih h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; exact NonceLe.refl _
  case case7 =>
    rename_i hchild _ _ _ hran _ resumed _ ih
    obtain ⟨-, hres⟩ := nonceResult_step hchild
    exact (hres _ _ resumed (runs _ _ _ _ hran)).trans (ih h)
  case case8 => cases h; exact NonceLe.refl _

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
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          NonceLe state ended.val.state := by
      intro message state substate meter held hn ended h
      by_cases herr : ended.val.error.isSome = true
      · exact NonceLe.of_sameOutside (processMessage_sameOutside_of_error h herr)
      rw [processMessage] at h
      obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
      have hst := nonceLe_startState message state
      have core : NonceLe state ended0.val.state := by
        dsimp only at hdo
        split at hdo
        all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
        all_goals
          have hp1 : NonceLe state state1 := by
            first
            | exact hst.trans (nonceLe_moveEther (Base.mapError_ok_iff.mp hm))
            | (cases hm; exact hst)
          rcases hpa : precompileAddress fork message with _ | addr
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
            · rename_i after hrun
              cases hdo
              refine hp1.trans (nonceLe_runFrame ?_ hrun)
              rintro caller' message' lt ⟨c, used⟩ hrun'
              dsimp only at hrun'
              split at hrun'
              · exact (ih message'.gas (by omega)).1 message' caller'.state _ _ _ rfl ⟨c, used⟩
                  hrun'
              · exact (ih message'.gas (by omega)).2 message' caller'.state _ _ _ rfl ⟨c, used⟩
                  hrun'
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
              exact hp1
            · split at hdo
              · rename_i after hrp
                cases hdo
                exact hp1.trans (staticStep_runPrecompile hrp).nonceLe
              · cases hdo
                exact hp1
      have hval := congrArg Subtype.val rolled
      simp only at hval
      rw [← hval] at herr ⊢
      unfold rollbackOnError at herr ⊢
      split
      · rename_i he
        simp [he] at herr
      · exact core
    refine ⟨call, ?_⟩
    intro message state substate meter held hn ended h
    rw [processCreateMessage] at h
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · cases h
      have hle : NonceLe prepared evm.state := call message prepared substate meter held hn _ hrun
      have hpar : evm.state.parent = state.parent :=
        (parent_processMessage hrun).trans (parent_prepareCreation hp)
      exact nonceLe_depositCode ((nonceLe_prepareCreation hp).trans hle) hpar
        ‹depositCode _ _ _ = .ok _›

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

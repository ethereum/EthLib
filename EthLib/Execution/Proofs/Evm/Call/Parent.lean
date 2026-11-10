module

public import EthLib.Execution.Proofs.Evm.Call.StaticMessage

/-!
# Proofs: every message keeps the block of the state

The block of a transaction state is the state before the block, with the writes of the block so far.

Every successful step of every frame keeps the block, at every fork, static frame or not.

A successful run of a frame keeps it too, under a runner of messages that keeps it.

Such a runner ends each message that succeeds with the block of the frame that sends it.

Every successful call and creation keeps the block, by induction on the gas of the message.

A rollback to a snapshot of the same block gives back the storage of the snapshot.

So a call that ends with an error leaves every storage word of every address as it was.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The writes of the state -/

/-- A successful move of the balance of a destroyed account keeps the block of the state. -/
theorem parent_selfdestructTransfer {tx tx' : TransactionState} {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.parent = tx.parent := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (TransactionState.parent_setAccountBalance h).trans
        (TransactionState.parent_moveEther h1)
    · cases h
      exact TransactionState.parent_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (TransactionState.parent_setAccountBalance h).trans
      (TransactionState.parent_createEther h1)

/-- A successful preparation of a creation keeps the block of the state. -/
theorem parent_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : tx'.parent = tx.parent := by
  unfold prepareCreation at h
  split at h
  · exact (TransactionState.parent_incrementNonce (Base.mapError_ok_iff.mp h) :)
  · cases h
    rfl

/-! ## The instructions that give the next frame -/

/-- A successful SSTORE keeps the block of the state. -/
theorem parent_sstoreStep {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : e2.state.parent = evm.state.parent := by
    rw [(popWord_sameContext h2).state, (popWord_sameContext h1).state]
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : e3.state.parent = e2.state.parent := by
      have := (staticStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)).parent
      rwa [hpair] at this
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.state.parent = evm.state.parent := by
        rw [(chargeStateGas_sameContext h5).state, (chargeGas_sameContext h4).state]
        exact ha.trans c2
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact (TransactionState.parent_setStorage (Base.mapError_ok_iff.mp hst)).trans m5
    · exact ha.trans c2

/-- A successful TSTORE keeps the block of the state. -/
theorem parent_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    after.state.parent = evm.state.parent := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    show e3.state.parent = _
    rw [(chargeGas_sameContext h3).state, (popWord_sameContext h2).state,
      (popWord_sameContext h1).state]

/-- A successful SELFDESTRUCT keeps the block of the state, static frame or not. -/
theorem parent_selfdestructStep {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : after.state.parent = evm.state.parent := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : e2.state.parent = e1.state.parent := by
    have := (staticStep_accessAddress e1 (toAddressMasked w)).parent
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c : (recordAccountRead e2 (toAddressMasked w)).state.parent = evm.state.parent := by
    show e2.state.parent = _
    rw [ha, (popWord_sameContext h1).state]
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.state.parent = evm.state.parent := by
      rw [(chargeStateGas_sameContext h4).state, (chargeGas_sameContext h3).state]
      exact c
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact (parent_selfdestructTransfer (Base.mapError_ok_iff.mp hst)).trans m4
  · exact c

/-- Each instruction that gives the next frame keeps the block of the state when it succeeds.

That holds in a static frame and in any other frame. -/
theorem parent_instruction {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact congrArg _ (stackOnlyStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact congrArg _ (controlFlowStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact congrArg _ (memoryDataStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact (staticStep_returnOpStep hf h).parent
  rcases orElse_eq_some hrun with hf | hrun
  · exact congrArg _ (environmentStep_sameContext hf h).state
  rcases orElse_eq_some hrun with hf | hrun
  · exact (staticStep_accountStep hf h).parent
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact (staticStep_sloadStep h).parent
    case sstore => subst hf; exact parent_sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact congrArg _ (tloadStep_sameContext h).state
    · exact parent_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, hs, -⟩ := logStep_eq_ok h
    rw [hs]
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact parent_selfdestructStep h

/-! ## The calls and the creations -/

/-- A result of a step from `evm` that keeps the block of the state.

The next frame has the block of `evm`.

A child is sent from a frame with the block of `evm`.

The frame that resumes has it too, when the frame that ends the child has the caller's block. -/
abbrev ParentResult (evm : Evm fork Meter) : StepResult fork Meter → Prop :=
  StepResult.Keeps (fun a b => b.state.parent = a.state.parent)
    (fun caller _ child => child.state.parent = caller.state.parent) evm

omit [GasMeter Meter] in
/-- A result that keeps the block of a frame keeps the block of each frame with the same block. -/
theorem ParentResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : evm'.state.parent = evm.state.parent) (r : ParentResult evm' result) :
    ParentResult evm result :=
  StepResult.Keeps.lift (fun hab hbc => hbc.trans hab) h r

/-- The caller that resumes after a call has the state of the frame that ends the call. -/
theorem state_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.state = child.state := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  show e.state = child.state
  rw [(pushWord_sameContext h1).state]
  split <;> simp [state_incorporateChild, refillStateGas]

/-- The creator that resumes after a creation has the state of the frame that ends it. -/
theorem state_resumeCreate {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.state = child.state := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  show e.state = child.state
  rw [(pushWord_sameContext h1).state]
  split <;> simp [state_incorporateChild, refillStateGas]

/-- A successful send of a message keeps the block of the state. -/
theorem parentResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    ParentResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).parent
  · cases h
    exact ⟨rfl, fun child after hres p =>
      (congrArg TransactionState.parent (state_resumeCall hres)).trans p⟩

/-- The successful end of a call instruction keeps the block of the state. -/
theorem parentResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ParentResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).parent
  · refine ParentResult.lift ?_ (parentResult_genericCall h)
    rfl

/-- A successful step of a call instruction keeps the block of the state. -/
theorem parentResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    ParentResult evm result := by
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
      exact ParentResult.lift (s4.trans (staticStep_payCall h5)).parent
        (parentResult_finishCall h)
    · exact (s4.trans (staticStep_exceptionalHalt _ _)).parent
  · exact (s3.trans (staticStep_exceptionalHalt _ _)).parent

/-- A successful launch of a creation keeps the block of the state. -/
theorem parentResult_launchCreate {evm : Evm fork Meter} {value : U256} {initCode : ByteArray}
    {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) : ParentResult evm result := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (staticStep_skipCall hs).parent
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2
      address).state.parent = evm.state.parent :=
    ((staticStep_accessAddress _ _).trans (staticStep_recordAccountRead _ _)).parent
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have m2 : e2.state.parent = evm.state.parent := by
      rw [(chargeGas_sameContext h2).state, (chargeStateGas_sameContext h1).state]
      exact c0
    have ms : state.parent = evm.state.parent :=
      (TransactionState.parent_incrementNonce (Base.mapError_ok_iff.mp hst)).trans m2
    split at hr
    · cases hr
      exact ⟨ms, fun child after hres p =>
        (congrArg TransactionState.parent (state_resumeCreate hres)).trans (p.trans ms)⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      show e3.state.parent = _
      rw [(pushWord_sameContext h3).state]
      exact ms
  · exact c0

/-- A successful step of CREATE or CREATE2 keeps the block of the state. -/
theorem parentResult_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    ParentResult evm result := by
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
  have m5 : e5.state.parent = evm.state.parent := by
    rw [(chargeGasAndMemory_sameContext h5).state, m4, (popWord_sameContext h3).state,
      (popWord_sameContext h2).state, (popWord_sameContext h1).state]
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact ParentResult.lift m5 (parentResult_launchCreate h)

/-- A successful instruction that may send a message keeps the block of the state. -/
theorem parentResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : ParentResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact parentResult_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact parentResult_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact parentResult_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact parentResult_createStep h
         · cases hrun)

/-- Every successful step of every frame keeps the block of the state, static frame or not. -/
theorem parentResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : ParentResult evm result := by
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
          exact parent_instruction hop hr
      · split at h
        · rename_i hcall
          exact parentResult_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact congrArg _ (controlFlowStep_sameContext (op := .stop) rfl rfl).state

/-! ## A run of a frame -/

/-- A runner of messages that keeps the block of the state.

It ends each message that it runs successfully with the block of the frame that sends it. -/
def KeepsParent {bound : Nat} (runChild : MessageRunner fork Meter bound) : Prop :=
  ∀ caller message lt ended, runChild caller message lt = .ok ended →
    ended.val.state.parent = caller.state.parent

/-- A successful run of a frame keeps the block of the state.

The runner of its messages must keep the block. -/
theorem parent_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound} (runs : KeepsParent runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    after.state.parent = evm.state.parent :=
  rel_runFrame (R := fun a b => b.state.parent = a.state.parent)
    (C := fun caller _ child => child.state.parent = caller.state.parent)
    (Inv := fun _ => True) (fun _ => rfl) (fun hab hbc => hbc.trans hab) (fun _ _ => trivial)
    (fun _ _ _ => rfl) (fun _ h => parentResult_step h) (fun _ _ _ _ _ => runs _ _ _ _) trivial h

/-! ## Messages -/

/-- A successful deposit of code keeps the block of the frame that ends the init code. -/
theorem parent_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.state.parent = evm.state.parent := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    rfl
  split at h
  · cases h
    split <;> rfl
  split at h
  · cases h
    rfl
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact TransactionState.parent_setCode (Base.mapError_ok_iff.mp hst)

/-- The state that a message starts its frame from has the block of the state it is sent from. -/
theorem parent_startState (message : Message fork) (state : TransactionState) :
    (startState fork message state).parent = state.parent := by
  unfold startState
  split
  · exact TransactionState.parent_touchAccount _ _
  · rfl

/-- The rollback of a frame keeps the block of that frame. -/
theorem parent_rollbackOnError (snapshot : TransactionState) (evm : Evm fork Meter) :
    (rollbackOnError snapshot evm).state.parent = evm.state.parent := by
  unfold rollbackOnError
  split <;> rfl

/-- A call ends with the rollback of the frame that ends it, to the state it is sent from. -/
theorem exists_rollbackOnError_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ∃ last : Evm fork Meter, ended.val = rollbackOnError state last := by
  rw [processMessage] at h
  obtain ⟨ended0, -, rolled⟩ := Base.map_ok_iff.mp h
  have hval := congrArg Subtype.val rolled
  simp only at hval
  exact ⟨ended0.val, hval.symm⟩

/-- Every successful call and creation keeps the block of the state, at every fork.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_parent [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ended.val.state.parent = state.parent) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ended.val.state.parent = state.parent) :=
  processMessage_rel (R := fun a b => b.state.parent = a.state.parent) (Inv := fun _ => True)
    (M := fun _ state _ _ ended => ended.state.parent = state.parent)
    (fun _ => rfl) (fun hab hbc => hbc.trans hab) (fun _ _ => trivial) (fun _ _ _ => rfl)
    (fun _ h => parentResult_step h) (fun _ _ => rfl)
    (fun h _ => (staticStep_runPrecompile h).parent)
    (fun {message state _ _ _ _ _} hstate hrun => by
      rw [parent_rollbackOnError]
      refine (hrun trivial).trans ?_
      rcases hstate with ⟨rfl, -, -⟩ | ⟨-, hm, -⟩
      · exact parent_startState message state
      · exact (TransactionState.parent_moveEther hm).trans (parent_startState message state))
    (fun hp hm hd => (parent_depositCode hd).trans (hm.trans (parent_prepareCreation hp))) n

/-- A successful call keeps the block of the state it is sent from, at every fork. -/
theorem parent_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ended.val.state.parent = state.parent :=
  (processMessage_parent message.gas).1 message state substate meter held rfl ended h

/-- A successful creation keeps the block of the state it is sent from, at every fork. -/
theorem parent_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    ended.val.state.parent = state.parent :=
  (processMessage_parent message.gas).2 message state substate meter held rfl ended h

/-- A call that ends with an error reads as the state it is sent from, at every address.

That holds for the account, every word of storage and every word of transient storage.

It holds at every fork, whatever the code of the message. -/
theorem processMessage_sameOutside_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (herr : ended.val.error.isSome = true) :
    TransactionState.SameOutside [] state ended.val.state := by
  have hp := parent_processMessage h
  obtain ⟨last, hl⟩ := exists_rollbackOnError_processMessage h
  rw [hl] at herr hp ⊢
  unfold rollbackOnError at herr hp ⊢
  split at herr
  · simp only [‹last.error.isSome = true›, ↓reduceIte] at hp ⊢
    exact TransactionState.sameOutside_restoreTxState hp
  · exact absurd herr ‹_›

/-- A call that ends with an error leaves every storage word as it was in the state it is sent from.

That holds at every fork, at every address, whatever the code of the message. -/
theorem getStorage_processMessage_of_error [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (herr : ended.val.error.isSome = true) (address : Address) (key : Bytes32) :
    ended.val.state.getStorage address key = state.getStorage address key :=
  (processMessage_sameOutside_of_error h herr address List.not_mem_nil).2.1 key

end EthLib.Execution.Evm

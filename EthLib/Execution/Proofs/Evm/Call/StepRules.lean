module

public import EthLib.Execution.Proofs.Evm.Call.StaticMessage

/-!
# Proofs: a relation of frames that each write keeps holds for every step and every message

Many facts about a message are relations between two frames, such as a block that stays.

Most steps keep the state and the substate up to the records of their reads.

So a relation that looks only at the state and the substate holds of them.

Only a few writes change more: storage, transient storage, a log, SELFDESTRUCT and a nonce.

A caller also takes in the frame that ends its child.

A relation that holds of each of these holds of every step, every run and every message.

The relation sees no gas, memory or stack, since steps that keep the state change them freely.

For messages, each relation must still handle the start of a call and the deposit of code.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The rules for a relation `R` of two frames to hold of every step.

It must be transitive, and hold of each step that keeps the state up to the records of reads.

So it can only look at the state and the substate, apart from the logs and the refund counter.

It must hold of each write of storage, of transient storage, of a log and of SELFDESTRUCT.

It must hold of the rise of a nonce, and of a caller that takes in a child related to it.

It also relates a caller to the frame that ends each message the caller sends. -/
structure StepRules (fork : Fork) (R : Evm fork Meter → Evm fork Meter → Prop) : Prop where
  /-- The relation is transitive. -/
  trans : ∀ {a b c}, R a b → R b c → R a c
  /-- A step that keeps the state up to the records of its reads keeps the relation. -/
  static : ∀ {a b}, StaticStep a b → R a b
  /-- A write of storage that changes the refund counter keeps the relation. -/
  sstore : ∀ (evm : Evm fork Meter) (address : Address) (key : Bytes32) (value : U256)
    (state : TransactionState) (gain : Int), evm.state.setStorage address key value = .ok state →
    R evm (advance { evm with
      state, substate := { evm.substate with refundCounter := evm.substate.refundCounter + gain } })
  /-- A write of transient storage keeps the relation. -/
  tstore : ∀ (evm : Evm fork Meter) (address : Address) (key : Bytes32) (value : U256),
    R evm (advance { evm with state := evm.state.setTransientStorage address key value })
  /-- A step that keeps the state and appends a log keeps the relation. -/
  log : ∀ {a b : Evm fork Meter} (log : Blocks.Log), b.state = a.state →
    b.substate = { a.substate with logs := a.substate.logs.push log } → R a b
  /-- The end of a successful SELFDESTRUCT keeps the relation. -/
  selfdestruct : ∀ {evm after : Evm fork Meter} (beneficiary : Address) (refund : Nat),
    finishSelfdestruct fork beneficiary refund evm = .ok after → R evm after
  /-- The rise of a nonce keeps the relation. -/
  incrementNonce : ∀ (evm : Evm fork Meter) (address : Address) (state : TransactionState),
    evm.state.incrementNonce fork address = .ok state → R evm { evm with state }
  /-- A caller that takes in a child related to it is related to its frame before. -/
  incorporate : ∀ {caller child : Evm fork Meter}, R caller child →
    R caller (incorporateChild fork caller child)

/-- A refill of state gas keeps the message, the state, the substate and the code. -/
theorem sameContext_refillStateGas (evm : Evm fork Meter) (amount : Nat) :
    SameContext evm (refillStateGas evm amount) :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- A new return data keeps the message, the state, the substate and the code. -/
theorem sameContext_returnData (evm : Evm fork Meter) (returnData : ByteArray) :
    SameContext evm { evm with returnData } :=
  ⟨rfl, rfl, rfl, rfl⟩

namespace StepRules

variable {R : Evm fork Meter → Evm fork Meter → Prop}

/-- A step that keeps the message, the state, the substate and the code keeps the relation. -/
theorem sameContext (rules : StepRules fork R) {a b : Evm fork Meter} (h : SameContext a b) :
    R a b :=
  rules.static (.of_sameContext h)

/-- Every frame is related to itself. -/
theorem refl (rules : StepRules fork R) (evm : Evm fork Meter) : R evm evm :=
  rules.static (.refl evm)

/-- Two relations that follow the rules follow them together. -/
theorem and {S : Evm fork Meter → Evm fork Meter → Prop} (r : StepRules fork R)
    (s : StepRules fork S) : StepRules fork (fun a b => R a b ∧ S a b) where
  trans hab hbc := ⟨r.trans hab.1 hbc.1, s.trans hab.2 hbc.2⟩
  static h := ⟨r.static h, s.static h⟩
  sstore evm address key value state gain h :=
    ⟨r.sstore evm address key value state gain h, s.sstore evm address key value state gain h⟩
  tstore evm address key value := ⟨r.tstore evm address key value, s.tstore evm address key value⟩
  log log hs hsub := ⟨r.log log hs hsub, s.log log hs hsub⟩
  selfdestruct beneficiary refund h :=
    ⟨r.selfdestruct beneficiary refund h, s.selfdestruct beneficiary refund h⟩
  incrementNonce evm address state h :=
    ⟨r.incrementNonce evm address state h, s.incrementNonce evm address state h⟩
  incorporate h := ⟨r.incorporate h.1, s.incorporate h.2⟩

/-! ## The instructions that give the next frame -/

/-- A successful SSTORE keeps the relation. -/
theorem sstoreStep (rules : StepRules fork R) {evm after : Evm fork Meter}
    (h : sstoreStep evm = .ok after) : R evm after := by
  unfold Evm.sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : StaticStep evm e2 :=
    .of_sameContext ((popWord_sameContext h1).trans (popWord_sameContext h2))
  dsimp only at h
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
      have m5 : StaticStep evm e5 :=
        ha.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
          ((chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5))))
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact rules.trans (rules.static m5) (rules.sstore _ _ _ _ _ _ (Base.mapError_ok_iff.mp hst))
    · exact rules.static (ha.trans (staticStep_exceptionalHalt _ _))

/-- A successful TSTORE keeps the relation. -/
theorem tstoreStep (rules : StepRules fork R) {evm after : Evm fork Meter}
    (h : tstoreStep evm = .ok after) : R evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact rules.trans (rules.sameContext ((popWord_sameContext h1).trans
      ((popWord_sameContext h2).trans (chargeGas_sameContext h3)))) (rules.tstore _ _ _ _)

/-- A successful SELFDESTRUCT keeps the relation. -/
theorem selfdestructStep (rules : StepRules fork R) {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : R evm after := by
  unfold Evm.selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha := staticStep_accessAddress e1 (toAddressMasked w)
  rw [hacc] at ha
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c : StaticStep evm (recordAccountRead e2 (toAddressMasked w)) :=
    ((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (staticStep_recordAccountRead _ _)
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    exact rules.trans (rules.static (c.trans (.of_sameContext
      ((chargeGas_sameContext h3).trans (chargeStateGas_sameContext h4)))))
      (rules.selfdestruct _ _ h)
  · exact rules.static (c.trans (staticStep_exceptionalHalt _ _))

/-- Each successful instruction that gives the next frame keeps the relation. -/
theorem instruction (rules : StepRules fork R) {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) : R evm after := by
  unfold Evm.instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.static (staticStep_returnOpStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact rules.static (staticStep_accountStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact rules.static (staticStep_sloadStep h)
    case sstore => subst hf; exact rules.sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact rules.sameContext (tloadStep_sameContext h)
    · exact rules.tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨log, -, -, -, hs, hsub⟩ := logStep_eq_ok h
    exact rules.log log hs hsub
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact rules.selfdestructStep h

/-! ## The calls and the creations -/

/-- A caller that resumes after a call is related to the caller, when the child is. -/
theorem resumeCall (rules : StepRules fork R) {caller child after : Evm fork Meter}
    {newAccount : Nat} {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (hc : R caller child) : R caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine rules.trans (rules.incorporate hc) (rules.sameContext ?_)
  refine SameContext.trans ?_ ((pushWord_sameContext h1).trans ⟨rfl, rfl, rfl, rfl⟩)
  constructor <;> split <;> rfl

/-- A creator that resumes after a creation is related to the creator, when the child is. -/
theorem resumeCreate (rules : StepRules fork R) {caller child after : Evm fork Meter}
    {newAccount : Nat} {address : Address}
    (h : resumeCreate fork caller newAccount address child = .ok after) (hc : R caller child) :
    R caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine rules.trans (rules.incorporate hc) (rules.sameContext ?_)
  refine SameContext.trans ?_ ((pushWord_sameContext h1).trans ⟨rfl, rfl, rfl, rfl⟩)
  constructor <;> split <;> rfl

/-- A result that keeps the relation from a frame keeps it from any frame related to that one. -/
theorem lift (rules : StepRules fork R) {evm evm' : Evm fork Meter}
    {result : StepResult fork Meter} (h : R evm evm')
    (r : result.Keeps R (fun caller _ child => R caller child) evm') :
    result.Keeps R (fun caller _ child => R caller child) evm :=
  StepResult.Keeps.lift (R := R) (C := fun caller _ child => R caller child) rules.trans h r

/-- A successful send of a message keeps the relation. -/
theorem genericCall (rules : StepRules fork R) {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (rules.static (((StaticStep.of_sameContext (sameContext_returnData evm .empty)).trans
      (.of_sameContext (sameContext_refillStateGas _ newAccount))).trans
      (staticStep_skipCall hs)) :)
  · cases h
    have pre : R evm { evm with returnData := .empty } := rules.sameContext ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨pre, fun _ _ hres p => rules.trans pre (rules.resumeCall hres p)⟩

/-- The successful end of a call instruction keeps the relation. -/
theorem finishCall (rules : StepRules fork R) {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : StaticStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨StateKept.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (rules.static ((pre.trans (.of_sameContext (sameContext_refillStateGas _ _))).trans
      (staticStep_skipCall hs)) :)
  · exact rules.lift (rules.static pre) (rules.genericCall h)

/-- A successful step of a call instruction keeps the relation. -/
theorem callStep (rules : StepRules fork R) {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := (staticStep_popCallOperands h1).1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha := staticStep_accessAddress e1 call.address
  rw [hacc] at ha
  have s3 : StaticStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (staticStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : StaticStep evm e4 := s3.trans (staticStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact rules.lift (rules.static (s4.trans (staticStep_payCall h5))) (rules.finishCall h)
    · exact rules.static (s4.trans (staticStep_exceptionalHalt _ _))
  · exact rules.static (s3.trans (staticStep_exceptionalHalt _ _))

/-- A successful launch of a creation keeps the relation. -/
theorem launchCreate (rules : StepRules fork R) {evm : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.launchCreate at h
  dsimp only at h
  have pre : StaticStep evm
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    (StaticStep.of_sameContext (sameContext_returnData evm .empty)).trans
      (staticStep_recordAccountRead _ _)
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (rules.static (pre.trans (staticStep_skipCall hs)) :)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : StaticStep evm (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2 address) :=
    (pre.trans (staticStep_accessAddress _ address)).trans (staticStep_recordAccountRead _ address)
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have ms : R evm { e2 with state } := rules.trans (rules.static (c0.trans (.of_sameContext
      ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)))))
      (rules.incrementNonce _ _ _ (Base.mapError_ok_iff.mp hst))
    split at hr
    · cases hr
      have md : R evm { e2 with state, gas := GasMeter.drain e2.gas } :=
        rules.trans ms (rules.sameContext ⟨rfl, rfl, rfl, rfl⟩)
      exact ⟨md, fun _ _ hres p => rules.trans md (rules.resumeCreate hres p)⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact rules.trans ms
        (rules.sameContext ((pushWord_sameContext h3).trans ⟨rfl, rfl, rfl, rfl⟩))
  · exact rules.static (c0.trans (staticStep_exceptionalHalt _ _))

/-- A successful step of CREATE or CREATE2 keeps the relation. -/
theorem createStep (rules : StepRules fork R) {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : SameContext e3 e4 := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact popWord_sameContext he
    · cases h4
      exact SameContext.refl _
  have m5 : R evm e5 := rules.sameContext (((((popWord_sameContext h1).trans
    (popWord_sameContext h2)).trans (popWord_sameContext h3)).trans m4).trans
    (chargeGasAndMemory_sameContext h5))
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact rules.lift m5 (rules.launchCreate h)

/-- A successful instruction that may send a message keeps the relation. -/
theorem messageInstruction (rules : StepRules fork R) {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact rules.callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact rules.callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact rules.createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact rules.createStep h
         · cases hrun)

/-- Every successful step of every frame keeps the relation.

A message that the step sends must end in a frame related to its caller. -/
theorem step (rules : StepRules fork R) {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) :
    result.Keeps R (fun caller _ child => R caller child) evm := by
  unfold Evm.step at h
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
          exact rules.instruction hop hr
      · split at h
        · rename_i hcall
          exact rules.messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact rules.sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

/-! ## A run of a frame and a message -/

/-- A successful run of a frame keeps the relation.

The runner must end each message that it runs in a frame related to the caller. -/
theorem runFrame [LawfulGasMeter Meter] (rules : StepRules fork R) {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (runs : RunnerEnsures (fun caller _ child => R caller child) runChild)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : Evm.runFrame (Evm.step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    R evm after :=
  rel_runFrame (Inv := fun _ => True) rules.refl rules.trans (fun _ _ => trivial)
    (fun _ _ _ => rules.static (staticStep_exceptionalHalt _ _)) (fun _ h => rules.step h)
    (fun _ _ _ _ _ => runs _ _ _ _) trivial h

/-- Every successful call and creation satisfies a relation `M` of messages.

A call must satisfy `M` after its rollback, when its frame ends related to its start frame.

That frame starts from the state and the substate that the message enters.

A creation must satisfy `M` when the call of its init code does, after its deposit of code.

A message that satisfies `M` must end in a frame related to the frame that sends it.

It instantiates the strong induction on the gas of the message, for calls and creations together.
-/
theorem processMessage [LawfulGasMeter Meter] (rules : StepRules fork R)
    {M : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    (call : ∀ {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter},
      Entered fork message state substate entry entrySubstate →
      R (startFrame message entry entrySubstate meter) ended →
      M message state substate meter (rollbackOnError state ended))
    (create : ∀ {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter},
      prepareCreation fork state message.currentTarget = .ok prepared →
      M message prepared substate meter evm → depositCode fork state evm = .ok after →
      M message state substate meter after)
    (ends : ∀ {caller : Evm fork Meter} {message : Message fork} {ended : Evm fork Meter},
      ChildRel M caller message ended → R caller ended)
    (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, Evm.processMessage fork message state substate meter held = .ok ended →
        M message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        M message state substate meter ended.val) :=
  processMessage_rel (Inv := fun _ => True) rules.refl rules.trans (fun _ _ => trivial)
    (fun _ _ _ => rules.static (staticStep_exceptionalHalt _ _))
    (fun _ h => (rules.step h).of_child ends)
    (fun _ _ => rules.sameContext ⟨rfl, rfl, rfl, rfl⟩)
    (fun h _ => rules.static (staticStep_runPrecompile h))
    (fun hentry hrun => call hentry (hrun trivial)) create n

end StepRules

/-! ## The resume of a message -/

/-- The message of a result, if it sends one, resumes its caller as a call or as a creation. -/
private def ResumesCaller : StepResult fork Meter → Prop
  | .next _ => True
  | .child caller _ resume =>
    (∃ newAccount outputStart outputSize,
      resume = resumeCall fork caller newAccount outputStart outputSize) ∨
    ∃ newAccount address, resume = resumeCreate fork caller newAccount address

/-- A successful send of a message resumes its caller as a call or a creation.

That holds whenever it sends a message. -/
private theorem resumesCaller_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    ResumesCaller result := by
  unfold Evm.genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, -, rfl⟩ := Base.map_ok_iff.mp h
    trivial
  · cases h
    exact .inl ⟨_, _, _, rfl⟩

/-- The successful end of a call instruction resumes its caller as a call or a creation.

That holds whenever it sends a message. -/
private theorem resumesCaller_finishCall {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ResumesCaller result := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, -, rfl⟩ := Base.map_ok_iff.mp h
    trivial
  · exact resumesCaller_genericCall h

/-- A successful step of a call instruction resumes its caller as a call or a creation.

That holds whenever it sends a message. -/
private theorem resumesCaller_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    ResumesCaller result := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, -, h⟩ := Base.bind_ok_iff.mp h
      exact resumesCaller_finishCall h
    · trivial
  · trivial

/-- A successful launch of a creation resumes its caller as a call or a creation.

That holds whenever it sends a message. -/
private theorem resumesCaller_launchCreate {evm : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) : ResumesCaller result := by
  unfold Evm.launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, -, rfl⟩ := Base.map_ok_iff.mp h
    trivial
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, -, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, -, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    split at hr
    · cases hr
      exact .inr ⟨_, _, rfl⟩
    · obtain ⟨e3, -, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      trivial
  · trivial

/-- A successful step of CREATE or CREATE2 resumes its caller as a call or a creation.

That holds whenever it sends a message. -/
private theorem resumesCaller_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    ResumesCaller result := by
  unfold Evm.createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, -, h⟩ := Base.bind_ok_iff.mp h
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact resumesCaller_launchCreate h

/-- A successful instruction that may send a message resumes its caller as a call or a creation. -/
private theorem resumesCaller_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : ResumesCaller result := by
  unfold Evm.messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact resumesCaller_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact resumesCaller_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact resumesCaller_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact resumesCaller_createStep h
         · cases hrun)

/-- Each message that a successful step sends resumes its caller as a call or as a creation. -/
theorem step_eq_child_resume {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    (∃ newAccount outputStart outputSize,
      resume = resumeCall fork caller newAccount outputStart outputSize) ∨
    ∃ newAccount address, resume = resumeCreate fork caller newAccount address := by
  suffices ∀ result, step fork evm = .ok result → ResumesCaller result from this _ h
  intro result h
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          trivial
      · split at h
        · rename_i hcall
          exact resumesCaller_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    trivial

end EthLib.Execution.Evm

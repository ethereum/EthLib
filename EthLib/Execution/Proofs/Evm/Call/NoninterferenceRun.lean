module

public import EthLib.Execution.Proofs.Evm.Call.Noninterference
public import EthLib.Execution.Proofs.Evm.Call.Candidate
public import EthLib.Execution.Proofs.Evm.Call.CodeOrigin
public import EthLib.Execution.Proofs.Evm.Call.ReadsGrow

/-!
# Proofs: a message depends only on what it records

Run the same message on two states that agree on four sets of accounts, slots and code hashes.

When the first run ends with every read in the sets, the second ends in an agreeing frame.

The first state must have read the account that the message runs at.

Its code hashes must come from the block or from writes, with no new deployment candidate.

A first run that fails with an error that aborts the execution is not covered.

The two frames differ only in their states, and both carry the same tracker.

Each step of the first run reads only what it records, and a run never drops a read.

So every step of the first run has its reads in the sets, and the two runs move together.

The sets must hold the code hash in the block of each account in the account set.

They must hold the whole storage of each such account with nonce 0 and no code in the block.

The tracker sets of a transaction meet both conditions.

The sets play the part of a block access list in [EIP-7928, Scope and Inclusion][bal].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Hash32)
open EthLib.Execution.State (BlockState EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.State.TransactionState (AgreesOn NoNewCandidate)

variable {fork : Base.Fork} {Meter : Type} [GasMeter Meter]

/-- Sets that hold, for each account in the account set, what the block says of it.

The code set holds its code hash in the block.

The whole-storage set holds it when it has nonce 0 and no code in the block. -/
structure CoversBlock (block : BlockState) (account allStorage : Address → Prop)
    (code : Hash32 → Prop) : Prop where
  /-- The code hash in the block of each account in the account set is in the code set. -/
  code : ∀ address, account address →
    code ((TransactionState.ofBlock block).getAccount address).codeHash
  /-- Each such account with nonce 0 and no code in the block is in the whole-storage set. -/
  allStorage : ∀ address, account address →
    ((TransactionState.ofBlock block).getAccount address).nonce = 0 →
    ((TransactionState.ofBlock block).getAccount address).codeHash = EMPTY_CODE_HASH →
    allStorage address

/-- The read and written accounts, slots and code hashes of a transaction cover its block. -/
theorem CoversBlock.ofTracker (block : BlockState) (endState : TransactionState) :
    CoversBlock block (TransactionState.accessedAccount endState)
      (TransactionState.candidateStorage block endState)
      (TransactionState.accessedCode block endState) :=
  ⟨fun address h => ⟨address, h, rfl⟩, fun _ h hnonce hcode => ⟨h, hnonce, hcode⟩⟩

/-! ## A caller always has room to resume -/

section Room

open EthLib.Base (U256)

omit [GasMeter Meter] in
/-- A pop leaves one word fewer on the stack. -/
private theorem length_popWord {evm after : Evm fork Meter} {x : U256}
    (h : popWord evm = .ok (x, after)) : after.stack.val.length + 1 = evm.stack.val.length := by
  rw [(popWord_eq_ok h).1, List.length_cons]

omit [GasMeter Meter] in
/-- An access to an address keeps the stack. -/
private theorem stack_accessAddress (evm : Evm fork Meter) (address : Address) :
    (accessAddress evm address).2.stack = evm.stack := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]

/-- A charge keeps the stack. -/
private theorem stack_chargeGas {evm after : Evm fork Meter} {cost : Nat}
    (h : chargeGas evm cost = .ok after) : after.stack = evm.stack := by
  obtain ⟨_, -, rfl⟩ := chargeGas_eq_ok_iff_charge.mp h
  rfl

/-- A charge of state gas keeps the stack. -/
private theorem stack_chargeStateGas {evm after : Evm fork Meter} {cost : Nat}
    (h : chargeStateGas evm cost = .ok after) : after.stack = evm.stack := by
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- The access to a delegate keeps the stack. -/
private theorem stack_accessDelegation {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    after.stack = evm.stack := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact stack_accessAddress _ _
  · cases h
    rfl

/-- The payment of a call keeps the stack. -/
private theorem stack_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    after.stack = evm.stack := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (stack_chargeGas h3).trans ((stack_chargeStateGas h2).trans (stack_chargeGas h1))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact stack_chargeGas h1

/-- The frame that a step leaves to send a message holds fewer words than the frame before. -/
private def ShortCaller (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next _ => True
  | .child caller _ _ => caller.stack.val.length < evm.stack.val.length

/-- The end of a call sends a message from a frame with the stack it starts from. -/
private theorem shortCaller_finishCall {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm before : Evm fork Meter}
    {result : StepResult fork Meter}
    (hlt : evm.stack.val.length < before.stack.val.length)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ShortCaller before result := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, -, rfl⟩ := Base.map_ok_iff.mp h
    trivial
  · unfold Evm.genericCall at h
    dsimp only at h
    split at h
    · obtain ⟨after, -, rfl⟩ := Base.map_ok_iff.mp h
      trivial
    · cases h
      exact hlt

omit [GasMeter Meter] in
/-- The pops of a call take at least one word. -/
private theorem length_popCallOperands {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    after.stack.val.length < evm.stack.val.length := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have l3 : e3.stack.val.length ≤ e2.stack.val.length := by
    unfold popCallValue at h3
    split at h3
    · exact Nat.le_of_lt_succ (Nat.lt_succ_of_le (by have := length_popWord h3; omega))
    · cases h3
      exact Nat.le_refl _
  have := length_popWord h1
  have := length_popWord h2
  have := length_popWord h4
  have := length_popWord h5
  have := length_popWord h6
  have := length_popWord h7
  omega

/-- A call sends its message from a frame that holds fewer words. -/
private theorem shortCaller_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    ShortCaller evm result := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have l1 := length_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have s2 : e2.stack = e1.stack := by
    have := stack_accessAddress e1 call.address
    rw [hacc] at this
    exact this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 := stack_accessDelegation h4
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      refine shortCaller_finishCall ?_ h
      rw [stack_payCall h5, s4]
      change e2.stack.val.length < _
      rw [s2]
      exact l1
    · trivial
  · trivial

/-- A launch of a creation sends its message from a frame with the stack it starts from. -/
private theorem shortCaller_launchCreate {evm before : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (hlt : evm.stack.val.length < before.stack.val.length)
    (h : launchCreate evm value initCode salt = .ok result) : ShortCaller before result := by
  unfold Evm.launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, -, rfl⟩ := Base.map_ok_iff.mp h
    trivial
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    split at hr
    · cases hr
      change e2.stack.val.length < _
      rw [stack_chargeGas h2, stack_chargeStateGas h1]
      change (accessAddress _ address).2.stack.val.length < _
      rw [stack_accessAddress]
      exact hlt
    · obtain ⟨e3, -, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      trivial
  · trivial

/-- CREATE and CREATE2 send their message from a frame that holds fewer words. -/
private theorem shortCaller_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    ShortCaller evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨value, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨start, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨size, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨paid, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨word, -, s4⟩, -, -⟩ := popSalt_eq_ok h4
  obtain ⟨-, -, hlaunch⟩ := genericCreate_eq_ok h
  refine shortCaller_launchCreate ?_ hlaunch
  have s5 : paid.stack = e4.stack := by
    obtain ⟨e, he, hr⟩ := Base.bind_ok_iff.mp h5
    cases hr
    have := stack_chargeGas he
    exact this
  have l4 : e4.stack.val.length ≤ e3.stack.val.length := by
    rw [s4, List.length_append]
    exact Nat.le_add_left _ _
  have := length_popWord h1
  have := length_popWord h2
  have := length_popWord h3
  rw [s5]
  omega

/-- An instruction that may send a message sends it from a frame that holds fewer words. -/
private theorem shortCaller_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : ShortCaller evm result := by
  unfold Evm.messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact shortCaller_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact shortCaller_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact shortCaller_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact shortCaller_createStep h
         · cases hrun)

/-- Every step sends its message from a frame that holds fewer words. -/
private theorem shortCaller_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : ShortCaller evm result := by
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
          exact shortCaller_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    trivial

omit [GasMeter Meter] in
/-- A push onto a stack with room never fails. -/
private theorem pushWord_ne_error {evm : Evm fork Meter} {x : U256} {e : EvmError}
    (hne : evm.stack.val.length ≠ STACK_LIMIT) : pushWord evm x ≠ .error e := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact hne (Stack.push_eq_error_iff.mp h).1
  · cases h

/-- A caller resumes from every frame that ends the message it sends, with room on its stack. -/
private theorem resume_ne_error {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) (child : Evm fork Meter)
    (e : EvmError) : resume child ≠ .error e := by
  have hne : caller.stack.val.length ≠ STACK_LIMIT :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (shortCaller_step h) evm.stack.property)
  have hinc : (incorporateChild fork caller child).stack = caller.stack := by
    unfold incorporateChild
    split <;> rfl
  intro hres
  rcases step_eq_child_resume h with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩
  · unfold resumeCall at hres
    rcases Base.bind_eq_error hres with hp | ⟨_, -, hk⟩
    · refine pushWord_ne_error ?_ hp
      split <;> exact hinc ▸ hne
    · cases hk
  · unfold resumeCreate at hres
    rcases Base.bind_eq_error hres with hp | ⟨_, -, hk⟩
    · refine pushWord_ne_error ?_ hp
      split <;> exact hinc ▸ hne
    · cases hk

end Room

/-! ## What the first run keeps -/

section Kept

/-- The second frame keeps the reads, the origin of the code hashes and the candidates. -/
private def Kept (a b : Evm fork Meter) : Prop :=
  a.state.ReadsLe b.state ∧ KeepsCodeOrigin a.state b.state ∧ KeepsCandidates a.state b.state

/-- Each write of a step keeps the reads, the origin of the code hashes and the candidates. -/
private theorem stepRules_kept : StepRules fork (Kept (fork := fork) (Meter := Meter)) :=
  stepRules_readsLe.and (stepRules_keepsCodeOrigin.and stepRules_keepsCandidates)

/-- A step keeps the reads, the origin of the code hashes, the candidates and the message. -/
private def KeptStep (a b : Evm fork Meter) : Prop :=
  Kept a b ∧ b.message = a.message

/-- A step keeps what a run keeps, and its message, when each child keeps what its caller has. -/
private theorem step_keptStep {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) :
    result.Keeps KeptStep (fun caller _ child => Kept caller child) evm := by
  have r := (stepRules_kept.and stepRules_messageCode).step h
  cases result with
  | next after => exact ⟨r.1, r.2.1⟩
  | child caller message resume =>
    refine ⟨⟨r.1.1, r.1.2.1⟩, fun child after hres hc => ?_⟩
    have same := sameContext_of_step_eq_child h hres
    have hk : Kept evm child := stepRules_kept.trans r.1.1 hc
    refine ⟨?_, ?_⟩
    · unfold Kept at hk ⊢
      rw [same.state, state_incorporateChild]
      exact hk
    · rw [same.message, message_incorporateChild]
      exact r.1.2.1

/-- A deposit of code keeps the message of the frame. -/
private theorem message_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) : after.message = evm.message := by
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
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rfl

/-- By induction on gas, every call and creation ends with its own message. -/
private theorem processMessage_message [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ended.val.message = message) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ended.val.message = message) := by
  have T := stepRules_messageCode (fork := fork) (Meter := Meter)
  refine processMessage_rel_byKind
    (R := fun a b : Evm fork Meter => b.message = a.message ∧ b.code = a.code)
    (Inv := fun _ => True) (Mcall := fun message _ _ _ ended => ended.message = message)
    (Mcreate := fun message _ _ _ ended => ended.message = message) T.refl T.trans
    (fun _ _ => trivial) (fun _ _ _ => ⟨rfl, rfl⟩) ?_ (fun _ _ => ⟨rfl, rfl⟩)
    (fun h _ => ⟨(staticStep_runPrecompile h).message, (staticStep_runPrecompile h).code⟩)
    (fun _ hrun => (message_rollbackOnError _ _).trans (hrun trivial).1)
    (fun _ hm hd => (message_depositCode hd).trans hm) n
  intro evm result _ h
  have r := T.step h
  cases result with
  | next after => exact r
  | child caller message resume =>
    refine ⟨r.1, fun child after hres _ => ?_⟩
    have same := sameContext_of_step_eq_child h hres
    exact ⟨same.message.trans ((message_incorporateChild _ _).trans r.1.1),
      same.code.trans ((code_incorporateChild _ _).trans r.1.2)⟩

end Kept

/-! ## The parts of a message on two agreeing states -/

section Parts

open EthLib.Base (ExceptRel)
open EthLib.Execution.State.TransactionState (SameTracker)

variable {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop}

/-- A state with fewer reads than one whose reads are in the sets has its reads in the sets. -/
theorem ReadsIn.of_readsLe {tx tx' : TransactionState} (h : tx.ReadsLe tx')
    (hr : ReadsIn account slot tx') : ReadsIn account slot tx :=
  ⟨fun a ha => hr.account a (h.accountReads a ha),
    fun a k hk => hr.slot a k (h.storageReads a k hk)⟩

/-- With code hashes from the block or writes, each covered account has its hash in the sets. -/
private theorem codesIn_of_codeOrigin {block : BlockState}
    (covers : CoversBlock block account allStorage code) {tx : TransactionState}
    (h : CodeOrigin block tx) : CodesIn account code tx := fun a ha =>
  (h a).imp_right (Or.imp_right fun heq => by rw [heq]; exact covers.code a ha)

/-- With no new candidate, each candidate of the first set was wiped or is in the second set. -/
private theorem candidatesIn_of_noNewCandidate {block : BlockState}
    (covers : CoversBlock block account allStorage code) {tx : TransactionState}
    (h : NoNewCandidate block tx) : CandidatesIn account allStorage tx := fun a ha hn hc =>
  (h a hn hc).imp_right fun ⟨hn', hc'⟩ => covers.allStorage a ha hn' hc'

/-- Rollbacks to snapshots with the same tracker keep agreeing frames. -/
private theorem rollbackOnError_agrees {state other : TransactionState}
    (hs : SameTracker state other) {a b : Evm fork Meter}
    (h : FrameAgrees account allStorage slot code a b) :
    FrameAgrees account allStorage slot code (rollbackOnError state a)
      (rollbackOnError other b) := by
  obtain ⟨s, rfl⟩ : ∃ s, b = { a with state := s } := ⟨_, h.rest⟩
  unfold rollbackOnError
  dsimp only
  split
  · exact ⟨rfl, h.state.restoreTxState hs⟩
  · exact h

/-- A precompile on a frame with another state gives the same frame with that state. -/
private theorem runPrecompile_withState (address : Nat) (evm : Evm fork Meter)
    (s : TransactionState) :
    runPrecompile fork address { evm with state := s } =
      (runPrecompile fork address evm).map fun after => { after with state := s } := by
  unfold runPrecompile
  dsimp only
  split <;> (try split) <;> rfl

/-- The start states of a message agree on agreeing states, when its account is in the sets. -/
private theorem startState_agrees {message : Message fork} {state other : TransactionState}
    (h : AgreesOn account allStorage slot code state other)
    (hacc : account message.currentTarget) :
    AgreesOn account allStorage slot code (startState fork message state)
      (startState fork message other) := by
  unfold startState
  split
  · exact h.touchAccount (.inr hacc)
  · exact h

/-- A move of ether reads its sender. -/
private theorem mem_reads_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : Base.U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    sender ∈ tx'.accountReads := by
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  obtain ⟨_, _, hacc1, -⟩ := TransactionState.reads_modifyState h1
  obtain ⟨_, _, hacc2, -⟩ := TransactionState.reads_modifyState h2
  rw [hacc2, hacc1]
  exact Std.ExtTreeSet.mem_insert.mpr (.inr Std.ExtTreeSet.mem_insert_self)

/-- The preparations of a creation agree on agreeing states, when its address is in the sets. -/
private theorem prepareCreation_agrees {state other : TransactionState}
    (h : AgreesOn account allStorage slot code state other) {address : Address}
    (ha : account address) :
    ExceptRel (AgreesOn account allStorage slot code) (prepareCreation fork state address)
      (prepareCreation fork other address) := by
  unfold prepareCreation
  dsimp only
  have hw := (h.destroyStorage address).markAccountCreated address
  split
  · exact (hw.incrementNonce fork (.inr ha)).mapError _
  · exact hw

/-- The deposits of code from agreeing frames agree, when the new address is in the sets. -/
private theorem depositCode_agrees {state other : TransactionState}
    (hs : SameTracker state other) {a b after : Evm fork Meter}
    (h : FrameAgrees account allStorage slot code a b) (ha : account a.message.currentTarget)
    (hd : depositCode fork state a = .ok after) :
    ∃ after', depositCode fork other b = .ok after' ∧
      FrameAgrees account allStorage slot code after after' := by
  obtain ⟨s, rfl⟩ : ∃ s, b = { a with state := s } := ⟨_, h.rest⟩
  have hst : AgreesOn account allStorage slot code a.state s := h.state
  unfold depositCode at hd ⊢
  dsimp only at hd ⊢
  split at hd
  · cases hd
    rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    exact ⟨_, rfl, rfl, hst.restoreTxState hs⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]
  split at hd
  · cases hd
    rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    exact ⟨_, rfl, rfl, hst.restoreTxState hs⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]
  split at hd
  · cases hd
    rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    exact ⟨_, rfl, rfl, hst.restoreTxState hs⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]
  split at hd
  · cases hd
    refine ⟨_, rfl, ?_⟩
    split
    · exact ⟨rfl, hst.restoreTxState hs⟩
    · exact ⟨rfl, hst⟩
  · split at hd
    · cases hd
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
      exact ⟨_, rfl, rfl, hst.restoreTxState hs⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]
    obtain ⟨st, hset, hd⟩ := Base.bind_ok_iff.mp hd
    cases hd
    have hrel := (hst.setCode fork (.inr ha) a.output).mapError EvmError.state
    rw [hset] at hrel
    cases hset' : (s.setCode fork a.message.currentTarget a.output).mapError EvmError.state with
    | error e =>
      rw [hset'] at hrel
      exact absurd hrel id
    | ok st' =>
      rw [hset'] at hrel
      exact ⟨_, rfl, rfl, hrel⟩

/-! ## Two runs of a frame -/

/-- A frame with code hashes from the block or writes, no new candidate, and its account read. -/
private def Fit (block : BlockState) (evm : Evm fork Meter) : Prop :=
  CodeOrigin block evm.state ∧ NoNewCandidate block evm.state ∧
    evm.message.currentTarget ∈ evm.state.accountReads

omit [GasMeter Meter] in
/-- A step that keeps what a run keeps, and the message, keeps a fit frame fit. -/
private theorem Fit.of_keptStep {block : BlockState} {a b : Evm fork Meter} (h : Fit block a)
    (k : KeptStep a b) : Fit block b :=
  ⟨h.1.of_keepsCodeOrigin k.1.2.1, h.2.1.of_keepsCandidates k.1.2.2,
    by rw [k.2]; exact k.1.1.accountReads _ h.2.2⟩

section Unfold

variable {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Meter bound} {evm : Evm fork Meter}
  {within : GasMeter.gasHeld evm.gas ≤ bound}

/-- A run whose step fails without aborting halts the frame. -/
private theorem runFrame_of_halt (running : evm.running = true) {e : EvmError}
    (hstep : step evm = .error e) (aborts : e.aborts = false) :
    runFrame step decreases bound runChild evm within = .ok (exceptionalHalt evm e) := by
  rw [runFrame, dite_eq_left_of_eq_true (eq_true running)]
  split
  · rename_i heq
    rw [hstep] at heq
    cases heq
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [aborts]))]
  all_goals
    rename_i heq
    rw [hstep] at heq
    cases heq

/-- A run whose step gives the next frame goes on from that frame. -/
private theorem runFrame_of_next (running : evm.running = true) {after : Evm fork Meter}
    (hstep : step evm = .ok (.next after)) (within' : GasMeter.gasHeld after.gas ≤ bound) :
    runFrame step decreases bound runChild evm within =
      runFrame step decreases bound runChild after within' := by
  rw [runFrame, dite_eq_left_of_eq_true (eq_true running)]
  split
  all_goals
    rename_i heq
    rw [hstep] at heq
    cases heq
  rfl

/-- A run whose step sends a message goes on from the frame that resumes after it. -/
private theorem runFrame_of_child (running : evm.running = true) {caller after : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : step evm = .ok (.child caller message resume)) (lt : message.gas < bound)
    {ended : { child : Evm fork Meter // GasMeter.gasHeld child.gas ≤ message.gas }}
    (hran : runChild caller message lt = .ok ended) (resumed : resume ended.val = .ok after)
    (within' : GasMeter.gasHeld after.gas ≤ bound) :
    runFrame step decreases bound runChild evm within =
      runFrame step decreases bound runChild after within' := by
  rw [runFrame, dite_eq_left_of_eq_true (eq_true running)]
  split
  all_goals
    rename_i heq
    rw [hstep] at heq
    cases heq
  dsimp only
  split
  · rename_i heq
    rw [hran] at heq
    cases heq
  · rename_i heq
    rw [hran] at heq
    cases heq
    split
    · rename_i heq
      rw [resumed] at heq
      cases heq
    · rename_i heq
      rw [resumed] at heq
      cases heq
      rfl

end Unfold

/-- Runs of a frame from agreeing fit frames agree when the first ends with reads in the sets. -/
private theorem runFrame_agrees [LawfulGasMeter Meter] {block : BlockState}
    (covers : CoversBlock block account allStorage code) {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (ens : RunnerEnsures (fun caller message child => Kept caller child ∧ child.message = message)
      runChild)
    (sim : ∀ c1 c2 message lt ended, FrameAgrees account allStorage slot code c1 c2 →
      CodeOrigin block c1.state → NoNewCandidate block c1.state →
      message.currentTarget ∈ c1.state.accountReads → runChild c1 message lt = .ok ended →
      ReadsIn account slot ended.val.state →
      ∃ ended', runChild c2 message lt = .ok ended' ∧
        FrameAgrees account allStorage slot code ended.val ended'.val)
    {e1 after : Evm fork Meter} {within : GasMeter.gasHeld e1.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild e1 within = .ok after) :
    ∀ e2 (within' : GasMeter.gasHeld e2.gas ≤ bound),
      FrameAgrees account allStorage slot code e1 e2 → Fit block e1 →
      ReadsIn account slot after.state →
      ∃ after', runFrame (step fork) (step_decreases fork) bound runChild e2 within' = .ok after' ∧
        FrameAgrees account allStorage slot code after after' := by
  have kept : ∀ {a b : Evm fork Meter} {w : GasMeter.gasHeld a.gas ≤ bound},
      runFrame (step fork) (step_decreases fork) bound runChild a w = .ok b → Kept a b :=
    fun hrun => stepRules_kept.runFrame (fun c m lt ended hr => (ens c m lt ended hr).1) hrun
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild e1 within
  case case1 => cases h
  case case4 => cases h
  case case5 => cases h
  case case8 _ _ running =>
    cases h
    intro e2 w hagree _ _
    obtain ⟨s, rfl⟩ : ∃ s, e2 = { after with state := s } := ⟨_, hagree.rest⟩
    refine ⟨_, ?_, hagree⟩
    rw [runFrame]
    exact dite_eq_right_of_eq_false (eq_false running)
  case case2 evm _ running e hstep aborts =>
    cases h
    intro e2 w hagree hfit hreads
    obtain ⟨s, rfl⟩ : ∃ s, e2 = { evm with state := s } := ⟨_, hagree.rest⟩
    have aborts' : e.aborts = false := Bool.eq_false_iff.mpr aborts
    obtain ⟨herr, -⟩ := step_agrees hagree (codesIn_of_codeOrigin covers hfit.1)
      (candidatesIn_of_noNewCandidate covers hfit.2.1) (hreads.account _ hfit.2.2)
    exact ⟨_, runFrame_of_halt (by exact running) (herr _ hstep aborts') aborts', rfl,
      hagree.state⟩
  case case3 evm _ running a1 hstep lower ih =>
    intro e2 w hagree hfit hreads
    obtain ⟨s, rfl⟩ : ∃ s, e2 = { evm with state := s } := ⟨_, hagree.rest⟩
    have ks : KeptStep evm a1 := step_keptStep hstep
    have kr : Kept a1 after := kept h
    have hcur : account evm.message.currentTarget :=
      hreads.account _ (kr.1.accountReads _ (ks.1.1.accountReads _ hfit.2.2))
    obtain ⟨-, hok⟩ := step_agrees hagree (codesIn_of_codeOrigin covers hfit.1)
      (candidatesIn_of_noNewCandidate covers hfit.2.1) hcur
    obtain ⟨r2, hr2, hsa⟩ := hok _ hstep (ReadsIn.of_readsLe kr.1 hreads)
    cases r2 with
    | child => exact hsa.elim
    | next a2 =>
      have hg : a2.gas = a1.gas := by rw [hsa.rest]
      have w2 : GasMeter.gasHeld a2.gas ≤ bound := by
        rw [hg]
        exact Nat.le_trans (gasHeld_le_of_measure_lt lower) (by assumption)
      obtain ⟨after', hrun', hfa⟩ := ih h a2 w2 hsa (hfit.of_keptStep ks) hreads
      exact ⟨after', (runFrame_of_next (by exact running) hr2 w2).trans hrun', hfa⟩
  case case6 _ _ _ _ _ _ hstep _ _ _ _ _ resumed _ =>
    exact absurd resumed (resume_ne_error hstep _ _)
  case case7 evm _ running c1 m k1 hstep _ child1 used hran a1 resumed lower ih =>
    intro e2 w hagree hfit hreads
    obtain ⟨s, rfl⟩ : ∃ s, e2 = { evm with state := s } := ⟨_, hagree.rest⟩
    have ks := step_keptStep hstep
    have hens := ens c1 m _ ⟨child1, used⟩ hran
    have ka1 : KeptStep evm a1 := ks.2 child1 a1 resumed hens.1
    have kr : Kept a1 after := kept h
    have same := sameContext_of_step_eq_child hstep resumed
    have hreadsA : ReadsIn account slot a1.state := .of_readsLe kr.1 hreads
    have hreadsChild : ReadsIn account slot child1.state := by
      rw [same.state, state_incorporateChild] at hreadsA
      exact hreadsA
    have hreadsC1 : ReadsIn account slot c1.state := .of_readsLe hens.1.1 hreadsChild
    have hcur : account evm.message.currentTarget :=
      hreads.account _ (kr.1.accountReads _ (ka1.1.1.accountReads _ hfit.2.2))
    obtain ⟨-, hok⟩ := step_agrees hagree (codesIn_of_codeOrigin covers hfit.1)
      (candidatesIn_of_noNewCandidate covers hfit.2.1) hcur
    obtain ⟨r2, hr2, hsa⟩ := hok _ hstep hreadsC1
    cases r2 with
    | next => exact hsa.elim
    | child c2 m2 k2 =>
      obtain ⟨hfc, hm, hres⟩ := hsa
      subst m2
      have fitC1 := hfit.of_keptStep ks.1
      have hmcur : m.currentTarget ∈ c1.state.accountReads := step_eq_child_currentRead hstep
      obtain ⟨ended2, hran2, hfe⟩ :=
        sim c1 c2 m _ ⟨child1, used⟩ hfc fitC1.1 fitC1.2.1 hmcur hran hreadsChild
      have haccChild : account child1.message.currentTarget := by
        rw [hens.2]
        exact hreadsC1.account _ hmcur
      obtain ⟨-, hk⟩ := hres child1 ended2.val hfe haccChild
      obtain ⟨a2, hk2, hfa⟩ := hk a1 resumed hreadsA
      have hg : a2.gas = a1.gas := by rw [hfa.rest]
      have w2 : GasMeter.gasHeld a2.gas ≤ bound := by
        rw [hg]
        exact Nat.le_trans (gasHeld_le_of_measure_lt lower) (by assumption)
      obtain ⟨after', hrun', hfa'⟩ := ih h a2 w2 hfa (hfit.of_keptStep ka1) hreads
      exact ⟨after', (runFrame_of_child (by exact running) hr2 _ hran2 hk2 w2).trans hrun', hfa'⟩

/-! ## Two runs of a message -/

/-- The runner of the messages that a frame sends: a call or a creation, as a message runs them. -/
private def runner [LawfulGasMeter Meter] (fork : Base.Fork) (bound : Nat) :
    MessageRunner fork Meter bound := fun caller child _ =>
  match child.target with
  | some _ => processMessage fork child caller.state caller.substate.child
  | none => processCreateMessage fork child caller.state caller.substate.child

/-- The runner keeps what a run keeps, and ends each message with that message. -/
private theorem runner_ensures [LawfulGasMeter Meter] (bound : Nat) :
    RunnerEnsures (fun caller message child => Kept caller child ∧ child.message = message)
      (runner (Meter := Meter) fork bound) := by
  intro caller message lt ended h
  unfold runner at h
  split at h
  · exact ⟨⟨readsLe_processMessage h, keepsCodeOrigin_processMessage h,
      keepsCandidates_processMessage h⟩, (processMessage_message _).1 _ _ _ _ _ rfl _ h⟩
  · exact ⟨⟨readsLe_processCreateMessage h, keepsCodeOrigin_processCreateMessage h,
      keepsCandidates_processCreateMessage h⟩, (processMessage_message _).2 _ _ _ _ _ rfl _ h⟩

/-- The state that a message enters, before or after the move of its value. -/
private def enterState (fork : Base.Fork) (message : Message fork) (state : TransactionState) :
    Except EvmError TransactionState :=
  if message.shouldTransferValue = true ∧ message.value ≠ 0 then
    ((startState fork message state).moveEther fork message.caller message.currentTarget
      message.value).mapError .state
  else pure (startState fork message state)

/-- The substate that a message enters, with the log of the move of its value if any. -/
private def enterSubstate (fork : Base.Fork) (message : Message fork) (substate : Substate) :
    Substate :=
  if message.shouldTransferValue = true ∧ message.value ≠ 0 then
    { substate with
      logs := pushTransferLog fork substate.logs message.caller message.currentTarget
        message.value }
  else substate

/-- A message runs its code or its precompile from the state it enters. -/
private def runBody [LawfulGasMeter Meter] (fork : Base.Fork) (message : Message fork)
    (substate : Substate) (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas)
    (state : TransactionState) :
    Except EvmError { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } :=
  let evm : Evm fork Meter := startFrame message state (enterSubstate fork message substate) meter
  match precompileAddress fork message with
  | some address =>
    if message.disablePrecompiles then
      pure ⟨{ evm with running := false }, held⟩
    else
      match h : runPrecompile fork address evm with
      | some after => pure ⟨after, Nat.le_trans (gasHeld_runPrecompile_le h) held⟩
      | none => pure ⟨{ evm with running := false }, held⟩
  | none =>
    match h : runFrame (step fork) (step_decreases fork) message.gas (runner fork message.gas)
        evm held with
    | .error e => throw e
    | .ok after => pure ⟨after, Nat.le_trans (gasHeld_runFrame_le h) held⟩

omit [GasMeter Meter] in
/-- A success followed by a success with a property is a success with that property. -/
private theorem exists_bind_ok {α β : Type} {x : Except EvmError α} {a : α}
    {k : α → Except EvmError β} {P : β → Prop} (hx : x = .ok a) (hk : ∃ b, k a = .ok b ∧ P b) :
    ∃ b, x >>= k = .ok b ∧ P b := by
  rw [hx]
  exact hk

/-- A rollback leaves at most the gas of the message. -/
private theorem gasHeld_rollbackOnError_le [LawfulGasMeter Meter] {message : Message fork}
    (state : TransactionState)
    (ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }) :
    GasMeter.gasHeld (rollbackOnError state ended.val).gas ≤ message.gas := by
  unfold rollbackOnError
  split
  · dsimp only
    split
    · exact Nat.le_trans (LawfulGasMeter.gasHeld_rollback _) ended.property
    · exact ended.property
  · exact ended.property

/-- A call enters its state, runs its body, and rolls back on an error. -/
private theorem processMessage_eq [LawfulGasMeter Meter] (message : Message fork)
    (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) :
    processMessage fork message state substate meter held =
      Except.map (fun ended => ⟨rollbackOnError state ended.val,
        gasHeld_rollbackOnError_le state ended⟩)
        (enterState fork message state >>= runBody fork message substate meter held) := by
  rw [processMessage]
  unfold enterState runBody enterSubstate
  dsimp only
  split <;> rfl

/-- A message enters the state and the substate that its start describes. -/
private theorem entered_of_enterState {message : Message fork} {state entry : TransactionState}
    (substate : Substate) (h : enterState fork message state = .ok entry) :
    Entered fork message state substate entry (enterSubstate fork message substate) := by
  unfold enterState at h
  unfold enterSubstate
  split at h
  · exact .inr ⟨‹_›, Base.mapError_ok_iff.mp h, by rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]⟩
  · cases h
    exact .inl ⟨‹_›, rfl, by rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]⟩

/-- Agreeing states enter agreeing states, when the accounts the move reads are in the sets. -/
private theorem enterState_agrees {message : Message fork} {state other entry : TransactionState}
    (h : AgreesOn account allStorage slot code state other) (hacc : account message.currentTarget)
    (hreads : ∀ address, address ∈ entry.accountReads → account address)
    (hent : enterState fork message state = .ok entry) :
    ∃ entry', enterState fork message other = .ok entry' ∧
      AgreesOn account allStorage slot code entry entry' := by
  have hstart := startState_agrees (fork := fork) (message := message) h hacc
  unfold enterState at hent ⊢
  split at hent
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
    have hmoved := Base.mapError_ok_iff.mp hent
    have rel := (hstart.moveEther fork (.inr (hreads _ (mem_reads_moveEther hmoved))) (.inr hacc)
      message.value).mapError EvmError.state
    rw [hent] at rel
    cases hent' : ((startState fork message other).moveEther fork message.caller
        message.currentTarget message.value).mapError EvmError.state with
    | error e =>
      rw [hent'] at rel
      exact absurd rel id
    | ok entry' =>
      rw [hent'] at rel
      exact ⟨entry', rfl, rel⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]
    cases hent
    exact ⟨_, rfl, hstart⟩

/-- A precompile keeps the state of the frame. -/
private theorem state_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : after.state = evm.state := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    rfl
  · split at h <;> cases h <;> rfl

/-- The body of a message keeps every read of the state it starts from. -/
private theorem readsLe_runBody [LawfulGasMeter Meter] {message : Message fork}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    {state : TransactionState} {ended}
    (h : runBody fork message substate meter held state = .ok ended) :
    state.ReadsLe ended.val.state := by
  unfold runBody at h
  dsimp only at h
  split at h
  · split at h
    · cases h
      exact .refl _
    · split at h
      · rename_i hp
        cases h
        exact (staticStep_runPrecompile hp).tracker.readsLe
      · cases h
        exact .refl _
  · split at h
    · cases h
    · rename_i hrun
      cases h
      exact readsLe_runFrame (fun c m lt e hr => (runner_ensures _ c m lt e hr).1.1) hrun

/-- A message body from agreeing fit states agrees when the first ends with reads in the sets. -/
private theorem runBody_agrees [LawfulGasMeter Meter] {block : BlockState}
    (covers : CoversBlock block account allStorage code) {message : Message fork}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (sim : ∀ c1 c2 m lt ended, FrameAgrees account allStorage slot code c1 c2 →
      CodeOrigin block c1.state → NoNewCandidate block c1.state →
      m.currentTarget ∈ c1.state.accountReads →
      runner (Meter := Meter) fork message.gas c1 m lt = .ok ended →
      ReadsIn account slot ended.val.state →
      ∃ ended', runner (Meter := Meter) fork message.gas c2 m lt = .ok ended' ∧
        FrameAgrees account allStorage slot code ended.val ended'.val)
    {state other : TransactionState} (hagree : AgreesOn account allStorage slot code state other)
    (hfit : Fit block (startFrame message state (enterSubstate fork message substate) meter))
    {ended} (h : runBody fork message substate meter held state = .ok ended)
    (hreads : ReadsIn account slot ended.val.state) :
    ∃ ended', runBody fork message substate meter held other = .ok ended' ∧
      FrameAgrees account allStorage slot code ended.val ended'.val := by
  unfold runBody at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i address _
    split at h
    · cases h
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹_›)]
      exact ⟨_, rfl, rfl, hagree⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ‹_›)]
      have hws : runPrecompile fork address
          (startFrame message other (enterSubstate fork message substate) meter) =
          (runPrecompile fork address
            (startFrame message state (enterSubstate fork message substate) meter)).map
            fun after => { after with state := other } :=
        runPrecompile_withState address
          (startFrame message state (enterSubstate fork message substate) meter) other
      split at h
      · rename_i after hp
        cases h
        rw [hp] at hws
        split
        · rename_i heq
          rw [hws] at heq
          cases heq
          exact ⟨_, rfl, rfl, by rw [state_runPrecompile hp]; exact hagree⟩
        · rename_i heq
          rw [hws] at heq
          cases heq
      · rename_i hp
        cases h
        rw [hp] at hws
        split
        · rename_i heq
          rw [hws] at heq
          cases heq
        · exact ⟨_, rfl, rfl, hagree⟩
  · split at h
    · cases h
    · rename_i after hrun
      cases h
      obtain ⟨after', hrun', hfa⟩ := runFrame_agrees covers (runner_ensures _) sim hrun
        (startFrame message other (enterSubstate fork message substate) meter) held
        ⟨rfl, hagree⟩ hfit hreads
      split
      · rename_i heq
        rw [hrun'] at heq
        cases heq
      · rename_i heq
        rw [hrun'] at heq
        cases heq
        exact ⟨_, rfl, hfa⟩

/-- Runs of a message from agreeing fit states agree when the first ends with reads in the sets. -/
private def MessageAgrees (block : BlockState) (account allStorage : Address → Prop)
    (slot : Address → Bytes32 → Prop) (code : Hash32 → Prop)
    (run : (message : Message fork) → TransactionState → Substate → (meter : Meter) →
      GasMeter.gasHeld meter ≤ message.gas →
      Except EvmError { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas })
    (n : Nat) : Prop :=
  ∀ (message : Message fork) (state other : TransactionState) (substate : Substate)
    (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
    AgreesOn account allStorage slot code state other → CodeOrigin block state →
    NoNewCandidate block state → message.currentTarget ∈ state.accountReads →
    ∀ ended, run message state substate meter held = .ok ended →
    ReadsIn account slot ended.val.state →
    ∃ ended', run message other substate meter held = .ok ended' ∧
      FrameAgrees account allStorage slot code ended.val ended'.val

/-- By induction on gas, a call or a creation from agreeing fit states agrees.

The first run must end with its reads in the sets. -/
private theorem agrees_induction [LawfulGasMeter Meter] {block : BlockState}
    (covers : CoversBlock block account allStorage code) (n : Nat) :
    MessageAgrees (Meter := Meter) block account allStorage slot code
        (fun m s sub meter held => processMessage fork m s sub meter held) n ∧
      MessageAgrees (Meter := Meter) block account allStorage slot code
        (fun m s sub meter held => processCreateMessage fork m s sub meter held) n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have callCase : MessageAgrees (Meter := Meter) block account allStorage slot code
        (fun m s sub meter held => processMessage fork m s sub meter held) n := by
      intro message state other substate meter held hn hagree horigin hcand hcurrent ended h
        hreads
      dsimp only at h ⊢
      have hacc : account message.currentTarget :=
        hreads.account _ ((readsLe_processMessage h).accountReads _ hcurrent)
      rw [processMessage_eq] at h ⊢
      obtain ⟨ended0, hdo, rfl⟩ := Base.map_ok_iff.mp h
      obtain ⟨entry, hent, hbody⟩ := Base.bind_ok_iff.mp hdo
      have hreads0 : ReadsIn account slot ended0.val.state :=
        .of_readsLe (readsLe_rollbackOnError state ended0.val) hreads
      have hreadsEntry : ReadsIn account slot entry := .of_readsLe (readsLe_runBody hbody) hreads0
      obtain ⟨entry', hent', hagree'⟩ := enterState_agrees hagree hacc hreadsEntry.account hent
      have hentered := entered_of_enterState substate hent
      have sim : ∀ c1 c2 m lt ended, FrameAgrees account allStorage slot code c1 c2 →
          CodeOrigin block c1.state → NoNewCandidate block c1.state →
          m.currentTarget ∈ c1.state.accountReads →
      runner (Meter := Meter) fork message.gas c1 m lt = .ok ended →
          ReadsIn account slot ended.val.state →
          ∃ ended', runner (Meter := Meter) fork message.gas c2 m lt = .ok ended' ∧
            FrameAgrees account allStorage slot code ended.val ended'.val := by
        intro c1 c2 m lt ended1 hfc ho hc hm hr hri
        obtain ⟨s, rfl⟩ : ∃ s, c2 = { c1 with state := s } := ⟨_, hfc.rest⟩
        unfold runner at hr ⊢
        split at hr
        · exact (ih m.gas (hn ▸ lt)).1 m c1.state s c1.substate.child _ _ rfl hfc.state ho hc hm
            ended1 hr hri
        · exact (ih m.gas (hn ▸ lt)).2 m c1.state s c1.substate.child _ _ rfl hfc.state ho hc hm
            ended1 hr hri
      obtain ⟨ended0', hbody', hfa⟩ := runBody_agrees covers sim hagree'
        ⟨horigin.of_keepsCodeOrigin (keepsCodeOrigin_entered hentered),
          hcand.of_keepsCandidates (keepsCandidates_entered hentered),
          (readsLe_entered hentered).accountReads _ hcurrent⟩ hbody hreads0
      have hdo' : (enterState fork message other >>= runBody fork message substate meter held) =
          .ok ended0' := by
        rw [hent']
        exact hbody'
      rw [hdo']
      exact ⟨_, rfl, rollbackOnError_agrees hagree.tracker hfa⟩
    refine ⟨callCase, ?_⟩
    intro message state other substate meter held hn hagree horigin hcand hcurrent ended h hreads
    dsimp only at h ⊢
    have hacc : account message.currentTarget :=
      hreads.account _ ((readsLe_processCreateMessage h).accountReads _ hcurrent)
    rw [processCreateMessage] at h ⊢
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    rename_i after hd
    cases h
    have rel := prepareCreation_agrees (fork := fork) hagree hacc
    rw [hp] at rel
    cases hp' : prepareCreation fork other message.currentTarget with
    | error e =>
      rw [hp'] at rel
      exact absurd rel id
    | ok prepared' =>
      rw [hp'] at rel
      have hmsg : evm.message = message :=
        (processMessage_message _).1 _ _ _ _ _ rfl ⟨evm, used⟩ hrun
      obtain ⟨⟨evm', used'⟩, hrun', hfa⟩ := callCase message prepared prepared' substate meter held
        hn rel (horigin.of_keepsCodeOrigin (keepsCodeOrigin_prepareCreation hp))
        (hcand.of_keepsCandidates (keepsCandidates_prepareCreation hp).1)
        ((readsLe_prepareCreation hp).accountReads _ hcurrent) ⟨evm, used⟩ hrun
        (.of_readsLe (readsLe_depositCode hd) hreads)
      obtain ⟨after', hd', hfa'⟩ := depositCode_agrees hagree.tracker hfa
        (by rw [hmsg]; exact hacc) hd
      refine exists_bind_ok rfl (exists_bind_ok hrun' ?_)
      dsimp only
      split
      · rename_i heq
        rw [hd'] at heq
        cases heq
      · rename_i heq
        rw [hd'] at heq
        cases heq
        exact ⟨_, rfl, hfa'⟩

end Parts

/-- A call that ends with its reads in the sets gives agreeing frames on agreeing states.

The sets must cover the block.

The first state must have read the account that the message runs at.

Its code hashes must come from the block or from writes, with no new deployment candidate. -/
theorem processMessage_agrees [LawfulGasMeter Meter] {block : BlockState}
    {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop}
    (covers : CoversBlock block account allStorage code) {message : Message fork}
    {state other : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    (hagree : AgreesOn account allStorage slot code state other)
    (horigin : CodeOrigin block state) (hcandidates : NoNewCandidate block state)
    (hcurrent : message.currentTarget ∈ state.accountReads)
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended)
    (hreads : ReadsIn account slot ended.val.state) :
    ∃ ended', processMessage fork message other substate meter held = .ok ended' ∧
      FrameAgrees account allStorage slot code ended.val ended'.val :=
  (agrees_induction covers message.gas).1 message state other substate meter held rfl hagree horigin
    hcandidates hcurrent ended h hreads

/-- A creation that ends with its reads in the sets gives agreeing frames on agreeing states.

The sets must cover the block.

The first state must have read the address of the creation.

Its code hashes must come from the block or from writes, with no new deployment candidate. -/
theorem processCreateMessage_agrees [LawfulGasMeter Meter] {block : BlockState}
    {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop}
    (covers : CoversBlock block account allStorage code) {message : Message fork}
    {state other : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    (hagree : AgreesOn account allStorage slot code state other)
    (horigin : CodeOrigin block state) (hcandidates : NoNewCandidate block state)
    (hcurrent : message.currentTarget ∈ state.accountReads)
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (hreads : ReadsIn account slot ended.val.state) :
    ∃ ended', processCreateMessage fork message other substate meter held = .ok ended' ∧
      FrameAgrees account allStorage slot code ended.val ended'.val :=
  (agrees_induction covers message.gas).2 message state other substate meter held rfl hagree horigin
    hcandidates hcurrent ended h hreads

end EthLib.Execution.Evm

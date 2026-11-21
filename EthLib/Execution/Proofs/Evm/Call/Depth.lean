module

public import EthLib.Execution.Proofs.Evm.Call.ObserveMap
public import EthLib.Execution.Proofs.Evm.Call.StepRules

/-!
# Proofs: every frame of a run has a depth of at most 1024

A call or a creation runs its message one level below its frame, and only within the limit.

So every frame that an observer sees in a run that succeeds has a depth of at most 1024.

A record that an observer keeps then needs to hold only of such frames.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {σ : Type}

/-! ## The depth of the messages that a step sends -/

omit [LawfulGasMeter Meter] in
/-- The end of a call instruction sends only a message within the depth limit. -/
private theorem depth_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : finishCall kind call callee subCall newAccount expandBy evm =
      .ok (.child caller message resume)) : message.depth ≤ STACK_DEPTH_LIMIT := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  simp only at h
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
    cases hc
  · unfold Evm.genericCall at h
    split at h
    · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
      cases hc
    · rename_i within
      cases h
      -- The child is one level below the caller frame, which the check bounds.
      simp only [callMessage]
      exact Nat.le_of_not_gt within

omit [LawfulGasMeter Meter] in
/-- A step of a call instruction sends only a message within the depth limit. -/
private theorem depth_callStep {kind : CallKind} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : callStep kind evm = .ok (.child caller message resume)) :
    message.depth ≤ STACK_DEPTH_LIMIT := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨_, hc⟩
  · obtain ⟨⟨callee, e4⟩, -, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨_, hc⟩
    · obtain ⟨⟨subCall, e5⟩, -, h⟩ := Base.bind_ok_iff.mp h
      exact depth_finishCall h
    · cases hc
  · cases hc

omit [LawfulGasMeter Meter] in
/-- A launch of a creation sends only a message within the depth limit.

The charges between its check of the depth and the message keep the message of the frame. -/
private theorem depth_launchCreate {evm caller : Evm fork Meter} {value : Base.U256}
    {initCode : ByteArray} {salt : Option Base.U256} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : launchCreate evm value initCode salt = .ok (.child caller message resume)) :
    message.depth ≤ STACK_DEPTH_LIMIT := by
  unfold Evm.launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
    cases hc
  rename_i hcheck
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with hr | ⟨_, hc⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, -, hr⟩ := Base.bind_ok_iff.mp hr
    split at hr
    · cases hr
      -- The two charges keep the message whose depth the launch checked.
      have c2 : StaticStep
          (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) e2 :=
        ((staticStep_accessAddress _ address).trans (staticStep_recordAccountRead _ address)).trans
          (.of_sameContext ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)))
      have m2 : e2.message = evm.message := c2.message
      dsimp only
      rw [m2]
      exact Nat.le_of_not_gt fun hgt => hcheck (.inr (.inr hgt))
    · obtain ⟨_, -, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
  · cases hc

omit [LawfulGasMeter Meter] in
/-- A step of CREATE or CREATE2 sends only a message within the depth limit. -/
private theorem depth_createStep {create2 : Bool} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : createStep create2 evm = .ok (.child caller message resume)) :
    message.depth ≤ STACK_DEPTH_LIMIT := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, launched⟩ := createStep_eq_ok h
  exact depth_launchCreate launched

omit [LawfulGasMeter Meter] in
/-- An instruction that may send a message sends only one within the depth limit. -/
private theorem depth_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok (.child caller message resume)) : message.depth ≤ STACK_DEPTH_LIMIT := by
  unfold Evm.messageInstruction at hrun
  rcases orElse_eq_some hrun with hc | hc
  · cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact depth_callStep h
  · cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals (try split at hc) <;> (try simp only [Option.some.injEq, reduceCtorEq] at hc) <;>
      (try subst hc)
    all_goals first
      | cases hc
      | exact depth_createStep h

omit [LawfulGasMeter Meter] in
/-- Each message that a successful step sends is within the depth limit.

So the depth check on entry to a message that a step sends never fails. -/
theorem depth_le_of_step_eq_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (h : step fork evm = .ok (.child caller message resume)) :
    message.depth ≤ STACK_DEPTH_LIMIT := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
        cases hc
      · split at h
        · exact depth_messageInstruction (by assumption) h
        · cases h
  · obtain ⟨_, -, hc⟩ := Base.map_ok_iff.mp h
    cases hc

/-! ## A run of a frame -/

/-- An observed run of a frame within the depth limit keeps an invariant of the record.

Each message that the frame runs must keep the invariant when it is within the limit. -/
private theorem runFrameWith_inv (inv : σ → Prop)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s →
      inv (f evm result s))
    {bound : Nat} {runChild : MessageRunnerIn (StateT σ (Except EvmError)) fork Meter bound}
    (children : ∀ caller (message : Message fork) lt s r,
      message.depth ≤ STACK_DEPTH_LIMIT → inv s → runChild caller message lt s = .ok r →
        inv r.2)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound)
    (depth : evm.message.depth ≤ STACK_DEPTH_LIMIT) {s : σ} (start : inv s)
    {r : { after : Evm fork Meter // GasMeter.gasHeld after.gas ≤ bound } × σ}
    (run : runFrameWith (fun evm result => modify (f evm result)) (step fork)
      (step_decreases fork) bound runChild evm within s = .ok r) :
    inv r.2 := by
  induction h : measure evm using Nat.strongRecOn generalizing evm s r with
  | _ n ih =>
  subst h
  generalize hm : runFrameWith (fun evm result => modify (f evm result)) (step fork)
    (step_decreases fork) bound runChild evm within = m at run
  rw [runFrameWith] at hm
  by_cases running : evm.running
  · simp only [running, dite_true] at hm
    split at hm <;> rename_i hs <;> subst hm
    · rename_i e
      by_cases aborts : e.aborts <;>
        simp [aborts, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, modify,
          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe,
          MonadExceptOf.throw, StateT.lift] at run
      subst run
      exact keeps _ _ _ depth start
    · rename_i after
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure] at run
      -- The next frame keeps the message, so its depth.
      have kept : after.message = evm.message := (stepRules_messageCode.step hs).1
      exact ih _ (step_decreases fork running hs) _ _ (kept ▸ depth) (keeps _ _ _ depth start)
        run rfl
    · rename_i caller message resume
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure] at run
      generalize Nat.lt_of_lt_of_le (step_decreases fork running hs).1 within = lt at run
      have mid := keeps evm (.ok (.child caller message resume)) s depth start
      cases hr : runChild caller message lt (f evm (.ok (.child caller message resume)) s)
      all_goals rw [hr] at run
      · cases run
      rename_i a
      obtain ⟨⟨child, used⟩, s'⟩ := a
      have back : inv s' := children _ _ _ _ _ (depth_le_of_step_eq_child hs) mid hr
      dsimp only at run
      cases hres : resume child with
      | error e =>
        rw [runFrameWith_match_error hres] at run
        by_cases aborts : e.aborts <;>
          simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
            StateT.lift, Except.pure, bind, Except.bind] at run
        subst run
        exact back
      | ok after =>
        rw [runFrameWith_match_ok hres] at run
        -- The caller resumes with its own message, which is the message of the frame.
        have kept : after.message = evm.message := by
          rw [(sameContext_of_step_eq_child hs hres).message, message_incorporateChild]
          exact (stepRules_messageCode.step hs).1.1
        exact ih _ ((step_decreases fork running hs).2 child _ used hres) _ _ (kept ▸ depth)
          back run rfl
  · simp only [running] at hm
    subst hm
    cases run
    exact start

/-! ## A run of a message and of a creation -/

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- A run of a precompile, whose two branches return at once, keeps the state of the record. -/
private theorem precompile_match_state {α : Type} {x : Option (Evm fork Meter)}
    {g : (after : Evm fork Meter) → x = some after → α} {b : x = none → α} {s : σ} {r : α × σ}
    (h : processMessageWith.match_1 fork (fun _ => StateT σ (Except EvmError) α) x
      (fun after h => StateT.pure (g after h)) (fun h => StateT.pure (b h)) s = .ok r) :
    r.2 = s := by
  cases x <;> cases h <;> rfl

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- A deposit of code, which fails or returns at once, keeps the state of the record. -/
private theorem deposit_match_state {α : Type} {x : Except EvmError (Evm fork Meter)}
    {g : (after : Evm fork Meter) → x = .ok after → α} {s : σ} {r : α × σ}
    (h : processCreateMessageWith.match_1 fork (fun _ => StateT σ (Except EvmError) α) x
      (fun e _ => throw e) (fun after h => StateT.pure (g after h)) s = .ok r) :
    r.2 = s := by
  cases x <;> cases h <;> rfl

/-- An observed run of a message or a creation within the depth limit keeps an invariant.

The message has gas `n`, the measure of the induction. -/
private theorem process_inv (inv : σ → Prop)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s →
      inv (f evm result s)) (n : Nat) :
    ∀ message : Message fork, message.gas = n → message.depth ≤ STACK_DEPTH_LIMIT →
      (∀ state substate (meter : Meter) held s r, inv s →
        processMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (f evm result)) message state substate meter held s =
            .ok r → inv r.2) ∧
      (∀ state substate (meter : Meter) held s r, inv s →
        processCreateMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (f evm result)) message state substate meter held s =
            .ok r → inv r.2) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro message gas within
  have call : ∀ state substate (meter : Meter) held s r, inv s →
      processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (f evm result)) message state substate meter held s =
          .ok r → inv r.2 := by
    intro state substate meter held s r start run
    rw [processMessageWith] at run
    obtain ⟨r', run, hr⟩ := Base.stateT_map_eq_ok run
    rw [hr]
    dsimp only at run
    split at run
    case' isTrue =>
      cases hmv : (startState fork message state).moveEther fork message.caller
        message.currentTarget message.value
      case' error =>
        simp [hmv, liftExcept, Except.mapError, bind, StateT.bind, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, Except.bind] at run
      simp only [hmv, liftExcept, Except.mapError, pure, bind, StateT.bind,
        StateT.pure, Except.bind, Except.pure] at run
    case' isFalse =>
      simp only [pure, bind, StateT.bind, StateT.pure, Except.bind, Except.pure] at run
    -- Either way, the precompile runs no observer, and a frame of code runs the observed loop.
    all_goals
      rcases hp : precompileAddress fork message with _ | address
      · simp only [hp] at run
        refine runFrameWith_inv inv f keeps (fun caller child lt s' r'' depth st h => ?_) _ held
          within start run
        have lt' : child.gas < n := gas ▸ lt
        cases ht : child.target <;> simp only [ht] at h
        · exact (ih _ lt' child rfl depth).2 _ _ _ _ _ _ st h
        · exact (ih _ lt' child rfl depth).1 _ _ _ _ _ _ st h
      · simp only [hp] at run
        by_cases hd : message.disablePrecompiles = true
        · rw [ite_eq_left hd] at run
          cases run
          exact start
        · rw [ite_eq_right hd] at run
          rw [precompile_match_state run]
          exact start
  refine ⟨call, ?_⟩
  intro state substate meter held s r start run
  rw [processCreateMessageWith] at run
  cases hpc : prepareCreation fork state message.currentTarget
  · simp [hpc, liftExcept, bind, StateT.bind, throw, throwThe, MonadExceptOf.throw,
      StateT.lift, Except.bind] at run
  rename_i prepared
  simp only [hpc, liftExcept, pure, bind, StateT.bind, StateT.pure, Except.bind,
    Except.pure] at run
  cases hpm : processMessageWith (M := StateT σ (Except EvmError)) fork
    (fun evm result => modify (f evm result)) message prepared substate meter held s
  · rw [hpm] at run
    cases run
  rename_i ended
  obtain ⟨⟨evm, used⟩, s'⟩ := ended
  rw [hpm] at run
  have back : inv s' := call _ _ _ _ _ _ start hpm
  dsimp only at run
  rw [deposit_match_state run]
  exact back

/-- From a message within the depth limit, a run that succeeds keeps an invariant of its record.

The record needs to keep the invariant only at frames within the limit.

So no step that the observer sees is on a frame deeper than the limit. -/
theorem processMessageWith_inv_of_depth_le (inv : σ → Prop)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s →
      inv (f evm result s))
    {message : Message fork} (within : message.depth ≤ STACK_DEPTH_LIMIT)
    (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) {s : σ} (start : inv s)
    {r : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } × σ}
    (run : processMessageWith (M := StateT σ (Except EvmError)) fork
      (fun evm result => modify (f evm result)) message state substate meter held s = .ok r) :
    inv r.2 :=
  (process_inv inv f keeps _ message rfl within).1 state substate meter held s r start run

/-- From a creation within the depth limit, a run that succeeds keeps an invariant of its record.

The record needs to keep the invariant only at frames within the limit. -/
theorem processCreateMessageWith_inv_of_depth_le (inv : σ → Prop)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s →
      inv (f evm result s))
    {message : Message fork} (within : message.depth ≤ STACK_DEPTH_LIMIT)
    (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) {s : σ} (start : inv s)
    {r : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas } × σ}
    (run : processCreateMessageWith (M := StateT σ (Except EvmError)) fork
      (fun evm result => modify (f evm result)) message state substate meter held s = .ok r) :
    inv r.2 :=
  (process_inv inv f keeps _ message rfl within).2 state substate meter held s r start run

end EthLib.Execution.Evm

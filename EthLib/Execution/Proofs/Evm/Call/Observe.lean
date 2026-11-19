module

public import EthLib.Execution.Proofs.Evm.Call.MessageCall

/-!
# Proofs: the observed run

An observer that only records each step in a state leaves the run as it is.

Once that state is dropped, the observed run of a frame is the run with no observer.

The same holds of a message and of a creation.

So what the observer records is a view of the run, not a change to it.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {σ : Type}

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- The match on a resumed frame takes its error branch on an error. -/
private theorem resume_match_error {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {e : EvmError} (h : x = .error e) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    runFrameWith.match_1 (fun _ => β) x h_1 h_2 = h_1 e h :=
  eq_of_heq (runFrameWith.match_1.congr_eq_1 _ _ _ _ e h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- The match on a resumed frame takes its success branch on a frame. -/
private theorem resume_match_ok {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {after : Evm fork Meter} (h : x = .ok after) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    runFrameWith.match_1 (fun _ => β) x h_1 h_2 = h_2 after h :=
  eq_of_heq (runFrameWith.match_1.congr_eq_2 _ _ _ _ after h)

/-- An observed run of a frame, with its state dropped, is the run with no observer.

The observer only changes a state at each step.

Each observed run of a message, with its state dropped, must be the run of the plain runner. -/
theorem runFrameWith_modify
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm}
    {bound : Nat}
    {runChild : MessageRunnerIn (StateT σ (Except EvmError)) fork Meter bound}
    {runChild' : MessageRunner fork Meter bound}
    (children : ∀ caller message lt s,
      Prod.fst <$> runChild caller message lt s = runChild' caller message lt)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) (s : σ) :
    Prod.fst <$> runFrameWith (fun evm result => modify (record evm result)) step decreases
        bound runChild evm within s =
      runFrameWith (fun _ _ => pure ()) step decreases bound runChild' evm within := by
  induction h : measure evm using Nat.strongRecOn generalizing evm s with
  | _ n ih =>
  subst h
  generalize hm : runFrameWith (fun evm result => modify (record evm result)) step decreases
    bound runChild evm within = m
  rw [runFrameWith] at hm
  rw [runFrameWith]
  by_cases running : evm.running
  · simp only [running, dite_true] at hm ⊢
    split at hm <;> rename_i hs <;> subst hm
    · rename_i e
      by_cases aborts : e.aborts <;>
        simp [aborts, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, modify,
          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, Functor.map, Except.map]
    · simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure]
      exact ih _ (decreases running hs) _ _ _ rfl
    · rename_i caller message resume
      have run := children caller message
        (Nat.lt_of_lt_of_le (decreases running hs).1 within)
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure]
      generalize Nat.lt_of_lt_of_le (decreases running hs).1 within = lt at run ⊢
      cases hr : runChild caller message lt (record evm (.ok (.child caller message resume)) s)
      all_goals have run := run (record evm (.ok (.child caller message resume)) s)
      all_goals rw [hr] at run
      · rw [← run]
        rfl
      · rename_i a
        obtain ⟨⟨child, used⟩, s'⟩ := a
        simp only [Functor.map, Except.map] at run
        rw [← run]
        dsimp only [Functor.map]
        split <;> rename_i hres
        · rw [resume_match_error hres]
          rename_i e
          by_cases aborts : e.aborts <;>
            simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
              StateT.lift, Except.map, bind, Except.bind, Except.pure]
        · rw [resume_match_ok hres]
          exact ih _ ((decreases running hs).2 child _ used hres) _ _ _ rfl
  · simp only [running] at hm ⊢
    subst hm
    rfl

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- The match on a precompile run takes its first branch on a frame. -/
private theorem precompile_match_some {β : Sort _} {x : Option (Evm fork Meter)}
    {after : Evm fork Meter} (h : x = some after)
    (h_1 : (after : Evm fork Meter) → x = some after → β) (h_2 : x = none → β) :
    processMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_1 after h :=
  eq_of_heq (processMessageWith.match_1.congr_eq_1 _ _ _ _ _ after h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- The match on a precompile run takes its second branch on nothing. -/
private theorem precompile_match_none {β : Sort _} {x : Option (Evm fork Meter)}
    (h : x = none) (h_1 : (after : Evm fork Meter) → x = some after → β) (h_2 : x = none → β) :
    processMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_2 h :=
  eq_of_heq (processMessageWith.match_1.congr_eq_2 _ _ _ _ _ h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- The match on a deposit of code takes its error branch on an error. -/
private theorem deposit_match_error {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {e : EvmError} (h : x = .error e) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    processCreateMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_1 e h :=
  eq_of_heq (processCreateMessageWith.match_1.congr_eq_1 _ _ _ _ _ e h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- The match on a deposit of code takes its success branch on a frame. -/
private theorem deposit_match_ok {β : Sort _} {x : Except EvmError (Evm fork Meter)}
    {after : Evm fork Meter} (h : x = .ok after) (h_1 : (e : EvmError) → x = .error e → β)
    (h_2 : (after : Evm fork Meter) → x = .ok after → β) :
    processCreateMessageWith.match_1 fork (fun _ => β) x h_1 h_2 = h_2 after h :=
  eq_of_heq (processCreateMessageWith.match_1.congr_eq_2 _ _ _ _ _ after h)

omit [GasMeter Meter] [LawfulGasMeter Meter] in
/-- Dropping the state commutes with a map. -/
private theorem fst_map {α β : Type} (f : α → β) (x : StateT σ (Except EvmError) α) (s : σ) :
    Prod.fst <$> (f <$> x) s = f <$> (Prod.fst <$> x s) := by
  simp only [Functor.map, StateT.map, Except.map]
  cases x s <;> rfl

/-- An observed run of a frame, with its state and its gas bound dropped, is the plain run.

The observer only changes a state at each step.

Each observed run of a message, with its state dropped, must be the run of the plain runner. -/
theorem runFrame_modify
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm}
    {bound : Nat}
    {runChild : MessageRunnerIn (StateT σ (Except EvmError)) fork Meter bound}
    {runChild' : MessageRunner fork Meter bound}
    (children : ∀ caller message lt s,
      Prod.fst <$> runChild caller message lt s = runChild' caller message lt)
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) (s : σ) :
    (fun p => p.1.val) <$> runFrameWith (fun evm result => modify (record evm result)) step
        decreases bound runChild evm within s =
      runFrame step decreases bound runChild' evm within := by
  rw [runFrame, ← runFrameWith_modify record children evm within s]
  cases runFrameWith (fun evm result => modify (record evm result)) step decreases bound
    runChild evm within s <;> rfl

/-- An observed run of a message or a creation, with its state dropped, is the plain run.

The message has gas `n`, the measure of the induction. -/
private theorem process_modify
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ) (n : Nat) :
    ∀ message : Message fork, message.gas = n →
      (∀ state substate (meter : Meter) held s,
        Prod.fst <$> processMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (record evm result)) message state substate meter held s =
        processMessage fork message state substate meter held) ∧
      (∀ state substate (meter : Meter) held s,
        Prod.fst <$> processCreateMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (record evm result)) message state substate meter held s =
        processCreateMessage fork message state substate meter held) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro message gas
  have call : ∀ state substate (meter : Meter) held s,
      Prod.fst <$> processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (record evm result)) message state substate meter held s =
      processMessage fork message state substate meter held := by
    intro state substate meter held s
    rw [processMessageWith, processMessage, processMessageWith, fst_map]
    congr 1
    split <;> rename_i ht
    rotate_left
    simp only [ht, ite_false, pure, bind, StateT.bind, StateT.pure, Except.bind, Except.pure]
    rotate_left
    have ht' := eq_true ht
    cases hmv : (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value
    · simp only [ht', hmv, ite_true, liftExcept, Except.mapError, bind, StateT.bind,
        Function.comp, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind]
      rfl
    simp only [ht', hmv, ite_true, liftExcept, Except.mapError, pure, bind, StateT.bind,
      StateT.pure, Except.bind, Except.pure]
    all_goals
      split <;> rename_i hp <;> rw [hp]
      · dsimp only
        by_cases hd : message.disablePrecompiles = true
        · rw [ite_eq_left hd, ite_eq_left hd]
          rfl
        · rw [ite_eq_right hd, ite_eq_right hd]
          split <;> rename_i hr
          · rw [precompile_match_some hr]
            rfl
          · rw [precompile_match_none hr]
            rfl
      · refine runFrameWith_modify record (fun caller child lt s' => ?_) _ _ _
        have lt' : child.gas < n := gas ▸ lt
        cases child.target <;> dsimp only
        · exact (ih _ lt' child rfl).2 _ _ _ _ _
        · exact (ih _ lt' child rfl).1 _ _ _ _ _
  refine ⟨call, ?_⟩
  intro state substate meter held s
  rw [processCreateMessageWith, processCreateMessage, processCreateMessageWith]
  cases hpc : prepareCreation fork state message.currentTarget
  · simp only [liftExcept, bind, StateT.bind, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind]
    rfl
  rename_i prepared
  have run := call prepared substate meter held s
  simp only [liftExcept, pure, bind, StateT.bind, StateT.pure, Except.bind, Except.pure]
  cases hpm : processMessageWith (M := StateT σ (Except EvmError)) fork
    (fun evm result => modify (record evm result)) message prepared substate meter held s
  all_goals
    rw [hpm] at run
    simp only [processMessage, pure, Except.pure, Functor.map, Except.map] at run
    rw [← run]
  · rfl
  rename_i ended
  obtain ⟨⟨evm, used⟩, s'⟩ := ended
  dsimp only
  split <;> rename_i hd
  · rw [deposit_match_error hd]
    rfl
  · rw [deposit_match_ok hd]
    rfl

/-- An observed run of a message, with its state dropped, is the run with no observer.

The observer only changes a state at each step. -/
theorem processMessageWith_modify
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) (s : σ) :
    Prod.fst <$> processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (record evm result)) message state substate meter held s =
      processMessage fork message state substate meter held :=
  (process_modify record _ message rfl).1 state substate meter held s

/-- An observed run of a creation, with its state dropped, is the run with no observer.

The observer only changes a state at each step. -/
theorem processCreateMessageWith_modify
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) (s : σ) :
    Prod.fst <$> processCreateMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (record evm result)) message state substate meter held s =
      processCreateMessage fork message state substate meter held :=
  (process_modify record _ message rfl).2 state substate meter held s

end EthLib.Execution.Evm

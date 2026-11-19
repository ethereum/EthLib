module

public import EthLib.Execution.Proofs.Evm.Call.Observe

/-!
# Proofs: observed runs related by a map of their states

Two observers that record each step in a state can be related by a map of the states.

When the map sends each record of the first to the record of the second, so do the runs.

Each observed run of the first, with its state mapped, is the observed run of the second.

The same holds of a message and of a creation.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {σ τ : Type}

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

/-- An observed run of a frame, with its state mapped, is the run of the observer it maps to.

The map must send each record of the first observer to the record of the second.

Each observed run of a message, with its state mapped, must be that of the second runner. -/
theorem runFrameWith_map (h : σ → τ)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (g : Evm fork Meter → Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ evm result s, h (f evm result s) = g evm result (h s))
    {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
      result.Decreases evm}
    {bound : Nat}
    {runChild : MessageRunnerIn (StateT σ (Except EvmError)) fork Meter bound}
    {runChild' : MessageRunnerIn (StateT τ (Except EvmError)) fork Meter bound}
    (children : ∀ caller message lt s,
      Prod.map id h <$> runChild caller message lt s = runChild' caller message lt (h s))
    (evm : Evm fork Meter) (within : GasMeter.gasHeld evm.gas ≤ bound) (s : σ) :
    Prod.map id h <$> runFrameWith (fun evm result => modify (f evm result)) step decreases
        bound runChild evm within s =
      runFrameWith (fun evm result => modify (g evm result)) step decreases bound runChild'
        evm within (h s) := by
  induction hm : measure evm using Nat.strongRecOn generalizing evm s with
  | _ n ih =>
  subst hm
  generalize hl : runFrameWith (fun evm result => modify (f evm result)) step decreases
    bound runChild evm within = l
  generalize hr : runFrameWith (fun evm result => modify (g evm result)) step decreases
    bound runChild' evm within = r
  rw [runFrameWith] at hl hr
  by_cases running : evm.running
  · simp only [running, dite_true] at hl hr
    split at hl <;> rename_i hs <;> subst hl <;> split at hr <;> rename_i hs' <;>
      rw [hs] at hs' <;> cases hs' <;> subst hr
    · rename_i e
      by_cases aborts : e.aborts <;>
        simp [aborts, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, modify,
          modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe,
          MonadExceptOf.throw, StateT.lift, Functor.map, Except.map, hfg]
    · simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure]
      rw [← hfg]
      exact ih _ (decreases running hs) _ _ _ rfl
    · rename_i caller message resume
      have run := children caller message
        (Nat.lt_of_lt_of_le (decreases running hs).1 within)
      simp only [bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.bind, Except.pure]
      rw [← hfg]
      generalize Nat.lt_of_lt_of_le (decreases running hs).1 within = lt at run ⊢
      have run := run (f evm (.ok (.child caller message resume)) s)
      rw [← run]
      cases hc : runChild caller message lt (f evm (.ok (.child caller message resume)) s)
      · rfl
      · rename_i a
        obtain ⟨⟨child, used⟩, s'⟩ := a
        dsimp only [Functor.map, Except.map, Prod.map, id]
        obtain ⟨e, hres⟩ | ⟨after, hres⟩ :
            (∃ e, resume child = .error e) ∨ ∃ after, resume child = .ok after := by
          cases resume child <;> simp
        · rw [resume_match_error hres, resume_match_error hres]
          by_cases aborts : e.aborts <;>
            simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw,
              StateT.lift, bind, Except.bind, Except.pure]
        · rw [resume_match_ok hres, resume_match_ok hres]
          exact ih _ ((decreases running hs).2 child _ used hres) _ _ _ rfl
  · simp only [running] at hl hr
    subst hl hr
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
/-- A map of the state passes through the match on a precompile run whose branches are pure. -/
private theorem precompile_map {α : Type} (h : σ → τ) (x : Option (Evm fork Meter))
    (k : (after : Evm fork Meter) → x = some after → α) (d : α) (s : σ) :
    Prod.map id h <$> processMessageWith.match_1 fork (fun _ => StateT σ (Except EvmError) α) x
        (fun after hx => StateT.pure (k after hx)) (fun _ => StateT.pure d) s =
      processMessageWith.match_1 fork (fun _ => StateT τ (Except EvmError) α) x
        (fun after hx => StateT.pure (k after hx)) (fun _ => StateT.pure d) (h s) := by
  cases x <;> rfl

/-- Mapping the state commutes with a map of the result. -/
private theorem map_map_of {α β : Type} (h : σ → τ) (k : α → β)
    (x : StateT σ (Except EvmError) α) (y : StateT τ (Except EvmError) α) (s : σ)
    (hxy : Prod.map id h <$> x s = y (h s)) :
    Prod.map id h <$> (k <$> x) s = (k <$> y) (h s) := by
  simp only [Functor.map, StateT.map, Except.map] at hxy ⊢
  rw [← hxy]
  cases x s <;> rfl

/-- An observed run of a message or a creation, with its state mapped, is the mapped run.

The message has gas `n`, the measure of the induction. -/
private theorem process_map (h : σ → τ)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (g : Evm fork Meter → Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ evm result s, h (f evm result s) = g evm result (h s)) (n : Nat) :
    ∀ message : Message fork, message.gas = n →
      (∀ state substate (meter : Meter) held s,
        Prod.map id h <$> processMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (f evm result)) message state substate meter held s =
        processMessageWith (M := StateT τ (Except EvmError)) fork
          (fun evm result => modify (g evm result)) message state substate meter held (h s)) ∧
      (∀ state substate (meter : Meter) held s,
        Prod.map id h <$> processCreateMessageWith (M := StateT σ (Except EvmError)) fork
          (fun evm result => modify (f evm result)) message state substate meter held s =
        processCreateMessageWith (M := StateT τ (Except EvmError)) fork
          (fun evm result => modify (g evm result)) message state substate meter held
          (h s)) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro message gas
  have call : ∀ state substate (meter : Meter) held s,
      Prod.map id h <$> processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (f evm result)) message state substate meter held s =
      processMessageWith (M := StateT τ (Except EvmError)) fork
        (fun evm result => modify (g evm result)) message state substate meter held (h s) := by
    intro state substate meter held s
    rw [processMessageWith, processMessageWith]
    refine map_map_of h _ _ _ _ ?_
    split <;> rename_i ht
    rotate_left
    simp only [ht, ite_false, pure, bind, StateT.bind, StateT.pure, Except.bind, Except.pure]
    rotate_left
    have ht' := eq_true ht
    cases hmv : (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value
    · simp only [liftExcept, Except.mapError, bind, StateT.bind, Function.comp, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, Except.bind]
      rfl
    simp only [ht', ite_true, liftExcept, Except.mapError, pure, bind, StateT.bind,
      StateT.pure, Except.bind, Except.pure]
    all_goals
      obtain hp | ⟨address, hp⟩ : precompileAddress fork message = none ∨
          ∃ address, precompileAddress fork message = some address := by
        cases precompileAddress fork message <;> simp
      rotate_left
      · rw [hp]
        dsimp only
        by_cases hd : message.disablePrecompiles = true
        · rw [ite_eq_left hd, ite_eq_left hd]
          rfl
        · rw [ite_eq_right hd, ite_eq_right hd]
          exact precompile_map h _ _ _ _
      · rw [hp]
        refine runFrameWith_map h f g hfg (fun caller child lt s' => ?_) _ _ _
        have lt' : child.gas < n := gas ▸ lt
        cases child.target <;> dsimp only
        · exact (ih _ lt' child rfl).2 _ _ _ _ _
        · exact (ih _ lt' child rfl).1 _ _ _ _ _
  refine ⟨call, ?_⟩
  intro state substate meter held s
  rw [processCreateMessageWith, processCreateMessageWith]
  cases hpc : prepareCreation fork state message.currentTarget
  · simp only [liftExcept, bind, StateT.bind, Function.comp, throw, throwThe,
      MonadExceptOf.throw, StateT.lift, Except.bind]
    rfl
  rename_i prepared
  have run := call prepared substate meter held s
  simp only [liftExcept, pure, bind, StateT.bind, StateT.pure, Except.bind, Except.pure]
  rw [← run]
  cases hpm : processMessageWith (M := StateT σ (Except EvmError)) fork
    (fun evm result => modify (f evm result)) message prepared substate meter held s
  · rfl
  rename_i ended
  obtain ⟨⟨evm, used⟩, s'⟩ := ended
  dsimp only [Functor.map, Except.map, Prod.map, id]
  obtain ⟨e, hd⟩ | ⟨after, hd⟩ : (∃ e, depositCode fork state evm = .error e) ∨
      ∃ after, depositCode fork state evm = .ok after := by
    cases depositCode fork state evm <;> simp
  · rw [deposit_match_error hd, deposit_match_error hd]
    rfl
  · rw [deposit_match_ok hd, deposit_match_ok hd]
    rfl

/-- An observed run of a message, with its state mapped, is the run of the observer it maps to.

The map must send each record of the first observer to the record of the second. -/
theorem processMessageWith_map (h : σ → τ)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (g : Evm fork Meter → Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ evm result s, h (f evm result s) = g evm result (h s))
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) (s : σ) :
    Prod.map id h <$> processMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (f evm result)) message state substate meter held s =
      processMessageWith (M := StateT τ (Except EvmError)) fork
        (fun evm result => modify (g evm result)) message state substate meter held (h s) :=
  (process_map h f g hfg _ message rfl).1 state substate meter held s

/-- An observed run of a creation, with its state mapped, is the run of the observer it maps to.

The map must send each record of the first observer to the record of the second. -/
theorem processCreateMessageWith_map (h : σ → τ)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (g : Evm fork Meter → Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ evm result s, h (f evm result s) = g evm result (h s))
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
    (held : GasMeter.gasHeld meter ≤ message.gas) (s : σ) :
    Prod.map id h <$> processCreateMessageWith (M := StateT σ (Except EvmError)) fork
        (fun evm result => modify (f evm result)) message state substate meter held s =
      processCreateMessageWith (M := StateT τ (Except EvmError)) fork
        (fun evm result => modify (g evm result)) message state substate meter held (h s) :=
  (process_map h f g hfg _ message rfl).2 state substate meter held s

end EthLib.Execution.Evm

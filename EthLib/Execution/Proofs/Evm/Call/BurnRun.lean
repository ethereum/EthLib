module

public import EthLib.Execution.Proofs.Evm.Call.Burn

/-!
# Proofs: the log of burns of a run of a frame, a call or a creation

A certificate of a run gives its log of burns, and follows the interpreter.

Each rule of a frame takes one step of the interpreter from a running frame, or stops the run.

A step that gives the next frame adds the log of the step.

A step that sends a message adds the log of the run of that message, once the caller resumes.

A step that halts with an error adds nothing.

A message runs its code, or a precompile, from the state that it enters.

A call that ends with an error rolls back, and so does a creation that fails to deposit its code.

Their logs then count for nothing.

The supply at the end plus the total of the log is the supply at the start.

A run from a given start has one end, so every certificate from that start has the same total.

Each burn that a log counts comes from a step of SELFDESTRUCT that the run takes, with its burn.

From Glamsterdam, no step burns, so the total is 0.

Every successful call and creation has a certificate.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Where a certified run starts.

It starts from a frame, or from the frame of a message that may run a precompile.

It may also start from a call or a creation. -/
inductive BurnStart (fork : Fork) (Meter : Type) where
  | frame (evm : Evm fork Meter)
  | body (evm : Evm fork Meter)
  | call (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
  | create (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)

/-- The state at the start of the run. -/
def BurnStart.state : BurnStart fork Meter → TransactionState
  | .frame evm | .body evm => evm.state
  | .call _ state _ _ | .create _ state _ _ => state

/-- The start of a message that a caller sends: a call when it has a target, else a creation.

It starts from the state of the caller, a child of its substate and a new meter. -/
def BurnStart.child (caller : Evm fork Meter) (message : Message fork) : BurnStart fork Meter :=
  match message.target with
  | some _ => .call message caller.state caller.substate.child
      (GasMeter.start message.gas message.reservoir)
  | none => .create message caller.state caller.substate.child
      (GasMeter.start message.gas message.reservoir)

/-- A message starts with the state of the caller that sends it. -/
theorem BurnStart.state_child (caller : Evm fork Meter) (message : Message fork) :
    (BurnStart.child caller message).state = caller.state := by
  unfold BurnStart.child
  split <;> rfl

/-- A certificate that a run from `start` ends in a frame, with a log of its burns.

A frame that is not running ends the run.

A running frame takes a step, and halts when the step fails with an error that does not abort.

A step that gives the next frame adds its log, and the run goes on from that frame.

A step that sends a message adds the log of the run of the message, and the caller resumes.

A resume that fails with an error that does not abort halts the frame, and rolls back that log.

A message that selects no precompile runs its frame.

A precompile runs unless the message disables precompiles, and the frame stops when none runs.

A call starts from the state it enters, and rolls back when it ends with an error.

A creation prepares its account, runs as a call, and deposits its code.

A creation whose deposit rolls back the state counts nothing of its log.

When that rollback leaves the state as it was, the rule that keeps the log applies too.

That log then has a total of 0, as the supply is unchanged. -/
inductive RunBurns (fork : Fork) (Meter : Type) [GasMeter Meter] :
    BurnStart fork Meter → Evm fork Meter → BurnLog → Prop
  | stopped (evm : Evm fork Meter) (h : evm.running = false) :
      RunBurns fork Meter (.frame evm) evm .empty
  | halt {evm : Evm fork Meter} {error : EvmError} (running : evm.running = true)
      (h : step fork evm = .error error) (notAborts : error.aborts = false) :
      RunBurns fork Meter (.frame evm) (exceptionalHalt evm error) .empty
  | next {evm after ended : Evm fork Meter} {rest : BurnLog} (running : evm.running = true)
      (h : step fork evm = .ok (.next after))
      (tail : RunBurns fork Meter (.frame after) ended rest) :
      RunBurns fork Meter (.frame evm) ended (.append (stepBurnLog evm after) rest)
  | child {evm caller child after ended : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} {middle rest : BurnLog}
      (running : evm.running = true) (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child middle)
      (resumed : resume child = .ok after)
      (tail : RunBurns fork Meter (.frame after) ended rest) :
      RunBurns fork Meter (.frame evm) ended (.append middle rest)
  | failedResume {evm caller child : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} {middle : BurnLog}
      {error : EvmError}
      (running : evm.running = true) (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child middle)
      (resumed : resume child = .error error) (notAborts : error.aborts = false) :
      RunBurns fork Meter (.frame evm) (exceptionalHalt evm error) (.rollback middle)
  | bodyFrame {evm ended : Evm fork Meter} {log : BurnLog}
      (selected : precompileAddress fork evm.message = none)
      (run : RunBurns fork Meter (.frame evm) ended log) :
      RunBurns fork Meter (.body evm) ended log
  | skipPrecompile (evm : Evm fork Meter) (address : Nat)
      (selected : precompileAddress fork evm.message = some address)
      (skipped : evm.message.disablePrecompiles = true ∨ runPrecompile fork address evm = none) :
      RunBurns fork Meter (.body evm) { evm with running := false } .empty
  | precompile {address : Nat} {evm after : Evm fork Meter}
      (selected : precompileAddress fork evm.message = some address)
      (enabled : evm.message.disablePrecompiles = false)
      (h : runPrecompile fork address evm = some after) :
      RunBurns fork Meter (.body evm) after .empty
  | call {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter} {log : BurnLog}
      (entered : Entered fork message state substate entry entrySubstate)
      (run : RunBurns fork Meter (.body (startFrame message entry entrySubstate meter)) ended log)
      (parent : ended.state.parent = state.parent) :
      RunBurns fork Meter (.call message state substate meter) (rollbackOnError state ended)
        (if ended.error.isSome then .rollback log else log)
  | createRollback {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter} {log : BurnLog}
      (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
      (run : RunBurns fork Meter (.call message prepared substate meter) evm log)
      (deposit : depositCode fork state evm = .ok after)
      (rolled : after.state = evm.state.restoreTxState state)
      (parent : evm.state.parent = state.parent) :
      RunBurns fork Meter (.create message state substate meter) after (.rollback log)
  | createKeep {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter} {log : BurnLog}
      (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
      (run : RunBurns fork Meter (.call message prepared substate meter) evm log)
      (deposit : depositCode fork state evm = .ok after)
      (kept : after.state = evm.state ∨
        evm.state.setCode fork evm.message.currentTarget evm.output = .ok after.state) :
      RunBurns fork Meter (.create message state substate meter) after log

/-- The frames that a run from `start` reaches, by the same steps as a certificate.

A run of a frame reaches that frame.

It reaches what the next frame of a running step reaches.

A step that sends a message reaches what the run of that message reaches.

When a certified run of the message ends and the caller resumes, it reaches what that frame does.

A message that selects no precompile reaches what its frame reaches.

A call reaches what the frame of the state it enters reaches.

A creation reaches what the call of its init code reaches, after the account is prepared. -/
inductive RunReaches (fork : Fork) (Meter : Type) [GasMeter Meter] :
    BurnStart fork Meter → Evm fork Meter → Prop
  | here (evm : Evm fork Meter) : RunReaches fork Meter (.frame evm) evm
  | next {evm after reached : Evm fork Meter} (running : evm.running = true)
      (h : step fork evm = .ok (.next after))
      (tail : RunReaches fork Meter (.frame after) reached) :
      RunReaches fork Meter (.frame evm) reached
  | childRun {evm caller reached : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} (running : evm.running = true)
      (h : step fork evm = .ok (.child caller message resume))
      (run : RunReaches fork Meter (BurnStart.child caller message) reached) :
      RunReaches fork Meter (.frame evm) reached
  | childTail {evm caller child after reached : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} {middle : BurnLog}
      (running : evm.running = true) (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child middle)
      (resumed : resume child = .ok after) (tail : RunReaches fork Meter (.frame after) reached) :
      RunReaches fork Meter (.frame evm) reached
  | body {evm reached : Evm fork Meter} (selected : precompileAddress fork evm.message = none)
      (run : RunReaches fork Meter (.frame evm) reached) :
      RunReaches fork Meter (.body evm) reached
  | call {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {reached : Evm fork Meter}
      (entered : Entered fork message state substate entry entrySubstate)
      (run : RunReaches fork Meter (.body (startFrame message entry entrySubstate meter)) reached) :
      RunReaches fork Meter (.call message state substate meter) reached
  | create {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {reached : Evm fork Meter}
      (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
      (run : RunReaches fork Meter (.call message prepared substate meter) reached) :
      RunReaches fork Meter (.create message state substate meter) reached

/-- A certified run ends with the supply of its start, less the total of its log. -/
theorem RunBurns.supply {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    (h : RunBurns fork Meter start ended log) :
    ended.state.supply + log.total = start.state.supply := by
  induction h with
  | stopped => rfl
  | halt => rfl
  | next _ step _ ih =>
    have := supply_of_step_eq_next step
    simp only [BurnLog.total, BurnStart.state] at *
    omega
  | child _ step _ resumed _ ihChild ihTail =>
    have hw := supply_of_step_eq_child step
    have hc := sameContext_of_step_eq_child step resumed
    simp only [BurnStart.state] at ihTail
    rw [hc.state, state_incorporateChild] at ihTail
    rw [BurnStart.state_child] at ihChild
    simp only [BurnLog.total, BurnStart.state] at *
    omega
  | failedResume => rfl
  | bodyFrame _ _ ih => exact ih
  | skipPrecompile => rfl
  | precompile _ _ h =>
    exact TransactionState.supply_eq_of_sameOutside (staticStep_runPrecompile h).state
  | @call message state entry substate entrySubstate meter ended log entered _ hp ih =>
    have entrySupply := supply_entered entered
    unfold rollbackOnError
    split
    · simp only [BurnLog.total, BurnStart.state, Nat.add_zero]
      exact TransactionState.supply_restoreTxState hp
    · change ended.state.supply + log.total = entry.supply at ih
      simp only [BurnStart.state]
      omega
  | createRollback _ _ _ rolled hp _ =>
    rw [rolled]
    exact TransactionState.supply_restoreTxState hp
  | @createKeep message state preparedState substate meter evm after log prepared _ _ kept ih =>
    have startSupply := supply_prepareCreation prepared
    rcases kept with kept | coded
    · rw [kept]
      exact ih.trans startSupply
    · rw [TransactionState.supply_setCode coded]
      exact ih.trans startSupply

/-- Two certified runs from the same start end in the same frame. -/
theorem RunBurns.ended_eq {start : BurnStart fork Meter} {ended ended' : Evm fork Meter}
    {log log' : BurnLog} (h : RunBurns fork Meter start ended log)
    (h' : RunBurns fork Meter start ended' log') : ended' = ended := by
  induction h generalizing ended' log' with
  | stopped | halt | skipPrecompile | precompile => cases h' <;> simp_all
  | next _ _ _ ih | bodyFrame _ _ ih => cases h' <;> simp_all <;> exact ih ‹_›
  | child _ hs _ resumed _ ihRun ihTail =>
    cases h' with
    | child _ hs' run' resumed' tail' =>
      rw [hs] at hs'
      cases hs'
      cases ihRun run'
      rw [resumed] at resumed'
      cases resumed'
      exact ihTail tail'
    | failedResume _ hs' run' resumed' =>
      rw [hs] at hs'
      cases hs'
      cases ihRun run'
      rw [resumed] at resumed'
      cases resumed'
    | _ => simp_all
  | failedResume _ hs _ resumed _ ihRun =>
    cases h' with
    | child _ hs' run' resumed' =>
      rw [hs] at hs'
      cases hs'
      cases ihRun run'
      rw [resumed] at resumed'
      cases resumed'
    | failedResume _ hs' run' resumed' =>
      rw [hs] at hs'
      cases hs'
      cases ihRun run'
      rw [resumed] at resumed'
      cases resumed'
      rfl
    | _ => simp_all
  | call entered _ _ ih =>
    cases h' with
    | call entered' run' =>
      obtain ⟨rfl, rfl⟩ := entered.unique entered'
      rw [ih run']
  | createRollback preparation _ deposit _ _ ih | createKeep preparation _ deposit _ ih =>
    cases h' with
    | createRollback preparation' run' deposit' | createKeep preparation' run' deposit' =>
      rw [preparation] at preparation'
      cases preparation'
      cases ih run'
      rw [deposit] at deposit'
      cases deposit'
      rfl

/-- Two certified runs from the same start have the same total.

So the total is a function of the run, whatever the certificate. -/
theorem RunBurns.total_eq {start : BurnStart fork Meter} {ended ended' : Evm fork Meter}
    {log log' : BurnLog} (h : RunBurns fork Meter start ended log)
    (h' : RunBurns fork Meter start ended' log') : log'.total = log.total := by
  have same := h.ended_eq h'
  subst same
  have := h.supply
  have := h'.supply
  omega

/-- Each burn that a certified log counts is the burn of a step of SELFDESTRUCT that the run takes.

The run reaches a running frame whose step runs SELFDESTRUCT, in the account the burn is from.

The burn is the burn of that step, and it is above 0. -/
theorem RunBurns.counted {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    {originator beneficiary : Address} {amount : Nat} (h : RunBurns fork Meter start ended log)
    (counted : log.Counted originator beneficiary amount) :
    ∃ evm after : Evm fork Meter, RunReaches fork Meter start evm ∧ evm.running = true ∧
      step fork evm = .ok (.next after) ∧ RunsSelfdestruct evm ∧
      originator = evm.message.currentTarget ∧
      amount = selfdestructBurn fork evm.state originator beneficiary ∧ amount ≠ 0 := by
  induction h with
  | stopped => exact counted.elim
  | halt => exact counted.elim
  | next running step _ ih =>
    rcases counted with c | c
    · obtain ⟨runs, o, a, nonzero⟩ := counted_stepBurnLog (Meter := Meter) c
      exact ⟨_, _, .here _, running, step, runs, o, a, nonzero⟩
    · obtain ⟨evm, after, reached, rest⟩ := ih c
      exact ⟨evm, after, .next running step reached, rest⟩
  | child running step run resumed _ ihChild ihTail =>
    rcases counted with c | c
    · obtain ⟨evm, after, reached, rest⟩ := ihChild c
      exact ⟨evm, after, .childRun running step reached, rest⟩
    · obtain ⟨evm, after, reached, rest⟩ := ihTail c
      exact ⟨evm, after, .childTail running step run resumed reached, rest⟩
  | failedResume => exact counted.elim
  | bodyFrame selected _ ih =>
    obtain ⟨evm, after, reached, rest⟩ := ih counted
    exact ⟨evm, after, .body selected reached, rest⟩
  | skipPrecompile => exact counted.elim
  | precompile => exact counted.elim
  | call entered _ _ ih =>
    split at counted
    · exact counted.elim
    · obtain ⟨evm, after, reached, rest⟩ := ih counted
      exact ⟨evm, after, .call entered reached, rest⟩
  | createRollback => exact counted.elim
  | createKeep preparation _ _ _ ih =>
    obtain ⟨evm, after, reached, rest⟩ := ih counted
    exact ⟨evm, after, .create preparation reached, rest⟩

/-- From Glamsterdam, a certified log counts no burn, so its total is 0. -/
theorem RunBurns.total_eq_zero_of_glamsterdam {start : BurnStart fork Meter}
    {ended : Evm fork Meter} {log : BurnLog} (hfork : .glamsterdam ≤ fork)
    (h : RunBurns fork Meter start ended log) : log.total = 0 := by
  refine BurnLog.total_eq_zero_of_not_counted fun originator beneficiary amount counted => ?_
  obtain ⟨_, _, _, _, _, _, _, hamount, nonzero⟩ := h.counted counted
  have early := (of_selfdestructBurn_ne_zero fun zero => nonzero (hamount.trans zero)).2
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le early hfork)

/-- Every successful run of a frame has a certificate.

The runner of its messages must give a certificate of each message that it runs. -/
theorem runBurns_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (runs : RunnerEnsures (fun caller message child =>
      ∃ log, RunBurns fork Meter (BurnStart.child caller message) child log) runChild)
    {evm ended : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok ended) :
    ∃ log, RunBurns fork Meter (.frame evm) ended log := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 =>
    cases h
    exact ⟨.empty, .halt (by assumption) (by assumption) (Bool.eq_false_iff.mpr (by assumption))⟩
  case case3 =>
    rename_i result _ ih
    obtain ⟨rest, tail⟩ := ih h
    exact ⟨_, .next (by assumption) result tail⟩
  case case4 => cases h
  case case5 => cases h
  case case6 =>
    rename_i hstep _ _ _ hchild _ resumed _
    cases h
    obtain ⟨middle, run⟩ := runs _ _ _ _ hchild
    exact ⟨.rollback middle,
      .failedResume (by assumption) hstep run resumed (Bool.eq_false_iff.mpr (by assumption))⟩
  case case7 =>
    rename_i hstep _ _ _ hchild _ resumed _ ih
    obtain ⟨middle, run⟩ := runs _ _ _ _ hchild
    obtain ⟨rest, tail⟩ := ih h
    exact ⟨.append middle rest, .child (by assumption) hstep run resumed tail⟩
  case case8 =>
    cases h
    exact ⟨.empty, .stopped _ (Bool.eq_false_iff.mpr (by assumption))⟩

private theorem childRelByKind_burns {caller : Evm fork Meter} {message : Message fork}
    {child : Evm fork Meter}
    (c : ChildRelByKind
      (fun (message : Message fork) state substate (meter : Meter) ended =>
        (∃ log, RunBurns fork Meter (.call message state substate meter) ended log) ∧
          ended.state.parent = state.parent)
      (fun (message : Message fork) state substate (meter : Meter) ended =>
        (∃ log, RunBurns fork Meter (.create message state substate meter) ended log) ∧
          ended.state.parent = state.parent) caller message child) :
    (∃ log, RunBurns fork Meter (BurnStart.child caller message) child log) ∧
      child.state.parent = caller.state.parent := by
  unfold ChildRelByKind ChildRel at c
  unfold BurnStart.child
  split at c <;> rename_i h <;> simp only [h] <;> exact c

/-- Every successful call and creation has a certificate of its run.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_runBurns [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ∃ log, RunBurns fork Meter (.call message state substate meter) ended.val log) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ∃ log, RunBurns fork Meter (.create message state substate meter) ended.val log) := by
  have key := processMessage_frame_byKind (fork := fork) (Meter := Meter)
    (F := fun a b => (∃ log, RunBurns fork Meter (.body a) b log) ∧
      b.state.parent = a.state.parent)
    (Mcall := fun message state substate meter ended =>
      (∃ log, RunBurns fork Meter (.call message state substate meter) ended log) ∧
        ended.state.parent = state.parent)
    (Mcreate := fun message state substate meter ended =>
      (∃ log, RunBurns fork Meter (.create message state substate meter) ended log) ∧
        ended.state.parent = state.parent)
    (by
      intro _ _ _ _ _ runs selected h
      have both := fun caller message lt ended hran =>
        childRelByKind_burns (runs caller message lt ended hran)
      obtain ⟨log, run⟩ := runBurns_runFrame (fun c m lt e hr => (both c m lt e hr).1) h
      exact ⟨⟨log, .bodyFrame selected run⟩,
        parent_runFrame (fun c m lt e hr => (both c m lt e hr).2) h⟩)
    (fun evm selected skipped => ⟨⟨_, .skipPrecompile evm _ selected skipped⟩, rfl⟩)
    (fun selected enabled h =>
      ⟨⟨_, .precompile selected enabled h⟩, (staticStep_runPrecompile h).parent⟩)
    (by
      intro message state entry substate entrySubstate meter ended hentry hrun
      obtain ⟨⟨log, run⟩, hp⟩ := hrun
      have hp' : ended.state.parent = state.parent := hp.trans (parent_entered hentry)
      exact ⟨⟨_, .call hentry run hp'⟩, (parent_rollbackOnError state ended).trans hp'⟩)
    (by
      intro message state prepared substate meter evm after hprep hm hd
      obtain ⟨⟨log, run⟩, hp⟩ := hm
      have hp' := hp.trans (parent_prepareCreation hprep)
      refine ⟨?_, (parent_depositCode hd).trans hp'⟩
      rcases (depositCode_cases hd).2.2 with rolled | kept | coded
      · exact ⟨_, .createRollback hprep run hd rolled hp'⟩
      · exact ⟨_, .createKeep hprep run hd (.inl kept)⟩
      · exact ⟨_, .createKeep hprep run hd (.inr coded)⟩)
    n
  exact ⟨fun message state substate meter held hn ended h =>
      (key.1 message state substate meter held hn ended h).1,
    fun message state substate meter held hn ended h =>
      (key.2 message state substate meter held hn ended h).1⟩

end EthLib.Execution.Evm

module

public import EthLib.Execution.Proofs.Evm.Call.Burn

/-!
# Proofs: the log of burns of a run of a frame, a call or a creation

A certificate of a run gives its log of burns, from the steps of the interpreter.

Each step that gives the next frame adds the log of the step.

Each step that sends a message adds the log of that message, once the caller resumes.

A step that keeps the state up to the records of its reads adds nothing.

A call that ends with an error rolls back, and so does a creation that fails to deposit its code.

Their logs then count for nothing.

The supply at the end plus the total of the log is the supply at the start.

So the supplies at the two ends fix the total, whatever the certificate.

The log splits that total into burns, and each burn it counts comes from a step of SELFDESTRUCT.

From Glamsterdam, no step burns, so the total is 0.

Every successful call and creation has a certificate.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Where a certified run starts: a frame, or a call or a creation from its start. -/
inductive BurnStart (fork : Fork) (Meter : Type) where
  | frame (evm : Evm fork Meter)
  | call (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
  | create (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)

/-- The state at the start of the run. -/
def BurnStart.state : BurnStart fork Meter → TransactionState
  | .frame evm => evm.state
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

A run of a frame is made of steps that keep the state up to reads, and steps of the interpreter.

A step that sends a message adds nothing, and the frame that resumes adds the log of the message.

A call starts from the state it enters, and rolls back when it ends with an error.

A creation prepares its account, runs as a call, and deposits its code.

A creation whose deposit rolls back the state counts nothing of its log. -/
inductive RunBurns (fork : Fork) (Meter : Type) [GasMeter Meter] :
    BurnStart fork Meter → Evm fork Meter → BurnLog → Prop
  | static {evm after : Evm fork Meter} (h : StaticStep evm after) :
      RunBurns fork Meter (.frame evm) after .empty
  | append {evm middle after : Evm fork Meter} {first second : BurnLog}
      (head : RunBurns fork Meter (.frame evm) middle first)
      (tail : RunBurns fork Meter (.frame middle) after second) :
      RunBurns fork Meter (.frame evm) after (.append first second)
  | next {evm after : Evm fork Meter} (h : step fork evm = .ok (.next after)) :
      RunBurns fork Meter (.frame evm) after (stepBurnLog evm after)
  | send {evm caller : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
      (h : step fork evm = .ok (.child caller message resume)) :
      RunBurns fork Meter (.frame evm) caller .empty
  | resume {evm caller child after : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} {log : BurnLog}
      (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child log)
      (resumed : resume child = .ok after) :
      RunBurns fork Meter (.frame evm) after log
  | call {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter} {log : BurnLog}
      (entered : Entered fork message state substate entry entrySubstate)
      (run : RunBurns fork Meter (.frame (startFrame message entry entrySubstate meter)) ended log)
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

/-- A certified run ends with the supply of its start, less the total of its log. -/
theorem RunBurns.supply {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    (h : RunBurns fork Meter start ended log) :
    ended.state.supply + log.total = start.state.supply := by
  induction h with
  | static h =>
    simpa only [BurnLog.total, BurnStart.state, Nat.add_zero] using
      TransactionState.supply_eq_of_sameOutside h.state
  | append _ _ ih1 ih2 =>
    simp only [BurnLog.total, BurnStart.state] at *
    omega
  | next h => exact supply_of_step_eq_next h
  | send h => simpa only [BurnLog.total, BurnStart.state, Nat.add_zero] using
      supply_of_step_eq_child h
  | resume h _ resumed ih =>
    have hw := supply_of_step_eq_child h
    have hc := sameContext_of_step_eq_child h resumed
    rw [BurnStart.state_child] at ih
    rw [hc.state, state_incorporateChild] at *
    simp only [BurnStart.state]
    omega
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

/-- Two certificates of a run from the same start to the same end have the same total. -/
theorem RunBurns.total_eq {start : BurnStart fork Meter} {ended : Evm fork Meter}
    {log log' : BurnLog} (h : RunBurns fork Meter start ended log)
    (h' : RunBurns fork Meter start ended log') : log.total = log'.total := by
  have := h.supply
  have := h'.supply
  omega

/-- Each burn that a certified log counts is the burn of a step of SELFDESTRUCT.

That step runs SELFDESTRUCT in the account the burn is from, and the burn is above 0. -/
theorem RunBurns.counted {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    {originator beneficiary : Address} {amount : Nat} (h : RunBurns fork Meter start ended log)
    (counted : log.Counted originator beneficiary amount) :
    ∃ evm after, step fork evm = .ok (.next after) ∧ RunsSelfdestruct evm ∧
      originator = evm.message.currentTarget ∧
      amount = selfdestructBurn fork evm.state originator beneficiary ∧ amount ≠ 0 := by
  sorry

/-- From Glamsterdam, a certified log counts no burn, so its total is 0. -/
theorem RunBurns.total_eq_zero {start : BurnStart fork Meter} {ended : Evm fork Meter}
    {log : BurnLog} (hfork : .glamsterdam ≤ fork) (h : RunBurns fork Meter start ended log) :
    log.total = 0 := by
  sorry

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
  have key := processMessage_rel_byKind (fork := fork) (Meter := Meter)
    (R := fun a b => (∃ log, RunBurns fork Meter (.frame a) b log) ∧
      b.state.parent = a.state.parent)
    (Inv := fun _ => True)
    (Mcall := fun message state substate meter ended =>
      (∃ log, RunBurns fork Meter (.call message state substate meter) ended log) ∧
        ended.state.parent = state.parent)
    (Mcreate := fun message state substate meter ended =>
      (∃ log, RunBurns fork Meter (.create message state substate meter) ended log) ∧
        ended.state.parent = state.parent)
    (fun _ => ⟨⟨_, .static (.refl _)⟩, rfl⟩)
    (fun {_ _ _} ⟨⟨_, l1⟩, p1⟩ ⟨⟨_, l2⟩, p2⟩ => ⟨⟨_, .append l1 l2⟩, p2.trans p1⟩)
    (fun _ r => trivial)
    (fun _ e _ => ⟨⟨_, .static (staticStep_exceptionalHalt _ _)⟩,
      (staticStep_exceptionalHalt _ _).parent⟩)
    (by
      intro evm result _ h
      have p := stepRules_parent.step h
      cases result with
      | next after => exact ⟨⟨_, .next h⟩, p⟩
      | child caller message resume =>
        refine ⟨⟨⟨_, .send h⟩, p.1⟩, fun child after hres c => ?_⟩
        obtain ⟨⟨log, run⟩, cparent⟩ := childRelByKind_burns c
        exact ⟨⟨log, .resume h run hres⟩, p.2 child after hres cparent⟩)
    (fun evm _ => ⟨⟨_, .static (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩)⟩, rfl⟩)
    (fun h _ => ⟨⟨_, .static (staticStep_runPrecompile h)⟩, (staticStep_runPrecompile h).parent⟩)
    (by
      intro message state entry substate entrySubstate meter ended hentry hrun
      obtain ⟨⟨log, run⟩, hp⟩ := hrun trivial
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

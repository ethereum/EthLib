module

public import EthLib.Execution.Proofs.Evm.Call.BurnStep

/-!
# Proofs: a burn log for an actual message run

The trace follows the interpreter's steps, messages, resumes and rollbacks.

The trace records the interpreter's step and resume equations.

The log counts a child's burns only when its writes survive the enclosing frame.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The initial configuration of a frame, call or creation. -/
inductive BurnStart (fork : Fork) (Meter : Type) where
  | frame (evm : Evm fork Meter)
  | body (evm : Evm fork Meter)
  | call (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
  | create (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)

/-- The state in the initial configuration. -/
def BurnStart.state : BurnStart fork Meter → TransactionState
  | .frame evm | .body evm => evm.state
  | .call _ state _ _ | .create _ state _ _ => state

/-- The child runs as a call when it has a target, and as a creation otherwise. -/
def BurnStart.child (caller : Evm fork Meter) (message : Message fork) : BurnStart fork Meter :=
  match message.target with
  | some _ => .call message caller.state caller.substate.child
      (GasMeter.start message.gas message.reservoir)
  | none => .create message caller.state caller.substate.child
      (GasMeter.start message.gas message.reservoir)

/-- The child starts with the state of its caller. -/
theorem BurnStart.state_child (caller : Evm fork Meter) (message : Message fork) :
    (BurnStart.child caller message).state = caller.state := by
  unfold BurnStart.child
  split <;> rfl

/-- A structural certificate of an interpreter run and its burn log.

The next-step and child constructors retain the actual step and resume equations.

A call and a creation record the rollback that discards their writes. -/
inductive RunBurns (fork : Fork) (Meter : Type) [GasMeter Meter] :
    BurnStart fork Meter → Evm fork Meter → BurnLog → Prop
  | stopped (evm) (h : evm.running = false) : RunBurns fork Meter (.frame evm) evm .empty
  | halt {evm error} (running : evm.running = true) (h : step fork evm = .error error)
      (notAborts : error.aborts = false) :
      RunBurns fork Meter (.frame evm) (exceptionalHalt evm error) .empty
  | next {evm after ended rest} (running : evm.running = true)
      (h : step fork evm = .ok (.next after))
      (tail : RunBurns fork Meter (.frame after) ended rest) :
      RunBurns fork Meter (.frame evm) ended (.append (stepBurnLog evm after) rest)
  | child {evm caller message resume child after ended middle rest}
      (running : evm.running = true) (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child middle)
      (resumed : resume child = .ok after)
      (tail : RunBurns fork Meter (.frame after) ended rest) :
      RunBurns fork Meter (.frame evm) ended (.append middle rest)
  | failedResume {evm caller message resume child middle error}
      (running : evm.running = true) (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child middle)
      (resumed : resume child = .error error) (notAborts : error.aborts = false) :
      RunBurns fork Meter (.frame evm) (exceptionalHalt evm error) (.rollback middle)
  | bodyFrame {evm ended log} (selected : precompileAddress fork evm.message = none)
      (run : RunBurns fork Meter (.frame evm) ended log) :
      RunBurns fork Meter (.body evm) ended log
  | skipPrecompile (evm : Evm fork Meter) (address : Nat)
      (selected : precompileAddress fork evm.message = some address)
      (skipped : evm.message.disablePrecompiles = true ∨ runPrecompile fork address evm = none) :
      RunBurns fork Meter (.body evm) { evm with running := false } .empty
  | precompile {address evm after}
      (selected : precompileAddress fork evm.message = some address)
      (enabled : evm.message.disablePrecompiles = false)
      (h : runPrecompile fork address evm = some after) :
      RunBurns fork Meter (.body evm) after .empty
  | call {message state entry substate entrySubstate meter ended log}
      (entered : Entered fork message state substate entry entrySubstate)
      (run : RunBurns fork Meter (.body (startFrame message entry entrySubstate meter)) ended log)
      (parent : ended.state.parent = state.parent) :
      RunBurns fork Meter (.call message state substate meter) (rollbackOnError state ended)
        (if ended.error.isSome then .rollback log else log)
  | createRollback {message state prepared substate meter evm after log}
      (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
      (run : RunBurns fork Meter (.call message prepared substate meter) evm log)
      (deposit : depositCode fork state evm = .ok after)
      (rolled : after.state = evm.state.restoreTxState state)
      (parent : evm.state.parent = state.parent) :
      RunBurns fork Meter (.create message state substate meter) after (.rollback log)
  | createKeep {message state prepared substate meter evm after log}
      (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
      (run : RunBurns fork Meter (.call message prepared substate meter) evm log)
      (deposit : depositCode fork state evm = .ok after)
      (kept : after.state = evm.state ∨
        evm.state.setCode fork evm.message.currentTarget evm.output = .ok after.state) :
      RunBurns fork Meter (.create message state substate meter) after log

/-- A certified run keeps the block of its starting state. -/
theorem RunBurns.parent {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    (h : RunBurns fork Meter start ended log) : ended.state.parent = start.state.parent := by
  induction h with
  | stopped => rfl
  | halt => rfl
  | next _ h _ ih =>
    exact ih.trans (stepRules_parent.step h)
  | bodyFrame _ _ ih => exact ih
  | child _ h _ resumed _ ihChild ihTail =>
    rw [BurnStart.state_child] at ihChild
    exact ihTail.trans ((stepRules_parent.step h).2 _ _ resumed ihChild)
  | failedResume => rfl
  | skipPrecompile => rfl
  | precompile _ _ h => exact (staticStep_runPrecompile h).parent
  | call _ _ hp _ => exact (parent_rollbackOnError _ _).trans hp
  | createRollback hp _ hd _ _ ih =>
    exact (parent_depositCode hd).trans (ih.trans (parent_prepareCreation hp))
  | createKeep hp _ hd _ ih =>
    exact (parent_depositCode hd).trans (ih.trans (parent_prepareCreation hp))

/-- The supply of the starting state is the end supply plus the log's surviving burns. -/
theorem RunBurns.supply {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    (h : RunBurns fork Meter start ended log) :
    ended.state.supply + log.total = start.state.supply := by
  induction h with
  | stopped => rfl
  | halt => rfl
  | next _ step _ ih =>
    have := supply_step_next step
    simp only [BurnLog.total, BurnStart.state] at *
    omega
  | child _ step _ resumed _ ihChild ihTail =>
    have hw := supply_step_child step
    have hc := sameContext_of_step_eq_child step resumed
    simp only [BurnStart.state] at ihTail
    rw [hc.state, state_incorporateChild] at ihTail
    rw [BurnStart.state_child] at ihChild
    simp only [BurnLog.total, BurnStart.state] at *
    omega
  | failedResume => rfl
  | skipPrecompile => rfl
  | bodyFrame _ _ ih => exact ih
  | precompile _ _ h =>
    exact TransactionState.supply_eq_of_sameOutside (staticStep_runPrecompile h).state
  | @call message state entry substate entrySubstate meter ended log entered _ hp ih =>
    have entrySupply : entry.supply = state.supply := by
      rcases entered with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
      · exact supply_startState _ _
      · exact (TransactionState.supply_moveEther moved).trans (supply_startState _ _)
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
    have startSupply : preparedState.supply = state.supply := by
      unfold prepareCreation at prepared
      split at prepared
      · rw [TransactionState.supply_incrementNonce (Base.mapError_ok_iff.mp prepared),
          TransactionState.supply_markAccountCreated, TransactionState.supply_destroyStorage]
      · cases prepared
        rw [TransactionState.supply_markAccountCreated, TransactionState.supply_destroyStorage]
    rcases kept with kept | coded
    · rw [kept]
      exact ih.trans startSupply
    · rw [TransactionState.supply_setCode coded]
      exact ih.trans startSupply


/-- An actual successful frame run has a structural burn certificate.

The runner must provide certificates for the actual children that it returns. -/
theorem runBurns_runFrame [LawfulGasMeter Meter] {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (runs : ∀ caller message lt child, runChild caller message lt = .ok child →
      ∃ log, RunBurns fork Meter (BurnStart.child caller message) child.val log)
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
      .failedResume (by assumption) hstep run resumed
        (Bool.eq_false_iff.mpr (by assumption))⟩
  case case7 =>
    rename_i hstep _ _ _ hchild _ resumed _ ih
    obtain ⟨middle, run⟩ := runs _ _ _ _ hchild
    obtain ⟨rest, tail⟩ := ih h
    exact ⟨.append middle rest, .child (by assumption) hstep run resumed tail⟩
  case case8 =>
    cases h
    exact ⟨.empty, .stopped _ (Bool.eq_false_iff.mpr (by assumption))⟩


/-- A frame certificate becomes a call certificate at the actual entry and rollback. -/
theorem RunBurns.of_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter} {log : BurnLog}
    (entered : Entered fork message state substate entry entrySubstate)
    (run : RunBurns fork Meter (.body (startFrame message entry entrySubstate meter)) ended log) :
    ∃ log, RunBurns fork Meter (.call message state substate meter)
      (rollbackOnError state ended) log := by
  have entryParent : entry.parent = state.parent := by
    rcases entered with ⟨-, rfl, -⟩ | ⟨-, moved, -⟩
    · exact parent_startState _ _
    · exact (TransactionState.parent_moveEther moved).trans (parent_startState _ _)
  exact ⟨_, .call entered run (run.parent.trans entryParent)⟩

/-- Every successful call and creation has a structural certificate of its actual execution. -/
theorem processMessage_runBurns [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        ∃ log, RunBurns fork Meter (.call message state substate meter) ended.val log) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        ∃ log, RunBurns fork Meter (.create message state substate meter) ended.val log) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have callCase : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          ∃ log, RunBurns fork Meter (.call message state substate meter) ended.val log := by
      intro message state substate meter held hn ended h
      rw [processMessage] at h
      obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
      have hval := congrArg Subtype.val rolled
      simp only at hval
      rw [← hval]
      dsimp only at hdo
      split at hdo
      all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
      all_goals
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            obtain ⟨log, trace⟩ := runBurns_runFrame (fun caller' message' lt child hrun' => by
              unfold BurnStart.child
              split at hrun'
              · rename_i ht
                simp only [ht]
                exact (ih message'.gas (by omega)).1 message' caller'.state _ _ _ rfl child hrun'
              · rename_i ht
                simp only [ht]
                exact (ih message'.gas (by omega)).2 message' caller'.state _ _ _ rfl child hrun')
              hrun
            refine RunBurns.of_entered (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨‹_›, rfl,
                     by first | rfl | (split <;> first | rfl | contradiction)⟩))
              (.bodyFrame hpa trace)
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            refine RunBurns.of_entered (by first
                | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                    Base.mapError_ok_iff.mp hm,
                    by first | rfl | (split <;> first | rfl | contradiction)⟩
                | (cases hm
                   exact Or.inl ⟨‹_›, rfl,
                     by first | rfl | (split <;> first | rfl | contradiction)⟩))
              (.skipPrecompile _ addr hpa (.inl (by assumption)))
          · split at hdo
            · rename_i after hrp
              cases hdo
              refine RunBurns.of_entered (by first
                  | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                      Base.mapError_ok_iff.mp hm,
                      by first | rfl | (split <;> first | rfl | contradiction)⟩
                  | (cases hm
                     exact Or.inl ⟨‹_›, rfl,
                       by first | rfl | (split <;> first | rfl | contradiction)⟩))
                (.precompile hpa (Bool.eq_false_iff.mpr (by assumption)) hrp)
            · rename_i hnone
              cases hdo
              refine RunBurns.of_entered (by first
                  | exact Or.inr ⟨‹message.shouldTransferValue = true ∧ message.value ≠ 0›,
                      Base.mapError_ok_iff.mp hm,
                      by first | rfl | (split <;> first | rfl | contradiction)⟩
                  | (cases hm
                     exact Or.inl ⟨‹_›, rfl,
                       by first | rfl | (split <;> first | rfl | contradiction)⟩))
                (.skipPrecompile _ addr hpa (.inr (by
                  split at hnone <;> first | exact hnone | contradiction)))

    refine ⟨callCase, ?_⟩
    intro message state substate meter held hn ended h
    rw [processCreateMessage] at h
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · cases h
      obtain ⟨log, trace⟩ := callCase message prepared substate meter held hn _ hrun
      have hd := ‹depositCode fork state evm = .ok _›
      rcases (depositCode_cases hd).2.2 with rolled | kept | coded
      · exact ⟨.rollback log,
          .createRollback hp trace hd rolled (trace.parent.trans (parent_prepareCreation hp))⟩
      · exact ⟨log, .createKeep hp trace hd (.inl kept)⟩
      · exact ⟨log, .createKeep hp trace hd (.inr coded)⟩

end EthLib.Execution.Evm

module

public import EthLib.Execution.Proofs.Evm.Call.BurnRun
public import EthLib.Execution.Proofs.Evm.Call.StorageAt

/-!
# Proofs: a run that reaches no frame at an address keeps or wipes its storage

A run of a call or a creation reaches the frames that its certificate steps through.

When none of them runs at an address, the storage of that address ends as it started, or wiped.

A wipe can come from an empty account that a change deletes, as EIP-161 and EIP-7610 allow.

The statements allow any wipe: they do not show that the account was empty.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {Meter : Type} [GasMeter Meter] {address : Address}

/-- No frame that a run from `start` reaches runs at `address`.

A precompile runs no frame. -/
def RunsAway (address : Address) (start : BurnStart fork Meter) : Prop :=
  ∀ reached, RunReaches fork Meter start reached → reached.message.currentTarget ≠ address

/-- A certified run that reaches no frame at `address` keeps or wipes its storage. -/
theorem RunBurns.keptOrWiped {start : BurnStart fork Meter} {ended : Evm fork Meter}
    {log : BurnLog} (h : RunBurns fork Meter start ended log) (away : RunsAway address start) :
    KeptOrWiped address start.state ended.state := by
  let T := stepRules_keptOrWiped (fork := fork) (Meter := Meter) address
  induction h with
  | stopped => exact .refl _ _
  | halt running _ _ =>
    exact .of_eq fun key =>
      ((staticStep_exceptionalHalt _ _).state address List.not_mem_nil).2.1 key
  | next running hstep _ ih =>
    exact ((T.step hstep).2 (away _ (.here _))).trans
      (ih fun r hr => away r (.next running hstep hr))
  | child running hstep _ resumed _ ihRun ihTail =>
    -- The step sends the message from a frame that keeps the storage.
    have hcaller := ((T.step hstep).1.2 (away _ (.here _)))
    -- The run of the message keeps it, and the caller resumes in the state of the child.
    have hrun := ihRun fun r hr => away r (.childRun running hstep hr)
    rw [BurnStart.state_child] at hrun
    have hstate := (sameContext_of_step_eq_child hstep resumed).state
    rw [state_incorporateChild] at hstate
    have htail := ihTail fun r hr => away r (.childTail running hstep ‹_› resumed hr)
    simp only [BurnStart.state] at htail ⊢
    rw [hstate] at htail
    exact (hcaller.trans hrun).trans htail
  | failedResume running hstep _ _ _ _ =>
    exact .of_eq fun key =>
      ((staticStep_exceptionalHalt _ _).state address List.not_mem_nil).2.1 key
  | bodyFrame selected _ ih => exact ih fun r hr => away r (.body selected hr)
  | skipPrecompile => exact .refl _ _
  | precompile _ _ hrun =>
    -- A precompile writes no storage.
    exact .of_eq fun key =>
      ((staticStep_runPrecompile hrun).state address List.not_mem_nil).2.1 key
  | call entered _ parent ih =>
    have hrun := ih fun r hr => away r (.call entered hr)
    simp only [BurnStart.state, startFrame] at hrun ⊢
    have hentry := keptOrWiped_entered (address := address) entered
    unfold rollbackOnError
    split
    · -- A call that fails gives back the state it was sent from.
      exact .of_eq fun key => getStorage_restoreTxState parent address key
    · exact hentry.trans hrun
  | createRollback preparation _ _ rolled parent _ =>
    simp only [BurnStart.state]
    rw [rolled]
    exact .of_eq fun key => getStorage_restoreTxState parent address key
  | createKeep preparation _ _ kept ih =>
    have hrun := ih fun r hr => away r (.create preparation hr)
    simp only [BurnStart.state] at hrun ⊢
    refine (keptOrWiped_prepareCreation preparation).trans (hrun.trans ?_)
    rcases kept with hk | hk
    · rw [hk]
      exact .refl _ _
    · exact keptOrWiped_setCode hk

variable [LawfulGasMeter Meter]

/-- A call that reaches no frame at `address` keeps or wipes its storage. -/
theorem keptOrWiped_processMessage_of_away {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    (away : RunsAway address (.call message state substate meter)) :
    KeptOrWiped address state ended.val.state := by
  obtain ⟨log, run⟩ := (processMessage_runBurns message.gas).1 message state substate meter held
    rfl ended h
  exact run.keptOrWiped away

/-- A creation that reaches no frame at `address` keeps or wipes its storage. -/
theorem keptOrWiped_processCreateMessage_of_away {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (away : RunsAway address (.create message state substate meter)) :
    KeptOrWiped address state ended.val.state := by
  obtain ⟨log, run⟩ := (processMessage_runBurns message.gas).2 message state substate meter held
    rfl ended h
  exact run.keptOrWiped away

end EthLib.Execution.Evm

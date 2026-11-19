module

public import EthLib.Execution.Proofs.Evm.Call.StepRules
public import EthLib.Execution.Proofs.Evm.Call.TransferLog

/-!
# Proofs: from Glamsterdam, a message keeps both lists of logs equal

A frame keeps two lists of logs: its own, and those that a simulation reports.

From Glamsterdam, a move of ether adds the same transfer log to both, or none.

A LOG writes the same log to both lists, and a child passes on both or neither.

So a message that starts with equal lists ends with equal lists.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The logs of a frame equal the logs that a simulation reports. -/
private def LogsMatch (evm : Evm fork Meter) : Prop :=
  evm.substate.simulatedLogs = evm.substate.logs

omit [GasMeter Meter] in
/-- From Glamsterdam, the end of SELFDESTRUCT keeps equal lists of logs. -/
private theorem logsMatch_finishSelfdestruct (hfork : fork ≥ .glamsterdam) {beneficiary : Address}
    {refund : Nat} {evm after : Evm fork Meter}
    (h : finishSelfdestruct fork beneficiary refund evm = .ok after) (start : LogsMatch evm) :
    LogsMatch after := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    unfold LogsMatch at start ⊢
    dsimp only
    rw [pushSimulatedTransferLog_of_glamsterdam hfork, start]

/-- A caller with equal lists that takes in a child with equal lists keeps equal lists. -/
private theorem logsMatch_incorporateChild {caller child : Evm fork Meter}
    (hcaller : LogsMatch caller) (hchild : LogsMatch child) :
    LogsMatch (incorporateChild fork caller child) := by
  unfold LogsMatch at hcaller hchild ⊢
  unfold incorporateChild
  split
  · dsimp only
    rw [hcaller, hchild]
  · exact hcaller

/-- From Glamsterdam, each write of a step keeps equal lists of logs. -/
private theorem stepRules_logsMatch (hfork : fork ≥ .glamsterdam) :
    StepRules fork (fun a b : Evm fork Meter => LogsMatch a → LogsMatch b) where
  trans hab hbc h := hbc (hab h)
  static h hm := by
    unfold LogsMatch at hm ⊢
    rw [h.simulatedLogs, h.logs]
    exact hm
  sstore _ _ _ _ _ _ _ h := h
  tstore _ _ _ _ h := h
  log _ _ hsub _ _ h := by
    unfold LogsMatch at h ⊢
    rw [hsub]
    dsimp only
    rw [h]
  selfdestruct _ _ h := logsMatch_finishSelfdestruct hfork h
  incrementNonce _ _ _ _ _ h := h
  incorporate h hc := logsMatch_incorporateChild hc (h hc)

/-- From Glamsterdam, calls and creations that start with equal lists end with equal lists. -/
private theorem logsMatch_processMessage_induction [LawfulGasMeter Meter]
    (hfork : fork ≥ .glamsterdam) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        substate.simulatedLogs = substate.logs → LogsMatch ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        substate.simulatedLogs = substate.logs → LogsMatch ended.val) :=
  (stepRules_logsMatch hfork).processMessage
    (M := fun _ _ substate _ ended => substate.simulatedLogs = substate.logs → LogsMatch ended)
    (fun {message _ _ substate _ _ ended} hentry hd start => by
      have h0 : LogsMatch ended := hd (by
        rcases hentry with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
        · exact start
        · show pushSimulatedTransferLog fork _ _ _ _ = pushTransferLog fork _ _ _ _
          rw [pushSimulatedTransferLog_of_glamsterdam hfork, start])
      unfold rollbackOnError
      split
      · exact h0
      · exact h0)
    (fun _ hm hd start => by
      unfold LogsMatch
      rw [(depositCode_cases hd).1]
      exact hm start)
    (fun h _ => h rfl) n

/-- From Glamsterdam, a call that starts with equal lists of logs ends with equal lists. -/
theorem simulatedLogs_processMessage [LawfulGasMeter Meter] (hfork : fork ≥ .glamsterdam)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended)
    (start : substate.simulatedLogs = substate.logs) :
    ended.val.substate.simulatedLogs = ended.val.substate.logs :=
  (logsMatch_processMessage_induction hfork message.gas).1 message state substate meter held rfl
    ended h start

/-- From Glamsterdam, a creation that starts with equal lists of logs ends with equal lists. -/
theorem simulatedLogs_processCreateMessage [LawfulGasMeter Meter] (hfork : fork ≥ .glamsterdam)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (start : substate.simulatedLogs = substate.logs) :
    ended.val.substate.simulatedLogs = ended.val.substate.logs :=
  (logsMatch_processMessage_induction hfork message.gas).2 message state substate meter held rfl
    ended h start

end EthLib.Execution.Evm

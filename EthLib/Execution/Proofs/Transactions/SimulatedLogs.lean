module

public import EthLib.Execution.Proofs.Evm.Call.SimulatedLogs
public import EthLib.Execution.Proofs.Transactions.Deletion

/-!
# Proofs: from Glamsterdam, a simulation reports the logs of each transaction

A transaction starts with no log in either list.

From Glamsterdam, its message then ends with equal lists.

A message that fails, or never runs, has no log in either list.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork bind_ok_iff)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The first frame of a transaction keeps both lists of logs of the substate it is given. -/
private theorem logs_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    first.substate.logs = substate.logs ∧
      first.substate.simulatedLogs = substate.simulatedLogs := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨rfl, rfl⟩
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨rfl, rfl⟩
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · dsimp only at h
    obtain ⟨done, -, h⟩ := bind_ok_iff.mp h
    generalize (if message.value ≠ 0 then _ else done.state) = read0 at h
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact ⟨rfl, rfl⟩
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact ⟨rfl, rfl⟩

/-- From Glamsterdam, a message call that starts with equal lists of logs ends with equal lists. -/
theorem simulatedLogs_processMessageCall [LawfulGasMeter Meter] (hfork : fork ≥ .glamsterdam)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (start : substate.simulatedLogs = substate.logs) :
    output.simulatedLogs = output.logs := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      rfl
  rename_i first hfirst
  obtain ⟨hlogs, hsim⟩ := logs_prepareFirstFrame hfirst
  have equal : first.substate.simulatedLogs = first.substate.logs := by
    rw [hlogs, hsim, start]
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    unfold CallOutput.ofFrame
    split
    · rfl
    · exact simulatedLogs_processCreateMessage hfork hrun equal
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    unfold CallOutput.ofFrame
    split
    · rfl
    · exact simulatedLogs_processMessage hfork hrun equal

/-- From Glamsterdam, a run of a transaction reports the logs of the transaction. -/
private theorem simulatedLogs_runTransaction [LawfulGasMeter Meter]
    (hfork : fork ≥ .glamsterdam) {env : BlockEnvironment fork} {block : BlockState}
    {included : Included} {tx : Transaction} {precompiles : Address → Option Address}
    {lifted : LiftedRules} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx precompiles lifted = .ok out) :
    out.simulatedLogs = out.logs := by
  unfold runTransaction at h
  obtain ⟨target, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨message, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, hcall, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨deleted, -, h⟩ := bind_ok_iff.mp h
  cases h
  exact simulatedLogs_processMessageCall hfork hcall rfl

/-- From Glamsterdam, a simulation reports the logs of a transaction and nothing more. -/
theorem simulatedLogs_processTransaction (hfork : fork ≥ .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included} {tx : Transaction}
    {precompiles : Address → Option Address} {lifted : LiftedRules} {out : TransactionOutput}
    (h : processTransaction env block included tx precompiles lifted = .ok out) :
    out.simulatedLogs = out.logs := by
  unfold processTransaction at h
  split at h
  · cases h
  exact simulatedLogs_runTransaction hfork h

end EthLib.Execution.Transactions

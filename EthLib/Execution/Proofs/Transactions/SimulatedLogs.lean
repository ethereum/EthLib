module

public import EthLib.Execution.Proofs.Transactions.Unfold
public import EthLib.Execution.Proofs.Evm.Call.SimulatedLogs
public import EthLib.Execution.Proofs.Evm.Call.SimulatedLogsErase
public import EthLib.Execution.Proofs.Transactions.Deletion

/-!
# Proofs: from Glamsterdam, a simulation reports the logs of each transaction

A transaction starts with no log in either list.

From Glamsterdam, its message then ends with equal lists.

A message that fails, or never runs, has no log in either list.

At every fork, the simulated logs that a message starts with change nothing else that it computes.
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

/-- The first frame of a transaction keeps the simulated logs of the substate it is given.

Everything else that it computes does not read them. -/
private theorem prepareFirstFrame_simulatedLogs (logs : Array Blocks.Log) (chainId : Nat)
    (message : Message fork) (state : State.TransactionState) (substate : Substate)
    (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    prepareFirstFrame (Meter := Meter) chainId message state
        { substate with simulatedLogs := logs } auths paid =
      (fun first => { first with substate := { first.substate with simulatedLogs := logs } }) <$>
        prepareFirstFrame (Meter := Meter) chainId message state substate auths paid := by
  unfold prepareFirstFrame
  repeat' (first
    | rfl
    | refine congrArg (fun k => _ >>= k) (funext fun _ => ?_)
    | simp only [map_bind, map_pure]
    | split)

/-- Outputs read from two runs differ only in their simulated logs when the frames do.

The output must read the frame only outside its simulated logs. -/
private theorem erase_bind_output {bound : Nat}
    (x y : Except EvmError { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ bound })
    (output : Evm fork Meter → CallOutput)
    (reads : ∀ evm, { output evm with simulatedLogs := #[] } =
      { output evm.eraseSimulatedLogs with simulatedLogs := #[] })
    (h : (fun ended => ended.val.eraseSimulatedLogs) <$> x =
      (fun ended => ended.val.eraseSimulatedLogs) <$> y) :
    (fun out => { out with simulatedLogs := #[] }) <$> (x >>= fun e => pure (output e.val)) =
      (fun out => { out with simulatedLogs := #[] }) <$> (y >>= fun e => pure (output e.val)) := by
  cases x <;> cases y <;> simp only [Functor.map, Except.map, Except.error.injEq,
    Except.ok.injEq, reduceCtorEq] at h ⊢
  · rw [h]
  · show Except.ok _ = Except.ok _
    rw [reads, h, ← reads]

/-- Two messages that differ only in the simulated logs they start with differ only in them.

Both fail with the same error, or both give the same output but for its simulated logs. -/
theorem processMessageCall_eraseSimulatedLogs [LawfulGasMeter Meter] (logs : Array Blocks.Log)
    (chainId : Nat) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    (fun output => { output with simulatedLogs := #[] }) <$>
        processMessageCall (Meter := Meter) chainId message state
          { substate with simulatedLogs := logs } auths paid =
      (fun output => { output with simulatedLogs := #[] }) <$>
        processMessageCall (Meter := Meter) chainId message state substate auths paid := by
  rw [processMessageCall_unfold, processMessageCall_unfold, prepareFirstFrame_simulatedLogs]
  rcases prepareFirstFrame (Meter := Meter) chainId message state substate auths paid with
    ⟨e, read⟩ | first
  · rfl
  simp only [Base.map_ok]
  cases message.target with
  | none =>
    dsimp only
    refine erase_bind_output _ _ (fun evm => CallOutput.ofFrame evm 0 evm.substate.touchedAccounts)
      ?_
      (processCreateMessage_eraseSimulatedLogs logs first.message first.state first.substate
        first.meter first.held)
    intro evm
    unfold CallOutput.ofFrame Evm.eraseSimulatedLogs
    by_cases h : evm.error.isSome = true <;> simp [h]
  | some target =>
    dsimp only
    refine erase_bind_output _ _ (fun evm => CallOutput.ofFrame evm first.refund
      (if fork ≥ .spuriousDragon ∧ fork < .paris ∧ evm.state.accountExistsAndIsEmpty target then
        evm.substate.touchedAccounts.insert target
      else evm.substate.touchedAccounts)) ?_
      (processMessage_eraseSimulatedLogs logs first.message first.state first.substate
        first.meter first.held)
    intro evm
    unfold CallOutput.ofFrame Evm.eraseSimulatedLogs
    by_cases h : evm.error.isSome = true <;> simp [h]

/-- From Glamsterdam, a message call that starts with equal lists of logs ends with equal lists. -/
theorem simulatedLogs_processMessageCall [LawfulGasMeter Meter] (hfork : fork ≥ .glamsterdam)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (start : substate.simulatedLogs = substate.logs) :
    output.simulatedLogs = output.logs := by
  rw [processMessageCall_unfold] at h
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
  rw [runTransaction_unfold] at h
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
  rw [processTransaction_unfold] at h
  split at h
  · cases h
  exact simulatedLogs_runTransaction hfork h

end EthLib.Execution.Transactions

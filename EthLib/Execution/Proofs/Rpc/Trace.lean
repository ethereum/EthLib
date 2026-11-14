module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Observe
public import EthLib.Execution.Rpc.Trace

/-!
# Proofs: the opcode trace

The opcode logger changes nothing in the run of a transaction, for every configuration.

The trace of a transaction of a block exists whenever the block runs it, at every fork.

From Byzantium, the trace fails exactly when the receipt of the transaction says it failed.
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)
open EthLib.Execution.Transactions

/-- A run with the opcode logger gives what the run with no observer gives.

It holds for every configuration and every bound on the entries. -/
theorem traceRun_output {fork : Fork} (config : TraceConfig) (env : BlockEnvironment fork)
    (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) :
    Prod.fst <$> traceRun config env block included tx precompiles lifted =
      processTransaction env block included tx precompiles lifted :=
  processTransactionWith_modify (fun evm result => Tracer.record config evm result) env block
    included tx precompiles lifted {}

/-- A transaction that the body of a block runs has a trace, and its receipt comes last.

From Byzantium, the receipt says it succeeded exactly when the trace says it did not fail. -/
private theorem traceTransaction_receipt {fork : Fork} (config : TraceConfig)
    (env : BlockEnvironment fork) {index : Nat} {before after : BodyOutput fork}
    {tx : Transaction} (since : Fork.byzantium ≤ fork)
    (h : applyTransaction env index before tx = .ok after) :
    ∃ trace, traceTransaction config env index before tx = .ok trace ∧
      ∃ receipt, after.receipts = before.receipts ++ [(tx.type, receipt)] ∧
        receipt.outcome = .status since (!trace.failed) := by
  unfold applyTransaction at h
  obtain ⟨included, hinc, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_ok_iff.mp h
  have hrun := traceRun_output config env before.block included tx some {}
  rw [mapError_ok_iff.mp hout] at hrun
  obtain ⟨⟨out', tracer⟩, htr, hfst⟩ := map_ok_iff.mp hrun
  dsimp only at hfst
  subst hfst
  have hinc := mapError_ok_iff.mp hinc
  dsimp only at hinc
  refine ⟨.ofRun out' tracer, ?_, ?_⟩
  · simp only [traceTransaction, hinc, htr, bind, Except.bind, Except.mapError, pure,
      Except.pure]
  obtain ⟨body, -, h⟩ := bind_ok_iff.mp h
  simp only [since, dite_true, pure, bind, Except.bind, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨_, rfl, ?_⟩
  simp only [makeReceipt, TransactionTrace.ofRun]
  cases out'.error <;> rfl

/-- A transaction that the body of a block runs has a trace, at every fork. -/
theorem traceTransaction_ok {fork : Fork} (config : TraceConfig) (env : BlockEnvironment fork)
    {index : Nat} {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    ∃ trace, traceTransaction config env index before tx = .ok trace := by
  unfold applyTransaction at h
  obtain ⟨included, hinc, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hout, -⟩ := bind_ok_iff.mp h
  have hrun := traceRun_output config env before.block included tx some {}
  rw [mapError_ok_iff.mp hout] at hrun
  obtain ⟨⟨out', tracer⟩, htr, -⟩ := map_ok_iff.mp hrun
  have hinc := mapError_ok_iff.mp hinc
  dsimp only at hinc
  exact ⟨.ofRun out' tracer, by
    simp only [traceTransaction, hinc, htr, bind, Except.bind, Except.mapError, pure,
      Except.pure]⟩

/-- From Byzantium, a receipt says its transaction succeeded exactly when its trace did not fail.

The receipt is the one that the body of the block adds for the transaction. -/
theorem traceTransaction_failed {fork : Fork} (config : TraceConfig)
    (env : BlockEnvironment fork) {index : Nat} {before after : BodyOutput fork}
    {tx : Transaction} {trace : TransactionTrace} (since : Fork.byzantium ≤ fork)
    (h : applyTransaction env index before tx = .ok after)
    (htrace : traceTransaction config env index before tx = .ok trace) :
    ∃ receipt, after.receipts = before.receipts ++ [(tx.type, receipt)] ∧
      receipt.outcome = .status since (!trace.failed) := by
  obtain ⟨trace', h', hr⟩ := traceTransaction_receipt config env since h
  rw [htrace] at h'
  cases h'
  exact hr

end EthLib.Execution.Rpc

module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Transactions.Observe
public import EthLib.Execution.Rpc.Trace

/-!
# Proofs: the opcode trace

The opcode logger changes nothing in the run of a transaction, for every configuration.

The trace of a transaction of a block exists whenever the block runs it, at every fork.

From Byzantium, the trace fails exactly when the receipt of the transaction says it failed.

An entry holds storage only at an SLOAD or SSTORE that runs, and a failed step changes no slot.
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

/-- The counter after one step of a frame: one more when the frame has code. -/
def countSteps {fork : Fork} {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter)
    (_ : Except EvmError (StepResult fork Meter)) (n : Nat) : Nat :=
  if evm.code.size = 0 then n else n + 1

/-- With no bound, the trace has one entry for each step of a frame with code.

That count of steps comes from the same run, observed by a counter. -/
theorem traceRun_count {fork : Fork} (config : TraceConfig) (unbounded : config.limit = 0)
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) :
    (fun p => (p.1, p.2.logs.size)) <$> traceRun config env block included tx precompiles lifted =
      (processTransactionWith (M := StateT Nat (Except EvmError))
        (fun evm result => modify (countSteps evm result)) env block included tx precompiles
        lifted).run 0 := by
  refine processTransactionWith_map (fun tracer : Tracer => tracer.logs.size)
    (fun evm result => Tracer.record config evm result) (fun evm result => countSteps evm result)
    (fun evm result tracer => ?_) env block included tx precompiles lifted {}
  by_cases empty : evm.code.size = 0 <;> simp [Tracer.record, countSteps, unbounded, empty]


/-- A step that touches a slot is an SLOAD or SSTORE that runs without an error. -/
theorem touchedSlot_isSome {fork : Fork} {Meter : Type} [GasMeter Meter] {op : Option Op}
    {evm : Evm fork Meter} {result : Except EvmError (StepResult fork Meter)}
    (h : (touchedSlot op evm result).isSome) :
    (op = some .sload ∨ op = some .sstore) ∧ stepError result = none := by
  unfold touchedSlot at h
  split at h
  · rename_i after
    split at h
    · rename_i hrun
      obtain ⟨hop, hnone⟩ := hrun
      refine ⟨hop, ?_⟩
      simp [stepError, Option.isNone_iff_eq_none.mp hnone]
    · simp at h
  · simp at h

/-- An entry of the logger holds storage only at an SLOAD or SSTORE step that runs.

A step that fails runs no opcode, so its entry has no storage. -/
theorem record_storage {fork : Fork} {Meter : Type} [GasMeter Meter] (config : TraceConfig)
    (evm : Evm fork Meter) (result : Except EvmError (StepResult fork Meter)) (tracer : Tracer) :
    (tracer.record config evm result).logs = tracer.logs ∨
      ∃ entry, (tracer.record config evm result).logs = tracer.logs.push entry ∧
        (entry.storage.isSome →
          (stepOp evm = some .sload ∨ stepOp evm = some .sstore) ∧ stepError result = none) := by
  unfold Tracer.record
  split
  · exact .inl rfl
  · refine .inr ⟨_, rfl, fun hs => touchedSlot_isSome (evm := evm) ?_⟩
    cases h : touchedSlot (stepOp evm) evm result <;> simp_all

/-- Leaving out the entry of one account keeps the entry of every other account. -/
private theorem lookup_filter_ne {β : Type} {a b : Address} (hab : a ≠ b) :
    ∀ (l : List (Address × β)), (l.filter (·.1 != b)).lookup a = l.lookup a
  | [] => rfl
  | (k, v) :: rest => by
    by_cases hk : k = b
    · subst hk
      have hka : (a == k) = false := by simpa using hab
      simp [List.filter, List.lookup, hka, lookup_filter_ne hab rest]
    · have hkb : (k != b) = true := by simpa using hk
      simp only [List.filter, hkb, List.lookup]
      split <;> simp [lookup_filter_ne hab rest]

/-- A step that fails leaves the slots that the logger has seen for each account as they were.

Only the order of the accounts may change. -/
theorem record_slots_of_stepError {fork : Fork} {Meter : Type} [GasMeter Meter]
    (config : TraceConfig) (evm : Evm fork Meter) (result : Except EvmError (StepResult fork Meter))
    (tracer : Tracer) (h : (stepError result).isSome) (a : Address) :
    ((tracer.record config evm result).slots.lookup a).getD [] =
      (tracer.slots.lookup a).getD [] := by
  -- A step that fails touches no slot.
  have ht : touchedSlot (stepOp evm) evm result = none := by
    cases hts : touchedSlot (stepOp evm) evm result with
    | none => rfl
    | some _ =>
      have := (touchedSlot_isSome (evm := evm) (op := stepOp evm) (by rw [hts]; rfl)).2
      rw [this] at h
      cases h
  unfold Tracer.record
  split
  · rfl
  · simp only [ht]
    split
    · by_cases ha : a = evm.message.currentTarget
      · subst ha
        simp [List.lookup]
      · have hne : (a == evm.message.currentTarget) = false := by simpa using ha
        simp [List.lookup, hne, lookup_filter_ne ha]
    · rfl

end EthLib.Execution.Rpc

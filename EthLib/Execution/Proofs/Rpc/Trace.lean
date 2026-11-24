module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Depth
public import EthLib.Execution.Rpc.Trace

/-!
# Proofs: the opcode trace

The opcode logger changes nothing in the run of a transaction, for every configuration.

A transaction or a block has a trace whenever it runs, at every fork.

An entry holds storage only at an SLOAD or SSTORE that runs, and a failed step changes no slot.

Each entry has a depth from 1 to 1025, since no frame is deeper than the limit.
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

/-! ## The trace of a block -/

/-- The fold of the block trace runs the transactions as the body does, and adds their traces.

The trace at each position is the trace of that transaction, after the transactions before it. -/
private theorem foldlM_trace {fork : Fork} (config : TraceConfig) (env : BlockEnvironment fork) :
    ∀ (pairs : List (Transaction × Nat)) (before after : BodyOutput fork)
      (traces traces' : List TransactionTrace),
      pairs.foldlM (fun (before, traces) (tx, index) => do
          let trace ← traceTransaction config env index before tx
          let after ← applyTransaction env index before tx
          return (after, traces ++ [trace])) (before, traces) = .ok (after, traces') →
      pairs.foldlM (fun before (tx, index) => applyTransaction env index before tx) before =
          .ok after ∧
        ∃ added, traces' = traces ++ added ∧ added.length = pairs.length ∧
          ∀ i trace, added[i]? = some trace → ∃ tx index mid, pairs[i]? = some (tx, index) ∧
            (pairs.take i).foldlM (fun before (tx, index) => applyTransaction env index before tx)
              before = .ok mid ∧
            traceTransaction config env index mid tx = .ok trace := by
  intro pairs
  induction pairs with
  | nil =>
    intro before after traces traces' h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, [], by simp, rfl, fun i trace h => by simp at h⟩
  | cons p rest ih =>
    intro before after traces traces' h
    obtain ⟨tx, index⟩ := p
    rw [List.foldlM_cons, bind_ok_iff] at h
    obtain ⟨⟨mid, ts⟩, first, h⟩ := h
    obtain ⟨trace, htrace, first⟩ := bind_ok_iff.mp first
    obtain ⟨next, hnext, first⟩ := bind_ok_iff.mp first
    cases first
    obtain ⟨hrest, added, rfl, hlen, hget⟩ := ih _ _ _ _ h
    refine ⟨?_, trace :: added, by simp, by simp [hlen], ?_⟩
    · rw [List.foldlM_cons]
      exact bind_ok_iff.mpr ⟨mid, hnext, hrest⟩
    · intro i t hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨tx, index, before, rfl, rfl, htrace⟩
      | succ i =>
        obtain ⟨tx', index', mid', hp, hf, ht⟩ := hget i t (by simpa using hi)
        refine ⟨tx', index', mid', by simpa using hp, ?_, ht⟩
        rw [List.take_succ_cons, List.foldlM_cons]
        exact bind_ok_iff.mpr ⟨mid, hnext, hf⟩

/-- A fold of the body that runs has a fold of the block trace, from any traces. -/
private theorem foldlM_trace_of_ok {fork : Fork} (config : TraceConfig)
    (env : BlockEnvironment fork) :
    ∀ (pairs : List (Transaction × Nat)) (before after : BodyOutput fork)
      (traces : List TransactionTrace),
      pairs.foldlM (fun before (tx, index) => applyTransaction env index before tx) before =
          .ok after →
      ∃ traces', pairs.foldlM (fun (before, traces) (tx, index) => do
          let trace ← traceTransaction config env index before tx
          let after ← applyTransaction env index before tx
          return (after, traces ++ [trace])) (before, traces) = .ok (after, traces') := by
  intro pairs
  induction pairs with
  | nil =>
    intro before after traces h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨traces, rfl⟩
  | cons p rest ih =>
    intro before after traces h
    obtain ⟨tx, index⟩ := p
    rw [List.foldlM_cons, bind_ok_iff] at h
    obtain ⟨next, hnext, h⟩ := h
    obtain ⟨trace, htrace⟩ := traceTransaction_ok config env hnext
    obtain ⟨traces', h'⟩ := ih next after (traces ++ [trace]) h
    refine ⟨traces', ?_⟩
    rw [List.foldlM_cons]
    refine bind_ok_iff.mpr ⟨_, ?_, h'⟩
    simp only [htrace, hnext, bind, Except.bind, pure, Except.pure]

/-- A block trace that succeeds has one entry per transaction.

Each entry is the trace of that transaction alone, after the transactions before it. -/
theorem traceBlock_eq_ok (config : TraceConfig) {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {traces : List TransactionTrace}
    (h : traceBlock config chain block = .ok traces) :
    traces.length = block.transactions.length ∧
      ∀ i (hi : i < traces.length),
        traceTransactionAt config chain block i = .ok (some traces[i]) := by
  unfold traceBlock at h
  obtain ⟨⟨env, body⟩, hstart, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨last, found⟩, hfold, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨-, added, htraces, hlen, hget⟩ := foldlM_trace config env _ _ _ _ _ hfold
  rw [List.nil_append] at htraces
  subst htraces
  rw [List.length_zipIdx] at hlen
  refine ⟨hlen, fun i hi => ?_⟩
  have hlt : i < block.transactions.length := hlen ▸ hi
  obtain ⟨tx, index, mid, hp, hf, ht⟩ := hget i _ (List.getElem?_eq_getElem hi)
  rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hlt] at hp
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, Nat.zero_add] at hp
  obtain ⟨rfl, rfl⟩ := hp
  have happly : applyTransactions env body (block.transactions.take i) = .ok mid := by
    unfold applyTransactions
    rw [zipIdx_take]
    exact hf
  simp only [traceTransactionAt, List.getElem?_eq_getElem hlt, hstart, happly, ht, bind,
    Except.bind, Functor.map, Except.map]

/-- A block whose transactions run after the start of its body has a trace. -/
theorem traceBlock_ok (config : TraceConfig) {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {env : BlockEnvironment fork} {body : BodyState}
    {output : BodyOutput fork} (start : bodyStart chain block = .ok (env, body))
    (h : applyTransactions env body block.transactions = .ok output) :
    ∃ traces, traceBlock config chain block = .ok traces := by
  have hfold : block.transactions.zipIdx.foldlM
      (fun before (tx, index) => applyTransaction env index before tx)
      ⟨body, .zero, 0, [], [], []⟩ = .ok output := h
  obtain ⟨traces, ht⟩ := foldlM_trace_of_ok config env _ _ _ [] hfold
  exact ⟨traces, bind_ok_iff.mpr ⟨_, start, bind_ok_iff.mpr ⟨_, ht, rfl⟩⟩⟩

/-- A block that passes its transition has a trace, with one entry per receipt of its body.

From Byzantium, each entry failed exactly when the receipt of its transaction says so. -/
theorem stateTransition_traceBlock (config : TraceConfig) {chain : BlockChain} {fork : Fork}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State.State}
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ traces result, traceBlock config chain block = .ok traces ∧
      runBody chain block = .ok result ∧ result.output.receipts.length = traces.length ∧
      ∀ (since : .byzantium ≤ fork) i (hi : i < traces.length),
        result.output.receipts[i]?.map (·.2.outcome) =
          some (.status since (!traces[i].failed)) := by
  obtain ⟨-, -, -, hashes, output, roots, hHashes, hBody, hRoots, -, -⟩ := stateTransition_eq_ok h
  obtain ⟨state, body, txs, hdao, hsys, htxs, hrec⟩ := applyBody_receipts hBody
  have hstart :
      bodyStart chain block = .ok (blockEnvironment chain.config hashes block.header, body) := by
    simp only [bodyStart, hHashes, hdao, hsys, bind, Except.bind, Except.mapError, pure,
      Except.pure]
  obtain ⟨traces, ht⟩ := traceBlock_ok config hstart htxs
  obtain ⟨hlen, hat⟩ := traceBlock_eq_ok config ht
  refine ⟨traces, ⟨output, roots⟩, ht, runBody_eq_ok.mpr ⟨hashes, hHashes, hBody, hRoots⟩, ?_, ?_⟩
  · rw [hrec, applyTransactions_receipts_length htxs, hlen]
  intro since i hi
  have hlt : i < block.transactions.length := hlen ▸ hi
  -- Each transaction extends the receipts of the body before it.
  obtain ⟨-, steps⟩ := applyTransactions_steps
    (fun a b : BodyOutput fork => a.receipts <+: b.receipts) (fun _ => List.prefix_refl _)
    (fun hab hbc => hab.trans hbc)
    (fun hstep => by
      obtain ⟨_, _, -, hr, -⟩ := applyTransaction_status since hstep
      exact ⟨_, hr.symm⟩) htxs
  obtain ⟨before, next, hb, hn, hpre⟩ := steps i hlt
  -- The trace of the block at `i` is the trace of that transaction after those before it.
  have htrace : traceTransaction config (blockEnvironment chain.config hashes block.header) i
      before block.transactions[i] = .ok traces[i] := by
    have hi' := hat i hi
    simp only [traceTransactionAt, List.getElem?_eq_getElem hlt, hstart, hb, bind, Except.bind,
      Functor.map, Except.map] at hi'
    split at hi' <;> simp_all
  obtain ⟨receipt, hnr, hout⟩ := traceTransaction_failed config _ since hn htrace
  have hbl : before.receipts.length = i := by
    rw [applyTransactions_receipts_length hb, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have hget : next.receipts[i]? = some (block.transactions[i].type, receipt) := by
    rw [hnr, List.getElem?_append_right (Nat.le_of_eq hbl), hbl, Nat.sub_self]
    rfl
  obtain ⟨rest, hrest⟩ := hpre
  show (output.receipts[i]?).map (·.2.outcome) = _
  rw [hrec, ← hrest, List.getElem?_append_left (by rw [hnr]; simp [hbl]), hget]
  simp [hout]

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

/-- A step of a frame within the depth limit adds only an entry of depth from 1 to 1025. -/
private theorem depth_mem_record {fork : Fork} {Meter : Type} [GasMeter Meter]
    (config : TraceConfig) (evm : Evm fork Meter) (result : Except EvmError (StepResult fork Meter))
    (tracer : Tracer) (within : evm.message.depth ≤ STACK_DEPTH_LIMIT)
    (kept : ∀ log ∈ tracer.logs, 1 ≤ log.depth ∧ log.depth ≤ STACK_DEPTH_LIMIT + 1) :
    ∀ log ∈ (Tracer.record config evm result tracer).logs,
      1 ≤ log.depth ∧ log.depth ≤ STACK_DEPTH_LIMIT + 1 := by
  unfold Tracer.record
  split
  · exact kept
  · intro log mem
    rcases Array.mem_push.mp mem with mem | rfl
    · exact kept log mem
    · exact ⟨Nat.le_add_left _ _, Nat.add_le_add_right within 1⟩

/-- Each entry of the opcode trace of a transaction has a depth from 1 to 1025.

The depth of an entry is that of its frame plus one. -/
theorem depth_mem_traceRun {fork : Fork} {config : TraceConfig} {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction}
    {precompiles : Address → Option Address} {lifted : LiftedRules}
    {output : TransactionOutput} {tracer : Tracer}
    (run : traceRun config env block included tx precompiles lifted = .ok (output, tracer)) :
    ∀ log ∈ tracer.logs, 1 ≤ log.depth ∧ log.depth ≤ STACK_DEPTH_LIMIT + 1 :=
  processTransactionWith_inv_of_depth_le
    (fun tracer : Tracer => ∀ log ∈ tracer.logs, 1 ≤ log.depth ∧ log.depth ≤ STACK_DEPTH_LIMIT + 1)
    (fun evm result tracer => Tracer.record config evm result tracer)
    (fun evm result tracer within kept => depth_mem_record config evm result tracer within kept)
    env block included tx precompiles lifted (fun _ mem => by simp at mem) run

end EthLib.Execution.Rpc

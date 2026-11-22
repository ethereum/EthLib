module

public import EthLib.Execution.Proofs.Blocks.SimulatedLogs
public import EthLib.Execution.Proofs.Rpc.SimulateBlocks

/-!
# Proofs: the transfer logs of `eth_simulateV1`

Without traced transfers, a call reports the logs of its receipt.

The blocks of a simulation, with their headers, do not depend on traced transfers.

Only the logs of the call results read that choice.

From Glamsterdam, the receipts already hold the transfer logs of EIP-7708.

So a block from Glamsterdam gives the same answer with transfers traced or not.

A block without transactions reports no call result, so it gives the same answer too.

So does a simulation whose blocks are each from Glamsterdam or without transactions.

It suffices that each block of the plan is from Glamsterdam or has no calls.

A gap block has no calls.

It also suffices that the active fork at the header of the base block is Glamsterdam or later.
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base (Fork bind_ok_iff mapError_ok_iff)
open EthLib.Execution.Blocks

/-- Without traced transfers, a call reports the logs of its receipt. -/
theorem callLogs_false {fork : Fork} (receipt : Receipt fork) (result : TransactionResult) :
    callLogs false receipt result = receipt.logs := rfl

/-- The first components of a prefix of a zip are the prefix of the first list. -/
private theorem map_fst_take_zip {α β γ : Type} (f : α → γ) :
    ∀ (n : Nat) (as : List α) (bs : List β), n ≤ bs.length →
      ((as.zip bs).take n).map (fun p => f p.1) = (as.take n).map f
  | 0, _, _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | n + 1, a :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, List.take_succ_cons, List.map_cons]
    rw [map_fst_take_zip f n as bs (by simpa using h)]
  | _ + 1, _ :: _, [], h => by simp at h

/-- Without traced transfers, a call reports the log objects of its receipt, numbered alike.

The logs of the receipts before it number those before its own. -/
theorem callLogInfos_false {b : SimulatedBlock} {index : Nat} (h : index ≤ b.results.length)
    (hash : Base.Hash32) (receipt : Receipt b.record.fork) (result : TransactionResult) :
    b.callLogInfos false index hash receipt result =
      b.record.logInfos index (b.record.logsBefore index) hash receipt.logs := by
  unfold SimulatedBlock.callLogInfos SimulatedBlock.firstLog BlockRecord.logsBefore
  congr 1
  simp only [callLogs, Bool.false_eq_true, ↓reduceIte]
  exact congrArg List.sum
    (map_fst_take_zip (fun x : _ × Receipt b.record.fork => x.2.logs.length) index _ _ h)

/-- The blocks of a simulation, with their headers, never read whether transfers are traced. -/
theorem simulateBlocks_traceTransfers (v : ChainView) (payload : SimulatePayload)
    (p : BlockParam) (choices : SimulateChoices) (trace : Bool) :
    v.simulateBlocks { payload with traceTransfers := trace } p choices =
      v.simulateBlocks payload p choices := rfl

/-- Two lists with equal images pair each element with one of the same image. -/
private theorem map_eq_of_mem_zip {α β γ : Type} {f : α → γ} {g : β → γ} :
    ∀ {as : List α} {bs : List β}, as.map f = bs.map g → ∀ a b, (a, b) ∈ as.zip bs → f a = g b
  | [], _, _, _, _, mem => by simp at mem
  | _ :: _, [], _, _, _, mem => by simp at mem
  | a' :: as, b' :: bs, same, a, b, mem => by
    simp only [List.map_cons, List.cons.injEq] at same
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at mem
    rcases mem with ⟨rfl, rfl⟩ | mem
    · exact same.1
    · exact map_eq_of_mem_zip same.2 a b mem

/-- When each result reports the logs of its receipt, traced transfers change no call result. -/
theorem callsJson_trace {b : SimulatedBlock}
    (h : b.results.map (·.simulatedLogs) = b.record.receipts.map (·.2.logs)) :
    b.callsJson true = b.callsJson false := by
  have first : ∀ index, b.firstLog true index = b.firstLog false index := by
    intro index
    unfold SimulatedBlock.firstLog
    congr 1
    apply List.map_congr_left
    rintro ⟨⟨_, receipt⟩, result⟩ mem
    have inner := List.mem_of_mem_take mem
    simp only [(map_eq_of_mem_zip h.symm _ _ inner).symm, callLogs, ↓reduceIte,
      Bool.false_eq_true]
  unfold SimulatedBlock.callsJson
  dsimp only
  congr 1
  apply EthLib.Base.mapM_congr
  intro ⟨⟨tx, ⟨type, receipt⟩, result⟩, index⟩ mem
  have inner := (List.of_mem_zip
    (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp mem))).2
  have same : callLogs true receipt result = callLogs false receipt result :=
    (map_eq_of_mem_zip h.symm (type, receipt) result inner).symm
  simp only [SimulatedBlock.callLogInfos, first, same]

/-- A simulated block from Glamsterdam is the same with transfers traced or not. -/
theorem simulateBlock_json_trace {chain chain' : BlockChain} {base : RecentBlock} {fork : Fork}
    {number time : Nat} {request : BlockStateCall} {validation : Bool} {budget budget' : Nat}
    {b : SimulatedBlock} (hfork : fork ≥ .glamsterdam)
    (h : simulateBlock chain base fork number time request validation budget =
      .ok (chain', budget', b)) (full validated : Bool) :
    b.json full validated true = b.json full validated false := by
  simp only [simulateBlock] at h
  split at h
  · simp only [bind_ok_iff, mapError_ok_iff] at h
    obtain ⟨-, -, _, -, -, -, -, -, -, -, _, -, res, hres, _, -, hEq⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨-, -, hb⟩ := hEq
    have same := callsJson_trace (b := b) (by rw [← hb]; exact runBody_simulatedLogs hfork hres)
    unfold SimulatedBlock.json
    rw [same]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A block without transactions has an empty list of call results, with transfers traced or not. -/
theorem callsJson_nil {b : SimulatedBlock} (h : b.record.block.transactions = []) (trace : Bool) :
    b.callsJson trace = .ok (.arr #[]) := by
  simp [SimulatedBlock.callsJson, h, pure, Except.pure, bind, Except.bind]

/-- A block without transactions is the same with transfers traced or not. -/
theorem json_trace_of_nil {b : SimulatedBlock} (h : b.record.block.transactions = [])
    (full validated : Bool) : b.json full validated true = b.json full validated false := by
  unfold SimulatedBlock.json
  rw [callsJson_nil h, callsJson_nil h]

/-- A simulation gives the same answer with transfers traced or not.

It needs each block that the simulation gives to be from Glamsterdam or to have no transactions.

A failed simulation gives the same error both ways. -/
theorem simulate_traceTransfers_of_glamsterdam_le_or_nil {v : ChainView}
    {payload : SimulatePayload} {p : BlockParam} {choices : SimulateChoices}
    (hfork : ∀ blocks, v.simulateBlocks payload p choices = .ok blocks →
      ∀ b ∈ blocks, .glamsterdam ≤ b.record.fork ∨ b.record.block.transactions = [])
    (trace : Bool) :
    v.simulate { payload with traceTransfers := trace } p choices =
      v.simulate payload p choices := by
  cases h : v.simulateBlocks payload p choices with
  | error e =>
    simp only [ChainView.simulate, simulateBlocks_traceTransfers, h, bind, Except.bind]
  | ok blocks =>
    have same : ∀ b ∈ blocks, ∀ t : Bool,
        b.json payload.returnFullTransactions payload.validation t =
          b.json payload.returnFullTransactions payload.validation false := by
      intro b hb t
      cases t
      · rfl
      · rcases hfork blocks h b hb with hFork | hNil
        · obtain ⟨_, _, _, _, _, _, _, _, hBlk⟩ := simulateBlocks_mem_exists h b hb
          exact simulateBlock_json_trace hFork hBlk _ _
        · exact json_trace_of_nil hNil _ _
    have agree := EthLib.Base.mapM_congr (xs := blocks)
      (φ := (·.json payload.returnFullTransactions payload.validation trace))
      (g := (·.json payload.returnFullTransactions payload.validation payload.traceTransfers))
      fun b hb => (same b hb trace).trans (same b hb payload.traceTransfers).symm
    simp only [ChainView.simulate, simulateBlocks_traceTransfers, h]
    exact congrArg (fun r : Except Serialization.JsonRpc.RpcError (List Lean.Json) =>
      r >>= fun l => pure (Lean.Json.arr l.toArray)) agree

/-- A simulation from Glamsterdam gives the same answer with transfers traced or not.

It needs each block that the simulation gives, gap blocks included, to be from Glamsterdam.

A failed simulation gives the same error both ways. -/
theorem simulate_traceTransfers {v : ChainView} {payload : SimulatePayload} {p : BlockParam}
    {choices : SimulateChoices}
    (hfork : ∀ blocks, v.simulateBlocks payload p choices = .ok blocks →
      ∀ b ∈ blocks, .glamsterdam ≤ b.record.fork) (trace : Bool) :
    v.simulate { payload with traceTransfers := trace } p choices =
      v.simulate payload p choices :=
  simulate_traceTransfers_of_glamsterdam_le_or_nil
    (fun blocks h b hb => .inl (hfork blocks h b hb)) trace

/-- A simulation gives the same answer with transfers traced or not.

It needs each block of the plan to be from Glamsterdam or to have no calls.

A gap block needs nothing, since it has no calls.

A failed simulation gives the same error both ways. -/
theorem simulate_traceTransfers_of_plan {v : ChainView} {payload : SimulatePayload}
    {p : BlockParam} {choices : SimulateChoices}
    (hCalls : ∀ plan, v.planSimulate payload p choices = .ok plan →
      ∀ x ∈ plan.blocks, .glamsterdam ≤ x.2 ∨ x.1.request.calls = []) (trace : Bool) :
    v.simulate { payload with traceTransfers := trace } p choices =
      v.simulate payload p choices :=
  simulate_traceTransfers_of_glamsterdam_le_or_nil
    (simulateBlocks_glamsterdam_le_or_nil hCalls) trace

/-- A simulation gives the same answer with transfers traced or not.

It needs the active fork at the header of the base block to be Glamsterdam or later.

A failed simulation gives the same error both ways. -/
theorem simulate_traceTransfers_of_base {v : ChainView} {payload : SimulatePayload}
    {p : BlockParam} {choices : SimulateChoices}
    (hBase : ∀ plan, v.planSimulate payload p choices = .ok plan →
      ∃ fork, v.config.activeFork plan.base.block.header.number
        plan.base.block.header.timestamp.toNat = some fork ∧ .glamsterdam ≤ fork)
    (trace : Bool) :
    v.simulate { payload with traceTransfers := trace } p choices =
      v.simulate payload p choices :=
  simulate_traceTransfers_of_plan (fun plan h x hx =>
    let ⟨_, hFork, hGlamsterdam⟩ := hBase plan h
    .inl (Nat.le_trans hGlamsterdam (planSimulate_fork_le h hFork x hx))) trace

end EthLib.Execution.Rpc

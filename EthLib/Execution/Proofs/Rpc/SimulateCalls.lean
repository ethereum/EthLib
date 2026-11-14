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

/-- Two monadic maps agree when their steps agree on every element of the list. -/
private theorem mapM_congr_mem {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    {f g : α → m β} :
    ∀ {xs : List α}, (∀ x, x ∈ xs → f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, same => by
    rw [List.mapM_cons, List.mapM_cons, same x List.mem_cons_self]
    congr 1
    funext y
    rw [mapM_congr_mem fun z hz => same z (List.mem_cons_of_mem x hz)]

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
  apply mapM_congr_mem
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
    obtain ⟨_, -, -, -, -, -, -, -, _, -, res, hres, _, -, hEq⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hEq
    obtain ⟨-, -, hb⟩ := hEq
    have same := callsJson_trace (b := b) (by rw [← hb]; exact runBody_simulatedLogs hfork hres)
    unfold SimulatedBlock.json
    rw [same]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end EthLib.Execution.Rpc

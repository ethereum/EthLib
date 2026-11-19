module

public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.SimulatedLogs

/-!
# Proofs: from Glamsterdam, a simulation reports the logs of each receipt

Each transaction of a body adds a receipt and a result.

From Glamsterdam, the result reports the logs of the receipt, and nothing more.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base (ChainConfig Fork bind_ok_iff foldlM_ok_invariant mapError_ok_iff)
open EthLib.Execution.Evm (BlockEnvironment)
open EthLib.Execution.State (BlockState)
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-- From Glamsterdam, a transaction adds a receipt and a result that reports its logs. -/
theorem applyTransaction_simulatedLogs {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction} {overrides : BodyOverrides}
    (hfork : fork ≥ .glamsterdam)
    (h : applyTransaction env index before tx overrides = .ok after) :
    ∃ (result : TransactionResult) (receipt : Receipt fork),
      after.results = before.results ++ [result] ∧
      after.receipts = before.receipts ++ [(tx.type, receipt)] ∧
      result.simulatedLogs = receipt.logs := by
  unfold applyTransaction at h
  obtain ⟨included, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, -, h⟩ := bind_ok_iff.mp h
  dsimp only at h
  have hb : .byzantium ≤ fork := Nat.le_trans (by decide) hfork
  simp only [hb, ↓reduceDIte] at h
  obtain ⟨_, hOutcome, h⟩ := bind_ok_iff.mp h
  cases hOutcome
  cases h
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp [makeReceipt,
    Transactions.simulatedLogs_processTransaction hfork (mapError_ok_iff.mp hOut)]

/-- From Glamsterdam, the result of each transaction of a body reports the logs of its receipt. -/
theorem applyTransactions_simulatedLogs {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {overrides : BodyOverrides} {output : BodyOutput fork}
    (hfork : fork ≥ .glamsterdam)
    (h : applyTransactions env body transactions overrides = .ok output) :
    output.results.map (·.simulatedLogs) = output.receipts.map (·.2.logs) := by
  refine foldlM_ok_invariant
    (fun b : BodyOutput fork => b.results.map (·.simulatedLogs) = b.receipts.map (·.2.logs))
    ?_ rfl h
  rintro before ⟨tx, index⟩ after hBefore hStep
  obtain ⟨result, receipt, hResults, hReceipts, hLogs⟩ := applyTransaction_simulatedLogs hfork hStep
  simp [hResults, hReceipts, hBefore, hLogs]

/-- A body gives the results and the receipts of the run of its transactions. -/
private theorem applyBody_results {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {overrides : BodyOverrides}
    {output : BlockOutput fork} (h : applyBody config env block start overrides = .ok output) :
    ∃ body txs, applyTransactions env body block.transactions overrides = .ok txs ∧
      output.results = txs.results ∧ output.receipts = txs.receipts := by
  unfold applyBody at h
  dsimp only at h
  obtain ⟨state, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨txs, hTxs, h⟩ := bind_ok_iff.mp h
  refine ⟨body, txs, hTxs, ?_⟩
  split at h
  · obtain ⟨tx, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨withdrawn, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨requested, requests⟩, -, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨rewarded, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨rfl, rfl⟩
  · obtain ⟨withdrawn, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨requested, requests⟩, -, h⟩ := bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨rewarded, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    cases h
    exact ⟨rfl, rfl⟩

/-- From Glamsterdam, each result of a block reports the logs of its receipt. -/
theorem runBody_simulatedLogs {chain : BlockChain} {block : Block fork Transaction}
    {overrides : BodyOverrides} {blobGasPrice : Option Nat} {result : BodyResult fork}
    (hfork : fork ≥ .glamsterdam) (h : runBody chain block overrides blobGasPrice = .ok result) :
    result.output.results.map (·.simulatedLogs) = result.output.receipts.map (·.2.logs) := by
  unfold runBody at h
  obtain ⟨hashes, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, hOutput, h⟩ := bind_ok_iff.mp h
  obtain ⟨roots, -, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨body, txs, hTxs, hResults, hReceipts⟩ := applyBody_results hOutput
  rw [hResults, hReceipts]
  exact applyTransactions_simulatedLogs hfork hTxs

end EthLib.Execution.Blocks

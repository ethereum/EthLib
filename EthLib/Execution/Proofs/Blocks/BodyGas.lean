module

public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: the gas counts of a block body

Before it runs a transaction, a block checks that the transaction fits in what the block has left.

At every fork, the blob gas of the body is at most the blob gas limit of the block.

Before Dencun that limit is 0, so a body that runs uses no blob gas.

Up to BPO5, the gas of the body is at most the gas limit of the block, and it counts no state gas.

[EIP-4844][e4844] asks for the bound on the blob gas.

[e4844]: https://eips.ethereum.org/EIPS/eip-4844#execution-layer-validation
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Transactions
open EthLib.Execution.Fees.BlobBaseFee (calculateTotalBlobGas)

variable {fork : Fork}

/-- A transaction that enters the body passes the inclusion check, and its run succeeds.

The counts of the block then grow by the counts of that run. -/
theorem applyTransaction_eq_ok {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    ∃ included out,
      checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .ok included ∧
      processTransaction env before.block included tx = .ok out ∧
      after.gas = before.gas.add out.blockGas := by
  unfold applyTransaction at h
  obtain ⟨included, hIncluded, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, -, h⟩ := bind_ok_iff.mp h
  refine ⟨included, out, mapError_ok_iff.mp hIncluded, mapError_ok_iff.mp hOut, ?_⟩
  dsimp only at h
  split at h <;> (obtain ⟨_, -, h⟩ := bind_ok_iff.mp h; cases h; rfl)

/-- The blob gas of a body that runs is at most the blob gas limit of its block, at every fork. -/
theorem applyTransactions_blob_le {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    output.gas.blob ≤ maxBlobGasPerBlock env := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork => before.gas.blob ≤
    maxBlobGasPerBlock env) ?_ (Nat.zero_le _) h
  rintro before ⟨tx, index⟩ after hBefore hStep
  obtain ⟨included, out, hIncluded, hOut, hGas⟩ := applyTransaction_eq_ok hStep
  have hFits := (checkInclusion_eq_ok_iff.mp hIncluded).2.2.2.2.2
  rw [hGas, BlockGas.add, processTransaction_blockGas_blob hOut]
  dsimp only
  omega

/-- Up to BPO5, the gas of a body that runs is at most the gas limit of its block. -/
theorem applyTransactions_execution_le_of_lt {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} (hlt : fork < .glamsterdam)
    (h : applyTransactions env body transactions = .ok output) :
    output.gas.execution ≤ env.gasLimit := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork =>
    before.gas.execution ≤ env.gasLimit) ?_ (Nat.zero_le _) h
  rintro before ⟨tx, index⟩ after hExecution hStep
  obtain ⟨included, out, hIncluded, hOut, hGas⟩ := applyTransaction_eq_ok hStep
  obtain ⟨-, -, hValid, hFits, -⟩ := checkInclusion_eq_ok_iff.mp hIncluded
  rw [executionCapacity_of_lt hlt] at hFits
  have hTx :=
    processTransaction_blockGas_execution_le_of_lt hlt (validateTransaction_ok hValid).2.1 hOut
  rw [hGas, BlockGas.add]
  dsimp only
  omega

/-- Up to BPO5, a body that runs counts no state gas. -/
theorem applyTransactions_state_of_lt {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} (hlt : fork < .glamsterdam)
    (h : applyTransactions env body transactions = .ok output) :
    output.gas.state = 0 := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork => before.gas.state = 0) ?_ rfl h
  rintro before ⟨tx, index⟩ after hState hStep
  obtain ⟨included, out, -, hOut, hGas⟩ := applyTransaction_eq_ok hStep
  have hTx := processTransaction_blockGas_state_of_lt hlt hOut
  rw [hGas, BlockGas.add]
  dsimp only
  omega

end EthLib.Execution.Blocks

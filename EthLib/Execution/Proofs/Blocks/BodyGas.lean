module

public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Proofs.Transactions.StateGas

/-!
# Proofs: the gas counts of a block body

Before it runs a transaction, a block checks that the transaction fits in what the block has left.

At every fork, the blob gas of the body is at most the blob gas limit of the block.

Before Dencun that limit is 0, so a body that runs uses no blob gas.

Up to BPO5, the gas of the body is at most the gas limit of the block, and it counts no state gas.

From Glamsterdam, the execution gas and the state gas of the body are each at most the gas limit.

So at every fork, each count of the body is within its bound.

[EIP-4844][e4844] asks for the bound on the blob gas.

[EIP-8037][e8037] counts the execution gas and the state gas apart.

[e4844]: https://eips.ethereum.org/EIPS/eip-4844#execution-layer-validation
[e8037]: https://eips.ethereum.org/EIPS/eip-8037#block-level-gas-accounting
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Transactions
open EthLib.Execution.Fees.BlobBaseFee (calculateTotalBlobGas)

variable {fork : Fork}

/-- The blob gas of a body that runs is at most the blob gas limit of its block, at every fork. -/
theorem applyTransactions_blob_le {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    output.gas.blob ≤ maxBlobGasPerBlock env := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork => before.gas.blob ≤
    maxBlobGasPerBlock env) ?_ (Nat.zero_le _) h
  rintro before ⟨tx, index⟩ after hBefore hStep
  obtain ⟨included, out, hIncluded, hOut, hGas, -⟩ := applyTransaction_eq_ok hStep
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
  obtain ⟨included, out, hIncluded, hOut, hGas, -⟩ := applyTransaction_eq_ok hStep
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
  obtain ⟨included, out, -, hOut, hGas, -⟩ := applyTransaction_eq_ok hStep
  have hTx := processTransaction_blockGas_state_of_lt hlt hOut
  rw [hGas, BlockGas.add]
  dsimp only
  omega

/-- From Glamsterdam, the execution gas of a body that runs is at most its block gas limit. -/
theorem applyTransactions_execution_le_of_glamsterdam {env : BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (hGlam : .glamsterdam ≤ fork) (h : applyTransactions env body transactions = .ok output) :
    output.gas.execution ≤ env.gasLimit := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork =>
    before.gas.execution ≤ env.gasLimit) ?_ (Nat.zero_le _) h
  rintro before ⟨tx, index⟩ after hExecution hStep
  obtain ⟨included, out, hIncluded, hOut, hGas, -⟩ := applyTransaction_eq_ok hStep
  obtain ⟨-, -, hValid, hFits, -⟩ := checkInclusion_eq_ok_iff.mp hIncluded
  have hTx := processTransaction_blockGas_execution_le_of_glamsterdam hGlam hValid hOut
  rw [hGas, BlockGas.add]
  dsimp only
  omega

/-- From Glamsterdam, the state gas of a body that runs is at most its block gas limit. -/
theorem applyTransactions_state_le_of_glamsterdam {env : BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (hGlam : .glamsterdam ≤ fork) (h : applyTransactions env body transactions = .ok output) :
    output.gas.state ≤ env.gasLimit := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork =>
    before.gas.state ≤ env.gasLimit) ?_ (Nat.zero_le _) h
  rintro before ⟨tx, index⟩ after hState hStep
  obtain ⟨included, out, hIncluded, hOut, hGas, -⟩ := applyTransaction_eq_ok hStep
  obtain ⟨-, -, -, -, hFits, -⟩ := checkInclusion_eq_ok_iff.mp hIncluded
  have hTx := processTransaction_blockGas_state_le_of_glamsterdam hGlam hOut
  have hFits := hFits hGlam
  rw [hGas, BlockGas.add]
  dsimp only
  omega

/-- Each count of a body that runs is within its bound, at every fork.

The execution gas and the state gas are at most the gas limit of the block.

The blob gas is at most the blob gas limit of the block. -/
theorem applyTransactions_gas_le {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    output.gas.execution ≤ env.gasLimit ∧ output.gas.state ≤ env.gasLimit ∧
      output.gas.blob ≤ maxBlobGasPerBlock env := by
  refine ⟨?_, ?_, applyTransactions_blob_le h⟩
  · by_cases hGlam : .glamsterdam ≤ fork
    · exact applyTransactions_execution_le_of_glamsterdam hGlam h
    · exact applyTransactions_execution_le_of_lt (Nat.lt_of_not_le hGlam) h
  · by_cases hGlam : .glamsterdam ≤ fork
    · exact applyTransactions_state_le_of_glamsterdam hGlam h
    · rw [applyTransactions_state_of_lt (Nat.lt_of_not_le hGlam) h]
      exact Nat.zero_le _

end EthLib.Execution.Blocks

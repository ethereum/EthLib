module

public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Proofs.Transactions.StateGas
import EthLib.Execution.Proofs.Fees.GasLimit

/-!
# Proofs: the gas counts of a block body

Before it runs a transaction, a block checks that the transaction fits in what the block has left.

At every fork, the blob gas of the body is at most the blob gas limit of the block.

Before Dencun that limit is 0, so a body that runs uses no blob gas.

Up to BPO5, the gas of the body is at most the gas limit of the block, and it counts no state gas.

From Glamsterdam, the execution gas and the state gas of the body are each at most the gas limit.

So at every fork, each count of the body is within its bound.

Each transaction of a body that runs has a gas limit of at most the gas limit of the block.

Up to BPO5, the cumulative gas of each receipt is at most that gas limit too.

Up to BPO5, a block that passes its transition then records both below `2^64`.

That result needs the gas limit of the parent below `2^63`.

At every fork, each receipt records at most the execution gas plus the state gas of the body.

So at every fork, a block that passes its transition records its gas in 64 bits.

That result needs the gas limit of the parent below `2^62`.

Twice the gas limit of the block then stays below `2^64`.

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

/-- Up to BPO5, the gas of a body that runs is the gas used that its receipts add up.

That gas used is counted after the refunds. -/
theorem applyTransactions_execution_of_lt {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork} (hlt : fork < .glamsterdam)
    (h : applyTransactions env body transactions = .ok output) :
    output.gas.execution = output.cumulativeGasUsed := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork =>
    before.gas.execution = before.cumulativeGasUsed) ?_ rfl h
  rintro before ⟨tx, index⟩ after hExecution hStep
  obtain ⟨included, out, -, hOut, hGas, hCumulative, -⟩ := applyTransaction_eq_ok hStep
  have hTx := processTransaction_blockGas_execution_of_lt hlt hOut
  rw [hGas, hCumulative, BlockGas.add]
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

/-! ## The gas that the receipts record -/

/-- Each transaction of a body that runs has a gas limit of at most the gas limit of its block. -/
theorem applyTransactions_txGas_le {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    ∀ tx ∈ transactions, tx.gas.toNat ≤ env.gasLimit := by
  intro tx htx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htx
  obtain ⟨-, hSteps⟩ := applyTransactions_steps (fun _ _ => True) (fun _ => trivial)
    (fun _ _ => trivial) (fun _ => trivial) h
  obtain ⟨before, next, -, hNext, -⟩ := hSteps i hi
  obtain ⟨included, out, hIncluded, -⟩ := applyTransaction_eq_ok hNext
  obtain ⟨-, -, -, hFits, hState, -⟩ := checkInclusion_eq_ok_iff.mp hIncluded
  by_cases hGlam : .glamsterdam ≤ fork
  · have := hState hGlam
    omega
  · rw [executionCapacity_of_lt (Nat.lt_of_not_le hGlam)] at hFits
    omega

/-- Up to BPO5, each receipt of a body that runs records at most the gas limit of its block. -/
theorem applyTransactions_cumulativeGasUsed_le_of_lt {env : BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (hlt : fork < .glamsterdam) (h : applyTransactions env body transactions = .ok output) :
    ∀ p ∈ output.receipts, p.2.cumulativeGasUsed ≤ env.gasLimit := by
  intro p hp
  have hReceipt := (applyTransactions_receipts h).2.2 p hp
  rw [← applyTransactions_execution_of_lt hlt h] at hReceipt
  exact Nat.le_trans hReceipt (applyTransactions_execution_le_of_lt hlt h)

/-- A body that runs records in each receipt at most its execution gas plus its state gas.

It holds at every fork. -/
theorem applyTransactions_cumulativeGasUsed_le_add {env : BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    ∀ p ∈ output.receipts, p.2.cumulativeGasUsed ≤ output.gas.execution + output.gas.state := by
  have hSum : output.cumulativeGasUsed ≤ output.gas.execution + output.gas.state := by
    refine foldlM_ok_invariant (fun before : BodyOutput fork =>
      before.cumulativeGasUsed ≤ before.gas.execution + before.gas.state) ?_ (Nat.zero_le _) h
    rintro before ⟨tx, index⟩ after hBefore hStep
    obtain ⟨included, out, -, hOut, hGas, hCumulative, -⟩ := applyTransaction_eq_ok hStep
    have hTx := processTransaction_gasUsed_le_add hOut
    rw [hGas, hCumulative, BlockGas.add]
    dsimp only
    omega
  intro p hp
  exact Nat.le_trans ((applyTransactions_receipts h).2.2 p hp) hSum

/-- A block that passes its transition has a parent, the last recent block.

The gas limit rule keeps 1024 times its gas limit below 1025 times that of the parent.

That gas limit of the parent is the one that the rule reads, doubled at the first London block. -/
theorem stateTransition_gasLimit_mul_lt {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State.State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ parent, chain.recent.getLast? = some parent ∧ 1024 * block.header.gasLimit <
      1025 * Fees.GasLimit.parentGasLimitForCheck parent.fork fork parent.header.gasLimit := by
  obtain ⟨-, -, hCheck, -⟩ := stateTransition_eq_ok h
  obtain ⟨parent, hLast, hFork, hHead⟩ := checkBlock_checkHeader hCheck
  obtain ⟨-, -, -, -, hLimit, -⟩ := checkHeader_eq_ok_iff.mp hHead
  exact ⟨parent, hLast, Fees.GasLimit.mul_lt_of_checkGasLimit hLimit⟩

/-- Up to BPO5, a block that passes its transition records its gas in 64 bits.

Each of its transactions has a gas limit below `2^64`.

Each receipt that its body gives has a cumulative gas below `2^64`.

It needs the gas limit of the parent, the last recent block, below `2^63`.

That gas limit is the one that the rule of the gas limit reads, doubled at the first London block.
-/
theorem stateTransition_gas_lt_of_lt {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State.State} (hlt : fork < .glamsterdam)
    (h : stateTransition chain block checkSeal = .ok post)
    (hParent : ∀ parent, chain.recent.getLast? = some parent →
      Fees.GasLimit.parentGasLimitForCheck parent.fork fork parent.header.gasLimit < 2 ^ 63) :
    (∀ tx ∈ block.transactions, tx.gas.toNat < 2 ^ 64) ∧
      ∃ hashes output, recentHashes chain.recent = .ok hashes ∧
        applyBody chain.config (blockEnvironment chain.config hashes block.header) block
          ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
        ∀ p ∈ output.receipts, p.2.cumulativeGasUsed < 2 ^ 64 := by
  obtain ⟨-, -, -, hashes, output, roots, hHashes, hApply, -⟩ := stateTransition_eq_ok h
  obtain ⟨parent, hLast, hRule⟩ := stateTransition_gasLimit_mul_lt h
  have hGas : block.header.gasLimit < 2 ^ 64 := by
    have hBound := hParent parent hLast
    omega
  obtain ⟨state, body, txs, -, -, hTxs, hReceipts⟩ := applyBody_receipts hApply
  refine ⟨fun tx htx => Nat.lt_of_le_of_lt (applyTransactions_txGas_le hTxs tx htx) hGas,
    hashes, output, hHashes, hApply, fun p hp => ?_⟩
  rw [hReceipts] at hp
  exact Nat.lt_of_le_of_lt (applyTransactions_cumulativeGasUsed_le_of_lt hlt hTxs p hp) hGas

/-- A block that passes its transition records its gas in 64 bits, at every fork.

Each of its transactions has a gas limit below `2^64`.

Each receipt that its body gives has a cumulative gas below `2^64`.

It needs the gas limit of the parent, the last recent block, below `2^62`.

That gas limit is the one that the rule of the gas limit reads, doubled at the first London block.
-/
theorem stateTransition_gas_lt {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State.State} (h : stateTransition chain block checkSeal = .ok post)
    (hParent : ∀ parent, chain.recent.getLast? = some parent →
      Fees.GasLimit.parentGasLimitForCheck parent.fork fork parent.header.gasLimit < 2 ^ 62) :
    (∀ tx ∈ block.transactions, tx.gas.toNat < 2 ^ 64) ∧
      ∃ hashes output, recentHashes chain.recent = .ok hashes ∧
        applyBody chain.config (blockEnvironment chain.config hashes block.header) block
          ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
        ∀ p ∈ output.receipts, p.2.cumulativeGasUsed < 2 ^ 64 := by
  obtain ⟨-, -, -, hashes, output, roots, hHashes, hApply, -⟩ := stateTransition_eq_ok h
  obtain ⟨parent, hLast, hRule⟩ := stateTransition_gasLimit_mul_lt h
  have hGas : block.header.gasLimit < 2 ^ 63 := by
    have hBound := hParent parent hLast
    omega
  obtain ⟨state, body, txs, -, -, hTxs, hReceipts⟩ := applyBody_receipts hApply
  obtain ⟨hExecution, hState, -⟩ := applyTransactions_gas_le hTxs
  have hEnv : (blockEnvironment chain.config hashes block.header).gasLimit =
      block.header.gasLimit := rfl
  refine ⟨fun tx htx => ?_, hashes, output, hHashes, hApply, fun p hp => ?_⟩
  · have hTx := applyTransactions_txGas_le hTxs tx htx
    omega
  · rw [hReceipts] at hp
    have hReceipt := applyTransactions_cumulativeGasUsed_le_add hTxs p hp
    omega

end EthLib.Execution.Blocks

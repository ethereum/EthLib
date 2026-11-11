module

public import EthLib.Execution.Proofs.Blocks.Burn

/-!
# Proofs: the supply bound of a block and the Glamsterdam equality

The exact block supply equation counts created wei, burned fees and other losses.

Those losses are the surviving burns of SELFDESTRUCT and the balances that transactions delete.

Those losses are never negative, so dropping them gives a bound at every fork.

So a block leaves at most the supply before it, plus its created wei, minus its burned fees.

From Glamsterdam, every surviving burn and every deleted balance is 0, by [EIP-8246][e8246].

So the supply after the block plus its burned fees equals the supply before plus its created wei.

The burned fees are the base fee per gas times the gas used after the refunds.

They add the base fee per blob gas times the blob gas, by [EIP-1559][e1559] and [EIP-4844][e4844].

Before London the base fee per gas is 0, and before Dencun the base fee per blob gas is 0.

Before Glamsterdam, the header gives both: its gas used and its blob gas used.

[e1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[e4844]: https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
[e8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork}

/-! ## The fees that the header states -/

/-- The fees that a header states, in wei, at the base fees of the environment `env`.

It is the gas used at the base fee per gas, plus the blob gas used at the base fee per blob gas.

Before Dencun the header has no blob gas used, which counts as 0. -/
def headerBurnedWei (env : BlockEnvironment fork) (header : Header fork) : Nat :=
  header.gasUsed * baseFeeOf env +
    (if h : .dencun ≤ fork then (header.blobGasUsed h).toNat else 0) * blobGasPriceOf env

/-! ## The body -/

/-- After the body of a block, the supply plus its burned fees is at most the supply before.

To the supply before, it adds the ether that the block creates.

From Glamsterdam, the two are equal.

Before Paris, the block must have at most two ommers, as the checks of the block enforce. -/
theorem applyBody_supply {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hOmmers : fork < .paris → block.ommers.length ≤ 2)
    (h : applyBody config env block start = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput ≤
        (TransactionState.ofBlock start).supply + createdWei block ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock output.block).supply +
        burnedWei env output.toBodyOutput = (TransactionState.ofBlock start).supply +
          createdWei block) := by
  obtain ⟨losses, certificate⟩ := applyBody_bodyBurns h
  have hSupply := certificate.supply_eq hOmmers
  refine ⟨by omega, fun hFork => ?_⟩
  have hZero := certificate.total_eq_zero_of_glamsterdam hFork
  omega

/-- After the body of a block, the supply plus its burned fees is at most the supply before.

To the supply before, it adds the ether that the block creates.

The bound holds at every fork that the transition runs.

Before Paris, the block must have at most two ommers, as the checks of the block enforce. -/
theorem applyBody_supply_le {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hOmmers : fork < .paris → block.ommers.length ≤ 2)
    (h : applyBody config env block start = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput ≤
      (TransactionState.ofBlock start).supply + createdWei block :=
  (applyBody_supply hOmmers h).1

/-- From Glamsterdam, a block body adds the ether it creates and removes the fees it burns. -/
theorem applyBody_supply_of_glamsterdam {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hFork : .glamsterdam ≤ fork) (h : applyBody config env block start = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput =
      (TransactionState.ofBlock start).supply + createdWei block :=
  (applyBody_supply (fun hlt => absurd (Nat.lt_of_lt_of_le hlt (by decide)) (Nat.not_lt.mpr hFork))
    h).2 hFork

/-! ## The state transition -/

/-- After a block that passes the transition, the supply plus its burned fees is at most before.

To the supply before, it adds the ether that the block creates.

The bound holds at every fork that the transition runs, which fails from Hegotá.

The fees come from the body that the transition runs. -/
theorem stateTransition_supply_le {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      post.supply + burnedWei (blockEnvironment chain.config hashes block.header)
          output.toBodyOutput ≤ chain.state.supply + createdWei block := by
  obtain ⟨hashes, output, _, hHashes, hOutput, -, hSupply⟩ := stateTransition_supply_eq h
  exact ⟨hashes, output, hHashes, hOutput, by omega⟩

/-- From Glamsterdam, a block that passes the transition changes the supply by exactly its terms.

It adds its created ether and removes its burned fees.

The fees come from the body that the transition runs. -/
theorem stateTransition_supply_of_glamsterdam {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : .glamsterdam ≤ fork) (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      post.supply + burnedWei (blockEnvironment chain.config hashes block.header)
          output.toBodyOutput = chain.state.supply + createdWei block := by
  obtain ⟨hashes, output, _, hHashes, hOutput, certificate, hSupply⟩ :=
    stateTransition_supply_eq h
  have hZero := certificate.total_eq_zero_of_glamsterdam hFork
  exact ⟨hashes, output, hHashes, hOutput, by omega⟩

/-- Before Glamsterdam, a block lowers the supply by at least the fees that its header states.

Those are its gas used at the base fee per gas, and its blob gas used at the base fee per blob gas.

It also adds the ether that it creates.

The block must pass the transition. -/
theorem stateTransition_supply_le_of_lt_glamsterdam {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : fork < .glamsterdam) (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes, recentHashes chain.recent = .ok hashes ∧
      post.supply + headerBurnedWei (blockEnvironment chain.config hashes block.header)
          block.header ≤ chain.state.supply + createdWei block := by
  obtain ⟨hashes, output, hHashes, hOutput, hle⟩ := stateTransition_supply_le h
  obtain ⟨-, -, -, hashes', output', _, hHashes', hOutput', -, hChecks, -⟩ :=
    stateTransition_eq_ok h
  cases Except.ok.inj (hHashes'.symm.trans hHashes)
  cases Except.ok.inj (hOutput'.symm.trans hOutput)
  refine ⟨hashes, hHashes, ?_⟩
  suffices burned : burnedWei (blockEnvironment chain.config hashes block.header)
      output.toBodyOutput = headerBurnedWei (blockEnvironment chain.config hashes block.header)
        block.header by
    rwa [← burned]
  -- The gas of the body is the gas used that its receipts add up, with no state gas.
  obtain ⟨-, _, txs, -, -, -, -, hTxs, -, -, -, -, -, -, hGas, hCumulative⟩ :=
    applyBody_eq_ok hOutput
  have hExecution := applyTransactions_execution_of_lt hFork hTxs
  have hState := applyTransactions_state_of_lt hFork hTxs
  have hUsed : output.cumulativeGasUsed = block.header.gasUsed := by
    rw [← (of_outputChecks hChecks).1, BlockGas.gasUsed, hGas, hState, hExecution, hCumulative]
    exact (Nat.max_eq_left (Nat.zero_le _)).symm
  unfold burnedWei headerBurnedWei
  rw [hUsed]
  split
  · rename_i hDencun
    rw [blobGasUsed_of_outputChecks hDencun hChecks]
  · rename_i hDencun
    simp only [blobGasPriceOf, hDencun, ↓reduceDIte, Nat.mul_zero]

end EthLib.Execution.Blocks

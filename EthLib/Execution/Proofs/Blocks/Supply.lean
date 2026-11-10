module

public import EthLib.Execution.Proofs.Blocks.BodyGas
public import EthLib.Execution.Proofs.Blocks.Ommers
public import EthLib.Execution.Proofs.Blocks.Rewards
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.Withdrawal
public import EthLib.Execution.Proofs.Transactions.Supply

/-!
# Proofs: the ether that a block creates and burns

The supply of a state is the sum of its balances, and a block changes it step by step.

Before Paris, the DAO transfer at the first block of the DAO Fork moves ether, and keeps the supply.

The system calls keep or lower the supply, as a message does.

Each transaction lowers it by at least its burned fees, by the theorem on transactions.

From Shapella, each withdrawal creates its amount in Gwei times `10^9`, by [EIP-4895][e4895].

Before Paris, the rewards of the beneficiary and of the ommers create ether.

Section 11.3 of the Yellow Paper, Berlin version, sets them: [`Paper.tex`][yp].

[EIP-3675][e3675] removes them from Paris.

So a block leaves at most the supply before it, plus its created ether, minus its burned fees.

From Glamsterdam it is exactly that, since nothing burns ether beyond the fees there.

Before Glamsterdam, SELFDESTRUCT and the deletions can burn more, so only the bound holds.

The burned fees are the base fee per gas times the gas used after the refunds.

They add the base fee per blob gas times the blob gas, by [EIP-1559][e1559] and [EIP-4844][e4844].

Before Glamsterdam, the header gives both: its gas used and its blob gas used.

[e1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[e3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#specification
[e4844]: https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
[e4895]: https://eips.ethereum.org/EIPS/eip-4895#specification
[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork}

/-! ## What a block creates and burns -/

/-- The wei that withdrawals create: the sum of their amounts in Gwei, times `10^9`. -/
def withdrawnWei (withdrawals : List Withdrawal) : Nat :=
  (withdrawals.map fun w => w.amount.toNat * GWEI_TO_WEI).sum

/-- The wei that the rewards of a block at `number` create, at `fork`.

Each ommer comes with its beneficiary and its number.

Before Paris, it is the reward of the beneficiary plus the reward of each ommer.

From Paris, it is 0. -/
def rewardWei (fork : Fork) (number : Nat) (ommers : List (Address × Nat)) : Nat :=
  if .paris ≤ fork then 0
  else minerReward fork ommers.length + (ommers.map fun o => ommerReward fork (number - o.2)).sum

/-- The wei that a block creates: its withdrawals from Shapella, and its rewards before Paris. -/
def createdWei (block : Block fork Transaction) : Nat :=
  (if h : .shapella ≤ fork then withdrawnWei (block.withdrawals h) else 0) +
    rewardWei fork block.header.number
      (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number))

/-- The fees that the transactions of a body burn, in wei, from what the body gave.

It is the base fee per gas times their gas used after the refunds.

It adds the base fee per blob gas times their blob gas. -/
def burnedWei (env : BlockEnvironment fork) (output : BodyOutput fork) : Nat :=
  output.cumulativeGasUsed * baseFeeOf env + output.gas.blob * blobGasPriceOf env

/-- The fees that a block burns, in wei, from its header, in the environment `env` of the block.

It is the gas used at the base fee per gas, plus the blob gas used at the base fee per blob gas.

Before Dencun the blob gas used is 0. -/
def headerBurnedWei (env : BlockEnvironment fork) (header : Header fork) : Nat :=
  header.gasUsed * baseFeeOf env +
    (if h : .dencun ≤ fork then (header.blobGasUsed h).toNat else 0) * blobGasPriceOf env

/-! ## The steps on the block state -/

/-- A step that runs on a block state as a transaction leaves the supply of its end state. -/
theorem supply_onBlock {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (h : onBlock block step = .ok block') :
    ∃ tx, step (.ofBlock block) = .ok tx ∧
      (TransactionState.ofBlock block').supply = tx.supply := by
  unfold onBlock at h
  obtain ⟨tx, htx, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨tx, mapError_ok_iff.mp htx, TransactionState.supply_incorporateTxIntoBlock tx⟩

/-- A call that joins the body leaves the supply of its end state. -/
theorem BodyState.supply_join {body body' : BodyState} {tx : TransactionState}
    (h : body.join tx = .ok body') : (TransactionState.ofBlock body'.block).supply = tx.supply := by
  unfold BodyState.join at h
  obtain ⟨builder, -, h⟩ := bind_ok_iff.mp h
  cases h
  exact TransactionState.supply_incorporateTxIntoBlock tx

/-- The DAO transfer moves ether, and so keeps the supply. -/
theorem supply_applyDaoFork {tx tx' : TransactionState} (h : applyDaoFork fork tx = .ok tx') :
    tx'.supply = tx.supply :=
  foldlM_ok_invariant (fun mid : TransactionState => mid.supply = tx.supply)
    (fun _ _ _ hmid hstep => (TransactionState.supply_moveEther hstep).trans hmid) rfl h

/-- The DAO transfer of a block keeps the supply, whether it runs or not. -/
theorem supply_daoTransfer {config : ChainConfig} {number : Nat} {start state : BlockState}
    (h : daoTransfer config fork number start = .ok state) :
    (TransactionState.ofBlock state).supply = (TransactionState.ofBlock start).supply := by
  unfold daoTransfer at h
  split at h
  · obtain ⟨tx, htx, hsupply⟩ := supply_onBlock h
    rw [hsupply, supply_applyDaoFork htx]
  · cases h
    rfl

/-- A system call keeps or lowers the supply of its block state, and keeps it from Glamsterdam. -/
theorem supply_systemCall {env : BlockEnvironment fork} {block : BlockState} {target : Address}
    {data : ByteArray} {out : SystemCallOutput} (h : systemCall env block target data = .ok out) :
    out.state.supply ≤ (TransactionState.ofBlock block).supply ∧
      (.glamsterdam ≤ fork → out.state.supply = (TransactionState.ofBlock block).supply) := by
  unfold systemCall at h
  dsimp only at h
  split at h <;>
  · obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    have hle := supplyLe_processMessageCall hcall
    exact ⟨hle.1, fun hglam => hle.2.2 (.inl hglam)⟩

/-- A system call that joins the body keeps or lowers the supply, and keeps it from Glamsterdam. -/
theorem supply_systemCall_join {env : BlockEnvironment fork} {body body' : BodyState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (hcall : systemCall env body.block target data = .ok out)
    (hjoin : body.join out.state = .ok body') :
    (TransactionState.ofBlock body'.block).supply ≤ (TransactionState.ofBlock body.block).supply ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock body'.block).supply =
        (TransactionState.ofBlock body.block).supply) := by
  rw [BodyState.supply_join hjoin]
  exact supply_systemCall hcall

/-- The system calls at the start of a block keep or lower the supply, and keep it from Glamsterdam.
-/
theorem supply_startSystemCalls {env : BlockEnvironment fork} {parentHash : Hash32}
    {body body' : BodyState} (h : startSystemCalls env parentHash body = .ok body') :
    (TransactionState.ofBlock body'.block).supply ≤ (TransactionState.ofBlock body.block).supply ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock body'.block).supply =
        (TransactionState.ofBlock body.block).supply) := by
  -- The second call, from the body after the first.
  have second : ∀ mid : BodyState,
      (if Fork.pectra ≤ fork then do
          let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
          (mid.join out.state).mapError EvmError.state
        else pure mid) = .ok body' →
      (TransactionState.ofBlock body'.block).supply ≤ (TransactionState.ofBlock mid.block).supply ∧
        (.glamsterdam ≤ fork → (TransactionState.ofBlock body'.block).supply =
          (TransactionState.ofBlock mid.block).supply) := by
    intro mid h
    split at h
    · obtain ⟨out, hout, h⟩ := bind_ok_iff.mp h
      exact supply_systemCall_join hout (mapError_ok_iff.mp h)
    · cases h
      exact ⟨Nat.le_refl _, fun _ => rfl⟩
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · obtain ⟨out, hout, h⟩ := bind_ok_iff.mp h
    obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    obtain ⟨le1, eq1⟩ := supply_systemCall_join hout (mapError_ok_iff.mp hmid)
    obtain ⟨le2, eq2⟩ := second mid h
    exact ⟨Nat.le_trans le2 le1, fun hglam => (eq2 hglam).trans (eq1 hglam)⟩
  · obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    cases hmid
    exact second _ h

/-- The requests of a block keep or lower the supply, and keep it from Glamsterdam. -/
theorem supply_blockRequests {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} {logs : List Log} {result : BodyState × List ByteArray}
    (h : blockRequests depositContract env body logs = .ok result) :
    (TransactionState.ofBlock result.1.block).supply ≤
        (TransactionState.ofBlock body.block).supply ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock result.1.block).supply =
        (TransactionState.ofBlock body.block).supply) := by
  let P : BodyState × List ByteArray → Prop := fun state =>
    (TransactionState.ofBlock state.1.block).supply ≤ (TransactionState.ofBlock body.block).supply ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock state.1.block).supply =
        (TransactionState.ofBlock body.block).supply)
  have start : P (body, []) := ⟨Nat.le_refl _, fun _ => rfl⟩
  have reads : ∀ {read : BodyState × List ByteArray}, readRequests env body = .ok read →
      P read := by
    intro read hread
    unfold readRequests at hread
    split at hread
    · refine foldlM_ok_invariant P ?_ start hread
      rintro state contract next ⟨hle, heq⟩ hstep
      unfold readRequest at hstep
      obtain ⟨out, hout, hstep⟩ := bind_ok_iff.mp hstep
      obtain ⟨joined, hjoin, hstep⟩ := bind_ok_iff.mp hstep
      cases hstep
      obtain ⟨le1, eq1⟩ :=
        supply_systemCall_join (checkedSystemCall_ok hout).2.1 (mapError_ok_iff.mp hjoin)
      exact ⟨Nat.le_trans le1 hle, fun hglam => (eq1 hglam).trans (heq hglam)⟩
    · cases hread
      exact start
  unfold blockRequests at h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨read, hread, h⟩ := bind_ok_iff.mp h
    cases h
    have hrest := reads hread
    exact hrest
  · cases h
    exact start

/-- The withdrawals add the wei they withdraw to the supply. -/
theorem supply_withdrawalState {block : BlockState} {withdrawals : List Withdrawal}
    {tx : TransactionState} (h : withdrawalState fork block withdrawals = .ok tx) :
    tx.supply = (TransactionState.ofBlock block).supply + withdrawnWei withdrawals := by
  rw [TransactionState.supply_foldlM_createEther _ _ withdrawals h]
  simp only [toNat_withdrawalWei, withdrawnWei]

/-- The rewards add the wei they reward to the supply.

Before Paris, the block must have at most two ommers, as the checks of the block ensure. -/
theorem supply_payRewards {tx tx' : TransactionState} {coinbase : Address} {number : Nat}
    {ommers : List (Address × Nat)} (hn : fork < .paris → ommers.length ≤ 2)
    (h : payRewards fork tx coinbase number ommers = .ok tx') :
    tx'.supply = tx.supply + rewardWei fork number ommers := by
  unfold payRewards at h
  unfold rewardWei
  split at h
  · rename_i hparis
    cases h
    simp [hparis]
  · rename_i hparis
    simp only [hparis, ↓reduceIte]
    obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    rw [TransactionState.supply_foldlM_createEther Prod.fst
        (fun o => BitVec.ofNat 256 (ommerReward fork (number - o.2))) ommers h,
      TransactionState.supply_createEther hmid, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (minerReward_lt (hn (Nat.lt_of_not_le hparis)))]
    simp only [toNat_ommerReward, Nat.add_assoc]

/-! ## The transactions -/

/-- The transactions of a body lower the supply by at least their burned fees, at every fork.

From Glamsterdam, they lower it by exactly those fees. -/
theorem applyTransactions_supply {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output ≤
        (TransactionState.ofBlock body.block).supply ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock output.block).supply +
        burnedWei env output = (TransactionState.ofBlock body.block).supply) := by
  refine foldlM_ok_invariant (fun before : BodyOutput fork =>
    (TransactionState.ofBlock before.block).supply + burnedWei env before ≤
        (TransactionState.ofBlock body.block).supply ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock before.block).supply +
        burnedWei env before = (TransactionState.ofBlock body.block).supply)) ?_
    ⟨by simp [burnedWei, BlockGas.zero, BodyOutput.block], fun _ => by
      simp [burnedWei, BlockGas.zero, BodyOutput.block]⟩ h
  rintro before ⟨tx, index⟩ after ⟨hle, heq⟩ hStep
  obtain ⟨included, out, hIncluded, hOut, hGas, hCumulative, hJoin⟩ := applyTransaction_eq_ok hStep
  obtain ⟨-, -, hValid, -, -, -, -, hFee, -⟩ := checkInclusion_eq_ok_iff.mp hIncluded
  have hTx := processTransaction_supply (validateTransaction_ok hValid).2.1
    (le_effectiveGasPrice hFee) hOut
  have hBlob := processTransaction_blockGas_blob hOut
  have hAfter : (TransactionState.ofBlock after.block).supply = out.state.supply :=
    BodyState.supply_join hJoin
  have hBurned : burnedWei env after = burnedWei env before + burnedFees env tx out.gasUsed := by
    simp only [burnedWei, burnedFees, hGas, hCumulative, BlockGas.add, hBlob, Nat.add_mul]
    omega
  rw [hAfter, hBurned]
  refine ⟨?_, fun hglam => ?_⟩
  · have := hTx.1
    omega
  · have := hTx.2 (.inl hglam)
    have := heq hglam
    omega

/-! ## The body -/

/-- After the body of a block, the supply plus its burned fees is at most the supply before.

The supply before counts the ether that the block creates.

From Glamsterdam, the two are equal.

Before Paris, the block must have at most two ommers, as the checks of the block ensure. -/
theorem applyBody_supply {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hOmmers : fork < .paris → block.ommers.length ≤ 2)
    (h : applyBody config env block start = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput ≤
        (TransactionState.ofBlock start).supply + createdWei block ∧
      (.glamsterdam ≤ fork → (TransactionState.ofBlock output.block).supply +
        burnedWei env output.toBodyOutput = (TransactionState.ofBlock start).supply +
          createdWei block) := by
  obtain ⟨dao, system, txs, withdrawn, requested, hdao, hsystem, htxs, hShapella, hNot,
    hrequests, hrewarded, -, -, hGas, hCumulative⟩ := applyBody_eq_ok h
  have sDao := supply_daoTransfer hdao
  obtain ⟨sSysLe, sSysEq⟩ := supply_startSystemCalls hsystem
  obtain ⟨sTxLe, sTxEq⟩ := applyTransactions_supply htxs
  obtain ⟨sReqLe, sReqEq⟩ := supply_blockRequests hrequests
  obtain ⟨tx, hpay, sRew⟩ := supply_onBlock hrewarded
  rw [supply_payRewards (by simpa using hOmmers) hpay] at sRew
  -- The withdrawals add their wei from Shapella.
  have sWd : (TransactionState.ofBlock withdrawn.block).supply =
      (TransactionState.ofBlock txs.block).supply +
        (if h : .shapella ≤ fork then withdrawnWei (block.withdrawals h) else 0) := by
    by_cases hS : .shapella ≤ fork
    · obtain ⟨wtx, hwtx, hjoin⟩ := hShapella hS
      rw [BodyState.supply_join hjoin, supply_withdrawalState hwtx]
      simp only [hS, ↓reduceDIte]
      rfl
    · rw [hNot hS]
      simp only [hS, ↓reduceDIte, Nat.add_zero]
      rfl
  have hBurned : burnedWei env output.toBodyOutput = burnedWei env txs := by
    simp only [burnedWei, hGas, hCumulative]
  have hdaoInit : (TransactionState.ofBlock (BodyState.init dao).block).supply =
      (TransactionState.ofBlock start).supply := sDao
  rw [hBurned]
  simp only [BodyOutput.block, createdWei] at *
  refine ⟨by omega, fun hglam => ?_⟩
  have := sSysEq hglam
  have := sTxEq hglam
  have := sReqEq hglam
  omega

/-- After the body of a block, the supply plus its burned fees is at most the supply before.

The supply before counts the ether that the block creates, and the bound holds at every fork.

Before Paris, the block must have at most two ommers, as the checks of the block ensure. -/
theorem applyBody_supply_le {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hOmmers : fork < .paris → block.ommers.length ≤ 2)
    (h : applyBody config env block start = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput ≤
      (TransactionState.ofBlock start).supply + createdWei block :=
  (applyBody_supply hOmmers h).1

/-- From Glamsterdam, the body of a block changes the supply by its created ether minus its fees.

The fees are those that it burns. -/
theorem applyBody_supply_of_glamsterdam {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (hFork : .glamsterdam ≤ fork) (h : applyBody config env block start = .ok output) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput =
      (TransactionState.ofBlock start).supply + createdWei block :=
  (applyBody_supply (fun hlt => absurd (Nat.lt_of_lt_of_le hlt (by decide)) (Nat.not_lt.mpr hFork))
    h).2 hFork

/-! ## The state transition -/

/-- A block that passes the transition gives the state after its body, which runs as follows.

Before Paris it has at most two ommers.

Its header states the gas that the body used, and from Dencun the blob gas. -/
private theorem stateTransition_body {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      post = output.block.applyChanges ∧
      (fork < .paris → block.ommers.length ≤ 2) ∧
      output.gas.gasUsed = block.header.gasUsed ∧
      ∀ hFork : .dencun ≤ fork, output.gas.blob = (block.header.blobGasUsed hFork).toNat := by
  obtain ⟨-, -, hCheck, hashes, output, _, hHashes, hOutput, -, hChecks, hPost⟩ :=
    stateTransition_eq_ok h
  exact ⟨hashes, output, hHashes, hOutput, hPost,
    fun hParis => (validateOmmers_spec (checkBlock_validateOmmers hParis hCheck)).2.1,
    (of_outputChecks hChecks).1, fun hFork => blobGasUsed_of_outputChecks hFork hChecks⟩

/-- After a block that passes the transition, the supply plus its burned fees is at most before.

The supply before counts the ether that the block creates, and the bound holds at every fork.

The fees come from the body that the transition runs. -/
theorem stateTransition_supply_le {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      post.supply + burnedWei (blockEnvironment chain.config hashes block.header)
          output.toBodyOutput ≤ chain.state.supply + createdWei block := by
  obtain ⟨hashes, output, hHashes, hOutput, rfl, hOmmers, -⟩ := stateTransition_body h
  refine ⟨hashes, output, hHashes, hOutput, ?_⟩
  rw [← TransactionState.supply_ofBlock, ← TransactionState.supply_ofPreState]
  exact applyBody_supply_le hOmmers hOutput

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
  obtain ⟨hashes, output, hHashes, hOutput, rfl, -⟩ := stateTransition_body h
  refine ⟨hashes, output, hHashes, hOutput, ?_⟩
  rw [← TransactionState.supply_ofBlock, ← TransactionState.supply_ofPreState]
  exact applyBody_supply_of_glamsterdam hFork hOutput

/-- Before Glamsterdam, a block lowers the supply by at least the fees that its header gives.

The block must pass the transition.

Those are its gas used at the base fee per gas, and its blob gas used at the base fee per blob gas.

It also adds its created ether.
 -/
theorem stateTransition_supply_le_of_lt_glamsterdam {chain : BlockChain}
    {block : Block fork Transaction} {checkSeal : Bool} {post : State}
    (hFork : fork < .glamsterdam) (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes, recentHashes chain.recent = .ok hashes ∧
      post.supply + headerBurnedWei (blockEnvironment chain.config hashes block.header)
          block.header ≤ chain.state.supply + createdWei block := by
  obtain ⟨hashes, output, hHashes, hOutput, rfl, hOmmers, hGasUsed, hBlob⟩ :=
    stateTransition_body h
  refine ⟨hashes, hHashes, ?_⟩
  rw [← TransactionState.supply_ofBlock, ← TransactionState.supply_ofPreState]
  have hle := applyBody_supply_le hOmmers hOutput
  suffices burned : burnedWei (blockEnvironment chain.config hashes block.header)
      output.toBodyOutput = headerBurnedWei (blockEnvironment chain.config hashes block.header)
        block.header by
    rwa [← burned]
  -- The gas of the body is the gas used that its receipts add up, with no state gas.
  obtain ⟨-, body, txs, -, -, -, -, hTxs, -, -, -, -, -, -, hGas, hCumulative⟩ :=
    applyBody_eq_ok hOutput
  have hExecution := applyTransactions_execution_of_lt hFork hTxs
  have hState := applyTransactions_state_of_lt hFork hTxs
  have hUsed : output.cumulativeGasUsed = block.header.gasUsed := by
    rw [← hGasUsed, BlockGas.gasUsed, hGas, hState, hExecution, hCumulative]
    exact (Nat.max_eq_left (Nat.zero_le _)).symm
  unfold burnedWei headerBurnedWei
  rw [hUsed]
  split
  · rename_i hDencun
    rw [hBlob hDencun]
  · rename_i hDencun
    simp only [blobGasPriceOf, hDencun, ↓reduceDIte, Nat.mul_zero]

end EthLib.Execution.Blocks

module

public import EthLib.Execution.Proofs.Blocks.BodyGas
public import EthLib.Execution.Proofs.Blocks.Ommers
public import EthLib.Execution.Proofs.Blocks.Rewards
public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.Withdrawal
public import EthLib.Execution.Proofs.Transactions.Burn

/-!
# Proofs: the exact change of the supply of ether across a block

A block changes the supply by its created wei, its burned fees and its other losses.

From Shapella, each withdrawal creates its amount in Gwei times `10^9`, by [EIP-4895][e4895].

Before Paris, the rewards of the beneficiary and of the ommers create ether.

Section 11.3 of the Yellow Paper, Berlin version, sets them: [`Paper.tex`][yp].

[EIP-3675][e3675] removes them from Paris.

Before Paris, the DAO transfer at the first block of the DAO Fork moves ether, and keeps the supply.

The burned fees are the base fee per gas times the gas used after the refunds.

They add the base fee per blob gas times the blob gas, by [EIP-1559][e1559] and [EIP-4844][e4844].

Before London the base fee per gas is 0, and before Dencun the base fee per blob gas is 0.

The other losses are the surviving burns of SELFDESTRUCT and the balances that transactions delete.

A surviving burn is a burn of SELFDESTRUCT that no rollback of its frame drops.

From Glamsterdam, every surviving burn and every deleted balance is 0, by [EIP-8246][e8246].

Two certificates of the same run give the same total of those losses.

That needs at most two ommers before Paris, which the checks of the block enforce.

System calls also have surviving burn logs, since their stored code is arbitrary.

They pay no fees and perform no transaction-end deletion.

The certificates below keep those calls and each transaction in their execution order.

[e1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[e3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#specification
[e4844]: https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
[e4895]: https://eips.ethereum.org/EIPS/eip-4895#specification
[e8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
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

/-- The fees that the transactions of a body burn, in wei, from the gas counts of its output.

It is the base fee per gas times their gas used after the refunds.

It adds the base fee per blob gas times their blob gas. -/
def burnedWei (env : BlockEnvironment fork) (output : BodyOutput fork) : Nat :=
  output.cumulativeGasUsed * baseFeeOf env + output.gas.blob * blobGasPriceOf env

/-! ## The steps on the block state -/

/-- A step that runs on a block state as a transaction leaves the supply of its end state. -/
theorem supply_onBlock {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (h : onBlock block step = .ok block') :
    ∃ tx, step (.ofBlock block) = .ok tx ∧
      (TransactionState.ofBlock block').supply = tx.supply := by
  obtain ⟨tx, htx, rfl⟩ := onBlock_eq_ok h
  exact ⟨tx, htx, TransactionState.supply_incorporateTxIntoBlock tx⟩

/-- A call that joins the body leaves the supply of its end state. -/
theorem BodyState.supply_join {body body' : BodyState} {tx : TransactionState}
    (h : body.join tx = .ok body') : (TransactionState.ofBlock body'.block).supply = tx.supply := by
  obtain ⟨builder, -, rfl⟩ := BodyState.join_eq_ok h
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

/-- The withdrawals add the wei they withdraw to the supply. -/
theorem supply_withdrawalState {block : BlockState} {withdrawals : List Withdrawal}
    {tx : TransactionState} (h : withdrawalState fork block withdrawals = .ok tx) :
    tx.supply = (TransactionState.ofBlock block).supply + withdrawnWei withdrawals := by
  rw [TransactionState.supply_foldlM_createEther _ _ withdrawals h]
  simp only [toNat_withdrawalWei, withdrawnWei]

/-- The withdrawals of a block add their wei to the supply after its transactions.

They run from Shapella, and before it the body keeps its supply. -/
theorem supply_withdrawals {block : Block fork Transaction} {txs : BodyOutput fork}
    {withdrawn : BodyState}
    (hShapella : ∀ hShapella : .shapella ≤ fork, ∃ tx,
      withdrawalState fork txs.body.block (block.withdrawals hShapella) = .ok tx ∧
      (txs.body.beginIndex (block.transactions.length + 1)).join tx = .ok withdrawn)
    (hNot : ¬.shapella ≤ fork → withdrawn = txs.body.beginIndex (block.transactions.length + 1)) :
    (TransactionState.ofBlock withdrawn.block).supply =
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

/-- The rewards add the wei they reward to the supply.

Before Paris, at most two ommers keep the reward of the beneficiary below `2^256`.

The checks of the block enforce that bound. -/
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

/-! ## System calls -/

/-- A certificate of the message of a system call, with the gas meter of its fork. -/
def SystemCallBurns (env : BlockEnvironment fork) (block : BlockState) (target : Address)
    (data : ByteArray) (out : SystemCallOutput) (log : BurnLog) : Prop :=
  if .glamsterdam ≤ fork then
    MessageCallBurns (Meter := StateGasMeter) env.chainId.toNat (systemMessage env target data)
      (.ofBlock block) .empty [] ∅ out.state log
  else
    MessageCallBurns (Meter := Nat) env.chainId.toNat (systemMessage env target data)
      (.ofBlock block) .empty [] ∅ out.state log

/-- Each system call that runs has a certificate of the surviving burns of its message. -/
theorem systemCall_systemCallBurns {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out) :
    ∃ log, SystemCallBurns env block target data out log := by
  unfold systemCall at h
  dsimp only at h
  split at h <;>
  · rename_i hfork
    obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    obtain ⟨log, certificate⟩ := processMessageCall_messageCallBurns hcall
    exact ⟨log, by simpa only [SystemCallBurns, hfork, ↓reduceIte] using certificate⟩

/-- A system call lowers the supply by exactly the surviving burns of its message. -/
theorem SystemCallBurns.supply_eq {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput} {log : BurnLog}
    (h : SystemCallBurns env block target data out log) :
    out.state.supply + log.total = (TransactionState.ofBlock block).supply := by
  unfold SystemCallBurns at h
  split at h <;> exact h.supply

/-- From Glamsterdam, a certified system call burns nothing. -/
theorem SystemCallBurns.total_eq_zero_of_glamsterdam {env : BlockEnvironment fork}
    {block : BlockState} {target : Address} {data : ByteArray} {out : SystemCallOutput}
    {log : BurnLog} (hfork : .glamsterdam ≤ fork)
    (h : SystemCallBurns env block target data out log) : log.total = 0 := by
  unfold SystemCallBurns at h
  simp only [hfork, ↓reduceIte] at h
  exact h.total_eq_zero_of_glamsterdam hfork

/-- The beacon root call from Dencun and the parent hash call from Pectra, with their burns. -/
def StartSystemCallsBurns (env : BlockEnvironment fork) (parentHash : Hash32)
    (body after : BodyState) (log : BurnLog) : Prop :=
  ∃ mid first second,
    (if h : .dencun ≤ fork then ∃ out,
      systemCall env body.block BEACON_ROOTS_ADDRESS
        ⟨(env.parentBeaconBlockRoot h).toArray⟩ = .ok out ∧
      body.join out.state = .ok mid ∧
      SystemCallBurns env body.block BEACON_ROOTS_ADDRESS
        ⟨(env.parentBeaconBlockRoot h).toArray⟩ out first
    else mid = body ∧ first = .empty) ∧
    (if .pectra ≤ fork then ∃ out,
      systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩ = .ok out ∧
      mid.join out.state = .ok after ∧
      SystemCallBurns env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩ out second
    else after = mid ∧ second = .empty) ∧
    log = .append first second

/-- The system calls at the start of a block have certificates of their surviving burns. -/
theorem startSystemCalls_startSystemCallsBurns {env : BlockEnvironment fork} {parentHash : Hash32}
    {body after : BodyState} (h : startSystemCalls env parentHash body = .ok after) :
    ∃ log, StartSystemCallsBurns env parentHash body after log := by
  obtain ⟨mid, first, noFirst, second, noSecond⟩ := startSystemCalls_eq_ok h
  have firstRun : ∃ log,
      (if h : .dencun ≤ fork then ∃ out,
        systemCall env body.block BEACON_ROOTS_ADDRESS
          ⟨(env.parentBeaconBlockRoot h).toArray⟩ = .ok out ∧
        body.join out.state = .ok mid ∧
        SystemCallBurns env body.block BEACON_ROOTS_ADDRESS
          ⟨(env.parentBeaconBlockRoot h).toArray⟩ out log
      else mid = body ∧ log = .empty) := by
    by_cases hd : .dencun ≤ fork
    · obtain ⟨out, call, join⟩ := first hd
      obtain ⟨log, burns⟩ := systemCall_systemCallBurns call
      exact ⟨log, by simpa only [hd, ↓reduceDIte] using ⟨out, call, join, burns⟩⟩
    · refine ⟨.empty, ?_⟩
      simp only [hd, ↓reduceDIte]
      exact ⟨noFirst hd, trivial⟩
  obtain ⟨log1, cert1⟩ := firstRun
  by_cases hp : .pectra ≤ fork
  · obtain ⟨out, call, join⟩ := second hp
    obtain ⟨log2, burns⟩ := systemCall_systemCallBurns call
    refine ⟨.append log1 log2, mid, log1, log2, cert1, ?_, rfl⟩
    simpa only [hp, ↓reduceIte] using ⟨out, call, join, burns⟩
  · refine ⟨.append log1 .empty, mid, log1, .empty, cert1, ?_, rfl⟩
    simp only [hp, ↓reduceIte]
    exact ⟨noSecond hp, trivial⟩

/-- The certified system calls lose exactly their surviving burns. -/
theorem StartSystemCallsBurns.supply_eq {env : BlockEnvironment fork} {parentHash : Hash32}
    {body after : BodyState} {log : BurnLog}
    (h : StartSystemCallsBurns env parentHash body after log) :
    (TransactionState.ofBlock after.block).supply + log.total =
      (TransactionState.ofBlock body.block).supply := by
  obtain ⟨mid, first, second, hfirst, hsecond, rfl⟩ := h
  have firstSupply : (TransactionState.ofBlock mid.block).supply + first.total =
      (TransactionState.ofBlock body.block).supply := by
    split at hfirst
    · obtain ⟨out, -, join, burns⟩ := hfirst
      rw [BodyState.supply_join join]
      exact burns.supply_eq
    · obtain ⟨rfl, rfl⟩ := hfirst
      rfl
  split at hsecond
  · obtain ⟨out, -, join, burns⟩ := hsecond
    have secondSupply := burns.supply_eq
    rw [← BodyState.supply_join join] at secondSupply
    simp only [BurnLog.total]
    omega
  · obtain ⟨rfl, rfl⟩ := hsecond
    simpa only [BurnLog.total, Nat.add_zero] using firstSupply

/-- From Glamsterdam, the certified system calls at the start of a block burn nothing. -/
theorem StartSystemCallsBurns.total_eq_zero_of_glamsterdam {env : BlockEnvironment fork}
    {parentHash : Hash32} {body after : BodyState} {log : BurnLog} (hfork : .glamsterdam ≤ fork)
    (h : StartSystemCallsBurns env parentHash body after log) : log.total = 0 := by
  obtain ⟨mid, first, second, hfirst, hsecond, rfl⟩ := h
  have firstZero : first.total = 0 := by
    split at hfirst
    · obtain ⟨_, -, -, burns⟩ := hfirst
      exact burns.total_eq_zero_of_glamsterdam hfork
    · rw [hfirst.2]
      rfl
  have secondZero : second.total = 0 := by
    split at hsecond
    · obtain ⟨_, -, -, burns⟩ := hsecond
      exact burns.total_eq_zero_of_glamsterdam hfork
    · rw [hsecond.2]
      rfl
  simp only [BurnLog.total, firstZero, secondZero]

/-! ## Transactions -/

/-- The surviving burn log and deleted balances of each transaction, in order. -/
abbrev TransactionLosses := List (BurnLog × Nat)

/-- The sum, over the transactions, of their surviving burns and their deleted balances. -/
def TransactionLosses.total (losses : TransactionLosses) : Nat :=
  (losses.map fun loss => loss.1.total + loss.2).sum

/-- The transaction fold, with one certificate for each transaction it runs. -/
inductive TransactionsBurns (env : BlockEnvironment fork) :
    BodyOutput fork → List (Transaction × Nat) → BodyOutput fork → TransactionLosses → Prop
  | nil (body) : TransactionsBurns env body [] body []
  | cons {before after last tx index rest log deleted losses included out}
      (step : applyTransaction env index before tx = .ok after)
      (inclusion : checkInclusion env.chainId env before.gas (.ofBlock before.block) tx =
        .ok included)
      (run : processTransaction env before.block included tx = .ok out)
      (burns : TransactionBurns env before.block included tx out log deleted)
      (tail : TransactionsBurns env after rest last losses) :
      TransactionsBurns env before ((tx, index) :: rest) last ((log, deleted) :: losses)

/-- The transaction fold gives a certificate for each transaction it runs. -/
private theorem fold_transactionsBurns {env : BlockEnvironment fork}
    {transactions : List (Transaction × Nat)} {before after : BodyOutput fork}
    (h : transactions.foldlM (fun body (tx, index) => applyTransaction env index body tx)
      before = .ok after) :
    ∃ losses, TransactionsBurns env before transactions after losses := by
  induction transactions generalizing before with
  | nil => cases h; exact ⟨[], .nil _⟩
  | cons item rest ih =>
    obtain ⟨tx, index⟩ := item
    obtain ⟨mid, step, tail⟩ := bind_ok_iff.mp h
    obtain ⟨included, out, inclusion, run, -⟩ := applyTransaction_eq_ok step
    obtain ⟨log, deleted, burns⟩ := processTransaction_transactionBurns run
    obtain ⟨losses, rest⟩ := ih tail
    exact ⟨(log, deleted) :: losses, .cons step inclusion run burns rest⟩

/-- The certified transactions lose exactly their fees and the losses of their certificates. -/
theorem TransactionsBurns.supply_eq {env : BlockEnvironment fork}
    {transactions : List (Transaction × Nat)} {before after : BodyOutput fork}
    {losses : TransactionLosses} (h : TransactionsBurns env before transactions after losses) :
    (TransactionState.ofBlock after.block).supply + burnedWei env after + losses.total =
      (TransactionState.ofBlock before.block).supply + burnedWei env before := by
  induction h with
  | nil => simp [TransactionLosses.total]
  | @cons before after last tx index rest log deleted losses included out step inclusion run
      burns tail ih =>
    obtain ⟨included', out', inclusion', run', gas, cumulative, join⟩ :=
      applyTransaction_eq_ok step
    have hi : included' = included := Except.ok.inj (inclusion'.symm.trans inclusion)
    subst included'
    have ho : out' = out := Except.ok.inj (run'.symm.trans run)
    subst out'
    obtain ⟨-, -, valid, -, -, -, -, fee, -⟩ := checkInclusion_eq_ok_iff.mp inclusion
    have supply := burns.supply_eq (validateTransaction_ok valid).2.1
      (le_effectiveGasPrice fee)
    have blob := processTransaction_blockGas_blob run
    have joined := BodyState.supply_join join
    have fees : burnedWei env after = burnedWei env before + burnedFees env tx out.gasUsed := by
      simp only [burnedWei, burnedFees, gas, cumulative, BlockGas.add, blob, Nat.add_mul]
      omega
    simp only [TransactionLosses.total, List.map_cons, List.sum_cons] at *
    change (TransactionState.ofBlock after.block).supply = out.state.supply at joined
    omega

/-- From Glamsterdam, certified transactions have no surviving burns and no deleted balances. -/
theorem TransactionsBurns.total_eq_zero_of_glamsterdam {env : BlockEnvironment fork}
    {transactions : List (Transaction × Nat)} {before after : BodyOutput fork}
    {losses : TransactionLosses} (hfork : .glamsterdam ≤ fork)
    (h : TransactionsBurns env before transactions after losses) : losses.total = 0 := by
  induction h with
  | nil => rfl
  | cons _ _ _ burns _ ih =>
    obtain ⟨hlog, hdeleted⟩ := burns.eq_zero_of_glamsterdam hfork
    simp only [TransactionLosses.total] at ih ⊢
    simp only [List.map_cons, List.sum_cons, hlog, hdeleted, ih]

/-! ## Requests -/

/-- The request calls in order, with a surviving burn log for each call. -/
inductive RequestsBurns (env : BlockEnvironment fork) :
    BodyState × List ByteArray → List (UInt8 × Address) → BodyState × List ByteArray →
      BurnLog → Prop
  | nil (body) : RequestsBurns env body [] body .empty
  | cons {before after last contract rest first later out}
      (step : readRequest env before contract = .ok after)
      (call : checkedSystemCall env before.1.block contract.2 .empty = .ok out)
      (burns : SystemCallBurns env before.1.block contract.2 .empty out first)
      (tail : RequestsBurns env after rest last later) :
      RequestsBurns env before (contract :: rest) last (.append first later)

/-- Each successful fold over request contracts has a certificate. -/
private theorem fold_requestsBurns {env : BlockEnvironment fork}
    {contracts : List (UInt8 × Address)} {before after : BodyState × List ByteArray}
    (h : contracts.foldlM (readRequest env) before = .ok after) :
    ∃ log, RequestsBurns env before contracts after log := by
  induction contracts generalizing before with
  | nil => cases h; exact ⟨.empty, .nil _⟩
  | cons contract rest ih =>
    obtain ⟨mid, step, tail⟩ := bind_ok_iff.mp h
    obtain ⟨out, call, -⟩ := readRequest_eq_ok step
    obtain ⟨first, burns⟩ := systemCall_systemCallBurns (checkedSystemCall_ok call).2.1
    obtain ⟨later, certificate⟩ := ih tail
    exact ⟨.append first later, .cons step call burns certificate⟩

/-- The certified request calls lose exactly the surviving burns of their messages. -/
theorem RequestsBurns.supply_eq {env : BlockEnvironment fork}
    {contracts : List (UInt8 × Address)} {before after : BodyState × List ByteArray}
    {log : BurnLog} (h : RequestsBurns env before contracts after log) :
    (TransactionState.ofBlock after.1.block).supply + log.total =
      (TransactionState.ofBlock before.1.block).supply := by
  induction h with
  | nil => rfl
  | cons step call burns tail ih =>
    obtain ⟨out, call', join, -⟩ := readRequest_eq_ok step
    cases Except.ok.inj (call'.symm.trans call)
    have supply := burns.supply_eq
    rw [← BodyState.supply_join join] at supply
    simp only [BurnLog.total]
    omega

/-- From Glamsterdam, the certified request calls burn nothing. -/
theorem RequestsBurns.total_eq_zero_of_glamsterdam {env : BlockEnvironment fork}
    {contracts : List (UInt8 × Address)} {before after : BodyState × List ByteArray}
    {log : BurnLog} (hfork : .glamsterdam ≤ fork)
    (h : RequestsBurns env before contracts after log) : log.total = 0 := by
  induction h with
  | nil => rfl
  | cons _ _ burns _ ih =>
    simp only [BurnLog.total, burns.total_eq_zero_of_glamsterdam hfork, ih]

/-- From Pectra, a certificate of each call that reads requests; before Pectra, no call. -/
def BlockRequestsBurns (env : BlockEnvironment fork) (body after : BodyState)
    (log : BurnLog) : Prop :=
  if .pectra ≤ fork then ∃ requests,
    RequestsBurns env (body, []) (requestContracts fork) (after, requests) log
  else after = body ∧ log = .empty

/-- The requests of a block that run have a certificate of their surviving burns. -/
theorem blockRequests_blockRequestsBurns {depositContract : Address}
    {env : BlockEnvironment fork} {body : BodyState} {logs : List Log}
    {result : BodyState × List ByteArray}
    (h : blockRequests depositContract env body logs = .ok result) :
    ∃ log, BlockRequestsBurns env body result.1 log := by
  obtain ⟨noPectra, pectra⟩ := blockRequests_eq_ok h
  by_cases hp : .pectra ≤ fork
  · obtain ⟨deposits, read, -, hread, rfl⟩ := pectra hp
    obtain ⟨log, certificate⟩ := fold_requestsBurns hread
    exact ⟨log, by simpa only [BlockRequestsBurns, hp, ↓reduceIte] using ⟨_, certificate⟩⟩
  · rw [noPectra hp]
    exact ⟨.empty, by simp [BlockRequestsBurns, hp]⟩

/-- The certified requests of a block lose exactly their surviving burns. -/
theorem BlockRequestsBurns.supply_eq {env : BlockEnvironment fork} {body after : BodyState}
    {log : BurnLog} (h : BlockRequestsBurns env body after log) :
    (TransactionState.ofBlock after.block).supply + log.total =
      (TransactionState.ofBlock body.block).supply := by
  unfold BlockRequestsBurns at h
  split at h
  · obtain ⟨requests, certificate⟩ := h
    exact certificate.supply_eq
  · obtain ⟨rfl, rfl⟩ := h
    rfl

/-- From Glamsterdam, the certified requests of a block burn nothing. -/
theorem BlockRequestsBurns.total_eq_zero_of_glamsterdam {env : BlockEnvironment fork}
    {body after : BodyState} {log : BurnLog} (hfork : .glamsterdam ≤ fork)
    (h : BlockRequestsBurns env body after log) : log.total = 0 := by
  unfold BlockRequestsBurns at h
  split at h
  · obtain ⟨_, certificate⟩ := h
    exact certificate.total_eq_zero_of_glamsterdam hfork
  · rw [h.2]
    rfl

/-! ## The block -/

/-- The losses beyond fees of the three phases that run messages in a block. -/
structure BlockLosses where
  /-- Surviving burns of the system calls before the transactions. -/
  start : BurnLog
  /-- Surviving burns and deleted balances, one pair per transaction in order. -/
  transactions : TransactionLosses
  /-- Surviving burns of the calls that read requests. -/
  requests : BurnLog

/-- The sum of the surviving burns and the deleted balances of a block. -/
def BlockLosses.total (losses : BlockLosses) : Nat :=
  losses.start.total + losses.transactions.total + losses.requests.total

/-- The phases of a block body that change the supply, with certificates of its losses. -/
def BodyBurns (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) (output : BlockOutput fork)
    (losses : BlockLosses) : Prop :=
  ∃ dao system txs withdrawn requested,
    daoTransfer config fork block.header.number start = .ok dao ∧
    StartSystemCallsBurns env block.header.parentHash (.init dao) system losses.start ∧
    TransactionsBurns env ⟨system, .zero, 0, [], []⟩ block.transactions.zipIdx txs
      losses.transactions ∧
    (if h : .shapella ≤ fork then ∃ tx,
      withdrawalState fork txs.block (block.withdrawals h) = .ok tx ∧
      (txs.body.beginIndex (block.transactions.length + 1)).join tx = .ok withdrawn
    else withdrawn = txs.body.beginIndex (block.transactions.length + 1)) ∧
    BlockRequestsBurns env withdrawn requested losses.requests ∧
    onBlock requested.block (fun tx => payRewards fork tx block.header.coinbase
      block.header.number (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number))) =
      .ok output.block ∧
    output.gas = txs.gas ∧ output.cumulativeGasUsed = txs.cumulativeGasUsed

/-- Every body that runs certifies its system calls, its transactions and its request calls. -/
theorem applyBody_bodyBurns {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ losses, BodyBurns config env block start output losses := by
  obtain ⟨dao, system, txs, withdrawn, requested, hdao, hsystem, htxs, hshapella, hnot,
    hrequests, hrewarded, -, -, hgas, hcumulative⟩ := applyBody_eq_ok h
  obtain ⟨startLog, startBurns⟩ := startSystemCalls_startSystemCallsBurns hsystem
  obtain ⟨txLosses, txBurns⟩ := fold_transactionsBurns htxs
  obtain ⟨requestLog, requestBurns⟩ := blockRequests_blockRequestsBurns hrequests
  refine ⟨⟨startLog, txLosses, requestLog⟩,
    dao, system, txs, withdrawn, requested, hdao, startBurns, txBurns, ?_, requestBurns,
    hrewarded, hgas, hcumulative⟩
  split
  · exact hshapella ‹_›
  · exact hnot ‹_›

/-- A certificate of a block body gives the exact supply change at every fork.

The block adds its withdrawals and rewards, and loses its fees and certified losses.

Before Paris, the block must have at most two ommers, as the checks of the block enforce. -/
theorem BodyBurns.supply_eq {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {losses : BlockLosses} (hom : fork < .paris → block.ommers.length ≤ 2)
    (h : BodyBurns config env block start output losses) :
    (TransactionState.ofBlock output.block).supply + burnedWei env output.toBodyOutput +
      losses.total = (TransactionState.ofBlock start).supply + createdWei block := by
  obtain ⟨dao, system, txs, withdrawn, requested, hdao, hsystem, htxs, hwithdrawn,
    hrequests, hrewarded, hgas, hcumulative⟩ := h
  have daoSupply := supply_daoTransfer hdao
  have startSupply := hsystem.supply_eq
  have txSupply := htxs.supply_eq
  have withdrawnSupply := supply_withdrawals (block := block)
    (fun hs => by simpa only [hs, ↓reduceDIte, BodyOutput.block] using hwithdrawn)
    (fun hs => by simpa only [hs, ↓reduceDIte] using hwithdrawn)
  have requestSupply := hrequests.supply_eq
  obtain ⟨rewarded, hpay, rewardSupply⟩ := supply_onBlock hrewarded
  rw [supply_payRewards (by simpa using hom) hpay] at rewardSupply
  have fees : burnedWei env output.toBodyOutput = burnedWei env txs := by
    simp only [burnedWei, hgas, hcumulative]
  simp only [burnedWei, BlockGas.zero, Nat.zero_mul, Nat.add_zero] at txSupply
  change (TransactionState.ofBlock txs.block).supply +
      (txs.cumulativeGasUsed * baseFeeOf env + txs.gas.blob * blobGasPriceOf env) +
        losses.transactions.total = (TransactionState.ofBlock system.block).supply at txSupply
  rw [fees]
  change (TransactionState.ofBlock dao).supply =
    (TransactionState.ofBlock start).supply at daoSupply
  change (TransactionState.ofBlock system.block).supply + losses.start.total =
    (TransactionState.ofBlock dao).supply at startSupply
  simp only [BlockLosses.total, createdWei, burnedWei]
  omega

/-- Two certificates of a block body give the same total of losses.

Before Paris, the block must have at most two ommers, as the checks of the block enforce. -/
theorem BodyBurns.total_eq {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {losses losses' : BlockLosses} (hom : fork < .paris → block.ommers.length ≤ 2)
    (h : BodyBurns config env block start output losses)
    (h' : BodyBurns config env block start output losses') :
    losses'.total = losses.total := by
  have := h.supply_eq hom
  have := h'.supply_eq hom
  omega

/-- From Glamsterdam, the losses of a block certificate total 0. -/
theorem BodyBurns.total_eq_zero_of_glamsterdam {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    {losses : BlockLosses} (hfork : .glamsterdam ≤ fork)
    (h : BodyBurns config env block start output losses) : losses.total = 0 := by
  obtain ⟨_, _, _, _, _, -, hsystem, htxs, -, hrequests, -⟩ := h
  simp only [BlockLosses.total, hsystem.total_eq_zero_of_glamsterdam hfork,
    htxs.total_eq_zero_of_glamsterdam hfork, hrequests.total_eq_zero_of_glamsterdam hfork]

/-- A block that the transition accepts changes the supply exactly as its run gives.

The created wei includes withdrawals from Shapella and block and ommer rewards before Paris.

The losses are the surviving burns of every system call and every transaction.

They also count the balances that each transaction deletes.

The fees come from the gas counts of the body, so the form also holds from Glamsterdam. -/
theorem stateTransition_supply_eq {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output losses,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BodyBurns chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ output losses ∧
      post.supply + burnedWei (blockEnvironment chain.config hashes block.header)
          output.toBodyOutput + losses.total = chain.state.supply + createdWei block := by
  obtain ⟨-, -, hcheck, hashes, output, _, hhashes, houtput, -, -, hpost⟩ :=
    stateTransition_eq_ok h
  obtain ⟨losses, certificate⟩ := applyBody_bodyBurns houtput
  refine ⟨hashes, output, losses, hhashes, houtput, certificate, ?_⟩
  rw [hpost, ← TransactionState.supply_ofBlock, ← TransactionState.supply_ofPreState]
  exact certificate.supply_eq fun hparis =>
    (validateOmmers_spec (checkBlock_validateOmmers hparis hcheck)).2.1

end EthLib.Execution.Blocks

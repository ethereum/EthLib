module

public import EthLib.Execution.Proofs.Blocks.Supply
public import EthLib.Execution.Proofs.Transactions.Burn

/-!
# Proofs: the exact change of the supply of ether across a block

The run fixes each loss beyond the burned fees: the surviving burns and the deleted balances.

System calls also have surviving burn logs, since their stored code is arbitrary.

They pay no fees and perform no transaction-end deletion.

The certificates below keep those calls and each transaction in their execution order.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions

variable {fork : Fork}

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

/-- Each system call that runs has a surviving burn log certified by its message. -/
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

/-- The two optional calls at the start of a block, with their surviving burns. -/
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
theorem startSystemCalls_burns {env : BlockEnvironment fork} {parentHash : Hash32}
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

/-! ## Transactions -/

/-- The surviving burn log and deleted balances of each transaction, in order. -/
abbrev TransactionLosses := List (BurnLog × Nat)

/-- The total losses beyond fees, retaining the two amounts of each transaction. -/
def TransactionLosses.total (losses : TransactionLosses) : Nat :=
  (losses.map fun loss => loss.1.total + loss.2).sum

/-- The actual transaction fold, with one certificate for each transaction it runs. -/
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

/-! ## Requests -/

/-- The actual ordered request calls, with a surviving burn log for each call. -/
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

/-- The requests of a block keep their actual call certificates, or have no calls before Pectra. -/
def BlockRequestsBurns (env : BlockEnvironment fork) (body after : BodyState)
    (log : BurnLog) : Prop :=
  if .pectra ≤ fork then ∃ requests,
    RequestsBurns env (body, []) (requestContracts fork) (after, requests) log
  else after = body ∧ log = .empty

/-- The requests of a block lose exactly their certified surviving burns. -/
theorem blockRequests_burns {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} {logs : List Log} {result : BodyState × List ByteArray}
    (h : blockRequests depositContract env body logs = .ok result) :
    ∃ log, BlockRequestsBurns env body result.1 log ∧
      (TransactionState.ofBlock result.1.block).supply + log.total =
        (TransactionState.ofBlock body.block).supply := by
  obtain ⟨noPectra, pectra⟩ := blockRequests_eq_ok h
  by_cases hp : .pectra ≤ fork
  · obtain ⟨deposits, read, -, hread, rfl⟩ := pectra hp
    obtain ⟨log, certificate⟩ := fold_requestsBurns hread
    exact ⟨log, by simpa only [BlockRequestsBurns, hp, ↓reduceIte] using ⟨_, certificate⟩,
      certificate.supply_eq⟩
  · rw [noPectra hp]
    exact ⟨.empty, by simp [BlockRequestsBurns, hp], rfl⟩

/-! ## The block -/

/-- The losses beyond fees of the three phases that run messages in a block. -/
structure BlockLosses where
  /-- Surviving burns of the system calls before the transactions. -/
  start : BurnLog
  /-- Surviving burns and deleted balances, one pair per transaction in order. -/
  transactions : TransactionLosses
  /-- Surviving burns of the calls that read requests. -/
  requests : BurnLog

/-- All the surviving message burns and transaction-end deletions of a block. -/
def BlockLosses.total (losses : BlockLosses) : Nat :=
  losses.start.total + losses.transactions.total + losses.requests.total

/-- The supply-changing phases of the actual block body, with certificates of its losses. -/
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

/-- Every body that runs has certificates for its system calls and each transaction. -/
theorem applyBody_bodyBurns {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ losses, BodyBurns config env block start output losses := by
  obtain ⟨dao, system, txs, withdrawn, requested, hdao, hsystem, htxs, hshapella, hnot,
    hrequests, hrewarded, -, -, hgas, hcumulative⟩ := applyBody_eq_ok h
  obtain ⟨startLog, startBurns⟩ := startSystemCalls_burns hsystem
  obtain ⟨txLosses, txBurns⟩ := fold_transactionsBurns htxs
  obtain ⟨requestLog, requestBurns, -⟩ := blockRequests_burns hrequests
  refine ⟨⟨startLog, txLosses, requestLog⟩,
    dao, system, txs, withdrawn, requested, hdao, startBurns, txBurns, ?_, requestBurns,
    hrewarded, hgas, hcumulative⟩
  split
  · exact hshapella ‹_›
  · exact hnot ‹_›

/-- A certificate of a block body gives the exact supply change at every fork.

The block adds its withdrawals and rewards, and loses its fees and certified losses.

Before Paris, the block must have at most two ommers, as its checks ensure. -/
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
  have withdrawnSupply : (TransactionState.ofBlock withdrawn.block).supply =
      (TransactionState.ofBlock txs.block).supply +
        (if h : .shapella ≤ fork then withdrawnWei (block.withdrawals h) else 0) := by
    split at hwithdrawn
    · rename_i hs
      obtain ⟨tx, run, join⟩ := hwithdrawn
      rw [BodyState.supply_join join, supply_withdrawalState run]
      simp only [hs, ↓reduceDIte]
    · rename_i hs
      rw [hwithdrawn]
      simp only [hs, ↓reduceDIte, Nat.add_zero]
      rfl
  have requestSupply : (TransactionState.ofBlock requested.block).supply +
      losses.requests.total = (TransactionState.ofBlock withdrawn.block).supply := by
    unfold BlockRequestsBurns at hrequests
    split at hrequests
    · obtain ⟨requests, certificate⟩ := hrequests
      exact certificate.supply_eq
    · obtain ⟨rfl, hz⟩ := hrequests
      rw [hz]
      rfl
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

/-- A block accepted by the transition has the exact supply change given by its actual run.

The created wei includes withdrawals from Shapella and block and ommer rewards before Paris.

The losses retain the surviving burns of all system calls and each transaction's deletions.

The fees come from the gas counts of the body, including from Glamsterdam. -/
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

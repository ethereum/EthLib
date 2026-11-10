module

public import EthLib.Base.Proofs.List
public import EthLib.Execution.Proofs.Blocks.AccessListCoverage
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the block access list covers every call of the body

The body of a block runs system calls, transactions, withdrawals and calls to request contracts.

Each of them ends with a state that records what it read and what it wrote.

When one of these states joins the body, the builder records it.

So the builder at the end of the body covers every one of them.

That is, it records each account that one of them read or wrote.

It also names each storage key that one of them read or wrote, as a change or as a read.

The list of a builder that covers a call covers that call too, and the block commits to that list.

A header commits to that list from Glamsterdam, so a block that passes the transition names them.

Completeness is relative to the reads and writes that the state of each call records.

The DAO transfer and the block rewards write the state without a call.

The builder leaves them out.

Both run only before Paris, before any block commits to a list.

Source: [EIP-7928, Scope and Inclusion][eip7928].

It asks the list to hold every account that the block accessed, system contracts included.

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State)
open EthLib.Execution.Transactions
open AccessListBuilder (Covers Extends)

variable {fork : Fork}

/-! ## One step of the body -/

/-- A call that joins the body extends the builder, and the builder then covers the call. -/
theorem BodyState.join_covers {body body' : BodyState} {tx : State.TransactionState}
    (h : body.join tx = .ok body') :
    body.builder.Extends body'.builder ∧ body'.builder.Covers tx := by
  unfold join at h
  obtain ⟨b, hb, h⟩ := bind_ok_iff.mp h
  cases h
  exact AccessListBuilder.recordTransaction_covers hb

/-- A transaction that enters the body extends the builder, which then covers its run. -/
theorem applyTransaction_covers {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    ∃ included out,
      checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .ok included ∧
      processTransaction env before.block included tx = .ok out ∧
      before.body.builder.Extends after.body.builder ∧ after.body.builder.Covers out.state := by
  obtain ⟨included, out, hIncluded, hOut, -, -, hJoin⟩ := applyTransaction_eq_ok h
  obtain ⟨hExt, hCovers⟩ := BodyState.join_covers hJoin
  exact ⟨included, out, hIncluded, hOut, hExt, hCovers⟩

/-! ## The transactions -/

/-- The builder at the end of the transactions covers the run of each of them.

The transaction at index `i` of the list, from 0, runs after the transactions before it. -/
theorem applyTransactions_covers {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    body.builder.Extends output.body.builder ∧
      ∀ i (hi : i < transactions.length), ∃ before included out,
        applyTransactions env body (transactions.take i) = .ok before ∧
        checkInclusion env.chainId env before.gas (.ofBlock before.block) transactions[i] =
          .ok included ∧
        processTransaction env before.block included transactions[i] = .ok out ∧
        output.body.builder.Covers out.state := by
  obtain ⟨hExt, hSteps⟩ := foldlM_ok_steps
    (fun a b : BodyOutput fork => a.body.builder.Extends b.body.builder)
    (fun _ => Extends.refl _) (fun h h' => h.trans h')
    (fun _ _ _ hStep => (applyTransaction_covers hStep).choose_spec.choose_spec.2.2.1) h
  refine ⟨hExt, fun i hi => ?_⟩
  obtain ⟨before, next, hBefore, hNext, hEnd⟩ := hSteps i (by simpa using hi)
  simp only [List.getElem_zipIdx, Nat.zero_add] at hNext
  obtain ⟨included, out, hIncluded, hOut, -, hCovers⟩ := applyTransaction_covers hNext
  refine ⟨before, included, out, ?_, hIncluded, hOut, hCovers.mono hEnd⟩
  unfold applyTransactions
  rw [zipIdx_take]
  exact hBefore

/-! ## The system calls -/

/-- The system calls at the start of a block extend the builder, which then covers each call.

From Dencun, the beacon roots contract runs on the block state that the body starts from.

From Pectra, the history storage contract then runs on the block state after it. -/
theorem startSystemCalls_covers {env : BlockEnvironment fork} {parentHash : Hash32}
    {body body' : BodyState} (h : startSystemCalls env parentHash body = .ok body') :
    body.builder.Extends body'.builder ∧
      ∀ hDencun : .dencun ≤ fork, ∃ out mid,
        systemCall env body.block BEACON_ROOTS_ADDRESS
          ⟨(env.parentBeaconBlockRoot hDencun).toArray⟩ = .ok out ∧
        body.join out.state = .ok mid ∧ body'.builder.Covers out.state ∧
        (.pectra ≤ fork → ∃ out',
          systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩ = .ok out' ∧
          body'.builder.Covers out'.state) := by
  -- The second call, from the body after the first.
  have second : ∀ mid : BodyState,
      (if Fork.pectra ≤ fork then do
          let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
          (mid.join out.state).mapError EvmError.state
        else pure mid) = .ok body' →
      mid.builder.Extends body'.builder ∧
        (.pectra ≤ fork → ∃ out',
          systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩ = .ok out' ∧
          body'.builder.Covers out'.state) := by
    intro mid h
    split at h
    · obtain ⟨out', hOut', h⟩ := bind_ok_iff.mp h
      obtain ⟨hExt, hCovers⟩ := BodyState.join_covers (mapError_ok_iff.mp h)
      exact ⟨hExt, fun _ => ⟨out', hOut', hCovers⟩⟩
    · rename_i hPectra
      cases h
      exact ⟨Extends.refl _, fun h => absurd h hPectra⟩
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    have hJoin := mapError_ok_iff.mp hMid
    obtain ⟨hExt, hCovers⟩ := BodyState.join_covers hJoin
    obtain ⟨hRest, hSecond⟩ := second mid h
    exact ⟨hExt.trans hRest, fun _ => ⟨out, mid, hOut, hJoin, hCovers.mono hRest, hSecond⟩⟩
  · rename_i hDencun
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    cases hMid
    exact ⟨(second _ h).1, fun h => absurd h hDencun⟩

/-- The call to one request contract extends the builder, which then covers the call. -/
theorem readRequest_covers {env : BlockEnvironment fork}
    {state state' : BodyState × List ByteArray} {contract : UInt8 × Address}
    (h : readRequest env state contract = .ok state') :
    state.1.builder.Extends state'.1.builder ∧ ∃ out,
      checkedSystemCall env state.1.block contract.2 .empty = .ok out ∧
      state'.1.builder.Covers out.state := by
  unfold readRequest at h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  obtain ⟨joined, hJoined, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨hExt, hCovers⟩ := BodyState.join_covers (mapError_ok_iff.mp hJoined)
  exact ⟨hExt, out, hOut, hCovers⟩

/-- Reading the requests extends the builder, which then covers each call to a contract.

From Pectra, the contract at index `j` runs on the body after the calls before it. -/
theorem readRequests_covers {env : BlockEnvironment fork} {body body' : BodyState}
    {requests : List ByteArray} (h : readRequests env body = .ok (body', requests)) :
    body.builder.Extends body'.builder ∧
      (.pectra ≤ fork → ∀ j (hj : j < (requestContracts fork).length), ∃ mid out,
        ((requestContracts fork).take j).foldlM (readRequest env) (body, []) = .ok mid ∧
        checkedSystemCall env mid.1.block (requestContracts fork)[j].2 .empty = .ok out ∧
        body'.builder.Covers out.state) := by
  unfold readRequests at h
  split at h
  · obtain ⟨hExt, hSteps⟩ := foldlM_ok_steps
      (fun a b : BodyState × List ByteArray => a.1.builder.Extends b.1.builder)
      (fun _ => Extends.refl _) (fun h h' => h.trans h')
      (fun _ _ _ hStep => (readRequest_covers hStep).1) h
    refine ⟨hExt, fun _ j hj => ?_⟩
    obtain ⟨mid, next, hMid, hNext, hEnd⟩ := hSteps j hj
    obtain ⟨-, out, hOut, hCovers⟩ := readRequest_covers hNext
    exact ⟨mid, out, hMid, hOut, hCovers.mono hEnd⟩
  · rename_i hPectra
    cases h
    exact ⟨Extends.refl _, fun h => absurd h hPectra⟩

/-- The requests of a block extend the builder, which then covers each call to a contract. -/
theorem blockRequests_covers {depositContract : Address} {env : BlockEnvironment fork}
    {body body' : BodyState} {logs : List Log} {requests : List ByteArray}
    (h : blockRequests depositContract env body logs = .ok (body', requests)) :
    body.builder.Extends body'.builder ∧
      (.pectra ≤ fork → ∀ j (hj : j < (requestContracts fork).length), ∃ mid out,
        ((requestContracts fork).take j).foldlM (readRequest env) (body, []) = .ok mid ∧
        checkedSystemCall env mid.1.block (requestContracts fork)[j].2 .empty = .ok out ∧
        body'.builder.Covers out.state) := by
  unfold blockRequests at h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨mid, read⟩, hRead, h⟩ := bind_ok_iff.mp h
    cases h
    exact readRequests_covers hRead
  · rename_i hPectra
    cases h
    exact ⟨Extends.refl _, fun h => absurd h hPectra⟩

/-! ## The body -/

/-- The builder at the end of a body covers every call of the body.

The system calls at the start run on the block state after the DAO transfer.

From Paris that transfer leaves the state as it was.

The transactions then run, and the builder after them keeps every record to the end.

From Shapella, the withdrawals then join as one state at the position after the transactions.

From Pectra, each request contract is then called, from the body after the withdrawals. -/
theorem applyBody_covers {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ state body txOutput withdrawn,
      daoTransfer config fork block.header.number start = .ok state ∧
      startSystemCalls env block.header.parentHash (.init state) = .ok body ∧
      (BodyState.init state).builder.Extends output.body.builder ∧
      (∀ hDencun : .dencun ≤ fork, ∃ out mid,
        systemCall env state BEACON_ROOTS_ADDRESS
          ⟨(env.parentBeaconBlockRoot hDencun).toArray⟩ = .ok out ∧
        (BodyState.init state).join out.state = .ok mid ∧ output.body.builder.Covers out.state ∧
        (.pectra ≤ fork → ∃ out',
          systemCall env mid.block HISTORY_STORAGE_ADDRESS
            ⟨block.header.parentHash.toArray⟩ = .ok out' ∧
          output.body.builder.Covers out'.state)) ∧
      applyTransactions env body block.transactions = .ok txOutput ∧
      txOutput.body.builder.Extends output.body.builder ∧
      (∀ hShapella : .shapella ≤ fork, ∃ tx,
        withdrawalState fork txOutput.body.block (block.withdrawals hShapella) = .ok tx ∧
        (txOutput.body.beginIndex (block.transactions.length + 1)).join tx = .ok withdrawn ∧
        output.body.builder.Covers tx) ∧
      (¬.shapella ≤ fork → withdrawn = txOutput.body.beginIndex (block.transactions.length + 1)) ∧
      (.pectra ≤ fork → ∀ j (hj : j < (requestContracts fork).length), ∃ mid out,
        ((requestContracts fork).take j).foldlM (readRequest env) (withdrawn, []) = .ok mid ∧
        checkedSystemCall env mid.1.block (requestContracts fork)[j].2 .empty = .ok out ∧
        output.body.builder.Covers out.state) := by
  obtain ⟨state, body, txOutput, withdrawn, requested, hState, hBody, hTx, hW, hNotW, hRequests,
    -, hBuilder, -⟩ := applyBody_eq_ok h
  obtain ⟨hReqExt, hReqCovers⟩ := blockRequests_covers hRequests
  rw [← hBuilder] at hReqExt hReqCovers
  -- The withdrawals extend the builder after the transactions, and their state is covered.
  have hWExt : txOutput.body.builder.Extends withdrawn.builder := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨tx, -, hJoin⟩ := hW hShapella
      exact (BodyState.join_covers hJoin).1
    · rw [hNotW hShapella]
      exact Extends.refl _
  have hTxExt := hWExt.trans hReqExt
  obtain ⟨hStartExt, hStart⟩ := startSystemCalls_covers hBody
  have hBodyExt := (applyTransactions_covers hTx).1.trans hTxExt
  refine ⟨state, body, txOutput, withdrawn, hState, hBody, hStartExt.trans hBodyExt,
    fun hDencun => ?_, hTx, hTxExt, fun hS => ?_, hNotW, hReqCovers⟩
  · obtain ⟨out, mid, hOut, hMid, hCovers, hSecond⟩ := hStart hDencun
    refine ⟨out, mid, hOut, hMid, hCovers.mono hBodyExt, fun hPectra => ?_⟩
    obtain ⟨out', hOut', hCovers'⟩ := hSecond hPectra
    exact ⟨out', hOut', hCovers'.mono hBodyExt⟩
  · obtain ⟨tx, hTxState, hJoin⟩ := hW hS
    exact ⟨tx, hTxState, hJoin, (BodyState.join_covers hJoin).2.mono hReqExt⟩

/-- The builder at the end of a body covers the run of each of its transactions.

The transaction at index `i` of the list, from 0, runs after the transactions before it. -/
theorem applyBody_covers_transaction {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ state body,
      daoTransfer config fork block.header.number start = .ok state ∧
      startSystemCalls env block.header.parentHash (.init state) = .ok body ∧
      ∀ i (hi : i < block.transactions.length), ∃ before included out,
        applyTransactions env body (block.transactions.take i) = .ok before ∧
        checkInclusion env.chainId env before.gas (.ofBlock before.block)
          block.transactions[i] = .ok included ∧
        processTransaction env before.block included block.transactions[i] = .ok out ∧
        output.body.builder.Covers out.state := by
  obtain ⟨state, body, txOutput, -, hState, hBody, -, -, hTx, hExt, -⟩ := applyBody_covers h
  refine ⟨state, body, hState, hBody, fun i hi => ?_⟩
  obtain ⟨before, included, out, hBefore, hIncluded, hOut, hCovers⟩ :=
    (applyTransactions_covers hTx).2 i hi
  exact ⟨before, included, out, hBefore, hIncluded, hOut, hCovers.mono hExt⟩

/-! ## The list of the block -/

/-- From Glamsterdam, a body gives the hash of the list that its builder built. -/
theorem applyBody_accessListHash {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) (hFork : .glamsterdam ≤ fork) :
    ∃ value, output.accessListHash = some value ∧
      BlockAccessList.hash output.body.builder.build = .ok value := by
  obtain ⟨-, -, -, -, requested, -, -, -, -, -, -, -, hBuilder, hHash, -⟩ := applyBody_eq_ok h
  rw [hBuilder]
  exact (accessListHashOf_eq_ok hHash hFork).2

/-- From Glamsterdam, a block that passes the transition commits to the list that its builder built.

The hash in its header is the hash of the list that the builder built after the body.

With the coverage of the body, that list holds what each call touched.

From Hegota the transition is not yet specified, so this holds from Glamsterdam up to Hegota. -/
theorem stateTransition_accessList {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (hFork : .glamsterdam ≤ fork)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes output,
      recentHashes chain.recent = .ok hashes ∧
      applyBody chain.config (blockEnvironment chain.config hashes block.header) block
        ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) := by
  obtain ⟨-, -, -, hashes, output, _, hHashes, hOutput, -, hChecks, -⟩ := stateTransition_eq_ok h
  obtain ⟨value, hValue, hHash⟩ := applyBody_accessListHash hOutput hFork
  rw [accessListHash_of_outputChecks hFork hChecks] at hValue
  cases hValue
  exact ⟨hashes, output, hHashes, hOutput, hHash⟩

/-- From Glamsterdam, a block that passes the transition commits to a list that covers its body.

The hash in its header is the hash of the list that the builder built after the body.

The body starts from the state after the parent, since the DAO transfer runs only before Paris.

The list covers the beacon roots call there, and the history storage call after it.

It covers the run of each transaction, from the body after the transactions before it.

It covers the withdrawals, and then each call to a request contract.

From Hegota the transition is not yet specified, so this holds from Glamsterdam up to Hegota. -/
theorem stateTransition_accessList_covers {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (hFork : .glamsterdam ≤ fork)
    (h : stateTransition chain block checkSeal = .ok post) :
    ∃ hashes env output body txOutput withdrawn,
      recentHashes chain.recent = .ok hashes ∧
      env = blockEnvironment chain.config hashes block.header ∧
      applyBody chain.config env block ⟨chain.state, ∅, ∅, ∅, ∅⟩ = .ok output ∧
      BlockAccessList.hash output.body.builder.build =
        .ok (block.header.blockAccessListHash hFork) ∧
      (∃ out mid out',
        systemCall env ⟨chain.state, ∅, ∅, ∅, ∅⟩ BEACON_ROOTS_ADDRESS
          ⟨(block.header.parentBeaconBlockRoot (Nat.le_trans (by decide) hFork)).toArray⟩ =
          .ok out ∧
        (BodyState.init ⟨chain.state, ∅, ∅, ∅, ∅⟩).join out.state = .ok mid ∧
        systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨block.header.parentHash.toArray⟩ =
          .ok out' ∧
        output.body.builder.build.Covers out.state ∧
        output.body.builder.build.Covers out'.state) ∧
      startSystemCalls env block.header.parentHash (.init ⟨chain.state, ∅, ∅, ∅, ∅⟩) = .ok body ∧
      applyTransactions env body block.transactions = .ok txOutput ∧
      (∀ i (hi : i < block.transactions.length), ∃ before included out,
        applyTransactions env body (block.transactions.take i) = .ok before ∧
        checkInclusion env.chainId env before.gas (.ofBlock before.block)
          block.transactions[i] = .ok included ∧
        processTransaction env before.block included block.transactions[i] = .ok out ∧
        output.body.builder.build.Covers out.state) ∧
      (∃ tx,
        withdrawalState fork txOutput.body.block
          (block.withdrawals (Nat.le_trans (by decide) hFork)) = .ok tx ∧
        (txOutput.body.beginIndex (block.transactions.length + 1)).join tx = .ok withdrawn ∧
        output.body.builder.build.Covers tx) ∧
      ∀ j (hj : j < (requestContracts fork).length), ∃ mid out,
        ((requestContracts fork).take j).foldlM (readRequest env) (withdrawn, []) = .ok mid ∧
        checkedSystemCall env mid.1.block (requestContracts fork)[j].2 .empty = .ok out ∧
        output.body.builder.build.Covers out.state := by
  obtain ⟨hashes, output, hHashes, hOutput, hHash⟩ := stateTransition_accessList hFork h
  have hShapella : Fork.shapella ≤ fork := Nat.le_trans (by decide) hFork
  have hDencun : Fork.dencun ≤ fork := Nat.le_trans (by decide) hFork
  have hPectra : Fork.pectra ≤ fork := Nat.le_trans (by decide) hFork
  obtain ⟨state, body, txOutput, withdrawn, hState, hBody, -, hStart, hTx, hExt, hWithdrawn, -,
    hRequests⟩ := applyBody_covers hOutput
  rw [daoTransfer_of_paris_le (Nat.le_trans (by decide) hFork)] at hState
  cases hState
  obtain ⟨out, mid, hOut, hMid, hCovers, hSecond⟩ := hStart hDencun
  obtain ⟨out', hOut', hCovers'⟩ := hSecond hPectra
  obtain ⟨tx, hTxState, hJoin, hCoversTx⟩ := hWithdrawn hShapella
  refine ⟨hashes, _, output, body, txOutput, withdrawn, hHashes, rfl, hOutput, hHash,
    ⟨out, mid, out', hOut, hMid, hOut', hCovers.build, hCovers'.build⟩, hBody, hTx,
    fun i hi => ?_, ⟨tx, hTxState, hJoin, hCoversTx.build⟩, fun j hj => ?_⟩
  · obtain ⟨before, included, out, hBefore, hIncluded, hRun, hCoversRun⟩ :=
      (applyTransactions_covers hTx).2 i hi
    exact ⟨before, included, out, hBefore, hIncluded, hRun, (hCoversRun.mono hExt).build⟩
  · obtain ⟨mid, out, hMid, hCall, hCoversCall⟩ := hRequests hPectra j hj
    exact ⟨mid, out, hMid, hCall, hCoversCall.build⟩

end EthLib.Execution.Blocks

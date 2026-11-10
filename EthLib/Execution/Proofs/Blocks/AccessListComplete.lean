module

public import EthLib.Execution.Proofs.Blocks.AccessListCoverage
public import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: the block access list names everything that the body touched

The body of a block runs system calls, transactions and withdrawals.

Each of them ends with a state that records what it read and what it wrote.

The builder records each of these states when it joins the body.

So the builder at the end of the body covers every one of them.

That is, it records each account that one of them read or wrote.

It also names each storage key that one of them read or wrote, as a change or as a read.

The list that the block commits to from Glamsterdam holds each such account and key.

These facts hold at every fork, although a header commits to the list only from Glamsterdam.

Source: [EIP-7928][eip7928], which asks the list to hold every account and key that the block
accessed, with the system calls before and after the transactions.

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#recording-semantics-by-change-type
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)
open EthLib.Execution.Transactions
open AccessListBuilder (Covers Extends extends_refl)

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

/-- A new position keeps every record of the builder. -/
theorem BodyState.beginIndex_extends (body : BodyState) (index : Nat) :
    body.builder.Extends (body.beginIndex index).builder :=
  extends_refl _

/-- A transaction that enters the body extends the builder, which then covers its run. -/
theorem applyTransaction_covers {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    ∃ included out,
      checkInclusion env.chainId env before.gas (.ofBlock before.block) tx = .ok included ∧
      processTransaction env before.block included tx = .ok out ∧
      before.body.builder.Extends after.body.builder ∧ after.body.builder.Covers out.state := by
  unfold applyTransaction at h
  obtain ⟨included, hIncluded, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, hBody, h⟩ := bind_ok_iff.mp h
  have hAfter : after.body = body := by
    dsimp only at h
    split at h <;> (obtain ⟨_, -, h⟩ := bind_ok_iff.mp h; cases h; rfl)
  obtain ⟨hExt, hCovers⟩ := BodyState.join_covers (mapError_ok_iff.mp hBody)
  rw [hAfter]
  exact ⟨included, out, mapError_ok_iff.mp hIncluded, mapError_ok_iff.mp hOut, hExt, hCovers⟩

/-! ## The transactions -/

/-- The fold of the transactions extends the builder, and covers the run of each of them.

Each transaction runs on the output of the fold of the transactions before it. -/
theorem foldlM_applyTransaction_covers {env : BlockEnvironment fork} :
    ∀ (l : List (Transaction × Nat)) (start output : BodyOutput fork),
      l.foldlM (fun before (tx, index) => applyTransaction env index before tx) start =
        .ok output →
      start.body.builder.Extends output.body.builder ∧
        ∀ i (hi : i < l.length), ∃ before included out,
          (l.take i).foldlM (fun before (tx, index) => applyTransaction env index before tx)
            start = .ok before ∧
          checkInclusion env.chainId env before.gas (.ofBlock before.block) l[i].1 =
            .ok included ∧
          processTransaction env before.block included l[i].1 = .ok out ∧
          output.body.builder.Covers out.state
  | [], start, output, h => by
    cases h
    exact ⟨extends_refl _, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | (tx, index) :: l, start, output, h => by
    rw [List.foldlM_cons, bind_ok_iff] at h
    obtain ⟨mid, hmid, h⟩ := h
    obtain ⟨hRest, hAll⟩ := foldlM_applyTransaction_covers l mid output h
    obtain ⟨included, out, hIncluded, hOut, hExt, hCovers⟩ := applyTransaction_covers hmid
    refine ⟨hExt.trans hRest, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨start, included, out, rfl, hIncluded, hOut, hCovers.mono hRest⟩
    | succ i =>
      obtain ⟨before, included', out', hBefore, hIncluded', hOut', hCovers'⟩ :=
        hAll i (Nat.lt_of_succ_lt_succ hi)
      refine ⟨before, included', out', ?_, hIncluded', hOut', hCovers'⟩
      rw [List.take_succ_cons, List.foldlM_cons, hmid]
      exact hBefore

/-- The first `i` transactions with their indices are the transactions of the first `i`. -/
theorem zipIdx_take {α : Type} (l : List α) (i : Nat) : (l.take i).zipIdx = l.zipIdx.take i := by
  apply List.ext_getElem?
  intro n
  simp only [List.getElem?_zipIdx, List.getElem?_take]
  split <;> simp

/-- The builder at the end of the transactions covers the run of each of them.

The transaction at index `i` runs on the output of the transactions before it. -/
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
  obtain ⟨hExt, hAll⟩ := foldlM_applyTransaction_covers _ _ _ h
  refine ⟨hExt, fun i hi => ?_⟩
  obtain ⟨before, included, out, hBefore, hIncluded, hOut, hCovers⟩ :=
    hAll i (by simpa using hi)
  simp only [List.getElem_zipIdx] at hIncluded hOut
  refine ⟨before, included, out, ?_, hIncluded, hOut, hCovers⟩
  unfold applyTransactions
  rw [zipIdx_take]
  exact hBefore

/-! ## The system calls -/

/-- The system calls at the start of a block extend the builder, which then covers each call.

From Dencun, the beacon roots contract runs on the block state before the calls.

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
      exact ⟨extends_refl _, fun h => absurd h hPectra⟩
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

/-- The calls to the request contracts extend the builder, which then covers each call.

From Pectra, each contract of the fork is called, and the call joins the body. -/
theorem readRequests_covers {env : BlockEnvironment fork} {body body' : BodyState}
    {requests : List ByteArray} (h : readRequests env body = .ok (body', requests)) :
    body.builder.Extends body'.builder ∧
      (.pectra ≤ fork → ∀ contract ∈ requestContracts fork, ∃ block out,
        checkedSystemCall env block contract.2 .empty = .ok out ∧
        body'.builder.Covers out.state) := by
  unfold readRequests at h
  split at h
  · rename_i hPectra
    -- Each call extends the builder, and the builder covers each call made so far.
    have step : ∀ (l : List (UInt8 × Address)) (start result : BodyState × List ByteArray),
        l.foldlM (fun (body, requests) (type, target) => do
            let out ← checkedSystemCall env body.block target .empty
            let body ← (body.join out.state).mapError BlockError.state
            return (body, requests ++ requestList type out.output)) start = .ok result →
        start.1.builder.Extends result.1.builder ∧ ∀ contract ∈ l, ∃ block out,
          checkedSystemCall env block contract.2 .empty = .ok out ∧
          result.1.builder.Covers out.state := by
      intro l
      induction l with
      | nil =>
        intro start result h
        cases h
        exact ⟨extends_refl _, by simp⟩
      | cons c l ih =>
        intro start result h
        rw [List.foldlM_cons, bind_ok_iff] at h
        obtain ⟨mid, hmid, h⟩ := h
        obtain ⟨hRest, hAll⟩ := ih mid result h
        obtain ⟨out, hOut, hmid⟩ := bind_ok_iff.mp hmid
        obtain ⟨joined, hJoined, hmid⟩ := bind_ok_iff.mp hmid
        cases hmid
        obtain ⟨hExt, hCovers⟩ := BodyState.join_covers (mapError_ok_iff.mp hJoined)
        refine ⟨hExt.trans hRest, fun contract hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨_, out, hOut, hCovers.mono hRest⟩
        · exact hAll contract hc
    obtain ⟨hExt, hAll⟩ := step _ _ _ h
    exact ⟨hExt, fun _ => hAll⟩
  · rename_i hPectra
    cases h
    exact ⟨extends_refl _, fun h => absurd h hPectra⟩

/-- The requests of a block extend the builder, which then covers each call to a contract. -/
theorem blockRequests_covers {depositContract : Address} {env : BlockEnvironment fork}
    {body body' : BodyState} {logs : List Log} {requests : List ByteArray}
    (h : blockRequests depositContract env body logs = .ok (body', requests)) :
    body.builder.Extends body'.builder ∧
      (.pectra ≤ fork → ∀ contract ∈ requestContracts fork, ∃ block out,
        checkedSystemCall env block contract.2 .empty = .ok out ∧
        body'.builder.Covers out.state) := by
  unfold blockRequests at h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨mid, read⟩, hRead, h⟩ := bind_ok_iff.mp h
    cases h
    exact readRequests_covers hRead
  · rename_i hPectra
    cases h
    exact ⟨extends_refl _, fun h => absurd h hPectra⟩

/-! ## The body -/

/-- The builder at the end of a body covers every call of the body.

The system calls at the start run on the block state after the DAO transfer, if any.

The transactions then run, and each of them is covered as the fold of the transactions says.

From Shapella, the withdrawals then run as one call on the block state after the transactions.

From Pectra, each request contract is then called. -/
theorem applyBody_covers {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ state body txOutput,
      (if daoForkBlock config = some block.header.number then onBlock start (applyDaoFork fork)
        else pure start) = .ok state ∧
      startSystemCalls env block.header.parentHash (.init state) = .ok body ∧
      applyTransactions env body block.transactions = .ok txOutput ∧
      body.builder.Extends output.body.builder ∧
      txOutput.body.builder.Extends output.body.builder ∧
      (∀ hShapella : .shapella ≤ fork, ∃ tx,
        withdrawalState fork txOutput.body.block (block.withdrawals hShapella) = .ok tx ∧
        output.body.builder.Covers tx) ∧
      (.pectra ≤ fork → ∀ contract ∈ requestContracts fork, ∃ block out,
        checkedSystemCall env block contract.2 .empty = .ok out ∧
        output.body.builder.Covers out.state) := by
  unfold applyBody at h
  dsimp only at h
  split at h <;> rename_i hDao
  all_goals
    obtain ⟨state, hState, h⟩ := bind_ok_iff.mp h
    replace hState : (if daoForkBlock config = some block.header.number then
        onBlock start (applyDaoFork fork) else pure start) = .ok state := by
      simpa only [hDao, ↓reduceIte] using hState
    obtain ⟨body, hBody, h⟩ := bind_ok_iff.mp h
    obtain ⟨txOutput, hTx, h⟩ := bind_ok_iff.mp h
    split at h <;> rename_i hShapella
    all_goals first
      | obtain ⟨tx, hTxState, h⟩ := bind_ok_iff.mp h
        have hTxState := mapError_ok_iff.mp hTxState
        obtain ⟨withdrawn, hJoin, h⟩ := bind_ok_iff.mp h
        have hW := BodyState.join_covers (mapError_ok_iff.mp hJoin)
        have withdrawals : txOutput.body.builder.Extends withdrawn.builder ∧
            ∀ hShapella : .shapella ≤ fork, ∃ tx,
              withdrawalState fork txOutput.body.block (block.withdrawals hShapella) = .ok tx ∧
              withdrawn.builder.Covers tx :=
          ⟨hW.1, fun _ => ⟨tx, hTxState, hW.2⟩⟩
      | obtain ⟨withdrawn, hEq, h⟩ := bind_ok_iff.mp h
        have hEq := Except.ok.inj hEq
        have withdrawals : txOutput.body.builder.Extends withdrawn.builder ∧
            ∀ hShapella : .shapella ≤ fork, ∃ tx,
              withdrawalState fork txOutput.body.block (block.withdrawals hShapella) = .ok tx ∧
              withdrawn.builder.Covers tx :=
          ⟨by subst hEq; exact extends_refl _, fun h => absurd h hShapella⟩
    all_goals
      obtain ⟨⟨requested, requests⟩, hRequests, h⟩ := bind_ok_iff.mp h
      dsimp only at h
      obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
      cases h
      obtain ⟨hReqExt, hReqCovers⟩ := blockRequests_covers hRequests
      have hTxExt := withdrawals.1.trans hReqExt
      refine ⟨state, body, txOutput, hState, mapError_ok_iff.mp hBody, hTx,
        (applyTransactions_covers hTx).1.trans hTxExt, hTxExt, fun hS => ?_, hReqCovers⟩
      obtain ⟨tx, hTxState, hCovers⟩ := withdrawals.2 hS
      exact ⟨tx, hTxState, hCovers.mono hReqExt⟩

/-- The builder at the end of a body covers the run of each of its transactions.

The transaction at index `i` runs on the output of the transactions before it. -/
theorem applyBody_covers_transaction {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (h : applyBody config env block start = .ok output) :
    ∃ state body,
      (if daoForkBlock config = some block.header.number then onBlock start (applyDaoFork fork)
        else pure start) = .ok state ∧
      startSystemCalls env block.header.parentHash (.init state) = .ok body ∧
      ∀ i (hi : i < block.transactions.length), ∃ before included out,
        applyTransactions env body (block.transactions.take i) = .ok before ∧
        checkInclusion env.chainId env before.gas (.ofBlock before.block)
          block.transactions[i] = .ok included ∧
        processTransaction env before.block included block.transactions[i] = .ok out ∧
        output.body.builder.Covers out.state := by
  obtain ⟨state, body, txOutput, hState, hBody, hTx, -, hExt, -, -⟩ := applyBody_covers h
  refine ⟨state, body, hState, hBody, fun i hi => ?_⟩
  obtain ⟨before, included, out, hBefore, hIncluded, hOut, hCovers⟩ :=
    (applyTransactions_covers hTx).2 i hi
  exact ⟨before, included, out, hBefore, hIncluded, hOut, hCovers.mono hExt⟩

end EthLib.Execution.Blocks

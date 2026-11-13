module

public import EthLib.Execution.Proofs.Blocks.SystemCall
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Transactions.Codes

/-!
# Proofs: a block never aborts for a missing code

A state holds its codes when the code of each of its accounts is in it.

On such a state, the transition of a block never aborts for a missing code.

The system calls, the transactions and the requests each keep every code available.

The DAO transfer, the withdrawals and the rewards change only balances.

The record of a call in the block access list reads the new code of each account it changed.

That read finds the code, so joining a call to the body never fails.

The checks of the block and of its output never fail with an abort or with an error of the state.

The abort from Hegotá on is for a fork whose rules are not yet specified, not for a missing code.

So a block that passes its transition leaves a state that holds its codes.
-/

@[expose] public section

namespace EthLib.Execution.State

/-- Whether the state before a block holds the code of every account. -/
def State.HasCodes (state : State) : Prop :=
  ∀ address account, state.getAccountOptional address = some account →
    ∃ code, state.getCode account.codeHash = .ok code

/-- A block state with no writes holds every code exactly when its state does. -/
theorem State.hasCodes_ofState_iff (state : State) :
    Transactions.HasCodes (TransactionState.ofBlock ⟨state, ∅, ∅, ∅, ∅⟩) ↔ state.HasCodes := by
  have account : ∀ address, (TransactionState.ofBlock ⟨state, ∅, ∅, ∅, ∅⟩).getAccount address =
      (state.getAccountOptional address).getD EMPTY_ACCOUNT := fun _ => by
    simp [TransactionState.getAccount, TransactionState.getAccountOptional,
      TransactionState.ofBlock]
  have code : ∀ hash, (TransactionState.ofBlock ⟨state, ∅, ∅, ∅, ∅⟩).getCode hash =
      state.getCode hash := fun hash => by
    simp only [TransactionState.getCode, TransactionState.ofBlock, Std.ExtTreeMap.getElem?_empty]
    split
    · rename_i empty
      simp [State.getCode, empty]
    · rfl
  constructor
  · intro available address acc hacc
    obtain ⟨c, hc⟩ := available address
    rw [code, account, hacc] at hc
    exact ⟨c, hc⟩
  · intro available address
    rw [code, account]
    cases hacc : state.getAccountOptional address with
    | none => exact ⟨.empty, by simp [State.getCode, EMPTY_ACCOUNT]⟩
    | some acc => exact available address acc hacc

end EthLib.Execution.State

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (HasCodes Transaction)

variable {fork : Fork}

/-- The record of an account that a call wrote succeeds when the call holds every code. -/
private theorem recordAccountWrite_ok (b : AccessListBuilder) {tx : TransactionState}
    (available : HasCodes tx) {address : Address} {written : Option State.Account}
    (hw : tx.accountWrites[address]? = some written) :
    ∃ b', b.recordAccountWrite tx address written = .ok b' := by
  have account : tx.getAccount address = written.getD State.EMPTY_ACCOUNT := by
    simp [TransactionState.getAccount, TransactionState.getAccountOptional, hw]
  obtain ⟨code, hcode⟩ := available address
  rw [account] at hcode
  unfold AccessListBuilder.recordAccountWrite
  dsimp only
  split <;> simp [hcode, bind, Except.bind, pure, Except.pure]

/-- A call that holds every code joins the body. -/
theorem BodyState.join_ok_of_hasCodes (body : BodyState) {tx : TransactionState}
    (available : HasCodes tx) : ∃ body', body.join tx = .ok body' := by
  have writes : ∀ b : AccessListBuilder, ∃ b', tx.accountWrites.foldlM
      (fun b address written => b.recordAccountWrite tx address written) b = .ok b' := by
    intro b
    rw [Std.ExtTreeMap.foldlM_eq_foldlM_toList]
    refine foldlM_exists_ok_of_invariant (fun _ => True) (fun acc x hx _ => ?_) b trivial
    obtain ⟨r, hr⟩ :=
      recordAccountWrite_ok acc available (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hx)
    exact ⟨r, hr, trivial⟩
  unfold BodyState.join AccessListBuilder.recordTransaction
  obtain ⟨b', hb'⟩ := writes (tx.storageReads.foldl
    (fun b address keys => b.record address fun r =>
      { r with storageReads := r.storageReads.insertMany keys.toList })
    (tx.accountReads.foldl (fun b address => b.record address id) body.builder))
  simp only [hb', bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- A call that holds every code leaves a body that holds every code once it joins. -/
theorem BodyState.hasCodes_join {body body' : BodyState} {tx : TransactionState}
    (h : body.join tx = .ok body') (available : HasCodes tx) :
    HasCodes (.ofBlock body'.block) := by
  obtain ⟨_, -, rfl⟩ := BodyState.join_eq_ok h
  exact Transactions.hasCodes_incorporateTxIntoBlock available

/-- A system call on a block that holds every code keeps the code of each account available. -/
theorem systemCall_hasCodes {env : BlockEnvironment fork} {block : BlockState} {target : Address}
    {data : ByteArray} {out : SystemCallOutput} (available : HasCodes (.ofBlock block))
    (h : systemCall env block target data = .ok out) : HasCodes out.state := by
  simp only [systemCall] at h
  split at h <;>
  · obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact Transactions.processMessageCall_hasCodes available hcall

/-- A system call on a block that holds every code never aborts for a missing code. -/
theorem systemCall_ne_missingCode (env : BlockEnvironment fork) {block : BlockState}
    (target : Address) (data : ByteArray) (available : HasCodes (.ofBlock block))
    (codeHash : Hash32) :
    systemCall env block target data ≠ .error (.state (.missingCode codeHash)) := by
  intro h
  simp only [systemCall] at h
  split at h <;>
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact Transactions.processMessageCall_ne_missingCode available codeHash h
    · cases h

/-- A transaction that enters the body keeps the code of each account available. -/
private theorem applyTransaction_hasCodes {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (available : HasCodes (.ofBlock before.block))
    (h : applyTransaction env index before tx = .ok after) :
    HasCodes (.ofBlock after.block) := by
  obtain ⟨included, out, -, hout, -, -, hjoin⟩ := applyTransaction_eq_ok h
  exact BodyState.hasCodes_join hjoin (Transactions.processTransaction_hasCodes hout available).1

/-- The transactions of a block keep the code of each account available. -/
private theorem applyTransactions_hasCodes {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (available : HasCodes (.ofBlock body.block))
    (h : applyTransactions env body transactions = .ok output) :
    HasCodes (.ofBlock output.block) :=
  (applyTransactions_steps
    (fun a b : BodyOutput fork => HasCodes (.ofBlock a.block) → HasCodes (.ofBlock b.block))
    (fun _ => id) (fun hab hbc fit => hbc (hab fit))
    (fun h fit => applyTransaction_hasCodes fit h) h).1 available

/-- A system call that joins the body keeps the code of each account available. -/
private theorem join_systemCall_hasCodes {env : BlockEnvironment fork} {body body' : BodyState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (available : HasCodes (.ofBlock body.block))
    (hcall : systemCall env body.block target data = .ok out)
    (hjoin : body.join out.state = .ok body') : HasCodes (.ofBlock body'.block) :=
  BodyState.hasCodes_join hjoin (systemCall_hasCodes available hcall)

/-- The reads of the request contracts keep the code of each account available. -/
private theorem readRequests_hasCodes {env : BlockEnvironment fork} {body : BodyState}
    {result : BodyState × List ByteArray} (available : HasCodes (.ofBlock body.block))
    (h : readRequests env body = .ok result) : HasCodes (.ofBlock result.1.block) := by
  by_cases hp : .pectra ≤ fork
  · rw [readRequests_of_pectra hp] at h
    refine foldlM_ok_invariant
      (fun st : BodyState × List ByteArray => HasCodes (.ofBlock st.1.block)) ?_ available h
    intro st c st' fit hstep
    obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok hstep
    exact join_systemCall_hasCodes fit (checkedSystemCall_ok hout).2.1 hjoin
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hp)] at h
    cases h
    exact available

/-- The system calls at the start of a block keep the code of each account available. -/
private theorem startSystemCalls_hasCodes {env : BlockEnvironment fork} {parentHash : Hash32}
    {body body' : BodyState} (available : HasCodes (.ofBlock body.block))
    (h : startSystemCalls env parentHash body = .ok body') :
    HasCodes (.ofBlock body'.block) := by
  obtain ⟨mid, hFirst, hNoFirst, hSecond, hNoSecond⟩ := startSystemCalls_eq_ok h
  have first : HasCodes (.ofBlock mid.block) := by
    by_cases hd : .dencun ≤ fork
    · obtain ⟨out, hout, hjoin⟩ := hFirst hd
      exact join_systemCall_hasCodes available hout hjoin
    · rw [hNoFirst hd]
      exact available
  by_cases hp : .pectra ≤ fork
  · obtain ⟨out, hout, hjoin⟩ := hSecond hp
    exact join_systemCall_hasCodes first hout hjoin
  · rw [hNoSecond hp]
    exact first

/-- The requests of a block keep the code of each account available. -/
private theorem blockRequests_hasCodes {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} {logs : List Log} {result : BodyState × List ByteArray}
    (available : HasCodes (.ofBlock body.block))
    (h : blockRequests depositContract env body logs = .ok result) :
    HasCodes (.ofBlock result.1.block) := by
  obtain ⟨hNoPectra, hPectra⟩ := blockRequests_eq_ok h
  by_cases hp : .pectra ≤ fork
  · obtain ⟨_, read, -, hread, rfl⟩ := hPectra hp
    exact readRequests_hasCodes (result := read) available
      ((readRequests_of_pectra hp).trans hread)
  · rw [hNoPectra hp]
    exact available

/-- A step whose result holds every code gives a block state that holds every code. -/
private theorem onBlock_hasCodes {block block' : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (keeps : ∀ tx, step (.ofBlock block) = .ok tx → HasCodes tx)
    (h : onBlock block step = .ok block') : HasCodes (.ofBlock block') := by
  obtain ⟨tx, htx, rfl⟩ := onBlock_eq_ok h
  exact Transactions.hasCodes_incorporateTxIntoBlock (keeps tx htx)

/-- The DAO transfer keeps the code of each account available. -/
private theorem daoTransfer_hasCodes {config : ChainConfig} {number : Nat}
    {start state : BlockState} (available : HasCodes (.ofBlock start))
    (h : daoTransfer config fork number start = .ok state) : HasCodes (.ofBlock state) := by
  unfold daoTransfer at h
  split at h
  · refine onBlock_hasCodes (fun tx hdao => ?_) h
    exact foldlM_ok_invariant HasCodes
      (fun _ _ _ fit step => Transactions.hasCodes_moveEther step fit) available hdao
  · cases h
    exact available

/-- The rewards keep the code of each account available. -/
private theorem payRewards_hasCodes {tx tx' : TransactionState} {coinbase : Address}
    {number : Nat} {ommers : List (Address × Nat)} (available : HasCodes tx)
    (h : payRewards fork tx coinbase number ommers = .ok tx') : HasCodes tx' := by
  unfold payRewards at h
  split at h
  · cases h
    exact available
  · obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    exact foldlM_ok_invariant HasCodes
      (fun _ _ _ fit step => Transactions.hasCodes_createEther step fit)
      (Transactions.hasCodes_createEther hmid available) h

/-- The body of a block keeps the code of each account available. -/
theorem applyBody_hasCodes {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} {output : BlockOutput fork}
    (available : HasCodes (.ofBlock start)) (h : applyBody config env block start = .ok output) :
    HasCodes (.ofBlock output.block) := by
  obtain ⟨_, body, txs, withdrawn, requested, hdao, hsys, htxs, hWithdrawn, hStays, hreq, hrew,
    -⟩ := applyBody_eq_ok h
  have codesTxs := applyTransactions_hasCodes
    (startSystemCalls_hasCodes (daoTransfer_hasCodes available hdao) hsys) htxs
  have codesWithdrawn : HasCodes (.ofBlock withdrawn.block) := by
    by_cases hShapella : .shapella ≤ fork
    · obtain ⟨_, htx, hj⟩ := hWithdrawn hShapella
      exact BodyState.hasCodes_join hj (foldlM_ok_invariant HasCodes
        (fun _ _ _ fit step => Transactions.hasCodes_createEther step fit) codesTxs htx)
    · rw [hStays hShapella]
      exact codesTxs
  exact onBlock_hasCodes (fun _ hp => payRewards_hasCodes
    (blockRequests_hasCodes (result := (requested, _)) codesWithdrawn hreq) hp) hrew

/-! ## Failures with no missing code -/

/-- Whether an error of a block is an abort or a failure of the state for a missing code. -/
private def Missing (e : BlockError) : Prop :=
  ∃ c, e = .aborted (.state (.missingCode c)) ∨ e = .state (.missingCode c)

/-- Every failure of a result meets a property. -/
private def Fails {α : Type} (P : BlockError → Prop) (r : Except BlockError α) : Prop :=
  ∀ e, r = .error e → P e

/-- A success has no failure. -/
private theorem Fails.ok {α : Type} {P : BlockError → Prop} (a : α) :
    Fails P (.ok a : Except BlockError α) :=
  fun _ h => by cases h

/-- A pure result has no failure. -/
private theorem Fails.pure {α : Type} {P : BlockError → Prop} (a : α) :
    Fails P (Pure.pure a : Except BlockError α) :=
  fun _ h => by cases h

/-- A failure with an error that meets the property meets it. -/
private theorem Fails.error {α : Type} {P : BlockError → Prop} {e : BlockError} (h : P e) :
    Fails P (.error e : Except BlockError α) :=
  fun _ he => by cases he; exact h

/-- A throw of an error that meets the property meets it. -/
private theorem Fails.throw {α : Type} {P : BlockError → Prop} {e : BlockError} (h : P e) :
    Fails P (MonadExcept.throw e : Except BlockError α) :=
  fun _ he => by cases he; exact h

/-- A sequence meets the property when its first part does, and its rest after it. -/
private theorem Fails.bind {α β : Type} {P : BlockError → Prop} {x : Except BlockError α}
    {f : α → Except BlockError β} (hx : Fails P x) (hf : ∀ a, x = .ok a → Fails P (f a)) :
    Fails P (x >>= f) := by
  intro e h
  rcases Base.bind_eq_error h with h | ⟨a, ha, h⟩
  · exact hx e h
  · exact hf a ha e h

/-- A map of a result that meets the property meets it. -/
private theorem Fails.map {α β : Type} {P : BlockError → Prop} {x : Except BlockError α}
    (f : α → β) (hx : Fails P x) : Fails P (f <$> x) := by
  intro e h
  cases hx' : x with
  | error e' => rw [hx'] at h; cases h; exact hx e hx'
  | ok a => rw [hx'] at h; cases h

/-- A change of error meets the property when each changed failure does. -/
private theorem Fails.mapError {ε α : Type} {P : BlockError → Prop} {x : Except ε α}
    {f : ε → BlockError} (hf : ∀ e, x = .error e → P (f e)) : Fails P (x.mapError f) := by
  intro e h
  cases hx : x with
  | error e' => rw [hx] at h; cases h; exact hf e' hx
  | ok a => rw [hx] at h; cases h

/-- A fold whose steps fail only with errors of a property fails only with them.

The steps need only do so from an accumulator that holds an invariant. -/
private theorem foldlM_error_of_step {ε α β : Type} {g : β → α → Except ε β} (I : β → Prop)
    (Q : ε → Prop) (keep : ∀ b x b', I b → g b x = .ok b' → I b')
    (step : ∀ b x e, I b → g b x = .error e → Q e) :
    ∀ (xs : List α) (b : β) (e : ε), I b → xs.foldlM g b = .error e → Q e
  | [], _, _, _, h => by cases h
  | x :: xs, b, e, hb, h => by
    rw [List.foldlM_cons] at h
    rcases Base.bind_eq_error h with h | ⟨b', hb', h⟩
    · exact step b x e hb h
    · exact foldlM_error_of_step I Q keep step xs b' e (keep b x b' hb hb') h

/-- A move of ether never fails for a missing code. -/
private theorem moveEther_ne_missingCode (tx : TransactionState) (sender recipient : Address)
    (amount : U256) (c : Hash32) :
    tx.moveEther fork sender recipient amount ≠ .error (.missingCode c) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
  · exact modifyState_ne_missingCode
      (fun account c h => by unfold State.Account.debit at h; split at h <;> cases h) c h
  · exact modifyState_ne_missingCode
      (fun account c h => by unfold State.Account.credit at h; split at h <;> cases h) c h

/-- A creation of ether never fails for a missing code. -/
private theorem createEther_ne_missingCode (tx : TransactionState) (address : Address)
    (amount : U256) (c : Hash32) :
    tx.createEther fork address amount ≠ .error (.missingCode c) :=
  modifyState_ne_missingCode
    (fun account c h => by unfold State.Account.credit at h; split at h <;> cases h) c

/-- A fold whose steps never fail for a missing code never fails for one. -/
private theorem foldlM_ne_missingCode {α β : Type} {g : β → α → Except State.StateError β}
    (step : ∀ b x c, g b x ≠ .error (.missingCode c)) (xs : List α) (b : β) (c : Hash32) :
    xs.foldlM g b ≠ .error (.missingCode c) := fun h =>
  foldlM_error_of_step (fun _ => True) (· ≠ .missingCode c) (fun _ _ _ _ _ => trivial)
    (fun b x _ _ he => by rintro rfl; exact step b x c he) xs b _ trivial h rfl

/-- The rewards never fail for a missing code. -/
private theorem payRewards_ne_missingCode (tx : TransactionState) (coinbase : Address)
    (number : Nat) (ommers : List (Address × Nat)) (c : Hash32) :
    payRewards fork tx coinbase number ommers ≠ .error (.missingCode c) := by
  unfold payRewards
  split
  · nofun
  · intro h
    rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
    · exact createEther_ne_missingCode _ _ _ c h
    · exact foldlM_ne_missingCode (fun _ _ c => createEther_ne_missingCode _ _ _ c) _ _ c h

/-- The withdrawals never fail for a missing code. -/
private theorem withdrawalState_ne_missingCode (block : BlockState) (withdrawals : List Withdrawal)
    (c : Hash32) : withdrawalState fork block withdrawals ≠ .error (.missingCode c) :=
  foldlM_ne_missingCode (fun _ _ c => createEther_ne_missingCode _ _ _ c) _ _ c

/-- The DAO transfer never fails for a missing code. -/
private theorem applyDaoFork_ne_missingCode (tx : TransactionState) (c : Hash32) :
    applyDaoFork fork tx ≠ .error (.missingCode c) :=
  foldlM_ne_missingCode (fun _ _ c => moveEther_ne_missingCode _ _ _ _ c) _ _ c

/-- An error of the state that is never a missing code gives no missing code of the block. -/
private theorem Fails.mapError_state {α : Type} {x : Except State.StateError α}
    (h : ∀ c, x ≠ .error (.missingCode c)) : Fails (¬Missing ·) (x.mapError .state) :=
  Fails.mapError fun e he ⟨c, hc⟩ => by
    rcases hc with hc | hc
    · cases hc
    · cases hc
      exact h c he

/-- An abort with no missing code is no missing code of the block. -/
private theorem Fails.mapError_aborted {α : Type} {x : Except EvmError α}
    (h : ∀ c, x ≠ .error (.state (.missingCode c))) : Fails (¬Missing ·) (x.mapError .aborted) :=
  Fails.mapError fun e he ⟨c, hc⟩ => by
    rcases hc with hc | hc
    · cases hc
      exact h c he
    · cases hc

/-- A call that holds every code joins the body, so the join has no failure. -/
private theorem Fails.join {P : BlockError → Prop} (body : BodyState) {tx : TransactionState}
    (available : HasCodes tx) : Fails P ((body.join tx).mapError .state) := by
  obtain ⟨b, hb⟩ := BodyState.join_ok_of_hasCodes body available
  intro e h
  rw [hb] at h
  cases h

/-- A step on a block state that never fails for a missing code gives no missing code. -/
private theorem Fails.onBlock {block : BlockState}
    {step : TransactionState → Except State.StateError TransactionState}
    (h : ∀ c, step (.ofBlock block) ≠ .error (.missingCode c)) :
    Fails (¬Missing ·) (onBlock block step) :=
  Fails.bind (Fails.mapError_state h) fun _ _ => Fails.pure _

/-- The DAO transfer never fails for a missing code, as a failure of the block. -/
private theorem fails_daoTransfer (config : ChainConfig) (number : Nat) (start : BlockState) :
    Fails (¬Missing ·) (daoTransfer config fork number start) := by
  unfold daoTransfer
  split
  · exact Fails.onBlock (applyDaoFork_ne_missingCode _)
  · exact Fails.pure _

/-- A system call that joins a body that holds every code never aborts for a missing code. -/
private theorem systemCall_join_ne_missingCode {env : BlockEnvironment fork} {body : BodyState}
    {target : Address} {data : ByteArray} (available : HasCodes (.ofBlock body.block))
    (c : Hash32) :
    (do
      let out ← systemCall env body.block target data
      (body.join out.state).mapError EvmError.state : Except EvmError BodyState) ≠
      .error (.state (.missingCode c)) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨out, hout, h⟩
  · exact systemCall_ne_missingCode env target data available c h
  · obtain ⟨b, hb⟩ := BodyState.join_ok_of_hasCodes body (systemCall_hasCodes available hout)
    rw [hb] at h
    cases h

/-- The system calls at the start of a block never abort for a missing code. -/
private theorem startSystemCalls_ne_missingCode {env : BlockEnvironment fork}
    {parentHash : Hash32} {body : BodyState} (available : HasCodes (.ofBlock body.block))
    (c : Hash32) :
    startSystemCalls env parentHash body ≠ .error (.state (.missingCode c)) := by
  have second : ∀ mid : BodyState, HasCodes (.ofBlock mid.block) →
      (if Fork.pectra ≤ fork then do
        let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
        Except.mapError EvmError.state (mid.join out.state)
      else pure mid) ≠ .error (.state (.missingCode c)) := by
    intro mid codes h
    split at h
    · exact systemCall_join_ne_missingCode codes c h
    · cases h
  intro h
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨out, hout, h⟩
    · exact systemCall_ne_missingCode env _ _ available c h
    · rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
      · obtain ⟨b, hb⟩ := BodyState.join_ok_of_hasCodes body (systemCall_hasCodes available hout)
        rw [hb] at h
        cases h
      · exact second mid (join_systemCall_hasCodes available hout (mapError_ok_iff.mp hmid)) h
  · rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
    · cases h
    · cases hmid
      exact second _ available h

/-- A transaction on a body that holds every code never fails for a missing code. -/
private theorem fails_applyTransaction {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} (tx : Transaction) (available : HasCodes (.ofBlock before.block)) :
    Fails (¬Missing ·) (applyTransaction env index before tx) := by
  unfold applyTransaction
  refine Fails.bind (Fails.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
    fun included _ => ?_
  refine Fails.bind (Fails.mapError_aborted
    (Transactions.processTransaction_ne_missingCode available)) fun out hout => ?_
  have codes := (Transactions.processTransaction_hasCodes (mapError_ok_iff.mp hout) available).1
  refine Fails.bind (Fails.join _ codes) fun body _ => ?_
  dsimp only
  split
  · exact Fails.bind (Fails.pure _) fun _ _ => Fails.pure _
  · exact Fails.bind (Fails.map _ (Fails.mapError fun _ _ ⟨_, h⟩ => by
      rcases h with h | h <;> cases h)) fun _ _ => Fails.pure _

/-- The transactions on a body that holds every code never fail for a missing code. -/
private theorem fails_applyTransactions {env : BlockEnvironment fork} {body : BodyState}
    (transactions : List Transaction) (available : HasCodes (.ofBlock body.block)) :
    Fails (¬Missing ·) (applyTransactions env body transactions) := fun e h =>
  foldlM_error_of_step (fun before : BodyOutput fork => HasCodes (.ofBlock before.block))
    (¬Missing ·) (fun _ _ _ fit h => applyTransaction_hasCodes fit h)
    (fun _ _ e fit h => fails_applyTransaction _ fit e h) transactions.zipIdx
    ⟨body, .zero, 0, [], []⟩ e available h

/-- A checked system call on a block that holds every code never fails for a missing code. -/
private theorem fails_checkedSystemCall {env : BlockEnvironment fork} {block : BlockState}
    (target : Address) (data : ByteArray) (available : HasCodes (.ofBlock block)) :
    Fails (¬Missing ·) (checkedSystemCall env block target data) := by
  obtain ⟨code, hcode⟩ := available target
  have hat : codeAt block target = .ok code := by
    simp only [codeAt, hcode]
    rfl
  unfold checkedSystemCall
  rw [hat]
  refine Fails.bind (Fails.ok _) fun _ _ => ?_
  have rest : Fails (¬Missing ·) (do
      let out ← (systemCall env block target data).mapError BlockError.aborted
      match out.error with
      | some error => throw (BlockError.systemCallFailed target error)
      | none => pure out) := by
    refine Fails.bind
      (Fails.mapError_aborted (systemCall_ne_missingCode env target data available))
      fun _ _ => ?_
    split
    · exact Fails.throw fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
    · exact Fails.pure _
  dsimp only
  split
  · exact Fails.bind (Fails.throw fun ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => rest
  · exact rest

/-- A read of a request contract on a body that holds every code never fails for a missing code. -/
private theorem fails_readRequest {env : BlockEnvironment fork}
    {state : BodyState × List ByteArray} (contract : UInt8 × Address)
    (available : HasCodes (.ofBlock state.1.block)) :
    Fails (¬Missing ·) (readRequest env state contract) := by
  unfold readRequest
  refine Fails.bind (fails_checkedSystemCall _ _ available) fun out hout => ?_
  refine Fails.bind (Fails.join _
    (systemCall_hasCodes available (checkedSystemCall_ok hout).2.1)) fun _ _ => Fails.pure _

/-- The request reads on a body that holds every code never fail for a missing code. -/
private theorem fails_readRequests {env : BlockEnvironment fork} {body : BodyState}
    (available : HasCodes (.ofBlock body.block)) : Fails (¬Missing ·) (readRequests env body) := by
  unfold readRequests
  split
  · intro e h
    refine foldlM_error_of_step
      (fun st : BodyState × List ByteArray => HasCodes (.ofBlock st.1.block)) (¬Missing ·)
      (fun st c st' fit hstep => ?_) (fun _ c e fit h => fails_readRequest c fit e h) _
      (body, []) e available h
    obtain ⟨out, hout, hjoin, -⟩ := readRequest_eq_ok hstep
    exact join_systemCall_hasCodes fit (checkedSystemCall_ok hout).2.1 hjoin
  · exact Fails.ok _

/-- The requests of a body that holds every code never fail for a missing code. -/
private theorem fails_blockRequests {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} (logs : List Log) (available : HasCodes (.ofBlock body.block)) :
    Fails (¬Missing ·) (blockRequests depositContract env body logs) := by
  unfold blockRequests
  split
  · refine Fails.bind (Fails.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => ?_
    refine Fails.bind (fails_readRequests available) fun r _ => ?_
    exact Fails.pure _
  · exact Fails.pure _

/-- The hash of the block access list never fails for a missing code. -/
private theorem fails_accessListHashOf (body : BodyState) (gasLimit : Nat) :
    Fails (¬Missing ·) (accessListHashOf fork body gasLimit) := by
  unfold accessListHashOf
  split
  · refine Fails.bind (Fails.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => ?_
    exact Fails.map _ (Fails.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
  · exact Fails.pure _

/-- The body of a block on a block state that holds every code never aborts for a missing code.

Nor does it fail with that error outside a call. -/
theorem applyBody_ne_missingCode (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) {start : BlockState} (available : HasCodes (.ofBlock start))
    (codeHash : Hash32) :
    applyBody config env block start ≠ .error (.aborted (.state (.missingCode codeHash))) ∧
      applyBody config env block start ≠ .error (.state (.missingCode codeHash)) := by
  have fails : Fails (¬Missing ·) (applyBody config env block start) := by
    unfold applyBody
    refine Fails.bind (fails_daoTransfer _ _ _) fun state hstate => ?_
    have c1 := daoTransfer_hasCodes available hstate
    refine Fails.bind (Fails.mapError_aborted
      (startSystemCalls_ne_missingCode (body := .init state) c1)) fun body hbody => ?_
    have c2 := startSystemCalls_hasCodes c1 (mapError_ok_iff.mp hbody)
    refine Fails.bind (fails_applyTransactions _ c2) fun output houtput => ?_
    have c3 := applyTransactions_hasCodes c2 houtput
    dsimp only
    split
    · refine Fails.bind (Fails.mapError_state (withdrawalState_ne_missingCode _ _))
        fun tx htx => ?_
      have ctx : HasCodes tx := foldlM_ok_invariant HasCodes
        (fun _ _ _ fit step => Transactions.hasCodes_createEther step fit) c3
        (mapError_ok_iff.mp htx)
      refine Fails.bind (Fails.join _ ctx) fun b hb => ?_
      have cb := BodyState.hasCodes_join (mapError_ok_iff.mp hb) ctx
      refine Fails.bind (fails_blockRequests _ cb) fun r _ => ?_
      obtain ⟨requested, requests⟩ := r
      refine Fails.bind (Fails.onBlock fun c => payRewards_ne_missingCode _ _ _ _ c)
        fun _ _ => ?_
      exact Fails.bind (fails_accessListHashOf _ _) fun _ _ => Fails.pure _
    · refine Fails.bind (Fails.pure _) fun b hb => ?_
      cases hb
      refine Fails.bind (fails_blockRequests _ c3) fun r _ => ?_
      obtain ⟨requested, requests⟩ := r
      refine Fails.bind (Fails.onBlock fun c => payRewards_ne_missingCode _ _ _ _ c)
        fun _ _ => ?_
      exact Fails.bind (fails_accessListHashOf _ _) fun _ _ => Fails.pure _
  exact ⟨fun h => fails _ h ⟨codeHash, .inl rfl⟩, fun h => fails _ h ⟨codeHash, .inr rfl⟩⟩

/-- Whether an error of a block is neither an abort nor an error of the state. -/
private def Plain (e : BlockError) : Prop :=
  (∀ error, e ≠ .aborted error) ∧ ∀ error, e ≠ .state error

/-- The first failure of a list of checks is one of their errors. -/
private theorem fails_firstFailure {P : BlockError → Prop} :
    ∀ (l : List (Bool × BlockError)), (∀ x ∈ l, P x.2) → Fails P (firstFailure l)
  | [], _ => Fails.ok _
  | (b, e) :: rest, h => by
    unfold firstFailure
    split
    · exact fails_firstFailure rest fun x hx => h x (List.mem_cons_of_mem _ hx)
    · exact Fails.error (h (b, e) List.mem_cons_self)

/-- The checks of a header against its parent fail with no abort and no error of the state. -/
private theorem plain_headerChecks {parentFork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule) :
    ∀ x ∈ headerChecks hFork parent header schedule, Plain x.2 := by
  unfold headerChecks
  dsimp only
  simp only [List.forall_mem_append, List.forall_mem_cons]
  and_intros
  all_goals repeat' split
  all_goals simp [Plain]

/-- A check of a header against its parent fails with no abort and no error of the state. -/
private theorem fails_validateHeader {parentFork : Fork} (hFork : parentFork ≤ fork)
    (parent : Header parentFork) (header : Header fork)
    (schedule : Since .dencun fork BlobSchedule) :
    Fails Plain (validateHeader hFork parent header schedule) := by
  unfold validateHeader
  refine Fails.bind (fails_firstFailure _ (plain_headerChecks hFork parent header schedule))
    fun _ _ => ?_
  split
  · exact Fails.mapError fun _ _ => ⟨fun _ => nofun, fun _ => nofun⟩
  · exact Fails.pure _

/-- The checks of a block before its body never fail with an abort or an error of the state. -/
theorem checkBlock_eq_error {config : ChainConfig} {checkSeal : Bool} {recent : List RecentBlock}
    {block : Block fork Transaction} {e : BlockError}
    (h : checkBlock config checkSeal recent block = .error e) :
    (∀ error, e ≠ .aborted error) ∧ ∀ error, e ≠ .state error := by
  have fails : Fails Plain (checkBlock config checkSeal recent block) := by
    unfold checkBlock
    refine Fails.bind ?_ fun items _ => ?_
    · unfold bodyItems
      exact Fails.bind (Fails.mapError fun _ _ => ⟨fun _ => nofun, fun _ => nofun⟩)
        fun _ _ => Fails.pure _
    refine Fails.bind ?_ fun _ _ => ?_
    · unfold validateBlockSize
      split
      · refine Fails.bind (Fails.mapError fun _ _ => ⟨fun _ => nofun, fun _ => nofun⟩)
          fun _ _ => fails_firstFailure _ ?_
        simp [Plain]
      · exact Fails.ok _
    have ommers : Fails Plain (if fork < .paris then
        (validateOmmers config checkSeal recent block.header block.ommers).mapError .ommers
      else if block.ommers.isEmpty = true then pure () else throw .ommersAfterParis) := by
      split
      · exact Fails.mapError fun _ _ => ⟨fun _ => nofun, fun _ => nofun⟩
      · split
        · exact Fails.pure _
        · exact Fails.throw ⟨fun _ => nofun, fun _ => nofun⟩
    split
    · dsimp only
      split
      · split
        · refine Fails.bind (fails_validateHeader _ _ _ _) fun _ _ => ?_
          split
          · exact ommers
          · exact Fails.bind (Fails.throw ⟨fun _ => nofun, fun _ => nofun⟩) fun _ _ => ommers
        · refine Fails.bind (fails_firstFailure _ (plain_headerChecks _ _ _ _)) fun _ _ => ?_
          split
          · exact ommers
          · exact Fails.bind (Fails.throw ⟨fun _ => nofun, fun _ => nofun⟩) fun _ _ => ommers
      · refine Fails.bind (Fails.throw ⟨fun _ => nofun, fun _ => nofun⟩) fun _ _ => ?_
        split
        · exact ommers
        · exact Fails.bind (Fails.throw ⟨fun _ => nofun, fun _ => nofun⟩) fun _ _ => ommers
    · exact Fails.throw ⟨fun _ => nofun, fun _ => nofun⟩
  exact fails e h

/-- A block that passes its transition leaves a state that holds every code.

The state before the block must hold every code. -/
theorem stateTransition_hasCodes {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (available : chain.state.HasCodes)
    (h : stateTransition chain block checkSeal = .ok post) : post.HasCodes := by
  obtain ⟨-, -, -, _, output, _, -, hbody, -, -, rfl⟩ := stateTransition_eq_ok h
  have codes := applyBody_hasCodes ((State.State.hasCodes_ofState_iff _).mpr available) hbody
  intro address account hacc
  obtain ⟨code, hcode⟩ := codes address
  rw [State.BlockState.getAccountOptional_applyChanges] at hacc
  rw [State.BlockState.getCode_applyChanges]
  have : (TransactionState.ofBlock output.block).getAccount address = account := by
    simp [TransactionState.getAccount, hacc]
  rw [this] at hcode
  exact ⟨code, hcode⟩

/-- The transition of a block never aborts for a missing code, on a state that holds every code.

Nor does it fail with that error outside a call. -/
theorem stateTransition_ne_missingCode (chain : BlockChain) (block : Block fork Transaction)
    (checkSeal : Bool) (available : chain.state.HasCodes) (codeHash : Hash32) :
    stateTransition chain block checkSeal ≠ .error (.aborted (.state (.missingCode codeHash))) ∧
      stateTransition chain block checkSeal ≠ .error (.state (.missingCode codeHash)) := by
  have plain : ∀ e, Plain e → ¬Missing e := by
    rintro e ⟨ha, hs⟩ ⟨c, h | h⟩
    · exact ha _ h
    · exact hs _ h
  have fails : Fails (¬Missing ·) (stateTransition chain block checkSeal) := by
    have rest : Fails (¬Missing ·) (do
        checkBlock chain.config checkSeal chain.recent block
        let result ← runBody chain block
        firstFailure (outputChecks block.header result.output result.roots)
        pure result.post : Except BlockError State) := by
      refine Fails.bind (fun e h => plain e (checkBlock_eq_error h)) fun _ _ => ?_
      refine Fails.bind ?_ fun result _ => ?_
      · unfold runBody
        refine Fails.bind ?_ fun hashes _ => ?_
        · unfold recentHashes
          dsimp only
          split
          · exact Fails.pure _
          · exact Fails.bind (Fails.mapError fun _ _ => plain _ ⟨fun _ => nofun, fun _ => nofun⟩)
              fun _ _ => Fails.pure _
        refine Fails.bind (fun e h => ?_) fun output _ => ?_
        · have body := applyBody_ne_missingCode chain.config
            (blockEnvironment chain.config hashes block.header) block
            ((State.State.hasCodes_ofState_iff _).mpr available)
          rintro ⟨c, h' | h'⟩ <;> subst h'
          · exact (body c).1 h
          · exact (body c).2 h
        refine Fails.bind ?_ fun _ _ => Fails.pure _
        unfold outputRoots
        refine Fails.bind (Fails.mapError fun _ _ => plain _ ⟨fun _ => nofun, fun _ => nofun⟩)
          fun _ _ => ?_
        refine Fails.bind (Fails.mapError fun _ _ => plain _ ⟨fun _ => nofun, fun _ => nofun⟩)
          fun _ _ => ?_
        refine Fails.bind (Fails.mapError fun _ _ => plain _ ⟨fun _ => nofun, fun _ => nofun⟩)
          fun _ _ => ?_
        refine Fails.bind ?_ fun _ _ => Fails.pure _
        unfold withdrawalsRootOf
        split
        · exact Fails.map _ (Fails.mapError fun _ _ => plain _ ⟨fun _ => nofun, fun _ => nofun⟩)
        · exact Fails.ok _
      refine Fails.bind (fails_firstFailure _ ?_) fun _ _ => Fails.pure _
      unfold outputChecks
      dsimp only
      simp only [List.forall_mem_append, List.forall_mem_cons]
      and_intros
      all_goals repeat' split
      all_goals simp [Missing]
    unfold stateTransition
    dsimp only
    split
    · refine Fails.bind (Fails.throw ?_) fun _ _ => ?_
      · rintro ⟨c, h | h⟩ <;> cases h
      split
      · exact rest
      · exact Fails.bind (Fails.throw (plain _ ⟨fun _ => nofun, fun _ => nofun⟩)) fun _ _ => rest
    · split
      · exact rest
      · exact Fails.bind (Fails.throw (plain _ ⟨fun _ => nofun, fun _ => nofun⟩)) fun _ _ => rest
  exact ⟨fun h => fails _ h ⟨codeHash, .inl rfl⟩, fun h => fails _ h ⟨codeHash, .inr rfl⟩⟩

end EthLib.Execution.Blocks

module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Transactions.Funded

/-!
# Proofs: no block fails with the state error for a balance below an amount

The DAO transfer moves the whole balance of each account it drains.

A system call moves no value.

Each transaction runs only once it passes its checks on the state it runs on.

Withdrawals and rewards create ether, and take none.

So the transition of a block never fails with the state error for a short balance, on any state.

A sender short of its most costly fee makes the block invalid at its inclusion check instead.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction getCode_ne_insufficientBalance
  modifyState_ne_insufficientBalance)

variable {fork : Fork}

/-! ## Changes of the state with no short balance -/

/-- Whether an error of a block is a short balance, in a call or outside one. -/
private def Short (e : BlockError) : Prop :=
  ∃ a, e = .aborted (.state (.insufficientBalance a)) ∨ e = .state (.insufficientBalance a)

/-- A credit of an account never fails for a short balance. -/
private theorem credit_ne_insufficientBalance (address : Address) (amount : U256)
    (other : Address) (account : State.Account) :
    State.Account.credit address amount account ≠ .error (.insufficientBalance other) := by
  intro h
  unfold State.Account.credit at h
  split at h <;> cases h

/-- A creation of ether never fails for a short balance. -/
private theorem createEther_ne_insufficientBalance (tx : TransactionState) (address : Address)
    (amount : U256) (other : Address) :
    tx.createEther fork address amount ≠ .error (.insufficientBalance other) :=
  modifyState_ne_insufficientBalance (credit_ne_insufficientBalance _ _ _)

/-- A move of the whole balance of an account never fails for a short balance. -/
private theorem moveEther_whole_ne_insufficientBalance (tx : TransactionState)
    (sender recipient other : Address) :
    tx.moveEther fork sender recipient (tx.getAccount sender).balance ≠
      .error (.insufficientBalance other) := by
  intro h
  unfold State.TransactionState.moveEther at h
  rcases State.TransactionState.modifyState_debit fork tx sender (tx.getAccount sender).balance
    with ⟨hlt, -⟩ | ⟨-, mid, hmid, -⟩
  · exact absurd hlt (BitVec.lt_irrefl _)
  · rw [hmid] at h
    exact modifyState_ne_insufficientBalance (credit_ne_insufficientBalance _ _ _) h

/-- A fold whose steps never fail for a short balance never fails for one. -/
private theorem foldlM_ne_insufficientBalance {α β : Type}
    {g : β → α → Except State.StateError β} {other : Address}
    (step : ∀ b x, g b x ≠ .error (.insufficientBalance other)) (xs : List α) (b : β) :
    xs.foldlM g b ≠ .error (.insufficientBalance other) := fun h =>
  foldlM_error_of_step (fun _ => True) (· ≠ .insufficientBalance other)
    (fun _ _ _ _ _ => trivial) (fun b x _ _ he => by rintro rfl; exact step b x he) trivial h rfl

/-- The rewards never fail for a short balance. -/
private theorem payRewards_ne_insufficientBalance (tx : TransactionState) (coinbase : Address)
    (number : Nat) (ommers : List (Address × Nat)) (other : Address) :
    payRewards fork tx coinbase number ommers ≠ .error (.insufficientBalance other) := by
  unfold payRewards
  split
  · nofun
  · intro h
    rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
    · exact createEther_ne_insufficientBalance _ _ _ _ h
    · exact foldlM_ne_insufficientBalance
        (fun _ _ => createEther_ne_insufficientBalance _ _ _ _) _ _ h

/-- The withdrawals never fail for a short balance. -/
private theorem withdrawalState_ne_insufficientBalance (block : BlockState)
    (withdrawals : List Withdrawal) (other : Address) :
    withdrawalState fork block withdrawals ≠ .error (.insufficientBalance other) :=
  foldlM_ne_insufficientBalance (fun _ _ => createEther_ne_insufficientBalance _ _ _ _) _ _

/-- The DAO transfer never fails for a short balance. -/
private theorem applyDaoFork_ne_insufficientBalance (tx : TransactionState) (other : Address) :
    applyDaoFork fork tx ≠ .error (.insufficientBalance other) :=
  foldlM_ne_insufficientBalance (fun _ _ => moveEther_whole_ne_insufficientBalance _ _ _ _) _ _

/-- The join of a call to the body never fails for a short balance. -/
private theorem join_ne_insufficientBalance (body : BodyState) (tx : TransactionState)
    (other : Address) : body.join tx ≠ .error (.insufficientBalance other) := by
  have code := fun hash => getCode_ne_insufficientBalance tx hash other
  have write : ∀ (b : AccessListBuilder) address written,
      b.recordAccountWrite tx address written ≠ .error (.insufficientBalance other) := by
    intro b address written h
    unfold AccessListBuilder.recordAccountWrite at h
    dsimp only at h
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact code _ h
      · cases h
    · cases h
  have record : ∀ b : AccessListBuilder,
      b.recordTransaction tx ≠ .error (.insufficientBalance other) := by
    intro b h
    unfold AccessListBuilder.recordTransaction at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i he
      cases h
      rw [Std.ExtTreeMap.foldlM_eq_foldlM_toList] at he
      exact foldlM_ne_insufficientBalance
        (g := fun a (x : Address × Option State.Account) => a.recordAccountWrite tx x.1 x.2)
        (fun a x => write a x.1 x.2) _ _ he
    · cases h
  intro h
  unfold BodyState.join at h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact record _ h
  · cases h

/-- A state step that never fails for a short balance gives none to the block. -/
private theorem notShort_state {α : Type} {x : Except State.StateError α}
    (h : ∀ a, x ≠ .error (.insufficientBalance a)) : ∀ e, x = .error e → ¬Short (.state e) :=
  fun e he ⟨a, hc⟩ => by
    rcases hc with hc | hc
    · cases hc
    · cases hc
      exact h a he

/-- A call that never aborts for a short balance gives none to the block. -/
private theorem notShort_aborted {α : Type} {x : Except EvmError α}
    (h : ∀ a, x ≠ .error (.state (.insufficientBalance a))) :
    ∀ e, x = .error e → ¬Short (.aborted e) :=
  fun e he ⟨a, hc⟩ => by
    rcases hc with hc | hc
    · cases hc
      exact h a he
    · cases hc

/-- An error that is neither an abort nor an error of the state is no short balance. -/
private theorem notShort_plain {e : BlockError} (ha : ∀ x, e ≠ .aborted x)
    (hs : ∀ x, e ≠ .state x) : ¬Short e :=
  fun ⟨_, h⟩ => h.elim (ha _) (hs _)

/-- The join of a call to the body has no short balance. -/
private theorem errorsMeet_join (body : BodyState) (tx : TransactionState) :
    ErrorsMeet (¬Short ·) ((body.join tx).mapError .state) :=
  ErrorsMeet.mapError (notShort_state (join_ne_insufficientBalance body tx))

/-! ## The calls of a block -/

/-- A system call moves no value, so it never fails for a short balance. -/
private theorem systemCall_ne_insufficientBalance (env : BlockEnvironment fork)
    (block : BlockState) (target : Address) (data : ByteArray) (other : Address) :
    systemCall env block target data ≠ .error (.state (.insufficientBalance other)) := by
  have funded : Funded (systemMessage env target data) (.ofBlock block) := fun t => by
    simp [systemMessage] at t
  intro h
  simp only [systemCall] at h
  split at h <;>
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact Transactions.processMessageCall_ne_insufficientBalance funded other h
    · cases h

/-- A system call that joins the body never fails for a short balance. -/
private theorem systemCall_join_ne_insufficientBalance {env : BlockEnvironment fork}
    {body : BodyState} {target : Address} {data : ByteArray} (other : Address) :
    (do
      let out ← systemCall env body.block target data
      (body.join out.state).mapError EvmError.state : Except EvmError BodyState) ≠
      .error (.state (.insufficientBalance other)) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨out, -, h⟩
  · exact systemCall_ne_insufficientBalance env _ _ _ other h
  · cases hj : body.join out.state with
    | error e' =>
      rw [hj] at h
      cases h
      exact join_ne_insufficientBalance _ _ _ hj
    | ok _ =>
      rw [hj] at h
      cases h

/-- The system calls at the start of a block never fail for a short balance. -/
private theorem startSystemCalls_ne_insufficientBalance {env : BlockEnvironment fork}
    {parentHash : Hash32} {body : BodyState} (other : Address) :
    startSystemCalls env parentHash body ≠ .error (.state (.insufficientBalance other)) := by
  have second : ∀ mid : BodyState,
      (if Fork.pectra ≤ fork then do
        let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
        Except.mapError EvmError.state (mid.join out.state)
      else pure mid) ≠ .error (.state (.insufficientBalance other)) := by
    intro mid h
    split at h
    · exact systemCall_join_ne_insufficientBalance other h
    · cases h
  intro h
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨out, -, h⟩
    · exact systemCall_ne_insufficientBalance env _ _ _ other h
    · rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
      · cases hj : body.join out.state with
        | error e' =>
          rw [hj] at h
          cases h
          exact join_ne_insufficientBalance _ _ _ hj
        | ok _ =>
          rw [hj] at h
          cases h
      · exact second mid h
  · rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
    · cases h
    · exact second mid h

/-- A transaction of a block never fails for a short balance.

It runs only once it passes its checks on the block state it runs on. -/
private theorem errorsMeet_applyTransaction {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} (tx : Transaction) :
    ErrorsMeet (¬Short ·) (applyTransaction env index before tx) := by
  unfold applyTransaction
  refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
    fun included hincl => ?_
  refine ErrorsMeet.bind (ErrorsMeet.aborted (notShort_aborted
    (Transactions.processTransaction_ne_insufficientBalance (mapError_ok_iff.mp hincl))))
    fun out _ => ?_
  refine ErrorsMeet.bind (errorsMeet_join _ _) fun body _ => ?_
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.pure _) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.bind (ErrorsMeet.map _ (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by
      rcases h with h | h <;> cases h)) fun _ _ => ErrorsMeet.pure _

/-- The transactions of a block never fail for a short balance. -/
private theorem errorsMeet_applyTransactions {env : BlockEnvironment fork} {body : BodyState}
    (transactions : List Transaction) :
    ErrorsMeet (¬Short ·) (applyTransactions env body transactions) := fun _ h =>
  foldlM_error_of_step (fun _ : BodyOutput fork => True) (¬Short ·)
    (fun _ _ _ _ _ => trivial) (fun _ _ e _ h => errorsMeet_applyTransaction _ e h)
    (b := ⟨body, .zero, 0, [], []⟩) trivial h

/-- A checked system call never fails for a short balance. -/
private theorem errorsMeet_checkedSystemCall {env : BlockEnvironment fork} {block : BlockState}
    (target : Address) (data : ByteArray) :
    ErrorsMeet (¬Short ·) (checkedSystemCall env block target data) := by
  unfold checkedSystemCall
  refine ErrorsMeet.bind (ErrorsMeet.aborted (notShort_aborted fun a h => ?_)) fun _ _ => ?_
  · unfold codeAt at h
    dsimp only at h
    cases hc : (TransactionState.ofBlock block).getCode
        ((TransactionState.ofBlock block).getAccount target).codeHash with
    | error e' =>
      rw [hc] at h
      cases h
      exact getCode_ne_insufficientBalance _ _ _ hc
    | ok _ =>
      rw [hc] at h
      cases h
  have rest : ErrorsMeet (¬Short ·) (do
      let out ← (systemCall env block target data).mapError BlockError.aborted
      match out.error with
      | some error => throw (BlockError.systemCallFailed target error)
      | none => pure out) := by
    refine ErrorsMeet.bind (ErrorsMeet.aborted
      (notShort_aborted (systemCall_ne_insufficientBalance env block target data)))
      fun _ _ => ?_
    split
    · exact ErrorsMeet.throw fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
    · exact ErrorsMeet.pure _
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.throw fun ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => rest
  · exact rest

/-- A read of a request contract never fails for a short balance. -/
private theorem errorsMeet_readRequest {env : BlockEnvironment fork}
    {state : BodyState × List ByteArray} (contract : UInt8 × Address) :
    ErrorsMeet (¬Short ·) (readRequest env state contract) := by
  unfold readRequest
  refine ErrorsMeet.bind (errorsMeet_checkedSystemCall _ _) fun _ _ => ?_
  exact ErrorsMeet.bind (errorsMeet_join _ _) fun _ _ => ErrorsMeet.pure _

/-- The request reads never fail for a short balance. -/
private theorem errorsMeet_readRequests {env : BlockEnvironment fork} {body : BodyState} :
    ErrorsMeet (¬Short ·) (readRequests env body) := by
  unfold readRequests
  split
  · intro _ h
    exact foldlM_error_of_step (fun _ : BodyState × List ByteArray => True) (¬Short ·)
      (fun _ _ _ _ _ => trivial) (fun _ c e _ h => errorsMeet_readRequest c e h) trivial h
  · exact ErrorsMeet.ok _

/-- The requests of a block never fail for a short balance. -/
private theorem errorsMeet_blockRequests {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} (logs : List Log) :
    ErrorsMeet (¬Short ·) (blockRequests depositContract env body logs) := by
  unfold blockRequests
  split
  · refine ErrorsMeet.bind
      (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => ?_
    exact ErrorsMeet.bind errorsMeet_readRequests fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.pure _

/-- The hash of the block access list never fails for a short balance. -/
private theorem errorsMeet_accessListHashOf (body : BodyState) (gasLimit : Nat) :
    ErrorsMeet (¬Short ·) (accessListHashOf fork body gasLimit) := by
  unfold accessListHashOf
  split
  · refine ErrorsMeet.bind
      (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => ?_
    exact ErrorsMeet.map _
      (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
  · exact ErrorsMeet.pure _

/-- The body of a block never fails for a short balance. -/
private theorem errorsMeet_applyBody {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState} :
    ErrorsMeet (¬Short ·) (applyBody config env block start) := by
  unfold applyBody
  refine ErrorsMeet.bind ?_ fun state _ => ?_
  · unfold daoTransfer
    split
    · exact ErrorsMeet.onBlock (notShort_state (applyDaoFork_ne_insufficientBalance _))
    · exact ErrorsMeet.pure _
  refine ErrorsMeet.bind (ErrorsMeet.aborted
    (notShort_aborted fun a => startSystemCalls_ne_insufficientBalance (body := .init state) a))
    fun body _ => ?_
  refine ErrorsMeet.bind (errorsMeet_applyTransactions _) fun output _ => ?_
  dsimp only
  have rest : ∀ b : BodyState, ErrorsMeet (¬Short ·) (do
      let (body, requests) ← blockRequests config.depositContractAddress env b output.logs
      let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
      let state ← onBlock body.block fun tx =>
        payRewards fork tx block.header.coinbase block.header.number ommers
      let accessListHash ← accessListHashOf fork body block.header.gasLimit
      return ({ output with body := { body with block := state }, requests, accessListHash } :
        BlockOutput fork)) := by
    intro b
    refine ErrorsMeet.bind (errorsMeet_blockRequests _) fun r _ => ?_
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock
      (notShort_state fun a => payRewards_ne_insufficientBalance _ _ _ _ a))
      fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _
  split
  · refine ErrorsMeet.bind (ErrorsMeet.mapError
      (notShort_state (withdrawalState_ne_insufficientBalance _ _)))
      fun tx _ => ?_
    exact ErrorsMeet.bind (errorsMeet_join _ _) fun b _ => rest b
  · exact ErrorsMeet.bind (ErrorsMeet.pure _) fun b _ => rest b

/-- The body of a block never fails with the state error for a short balance.

That holds in a call and outside one. -/
theorem applyBody_ne_insufficientBalance (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) (address : Address) :
    applyBody config env block start ≠ .error (.aborted (.state (.insufficientBalance address))) ∧
      applyBody config env block start ≠ .error (.state (.insufficientBalance address)) :=
  ⟨fun h => errorsMeet_applyBody _ h ⟨address, .inl rfl⟩,
    fun h => errorsMeet_applyBody _ h ⟨address, .inr rfl⟩⟩

/-- The transition of a block never fails with the state error for a short balance, on any state.

That holds in a call and outside one. -/
theorem stateTransition_ne_insufficientBalance (chain : BlockChain) (block : Block fork Transaction)
    (checkSeal : Bool) (address : Address) :
    stateTransition chain block checkSeal ≠
        .error (.aborted (.state (.insufficientBalance address))) ∧
      stateTransition chain block checkSeal ≠ .error (.state (.insufficientBalance address)) := by
  have fails : ErrorsMeet (¬Short ·) (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha hs => notShort_plain ha hs)
      (fun _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ => errorsMeet_applyBody
  exact ⟨fun h => fails _ h ⟨address, .inl rfl⟩, fun h => fails _ h ⟨address, .inr rfl⟩⟩

end EthLib.Execution.Blocks

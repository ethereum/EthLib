module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Blocks.Supply
public import EthLib.Execution.Proofs.Transactions.Overflow

/-!
# Proofs: no block overflows a balance when the supply leaves room

The DAO transfer and the system calls keep or lower the supply.

Each transaction keeps or lowers it, and runs only once it passes its checks.

The withdrawals and the rewards create ether, and the block creates no other.

So each state of the body has at most the supply before the block plus the ether still to create.

Each credit then raises one balance to at most the supply before the block plus all it creates.

So the transition never overflows a balance when that sum leaves room for the credits of a message.

Before Cancun, twice that sum must be below `2^256`.

A SELFDESTRUCT to its own account may double a balance before it clears it.

That bound is simple rather than sharp: only the supply before the block needs the factor two.

Every call that may double a balance runs before the block creates ether.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-! ## Errors that are no overflow -/

/-- Whether an error of a block reports a balance that would overflow, in a call or outside one. -/
private def Overflows (e : BlockError) : Prop :=
  ∃ a, e = .aborted (.state (.balanceOverflow a)) ∨ e = .state (.balanceOverflow a)

/-- A state step that never overflows a balance gives no overflow to the block. -/
private theorem notOverflows_state {α : Type} {x : Except State.StateError α}
    (h : ∀ a, x ≠ .error (.balanceOverflow a)) : ∀ e, x = .error e → ¬Overflows (.state e) :=
  fun e he ⟨a, hc⟩ => by
    rcases hc with hc | hc
    · cases hc
    · cases hc
      exact h a he

/-- A call that never aborts for an overflow gives none to the block. -/
private theorem notOverflows_aborted {α : Type} {x : Except EvmError α}
    (h : ∀ a, x ≠ .error (.state (.balanceOverflow a))) :
    ∀ e, x = .error e → ¬Overflows (.aborted e) :=
  fun e he ⟨a, hc⟩ => by
    rcases hc with hc | hc
    · cases hc
      exact h a he
    · cases hc

/-- An error that is neither an abort nor an error of the state is no overflow. -/
private theorem notOverflows_plain {e : BlockError} (ha : ∀ x, e ≠ .aborted x)
    (hs : ∀ x, e ≠ .state x) : ¬Overflows e :=
  fun ⟨_, h⟩ => h.elim (ha _) (hs _)

/-! ## State changes outside the calls -/

/-- A fold whose steps never overflow a balance never overflows one. -/
private theorem foldlM_ne_balanceOverflow {α β : Type}
    {g : β → α → Except State.StateError β} {other : Address}
    (step : ∀ b x, g b x ≠ .error (.balanceOverflow other)) (xs : List α) (b : β) :
    xs.foldlM g b ≠ .error (.balanceOverflow other) := fun h =>
  foldlM_error_of_step (fun _ => True) (· ≠ .balanceOverflow other)
    (fun _ _ _ _ _ => trivial) (fun b x _ _ he => by rintro rfl; exact step b x he) trivial h rfl

/-- The join of a call to the body never overflows a balance. -/
private theorem join_ne_balanceOverflow (body : BodyState) (tx : TransactionState)
    (other : Address) : body.join tx ≠ .error (.balanceOverflow other) := by
  have code := fun hash => Transactions.getCode_ne_balanceOverflow tx hash other
  have write : ∀ (b : AccessListBuilder) address written,
      b.recordAccountWrite tx address written ≠ .error (.balanceOverflow other) := by
    intro b address written h
    unfold AccessListBuilder.recordAccountWrite at h
    dsimp only at h
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact code _ h
      · cases h
    · cases h
  have record : ∀ b : AccessListBuilder,
      b.recordTransaction tx ≠ .error (.balanceOverflow other) := by
    intro b h
    unfold AccessListBuilder.recordTransaction at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i he
      cases h
      rw [Std.ExtTreeMap.foldlM_eq_foldlM_toList] at he
      exact foldlM_ne_balanceOverflow
        (g := fun a (x : Address × Option State.Account) => a.recordAccountWrite tx x.1 x.2)
        (fun a x => write a x.1 x.2) _ _ he
    · cases h
  intro h
  unfold BodyState.join at h
  rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
  · exact record _ h
  · cases h

/-- The join of a call to the body has no overflow. -/
private theorem errorsMeet_join (body : BodyState) (tx : TransactionState) :
    ErrorsMeet (¬Overflows ·) ((body.join tx).mapError .state) :=
  ErrorsMeet.mapError (notOverflows_state (join_ne_balanceOverflow body tx))

/-- Creations of ether never overflow a balance when the supply plus their bounds fits.

That sum must be below `2^256`. -/
private theorem foldlM_createEther_ne_balanceOverflow {α : Type} (target : α → Address)
    (amount : α → U256) (bound : α → Nat) (le : ∀ x, (amount x).toNat ≤ bound x)
    (other : Address) :
    ∀ (xs : List α) (tx : TransactionState), tx.supply + (xs.map bound).sum < 2 ^ 256 →
      xs.foldlM (fun tx x => tx.createEther fork (target x) (amount x)) tx ≠
        .error (.balanceOverflow other)
  | [], _, _, h => by cases h
  | x :: rest, tx, fits, h => by
    have hx := le x
    simp only [List.map_cons, List.sum_cons] at fits
    rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
    · exact TransactionState.createEther_ne_balanceOverflow (by omega) other h
    · have hs := TransactionState.supply_createEther hmid
      exact foldlM_createEther_ne_balanceOverflow target amount bound le other rest mid
        (by omega) h

/-- The rewards never overflow a balance when the supply plus the rewards is below `2^256`. -/
private theorem payRewards_ne_balanceOverflow {tx : TransactionState} {coinbase : Address}
    {number : Nat} {ommers : List (Address × Nat)}
    (fits : tx.supply + rewardWei fork number ommers < 2 ^ 256) (other : Address) :
    payRewards fork tx coinbase number ommers ≠ .error (.balanceOverflow other) := by
  unfold payRewards
  split
  · nofun
  · rename_i hparis
    simp only [rewardWei, hparis, ↓reduceIte] at fits
    have hmod := Nat.mod_le (minerReward fork ommers.length) (2 ^ 256)
    intro h
    rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
    · refine TransactionState.createEther_ne_balanceOverflow ?_ other h
      rw [BitVec.toNat_ofNat]
      omega
    · have hs := TransactionState.supply_createEther hmid
      rw [BitVec.toNat_ofNat] at hs
      exact foldlM_createEther_ne_balanceOverflow Prod.fst
        (fun o => BitVec.ofNat 256 (ommerReward fork (number - o.2)))
        (fun o => ommerReward fork (number - o.2))
        (fun _ => by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _) other ommers mid
        (by omega) h

/-- The withdrawals never overflow a balance when the supply plus the withdrawn wei fits.

That sum must be below `2^256`. -/
private theorem withdrawalState_ne_balanceOverflow {block : BlockState}
    {withdrawals : List Withdrawal}
    (fits : (TransactionState.ofBlock block).supply + withdrawnWei withdrawals < 2 ^ 256)
    (other : Address) :
    withdrawalState fork block withdrawals ≠ .error (.balanceOverflow other) := by
  have le : ∀ w : Withdrawal, (BitVec.ofNat 256 (w.amount.toNat * GWEI_TO_WEI)).toNat ≤
      w.amount.toNat * GWEI_TO_WEI := fun w => by
    rw [toNat_withdrawalWei]
    exact Nat.le_refl _
  have key := foldlM_createEther_ne_balanceOverflow (fork := fork) (fun w : Withdrawal => w.address)
    (fun w => BitVec.ofNat 256 (w.amount.toNat * GWEI_TO_WEI))
    (fun w => w.amount.toNat * GWEI_TO_WEI) le other withdrawals (.ofBlock block) fits
  exact key

/-- The DAO transfer never overflows a balance when the supply is below `2^256`. -/
private theorem applyDaoFork_ne_balanceOverflow {tx : TransactionState}
    (fits : tx.supply < 2 ^ 256) (other : Address) :
    applyDaoFork fork tx ≠ .error (.balanceOverflow other) := fun h =>
  foldlM_error_of_step (fun mid : TransactionState => mid.supply < 2 ^ 256)
    (· ≠ .balanceOverflow other)
    (fun _ _ _ hb hstep => (TransactionState.supply_moveEther hstep) ▸ hb)
    (fun _ _ e hb he => by
      rintro rfl
      exact TransactionState.moveEther_ne_balanceOverflow hb _ _ _ other he) fits h rfl

/-! ## The calls of a block -/

/-- A system call never overflows a balance when the supply of its block leaves room. -/
private theorem systemCall_ne_balanceOverflow {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray}
    (room : SupplyRoom fork (TransactionState.ofBlock block).supply) (other : Address) :
    systemCall env block target data ≠ .error (.state (.balanceOverflow other)) := by
  intro h
  simp only [systemCall] at h
  split at h <;>
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact Transactions.processMessageCall_ne_balanceOverflow room other h
    · cases h

/-- A system call keeps or lowers the supply of its block. -/
private theorem supply_systemCall_le {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out) :
    out.state.supply ≤ (TransactionState.ofBlock block).supply := by
  obtain ⟨log, burns⟩ := systemCall_systemCallBurns h
  have := burns.supply_eq
  omega

/-- A system call that joins the body never overflows a balance when the supply leaves room. -/
private theorem systemCall_join_ne_balanceOverflow {env : BlockEnvironment fork}
    {body : BodyState} {target : Address} {data : ByteArray}
    (room : SupplyRoom fork (TransactionState.ofBlock body.block).supply) (other : Address) :
    (do
      let out ← systemCall env body.block target data
      (body.join out.state).mapError EvmError.state : Except EvmError BodyState) ≠
      .error (.state (.balanceOverflow other)) := by
  intro h
  rcases Base.bind_eq_error h with h | ⟨out, -, h⟩
  · exact systemCall_ne_balanceOverflow room other h
  · cases hj : body.join out.state with
    | error e' =>
      rw [hj] at h
      cases h
      exact join_ne_balanceOverflow _ _ _ hj
    | ok _ =>
      rw [hj] at h
      cases h

/-- The first system calls of a block never overflow a balance when the supply leaves room. -/
private theorem startSystemCalls_ne_balanceOverflow {env : BlockEnvironment fork}
    {parentHash : Hash32} {body : BodyState}
    (room : SupplyRoom fork (TransactionState.ofBlock body.block).supply) (other : Address) :
    startSystemCalls env parentHash body ≠ .error (.state (.balanceOverflow other)) := by
  have second : ∀ mid : BodyState, SupplyRoom fork (TransactionState.ofBlock mid.block).supply →
      (if Fork.pectra ≤ fork then do
        let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
        Except.mapError EvmError.state (mid.join out.state)
      else pure mid) ≠ .error (.state (.balanceOverflow other)) := by
    intro mid hroom h
    split at h
    · exact systemCall_join_ne_balanceOverflow hroom other h
    · cases h
  intro h
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨out, hout, h⟩
    · exact systemCall_ne_balanceOverflow room other h
    · rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
      · cases hj : body.join out.state with
        | error e' =>
          rw [hj] at h
          cases h
          exact join_ne_balanceOverflow _ _ _ hj
        | ok _ =>
          rw [hj] at h
          cases h
      · refine second mid (room.mono ?_) h
        rw [BodyState.supply_join (Base.mapError_ok_iff.mp hmid)]
        exact supply_systemCall_le hout
  · rcases Base.bind_eq_error h with h | ⟨mid, hmid, h⟩
    · cases h
    · cases hmid
      exact second _ room h

/-- A transaction of a block never overflows a balance when the supply before it leaves room. -/
private theorem errorsMeet_applyTransaction {env : BlockEnvironment fork} {index : Nat}
    {before : BodyOutput fork} (tx : Transaction)
    (room : SupplyRoom fork (TransactionState.ofBlock before.block).supply) :
    ErrorsMeet (¬Overflows ·) (applyTransaction env index before tx) := by
  unfold applyTransaction
  refine ErrorsMeet.bind (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
    fun included hincluded => ?_
  refine ErrorsMeet.bind (ErrorsMeet.aborted (notOverflows_aborted
    (Transactions.processTransaction_ne_balanceOverflow (Base.mapError_ok_iff.mp hincluded)
      room))) fun out _ => ?_
  refine ErrorsMeet.bind (errorsMeet_join _ _) fun body _ => ?_
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.pure _) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.bind (ErrorsMeet.map _ (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by
      rcases h with h | h <;> cases h)) fun _ _ => ErrorsMeet.pure _

/-- A transaction of a block keeps or lowers the supply. -/
private theorem supply_applyTransaction_le {env : BlockEnvironment fork} {index : Nat}
    {before after : BodyOutput fork} {tx : Transaction}
    (h : applyTransaction env index before tx = .ok after) :
    (TransactionState.ofBlock after.block).supply ≤
      (TransactionState.ofBlock before.block).supply := by
  obtain ⟨included, out, inclusion, run, -, -, join⟩ := applyTransaction_eq_ok h
  obtain ⟨-, valid, -, -, -, fee, -⟩ := Transactions.checkInclusion_ok inclusion
  have := Transactions.processTransaction_supply_le
    (Transactions.validateTransaction_ok valid).2.1 (Transactions.le_effectiveGasPrice fee) run
  have joined := BodyState.supply_join join
  change (TransactionState.ofBlock after.block).supply = out.state.supply at joined
  omega

/-- The transactions of a block never overflow a balance when their start supply leaves room. -/
private theorem errorsMeet_applyTransactions {env : BlockEnvironment fork} {body : BodyState}
    (transactions : List Transaction)
    (room : SupplyRoom fork (TransactionState.ofBlock body.block).supply) :
    ErrorsMeet (¬Overflows ·) (applyTransactions env body transactions) := fun _ h =>
  foldlM_error_of_step
    (fun b : BodyOutput fork => SupplyRoom fork (TransactionState.ofBlock b.block).supply)
    (¬Overflows ·) (fun _ _ _ hb hstep => hb.mono (supply_applyTransaction_le hstep))
    (fun _ _ e hb h => errorsMeet_applyTransaction _ hb e h)
    (b := ⟨body, .zero, 0, [], [], []⟩) room h

/-- The transactions of a block keep or lower the supply. -/
private theorem supply_applyTransactions_le {env : BlockEnvironment fork} {body : BodyState}
    {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    (TransactionState.ofBlock output.block).supply ≤
      (TransactionState.ofBlock body.block).supply :=
  foldlM_ok_invariant
    (fun b : BodyOutput fork => (TransactionState.ofBlock b.block).supply ≤
      (TransactionState.ofBlock body.block).supply)
    (fun _ _ _ hb hstep => Nat.le_trans (supply_applyTransaction_le hstep) hb)
    (b := ⟨body, .zero, 0, [], [], []⟩) (Nat.le_refl _) h

/-- A checked system call never overflows a balance when the supply of its block leaves room. -/
private theorem errorsMeet_checkedSystemCall {env : BlockEnvironment fork} {block : BlockState}
    (target : Address) (data : ByteArray)
    (room : SupplyRoom fork (TransactionState.ofBlock block).supply) :
    ErrorsMeet (¬Overflows ·) (checkedSystemCall env block target data) := by
  unfold checkedSystemCall
  refine ErrorsMeet.bind (ErrorsMeet.aborted (notOverflows_aborted fun a h => ?_)) fun _ _ => ?_
  · unfold codeAt at h
    dsimp only at h
    cases hc : (TransactionState.ofBlock block).getCode
        ((TransactionState.ofBlock block).getAccount target).codeHash with
    | error e' =>
      rw [hc] at h
      cases h
      exact Transactions.getCode_ne_balanceOverflow _ _ _ hc
    | ok _ =>
      rw [hc] at h
      cases h
  have rest : ErrorsMeet (¬Overflows ·) (do
      let out ← (systemCall env block target data).mapError BlockError.aborted
      match out.error with
      | some error => throw (BlockError.systemCallFailed target error)
      | none => pure out) := by
    refine ErrorsMeet.bind (ErrorsMeet.aborted
      (notOverflows_aborted (systemCall_ne_balanceOverflow room)))
      fun _ _ => ?_
    split
    · exact ErrorsMeet.throw fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
    · exact ErrorsMeet.pure _
  dsimp only
  split
  · exact ErrorsMeet.bind (ErrorsMeet.throw fun ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => rest
  · exact rest

/-- A read of a request contract never overflows a balance when the supply leaves room. -/
private theorem errorsMeet_readRequest {env : BlockEnvironment fork}
    {state : BodyState × List ByteArray} (contract : UInt8 × Address)
    (room : SupplyRoom fork (TransactionState.ofBlock state.1.block).supply) :
    ErrorsMeet (¬Overflows ·) (readRequest env state contract) := by
  unfold readRequest
  refine ErrorsMeet.bind (errorsMeet_checkedSystemCall _ _ room) fun _ _ => ?_
  exact ErrorsMeet.bind (errorsMeet_join _ _) fun _ _ => ErrorsMeet.pure _

/-- A read of a request contract keeps or lowers the supply. -/
private theorem supply_readRequest_le {env : BlockEnvironment fork}
    {state state' : BodyState × List ByteArray} {contract : UInt8 × Address}
    (h : readRequest env state contract = .ok state') :
    (TransactionState.ofBlock state'.1.block).supply ≤
      (TransactionState.ofBlock state.1.block).supply := by
  obtain ⟨out, call, join, -⟩ := readRequest_eq_ok h
  rw [BodyState.supply_join join]
  exact supply_systemCall_le (checkedSystemCall_ok call).2.1

/-- The request reads never overflow a balance when the supply leaves room. -/
private theorem errorsMeet_readRequests {env : BlockEnvironment fork} {body : BodyState}
    (room : SupplyRoom fork (TransactionState.ofBlock body.block).supply) :
    ErrorsMeet (¬Overflows ·) (readRequests env body) := by
  unfold readRequests
  split
  · intro e h
    have keep : ∀ (s : BodyState × List ByteArray) (c : UInt8 × Address) s',
        SupplyRoom fork (TransactionState.ofBlock s.1.block).supply →
        readRequest env s c = .ok s' →
        SupplyRoom fork (TransactionState.ofBlock s'.1.block).supply :=
      fun _ _ _ hb hstep => hb.mono (supply_readRequest_le hstep)
    exact foldlM_error_of_step
      (fun s : BodyState × List ByteArray =>
        SupplyRoom fork (TransactionState.ofBlock s.1.block).supply) (¬Overflows ·) keep
      (fun _ c e hb h => errorsMeet_readRequest c hb e h) (b := (body, [])) room h
  · exact ErrorsMeet.ok _

/-- The requests of a block never overflow a balance when the supply leaves room. -/
private theorem errorsMeet_blockRequests {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} (logs : List Log)
    (room : SupplyRoom fork (TransactionState.ofBlock body.block).supply) :
    ErrorsMeet (¬Overflows ·) (blockRequests depositContract env body logs) := by
  unfold blockRequests
  split
  · refine ErrorsMeet.bind
      (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_readRequests room) fun _ _ => ErrorsMeet.pure _
  · exact ErrorsMeet.pure _

/-- The requests of a block keep or lower the supply. -/
private theorem supply_blockRequests_le {depositContract : Address} {env : BlockEnvironment fork}
    {body : BodyState} {logs : List Log} {result : BodyState × List ByteArray}
    (h : blockRequests depositContract env body logs = .ok result) :
    (TransactionState.ofBlock result.1.block).supply ≤
      (TransactionState.ofBlock body.block).supply := by
  obtain ⟨log, burns⟩ := blockRequests_blockRequestsBurns h
  have := burns.supply_eq
  omega

/-- The hash of the block access list never overflows a balance. -/
private theorem errorsMeet_accessListHashOf (body : BodyState) (gasLimit : Nat) :
    ErrorsMeet (¬Overflows ·) (accessListHashOf fork body gasLimit) := by
  unfold accessListHashOf
  split
  · refine ErrorsMeet.bind
      (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ _ => ?_
    exact ErrorsMeet.map _
      (ErrorsMeet.mapError fun _ _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
  · exact ErrorsMeet.pure _

/-! ## The body -/

/-- A body never overflows a balance when its supply plus the ether it creates leaves room. -/
private theorem errorsMeet_applyBody {config : ChainConfig} {env : BlockEnvironment fork}
    {block : Block fork Transaction} {start : BlockState}
    (room : SupplyRoom fork ((TransactionState.ofBlock start).supply + createdWei block)) :
    ErrorsMeet (¬Overflows ·) (applyBody config env block start) := by
  have fits := room.lt
  unfold applyBody
  refine ErrorsMeet.bind ?_ fun state hstate => ?_
  · unfold daoTransfer
    split
    · exact ErrorsMeet.onBlock
        (notOverflows_state fun a => applyDaoFork_ne_balanceOverflow (by omega) a)
    · exact ErrorsMeet.pure _
  have hdao := supply_daoTransfer hstate
  refine ErrorsMeet.bind (ErrorsMeet.aborted (notOverflows_aborted fun a =>
    startSystemCalls_ne_balanceOverflow (body := .init state) (room.mono ?_) a))
    fun body hbody => ?_
  · change (TransactionState.ofBlock state).supply ≤ _
    omega
  obtain ⟨log, burns⟩ := startSystemCalls_startSystemCallsBurns (Base.mapError_ok_iff.mp hbody)
  have hsystem := burns.supply_eq
  change _ = (TransactionState.ofBlock state).supply at hsystem
  refine ErrorsMeet.bind (errorsMeet_applyTransactions _ (room.mono (by omega)))
    fun output houtput => ?_
  have htxs := supply_applyTransactions_le houtput
  dsimp only
  have rest : ∀ b : BodyState, (TransactionState.ofBlock b.block).supply +
      rewardWei fork block.header.number
        (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) ≤
        (TransactionState.ofBlock start).supply + createdWei block →
      ErrorsMeet (¬Overflows ·) (do
      let (body, requests) ← blockRequests config.depositContractAddress env b output.logs
      let ommers := block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)
      let state ← onBlock body.block fun tx =>
        payRewards fork tx block.header.coinbase block.header.number ommers
      let accessListHash ← accessListHashOf fork body block.header.gasLimit
      return ({ output with body := { body with block := state }, requests, accessListHash } :
        BlockOutput fork)) := by
    intro b hb
    refine ErrorsMeet.bind (errorsMeet_blockRequests _ (room.mono (by omega))) fun r hr => ?_
    have hreq := supply_blockRequests_le hr
    obtain ⟨requested, requests⟩ := r
    refine ErrorsMeet.bind (ErrorsMeet.onBlock
      (notOverflows_state fun a => payRewards_ne_balanceOverflow (by dsimp only at hreq; omega) a))
      fun _ _ => ?_
    exact ErrorsMeet.bind (errorsMeet_accessListHashOf _ _) fun _ _ => ErrorsMeet.pure _
  split
  · rename_i hS
    have hcreated : createdWei block = withdrawnWei (block.withdrawals hS) +
        rewardWei fork block.header.number
          (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) := by
      simp only [createdWei, hS, ↓reduceDIte]
    refine ErrorsMeet.bind (ErrorsMeet.mapError
      (notOverflows_state fun a => withdrawalState_ne_balanceOverflow ?_ a))
      fun tx htx => ?_
    · change (TransactionState.ofBlock output.block).supply + _ < _
      omega
    have hw := supply_withdrawalState (Base.mapError_ok_iff.mp htx)
    change tx.supply = (TransactionState.ofBlock output.block).supply + _ at hw
    refine ErrorsMeet.bind (errorsMeet_join _ _) fun b hb => rest b ?_
    rw [BodyState.supply_join (Base.mapError_ok_iff.mp hb)]
    omega
  · rename_i hS
    have hcreated : createdWei block = rewardWei fork block.header.number
          (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) := by
      simp only [createdWei, hS, ↓reduceDIte, Nat.zero_add]
    refine ErrorsMeet.bind (ErrorsMeet.pure _) fun b hb => rest b ?_
    cases hb
    change (TransactionState.ofBlock output.block).supply + _ ≤ _
    omega

/-- The body of a block never fails with the state error for a balance that would overflow.

The supply of its start state plus the ether that the block creates must leave room.

That holds in a call and outside one. -/
theorem applyBody_ne_balanceOverflow (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState)
    (room : SupplyRoom fork ((TransactionState.ofBlock start).supply + createdWei block))
    (address : Address) :
    applyBody config env block start ≠ .error (.aborted (.state (.balanceOverflow address))) ∧
      applyBody config env block start ≠ .error (.state (.balanceOverflow address)) :=
  ⟨fun h => errorsMeet_applyBody room _ h ⟨address, .inl rfl⟩,
    fun h => errorsMeet_applyBody room _ h ⟨address, .inr rfl⟩⟩

/-- The transition of a block never fails with the state error for a balance that would overflow.

The supply of the chain state plus the ether that the block creates must leave room.

That holds in a call and outside one. -/
theorem stateTransition_ne_balanceOverflow (chain : BlockChain) (block : Block fork Transaction)
    (checkSeal : Bool) (room : SupplyRoom fork (chain.state.supply + createdWei block))
    (address : Address) :
    stateTransition chain block checkSeal ≠
        .error (.aborted (.state (.balanceOverflow address))) ∧
      stateTransition chain block checkSeal ≠ .error (.state (.balanceOverflow address)) := by
  have start : SupplyRoom fork
      ((TransactionState.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩).supply + createdWei block) := by
    rwa [TransactionState.supply_ofPreState]
  have fails : ErrorsMeet (¬Overflows ·) (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha hs => notOverflows_plain ha hs)
      (fun _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ => errorsMeet_applyBody start
  exact ⟨fun h => fails _ h ⟨address, .inl rfl⟩, fun h => fails _ h ⟨address, .inr rfl⟩⟩

end EthLib.Execution.Blocks

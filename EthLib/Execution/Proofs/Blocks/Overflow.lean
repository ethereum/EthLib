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

/-! ## The body of a block -/

/-- The leaves of a block body never overflow a balance when its supply plus all it creates fits.

Before the withdrawals, each state has at most the supply of the start state.

After them, each state plus the rewards still to come has at most that supply plus all it creates.

The sum must leave room for the credits of a message. -/
private theorem leaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState)
    (room : SupplyRoom fork ((TransactionState.ofBlock start).supply + createdWei block)) :
    BodyLeaves config env block (¬Overflows ·)
      (fun s => (TransactionState.ofBlock s).supply ≤ (TransactionState.ofBlock start).supply)
      (fun s => (TransactionState.ofBlock s).supply + rewardWei fork block.header.number
        (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) ≤
          (TransactionState.ofBlock start).supply + createdWei block)
      (fun _ => True) where
  plain _ ha hs _ _ := notOverflows_plain ha hs
  dao _ low := notOverflows_state fun a =>
    applyDaoFork_ne_balanceOverflow (by have := room.lt; omega) a
  dao_inv _ _ low h := by
    rw [supply_daoTransfer h]
    exact low
  start _ low := notOverflows_aborted fun a =>
    startSystemCalls_ne_balanceOverflow (room.mono (by omega)) a
  start_inv _ _ low h := by
    obtain ⟨log, burns⟩ := startSystemCalls_startSystemCallsBurns h
    have := burns.supply_eq
    omega
  inclusion _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  process _ _ _ low included := notOverflows_aborted
    (Transactions.processTransaction_ne_balanceOverflow included (room.mono (by omega)))
  transaction_inv _ _ _ _ low h := Nat.le_trans (supply_applyTransaction_le h) low
  join body tx _ := notOverflows_state (join_ne_balanceOverflow body tx)
  withdraw hS _ low := notOverflows_state fun a => withdrawalState_ne_balanceOverflow (by
    have := room.lt
    have created : createdWei block = withdrawnWei (block.withdrawals hS) +
        rewardWei fork block.header.number
          (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) := by
      simp only [createdWei, hS, ↓reduceDIte]
    omega) a
  withdraw_inv hS _ _ _ low withdrawn joined := by
    have created : createdWei block = withdrawnWei (block.withdrawals hS) +
        rewardWei fork block.header.number
          (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) := by
      simp only [createdWei, hS, ↓reduceDIte]
    rw [BodyState.supply_join joined, supply_withdrawalState withdrawn]
    omega
  skip_inv hS _ low := by
    have created : createdWei block = rewardWei fork block.header.number
        (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) := by
      simp only [createdWei, hS, ↓reduceDIte, Nat.zero_add]
    omega
  code _ _ _ := notOverflows_aborted fun a h => by
    obtain ⟨_, h, ⟨⟩⟩ := mapError_eq_error h
    exact Transactions.getCode_ne_balanceOverflow _ _ _ h
  call _ _ _ high := notOverflows_aborted (systemCall_ne_balanceOverflow (room.mono (by omega)))
  call_failed _ _ _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  call_inv _ _ _ _ _ high called joined := by
    rw [BodyState.supply_join joined]
    have := supply_systemCall_le called
    omega
  rewards _ high := notOverflows_state fun a =>
    payRewards_ne_balanceOverflow (by have := room.lt; omega) a

/-- The body of a block never fails with the state error for a balance that would overflow.

The supply of its start state plus the ether that the block creates must leave room.

That holds in a call and outside one. -/
theorem applyBody_ne_balanceOverflow (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState)
    (room : SupplyRoom fork ((TransactionState.ofBlock start).supply + createdWei block))
    (address : Address) :
    applyBody config env block start ≠ .error (.aborted (.state (.balanceOverflow address))) ∧
      applyBody config env block start ≠ .error (.state (.balanceOverflow address)) :=
  ⟨fun h => (leaves config env block start room).errorsMeet_applyBody (Nat.le_refl _) _ h
    ⟨address, .inl rfl⟩,
    fun h => (leaves config env block start room).errorsMeet_applyBody (Nat.le_refl _) _ h
      ⟨address, .inr rfl⟩⟩

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
      fun _ => (leaves _ _ _ _ start).errorsMeet_applyBody (Nat.le_refl _)
  exact ⟨fun h => fails _ h ⟨address, .inl rfl⟩, fun h => fails _ h ⟨address, .inr rfl⟩⟩

end EthLib.Execution.Blocks

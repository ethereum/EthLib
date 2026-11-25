module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Blocks.Supply
public import EthLib.Execution.Proofs.Transactions.Overflow

/-!
# Proofs: no block overflows a balance when the supply leaves room

The supply before a block plus the ether it creates must leave room for the credits of a message.

Before Cancun, twice that sum must be below `2^256`.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction)

variable {fork : Fork}

/-! ## State changes outside the calls -/

/-- Whether an error of a block reports a balance that would overflow, in a call or outside one. -/
private abbrev Overflows : BlockError → Prop := StateErrorOf .balanceOverflow

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

Each state of the body has at most the supply before the block plus the ether still to create.

Each credit then raises one balance to at most the supply before the block plus all it creates. -/
private theorem leaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState)
    -- The withdrawals and the rewards create ether, and the block creates no other.
    --
    -- The sum must leave room for the credits of a message.
    (room : SupplyRoom fork ((TransactionState.ofBlock start).supply + createdWei block)) :
    BodyLeaves config env block (¬Overflows ·)
      -- Before the withdrawals, each state has at most the supply of the start state.
      (fun s => (TransactionState.ofBlock s).supply ≤ (TransactionState.ofBlock start).supply)
      -- After them, a state plus the rewards to come has at most that supply plus all it creates.
      (fun s => (TransactionState.ofBlock s).supply + rewardWei fork block.header.number
        (block.ommers.map fun ommer => (ommer.2.coinbase, ommer.2.number)) ≤
          (TransactionState.ofBlock start).supply + createdWei block)
      (fun _ => True) where
  plain _ ha hs _ _ := StateErrorOf.not_plain ha hs
  dao _ low := StateErrorOf.not_state fun a =>
    applyDaoFork_ne_balanceOverflow (by have := room.lt; omega) a
  -- The DAO transfer keeps or lowers the supply.
  dao_inv _ _ low h := by
    rw [supply_daoTransfer h]
    exact low
  -- The system calls keep or lower the supply, so each leaves room for the next.
  start _ low := StateErrorOf.not_aborted fun a =>
    startSystemCalls_ne_error (fun s => SupplyRoom fork (TransactionState.ofBlock s).supply)
      (fun _ _ _ hroom => systemCall_ne_balanceOverflow hroom a)
      (fun b _ _ out _ _ => b.join_ne_error (Transactions.getCode_ne_balanceOverflow out.state · a))
      (fun _ _ _ _ _ hroom hout hjoin => hroom.mono (by
        rw [BodyState.supply_join hjoin]
        exact supply_systemCall_le hout))
      (room.mono (by omega))
  -- The system calls that start the block keep or lower the supply.
  start_inv _ _ low h := by
    obtain ⟨log, burns⟩ := startSystemCalls_startSystemCallsBurns h
    have := burns.supply_eq
    omega
  inclusion _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  -- A transaction runs only once it passes its checks.
  process _ _ _ low included := StateErrorOf.not_aborted
    (Transactions.processTransaction_ne_balanceOverflow included (room.mono (by omega)))
  -- Each transaction keeps or lowers the supply.
  transaction_inv _ _ _ _ low h := Nat.le_trans (supply_applyTransaction_le h) low
  join body tx _ := StateErrorOf.not_state fun a =>
    body.join_ne_error (Transactions.getCode_ne_balanceOverflow tx · a)
  withdraw hS _ low := StateErrorOf.not_state fun a => withdrawalState_ne_balanceOverflow (by
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
  code _ _ _ := StateErrorOf.not_aborted fun a h => by
    obtain ⟨_, h, ⟨⟩⟩ := mapError_eq_error h
    exact Transactions.getCode_ne_balanceOverflow _ _ _ h
  call _ _ _ high := StateErrorOf.not_aborted (systemCall_ne_balanceOverflow (room.mono (by omega)))
  call_failed _ _ _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  -- A call to a request contract keeps or lowers the supply.
  call_inv _ _ _ _ _ high called joined := by
    rw [BodyState.supply_join joined]
    have := supply_systemCall_le called
    omega
  rewards _ high := StateErrorOf.not_state fun a =>
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
    -- Before Cancun, a SELFDESTRUCT to its own account may double a balance before it clears it.
    --
    -- So the bound then doubles the sum, which is simple rather than sharp.
    --
    -- Only the supply before the block needs the factor two.
    --
    -- Every call that may double a balance runs before the block creates ether.
    (checkSeal : Bool) (room : SupplyRoom fork (chain.state.supply + createdWei block))
    (address : Address) :
    stateTransition chain block checkSeal ≠
        .error (.aborted (.state (.balanceOverflow address))) ∧
      stateTransition chain block checkSeal ≠ .error (.state (.balanceOverflow address)) := by
  have start : SupplyRoom fork
      ((TransactionState.ofBlock ⟨chain.state, ∅, ∅, ∅, ∅⟩).supply + createdWei block) := by
    rwa [TransactionState.supply_ofPreState]
  have fails : ErrorsMeet (¬Overflows ·) (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha hs => StateErrorOf.not_plain ha hs)
      (fun _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ => (leaves _ _ _ _ start).errorsMeet_applyBody (Nat.le_refl _)
  exact ⟨fun h => fails _ h ⟨address, .inl rfl⟩, fun h => fails _ h ⟨address, .inr rfl⟩⟩

end EthLib.Execution.Blocks

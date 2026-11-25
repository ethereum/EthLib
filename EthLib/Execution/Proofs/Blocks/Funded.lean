module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Transactions.Funded

/-!
# Proofs: no block fails with the state error for a balance below an amount

The transition of a block never fails with the state error for a short balance, on any state.

A sender short of its most costly fee makes the block invalid at its inclusion check instead.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction getCode_ne_insufficientBalance)

variable {fork : Fork}

/-! ## Changes of the state with no short balance -/

/-- Whether an error of a block is a short balance, in a call or outside one. -/
private abbrev Short : BlockError → Prop := StateErrorOf .insufficientBalance

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
    cases TransactionState.error_createEther h

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

/-! ## The body of a block -/

/-- The leaves of the body of a block never fail for a short balance. -/
private theorem leaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) :
    BodyLeaves config env block (¬Short ·) (fun _ => True) (fun _ => True) (fun _ => True) where
  plain _ ha hs _ _ := StateErrorOf.not_plain ha hs
  -- The DAO transfer moves the whole balance of each account it drains.
  dao _ _ := StateErrorOf.not_state fun _ =>
    foldlM_ne_error_of_step (fun _ _ => moveEther_whole_ne_insufficientBalance _ _ _ _) _ _
  -- A system call moves no value.
  start _ _ := StateErrorOf.not_aborted fun a =>
    startSystemCalls_ne_error (fun _ => True)
      (fun block target data _ => systemCall_ne_insufficientBalance env block target data a)
      (fun b _ _ out _ _ => b.join_ne_error (getCode_ne_insufficientBalance out.state · a))
      (fun _ _ _ _ _ _ _ _ => trivial) trivial
  inclusion _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  -- Each transaction runs only once it passes its checks on the state it runs on.
  process _ _ _ _ included :=
    StateErrorOf.not_aborted (Transactions.processTransaction_ne_insufficientBalance included)
  join body tx _ := StateErrorOf.not_state fun a =>
    body.join_ne_error (getCode_ne_insufficientBalance tx · a)
  -- The withdrawals create ether, and take none.
  withdraw _ _ _ := StateErrorOf.not_state fun _ => withdrawalState_ne_error nofun
  code _ _ _ := StateErrorOf.not_aborted fun a h => by
    obtain ⟨_, h, ⟨⟩⟩ := mapError_eq_error h
    exact getCode_ne_insufficientBalance _ _ _ h
  call s target data _ :=
    StateErrorOf.not_aborted (systemCall_ne_insufficientBalance env s target data)
  call_failed _ _ _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  -- The rewards create ether, and take none.
  rewards _ _ := StateErrorOf.not_state fun _ => payRewards_ne_error nofun

/-- The body of a block never fails with the state error for a short balance.

That holds in a call and outside one. -/
theorem applyBody_ne_insufficientBalance (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) (address : Address) :
    applyBody config env block start ≠ .error (.aborted (.state (.insufficientBalance address))) ∧
      applyBody config env block start ≠ .error (.state (.insufficientBalance address)) :=
  ⟨fun h => (leaves config env block).errorsMeet_applyBody trivial _ h ⟨address, .inl rfl⟩,
    fun h => (leaves config env block).errorsMeet_applyBody trivial _ h ⟨address, .inr rfl⟩⟩

/-- The transition of a block never fails with the state error for a short balance, on any state.

That holds in a call and outside one. -/
theorem stateTransition_ne_insufficientBalance (chain : BlockChain) (block : Block fork Transaction)
    (checkSeal : Bool) (address : Address) :
    stateTransition chain block checkSeal ≠
        .error (.aborted (.state (.insufficientBalance address))) ∧
      stateTransition chain block checkSeal ≠ .error (.state (.insufficientBalance address)) := by
  have fails : ErrorsMeet (¬Short ·) (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha hs => StateErrorOf.not_plain ha hs)
      (fun _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ => (leaves _ _ _).errorsMeet_applyBody trivial
  exact ⟨fun h => fails _ h ⟨address, .inl rfl⟩, fun h => fails _ h ⟨address, .inr rfl⟩⟩

end EthLib.Execution.Blocks

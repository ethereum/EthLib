module

public import EthLib.Execution.Proofs.Blocks.Failures
public import EthLib.Execution.Proofs.Transactions.NoAccount

/-!
# Proofs: no block writes storage at an address with no account

A system call runs the code that its target holds, so a target that runs code is settled.

No transaction writes storage at an address with no account.

The reads of the requests are system calls.

The DAO transfer, the withdrawals and the rewards write no storage.

So the transition of a block never fails with the state error for an absent account, on any state.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState State TransactionState)
open EthLib.Execution.Transactions (Transaction getCode_ne_noAccount)

variable {fork : Fork}

/-- Whether an error of a block is an absent account, in a call or outside one. -/
private abbrev Absent : BlockError → Prop := StateErrorOf .noAccount

/-! ## The calls of a block -/

/-- A system call runs at its own target, so it never fails for no account. -/
private theorem systemCall_ne_noAccount (env : BlockEnvironment fork)
    (block : BlockState) (target : Address) (data : ByteArray) (other : Address) :
    systemCall env block target data ≠ .error (.state (.noAccount other)) := by
  have own : ∀ to, (systemMessage env target data).target = some to →
      to = (systemMessage env target data).currentTarget := fun _ h => by
    simp only [systemMessage, Option.some.injEq] at h
    exact h.symm
  intro h
  simp only [systemCall] at h
  split at h <;>
  · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact Transactions.processMessageCall_ne_noAccount own other h
    · cases h

/-! ## The body of a block -/

/-- The leaves of the body of a block never fail for no account. -/
private theorem leaves (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) :
    BodyLeaves config env block (¬Absent ·) (fun _ => True) (fun _ => True) (fun _ => True) where
  plain _ ha hs _ _ := StateErrorOf.not_plain ha hs
  dao _ _ := StateErrorOf.not_state fun _ => foldlM_ne_error_of_step (fun _ _ h => by
    rcases TransactionState.error_moveEther h with h | h <;> cases h) _ _
  start _ _ := StateErrorOf.not_aborted fun a =>
    startSystemCalls_ne_error (fun _ => True)
      (fun block target data _ => systemCall_ne_noAccount env block target data a)
      (fun b _ _ out _ _ => b.join_ne_error (getCode_ne_noAccount out.state · a))
      (fun _ _ _ _ _ _ _ _ => trivial) trivial
  inclusion _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  process _ _ _ _ _ := StateErrorOf.not_aborted Transactions.processTransaction_ne_noAccount
  join body tx _ := StateErrorOf.not_state fun a => body.join_ne_error (getCode_ne_noAccount tx · a)
  withdraw _ _ _ := StateErrorOf.not_state fun _ => withdrawalState_ne_error nofun
  code _ _ _ := StateErrorOf.not_aborted fun a h => by
    obtain ⟨_, h, ⟨⟩⟩ := mapError_eq_error h
    exact getCode_ne_noAccount _ _ _ h
  call s target data _ := StateErrorOf.not_aborted (systemCall_ne_noAccount env s target data)
  call_failed _ _ _ _ _ _ _ _ := fun ⟨_, h⟩ => by rcases h with h | h <;> cases h
  rewards _ _ := StateErrorOf.not_state fun _ => payRewards_ne_error nofun

/-- The body of a block never fails with the state error for an absent account.

That holds as an abort and as an error of the state of the block. -/
theorem applyBody_ne_noAccount (config : ChainConfig) (env : BlockEnvironment fork)
    (block : Block fork Transaction) (start : BlockState) (address : Address) :
    applyBody config env block start ≠ .error (.aborted (.state (.noAccount address))) ∧
      applyBody config env block start ≠ .error (.state (.noAccount address)) :=
  ⟨fun h => (leaves config env block).errorsMeet_applyBody trivial _ h ⟨address, .inl rfl⟩,
    fun h => (leaves config env block).errorsMeet_applyBody trivial _ h ⟨address, .inr rfl⟩⟩

/-- The transition of a block never fails with the state error for an absent account, on any state.

That holds as an abort and as an error of the state of the block. -/
theorem stateTransition_ne_noAccount (chain : BlockChain) (block : Block fork Transaction)
    (checkSeal : Bool) (address : Address) :
    stateTransition chain block checkSeal ≠ .error (.aborted (.state (.noAccount address))) ∧
      stateTransition chain block checkSeal ≠ .error (.state (.noAccount address)) := by
  have fails : ErrorsMeet (¬Absent ·) (stateTransition chain block checkSeal) :=
    errorsMeet_stateTransition (fun _ ha hs => StateErrorOf.not_plain ha hs)
      (fun _ ⟨_, h⟩ => by rcases h with h | h <;> cases h)
      fun _ => (leaves _ _ _).errorsMeet_applyBody trivial
  exact ⟨fun h => fails _ h ⟨address, .inl rfl⟩, fun h => fails _ h ⟨address, .inr rfl⟩⟩

end EthLib.Execution.Blocks

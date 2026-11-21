module

public import EthLib.Execution.Proofs.Evm.Call.Depth
public import EthLib.Execution.Proofs.Transactions.Observe

/-!
# Proofs: every frame of a transaction has a depth of at most 1024

A transaction starts its message at depth 0.

So every frame of its run is within the depth limit, and an observer sees no deeper frame.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)

variable {Meter : Type} [GasMeter Meter] {σ : Type}

omit [GasMeter Meter] in
/-- A lifted result that leads to a successful run is a success, and the rest runs from it. -/
private theorem liftExcept_bind_eq_ok {α β : Type} {x : Except EvmError α}
    {g : α → StateT σ (Except EvmError) β} {s : σ} {r : β × σ}
    (h : (liftExcept x >>= g) s = .ok r) : ∃ a, x = .ok a ∧ g a s = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The first frame of a message keeps the depth of the message. -/
private theorem depth_prepareFirstFrame {fork : Fork} {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    first.message.depth = message.depth := by
  unfold prepareFirstFrame at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    rfl

/-- The message of a transaction starts at depth 0. -/
private theorem depth_transactionMessage {fork : Fork} {env : BlockEnvironment fork}
    {txEnv : TransactionEnvironment fork} {state : State.TransactionState}
    {sender target : Address} {gas : Nat} {tx : Transaction} {message : Message fork}
    (h : transactionMessage env txEnv state sender target gas tx = .ok message) :
    message.depth = 0 := by
  unfold transactionMessage at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Base.map_ok_iff.mp h
    rfl
  · cases h
    rfl

/-- An observed message of a transaction within the depth limit keeps an invariant. -/
private theorem processMessageCallWith_inv [LawfulGasMeter Meter] {fork : Fork}
    (inv : σ → Prop) (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s →
      inv (f evm result s))
    (chainId : Nat) (message : Message fork) (within : message.depth ≤ STACK_DEPTH_LIMIT)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) {s : σ} (start : inv s) {r : CallOutput × σ}
    (run : processMessageCallWith (Meter := Meter) (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) chainId message state substate auths paid s =
        .ok r) :
    inv r.2 := by
  rw [processMessageCallWith] at run
  rcases hp : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hp] at run
    by_cases aborts : e.aborts <;>
      simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift,
        bind, Except.bind, Except.pure] at run
    subst run
    exact start
  · rw [hp] at run
    have depth : first.message.depth ≤ STACK_DEPTH_LIMIT := by
      rw [depth_prepareFirstFrame hp]
      exact within
    dsimp only at run
    cases ht : message.target <;> simp only [ht] at run
    · obtain ⟨⟨⟨evm, used⟩, s'⟩, hrun, rest⟩ := Base.stateT_bind_eq_ok run
      cases rest
      exact processCreateMessageWith_inv_of_depth_le inv f keeps depth _ _ _ _ start hrun
    · obtain ⟨⟨⟨evm, used⟩, s'⟩, hrun, rest⟩ := Base.stateT_bind_eq_ok run
      cases rest
      exact processMessageWith_inv_of_depth_le inv f keeps depth _ _ _ _ start hrun

/-- An observed run of a transaction with one gas meter keeps an invariant.

Its message starts at depth 0, within the limit. -/
private theorem runTransactionWith_inv [LawfulGasMeter Meter] {fork : Fork}
    (inv : σ → Prop) (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s →
      inv (f evm result s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) {s : σ} (start : inv s)
    {r : TransactionOutput × σ}
    (run : runTransactionWith Meter (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
        .ok r) :
    inv r.2 := by
  rw [runTransactionWith] at run
  obtain ⟨target, -, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨state, -, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨message, hm, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨⟨output, s'⟩, hcall, run⟩ := Base.stateT_bind_eq_ok run
  have back : inv s' := processMessageCallWith_inv inv f keeps _ _
    (by simp only [depth_transactionMessage hm]; exact Nat.zero_le _) _ _ _ _ start hcall
  obtain ⟨_, -, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨_, -, run⟩ := liftExcept_bind_eq_ok run
  cases run
  exact back

/-- A run of a transaction that succeeds keeps an invariant of the record of its observer.

The record needs to keep the invariant only at frames within the depth limit, at every meter. -/
theorem processTransactionWith_inv_of_depth_le {fork : Fork} (inv : σ → Prop)
    (f : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) result s,
      evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s → inv (f evm result s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) {s : σ} (start : inv s)
    {r : TransactionOutput × σ}
    (run : processTransactionWith (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
        .ok r) :
    inv r.2 := by
  rw [processTransactionWith] at run
  by_cases hegota : .hegota ≤ fork
  · rw [ite_eq_left hegota] at run
    cases run
  rw [ite_eq_right hegota] at run
  -- Each fork runs the transaction with one meter, and the observer keeps the invariant at it.
  by_cases glamsterdam : fork ≥ .glamsterdam
  · rw [ite_eq_left glamsterdam] at run
    exact runTransactionWith_inv inv f (fun evm result s => keeps evm result s) env block
      included tx precompiles lifted start run
  · rw [ite_eq_right glamsterdam] at run
    exact runTransactionWith_inv inv f (fun evm result s => keeps evm result s) env block
      included tx precompiles lifted start run

end EthLib.Execution.Transactions

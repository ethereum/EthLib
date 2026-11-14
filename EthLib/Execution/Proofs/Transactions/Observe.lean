module

public import EthLib.Execution.Proofs.Evm.Call.Observe
public import EthLib.Execution.Proofs.Transactions.Unfold

/-!
# Proofs: the observed run of a transaction

An observer that only records each step in a state leaves the run of a transaction as it is.

Once that state is dropped, the observed run is the run with no observer.

The same holds of the message of the transaction, and of its run at the meter of its fork.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

variable {Meter : Type} [GasMeter Meter] {σ : Type}

omit [GasMeter Meter] in
/-- Dropping the state after a lifted result binds that result to the rest, state dropped. -/
private theorem fst_liftExcept_bind {α β : Type} (x : Except EvmError α)
    (f : α → StateT σ (Except EvmError) β) (s : σ) :
    Prod.fst <$> (liftExcept x >>= f) s = x >>= fun a => Prod.fst <$> f a s := by
  cases x <;> rfl

omit [GasMeter Meter] in
/-- Dropping the state of a bind, when both parts drop to plain runs, gives the plain bind. -/
private theorem fst_bind_of {α β : Type} {m : StateT σ (Except EvmError) α}
    {f : α → StateT σ (Except EvmError) β} {m' : Except EvmError α} {g : α → Except EvmError β}
    (hm : ∀ s, Prod.fst <$> m s = m') (hf : ∀ a s, Prod.fst <$> f a s = g a) (s : σ) :
    Prod.fst <$> (m >>= f) s = m' >>= g := by
  rw [← hm s]
  show Prod.fst <$> (m s >>= fun p => f p.1 p.2) = _
  cases m s with
  | error e => rfl
  | ok p => exact hf p.1 p.2

/-- An observed message of a transaction, with its state dropped, is the run with no observer.

The observer only changes a state at each step. -/
theorem processMessageCallWith_modify [LawfulGasMeter Meter] {fork : Fork}
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ) (chainId : Nat)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization) (paidWrites : Std.ExtTreeSet Address) (s : σ) :
    Prod.fst <$> processMessageCallWith (Meter := Meter) (M := StateT σ (Except EvmError))
        (fun evm result => modify (record evm result)) chainId message state substate auths
        paidWrites s =
      processMessageCall (Meter := Meter) chainId message state substate auths paidWrites := by
  rw [processMessageCallWith, processMessageCall_unfold]
  rcases prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites
    with ⟨e, read⟩ | first
  · by_cases aborts : e.aborts <;> simp [aborts] <;> rfl
  · cases message.target with
    | none =>
      refine fst_bind_of (fun s => processCreateMessageWith_modify record _ _ _ _ _ s) ?_ s
      rintro ⟨evm, used⟩ s
      rfl
    | some target =>
      refine fst_bind_of (fun s => processMessageWith_modify record _ _ _ _ _ s) ?_ s
      rintro ⟨evm, used⟩ s
      rfl

/-- An observed run of a transaction, with its state dropped, is the run with no observer.

The observer only changes a state at each step. -/
theorem runTransactionWith_modify [LawfulGasMeter Meter] {fork : Fork}
    (record : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) (s : σ) :
    Prod.fst <$> runTransactionWith Meter (M := StateT σ (Except EvmError))
        (fun evm result => modify (record evm result)) env block included tx precompiles
        lifted s =
      runTransaction Meter env block included tx precompiles lifted := by
  rw [runTransactionWith, runTransaction_unfold]
  simp only [fst_liftExcept_bind]
  refine congrArg _ (funext fun target => ?_)
  refine congrArg _ (funext fun state => ?_)
  refine congrArg _ (funext fun message => ?_)
  refine fst_bind_of (fun s => processMessageCallWith_modify record _ _ _ _ _ _ s) ?_ s
  intro output s
  simp only [fst_liftExcept_bind]
  refine congrArg _ (funext fun ⟨state, gasUsed⟩ => ?_)
  rfl

/-- An observed run at the fork of a transaction, state dropped, is the run with no observer.

The observer only changes a state at each step, for each gas meter. -/
theorem processTransactionWith_modify {fork : Fork}
    (record : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → σ → σ)
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) (s : σ) :
    Prod.fst <$> processTransactionWith (M := StateT σ (Except EvmError))
        (fun evm result => modify (record evm result)) env block included tx precompiles
        lifted s =
      processTransaction env block included tx precompiles lifted := by
  rw [processTransactionWith, processTransaction_unfold]
  split
  · rfl
  split
  · exact runTransactionWith_modify record env block included tx precompiles lifted s
  · exact runTransactionWith_modify record env block included tx precompiles lifted s

end EthLib.Execution.Transactions

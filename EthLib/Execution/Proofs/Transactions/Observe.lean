module

public import EthLib.Execution.Proofs.Evm.Call.Observe
public import EthLib.Execution.Proofs.Evm.Call.ObserveMap
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

omit [GasMeter Meter] in
/-- Mapping the state of a bind, when both parts map to the second runs, gives the second bind. -/
private theorem map_bind_of {τ α β : Type} (h : σ → τ) {m : StateT σ (Except EvmError) α}
    {f : α → StateT σ (Except EvmError) β} {m' : StateT τ (Except EvmError) α}
    {g : α → StateT τ (Except EvmError) β} (hm : ∀ s, Prod.map id h <$> m s = m' (h s))
    (hf : ∀ a s, Prod.map id h <$> f a s = g a (h s)) (s : σ) :
    Prod.map id h <$> (m >>= f) s = (m' >>= g) (h s) := by
  show Prod.map id h <$> (m s >>= fun p => f p.1 p.2) = m' (h s) >>= fun p => g p.1 p.2
  rw [← hm s]
  cases m s with
  | error e => rfl
  | ok p => exact hf p.1 p.2

omit [GasMeter Meter] in
/-- Mapping the state of a lifted result gives the lifted result. -/
private theorem map_liftExcept {τ α : Type} (h : σ → τ) (x : Except EvmError α) (s : σ) :
    Prod.map id h <$> (liftExcept x : StateT σ (Except EvmError) α) s =
      (liftExcept x : StateT τ (Except EvmError) α) (h s) := by
  cases x <;> rfl

/-- An observed message of a transaction, with its state mapped, is the mapped run.

The map must send each record of the first observer to the record of the second. -/
theorem processMessageCallWith_map [LawfulGasMeter Meter] {fork : Fork} {τ : Type} (h : σ → τ)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (g : Evm fork Meter → Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ evm result s, h (f evm result s) = g evm result (h s)) (chainId : Nat)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization) (paidWrites : Std.ExtTreeSet Address) (s : σ) :
    Prod.map id h <$> processMessageCallWith (Meter := Meter) (M := StateT σ (Except EvmError))
        (fun evm result => modify (f evm result)) chainId message state substate auths
        paidWrites s =
      processMessageCallWith (Meter := Meter) (M := StateT τ (Except EvmError))
        (fun evm result => modify (g evm result)) chainId message state substate auths
        paidWrites (h s) := by
  rw [processMessageCallWith, processMessageCallWith]
  rcases prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites
    with ⟨e, read⟩ | first
  · by_cases aborts : e.aborts <;> simp [aborts] <;> rfl
  · cases message.target with
    | none =>
      refine map_bind_of h (fun s => processCreateMessageWith_map h f g hfg _ _ _ _ _ s) ?_ s
      rintro ⟨evm, used⟩ s
      rfl
    | some target =>
      refine map_bind_of h (fun s => processMessageWith_map h f g hfg _ _ _ _ _ s) ?_ s
      rintro ⟨evm, used⟩ s
      rfl

/-- An observed run of a transaction, with its state mapped, is the mapped run.

The map must send each record of the first observer to the record of the second. -/
theorem runTransactionWith_map [LawfulGasMeter Meter] {fork : Fork} {τ : Type} (h : σ → τ)
    (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (g : Evm fork Meter → Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ evm result s, h (f evm result s) = g evm result (h s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) (s : σ) :
    Prod.map id h <$> runTransactionWith Meter (M := StateT σ (Except EvmError))
        (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
      runTransactionWith Meter (M := StateT τ (Except EvmError))
        (fun evm result => modify (g evm result)) env block included tx precompiles lifted
        (h s) := by
  rw [runTransactionWith, runTransactionWith]
  refine map_bind_of h (map_liftExcept h _) (fun target s => ?_) s
  refine map_bind_of h (map_liftExcept h _) (fun state s => ?_) s
  refine map_bind_of h (map_liftExcept h _) (fun message s => ?_) s
  refine map_bind_of h (fun s => processMessageCallWith_map h f g hfg _ _ _ _ _ _ s)
    (fun output s => ?_) s
  refine map_bind_of h (map_liftExcept h _) (fun ⟨state, gasUsed⟩ s => ?_) s
  refine map_bind_of h (map_liftExcept h _) (fun state s => ?_) s
  rfl

/-- An observed run at the fork of a transaction, with its state mapped, is the mapped run.

The map must send each record of the first observer to the record of the second, at each meter. -/
theorem processTransactionWith_map {fork : Fork} {τ : Type} (h : σ → τ)
    (f : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → σ → σ)
    (g : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → τ → τ)
    (hfg : ∀ {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) result s,
      h (f evm result s) = g evm result (h s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) (s : σ) :
    Prod.map id h <$> processTransactionWith (M := StateT σ (Except EvmError))
        (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
      processTransactionWith (M := StateT τ (Except EvmError))
        (fun evm result => modify (g evm result)) env block included tx precompiles lifted
        (h s) := by
  rw [processTransactionWith, processTransactionWith]
  split
  · rfl
  split
  · exact runTransactionWith_map h f g hfg env block included tx precompiles lifted s
  · exact runTransactionWith_map h f g hfg env block included tx precompiles lifted s

end EthLib.Execution.Transactions

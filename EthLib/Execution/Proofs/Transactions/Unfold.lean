module

public import EthLib.Execution.Transactions.Process

/-!
# Proofs: the runs of a transaction with no observer

The message of a transaction, its run and its run at a fork take an observer of the steps.

With no observer, in the monad of errors, each one unfolds to a body with no lifts.

Proofs that read that body rewrite with these equations.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

variable {Meter : Type} [GasMeter Meter]

omit [GasMeter Meter] in
/-- Lifting a result into the monad of errors leaves it unchanged. -/
private theorem liftExcept_except {ε α : Type} (x : Except ε α) :
    (liftExcept x : Except ε α) = x := by
  cases x <;> rfl

/-- The message of a transaction with no observer unfolds to its run in the monad of errors.

It prepares the first frame, then runs a creation or a call. -/
theorem processMessageCall_unfold {fork : Fork} [LawfulGasMeter Meter] (chainId : Nat)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization) (paidWrites : Std.ExtTreeSet Address) :
    processMessageCall (Meter := Meter) chainId message state substate auths paidWrites =
      match prepareFirstFrame (Meter := Meter) chainId message state substate auths
          paidWrites with
      | .error (e, read) =>
        if e.aborts then .error e else .ok (.ofHalt (state.withReadsOf read) message.reservoir e)
      | .ok first =>
        match message.target with
        | none => do
          let ⟨evm, _⟩ ← processCreateMessage fork first.message first.state first.substate
            first.meter first.held
          return .ofFrame evm 0 evm.substate.touchedAccounts
        | some target => do
          let ⟨evm, _⟩ ← processMessage fork first.message first.state first.substate
            first.meter first.held
          let touched := evm.substate.touchedAccounts
          let touched := if fork ≥ .spuriousDragon ∧ fork < .paris ∧
            evm.state.accountExistsAndIsEmpty target then touched.insert target else touched
          return .ofFrame evm first.refund touched := by
  rw [processMessageCall, processMessageCallWith]
  rcases prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites
    with ⟨e, read⟩ | first
  · rfl
  · cases message.target <;> rfl

/-- A transaction with no observer unfolds to its run in the monad of errors.

It buys the gas, runs its message, settles the gas and deletes the accounts. -/
theorem runTransaction_unfold {fork : Fork} [LawfulGasMeter Meter]
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) :
    runTransaction Meter env block included tx precompiles lifted = (do
      let state := TransactionState.ofBlock block
      let sender := included.sender
      let target ← messageTarget sender (state.getAccount sender).nonce tx
      let state ← (buyGas env state sender tx lifted).mapError .state
      let txEnv : TransactionEnvironment fork :=
        { origin := sender, gasPrice := included.gasPrice,
          blobVersionedHashes := fun _ => tx.blobHashes, precompiles }
      let gas := allocateGas fork tx included.intrinsicGas lifted
      let message ← transactionMessage env txEnv state sender target gas.execution tx
      let output ← processMessageCall (Meter := Meter) env.chainId.toNat
        { message with reservoir := gas.reservoir } state
        (startSubstate fork env.coinbase sender target tx) tx.authorizations
        (paidWrites sender target tx)
      let gasLeft := output.gasLeft + output.reservoir
      let blockGas := transactionBlockGas fork sender tx gasLeft output.refund output.stateGasUsed
      let gasBeforeRefund := gasUsed fork sender tx gasLeft 0
      let (state, gasUsed) ←
        (settleGas env output.state sender tx gasLeft output.refund lifted).mapError .state
      let state ← (deleteAccounts fork state output).mapError .state
      return ⟨state, gasUsed, blockGas, output.logs, output.simulatedLogs, output.error,
        output.output, gasBeforeRefund⟩) := by
  rw [runTransaction, runTransactionWith]
  simp only [liftExcept_except]
  rfl

/-- A transaction with no observer unfolds to its run at the meter of its fork.

From Hegotá it fails. -/
theorem processTransaction_unfold {fork : Fork} (env : BlockEnvironment fork)
    (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) :
    processTransaction env block included tx precompiles lifted =
      if .hegota ≤ fork then .error (.forkNotYetSpecified fork)
      else if fork ≥ .glamsterdam then
        runTransaction StateGasMeter env block included tx precompiles lifted
      else runTransaction Nat env block included tx precompiles lifted := by
  rfl

end EthLib.Execution.Transactions

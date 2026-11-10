module

public import EthLib.Execution.Proofs.Evm.Call.BurnRun
public import EthLib.Execution.Proofs.Transactions.Supply

/-!
# Proofs: the exact change of the supply of ether across a transaction

A transaction lowers the supply by its burned fees, the burns of its message and its deletions.

The burns of the message come from a certificate of its run, whose log drops each rollback.

The deletions remove the balance of each account to delete, read after the gas is settled.

Before Cancun, both can be above 0.

From Glamsterdam, both are 0.

Each successful run of a transaction has a certificate.

Every certificate of the run gives the same total of burns and the same deleted balances.

So each term of the change is fixed by the run.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The message call -/

/-- A certificate of the run of the message call of a transaction, with its log of burns.

A message call whose first frame fails to start burns nothing.

Otherwise its first frame runs as a creation or a call, with a certificate of that run. -/
inductive MessageCallBurns [LawfulGasMeter Meter] (chainId : Nat) (message : Message fork)
    (state : TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) : CallOutput → BurnLog → Prop
  | halt {error read}
      (preparation : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .error (error, read)) (notAborts : error.aborts = false) :
      MessageCallBurns chainId message state substate auths paid
        (.ofHalt (state.withReadsOf read) message.reservoir error) .empty
  | create {first : FirstFrame fork Meter} {evm : Evm fork Meter} {log : BurnLog}
      (preparation : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .ok first) (target : message.target = none)
      (run : RunBurns fork Meter (.create first.message first.state first.substate first.meter)
        evm log) :
      MessageCallBurns chainId message state substate auths paid
        (.ofFrame evm 0 evm.substate.touchedAccounts) log
  | call {first : FirstFrame fork Meter} {evm : Evm fork Meter} {log : BurnLog} {target : Address}
      (preparation : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .ok first) (selected : message.target = some target)
      (run : RunBurns fork Meter (.call first.message first.state first.substate first.meter)
        evm log) :
      MessageCallBurns chainId message state substate auths paid
        (.ofFrame evm first.refund (if fork ≥ .spuriousDragon ∧ fork < .paris ∧
          evm.state.accountExistsAndIsEmpty target then evm.substate.touchedAccounts.insert target
          else evm.substate.touchedAccounts)) log

/-- The supply after a certified message call plus the total of its log is the supply before. -/
theorem MessageCallBurns.supply [LawfulGasMeter Meter] {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput} {log : BurnLog}
    (h : MessageCallBurns (Meter := Meter) chainId message state substate auths paid output log) :
    output.state.supply + log.total = state.supply := by
  sorry

/-- Two certificates of a message call with the same output have the same total. -/
theorem MessageCallBurns.total_eq [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    {log log' : BurnLog}
    (h : MessageCallBurns (Meter := Meter) chainId message state substate auths paid output log)
    (h' : MessageCallBurns (Meter := Meter) chainId message state substate auths paid output log') :
    log.total = log'.total := by
  have := h.supply
  have := h'.supply
  omega

/-- Every successful message call of a transaction has a certificate. -/
theorem processMessageCall_messageCallBurns [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    ∃ log,
      MessageCallBurns (Meter := Meter) chainId message state substate auths paid output log := by
  sorry

/-! ## The transaction -/

/-- A certificate of a run of a transaction with the gas meter `Meter`, its burns and deletions.

The run takes its steps in order, and the log certifies the run of its message call.

The deleted balances are those of the state after the gas is settled. -/
def TransactionBurnsWith (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (env : BlockEnvironment fork) (block : State.BlockState) (included : Included)
    (tx : Transaction) (out : TransactionOutput) (log : BurnLog) (deleted : Nat) : Prop :=
  ∃ target bought message output settled,
    TransactionRun Meter env block included tx out target bought message output settled ∧
    MessageCallBurns (Meter := Meter) env.chainId.toNat
        { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
        (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) output log ∧
    deleted = deletedBalances fork settled output

/-- Every successful run of a transaction has a certificate. -/
theorem runTransaction_transactionBurnsWith [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) :
    ∃ log deleted, TransactionBurnsWith Meter env block included tx out log deleted := by
  sorry

/-- A certificate of a run of a transaction gives the exact change of the supply.

The supply at the end plus every loss of the run is the supply at the start.

The losses are the burned fees, the burns of the message and the deleted balances.

The gas limit must cover the least gas, and the price must cover the base fee. -/
theorem TransactionBurnsWith.supply_eq [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {log : BurnLog} {deleted : Nat}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : TransactionBurnsWith Meter env block included tx out log deleted) :
    out.state.supply + burnedFees env tx out.gasUsed + log.total + deleted =
      (TransactionState.ofBlock block).supply := by
  sorry

/-- Two certificates of a run of a transaction give the same burns and deleted balances. -/
theorem TransactionBurnsWith.unique [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {log log' : BurnLog} {deleted deleted' : Nat}
    (h : TransactionBurnsWith Meter env block included tx out log deleted)
    (h' : TransactionBurnsWith Meter env block included tx out log' deleted') :
    log'.total = log.total ∧ deleted' = deleted := by
  sorry

/-- A certificate of a run of a transaction with the gas meter that it runs with at its fork. -/
def TransactionBurns (env : BlockEnvironment fork) (block : State.BlockState)
    (included : Included) (tx : Transaction) (out : TransactionOutput) (log : BurnLog)
    (deleted : Nat) : Prop :=
  if fork ≥ .glamsterdam then
    TransactionBurnsWith StateGasMeter env block included tx out log deleted
  else TransactionBurnsWith Nat env block included tx out log deleted

/-- Every transaction that runs has a certificate, at every fork. -/
theorem processTransaction_transactionBurns {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out) :
    ∃ log deleted, TransactionBurns env block included tx out log deleted := by
  sorry

/-- A certificate of a transaction gives the exact change of the supply, at every fork.

The gas limit must cover the least gas, and the price must cover the base fee. -/
theorem TransactionBurns.supply_eq {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput} {log : BurnLog}
    {deleted : Nat} (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : TransactionBurns env block included tx out log deleted) :
    out.state.supply + burnedFees env tx out.gasUsed + log.total + deleted =
      (TransactionState.ofBlock block).supply := by
  sorry

/-- Two certificates of a transaction have the same total and the same deleted balances. -/
theorem TransactionBurns.unique {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput} {log log' : BurnLog}
    {deleted deleted' : Nat} (h : TransactionBurns env block included tx out log deleted)
    (h' : TransactionBurns env block included tx out log' deleted') :
    log'.total = log.total ∧ deleted' = deleted := by
  sorry

/-- A transaction that runs lowers the supply by exactly its losses, at every fork.

The losses are its burned fees, its burns of SELFDESTRUCT and its deleted balances.

A burn of SELFDESTRUCT counts only when no rollback drops it.

The last two come from a certificate of the run, and every certificate gives the same two values.

So the bound by the burned fees alone is an equality exactly when both are 0.

The gas limit must cover the least gas, and the price must cover the base fee.

The checks of the block ensure both. -/
theorem processTransaction_supply_eq {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : processTransaction env block included tx = .ok out) :
    ∃ log deleted, TransactionBurns env block included tx out log deleted ∧
      out.state.supply + burnedFees env tx out.gasUsed + log.total + deleted =
        (TransactionState.ofBlock block).supply := by
  obtain ⟨log, deleted, burns⟩ := processTransaction_transactionBurns h
  exact ⟨log, deleted, burns, burns.supply_eq hMin hPrice⟩

end EthLib.Execution.Transactions

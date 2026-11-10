module

public import EthLib.Execution.Proofs.Evm.Call.BurnRun
public import EthLib.Execution.Proofs.Transactions.Supply

/-!
# Proofs: the exact change of the supply of ether across a transaction

A transaction lowers the supply by its burned fees, the burns of its message and its deletions.

The burns of the message come from a certificate of its run, whose log drops each rollback.

The deletions remove the balance of each account to delete, read after the gas is settled.

From Glamsterdam, both are 0.

Each successful run of a transaction has a certificate.

The deleted balances are a function of the run.

The certificate follows the interpreter, so the total of its burns is a function of the run too.

The log splits that total into burns, each from a step of SELFDESTRUCT with its burn.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The message call -/

/-- A certificate of the run of the message call of a transaction, with the state it ends in.

A message call whose first frame fails to start burns nothing, and keeps the state up to reads.

Otherwise its first frame runs as a creation or a call, with a certificate of that run. -/
inductive MessageCallBurns [LawfulGasMeter Meter] (chainId : Nat) (message : Message fork)
    (state : TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) : TransactionState → BurnLog → Prop
  | halt {error read}
      (preparation : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .error (error, read)) :
      MessageCallBurns chainId message state substate auths paid (state.withReadsOf read) .empty
  | create {first : FirstFrame fork Meter} {evm : Evm fork Meter} {log : BurnLog}
      (preparation : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .ok first) (target : message.target = none)
      (run : RunBurns fork Meter (.create first.message first.state first.substate first.meter)
        evm log) :
      MessageCallBurns chainId message state substate auths paid evm.state log
  | call {first : FirstFrame fork Meter} {evm : Evm fork Meter} {log : BurnLog} {target : Address}
      (preparation : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
        .ok first) (selected : message.target = some target)
      (run : RunBurns fork Meter (.call first.message first.state first.substate first.meter)
        evm log) :
      MessageCallBurns chainId message state substate auths paid evm.state log

/-- The supply after a certified message call plus the total of its log is the supply before. -/
theorem MessageCallBurns.supply [LawfulGasMeter Meter] {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {ended : TransactionState} {log : BurnLog}
    (h : MessageCallBurns (Meter := Meter) chainId message state substate auths paid ended log) :
    ended.supply + log.total = state.supply := by
  cases h with
  | halt => rfl
  | create preparation _ run => exact run.supply.trans (supply_prepareFirstFrame preparation)
  | call preparation _ run => exact run.supply.trans (supply_prepareFirstFrame preparation)

/-- From Glamsterdam, a certified message call burns nothing. -/
theorem MessageCallBurns.total_eq_zero_of_glamsterdam [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {ended : TransactionState}
    {log : BurnLog} (hfork : .glamsterdam ≤ fork)
    (h : MessageCallBurns (Meter := Meter) chainId message state substate auths paid ended log) :
    log.total = 0 := by
  cases h with
  | halt => rfl
  | create _ _ run => exact run.total_eq_zero_of_glamsterdam hfork
  | call _ _ run => exact run.total_eq_zero_of_glamsterdam hfork

/-- Two certificates of a message call that end in the same state have the same total. -/
theorem MessageCallBurns.total_eq [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {ended : TransactionState}
    {log log' : BurnLog}
    (h : MessageCallBurns (Meter := Meter) chainId message state substate auths paid ended log)
    (h' : MessageCallBurns (Meter := Meter) chainId message state substate auths paid ended log') :
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
    ∃ log, MessageCallBurns (Meter := Meter) chainId message state substate auths paid
      output.state log := by
  unfold processMessageCall at h
  split at h
  · rename_i error read preparation
    split at h
    · cases h
    · cases h
      exact ⟨.empty, .halt preparation⟩
  · rename_i first preparation
    split at h
    · rename_i target
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      obtain ⟨log, trace⟩ := (processMessage_runBurns first.message.gas).2 first.message first.state
        first.substate first.meter first.held rfl ⟨evm, used⟩ hrun
      rw [state_ofFrame]
      exact ⟨log, .create preparation target trace⟩
    · rename_i target selected
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      obtain ⟨log, trace⟩ := (processMessage_runBurns first.message.gas).1 first.message first.state
        first.substate first.meter first.held rfl ⟨evm, used⟩ hrun
      rw [state_ofFrame]
      exact ⟨log, .call preparation selected trace⟩

/-! ## The transaction -/

/-- A certificate of a run of a transaction with the gas meter `Meter`, a log and deleted balances.

The run takes its steps in order, and the log certifies the run of its message call.

The deleted balances are those of the accounts to delete, in the state after the gas is settled.
-/
def TransactionBurnsWith (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (env : BlockEnvironment fork) (block : State.BlockState) (included : Included)
    (tx : Transaction) (out : TransactionOutput) (log : BurnLog) (deleted : Nat) : Prop :=
  ∃ target bought message output settled,
    TransactionRun Meter env block included tx out target bought message output settled ∧
    MessageCallBurns (Meter := Meter) env.chainId.toNat
        { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
        (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) output.state log ∧
    deleted = deletedBalances fork settled output

/-- Every successful run of a transaction has a certificate. -/
theorem runTransaction_transactionBurnsWith [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) :
    ∃ log deleted, TransactionBurnsWith Meter env block included tx out log deleted := by
  obtain ⟨target, bought, message, output, settled, run⟩ := runTransaction_eq_ok h
  obtain ⟨log, trace⟩ := processMessageCall_messageCallBurns run.2.2.2.1
  exact ⟨log, deletedBalances fork settled output,
    ⟨target, bought, message, output, settled, run, trace, rfl⟩⟩

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
  obtain ⟨target, bought, message, output, settled, ⟨ht, hb, hm, ho, -, hs, hd⟩, trace, hdel⟩ := h
  have hfees := supply_buyGas_settleGas hMin hPrice hb hs
  have hmsg := trace.supply
  have hdelete := supply_deleteAccounts_eq hd
  rw [hdel]
  omega

/-- Two certificates of a run of a transaction give the same burns and deleted balances. -/
theorem TransactionBurnsWith.unique [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    {log log' : BurnLog} {deleted deleted' : Nat}
    (h : TransactionBurnsWith Meter env block included tx out log deleted)
    (h' : TransactionBurnsWith Meter env block included tx out log' deleted') :
    log'.total = log.total ∧ deleted' = deleted := by
  obtain ⟨t, b, m, o, st, run, trace, hdel⟩ := h
  obtain ⟨t', b', m', o', st', run', trace', hdel'⟩ := h'
  obtain ⟨rt, rb, rm, ro, rs⟩ := TransactionRun.unique run run'
  subst rt rb rm ro rs
  exact ⟨(MessageCallBurns.total_eq trace trace').symm, hdel'.trans hdel.symm⟩

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
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · rename_i hfork
    simpa only [TransactionBurns, hfork, ↓reduceIte] using runTransaction_transactionBurnsWith h
  · rename_i hfork
    simpa only [TransactionBurns, hfork, ↓reduceIte] using runTransaction_transactionBurnsWith h

/-- A certificate of a transaction gives the exact change of the supply, at every fork.

The gas limit must cover the least gas, and the price must cover the base fee. -/
theorem TransactionBurns.supply_eq {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput} {log : BurnLog}
    {deleted : Nat} (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : TransactionBurns env block included tx out log deleted) :
    out.state.supply + burnedFees env tx out.gasUsed + log.total + deleted =
      (TransactionState.ofBlock block).supply := by
  unfold TransactionBurns at h
  split at h <;> exact h.supply_eq hMin hPrice

/-- Two certificates of a transaction have the same total and the same deleted balances. -/
theorem TransactionBurns.unique {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput} {log log' : BurnLog}
    {deleted deleted' : Nat} (h : TransactionBurns env block included tx out log deleted)
    (h' : TransactionBurns env block included tx out log' deleted') :
    log'.total = log.total ∧ deleted' = deleted := by
  unfold TransactionBurns at h h'
  by_cases hfork : fork ≥ .glamsterdam
  · simp only [hfork, ↓reduceIte] at h h'
    exact TransactionBurnsWith.unique h h'
  · simp only [hfork, ↓reduceIte] at h h'
    exact TransactionBurnsWith.unique h h'

/-- From Glamsterdam, a certificate of a transaction has no burns and no deleted balances. -/
theorem TransactionBurns.eq_zero_of_glamsterdam {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput} {log : BurnLog}
    {deleted : Nat} (hfork : .glamsterdam ≤ fork)
    (h : TransactionBurns env block included tx out log deleted) :
    log.total = 0 ∧ deleted = 0 := by
  unfold TransactionBurns at h
  simp only [ge_iff_le, hfork, ↓reduceIte] at h
  obtain ⟨_, _, _, _, settled, _, trace, hdel⟩ := h
  refine ⟨trace.total_eq_zero_of_glamsterdam hfork, ?_⟩
  rw [hdel]
  simp only [deletedBalances, ge_iff_le, hfork, ↓reduceIte]

/-- A transaction that runs lowers the supply by exactly its losses, at every fork.

The losses are its burned fees, its burns of SELFDESTRUCT and its deleted balances.

A burn of SELFDESTRUCT counts only when no rollback drops it.

The last two come from a certificate of the run.

Every certificate of the run gives the same two values, as a separate theorem proves.

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

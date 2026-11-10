module

public import EthLib.Execution.Proofs.Evm.Call.BurnRun
public import EthLib.Execution.Proofs.Transactions.Supply

/-!
# Proofs: exact ether accounting of a transaction

The surviving burn log of the message and the balances removed at deletion fill the supply gap.

The log follows the actual execution and discards the burns of reverted frames.

The deletion term reads each marked balance after gas settlement, before any account is deleted.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open State (TransactionState)
open EthLib.Execution.Fees.BlobBaseFee (calculateTotalBlobGas)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The first frame, its actual run certificate, and the output that the message call returns. -/
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

/-- The supply after the message call, plus its surviving burns, is its starting supply. -/
theorem MessageCallBurns.supply [LawfulGasMeter Meter] {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput} {log : BurnLog}
    (h : MessageCallBurns (Meter := Meter) chainId message state substate auths paid output log) :
    output.state.supply + log.total = state.supply := by
  cases h with
  | halt => rfl
  | create preparation _ run =>
    rw [state_ofFrame]
    exact run.supply.trans (supply_prepareFirstFrame preparation)
  | call preparation _ run =>
    rw [state_ofFrame]
    exact run.supply.trans (supply_prepareFirstFrame preparation)

/-- The actual message call yields a certificate and its surviving burn log. -/
theorem messageCallBurns_processMessageCall [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    ∃ log,
      MessageCallBurns (Meter := Meter) chainId message state substate auths paid output log := by
  unfold processMessageCall at h
  split at h
  · rename_i error read preparation
    split at h
    · cases h
    · cases h
      exact ⟨.empty, .halt preparation (Bool.eq_false_iff.mpr (by assumption))⟩
  · rename_i first preparation
    split at h
    · rename_i target
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      obtain ⟨log, trace⟩ := (processMessage_runBurns first.message.gas).2 first.message first.state
        first.substate first.meter first.held rfl ⟨evm, used⟩ hrun
      exact ⟨log, .create preparation target trace⟩
    · rename_i target selected
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      obtain ⟨log, trace⟩ := (processMessage_runBurns first.message.gas).1 first.message first.state
        first.substate first.meter first.held rfl ⟨evm, used⟩ hrun
      exact ⟨log, .call preparation selected trace⟩

/-- The balances removed at transaction end, read before deletion and counted once each.

From Glamsterdam, deletion preserves every balance, so this term is zero. -/
def deletedBalances (fork : Fork) (state : TransactionState) (output : CallOutput) : Nat :=
  if fork ≥ .glamsterdam then 0
  else (output.accountsToDelete.toList.map state.balanceOf).sum

/-- Deletion removes exactly the pre-deletion balances of the marked accounts. -/
theorem supply_deleteAccounts_eq {state state' : TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') :
    state'.supply + deletedBalances fork state output = state.supply := by
  have fold : ∀ (addresses : List Address), addresses.Nodup →
      ∀ (init final : TransactionState),
      addresses.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      final.supply + (if fork ≥ .glamsterdam then 0 else
        (addresses.map init.balanceOf).sum) = init.supply := by
    intro addresses
    induction addresses with
    | nil =>
      intro _ init final h
      cases h
      simp
    | cons address rest ih =>
      intro distinct init final h
      obtain ⟨notMem, distinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨mid, hm, h⟩ := bind_ok_iff.mp h
      have tail := ih distinct mid final h
      split at hm
      · rename_i hfork
        have hs := TransactionState.supply_clearAccountPreservingBalance hm
        simp only [hfork, ↓reduceIte, Nat.add_zero] at tail ⊢
        exact tail.trans hs
      · rename_i hfork
        cases hm
        have hs := TransactionState.supply_destroyAccount init address
        have balances : rest.map (init.destroyAccount address).balanceOf =
            rest.map init.balanceOf := by
          refine List.map_congr_left fun other mem => ?_
          have hne : other ≠ address := fun same => notMem (same ▸ mem)
          simp only [TransactionState.balanceOf, TransactionState.getAccount_destroyAccount,
            hne, ↓reduceIte]
        simp only [hfork, ↓reduceIte, balances] at tail
        simp only [hfork, ↓reduceIte, List.map_cons, List.sum_cons]
        omega
  unfold deleteAccounts at h
  obtain ⟨mid, hm, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hm
  have distinct : output.accountsToDelete.toList.Nodup :=
    (Std.ExtTreeSet.distinct_toList).imp fun hne same => hne (by simp [same])
  have hs := fold _ distinct _ _ hm
  rw [TransactionState.supply_destroyTouchedEmptyAccounts]
  exact hs


/-- The actual transaction pipeline and the certified log of its message.

The deletion amount is computed from its state after settlement and its marked accounts. -/
def TransactionBurnsWith (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (env : BlockEnvironment fork) (block : State.BlockState) (included : Included)
    (tx : Transaction) (out : TransactionOutput) (log : BurnLog) (deleted : Nat) : Prop :=
  let gas := allocateGas fork tx included.intrinsicGas
  ∃ target bought message output settled,
    messageTarget included.sender
        ((TransactionState.ofBlock block).getAccount included.sender).nonce tx = .ok target ∧
    buyGas env (TransactionState.ofBlock block) included.sender tx = .ok bought ∧
    transactionMessage env ⟨included.sender, included.gasPrice, fun _ => tx.blobHashes⟩ bought
        included.sender target gas.execution tx = .ok message ∧
    processMessageCall (Meter := Meter) env.chainId.toNat
        { message with reservoir := gas.reservoir } bought
        (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) = .ok output ∧
    MessageCallBurns (Meter := Meter) env.chainId.toNat
        { message with reservoir := gas.reservoir } bought
        (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) output log ∧
    settleGas env output.state included.sender tx (output.gasLeft + output.reservoir)
        output.refund = .ok (settled, out.gasUsed) ∧
    deleteAccounts fork settled output = .ok out.state ∧
    deleted = deletedBalances fork settled output

/-- The burn certificate uses the same gas meter as the transaction at its fork. -/
def TransactionBurns (env : BlockEnvironment fork) (block : State.BlockState)
    (included : Included) (tx : Transaction) (out : TransactionOutput) (log : BurnLog)
    (deleted : Nat) : Prop :=
  if fork ≥ .glamsterdam then
    TransactionBurnsWith StateGasMeter env block included tx out log deleted
  else TransactionBurnsWith Nat env block included tx out log deleted

/-- A successful transaction has a certified burn log and exact supply accounting.

The three losses are its burned fees, the surviving SELFDESTRUCT burns, and deleted balances. -/
theorem runTransaction_supply_eq [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : runTransaction Meter env block included tx = .ok out) :
    ∃ log deleted, TransactionBurnsWith Meter env block included tx out log deleted ∧
      out.state.supply + burnedFees env tx out.gasUsed + log.total + deleted =
        (TransactionState.ofBlock block).supply := by
  obtain ⟨target, bought, message, output, settled, ht, hb, hm, ho, -, hs, hd⟩ :=
    runTransaction_eq_ok h
  obtain ⟨log, trace⟩ := messageCallBurns_processMessageCall ho
  refine ⟨log, deletedBalances fork settled output,
    ⟨target, bought, message, output, settled, ht, hb, hm, ho, trace, hs, hd, rfl⟩, ?_⟩
  obtain ⟨hbuy, -⟩ := supply_buyGas hb
  have hmsg := trace.supply
  have hset := supply_settleGas hs
  have hdel := supply_deleteAccounts_eq hd
  have hused := settleGas_gasUsed hs
  have conserve := settlement_conserves hMin hPrice (output.gasLeft + output.reservoir)
    output.refund
  dsimp only at hset conserve
  simp only [settlement, priorityFeeOf] at hset conserve
  simp only [burnedFees]
  rw [hused]
  generalize gasUsed fork included.sender tx (output.gasLeft + output.reservoir) output.refund =
    g at hset conserve ⊢
  omega

/-- At every fork, the end supply plus every loss of the actual transaction is its start supply.

The bound on the least gas and the base fee are the checks made before the transaction runs. -/
theorem processTransaction_supply_eq {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (h : processTransaction env block included tx = .ok out) :
    ∃ log deleted, TransactionBurns env block included tx out log deleted ∧
      out.state.supply + burnedFees env tx out.gasUsed + log.total + deleted =
        (TransactionState.ofBlock block).supply := by
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · rename_i hfork
    simpa only [TransactionBurns, hfork, ↓reduceIte] using runTransaction_supply_eq hMin hPrice h
  · rename_i hfork
    simpa only [TransactionBurns, hfork, ↓reduceIte] using runTransaction_supply_eq hMin hPrice h

end EthLib.Execution.Transactions

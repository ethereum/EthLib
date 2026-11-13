module

public import EthLib.Execution.Proofs.Evm.Call.Overflow
public import EthLib.Execution.Proofs.Transactions.Supply
import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: no transaction overflows a balance when the supply leaves room

A transaction first takes from its sender the fee for its whole gas limit and its blob gas.

The authorizations keep every balance.

So its first message starts with at most the supply before the transaction.

No call or creation overflows a balance when the supply it starts with leaves room.

A supply leaves room when it is below `2^256`, or twice it is before Cancun.

The settlement credits the refund of the sender and the priority fee of the beneficiary.

Those two add up to at most the fee that the sender paid.

So each credit raises one balance to at most the supply before the transaction.

The deletions at the end credit nothing.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

section

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A read of code never fails for a balance that would overflow. -/
theorem getCode_ne_balanceOverflow (state : TransactionState) (codeHash : Base.Hash32)
    (address : Address) : state.getCode codeHash ≠ .error (.balanceOverflow address) := by
  intro h
  unfold State.TransactionState.getCode at h
  repeat' split at h
  all_goals try cases h
  unfold State.State.getCode at h
  repeat' split at h
  all_goals cases h

/-- A change of one account fails for an overflow only when the update it applies does. -/
private theorem modifyState_ne_balanceOverflow {state : TransactionState}
    {address other : Address} {f : State.Account → Except State.StateError State.Account}
    (hf : ∀ account, f account ≠ .error (.balanceOverflow other)) :
    state.modifyState fork address f ≠ .error (.balanceOverflow other) := fun h =>
  hf _ (State.TransactionState.modifyState_eq_error.mp h)

/-- A credit of ether never overflows a balance when the supply plus the credit is below `2^256`. -/
private theorem creditEther_ne_balanceOverflow {state : TransactionState}
    {address : Address} {amount : Nat} (fits : state.supply + amount < 2 ^ 256)
    (other : Address) :
    creditEther fork state address amount ≠ .error (.balanceOverflow other) := by
  unfold creditEther
  split
  · rename_i hlt
    refine State.TransactionState.createEther_ne_balanceOverflow ?_ other
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact fits
  · omega

/-- The deletions at the end of a transaction never fail for a balance that would overflow. -/
private theorem deleteAccounts_ne_balanceOverflow (state : TransactionState)
    (output : CallOutput) (other : Address) :
    deleteAccounts fork state output ≠ .error (.balanceOverflow other) := by
  have fold : ∀ (l : List Address) (init : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init ≠ .error (.balanceOverflow other) := by
    intro l
    induction l with
    | nil => exact fun _ h => by cases h
    | cons address rest ih =>
      intro init h
      rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
      · split at h
        · exact modifyState_ne_balanceOverflow (fun _ h => by cases h) h
        · cases h
      · exact ih mid h
  intro h
  unfold deleteAccounts at h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at h
    exact fold _ _ h
  · cases h

/-- The purchase of gas never fails for a balance that would overflow. -/
private theorem buyGas_ne_balanceOverflow (env : BlockEnvironment fork)
    (state : TransactionState) (sender : Address) (tx : Transaction) (other : Address) :
    buyGas env state sender tx ≠ .error (.balanceOverflow other) := by
  intro h
  unfold buyGas at h
  obtain ⟨mid, hmid⟩ := State.TransactionState.incrementNonce_isOk fork state sender
  simp only [hmid, bind, Except.bind] at h
  refine modifyState_ne_balanceOverflow (fun _ h => ?_) h
  split at h <;> cases h

/-- The settlement never overflows a balance when the supply plus both credits is below `2^256`. -/
private theorem settleGas_ne_balanceOverflow {env : BlockEnvironment fork}
    {state : TransactionState} {sender : Address} {tx : Transaction} {gasLeft refund : Nat}
    (fits : state.supply +
      (settlement fork (baseFeeOf env) sender tx gasLeft refund).senderRefund +
      (settlement fork (baseFeeOf env) sender tx gasLeft refund).priorityFee < 2 ^ 256)
    (other : Address) :
    settleGas env state sender tx gasLeft refund ≠ .error (.balanceOverflow other) := by
  intro he
  unfold settleGas at he
  rcases Base.bind_eq_error he with he | ⟨mid, hmid, he⟩
  · exact creditEther_ne_balanceOverflow (by omega) _ he
  have hsupply := (supply_creditEther hmid).1
  rcases Base.bind_eq_error he with he | ⟨paid, -, he⟩
  · unfold payBeneficiary at he
    split at he
    · cases he
    · exact creditEther_ne_balanceOverflow (by omega) _ he
  · cases he

/-- The charge of an authorization never fails for a balance that would overflow. -/
private theorem chargeAuthorization_ne_balanceOverflow [LawfulGasMeter Meter]
    {done : Delegations Meter} {authority : Address} {auth : Authorization}
    (address : Address) :
    chargeAuthorization done authority auth ≠ .error (.state (.balanceOverflow address)) := by
  intro h
  unfold chargeAuthorization at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | cases LawfulGasMeter.charge_error h
    | cases LawfulGasMeter.chargeState_error h
    | (unfold Except.mapError at h
       split at h
       · rename_i he'
         cases h
         exact getCode_ne_balanceOverflow _ _ _ he'
       · cases h)

/-- One authorization never fails for a balance that would overflow. -/
private theorem applyAuthorization_ne_balanceOverflow [LawfulGasMeter Meter] {chainId : Nat}
    {done : Delegations Meter} {auth : Authorization} (address : Address)
    (read : TransactionState) :
    applyAuthorization fork chainId done auth ≠
      .error (.state (.balanceOverflow address), read) := by
  intro h
  unfold applyAuthorization at h
  dsimp only at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | (unfold Except.mapError at h
       split at h
       · rename_i he'
         simp only [Except.error.injEq, Function.comp_apply, Prod.mk.injEq,
           EvmError.state.injEq] at h
         obtain ⟨rfl, -⟩ := h
         first
           | (unfold authorityAccepts at he'
              rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
              · exact getCode_ne_balanceOverflow _ _ _ he'
              · cases he')
           | (unfold payAuthorization at he'
              split at he'
              · rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
                · exact chargeAuthorization_ne_balanceOverflow _ he'
                · cases he'
              · cases he')
           | (unfold delegate at he'
              rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
              · unfold State.TransactionState.setCode at he'
                exact modifyState_ne_balanceOverflow (fun _ h => by cases h) he'
              rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
              · exact modifyState_ne_balanceOverflow (fun _ h => by cases h) he'
              · cases he')
       · cases h)

/-- A list of authorizations never fails for a balance that would overflow. -/
private theorem foldlM_applyAuthorization_ne_balanceOverflow [LawfulGasMeter Meter]
    {chainId : Nat} (address : Address) (read : TransactionState) :
    ∀ {auths : List Authorization} {start : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start ≠
        .error (.state (.balanceOverflow address), read)
  | [], _, h => by cases h
  | _ :: _, _, h => by
    rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact applyAuthorization_ne_balanceOverflow address read h
    · exact foldlM_applyAuthorization_ne_balanceOverflow address read h

/-- The first frame of a message never fails for a balance that would overflow. -/
private theorem prepareFirstFrame_ne_balanceOverflow [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (address : Address)
    (read : TransactionState) :
    prepareFirstFrame (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.balanceOverflow address), read) := by
  intro h
  unfold prepareFirstFrame at h
  split at h <;> dsimp only at h <;>
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | (cases h; done)
    | exact foldlM_applyAuthorization_ne_balanceOverflow address read h
    | (unfold Except.mapError at h
       split at h
       · rename_i he'
         simp only [Except.error.injEq, Prod.mk.injEq, EvmError.state.injEq] at h
         obtain ⟨rfl, -⟩ := h
         first
           | cases LawfulGasMeter.charge_error he'
           | cases LawfulGasMeter.chargeState_error he'
           | exact getCode_ne_balanceOverflow _ _ _ he'
       · cases h)

/-- The message of a transaction never overflows a balance when its start supply leaves room. -/
theorem processMessageCall_ne_balanceOverflow [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    (room : SupplyRoom fork state.supply) (address : Address) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.balanceOverflow address)) := by
  intro h
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
      exact prepareFirstFrame_ne_balanceOverflow address read hprep
    · cases h
  · rw [hprep] at h
    dsimp only at h
    have froom : SupplyRoom fork first.state.supply := by
      rwa [supply_prepareFirstFrame hprep]
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processCreateMessage_ne_balanceOverflow froom address h
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processMessage_ne_balanceOverflow froom address h
      · cases h

/-- A run of a transaction never overflows a balance when the supply before it leaves room.

Its gas limit must cover the least gas, and its price must cover the base fee. -/
private theorem runTransaction_ne_balanceOverflow [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {included : Included} {tx : Transaction}
    (hMin : minimumGas fork included.sender tx ≤ tx.gas.toNat)
    (hPrice : baseFeeOf env ≤ effectiveGasPrice (baseFeeOf env) tx)
    (room : SupplyRoom fork (TransactionState.ofBlock block).supply) (address : Address) :
    runTransaction Meter env block included tx ≠ .error (.state (.balanceOverflow address)) := by
  intro h
  unfold runTransaction at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · unfold Except.mapError at h
      split at h <;> cases h
  rcases Base.bind_eq_error h with h | ⟨bought, hbought, h⟩
  · unfold Except.mapError at h
    split at h
    · rename_i he'
      cases h
      exact buyGas_ne_balanceOverflow _ _ _ _ _ he'
    · cases h
  have hbought := Base.mapError_ok_iff.mp hbought
  have hbuy := (supply_buyGas hbought).1
  rcases Base.bind_eq_error h with h | ⟨message, -, h⟩
  · unfold transactionMessage at h
    split at h
    · dsimp only at h
      generalize hx : Except.mapError EvmError.state _ = x at h
      cases x with
      | error e' =>
        cases h
        unfold Except.mapError at hx
        split at hx
        · rename_i he'
          cases hx
          exact getCode_ne_balanceOverflow _ _ _ he'
        · cases hx
      | ok _ => cases h
    · cases h
  rcases Base.bind_eq_error h with h | ⟨output, houtput, h⟩
  · exact processMessageCall_ne_balanceOverflow (room.mono (by omega)) address h
  have hended := (supplyLe_processMessageCall houtput).1
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · unfold Except.mapError at h
    split at h
    · rename_i he'
      cases h
      refine settleGas_ne_balanceOverflow ?_ _ he'
      have conserve := settlement_conserves hMin hPrice
        (output.gasLeft + output.reservoir) output.refund
      have := room.lt
      dsimp only at conserve
      omega
    · cases h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · unfold Except.mapError at h
    split at h
    · rename_i he'
      cases h
      exact deleteAccounts_ne_balanceOverflow _ _ _ he'
    · cases h
  · cases h

end

/-- No transaction fails with the state error for a balance that would overflow.

It must pass its checks on the block state it runs on.

The supply of that state must leave room for the credits of a message. -/
theorem processTransaction_ne_balanceOverflow {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {chainId : UInt64} {used : BlockGas} {tx : Transaction}
    {included : Included}
    (checked : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (room : SupplyRoom fork (TransactionState.ofBlock block).supply) (address : Address) :
    processTransaction env block included tx ≠ .error (.state (.balanceOverflow address)) := by
  obtain ⟨-, valid, -, -, -, fee, -⟩ := checkInclusion_ok checked
  have hMin := (validateTransaction_ok valid).2.1
  have hPrice := le_effectiveGasPrice fee
  unfold processTransaction
  split
  · nofun
  split
  · exact runTransaction_ne_balanceOverflow hMin hPrice room address
  · exact runTransaction_ne_balanceOverflow hMin hPrice room address

end EthLib.Execution.Transactions

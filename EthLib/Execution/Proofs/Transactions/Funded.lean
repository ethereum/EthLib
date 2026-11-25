module

public import EthLib.Execution.Proofs.Transactions.Unfold
public import EthLib.Execution.Proofs.Evm.Call.Funded
public import EthLib.Execution.Proofs.Transactions.Process
import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: a transaction that may enter its block never fails for a balance below an amount

A transaction takes its fee from the sender, then moves its value to the target.

The checks of the transaction make the sender hold both the fee and the value.

No later step fails for a balance that is too low.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork Hash32)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)
open EthLib.Execution.Fees.BlobBaseFee (calculateTotalBlobGas)

section

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A read of code never fails for a short balance. -/
theorem getCode_ne_insufficientBalance (state : TransactionState) (codeHash : Hash32)
    (address : Address) : state.getCode codeHash ≠ .error (.insufficientBalance address) :=
  fun h => by cases State.TransactionState.error_getCode h

/-- A sender that holds the fee and an amount more buys the gas, and keeps that amount. -/
private theorem buyGas_ok {env : BlockEnvironment fork} {state : TransactionState}
    {sender : Address} {tx : Transaction} {rest : Nat}
    (funds : tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
      calculateTotalBlobGas tx * blobGasPriceOf env + rest ≤
        (state.getAccount sender).balance.toNat) :
    ∃ state', buyGas env state sender tx = .ok state' ∧
      rest ≤ (state'.getAccount sender).balance.toNat := by
  cases hb : buyGas env state sender tx with
  | error e =>
    exfalso
    unfold buyGas at hb
    rw [paidBaseFee_empty] at hb
    obtain ⟨mid, hmid⟩ := State.TransactionState.incrementNonce_isOk fork state sender
    simp only [hmid, bind, Except.bind] at hb
    have hf := State.TransactionState.modifyState_eq_error.mp hb
    rw [(State.TransactionState.getAccount_incrementNonce hmid).1] at hf
    dsimp only at hf
    split at hf
    · cases hf
    · omega
  | ok state' =>
    refine ⟨state', rfl, ?_⟩
    have := buyGas_sender rfl hb
    omega

/-- One authorization keeps every balance. -/
private theorem balance_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done')
    (address : Address) :
    (done'.state.getAccount address).balance = (done.state.getAccount address).balance := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · rfl
  · simp
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    obtain ⟨-, hself, hother⟩ := delegate_eq_ok hdelegate
    by_cases same : address = authority
    · subst same
      rw [hself]
      simp
    · have := hother address same
      unfold State.TransactionState.getAccount at this ⊢
      rw [this]
      simp

/-- Authorizations that succeed keep every balance. -/
private theorem balance_foldlM_applyAuthorization {chainId : Nat} (address : Address) :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      (done.state.getAccount address).balance = (start.state.getAccount address).balance
  | [], _, _, h => by
    cases h
    rfl
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := Base.bind_ok_iff.mp h
    exact (balance_foldlM_applyAuthorization address h).trans
      (balance_applyAuthorization hnext address)

/-- A message that keeps the caller, the value and the move stays funded on equal balances. -/
private theorem Funded.of_balance {message message' : Message fork}
    {state state' : TransactionState} (funded : Funded message state)
    (caller : message'.caller = message.caller) (value : message'.value = message.value)
    (transfers : message'.shouldTransferValue = message.shouldTransferValue)
    (balance : (state'.getAccount message.caller).balance =
      (state.getAccount message.caller).balance) :
    Funded message' state' := fun t => by
  rw [caller, value, balance]
  exact funded (transfers ▸ t)

/-- The first frame of a funded message is funded. -/
private theorem funded_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (funded : Funded message state)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    Funded first.message first.state := by
  have read : ∀ (s : TransactionState) (address other : Address),
      ((s.recordAccountRead address).getAccount other).balance = (s.getAccount other).balance :=
    fun _ _ _ => by simp
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact Funded.of_balance funded rfl rfl rfl (read _ _ _)
      · obtain ⟨m, -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact Funded.of_balance funded rfl rfl rfl (read _ _ _)
    · obtain ⟨m, h, -⟩ := Base.bind_ok_iff.mp h
      cases h
  · rename_i target _
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := Base.bind_ok_iff.mp h
    have hauth := balance_foldlM_applyAuthorization message.caller hdone
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : (read0.getAccount message.caller).balance =
        (state.getAccount message.caller).balance := by
      subst hread
      split
      · exact (read _ _ _).trans hauth
      · exact hauth
    split at h <;>
    · obtain ⟨m, -, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact Funded.of_balance funded rfl rfl rfl ((read _ _ _).trans base)
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := Base.bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := Base.bind_ok_iff.mp h
          cases h
          exact Funded.of_balance funded rfl rfl rfl
            ((read _ _ _).trans ((read _ _ _).trans base))

/-- A message whose caller holds its value never fails for a balance below an amount. -/
theorem processMessageCall_ne_insufficientBalance [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (funded : Funded message state)
    (address : Address) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.insufficientBalance address)) := by
  intro h
  rw [processMessageCall_unfold] at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
      exact prepareFirstFrame_ne_state (fun _ h => by cases h) read hprep
    · cases h
  · rw [hprep] at h
    dsimp only at h
    have ready := funded_prepareFirstFrame funded hprep
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processCreateMessage_ne_insufficientBalance ready address h
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processMessage_ne_insufficientBalance ready address h
      · cases h

/-- A run of a transaction never fails for a short balance.

Its sender holds its fee and its value. -/
private theorem runTransaction_ne_insufficientBalance [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {included : Included} {tx : Transaction}
    (funds : tx.gas.toNat * effectiveGasPrice (baseFeeOf env) tx +
      calculateTotalBlobGas tx * blobGasPriceOf env + tx.value.toNat ≤
        ((TransactionState.ofBlock block).getAccount included.sender).balance.toNat)
    (address : Address) :
    runTransaction Meter env block included tx ≠
      .error (.state (.insufficientBalance address)) := by
  intro h
  rw [runTransaction_unfold] at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · obtain ⟨e, -, he⟩ := Base.mapError_eq_error h
      cases he
  -- The sender holds the fee, and after it the value.
  obtain ⟨bought, hBought, kept⟩ := buyGas_ok funds
  rw [hBought] at h
  dsimp only [Except.mapError, bind, Except.bind] at h
  rcases Base.bind_eq_error h with h | ⟨message, hmsg, h⟩
  · unfold transactionMessage at h
    split at h
    · dsimp only at h
      generalize hx : Except.mapError EvmError.state _ = x at h
      cases x with
      | error e' =>
        cases h
        obtain ⟨e'', he'', hee⟩ := Base.mapError_eq_error hx
        cases hee
        exact getCode_ne_insufficientBalance _ _ _ he''
      | ok _ => cases h
    · cases h
  have key : message.caller = included.sender ∧ message.value = tx.value ∧
      message.shouldTransferValue = true := by
    unfold transactionMessage at hmsg
    split at hmsg
    · obtain ⟨_, -, rfl⟩ := Base.map_ok_iff.mp hmsg
      exact ⟨rfl, rfl, rfl⟩
    · cases hmsg
      exact ⟨rfl, rfl, rfl⟩
  have funded : Funded { message with reservoir := (allocateGas fork tx
      included.intrinsicGas).reservoir } bought := fun _ => by
    show message.value ≤ (bought.getAccount message.caller).balance
    rw [key.1, key.2.1, BitVec.le_def]
    omega
  rcases Base.bind_eq_error h with h | ⟨output, -, h⟩
  -- The authorizations keep every balance, so the first message is funded.
  --
  -- No funded message fails for a balance below an amount.
  · exact processMessageCall_ne_insufficientBalance funded address h
  -- The settlement only credits.
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    obtain ⟨_, he⟩ := error_settleGas he
    cases he
  -- The deletions never check a balance.
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    exact deleteAccounts_ne_error _ _ _ he
  · cases h

end

/-- A transaction never fails with the state error for a balance below an amount.

It passed its checks on the block state it runs on. -/
theorem processTransaction_ne_insufficientBalance {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {chainId : UInt64} {used : BlockGas} {tx : Transaction}
    {included : Included}
    (checked : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (address : Address) :
    processTransaction env block included tx ≠ .error (.state (.insufficientBalance address)) := by
  -- The checks ask the sender to hold its most costly fee and its value.
  have funds := checkInclusion_no_overdraw checked
  obtain ⟨-, -, -, hBlob, -, -, -, hPrice, -⟩ := checkInclusion_ok checked
  -- The fee it pays is at most that: the price per gas and per blob gas are at most their maxima.
  rw [hPrice, hBlob] at funds
  rw [processTransaction_unfold]
  split
  · nofun
  split
  · exact runTransaction_ne_insufficientBalance funds address
  · exact runTransaction_ne_insufficientBalance funds address

end EthLib.Execution.Transactions

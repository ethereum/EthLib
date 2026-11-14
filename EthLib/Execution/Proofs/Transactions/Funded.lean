module

public import EthLib.Execution.Proofs.Evm.Call.Funded
public import EthLib.Execution.Proofs.Transactions.Process
import EthLib.Execution.Proofs.Transactions.Inclusion

/-!
# Proofs: a transaction that may enter its block never fails for a balance below an amount

A transaction takes its fee from the sender, then moves its value to the target.

The checks of the transaction ask the sender to hold its most costly fee and its value.

The fee it pays is at most that: the price per gas and per blob gas are at most their maxima.

So the sender holds the fee, and after it the value.

The authorizations keep every balance, so the first message is funded.

No funded message fails for a balance below an amount.

The settlement only credits, and the deletions never check a balance.
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
    (address : Address) : state.getCode codeHash ≠ .error (.insufficientBalance address) := by
  intro h
  unfold State.TransactionState.getCode at h
  repeat' split at h
  all_goals try cases h
  unfold State.State.getCode at h
  repeat' split at h
  all_goals cases h

/-- A change of one account fails for a short balance only when its function does. -/
theorem modifyState_ne_insufficientBalance {state : TransactionState}
    {address other : Address} {f : State.Account → Except State.StateError State.Account}
    (hf : ∀ account, f account ≠ .error (.insufficientBalance other)) :
    state.modifyState fork address f ≠ .error (.insufficientBalance other) := fun h =>
  hf _ (State.TransactionState.modifyState_eq_error.mp h)

/-- A credit of ether never fails for a short balance. -/
private theorem creditEther_ne_insufficientBalance (state : TransactionState)
    (address : Address) (amount : Nat) (other : Address) :
    creditEther fork state address amount ≠ .error (.insufficientBalance other) := by
  unfold creditEther
  split
  · exact modifyState_ne_insufficientBalance fun _ h => by
      unfold State.Account.credit at h
      split at h <;> cases h
  · nofun

/-- The deletions at the end of a transaction never fail for a short balance. -/
private theorem deleteAccounts_ne_insufficientBalance (state : TransactionState)
    (output : CallOutput) (other : Address) :
    deleteAccounts fork state output ≠ .error (.insufficientBalance other) := by
  have fold : ∀ (l : List Address) (init : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init ≠ .error (.insufficientBalance other) := by
    intro l
    induction l with
    | nil => exact fun _ h => by cases h
    | cons address rest ih =>
      intro init h
      rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
      · split at h
        · exact modifyState_ne_insufficientBalance (fun _ h => by cases h) h
        · cases h
      · exact ih mid h
  intro h
  unfold deleteAccounts at h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at h
    exact fold _ _ h
  · cases h

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

/-- The charge of an authorization never fails for a short balance. -/
private theorem chargeAuthorization_ne_insufficientBalance [LawfulGasMeter Meter]
    {done : Delegations Meter} {authority : Address} {auth : Authorization}
    (address : Address) :
    chargeAuthorization done authority auth ≠ .error (.state (.insufficientBalance address)) := by
  intro h
  unfold chargeAuthorization at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | cases LawfulGasMeter.charge_error h
    | cases LawfulGasMeter.chargeState_error h
    | (obtain ⟨e', he', hee⟩ := Base.mapError_eq_error h
       cases hee
       exact getCode_ne_insufficientBalance _ _ _ he')

/-- One authorization never fails for a short balance. -/
private theorem applyAuthorization_ne_insufficientBalance [LawfulGasMeter Meter] {chainId : Nat}
    {done : Delegations Meter} {auth : Authorization} (address : Address)
    (read : TransactionState) :
    applyAuthorization fork chainId done auth ≠
      .error (.state (.insufficientBalance address), read) := by
  intro h
  unfold applyAuthorization at h
  dsimp only at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | (obtain ⟨e', he', hee⟩ := Base.mapError_eq_error h
       simp only [Function.comp_apply, Prod.mk.injEq, EvmError.state.injEq] at hee
       obtain ⟨rfl, -⟩ := hee
       first
         | (unfold authorityAccepts at he'
            rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
            · exact getCode_ne_insufficientBalance _ _ _ he'
            · cases he')
         | (unfold payAuthorization at he'
            split at he'
            · rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
              · exact chargeAuthorization_ne_insufficientBalance _ he'
              · cases he'
            · cases he')
         | (unfold delegate at he'
            rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
            · unfold State.TransactionState.setCode at he'
              exact modifyState_ne_insufficientBalance (fun _ h => by cases h) he'
            rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
            · exact modifyState_ne_insufficientBalance (fun _ h => by cases h) he'
            · cases he'))

/-- A list of authorizations never fails for a short balance. -/
private theorem foldlM_applyAuthorization_ne_insufficientBalance [LawfulGasMeter Meter]
    {chainId : Nat}
    (address : Address) (read : TransactionState) :
    ∀ {auths : List Authorization} {start : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start ≠
        .error (.state (.insufficientBalance address), read)
  | [], _, h => by cases h
  | _ :: _, _, h => by
    rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact applyAuthorization_ne_insufficientBalance address read h
    · exact foldlM_applyAuthorization_ne_insufficientBalance address read h

/-- The first frame of a message never fails for a short balance. -/
private theorem prepareFirstFrame_ne_insufficientBalance [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (address : Address)
    (read : TransactionState) :
    prepareFirstFrame (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.insufficientBalance address), read) := by
  intro h
  unfold prepareFirstFrame at h
  split at h <;> dsimp only at h <;>
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | (cases h; done)
    | exact foldlM_applyAuthorization_ne_insufficientBalance address read h
    | (obtain ⟨e', he', hee⟩ := Base.mapError_eq_error h
       simp only [Prod.mk.injEq, EvmError.state.injEq] at hee
       obtain ⟨rfl, -⟩ := hee
       first
         | cases LawfulGasMeter.charge_error he'
         | cases LawfulGasMeter.chargeState_error he'
         | exact getCode_ne_insufficientBalance _ _ _ he')

/-- A message whose caller holds its value never fails for a balance below an amount. -/
theorem processMessageCall_ne_insufficientBalance [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (funded : Funded message state)
    (address : Address) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.insufficientBalance address)) := by
  intro h
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
      exact prepareFirstFrame_ne_insufficientBalance address read hprep
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
  unfold runTransaction at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · obtain ⟨e, -, he⟩ := Base.mapError_eq_error h
      cases he
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
  · exact processMessageCall_ne_insufficientBalance funded address h
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    unfold settleGas at he
    rw [paidBaseFee_empty] at he
    rcases Base.bind_eq_error he with he | ⟨mid, -, he⟩
    · exact creditEther_ne_insufficientBalance _ _ _ _ he
    rcases Base.bind_eq_error he with he | ⟨paid, -, he⟩
    · unfold payBeneficiary at he
      split at he
      · cases he
      · exact creditEther_ne_insufficientBalance _ _ _ _ he
    · cases he
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    exact deleteAccounts_ne_insufficientBalance _ _ _ he
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
  have funds := checkInclusion_no_overdraw checked
  obtain ⟨-, -, -, hBlob, -, -, -, hPrice, -⟩ := checkInclusion_ok checked
  rw [hPrice, hBlob] at funds
  unfold processTransaction
  split
  · nofun
  split
  · exact runTransaction_ne_insufficientBalance funds address
  · exact runTransaction_ne_insufficientBalance funds address

end EthLib.Execution.Transactions

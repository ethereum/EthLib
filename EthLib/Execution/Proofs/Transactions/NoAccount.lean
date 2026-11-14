module

public import EthLib.Execution.Proofs.Evm.Call.NoAccount
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: no transaction writes storage at an address with no account

The first message of a call runs the code of its target, or of the delegate of its target.

When that code is not empty, the target holds code: its own, or a delegation indicator.

So the target is settled.

A creation needs nothing: its new address gets an account when the creation starts.

So the first message never fails for a write of storage at an address with no account.

The purchase of gas, the authorizations, the settlement and the deletions write no storage.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork Hash32)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

section

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A read of code never fails for no account. -/
theorem getCode_ne_noAccount (state : TransactionState) (codeHash : Hash32)
    (address : Address) : state.getCode codeHash ≠ .error (.noAccount address) := by
  intro h
  unfold State.TransactionState.getCode at h
  repeat' split at h
  all_goals try cases h
  unfold State.State.getCode at h
  repeat' split at h
  all_goals cases h

/-- A change of one account fails for no account only when the update it applies does. -/
theorem modifyState_ne_noAccount {state : TransactionState}
    {address other : Address} {f : State.Account → Except State.StateError State.Account}
    (hf : ∀ account, f account ≠ .error (.noAccount other)) :
    state.modifyState fork address f ≠ .error (.noAccount other) := fun h =>
  hf _ (State.TransactionState.modifyState_eq_error.mp h)

/-- A credit of ether never fails for no account. -/
private theorem creditEther_ne_noAccount (state : TransactionState)
    (address : Address) (amount : Nat) (other : Address) :
    creditEther fork state address amount ≠ .error (.noAccount other) := by
  unfold creditEther
  split
  · exact modifyState_ne_noAccount fun _ h => by
      unfold State.Account.credit at h
      split at h <;> cases h
  · nofun

/-- The deletions at the end of a transaction never fail for no account. -/
private theorem deleteAccounts_ne_noAccount (state : TransactionState)
    (output : CallOutput) (other : Address) :
    deleteAccounts fork state output ≠ .error (.noAccount other) := by
  have fold : ∀ (l : List Address) (init : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init ≠ .error (.noAccount other) := by
    intro l
    induction l with
    | nil => exact fun _ h => by cases h
    | cons address rest ih =>
      intro init h
      rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
      · split at h
        · exact modifyState_ne_noAccount (fun _ h => by cases h) h
        · cases h
      · exact ih mid h
  intro h
  unfold deleteAccounts at h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at h
    exact fold _ _ h
  · cases h

/-- The purchase of gas never fails for no account. -/
private theorem buyGas_ne_noAccount (env : BlockEnvironment fork) (state : TransactionState)
    (sender : Address) (tx : Transaction) (other : Address) :
    buyGas env state sender tx ≠ .error (.noAccount other) := by
  intro h
  unfold buyGas at h
  rw [paidBaseFee_empty] at h
  obtain ⟨mid, hmid⟩ := State.TransactionState.incrementNonce_isOk fork state sender
  simp only [hmid, bind, Except.bind] at h
  refine modifyState_ne_noAccount (fun _ h => ?_) h
  split at h <;> cases h

/-- The settlement of gas never fails for no account. -/
private theorem settleGas_ne_noAccount (env : BlockEnvironment fork) (state : TransactionState)
    (sender : Address) (tx : Transaction) (gasLeft refund : Nat) (other : Address) :
    settleGas env state sender tx gasLeft refund ≠ .error (.noAccount other) := by
  intro he
  unfold settleGas at he
  rw [paidBaseFee_empty] at he
  rcases Base.bind_eq_error he with he | ⟨mid, -, he⟩
  · exact creditEther_ne_noAccount _ _ _ _ he
  rcases Base.bind_eq_error he with he | ⟨paid, -, he⟩
  · unfold payBeneficiary at he
    split at he
    · cases he
    · exact creditEther_ne_noAccount _ _ _ _ he
  · cases he

/-- The charge of an authorization never fails for no account. -/
private theorem chargeAuthorization_ne_noAccount [LawfulGasMeter Meter]
    {done : Delegations Meter} {authority : Address} {auth : Authorization}
    (address : Address) :
    chargeAuthorization done authority auth ≠ .error (.state (.noAccount address)) := by
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
       exact getCode_ne_noAccount _ _ _ he')

/-- One authorization never fails for no account. -/
private theorem applyAuthorization_ne_noAccount [LawfulGasMeter Meter] {chainId : Nat}
    {done : Delegations Meter} {auth : Authorization} (address : Address)
    (read : TransactionState) :
    applyAuthorization fork chainId done auth ≠
      .error (.state (.noAccount address), read) := by
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
            · exact getCode_ne_noAccount _ _ _ he'
            · cases he')
         | (unfold payAuthorization at he'
            split at he'
            · rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
              · exact chargeAuthorization_ne_noAccount _ he'
              · cases he'
            · cases he')
         | (unfold delegate at he'
            rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
            · unfold State.TransactionState.setCode at he'
              exact modifyState_ne_noAccount (fun _ h => by cases h) he'
            rcases Base.bind_eq_error he' with he' | ⟨_, -, he'⟩
            · exact modifyState_ne_noAccount (fun _ h => by cases h) he'
            · cases he'))

/-- A list of authorizations never fails for no account. -/
private theorem foldlM_applyAuthorization_ne_noAccount [LawfulGasMeter Meter]
    {chainId : Nat} (address : Address) (read : TransactionState) :
    ∀ {auths : List Authorization} {start : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start ≠
        .error (.state (.noAccount address), read)
  | [], _, h => by cases h
  | _ :: _, _, h => by
    rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
    · exact applyAuthorization_ne_noAccount address read h
    · exact foldlM_applyAuthorization_ne_noAccount address read h

/-- The first frame of a message never fails for no account. -/
private theorem prepareFirstFrame_ne_noAccount [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (address : Address)
    (read : TransactionState) :
    prepareFirstFrame (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.noAccount address), read) := by
  intro h
  unfold prepareFirstFrame at h
  split at h <;> dsimp only at h <;>
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | (cases h; done)
    | exact foldlM_applyAuthorization_ne_noAccount address read h
    | (obtain ⟨e', he', hee⟩ := Base.mapError_eq_error h
       simp only [Prod.mk.injEq, EvmError.state.injEq] at hee
       obtain ⟨rfl, -⟩ := hee
       first
         | cases LawfulGasMeter.charge_error he'
         | cases LawfulGasMeter.chargeState_error he'
         | exact getCode_ne_noAccount _ _ _ he')

/-- Code that is not empty is read at a hash other than that of empty code. -/
private theorem codeHash_ne_of_getCode {state : TransactionState} {codeHash : Hash32}
    {code : ByteArray} (h : state.getCode codeHash = .ok code) (size : code.size ≠ 0) :
    codeHash ≠ State.EMPTY_CODE_HASH := by
  rintro rfl
  unfold State.TransactionState.getCode at h
  simp only [↓reduceIte, Except.ok.injEq] at h
  subst h
  exact size rfl

/-- A delegation indicator is not empty. -/
private theorem size_ne_zero_of_delegatedAddress {code : ByteArray} {delegate : Address}
    (h : delegatedAddress code = some delegate) : code.size ≠ 0 := by
  unfold delegatedAddress at h
  split at h
  · rename_i hv
    simp only [isValidDelegation, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [hv.1, DELEGATION_SIZE]
    omega
  · cases h

/-- A call that runs at the address it calls starts any code at a settled address. -/
private theorem hosts_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (target : message.target = some message.currentTarget)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    Hosts fork first.message first.state := by
  unfold prepareFirstFrame at h
  split at h
  · rename_i hnone
    rw [hnone] at target
    cases target
  rename_i to hto
  rw [hto, Option.some.injEq] at target
  subst target
  dsimp only at h
  obtain ⟨done, -, h⟩ := Base.bind_ok_iff.mp h
  generalize (if message.value ≠ 0 then done.state.recordAccountRead message.currentTarget
    else done.state) = read0 at h
  split at h <;>
  · obtain ⟨m, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨code, hcode, h⟩ := Base.bind_ok_iff.mp h
    have hcode := Base.mapError_ok_iff.mp hcode
    generalize hd : (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
    rcases delegate with _ | delegate
    · cases h
      exact fun size => settled_of_getAccount (.inr (codeHash_ne_of_getCode hcode size))
    · have size : code.size ≠ 0 := by
        split at hd
        · exact size_ne_zero_of_delegatedAddress hd
        · cases hd
      dsimp only at h
      split at h <;>
      · obtain ⟨m', -, h⟩ := Base.bind_ok_iff.mp h
        obtain ⟨code', -, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact fun _ => settled_of_getAccount (.inr (codeHash_ne_of_getCode hcode size))

/-- A message that runs at the address it calls never fails for a storage write with no account.

Nor does a creation. -/
theorem processMessageCall_ne_noAccount [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    (target : ∀ to, message.target = some to → to = message.currentTarget)
    (address : Address) :
    processMessageCall (Meter := Meter) chainId message state substate auths paid ≠
      .error (.state (.noAccount address)) := by
  intro h
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
      exact prepareFirstFrame_ne_noAccount address read hprep
    · cases h
  · rw [hprep] at h
    dsimp only at h
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processCreateMessage_ne_noAccount address h
      · cases h
    · rename_i to hto
      rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · rw [target to hto] at hto
        exact processMessage_ne_noAccount (hosts_prepareFirstFrame hto hprep) address h
      · cases h

/-- A run of a transaction never fails for a write of storage with no account. -/
private theorem runTransaction_ne_noAccount [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {included : Included} {tx : Transaction}
    (address : Address) :
    runTransaction Meter env block included tx ≠ .error (.state (.noAccount address)) := by
  intro h
  unfold runTransaction at h
  rcases Base.bind_eq_error h with h | ⟨target, htarget, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · obtain ⟨e, -, he⟩ := Base.mapError_eq_error h
      cases he
  rcases Base.bind_eq_error h with h | ⟨bought, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    exact buyGas_ne_noAccount _ _ _ _ _ he
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
        exact getCode_ne_noAccount _ _ _ he''
      | ok _ => cases h
    · cases h
  have own : ∀ to, message.target = some to → to = message.currentTarget := by
    intro to hto
    unfold transactionMessage at hmsg
    unfold messageTarget at htarget
    split at hmsg
    · rename_i to' hto'
      rw [hto'] at htarget
      cases htarget
      obtain ⟨_, -, rfl⟩ := Base.map_ok_iff.mp hmsg
      simp only [hto', Option.some.injEq] at hto
      exact hto.symm
    · rename_i hnone
      cases hmsg
      simp [hnone] at hto
  rcases Base.bind_eq_error h with h | ⟨output, -, h⟩
  · exact processMessageCall_ne_noAccount (message := { message with
      reservoir := (allocateGas fork tx included.intrinsicGas).reservoir }) own address h
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    exact settleGas_ne_noAccount _ _ _ _ _ _ _ he
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · obtain ⟨e, he, hee⟩ := Base.mapError_eq_error h
    cases hee
    exact deleteAccounts_ne_noAccount _ _ _ he
  · cases h

end

/-- No transaction fails with the state error for a write of storage with no account. -/
theorem processTransaction_ne_noAccount {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} (address : Address) :
    processTransaction env block included tx ≠ .error (.state (.noAccount address)) := by
  unfold processTransaction
  split
  · nofun
  split
  · exact runTransaction_ne_noAccount address
  · exact runTransaction_ne_noAccount address

end EthLib.Execution.Transactions

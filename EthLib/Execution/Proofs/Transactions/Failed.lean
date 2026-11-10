module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: what a transaction whose message fails leaves

When the message of a transaction fails, every write of the message is undone.

The transaction still leaves the writes that come before and after its message.

The first theorems say only where those writes land.

The later ones say their values.

- The sender buys the gas: its nonce grows by one and it pays the fee.
- The fee is the gas limit times the price, plus the blob fee.
- From Pectra, each accepted authorization, taken alone, sets the code and nonce of its authority.
- The sender gets back the price of the gas it did not use.
- The beneficiary gets the priority fee of the gas that the transaction used.
- From Spurious Dragon, an empty beneficiary paid a fee of 0 is deleted.

The values read a missing account as empty, so they do not say which of these accounts exist.

A halt before the first frame undoes the authorizations, as [EIP-8037][e8037] asks.

A frame that fails keeps each accepted authorization, as [EIP-7702][e7702] asks.

So the state after the transaction reads as the state before it at every other address.

That holds for the account, every word of storage and every word of transient storage.

It holds up to Glamsterdam, whether the message fails in its first frame or before it starts.

From Hegotá a transaction is not yet specified, so none runs.

[e7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[e8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-halts-and-reverts
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm

variable {fork : Fork} {tx : Transaction}

open State.TransactionState (SameOutside)

/-! ## The authorizations -/

section Meter

variable {Meter : Type} [GasMeter Meter]

/-- Applying an authorization changes only the authority that its signature names, if any. -/
theorem sameOutside_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    SameOutside (recoverAuthority auth).toList done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, hrecover, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact SameOutside.refl _ _
  · exact (State.TransactionState.sameOutside_recordAccountRead _ _).mono (by simp)
  · rw [hrecover]
    obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    exact (State.TransactionState.sameOutside_recordAccountRead _ _).trans
      (sameOutside_delegate hdelegate).1

/-- Authorizations that succeed change only the authorities that their signatures name. -/
theorem sameOutside_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      SameOutside (auths.filterMap recoverAuthority) start.state done.state
  | [], _, _, h => by
    cases h
    exact SameOutside.refl _ _
  | auth :: rest, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    refine ((sameOutside_applyAuthorization hnext).trans
      (sameOutside_foldlM_applyAuthorization h)).mono ?_
    cases hrecover : recoverAuthority auth <;> simp [hrecover]

/-! ## The frame -/

/-- A creation that ends with an error reads as the state it is sent from, at every address.

That holds for the account, every word of storage and every word of transient storage.

It holds at every fork, whatever the init code. -/
theorem processCreateMessage_sameOutside_of_error [LawfulGasMeter Meter]
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended)
    (herr : ended.val.error.isSome = true) :
    SameOutside [] state ended.val.state := by
  rw [processCreateMessage] at h
  obtain ⟨prepared, hp, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
  have hparent : evm.state.parent = state.parent :=
    (parent_processMessage hrun).trans (parent_prepareCreation hp)
  dsimp only at h
  split at h
  · cases h
  rename_i after hdeposit
  cases h
  simp only at herr ⊢
  unfold depositCode at hdeposit
  dsimp only at hdeposit
  have restored := State.TransactionState.sameOutside_restoreTxState hparent
  split at hdeposit
  · cases hdeposit
    exact restored
  rename_i hok
  split at hdeposit
  · cases hdeposit
    exact restored
  split at hdeposit
  · cases hdeposit
    exact restored
  split at hdeposit
  · cases hdeposit
    split
    · exact restored
    · rename_i hfork
      simp only [hfork, ↓reduceIte] at herr
      exact absurd herr hok
  split at hdeposit
  · cases hdeposit
    exact restored
  obtain ⟨_, -, hdeposit⟩ := bind_ok_iff.mp hdeposit
  cases hdeposit
  exact absurd herr hok

/-- The first frame of a transaction reads as the state before it, but at the authorities.

The authorities are the addresses that the signatures of the authorizations name. -/
theorem prepareFirstFrame_sameOutside {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    SameOutside (auths.filterMap recoverAuthority) state first.state := by
  unfold prepareFirstFrame at h
  split at h
  · have read : SameOutside (auths.filterMap recoverAuthority) state
        (state.recordAccountRead message.currentTarget) :=
      (State.TransactionState.sameOutside_recordAccountRead _ _).mono (List.nil_subset _)
    dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target _
    have read : ∀ {s : State.TransactionState} (address : Address),
        SameOutside (auths.filterMap recoverAuthority) state s →
        SameOutside (auths.filterMap recoverAuthority) state (s.recordAccountRead address) :=
      fun address hs =>
        (hs.trans (State.TransactionState.sameOutside_recordAccountRead _ address)).mono
          (by simp)
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have hauth : SameOutside (auths.filterMap recoverAuthority) state done.state :=
      sameOutside_foldlM_applyAuthorization hdone
    -- After the authorizations, the first frame only records reads.
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : SameOutside (auths.filterMap recoverAuthority) state read0 := by
      subst hread
      split
      · exact read _ hauth
      · exact hauth
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact read _ base
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact read _ (read _ base)

/-- The state after a message that fails reads as the state before it, but at the authorities.

It also leaves no account to delete and no touched account. -/
theorem processMessageCall_of_error [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) (failed : output.error.isSome) :
    output.accountsToDelete = ∅ ∧ output.touchedAccounts = ∅ ∧
      SameOutside (auths.filterMap recoverAuthority) state output.state := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl, (State.TransactionState.sameOutside_withReadsOf _ _).mono (by simp)⟩
  rename_i first hfirst
  have hstart := prepareFirstFrame_sameOutside hfirst
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    unfold CallOutput.ofFrame at failed ⊢
    split
    · rename_i herr
      exact ⟨rfl, rfl, (hstart.trans (processCreateMessage_sameOutside_of_error hrun herr)).mono
        (by simp)⟩
    · rename_i herr
      simp [herr] at failed
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    unfold CallOutput.ofFrame at failed ⊢
    split
    · rename_i herr
      exact ⟨rfl, rfl, (hstart.trans (processMessage_sameOutside_of_error hrun herr)).mono
        (by simp)⟩
    · rename_i herr
      simp [herr] at failed

end Meter

/-! ## The transaction -/

/-- The purchase of gas changes only the sender. -/
theorem sameOutside_buyGas {env : BlockEnvironment fork} {state state' : State.TransactionState}
    {sender : Address} (h : buyGas env state sender tx = .ok state') :
    SameOutside [sender] state state' := by
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  exact ((State.TransactionState.sameOutside_incrementNonce hnonce).trans
    (State.TransactionState.sameOutside_modifyState h)).mono (by simp)

/-- The settlement of gas changes only the sender and the beneficiary. -/
theorem sameOutside_settleGas {env : BlockEnvironment fork}
    {state state' : State.TransactionState} {sender : Address} {gasLeft refund used : Nat}
    (h : settleGas env state sender tx gasLeft refund = .ok (state', used)) :
    SameOutside [sender, env.coinbase] state state' := by
  have credit : ∀ {state state' : State.TransactionState} {address : Address} {amount : Nat},
      creditEther fork state address amount = .ok state' → SameOutside [address] state state' := by
    intro state state' address amount h
    unfold creditEther at h
    split at h
    · exact State.TransactionState.sameOutside_createEther h
    · cases h
  obtain ⟨refunded, hrefund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, hpay, h⟩ := bind_ok_iff.mp h
  cases h
  refine ((credit hrefund).trans (?_ : SameOutside [env.coinbase] refunded state')).mono
    (by simp)
  unfold payBeneficiary at hpay
  split at hpay
  · cases hpay
    split
    · exact State.TransactionState.sameOutside_destroyAccount _ _
    · exact SameOutside.refl _ _
  · exact credit hpay

/-- A run whose message fails changes only the sender, the beneficiary and the authorities. -/
theorem runTransaction_sameOutside_of_error {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) (failed : out.error.isSome) :
    SameOutside (included.sender :: env.coinbase :: tx.authorizations.filterMap recoverAuthority)
      (State.TransactionState.ofBlock block) out.state := by
  unfold runTransaction at h
  obtain ⟨target, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  obtain ⟨message, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hsettle, h⟩ := bind_ok_iff.mp h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨hdelete, htouched, hmessage⟩ := processMessageCall_of_error houtput failed
  have hdeleted : deleted = settled.destroyTouchedEmptyAccounts fork [] := by
    have hnil : (∅ : Std.ExtTreeSet Address).toList = [] :=
      Std.ExtTreeSet.toList_eq_nil_iff.mpr rfl
    rw [mapError_ok_iff] at hdeleted
    simpa [deleteAccounts, hdelete, htouched, Std.ExtTreeSet.foldlM_eq_foldlM_toList, hnil,
      eq_comm, pure, Except.pure, bind, Except.bind] using hdeleted
  subst hdeleted
  exact ((((sameOutside_buyGas (mapError_ok_iff.mp hbought)).trans hmessage).trans
    (sameOutside_settleGas (mapError_ok_iff.mp hsettle))).trans
    (State.TransactionState.sameOutside_destroyTouchedEmptyAccounts fork settled [])).mono
    (by simp)

/-- A transaction whose message fails changes only its sender, its beneficiary and its authorities.

The authorities are the addresses that the signatures of its authorizations name.

The state after it reads as the state before it at every other address. -/
theorem processTransaction_sameOutside_of_error {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out) (failed : out.error.isSome) :
    State.TransactionState.SameOutside
      (included.sender :: env.coinbase :: tx.authorizations.filterMap recoverAuthority)
      (State.TransactionState.ofBlock block) out.state := by
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · exact runTransaction_sameOutside_of_error h failed
  · exact runTransaction_sameOutside_of_error h failed

/-! ## The values -/

open State.TransactionState

/-- The purchase of gas keeps the code hash of the sender.

Every word of storage stays, because the higher nonce keeps the account.

No code changes. -/
theorem buyGas_keeps {env : BlockEnvironment fork} {state state' : State.TransactionState}
    {sender : Address} (h : buyGas env state sender tx = .ok state') :
    (state'.getAccount sender).codeHash = (state.getAccount sender).codeHash ∧
      (∀ address key, state'.getStorage address key = state.getStorage address key) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) := by
  have hnonce' := (buyGas_sender rfl h).2.2
  obtain ⟨bumped, hnonce, hfee⟩ := bind_ok_iff.mp h
  obtain ⟨hself, -⟩ := getAccount_incrementNonce hnonce
  have hlive : state'.getAccountOptional sender ≠ none := by
    intro hnone
    simp [getAccount, hnone, State.EMPTY_ACCOUNT] at hnonce'
  have hbumped : bumped.getAccountOptional sender ≠ none := by
    intro hnone
    have := congrArg State.Account.nonce hself
    simp [getAccount, hnone, State.EMPTY_ACCOUNT] at this
  refine ⟨?_, fun address key => ?_, fun codeHash => ?_⟩
  · obtain ⟨account, hf, hread, -⟩ := modifyState_eq_ok hfee
    rw [hself] at hf
    dsimp only at hf
    split at hf
    · cases hf
      rw [hread]
    · cases hf
  · rw [getStorage_modifyState hfee, ite_eq_right_iff.mpr (fun h => absurd h.2 hlive),
      getStorage_modifyState hnonce, ite_eq_right_iff.mpr (fun h => absurd h.2 hbumped)]
  · rw [getCode_modifyState hfee, getCode_modifyState hnonce]

/-- A credit adds the amount to one balance.

It changes no nonce, no code hash and no code.

From Paris, a credit of 0 to an empty account deletes it, and with it its storage.

Every other word of storage stays. -/
private theorem creditEther_values {state state' : State.TransactionState} {target : Address}
    {amount : Nat} (h : creditEther fork state target amount = .ok state') (address : Address) :
    (state'.getAccount address).nonce = (state.getAccount address).nonce ∧
      (state'.getAccount address).codeHash = (state.getAccount address).codeHash ∧
      (state'.getAccount address).balance.toNat =
        (state.getAccount address).balance.toNat + (if target = address then amount else 0) ∧
      (∀ key, address ≠ target ∨ state'.getAccountOptional target ≠ none →
        state'.getStorage address key = state.getStorage address key) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) := by
  obtain ⟨hlt, hbal⟩ := creditEther_balance h address
  rw [creditEther_of_lt hlt] at h
  obtain ⟨-, hnonce, hcode⟩ := getAccount_createEther h address
  refine ⟨hnonce, hcode, hbal, ?_, fun codeHash => by rw [getCode_modifyState h]⟩
  · intro key hkeep
    rw [getStorage_modifyState h]
    refine ite_eq_right_iff.mpr ?_
    rintro ⟨rfl, hnone⟩
    rcases hkeep with hne | hlive
    · exact absurd rfl hne
    · exact absurd hnone hlive

/-- Paying the beneficiary adds the priority fee to its balance.

From Spurious Dragon, a fee of 0 paid to an empty beneficiary deletes it.

Its balance then stays 0.

No other balance, nonce or code hash changes.

No code changes, and storage changes only at a deleted beneficiary. -/
private theorem payBeneficiary_values {state state' : State.TransactionState}
    {coinbase : Address} {fee : Nat} (h : payBeneficiary fork state coinbase fee = .ok state')
    (address : Address) :
    (state'.getAccount address).nonce = (state.getAccount address).nonce ∧
      (state'.getAccount address).codeHash = (state.getAccount address).codeHash ∧
      (state'.getAccount address).balance.toNat =
        (state.getAccount address).balance.toNat + (if coinbase = address then fee else 0) ∧
      (∀ key, address ≠ coinbase ∨ state'.getAccountOptional coinbase ≠ none →
        state'.getStorage address key = state.getStorage address key) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) := by
  unfold payBeneficiary at h
  split at h
  · cases h
    rename_i hcond
    have hzero : (state.getAccount coinbase).balance.toNat = 0 ∧ fee = 0 := by omega
    split
    · rename_i hempty
      have hempty' := eq_empty_of_accountExistsAndIsEmpty hempty
      refine ⟨?_, ?_, ?_, ?_, fun _ => rfl⟩
      · by_cases hsame : address = coinbase
        · subst hsame
          rw [getAccount_destroyAccount, ite_eq_left_iff.mpr fun h => absurd rfl h, hempty']
        · rw [getAccount_destroyAccount, ite_eq_right_iff.mpr fun h => absurd h hsame]
      · by_cases hsame : address = coinbase
        · subst hsame
          rw [getAccount_destroyAccount, ite_eq_left_iff.mpr fun h => absurd rfl h, hempty']
        · rw [getAccount_destroyAccount, ite_eq_right_iff.mpr fun h => absurd h hsame]
      · by_cases hsame : address = coinbase
        · subst hsame
          rw [getAccount_destroyAccount, ite_eq_left_iff.mpr fun h => absurd rfl h, hzero.1,
            hzero.2]
          simp [State.EMPTY_ACCOUNT]
        · rw [getAccount_destroyAccount, ite_eq_right_iff.mpr fun h => absurd h hsame]
          simp [Ne.symm hsame]
      · intro key hkeep
        rcases hkeep with hne | hlive
        · rw [getStorage_destroyAccount, ite_eq_right_iff.mpr fun h => absurd h hne]
        · exact absurd (by simp [destroyAccount, getAccountOptional_setAccount_self]) hlive
    · exact ⟨rfl, rfl, by simp [hzero.2], fun _ _ => rfl, fun _ => rfl⟩
  · obtain ⟨hnonce, hcode, hbal, hstorage, hget⟩ := creditEther_values h address
    exact ⟨hnonce, hcode, hbal, hstorage, hget⟩

/-- The settlement reports the gas used, refunds the sender and pays the beneficiary.

No nonce, no code hash and no code changes.

Storage stays at the sender when its nonce is not 0, and at the beneficiary unless it is deleted.
-/
theorem settleGas_accounts {env : BlockEnvironment fork} {state state' : State.TransactionState}
    {sender : Address} {gasLeft refund used : Nat}
    (h : settleGas env state sender tx gasLeft refund = .ok (state', used)) (address : Address) :
    let s := settlement fork (baseFeeOf env) sender tx gasLeft refund
    used = s.gasUsed ∧
      (state'.getAccount address).nonce = (state.getAccount address).nonce ∧
      (state'.getAccount address).codeHash = (state.getAccount address).codeHash ∧
      (state'.getAccount address).balance.toNat = (state.getAccount address).balance.toNat +
        (if sender = address then s.senderRefund else 0) +
        (if env.coinbase = address then s.priorityFee else 0) ∧
      (∀ key, (address ≠ sender ∨ (state.getAccount sender).nonce ≠ 0) →
        (address ≠ env.coinbase ∨ state'.getAccountOptional env.coinbase ≠ none) →
        state'.getStorage address key = state.getStorage address key) ∧
      (∀ codeHash, state'.getCode codeHash = state.getCode codeHash) := by
  unfold settleGas at h
  dsimp only at h ⊢
  obtain ⟨refunded, hrefund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, hpay, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨hnonce, hcode, hbal, hstore, hget⟩ := creditEther_values hrefund address
  obtain ⟨hnonce', hcode', hbal', hstore', hget'⟩ := payBeneficiary_values hpay address
  have hsum : (state'.getAccount address).balance.toNat = (state.getAccount address).balance.toNat +
      (if sender = address then
        (settlement fork (baseFeeOf env) sender tx gasLeft refund).senderRefund else 0) +
      (if env.coinbase = address then
        (settlement fork (baseFeeOf env) sender tx gasLeft refund).priorityFee else 0) := by
    rw [hbal', hbal]
  refine ⟨rfl, by rw [hnonce', hnonce], by rw [hcode', hcode], hsum, ?_,
    fun codeHash => by rw [hget', hget]⟩
  intro key hsender hcoinbase
  have href_keep : address ≠ sender ∨ refunded.getAccountOptional sender ≠ none := by
    rcases hsender with hne | hpos
    · exact .inl hne
    · refine .inr fun hnone => hpos ?_
      obtain ⟨hsn, -, -, -, -⟩ := creditEther_values hrefund sender
      rw [← hsn]
      simp [getAccount, hnone, State.EMPTY_ACCOUNT]
  rw [hstore' key hcoinbase, hstore key href_keep]

/-! ## The authorities -/

section Meter

variable {Meter : Type} [GasMeter Meter]

/-- An accepted authorization in scope adds one to the nonce of its authority.

It sets the code that the authorization names, and keeps the balance of the authority.

That code is the delegation indicator, or no code for the zero address.

The payment changes no account, so the authority is read as it was before the authorization. -/
theorem authority_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} {authority : Address}
    (h : applyAuthorization fork chainId done auth = .ok done')
    (hscope : authorizationInScope chainId auth = true)
    (hrecover : recoverAuthority auth = some authority)
    (haccept : authorityAccepts done.state authority auth = .ok true) :
    (done'.state.getAccount authority).nonce = (done.state.getAccount authority).nonce + 1 ∧
      (done'.state.getAccount authority).codeHash =
        Cryptography.Hash.Keccak.keccak256 (delegationCode auth) ∧
      (done'.state.getAccount authority).balance = (done.state.getAccount authority).balance := by
  cases hpay : payAuthorization fork { done with
      state := done.state.recordAccountRead authority
      accessed := done.accessed.insert authority } authority auth with
  | error e =>
    rw [applyAuthorization_of_payAuthorization_error hscope hrecover haccept hpay] at h
    cases h
  | ok paid =>
    obtain ⟨state, hdelegate⟩ := delegate_isOk (fork := fork) (authority := authority)
      (auth := auth) paid.state
    rw [applyAuthorization_of_accepts_of_pay hscope hrecover haccept hpay, hdelegate] at h
    simp only [Except.map, Except.mapError, Except.ok.injEq] at h
    subst h
    obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    obtain ⟨-, haccount, -⟩ := delegate_eq_ok hdelegate
    have hpaid : paid.state.getAccount authority = done.state.getAccount authority := by
      rw [hstate]
      rfl
    rw [hpaid] at haccount
    dsimp only
    rw [haccount]
    exact ⟨rfl, rfl, rfl⟩

/-- A failed message either halts before its first frame or rolls back to the state of that frame.

On a halt, every account, storage word, transient word and code reads as before the message.

On a failed frame, every one of them reads as at the start of the first frame. -/
theorem processMessageCall_reads_of_error [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (hout : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (herr : output.error.isSome = true) :
    output.logs = #[] ∧ output.accountsToDelete = ∅ ∧ output.touchedAccounts = ∅ ∧
      ((∃ e read, prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
          .error (e, read) ∧ output.state = state.withReadsOf read) ∨
        ∃ first, prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
          .ok first ∧ SameOutside [] first.state output.state ∧
          ∀ codeHash, output.state.getCode codeHash = first.state.getCode codeHash) := by
  have hcode_create : ∀ {m : Message fork} {s : State.TransactionState} {sub : Substate}
      {meter : Meter} {held : GasMeter.gasHeld meter ≤ m.gas} {ended},
      processCreateMessage fork m s sub meter held = .ok ended →
      ended.val.error.isSome = true →
      ∀ codeHash, ended.val.state.getCode codeHash = s.getCode codeHash := by
    intro m s sub meter held ended hrun herr' codeHash
    rw [processCreateMessage] at hrun
    obtain ⟨prepared, hp, hrun⟩ := bind_ok_iff.mp hrun
    obtain ⟨⟨evm, used⟩, hm, hrun⟩ := bind_ok_iff.mp hrun
    have hparent : evm.state.parent = s.parent :=
      (parent_processMessage hm).trans (parent_prepareCreation hp)
    dsimp only at hrun
    split at hrun
    · cases hrun
    rename_i after hdeposit
    cases hrun
    simp only at herr' ⊢
    unfold depositCode at hdeposit
    dsimp only at hdeposit
    have restored := getCode_restoreTxState hparent codeHash
    split at hdeposit
    · cases hdeposit
      exact restored
    rename_i hok
    split at hdeposit
    · cases hdeposit
      exact restored
    split at hdeposit
    · cases hdeposit
      exact restored
    split at hdeposit
    · cases hdeposit
      split
      · exact restored
      · rename_i hfork
        simp only [hfork, ↓reduceIte] at herr'
        exact absurd herr' hok
    split at hdeposit
    · cases hdeposit
      exact restored
    obtain ⟨_, -, hdeposit⟩ := bind_ok_iff.mp hdeposit
    cases hdeposit
    exact absurd herr' hok
  have hcode_call : ∀ {m : Message fork} {s : State.TransactionState} {sub : Substate}
      {meter : Meter} {held : GasMeter.gasHeld meter ≤ m.gas} {ended},
      processMessage fork m s sub meter held = .ok ended →
      ended.val.error.isSome = true →
      ∀ codeHash, ended.val.state.getCode codeHash = s.getCode codeHash := by
    intro m s sub meter held ended hrun herr' codeHash
    have hp := parent_processMessage hrun
    obtain ⟨last, hl⟩ := exists_rollbackOnError_processMessage hrun
    rw [hl] at herr' hp ⊢
    unfold rollbackOnError at herr' hp ⊢
    split at herr'
    · simp only [‹last.error.isSome = true›, ↓reduceIte] at hp ⊢
      exact getCode_restoreTxState hp codeHash
    · exact absurd herr' ‹_›
  unfold processMessageCall at hout
  split at hout
  · rename_i e read hprep
    split at hout
    · cases hout
    · cases hout
      exact ⟨rfl, rfl, rfl, .inl ⟨e, read, hprep, rfl⟩⟩
  · rename_i first hfirst
    split at hout
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp hout
      cases h
      unfold CallOutput.ofFrame at herr ⊢
      split
      · rename_i herr'
        exact ⟨rfl, rfl, rfl, .inr ⟨first, hfirst,
          processCreateMessage_sameOutside_of_error hrun herr', hcode_create hrun herr'⟩⟩
      · rename_i herr'
        simp [herr'] at herr
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp hout
      cases h
      unfold CallOutput.ofFrame at herr ⊢
      split
      · rename_i herr'
        exact ⟨rfl, rfl, rfl, .inr ⟨first, hfirst,
          processMessage_sameOutside_of_error hrun herr', hcode_call hrun herr'⟩⟩
      · rename_i herr'
        simp [herr'] at herr

/-- The first frame of a creation reads as the state before it, at every address and code hash.

The first frame of a call reads as the state that its authorizations leave. -/
theorem prepareFirstFrame_reads {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    match message.target with
    | none => SameOutside [] state first.state ∧
        ∀ codeHash, first.state.getCode codeHash = state.getCode codeHash
    | some _ => ∃ done : Delegations Meter,
        applyAuthorizations fork chainId state substate.accessedAddresses
        (GasMeter.start message.gas message.reservoir) paid auths = .ok done ∧
        first.refund = done.refund ∧ SameOutside [] done.state first.state ∧
        ∀ codeHash, first.state.getCode codeHash = done.state.getCode codeHash := by
  unfold prepareFirstFrame at h
  cases htarget : message.target with
  | none =>
    rw [htarget] at h
    dsimp only at h
    split at h
    · split at h <;>
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨sameOutside_recordAccountRead _ _, fun _ => rfl⟩
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  | some target =>
    rw [htarget] at h
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have read : ∀ {s : State.TransactionState} (address : Address),
        SameOutside [] done.state s → SameOutside [] done.state (s.recordAccountRead address) :=
      fun address hs => (hs.trans (sameOutside_recordAccountRead _ address)).mono (by simp)
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : SameOutside [] done.state read0 ∧
        ∀ codeHash, read0.getCode codeHash = done.state.getCode codeHash := by
      subst hread
      split
      · exact ⟨sameOutside_recordAccountRead _ _, fun _ => rfl⟩
      · exact ⟨SameOutside.refl _ _, fun _ => rfl⟩
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact ⟨done, hdone, rfl, read _ base.1, fun codeHash => by
          change read0.getCode codeHash = done.state.getCode codeHash
          exact base.2 codeHash⟩
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact ⟨done, hdone, rfl, read _ (read _ base.1), fun codeHash => by
            change read0.getCode codeHash = done.state.getCode codeHash
            exact base.2 codeHash⟩

end Meter

section Values

variable {env : BlockEnvironment fork} {included : Included} {out : TransactionOutput}

/-- The nonce, code hash, balance and storage that settlement leaves, against the message state. -/
abbrev SettledAccounts (tx : Transaction) (env : BlockEnvironment fork)
    (included : Included) (out : TransactionOutput) (base : State.TransactionState)
    (gasLeft refund : Nat) : Prop :=
  ∀ address,
    (out.state.getAccount address).nonce = (base.getAccount address).nonce ∧
    (out.state.getAccount address).codeHash = (base.getAccount address).codeHash ∧
    (out.state.getAccount address).balance.toNat = (base.getAccount address).balance.toNat +
      (if included.sender = address then
        (settlement fork (baseFeeOf env) included.sender tx gasLeft refund).senderRefund
      else 0) +
      (if env.coinbase = address then
        (settlement fork (baseFeeOf env) included.sender tx gasLeft refund).priorityFee
      else 0) ∧
    (∀ key, (address ≠ included.sender ∨ (base.getAccount included.sender).nonce ≠ 0) →
      (address ≠ env.coinbase ∨ out.state.getAccountOptional env.coinbase ≠ none) →
      out.state.getStorage address key = base.getStorage address key)

/-- The authorizations of a call that fails, read as the state before settlement. -/
abbrev KeptAuthorizations {Meter : Type} [GasMeter Meter] (tx : Transaction)
    (env : BlockEnvironment fork) (included : Included) (bought base : State.TransactionState)
    (target : Address) (done : Delegations Meter) (refund : Nat) : Prop :=
  applyAuthorizations fork env.chainId.toNat bought
      (startAccessedAddresses fork env.coinbase included.sender target tx)
      (GasMeter.start (allocateGas fork tx included.intrinsicGas).execution
        (allocateGas fork tx included.intrinsicGas).reservoir)
      (paidWrites included.sender target tx) tx.authorizations = .ok done ∧
    SameOutside [] done.state base ∧
    (∀ codeHash, base.getCode codeHash = done.state.getCode codeHash) ∧
    refund = done.refund

/-- The preparation of the first frame of the message of a transaction, after the gas purchase. -/
abbrev transactionFirstFrame (Meter : Type) [GasMeter Meter] (tx : Transaction)
    (env : BlockEnvironment fork) (included : Included) (bought : State.TransactionState)
    (target : Address) (message : Message fork) :
    Except (EvmError × State.TransactionState) (FirstFrame fork Meter) :=
  prepareFirstFrame (Meter := Meter) env.chainId.toNat
    { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
    (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
    (paidWrites included.sender target tx)

/-- What a failed run leaves: it buys the gas, then settles it against the state of the message.

When the transaction creates a contract, or its first frame never starts, no authorization stays.

The state before settlement then reads as the state after the gas purchase.

When the first frame of a call starts and fails, that state reads as the authorizations left it.

No log is kept. -/
abbrev FailedRun (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter] (tx : Transaction)
    (env : BlockEnvironment fork) (block : State.BlockState) (included : Included)
    (out : TransactionOutput) : Prop :=
  let pre := State.TransactionState.ofBlock block
  ∃ target bought message output base gasLeft refund,
    messageTarget included.sender (pre.getAccount included.sender).nonce tx = .ok target ∧
    buyGas env pre included.sender tx = .ok bought ∧
    transactionMessage env
      { origin := included.sender, gasPrice := included.gasPrice,
        blobVersionedHashes := fun _ => tx.blobHashes } bought included.sender target
      (allocateGas fork tx included.intrinsicGas).execution tx = .ok message ∧
    processMessageCall (Meter := Meter) env.chainId.toNat
      { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
      (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
      (paidWrites included.sender target tx) = .ok output ∧
    base = output.state ∧ gasLeft = output.gasLeft + output.reservoir ∧ refund = output.refund ∧
    out.logs = #[] ∧
    out.gasUsed = (settlement fork (baseFeeOf env) included.sender tx gasLeft refund).gasUsed ∧
    SettledAccounts tx env included out base gasLeft refund ∧
    (∀ codeHash, out.state.getCode codeHash = base.getCode codeHash) ∧
    (((tx.to = none ∨ ∃ e read,
          transactionFirstFrame Meter tx env included bought target message = .error (e, read)) ∧
        SameOutside [] bought base ∧
        (∀ codeHash, base.getCode codeHash = bought.getCode codeHash) ∧ refund = 0) ∨
      ∃ first, ∃ done : Delegations Meter, tx.to = some target ∧
        transactionFirstFrame Meter tx env included bought target message = .ok first ∧
        KeptAuthorizations tx env included bought base target done refund)

/-- A failed run at one gas meter leaves the fees, the nonce and any committed authorizations. -/
theorem runTransaction_values_of_error {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {block : State.BlockState} (h : runTransaction Meter env block included tx = .ok out)
    (failed : out.error.isSome = true) : FailedRun Meter tx env block included out := by
  dsimp only [FailedRun]
  unfold runTransaction at h
  obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hsettle, h⟩ := bind_ok_iff.mp h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  have hbought' := mapError_ok_iff.mp hbought
  have hsettle' := mapError_ok_iff.mp hsettle
  obtain ⟨hlogs, hdelete, htouched, hcases⟩ := processMessageCall_reads_of_error houtput failed
  have hdeleted_eq : deleted = settled := by
    have hnil : (∅ : Std.ExtTreeSet Address).toList = [] :=
      Std.ExtTreeSet.toList_eq_nil_iff.mpr rfl
    rw [mapError_ok_iff] at hdeleted
    have hd : settled.destroyTouchedEmptyAccounts fork [] = settled := by
      unfold destroyTouchedEmptyAccounts
      split <;> rfl
    simpa [deleteAccounts, hdelete, htouched, Std.ExtTreeSet.foldlM_eq_foldlM_toList, hnil, hd,
      eq_comm, pure, Except.pure, bind, Except.bind] using hdeleted
  subst hdeleted_eq
  have hmsg_target : ({ message with reservoir :=
      (allocateGas fork tx included.intrinsicGas).reservoir }).target = tx.to ∧
      ({ message with reservoir :=
        (allocateGas fork tx included.intrinsicGas).reservoir }).gas =
        (allocateGas fork tx included.intrinsicGas).execution := by
    unfold transactionMessage at hmessage
    cases hto : tx.to with
    | none =>
      rw [hto] at hmessage
      cases hmessage
      exact ⟨rfl, rfl⟩
    | some to =>
      rw [hto] at hmessage
      obtain ⟨code, -, hmessage⟩ := map_ok_iff.mp hmessage
      cases hmessage
      exact ⟨rfl, rfl⟩
  refine ⟨target, bought, message, output, output.state, output.gasLeft + output.reservoir,
    output.refund, htarget, hbought', hmessage, houtput, rfl, rfl, rfl, hlogs,
    (settleGas_accounts hsettle' included.sender).1, fun address => ?_,
    (settleGas_accounts hsettle' included.sender).2.2.2.2.2, ?_⟩
  · obtain ⟨-, hnonce, hcode, hbal, hstore, -⟩ := settleGas_accounts hsettle' address
    exact ⟨hnonce, hcode, hbal, hstore⟩
  · rcases hcases with ⟨e, read, hprep, hstate⟩ | ⟨first, hfirst, hsame, hcode⟩
    · refine .inl ⟨.inr ⟨e, read, hprep⟩, ?_, fun codeHash => by rw [hstate]; rfl, ?_⟩
      · rw [hstate]
        exact sameOutside_withReadsOf _ _
      · have hzero : output.refund = 0 := by
          unfold processMessageCall at houtput
          rw [hprep] at houtput
          cases he : e.aborts <;> simp [he] at houtput <;> cases houtput <;> rfl
        exact hzero
    · have hprep := prepareFirstFrame_reads hfirst
      cases hto : tx.to with
      | none =>
        rw [hmsg_target.1, hto] at hprep
        refine .inl ⟨.inl rfl, (hprep.1.trans hsame).mono (by simp),
          fun codeHash => (hcode codeHash).trans (hprep.2 codeHash), ?_⟩
        unfold processMessageCall at houtput
        rw [hfirst, hmsg_target.1, hto] at houtput
        obtain ⟨⟨evm, _⟩, -, houtput⟩ := bind_ok_iff.mp houtput
        cases houtput
        unfold CallOutput.ofFrame at failed ⊢
        split
        · rfl
        · rename_i herr'
          simp [herr'] at failed
      | some to =>
        have htarget_eq : to = target := by
          simpa [messageTarget, hto] using htarget
        subst htarget_eq
        rw [hmsg_target.1, hto] at hprep
        obtain ⟨done, hdone, hrefund, hfirst_same, hfirst_code⟩ := hprep
        rw [hmsg_target.2] at hdone
        refine .inr ⟨first, done, rfl, hfirst, hdone, (hfirst_same.trans hsame).mono (by simp),
          fun codeHash => (hcode codeHash).trans (hfirst_code codeHash), ?_⟩
        unfold processMessageCall at houtput
        rw [hfirst, hmsg_target.1, hto] at houtput
        obtain ⟨⟨evm, _⟩, -, houtput⟩ := bind_ok_iff.mp houtput
        cases houtput
        unfold CallOutput.ofFrame at failed ⊢
        split
        · exact hrefund
        · rename_i herr'
          simp [herr'] at failed

/-- Before Hegotá, a transaction whose message fails leaves the fees and the nonce of the sender.

It also leaves the authorizations that its first frame commits.

Up to BPO5 it runs with one counter of gas, and from Glamsterdam with the meter of state gas. -/
theorem processTransaction_values_of_error {block : State.BlockState}
    (h : processTransaction env block included tx = .ok out) (failed : out.error.isSome = true) :
    (fork < .glamsterdam ∧ FailedRun Nat tx env block included out) ∨
      (.glamsterdam ≤ fork ∧ fork < .hegota ∧
        FailedRun StateGasMeter tx env block included out) := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  have hlt_hegota : fork < .hegota := Nat.lt_of_not_le hhegota
  by_cases hglam : .glamsterdam ≤ fork
  · rw [processTransaction_of_glamsterdam hglam hlt_hegota] at h
    exact .inr ⟨hglam, hlt_hegota, runTransaction_values_of_error h failed⟩
  · have hlt_glam : fork < .glamsterdam := Nat.lt_of_not_le hglam
    rw [processTransaction_of_lt_glamsterdam hlt_glam] at h
    exact .inl ⟨hlt_glam, runTransaction_values_of_error h failed⟩

end Values

/-! ## The block -/

/-- The block after a transaction reads as the state that the transaction leaves.

That holds for each account, each word of storage and each code.

The transient storage of the next transaction is empty. -/
theorem block_of_output (out : TransactionOutput) (address : Address) (key : Bytes32)
    (codeHash : Hash32) :
    (State.TransactionState.ofBlock out.block).getAccountOptional address =
      out.state.getAccountOptional address ∧
    (State.TransactionState.ofBlock out.block).getStorage address key =
      out.state.getStorage address key ∧
    (State.TransactionState.ofBlock out.block).getCode codeHash = out.state.getCode codeHash ∧
    (State.TransactionState.ofBlock out.block).getTransientStorage address key = 0 ∧
    out.block.applyChanges.getAccountOptional address = out.state.getAccountOptional address ∧
    out.block.applyChanges.getStorage address key = out.state.getStorage address key ∧
    out.block.applyChanges.getCode codeHash = out.state.getCode codeHash := by
  have hparent : State.TransactionState.ofBlock out.block = out.state.incorporateTxIntoBlock := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hparent, getAccountOptional_incorporateTxIntoBlock]
  · rw [hparent, getStorage_incorporateTxIntoBlock]
  · rw [hparent, getCode_incorporateTxIntoBlock]
  · rw [hparent, getTransientStorage_incorporateTxIntoBlock]
  · rw [State.BlockState.getAccountOptional_applyChanges, hparent,
      getAccountOptional_incorporateTxIntoBlock]
  · rw [State.BlockState.getStorage_applyChanges, hparent, getStorage_incorporateTxIntoBlock]
  · rw [State.BlockState.getCode_applyChanges, hparent, getCode_incorporateTxIntoBlock]

end EthLib.Execution.Transactions

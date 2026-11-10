module

public import EthLib.Execution.Proofs.Evm.Call.Nonce
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: what a transaction whose message fails leaves

When the message of a transaction fails, every write of the message is undone.

The transaction still leaves the writes that come before and after its message.

The first theorems say only where those writes land.

The later ones say their values.

- The sender buys the gas: its nonce grows by one and it pays the fee.
- The fee is the gas limit times the price, plus the blob fee.
- From Pectra, each authorization that an authority accepts adds one to its nonce.
- The last one sets the code of the authority: a delegation indicator, or no code.
- The sender gets back the price of the gas it did not use.
- The beneficiary gets the priority fee of the gas that the transaction used.
- Storage stays at the beneficiary unless the payment deletes it.

The values read a missing account as empty, so they do not say which of these accounts exist.

A halt before the first frame undoes the authorizations, as [EIP-8037][e8037] asks.

A frame that fails keeps each accepted authorization, as [EIP-7702][e7702] asks.

So the state after the transaction reads as the state before it at every other address.

That holds for the account, every word of storage and every word of transient storage.

It holds up to Glamsterdam, whether the message fails in its first frame or before it starts.

Up to BPO5, a call halts before its first frame only when a code is missing.

That error aborts the whole run, so up to BPO5 a failed call keeps its authorizations.

A sender that signs its own authorization then ends two nonces above its transaction.

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

/-- Applying an authorization lowers no nonce. -/
theorem nonceLe_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    NonceLe done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact NonceLe.refl _
  · exact NonceLe.refl _
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    unfold delegate at hdelegate
    obtain ⟨coded, hcode, hdelegate⟩ := bind_ok_iff.mp hdelegate
    obtain ⟨bumped, hnonce, hdelegate⟩ := bind_ok_iff.mp hdelegate
    cases hdelegate
    rw [hstate] at hcode
    intro address
    have h1 := nonceLe_setCode hcode address
    simp only [State.TransactionState.getAccount_recordAccountRead] at h1
    exact Nat.le_trans h1 (nonceLe_incrementNonce hnonce address)

/-- Applying an authorization keeps the created accounts. -/
theorem createdAccounts_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    done'.state.createdAccounts = done.state.createdAccounts := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · rfl
  · rfl
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    unfold delegate at hdelegate
    obtain ⟨coded, hcode, hdelegate⟩ := bind_ok_iff.mp hdelegate
    obtain ⟨bumped, hnonce, hdelegate⟩ := bind_ok_iff.mp hdelegate
    cases hdelegate
    rw [hstate] at hcode
    rw [State.TransactionState.createdAccounts_modifyState hnonce,
      State.TransactionState.createdAccounts_setCode hcode,
      State.TransactionState.createdAccounts_recordAccountRead]

/-- Authorizations that succeed lower no nonce. -/
theorem nonceLe_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      NonceLe start.state done.state
  | [], _, _, h => by
    cases h
    exact NonceLe.refl _
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (nonceLe_applyAuthorization hnext).trans (nonceLe_foldlM_applyAuthorization h)

/-- Authorizations that succeed keep the created accounts. -/
theorem createdAccounts_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      done.state.createdAccounts = start.state.createdAccounts
  | [], _, _, h => by
    cases h
    rfl
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (createdAccounts_foldlM_applyAuthorization h).trans
      (createdAccounts_applyAuthorization hnext)

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

/-- Two states that read the same outside a list read the same account at an address off it. -/
private theorem getAccount_of_sameOutside {touched : List Address}
    {state state' : State.TransactionState} {address : Address}
    (h : SameOutside touched state state') (hout : address ∉ touched) :
    state'.getAccount address = state.getAccount address := by
  unfold getAccount
  rw [(h address hout).1]

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

/-- The first frame of a transaction lowers no nonce. -/
theorem nonceLe_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    NonceLe state first.state := by
  have reads := prepareFirstFrame_reads h
  intro address
  unfold State.TransactionState.getAccount
  split at reads
  · rw [(reads.1 address List.not_mem_nil).1]
    exact Nat.le_refl _
  · obtain ⟨done, hdone, -, same, -⟩ := reads
    rw [(same address List.not_mem_nil).1]
    exact nonceLe_foldlM_applyAuthorization hdone address

/-- The first frame of a transaction keeps the created accounts. -/
theorem createdAccounts_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    first.state.createdAccounts = state.createdAccounts := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h <;>
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        rfl
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target _
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have hcreated := createdAccounts_foldlM_applyAuthorization hdone
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : read0.createdAccounts = state.createdAccounts := by
      subst hread
      split <;> exact hcreated
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact base
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact base

/-- Up to BPO5, the first frame of a call fails only when the state lacks a code.

That error aborts the whole run, so a call that fails up to BPO5 always starts its first frame. -/
theorem aborts_of_prepareFirstFrame_of_lt_glamsterdam (hfork : fork < .glamsterdam)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {target : Address} {e : EvmError} {read : State.TransactionState}
    (htarget : message.target = some target)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .error (e, read)) :
    e.aborts = true := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hfork
  -- A missing code comes out as an error of the state.
  have hstate : ∀ {α : Type} {x : Except State.StateError α} {s : State.TransactionState},
      x.mapError (fun e => (EvmError.state e, s)) = .error (e, read) → e.aborts = true := by
    intro α x s hx
    cases x with
    | error e' =>
      simp only [Except.mapError, Except.error.injEq, Prod.mk.injEq] at hx
      rw [← hx.1]
      rfl
    | ok _ => cases hx
  unfold prepareFirstFrame at h
  rw [htarget] at h
  dsimp only at h
  rcases bind_eq_error h with hauth | ⟨done, -, h⟩
  · exact aborts_of_foldlM_applyAuthorization_of_lt_glamsterdam hfork hauth
  simp only [hpre, false_and, ↓reduceIte] at h
  rcases bind_eq_error h with hcharge | ⟨meter, -, h⟩
  · cases hcharge
  rcases bind_eq_error h with hcode | ⟨code, -, h⟩
  · exact hstate hcode
  split at h
  · rcases bind_eq_error h with hcharge | ⟨meter', -, h⟩
    · cases hcharge
    rcases bind_eq_error h with hcode | ⟨code', -, h⟩
    · exact hstate hcode
    · cases h
  · cases h

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
    (∀ key, (address ≠ env.coinbase ∨ out.state.getAccountOptional env.coinbase ≠ none) →
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

The refund is then 0.

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
  · -- The gas purchase raised the nonce of the sender, and nothing since lowered it.
    have hsender : (output.state.getAccount included.sender).nonce ≠ 0 := by
      have hbump := (buyGas_sender rfl hbought').2.2
      have hle : (bought.getAccount included.sender).nonce ≤
          (output.state.getAccount included.sender).nonce := by
        rcases hcases with ⟨e, read, -, hstate⟩ | ⟨first, hfirst, hsame, -⟩
        · rw [hstate, getAccount_of_sameOutside (sameOutside_withReadsOf bought read)
            List.not_mem_nil]
          exact Nat.le_refl _
        · rw [getAccount_of_sameOutside hsame List.not_mem_nil]
          exact nonceLe_prepareFirstFrame hfirst _
      omega
    obtain ⟨-, hnonce, hcode, hbal, hstore, -⟩ := settleGas_accounts hsettle' address
    exact ⟨hnonce, hcode, hbal, fun key hcoinbase => hstore key (.inr hsender) hcoinbase⟩
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

/-- A creation holds no authorization. -/
theorem authorizations_eq_nil_of_to_eq_none (h : tx.to = none) : tx.authorizations = [] := by
  cases tx <;> simp_all [Transaction.to, Transaction.authorizations]

/-- What a failed run leaves an authority whose code is empty or a delegation indicator. -/
private theorem failedRun_authority {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {block : State.BlockState} (hrun : FailedRun Meter tx env block included out)
    {authority : Address} {code : ByteArray}
    (hcode : (State.TransactionState.ofBlock block).getCode
      ((State.TransactionState.ofBlock block).getAccount authority).codeHash = .ok code)
    (hdelegable : (code.size = 0 || isValidDelegation code) = true) :
    let pre := State.TransactionState.ofBlock block
    let start := (pre.getAccount authority).nonce + if authority = included.sender then 1 else 0
    let accepted := acceptedBy env.chainId.toNat authority start tx.authorizations
    (((out.state.getAccount authority).nonce = start + accepted.length ∧
        (out.state.getAccount authority).codeHash =
          delegatedCodeHash accepted (pre.getAccount authority).codeHash) ∨
      (.glamsterdam ≤ fork ∧ (out.state.getAccount authority).nonce = start ∧
        (out.state.getAccount authority).codeHash = (pre.getAccount authority).codeHash)) ∧
    (authority ≠ included.sender → authority ≠ env.coinbase →
      (out.state.getAccount authority).balance.toNat =
        (pre.getAccount authority).balance.toNat) := by
  intro pre start accepted
  obtain ⟨target, bought, message, output, base, gasLeft, refund, -, hbought, hmessage, houtput,
    rfl, -, -, -, -, hsettled, -, hcases⟩ := hrun
  obtain ⟨hnonce, hhash, hbal, -⟩ := hsettled authority
  -- The gas purchase changes only the nonce and the balance of the sender.
  have hbought_hash : (bought.getAccount authority).codeHash = (pre.getAccount authority).codeHash
      ∧ (bought.getAccount authority).nonce = start ∧
      (authority ≠ included.sender →
        (bought.getAccount authority).balance = (pre.getAccount authority).balance) := by
    by_cases hs : authority = included.sender
    · rw [hs]
      refine ⟨(buyGas_keeps hbought).1, ?_, fun hne => absurd rfl hne⟩
      rw [(buyGas_sender rfl hbought).2.2]
      simp [start, pre, hs]
    · rw [getAccount_of_sameOutside (sameOutside_buyGas hbought) (by simpa using hs)]
      exact ⟨rfl, by simp [start, pre, hs], fun _ => rfl⟩
  obtain ⟨hb_hash, hb_nonce, hb_bal⟩ := hbought_hash
  have hb_code : bought.getCode (bought.getAccount authority).codeHash = .ok code := by
    rw [hb_hash, (buyGas_keeps hbought).2.2]
    exact hcode
  have hfees : authority ≠ included.sender → authority ≠ env.coinbase →
      (out.state.getAccount authority).balance.toNat =
        (output.state.getAccount authority).balance.toNat :=
    fun hs hc => by simp [hbal, Ne.symm hs, Ne.symm hc]
  -- No authorization stays: the state before settlement reads as after the gas purchase.
  have kept_none : SameOutside [] bought output.state → accepted = [] →
      ((out.state.getAccount authority).nonce = start + accepted.length ∧
        (out.state.getAccount authority).codeHash =
          delegatedCodeHash accepted (pre.getAccount authority).codeHash) ∧
      (authority ≠ included.sender → authority ≠ env.coinbase →
        (out.state.getAccount authority).balance.toNat =
          (pre.getAccount authority).balance.toNat) := by
    intro hsame hnil
    have hbase := getAccount_of_sameOutside hsame (address := authority) List.not_mem_nil
    rw [hnil]
    refine ⟨⟨by rw [hnonce, hbase, hb_nonce]; rfl, by rw [hhash, hbase, hb_hash]; rfl⟩,
      fun hs hc => ?_⟩
    rw [hfees hs hc, hbase, hb_bal hs]
  rcases hcases with ⟨hhalt, hsame, -, -⟩ | ⟨first, done, hto, -, hdone, hsame_done, -, -⟩
  · cases hto : tx.to with
    | none =>
      have hnil : accepted = [] := by
        simp only [accepted, authorizations_eq_nil_of_to_eq_none hto, acceptedBy]
      obtain ⟨hvalues, hbalance⟩ := kept_none hsame hnil
      exact ⟨.inl hvalues, hbalance⟩
    | some to =>
      rcases hhalt with hnone | ⟨e, read, hprep⟩
      · rw [hto] at hnone
        cases hnone
      have hbase := getAccount_of_sameOutside hsame (address := authority) List.not_mem_nil
      refine ⟨?_, fun hs hc => by rw [hfees hs hc, hbase, hb_bal hs]⟩
      by_cases hglam : .glamsterdam ≤ fork
      · exact .inr ⟨hglam, by rw [hnonce, hbase, hb_nonce], by rw [hhash, hbase, hb_hash]⟩
      · -- Up to BPO5, the first frame of a call fails only with an error that aborts the run.
        have htarget : ({ message with reservoir :=
            (allocateGas fork tx included.intrinsicGas).reservoir }).target = some to := by
          rw [← hto]
          exact (target_transactionMessage hmessage).1
        have habort := aborts_of_prepareFirstFrame_of_lt_glamsterdam (Nat.lt_of_not_le hglam)
          htarget hprep
        simp only [processMessageCall, transactionFirstFrame] at houtput hprep
        rw [hprep] at houtput
        simp [habort] at houtput
  · have hdelegated := foldlM_applyAuthorization_authority hdone hb_code hdelegable
    have hbase := getAccount_of_sameOutside hsame_done (address := authority) List.not_mem_nil
    rw [hdelegated] at hbase
    refine ⟨.inl ⟨?_, ?_⟩, fun hs hc => ?_⟩
    · rw [hnonce, hbase]
      simp only [hb_nonce, accepted]
    · rw [hhash, hbase]
      simp only [hb_nonce, hb_hash, accepted]
    · rw [hfees hs hc, hbase, hb_bal hs]

/-- A transaction whose message fails leaves each authority the authorizations that it accepts.

The code of the authority before the transaction must be empty or a delegation indicator.

Its nonce starts at its nonce before the transaction, plus one for the sender, who buys the gas.

It gains one per accepted authorization, and its code hash is that of the code the last one sets.

Up to BPO5, a failed call always keeps its authorizations, as [EIP-7702][e7702] asks.

From Glamsterdam, a halt before the first frame undoes them, as [EIP-8037][e8037] asks.

The authority then keeps its code hash and that starting nonce.

Its balance stays unless it is the sender or the beneficiary.

[e7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[e8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-halts-and-reverts -/
theorem processTransaction_authority_of_error {block : State.BlockState}
    (h : processTransaction env block included tx = .ok out) (failed : out.error.isSome = true)
    {authority : Address} {code : ByteArray}
    (hcode : (State.TransactionState.ofBlock block).getCode
      ((State.TransactionState.ofBlock block).getAccount authority).codeHash = .ok code)
    (hdelegable : (code.size = 0 || isValidDelegation code) = true) :
    let pre := State.TransactionState.ofBlock block
    let start := (pre.getAccount authority).nonce + if authority = included.sender then 1 else 0
    let accepted := acceptedBy env.chainId.toNat authority start tx.authorizations
    (((out.state.getAccount authority).nonce = start + accepted.length ∧
        (out.state.getAccount authority).codeHash =
          delegatedCodeHash accepted (pre.getAccount authority).codeHash) ∨
      (.glamsterdam ≤ fork ∧ (out.state.getAccount authority).nonce = start ∧
        (out.state.getAccount authority).codeHash = (pre.getAccount authority).codeHash)) ∧
    (authority ≠ included.sender → authority ≠ env.coinbase →
      (out.state.getAccount authority).balance.toNat =
        (pre.getAccount authority).balance.toNat) := by
  rcases processTransaction_values_of_error h failed with ⟨-, hrun⟩ | ⟨-, -, hrun⟩
  · exact failedRun_authority hrun hcode hdelegable
  · exact failedRun_authority hrun hcode hdelegable

/-- A sender that signs its own authorization ends a failed call two nonces above its transaction.

The authorization is the only one of the transaction, and it is in scope.

Its nonce is the nonce of the transaction plus one, since the gas purchase comes first.

From Glamsterdam, a halt before the first frame undoes it, and the sender ends one nonce above. -/
theorem processTransaction_selfAuthorization_of_error {chainId : UInt64} {used : BlockGas}
    {block : State.BlockState} {auth : Authorization}
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .ok out) (failed : out.error.isSome = true)
    (hauths : tx.authorizations = [auth])
    (hscope : authorizationInScope env.chainId.toNat auth = true)
    (hrecover : recoverAuthority auth = some included.sender)
    (hnonce : auth.nonce.toNat = tx.nonce.toNat + 1) :
    (out.state.getAccount included.sender).nonce = tx.nonce.toNat + 2 ∨
      (.glamsterdam ≤ fork ∧
        (out.state.getAccount included.sender).nonce = tx.nonce.toNat + 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsender, _, code, hcode, hkind⟩ :=
    checkInclusion_eq_ok_iff.mp hcheck
  have hdelegable : (code.size = 0 || isValidDelegation code) = true := by
    rcases hkind with hempty | ⟨-, hvalid⟩
    · rw [hempty] at hcode
      simp only [getCode, ↓reduceIte, Except.ok.injEq] at hcode
      subst hcode
      rfl
    · simp [hvalid]
  have hvalues := (processTransaction_authority_of_error h failed hcode hdelegable).1
  have haccepted : acceptedBy env.chainId.toNat included.sender (tx.nonce.toNat + 1) [auth] =
      [auth] := by
    simp [acceptedBy, hscope, hrecover, hnonce]
  simp only [↓reduceIte, hauths, ← hsender] at hvalues
  simp only [haccepted, List.length_singleton] at hvalues
  rcases hvalues with ⟨hn, -⟩ | ⟨hglam, hn, -⟩
  · exact .inl hn
  · exact .inr ⟨hglam, hn⟩

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

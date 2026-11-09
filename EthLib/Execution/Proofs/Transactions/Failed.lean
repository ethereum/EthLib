module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: what a transaction whose message fails leaves

When the message of a transaction fails, every write of the message is undone.

The transaction still leaves the writes that come before and after its message.

This file proves only where those writes land, not their values.

- The sender buys the gas: its nonce grows by one and it pays the fee.
- From Pectra, each valid authorization sets the code and the nonce of its authority.
- The sender gets back the gas left, and the beneficiary gets the priority fee.
- From Spurious Dragon to Paris, an empty beneficiary paid a fee of 0 is deleted.

So the state after the transaction reads as the state before it at every other address.

That holds for the account, every word of storage and every word of transient storage.

It holds up to Glamsterdam, whether the message fails in its first frame or before it starts.

From Hegotá a transaction is not yet specified, so none runs.

[EIP-7702][e7702] keeps the authorizations when the message fails in its frame.

[e7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
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

end EthLib.Execution.Transactions

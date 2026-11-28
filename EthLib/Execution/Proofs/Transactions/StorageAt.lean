module

public import EthLib.Execution.Proofs.Evm.Call.StorageAt
public import EthLib.Execution.Proofs.Evm.Call.StorageAway
public import EthLib.Execution.Proofs.Transactions.Deletion
public import EthLib.Execution.Proofs.Transactions.NoninterferenceRun

/-!
# Proofs: a transaction keeps the storage of an account it does not read

Outside its message, each step of a transaction keeps or wipes the storage of every address.

Its message keeps or wipes the storage of an account, unless it reads the account.

When no frame of the message runs at the account, it keeps it, or wipes it from an empty account.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State.TransactionState

variable {fork : Fork} {Meter : Type} [GasMeter Meter] {address : Address}

/-! ## The steps outside the message -/

/-- An authorization keeps or wipes every storage: it only sets a code and raises a nonce. -/
theorem keptOrWiped_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    KeptOrWiped address done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact .refl _ _
  · exact .of_eq fun _ => rfl
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    obtain ⟨coded, hcode, hdelegate⟩ := bind_ok_iff.mp hdelegate
    obtain ⟨bumped, hnonce, hdelegate⟩ := bind_ok_iff.mp hdelegate
    cases hdelegate
    exact (KeptOrWiped.of_eq fun _ => rfl).trans
      ((keptOrWiped_setCode hcode).trans (keptOrWiped_incrementNonce hnonce))

/-- Authorizations that succeed keep or wipe every storage. -/
theorem keptOrWiped_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      KeptOrWiped address start.state done.state
  | [], _, _, h => by
    cases h
    exact .refl _ _
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (keptOrWiped_applyAuthorization hnext).trans (keptOrWiped_foldlM_applyAuthorization h)

/-- The first frame of a message keeps or wipes every storage of the state before it.

Only its authorizations write; the rest records reads. -/
theorem keptOrWiped_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    KeptOrWiped address state first.state := by
  have read : ∀ (s : State.TransactionState) (other : Address),
      KeptOrWiped address s (s.recordAccountRead other) := fun _ _ => .of_eq fun _ => rfl
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read _ _
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact read _ _
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target _
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have hauth : KeptOrWiped address state done.state := keptOrWiped_foldlM_applyAuthorization hdone
    -- After the authorizations, the first frame only records reads.
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : KeptOrWiped address state read0 := by
      subst hread
      split
      · exact hauth.trans (read _ _)
      · exact hauth
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact base.trans (read _ _)
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact (base.trans (read _ _)).trans (read _ _)

/-- The purchase of gas keeps or wipes every storage: it raises a nonce and takes a fee. -/
theorem keptOrWiped_buyGas {env : BlockEnvironment fork} {state bought : State.TransactionState}
    {sender : Address} {tx : Transaction} {lifted : LiftedRules}
    (h : buyGas env state sender tx lifted = .ok bought) :
    KeptOrWiped address state bought := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  exact (keptOrWiped_incrementNonce h1).trans (keptOrWiped_modifyState h2)

/-- The settlement of gas keeps or wipes every storage: it credits the sender and the beneficiary.

Before Paris, it may delete an empty beneficiary. -/
theorem keptOrWiped_settleGas {env : BlockEnvironment fork} {state settled : State.TransactionState}
    {sender : Address} {tx : Transaction} {gasLeft refundCounter gasUsed : Nat}
    {lifted : LiftedRules}
    (h : settleGas env state sender tx gasLeft refundCounter lifted = .ok (settled, gasUsed)) :
    KeptOrWiped address state settled := by
  have credit : ∀ {s s' : State.TransactionState} {other : Address} {amount : Nat},
      creditEther fork s other amount = .ok s' → KeptOrWiped address s s' := by
    intro s s' other amount hc
    unfold creditEther at hc
    split at hc
    · exact keptOrWiped_createEther hc
    · cases hc
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  refine (credit h1).trans ?_
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact keptOrWiped_destroyAccount _
    · exact .refl _ _
  · exact credit h2

/-- The deletions at the end of a transaction keep or wipe every storage. -/
theorem keptOrWiped_deleteAccounts {state state' : State.TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') : KeptOrWiped address state state' := by
  have fold : ∀ (l : List Address) (init final : State.TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      KeptOrWiped address init final := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact .refl _ _
    | cons other rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      refine KeptOrWiped.trans ?_ (ih mid final h)
      split at hmid
      · exact keptOrWiped_clearAccountPreservingBalance hmid
      · cases hmid
        exact keptOrWiped_destroyAccount _
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact (fold _ _ _ hdeleted).trans (keptOrWiped_destroyTouchedEmptyAccounts _)

/-- The purchase of gas keeps the storage of `address`, or wipes an empty account.

The sender ends with a nonce, and the account at `address` keeps its code. -/
theorem keptOrWipedEmpty_buyGas {env : BlockEnvironment fork}
    {state bought : State.TransactionState} {sender : Address} {tx : Transaction}
    {lifted : LiftedRules} (h : buyGas env state sender tx lifted = .ok bought) :
    KeptOrWipedEmpty address state bought ∧ (bought.getAccount sender).nonce ≠ 0 ∧
      (bought.getAccount address).codeHash = (state.getAccount address).codeHash := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  -- The rise of the nonce leaves the sender with a nonce.
  have hmid : mid.getAccount sender =
      { state.getAccount sender with nonce := (state.getAccount sender).nonce + 1 } :=
    getAccount_modifyState_of_nonce h1 rfl (by simp)
  -- The fee keeps that nonce.
  obtain ⟨account, hf, -⟩ := modifyState_eq_ok_iff.mp h2
  have hfee : account.nonce = (mid.getAccount sender).nonce ∧
      account.codeHash = (mid.getAccount sender).codeHash := by
    split at hf
    · cases hf
      exact ⟨rfl, rfl⟩
    · cases hf
  have hn : account.nonce ≠ 0 := by
    rw [hfee.1, hmid]
    simp
  have hbought := getAccount_modifyState_of_nonce h2 hf hn
  refine ⟨(keptOrWipedEmpty_incrementNonce h1).trans
    (keptOrWipedEmpty_modifyState h2 fun hs account' hf' hn' _ _ => ?_), ?_, ?_⟩
  · subst hs
    rw [hf] at hf'
    cases hf'
    exact absurd hn' hn
  · rw [hbought]
    exact hn
  · by_cases hs : sender = address
    · subst hs
      rw [hbought, hfee.2, hmid]
    · have hout : address ∉ [sender] := by simpa using Ne.symm hs
      rw [(sameOutside_modifyState h2).getAccount_eq hout,
        (sameOutside_incrementNonce h1).getAccount_eq hout]

/-- The settlement of gas keeps the storage of `address`, or wipes an empty account.

Before Paris, it may delete an empty beneficiary. -/
theorem keptOrWipedEmpty_settleGas {env : BlockEnvironment fork}
    {state settled : State.TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter gasUsed : Nat} {lifted : LiftedRules}
    (h : settleGas env state sender tx gasLeft refundCounter lifted = .ok (settled, gasUsed)) :
    KeptOrWipedEmpty address state settled := by
  have credit : ∀ {s s' : State.TransactionState} {other : Address} {amount : Nat},
      creditEther fork s other amount = .ok s' → KeptOrWipedEmpty address s s' := by
    intro s s' other amount hc
    unfold creditEther at hc
    split at hc
    · exact keptOrWipedEmpty_createEther hc
    · cases hc
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  refine (credit h1).trans ?_
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · rename_i hx
      exact keptOrWipedEmpty_destroyAccount fun ho => ho ▸ emptyAt_of_accountExistsAndIsEmpty hx
    · exact .refl _ _
  · exact credit h2

/-- The deletions at the end of a transaction keep the storage of `address`, or wipe it.

They wipe it only from an empty account, if the transaction does not mark the account. -/
theorem keptOrWipedEmpty_deleteAccounts {state state' : State.TransactionState}
    {output : CallOutput} (h : deleteAccounts fork state output = .ok state')
    (unmarked : address ∉ output.accountsToDelete) : KeptOrWipedEmpty address state state' := by
  have fold : ∀ (l : List Address), address ∉ l → ∀ (init final : State.TransactionState),
      l.foldlM (fun state other =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork other
        else pure (state.destroyAccount other)) init = .ok final →
      KeptOrWipedEmpty address init final := by
    intro l
    induction l with
    | nil =>
      intro _ init final h
      cases h
      exact .refl _ _
    | cons other rest ih =>
      intro hl init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      have hout : address ∉ [other] := fun hx => hl (by simp_all)
      refine KeptOrWipedEmpty.trans ?_ (ih (fun hx => hl (List.mem_cons_of_mem _ hx)) mid final h)
      split at hmid
      · exact .of_sameOutside (sameOutside_clearAccountPreservingBalance hmid) hout
      · cases hmid
        exact .of_sameOutside (sameOutside_destroyAccount _ _) hout
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact (fold _ (by simpa using unmarked) _ _ hdeleted).trans
    (keptOrWipedEmpty_destroyTouchedEmptyAccounts _)

/-- The settlement of gas keeps every read. -/
theorem readsLe_settleGas {env : BlockEnvironment fork} {state settled : State.TransactionState}
    {sender : Address} {tx : Transaction} {gasLeft refundCounter gasUsed : Nat}
    {lifted : LiftedRules}
    (h : settleGas env state sender tx gasLeft refundCounter lifted = .ok (settled, gasUsed)) :
    state.ReadsLe settled := by
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  refine (readsLe_creditEther h1).trans ?_
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact readsLe_destroyAccount _ _
    · exact .refl _
  · exact readsLe_creditEther h2

/-- An assumption: an authorization from `address` at nonce 0 finds no code there in `state`.

It asks for no code at all, and so excludes a delegation indicator at nonce 0.

No authorization makes such an indicator, but a genesis state can hold one. -/
def CodelessAtZero (address : Address) (state : State.TransactionState)
    (auths : List Authorization) : Prop :=
  ∀ auth ∈ auths, recoverAuthority auth = some address → auth.nonce = 0 →
    (state.getAccount address).codeHash = State.EMPTY_CODE_HASH

/-- The delegation of an authority keeps the storage of `address`, or wipes an empty account.

At `address`, the account must hold no code while its nonce is 0. -/
theorem keptOrWipedEmpty_delegate {state state' : State.TransactionState} {refund : Nat}
    {authority : Address} {auth : Authorization}
    (h : delegate fork state authority auth = .ok (state', refund))
    (keeps : authority = address → (state.getAccount address).nonce = 0 →
      (state.getAccount address).codeHash = State.EMPTY_CODE_HASH) :
    KeptOrWipedEmpty address state state' := by
  obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
  cases h
  exact (keptOrWipedEmpty_setCode hcode keeps).trans (keptOrWipedEmpty_incrementNonce hnonce)

/-- An authorization keeps the storage of `address`, or wipes an empty account.

The account at `address` must be as in `start`, or have a nonce, and it stays so.

An authorization from `address` at nonce 0 must find no code in `start`. -/
theorem keptOrWipedEmpty_applyAuthorization {chainId : Nat} {start : State.TransactionState}
    {done done' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok done')
    (codeless : recoverAuthority auth = some address → auth.nonce = 0 →
      (start.getAccount address).codeHash = State.EMPTY_CODE_HASH)
    (same : done.state.getAccount address = start.getAccount address ∨
      (done.state.getAccount address).nonce ≠ 0) :
    KeptOrWipedEmpty address done.state done'.state ∧
      (done'.state.getAccount address = start.getAccount address ∨
        (done'.state.getAccount address).nonce ≠ 0) := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, hrec, ⟨-, rfl⟩ |
    ⟨hacc, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact ⟨.refl _ _, same⟩
  · exact ⟨.of_eq rfl fun _ => rfl, same⟩
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    dsimp only at hdelegate
    obtain ⟨-, hself, hother⟩ := delegate_eq_ok hdelegate
    have hn := nonce_of_authorityAccepts hacc
    have read : KeptOrWipedEmpty address done.state (done.state.recordAccountRead authority) :=
      .of_eq (getAccount_recordAccountRead _ _ _) fun _ => rfl
    refine ⟨read.trans
      (keptOrWipedEmpty_delegate hdelegate fun ha h0 => ?_), ?_⟩
    · -- An authority at nonce 0 is still as in `start`, which holds no code there.
      subst ha
      rw [getAccount_recordAccountRead] at h0 ⊢
      rcases same with hs | hs
      · rw [hs]
        refine codeless hrec (UInt64.toNat_inj.mp ?_)
        rw [← hn, h0]
        rfl
      · exact absurd h0 hs
    · -- The authority ends with a nonce, and every other account stays.
      by_cases ha : authority = address
      · subst ha
        right
        dsimp only
        rw [hself]
        simp
      · dsimp only
        have hacc' : state.getAccount address = done.state.getAccount address := by
          unfold State.TransactionState.getAccount
          rw [hother address (Ne.symm ha)]
          rfl
        rw [hacc']
        exact same

/-- Authorizations that succeed keep the storage of `address`, or wipe an empty account.

The account at `address` must be as in `start`, or have a nonce, and it stays so. -/
theorem keptOrWipedEmpty_foldlM_applyAuthorization {chainId : Nat}
    {start : State.TransactionState} :
    ∀ {auths : List Authorization} {first done : Delegations Meter},
      CodelessAtZero address start auths →
      auths.foldlM (applyAuthorization fork chainId) first = .ok done →
      (first.state.getAccount address = start.getAccount address ∨
        (first.state.getAccount address).nonce ≠ 0) →
      KeptOrWipedEmpty address first.state done.state ∧
        (done.state.getAccount address = start.getAccount address ∨
          (done.state.getAccount address).nonce ≠ 0)
  | [], _, _, _, h, same => by
    cases h
    exact ⟨.refl _ _, same⟩
  | auth :: _, _, _, codeless, h, same => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    obtain ⟨k, same'⟩ := keptOrWipedEmpty_applyAuthorization hnext
      (codeless auth List.mem_cons_self) same
    obtain ⟨k', same''⟩ := keptOrWipedEmpty_foldlM_applyAuthorization
      (fun a ha => codeless a (List.mem_cons_of_mem _ ha)) h same'
    exact ⟨k.trans k', same''⟩

/-- The first frame of a message keeps the storage of `address`, or wipes an empty account.

The account at `address` is as before, or has a nonce. -/
theorem keptOrWipedEmpty_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first)
    (codeless : CodelessAtZero address state auths) :
    KeptOrWipedEmpty address state first.state ∧
      (first.state.getAccount address = state.getAccount address ∨
        (first.state.getAccount address).nonce ≠ 0) := by
  have hr := prepareFirstFrame_reads h
  split at hr
  · exact ⟨.of_sameOutside hr.1 List.not_mem_nil, .inl (hr.1.getAccount_eq List.not_mem_nil)⟩
  · obtain ⟨done, hdone, -, hsame, -⟩ := hr
    unfold applyAuthorizations at hdone
    obtain ⟨k, same⟩ := keptOrWipedEmpty_foldlM_applyAuthorization codeless hdone (.inl rfl)
    refine ⟨k.trans (.of_sameOutside hsame List.not_mem_nil), ?_⟩
    rw [hsame.getAccount_eq List.not_mem_nil]
    exact same

/-- The first frame of a message keeps the sender, the value and the transfer flag of the message.

A creation keeps its code address. -/
theorem transfer_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    first.message.caller = message.caller ∧ first.message.value = message.value ∧
      first.message.shouldTransferValue = message.shouldTransferValue ∧
      (message.target = none → first.message.codeAddress = message.codeAddress) := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target htarget
    dsimp only at h
    obtain ⟨done, -, h⟩ := bind_ok_iff.mp h
    generalize (if message.value ≠ 0 then _ else done.state) = read0 at h
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact ⟨rfl, rfl, rfl, fun hn => by simp [hn] at htarget⟩
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact ⟨rfl, rfl, rfl, fun hn => by simp [hn] at htarget⟩

/-! ## The message and the transaction -/

variable [LawfulGasMeter Meter]

/-- The message of a transaction keeps or wipes the storage of `address`, unless it reads it.

A call must run at its recipient, as the message of a transaction and a system call do. -/
theorem keptOrRead_processMessageCall {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    KeptOrRead address state output.state := by
  have ofFrame : ∀ (evm : Evm fork Meter) (refund : Nat) (touched : Std.ExtTreeSet Address),
      (CallOutput.ofFrame evm refund touched).state = evm.state := by
    intro evm refund touched
    unfold CallOutput.ofFrame
    split <;> rfl
  rw [processMessageCall_unfold] at h
  split at h
  · -- A halt before the first frame keeps the state, up to its reads.
    split at h
    · cases h
    · cases h
      exact .inl (.of_eq fun _ => rfl)
  · rename_i first hfirst
    have hstart : KeptOrWiped address state first.state :=
      keptOrWiped_prepareFirstFrame hfirst
    -- The first frame runs at the recipient, which its preparation reads.
    have hread : first.message.currentTarget = address → address ∈ first.state.accountReads :=
      fun hat => by
        rw [← hat, (substate_prepareFirstFrame hfirst).2.2.2]
        exact currentRead_prepareFirstFrame recipient hfirst
    split at h
    · obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [ofFrame]
      exact .of_keptOrWiped hstart (keptOrRead_processCreateMessage hrun hread)
    · obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [ofFrame]
      exact .of_keptOrWiped hstart (keptOrRead_processMessage hrun hread)

/-- A transaction keeps or wipes the storage of `address`, unless it reads the account.

Every frame at `address` runs from a state that has read the account.

It runs with the gas meter `Meter`. -/
theorem keptOrRead_runTransaction {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) :
    KeptOrRead address (.ofBlock block) out.state := by
  obtain ⟨target, bought, message, output, settled, htarget, hbought, hmessage, houtput, -,
    hsettle, hdelete⟩ := runTransaction_eq_ok h
  have hlast := (readsLe_settleGas hsettle).trans (readsLe_deleteAccounts hdelete)
  -- The message of a transaction runs at its recipient.
  have recipient : ∀ to, ({ message with
      reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } : Message fork).target =
        some to → to = ({ message with
          reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } :
            Message fork).currentTarget := by
    intro to hto
    obtain ⟨hmt, hmc⟩ := target_transactionMessage hmessage
    dsimp only at hto ⊢
    rw [hmc]
    rw [hmt] at hto
    unfold messageTarget at htarget
    rw [hto] at htarget
    exact Except.ok.inj htarget
  exact KeptOrRead.trans (.of_keptOrWiped (keptOrWiped_buyGas hbought)
    (keptOrRead_processMessageCall recipient houtput))
    (.inl ((keptOrWiped_settleGas hsettle).trans (keptOrWiped_deleteAccounts hdelete))) hlast

/-- A transaction keeps or wipes the storage of `address`, unless it reads the account.

It runs with the gas meter of its fork, at every fork that runs transactions. -/
theorem keptOrRead_processTransaction {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out) :
    KeptOrRead address (.ofBlock block) out.state := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  by_cases hglam : .glamsterdam ≤ fork
  · rw [processTransaction_of_glamsterdam hglam (Nat.lt_of_not_le hhegota)] at h
    exact keptOrRead_runTransaction h
  · rw [processTransaction_of_lt_glamsterdam (Nat.lt_of_not_le hglam)] at h
    exact keptOrRead_runTransaction h

/-! ## A message that runs no frame at the address -/

/-- Where the run of a message starts, from its first frame: a call, or a creation. -/
def FirstFrame.start (first : FirstFrame fork Meter) : BurnStart fork Meter :=
  match first.message.target with
  | some _ => .call first.message first.state first.substate first.meter
  | none => .create first.message first.state first.substate first.meter

/-- Every frame of the message that a transaction or a system call runs meets `P`. -/
def CallAll (P : Evm fork Meter → Prop) (chainId : Nat) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) : Prop :=
  ∀ first : FirstFrame fork Meter,
    prepareFirstFrame chainId message state substate auths paid = .ok first →
      ReachesAll P first.start

/-- No frame of the message that a transaction or a system call runs is at `address`. -/
def CallAway (address : Address) (chainId : Nat) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) : Prop :=
  CallAll (Meter := Meter) (fun reached => reached.message.currentTarget ≠ address) chainId message
    state substate auths paid

/-- The message of a transaction keeps the storage of `address`, or wipes an empty account.

No frame of the message may run at `address`.

A move of value from `address` must start where the account has a nonce.

A creation must run the code of no account.

An authorization from `address` at nonce 0 must find no code there.

An account empty at the end was empty at the start.

The message marks the account for deletion only if it was marked at the start. -/
theorem keptOrWipedEmpty_processMessageCall_of_away {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (away : CallAway (Meter := Meter) address chainId message state substate auths paid)
    (funded : SenderHasNonce address message state)
    (creates : message.target = none → message.codeAddress = none)
    (codeless : CodelessAtZero address state auths) :
    KeptOrWipedEmpty address state output.state ∧
      (address ∉ substate.accountsToDelete → address ∉ output.accountsToDelete) := by
  rw [processMessageCall_unfold] at h
  split at h
  · -- A halt before the first frame keeps the state, up to its reads, and deletes nothing.
    split at h
    · cases h
    · cases h
      exact ⟨.of_eq rfl fun _ => rfl, fun _ => by simp [CallOutput.ofHalt]⟩
  · rename_i first hfirst
    obtain ⟨hstart, hsame⟩ := keptOrWipedEmpty_prepareFirstFrame hfirst codeless
    obtain ⟨hcaller, hvalue, hmoves, hcreate⟩ := transfer_prepareFirstFrame hfirst
    -- The first frame moves the value from the sender, which keeps its nonce.
    have hfunded : SenderHasNonce address first.message first.state := fun ht hv hc => by
      rw [hmoves] at ht
      rw [hvalue] at hv
      rw [hcaller] at hc
      rcases hsame with hs | hs
      · rw [hs]
        exact funded ht hv hc
      · exact hs
    have hunmarked : address ∉ substate.accountsToDelete →
        address ∉ first.substate.accountsToDelete := fun unmarked => by
      rw [(substate_prepareFirstFrame hfirst).1]
      exact unmarked
    have htarget := (substate_prepareFirstFrame hfirst).2.2.1
    have hfar := away first hfirst
    unfold FirstFrame.start at hfar
    rw [htarget] at hfar
    split at h
    · rename_i hnone
      rw [hnone] at hfar
      obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      have hcode : first.message.codeAddress = none := (hcreate hnone).trans (creates hnone)
      obtain ⟨k, u⟩ := keptOrWipedEmpty_processCreateMessage_of_away hrun hfar hfunded hcode
      rw [state_ofFrame]
      exact ⟨hstart.trans k, fun hu hx =>
        u (hunmarked hu) (accountsToDelete_ofFrame_subset _ _ _ _ hx)⟩
    · rename_i t hsome
      rw [hsome] at hfar
      obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      obtain ⟨k, u⟩ := keptOrWipedEmpty_processMessage_of_away hrun hfar hfunded
      rw [state_ofFrame]
      exact ⟨hstart.trans k, fun hu hx =>
        u (hunmarked hu) (accountsToDelete_ofFrame_subset _ _ _ _ hx)⟩

variable (Meter) in
/-- Every frame of the message that a transaction runs, with the gas meter `Meter`, meets `P`. -/
def TransactionAll (P : Evm fork Meter → Prop) (env : BlockEnvironment fork)
    (block : State.BlockState) (included : Included) (tx : Transaction) (out : TransactionOutput) :
    Prop :=
  ∀ {target bought message output settled},
    TransactionRun Meter env block included tx out target bought message output settled →
    CallAll P env.chainId.toNat
      { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
      (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
      (paidWrites included.sender target tx)

variable (Meter) in
/-- No frame of the message that a transaction runs, with the gas meter `Meter`, is at `address`. -/
def TransactionAway (address : Address) (env : BlockEnvironment fork) (block : State.BlockState)
    (included : Included) (tx : Transaction) (out : TransactionOutput) : Prop :=
  TransactionAll Meter (fun reached => reached.message.currentTarget ≠ address) env block included
    tx out

/-- A transaction keeps the storage of `address`, or wipes it from an account empty at its start.

No frame of its message may run at `address`.

An authorization from `address` at nonce 0 must find no code there.

An account empty at the end was empty at the start.

It runs with the gas meter `Meter`. -/
theorem keptOrWipedEmpty_runTransaction_of_away {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out)
    (away : TransactionAway Meter address env block included tx out)
    (codeless : CodelessAtZero address (.ofBlock block) tx.authorizations) :
    KeptOrWipedEmpty address (.ofBlock block) out.state := by
  obtain ⟨target, bought, message, output, settled, run⟩ := runTransaction_eq_ok h
  have far := away run
  obtain ⟨-, hbought, hmessage, houtput, -, hsettle, hdelete⟩ := run
  obtain ⟨kb, hnonce, hcode⟩ := keptOrWipedEmpty_buyGas hbought
  -- The message comes from the sender, which has a nonce once it pays for gas.
  have hfunded : SenderHasNonce address
      { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir }
      bought := fun _ _ hc => by
    have hc' : message.caller = address := hc
    rw [caller_transactionMessage hmessage] at hc'
    rw [← hc']
    exact hnonce
  have hcodeless : CodelessAtZero address bought tx.authorizations := fun auth ha hr hz => by
    rw [hcode]
    exact codeless auth ha hr hz
  obtain ⟨km, unmarked⟩ := keptOrWipedEmpty_processMessageCall_of_away houtput far hfunded
    (fun hn => codeAddress_transactionMessage (message := message) hmessage hn) hcodeless
  -- The transaction starts with no account to delete.
  have hmarks := unmarked (by simp [startSubstate, Substate.empty])
  exact kb.trans (km.trans ((keptOrWipedEmpty_settleGas hsettle).trans
    (keptOrWipedEmpty_deleteAccounts hdelete hmarks)))

/-- A transaction keeps the storage of `address`, or wipes it from an account empty at its start.

No frame of its message may run at `address`.

An authorization from `address` at nonce 0 must find no code there.

An account empty at the end was empty at the start.

It runs with the gas meter of its fork. -/
theorem keptOrWipedEmpty_processTransaction_of_away {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out)
    (away : fork < .glamsterdam → TransactionAway Nat address env block included tx out)
    (awayState : .glamsterdam ≤ fork →
      TransactionAway StateGasMeter address env block included tx out)
    (codeless : CodelessAtZero address (.ofBlock block) tx.authorizations) :
    KeptOrWipedEmpty address (.ofBlock block) out.state := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  by_cases hglam : .glamsterdam ≤ fork
  · rw [processTransaction_of_glamsterdam hglam (Nat.lt_of_not_le hhegota)] at h
    exact keptOrWipedEmpty_runTransaction_of_away h (awayState hglam) codeless
  · rw [processTransaction_of_lt_glamsterdam (Nat.lt_of_not_le hglam)] at h
    exact keptOrWipedEmpty_runTransaction_of_away h (away (Nat.lt_of_not_le hglam)) codeless

end EthLib.Execution.Transactions

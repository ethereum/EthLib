module

public import EthLib.Execution.Proofs.Evm.Call.Candidate
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Deletion

/-!
# Proofs: a transaction makes no new deployment candidate

A deployment candidate is an address with nonce 0 and no code, where a creation may deploy.

A transaction makes none, except at an address whose storage it wiped.

Buying gas raises the nonce of the sender.

Settling gas moves ether, or deletes an empty beneficiary and so wipes its storage.

An authorization sets the code of its authority, then raises its nonce.

Clearing the code of an authority with nonce 0 leaves a candidate only until the nonce rises.

The message makes no new candidate, and the deletions at the end wipe the storage they delete.

Source: [EIP-7702, Behavior][eip7702].

[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState (NoNewCandidate)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Changes of the state -/

/-- A state with the writes and the block of another meets the condition on candidates too. -/
private theorem noNewCandidate_of_sameWrites {block : BlockState} {tx tx' : TransactionState}
    (hinv : NoNewCandidate block tx) (h : SameWrites tx' tx) (hp : tx'.parent = tx.parent) :
    NoNewCandidate block tx' := fun a hn hc => by
  rw [h.getAccount hp] at hn hc
  rw [h.storageClears]
  exact hinv a hn hc

/-- A change of one account keeps each wiped storage. -/
private theorem mem_storageClears_modifyState {tx tx' : TransactionState} {address x : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (hx : x ∈ tx.storageClears) : x ∈ tx'.storageClears := by
  obtain ⟨updated, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
  split
  · simp [TransactionState.destroyAccount, TransactionState.destroyStorage,
      TransactionState.setAccount, TransactionState.recordAccountRead, hx]
  · exact hx

/-- A change of one account that keeps its nonce and its code keeps the condition. -/
private theorem noNewCandidate_modifyState_of_keeps {block : BlockState}
    {tx tx' : TransactionState} {address : Address} {f : Account → Except StateError Account}
    (hinv : NoNewCandidate block tx)
    (hf : ∀ updated, f (tx.getAccount address) = .ok updated →
      updated.nonce = (tx.getAccount address).nonce ∧
        updated.codeHash = (tx.getAccount address).codeHash)
    (h : tx.modifyState fork address f = .ok tx') : NoNewCandidate block tx' :=
  hinv.modifyState (fun updated hupd hn hc => by
    obtain ⟨hn', hc'⟩ := hf updated hupd
    exact .inr ⟨hn' ▸ hn, hc' ▸ hc⟩) h

/-- A credit of ether keeps the condition on candidates. -/
private theorem noNewCandidate_creditEther {block : BlockState} {tx tx' : TransactionState}
    {address : Address} {amount : Nat} (hinv : NoNewCandidate block tx)
    (h : creditEther fork tx address amount = .ok tx') : NoNewCandidate block tx' := by
  unfold creditEther at h
  split at h
  · refine noNewCandidate_modifyState_of_keeps hinv (fun updated hupd => ?_) h
    unfold Account.credit at hupd
    split at hupd <;> cases hupd
    exact ⟨rfl, rfl⟩
  · cases h

/-- An authorization that sets the code of its authority keeps the condition on candidates.

The authority ends with a nonce above 0, so it is no candidate. -/
private theorem noNewCandidate_delegate {block : BlockState} {state state' : TransactionState}
    {authority : Address} {auth : Authorization} {refund : Nat}
    (hinv : NoNewCandidate block state)
    (h : delegate fork state authority auth = .ok (state', refund)) :
    NoNewCandidate block state' := by
  have hclears : ∀ x, x ∈ state.storageClears → x ∈ state'.storageClears := by
    intro x hx
    obtain ⟨coded, hcode, h⟩ := bind_ok_iff.mp h
    obtain ⟨bumped, hnonce, h⟩ := bind_ok_iff.mp h
    cases h
    refine mem_storageClears_modifyState hnonce ?_
    dsimp only [TransactionState.setCode] at hcode
    split at hcode
    · exact mem_storageClears_modifyState hcode hx
    · exact mem_storageClears_modifyState hcode hx
  obtain ⟨-, hself, hother⟩ := delegate_eq_ok h
  intro x hn hc
  by_cases hx : x = authority
  · subst hx
    rw [hself] at hn
    exact absurd hn (Nat.succ_ne_zero _)
  · have hacc : state'.getAccount x = state.getAccount x := by
      simp only [TransactionState.getAccount, hother x hx]
    rw [hacc] at hn hc
    exact (hinv x hn hc).imp_left (hclears x)

/-! ## The authorizations -/

/-- One authorization keeps the condition on candidates. -/
private theorem noNewCandidate_applyAuthorization {block : BlockState} {chainId : Nat}
    {done done' : Delegations Meter} {auth : Authorization}
    (hinv : NoNewCandidate block done.state)
    (h : applyAuthorization fork chainId done auth = .ok done') :
    NoNewCandidate block done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact hinv
  · exact hinv.recordAccountRead authority
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    exact noNewCandidate_delegate (hinv.recordAccountRead authority) hdelegate

/-- A list of authorizations keeps the condition on candidates. -/
private theorem noNewCandidate_foldlM_applyAuthorization {block : BlockState} {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      NoNewCandidate block start.state → NoNewCandidate block done.state
  | [], _, _, h, hinv => by
    cases h
    exact hinv
  | _ :: _, _, _, h, hinv => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact noNewCandidate_foldlM_applyAuthorization h
      (noNewCandidate_applyAuthorization hinv hnext)

/-- The authorizations of a transaction, from a state with no new candidate, end with none.

A new candidate is still allowed at an address whose storage was wiped. -/
theorem applyAuthorizations_noNewCandidate {block : BlockState} {chainId : Nat}
    {state : TransactionState} {accessed : Std.ExtTreeSet Address} {meter : Meter}
    {paid : Std.ExtTreeSet Address} {auths : List Authorization} {done : Delegations Meter}
    (hinv : NoNewCandidate block state)
    (h : applyAuthorizations fork chainId state accessed meter paid auths = .ok done) :
    NoNewCandidate block done.state :=
  noNewCandidate_foldlM_applyAuthorization h hinv

/-! ## The message -/

/-- Preparing the first frame of a message keeps the condition on candidates. -/
theorem noNewCandidate_prepareFirstFrame {block : BlockState} {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (hinv : NoNewCandidate block state)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    NoNewCandidate block first.state := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · have hfin : first.state = state.recordAccountRead message.currentTarget := by
        split at h <;>
        · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
          cases h
          rfl
      rw [hfin]
      exact hinv.recordAccountRead _
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have vdone := applyAuthorizations_noNewCandidate hinv hdone
    dsimp only at h
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have v1 : NoNewCandidate block s1 := by
      rw [← hs1]
      split
      · exact vdone.recordAccountRead _
      · exact vdone
    have v2 : NoNewCandidate block (s1.recordAccountRead target) := v1.recordAccountRead _
    split at h
    all_goals
      obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact v2
      · dsimp only at h
        split at h
        all_goals
          obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact v2.recordAccountRead _

/-- The message of a transaction, from a state with no new candidate, ends with none.

A new candidate is still allowed at an address whose storage was wiped. -/
theorem processMessageCall_noNewCandidate [LawfulGasMeter Meter] {block : BlockState}
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (hinv : NoNewCandidate block state)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    NoNewCandidate block output.state := by
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact noNewCandidate_of_sameWrites hinv (SameWrites.withReadsOf _ _) rfl
  · rw [hprep] at h
    dsimp only at h
    have vfirst := noNewCandidate_prepareFirstFrame hinv hprep
    have hframe : ∀ {evm : Evm fork Meter} {r : Nat} {t : Std.ExtTreeSet Address},
        (CallOutput.ofFrame evm r t).state = evm.state := by
      intro evm r t
      unfold CallOutput.ofFrame
      dsimp only
      split <;> rfl
    split at h
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact processCreateMessage_noNewCandidate vfirst hrun
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact processMessage_noNewCandidate vfirst hrun

/-! ## The transaction -/

/-- Buying gas keeps the condition on candidates, since it raises a nonce and takes a fee. -/
theorem noNewCandidate_buyGas {env : BlockEnvironment fork} {block : BlockState}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    (hinv : NoNewCandidate block state) (h : buyGas env state sender tx = .ok state') :
    NoNewCandidate block state' := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  have vmid : NoNewCandidate block mid :=
    hinv.modifyState (fun _ hupd hn _ => by cases hupd; exact absurd hn (Nat.succ_ne_zero _)) h1
  refine noNewCandidate_modifyState_of_keeps vmid (fun updated hupd => ?_) h2
  split at hupd
  · cases hupd
    exact ⟨rfl, rfl⟩
  · cases hupd

/-- Settling gas keeps the condition on candidates.

It moves ether, or deletes an empty beneficiary. -/
private theorem noNewCandidate_settleGas {env : BlockEnvironment fork} {block : BlockState}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter used : Nat} (hinv : NoNewCandidate block state)
    (h : settleGas env state sender tx gasLeft refundCounter = .ok (state', used)) :
    NoNewCandidate block state' := by
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  have vmid := noNewCandidate_creditEther hinv h1
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact vmid.destroyAccount _
    · exact vmid
  · exact noNewCandidate_creditEther vmid h2

/-- The deletion of empty touched accounts keeps the condition on candidates. -/
private theorem noNewCandidate_foldl_destroy {block : BlockState} :
    ∀ (touched : List Address) {tx : TransactionState}, NoNewCandidate block tx →
      NoNewCandidate block (touched.foldl (fun tx address =>
        if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx) tx)
  | [], _, hinv => hinv
  | address :: rest, tx, hinv => by
    refine noNewCandidate_foldl_destroy rest ?_
    dsimp only
    split
    · exact hinv.destroyAccount address
    · exact hinv

/-- The deletions at the end of a transaction keep the condition on candidates. -/
private theorem noNewCandidate_deleteAccounts {block : BlockState}
    {state state' : TransactionState} {output : CallOutput} (hinv : NoNewCandidate block state)
    (h : deleteAccounts fork state output = .ok state') : NoNewCandidate block state' := by
  have fold : ∀ (l : List Address) (init final : TransactionState),
      NoNewCandidate block init →
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      NoNewCandidate block final := by
    intro l
    induction l with
    | nil =>
      intro init final hinit h
      cases h
      exact hinit
    | cons address rest ih =>
      intro init final hinit h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      refine ih mid final ?_ h
      split at hmid
      · unfold TransactionState.clearAccountPreservingBalance at hmid
        exact (hinit.destroyStorage address).modifyState
          (fun _ _ _ _ => .inl (by simp [TransactionState.destroyStorage])) hmid
      · cases hmid
        exact hinit.destroyAccount address
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  have vdel := fold _ _ _ hinv hdeleted
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact vdel
  · exact noNewCandidate_foldl_destroy _ vdel

/-- A run of a transaction with any gas meter makes no new deployment candidate. -/
private theorem runTransaction_noNewCandidate [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {output : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok output) :
    NoNewCandidate block output.state := by
  obtain ⟨target, bought, message, out, settled, -, hBought, -, hOutput, -,
    hSettle, hDeleted⟩ := runTransaction_eq_ok h
  have vb := noNewCandidate_buyGas (NoNewCandidate.ofBlock block) hBought
  have vout := processMessageCall_noNewCandidate vb hOutput
  exact noNewCandidate_deleteAccounts (noNewCandidate_settleGas vout hSettle) hDeleted

/-- A transaction makes no candidate that its block lacked, except where it wiped storage. -/
theorem processTransaction_noNewCandidate {env : BlockEnvironment fork} {block : BlockState}
    {included : Included} {tx : Transaction} {output : TransactionOutput}
    (h : processTransaction env block included tx = .ok output) :
    NoNewCandidate block output.state := by
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · exact runTransaction_noNewCandidate h
  · exact runTransaction_noNewCandidate h

end EthLib.Execution.Transactions

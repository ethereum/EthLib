module

public import EthLib.Execution.Proofs.Evm.Call.NoncesFit
public import EthLib.Execution.Proofs.Transactions.Replay

/-!
# Proofs: no transaction raises a nonce above `2^64 - 1`

EIP-2681 limits every nonce to `2^64 - 1`.

The inclusion check asks that the nonce of a transaction is below that bound.

It also asks that the nonce equals the nonce of the sender, so the purchase of gas keeps the bound.

An EIP-7702 authorization raises its authority's nonce from the nonce it names, below the bound.

A creation transaction runs only at an address with nonce 0, by EIP-684.

The messages keep the bound; the end of a transaction only changes balances and deletes accounts.
-/

@[expose] public section

namespace EthLib.Execution.State

/-- Every account of the state has a nonce of at most `2^64 - 1`, the bound of EIP-2681.

An absent account counts as none. -/
def State.NoncesFit (state : State) : Prop :=
  ∀ address account, state.getAccountOptional address = some account →
    account.nonce ≤ Evm.MAX_NONCE

/-- Every account of the block state, with its writes, has a nonce of at most `2^64 - 1`. -/
def BlockState.NoncesFit (block : BlockState) : Prop :=
  (TransactionState.ofBlock block).NoncesFit

/-- A block state with no writes is within the bound exactly when its state is. -/
theorem BlockState.noncesFit_ofState_iff (state : State) :
    BlockState.NoncesFit ⟨state, ∅, ∅, ∅, ∅⟩ ↔ state.NoncesFit := by
  have same : ∀ address, (TransactionState.ofBlock ⟨state, ∅, ∅, ∅, ∅⟩).getAccountOptional
      address = state.getAccountOptional address := by
    intro address
    simp [TransactionState.ofBlock, TransactionState.getAccountOptional]
  constructor
  · intro hfit address account hacc
    have := hfit address
    unfold TransactionState.getAccount at this
    rw [same, hacc] at this
    exact this
  · intro hfit address
    unfold TransactionState.getAccount
    rw [same]
    cases hacc : state.getAccountOptional address with
    | none => simp [EMPTY_ACCOUNT, Evm.MAX_NONCE]
    | some account => exact hfit address account hacc

end EthLib.Execution.State

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {tx : Transaction}

/-- A state that reads each account as a state within the bound is within the bound. -/
private theorem noncesFit_of_getAccountOptional {tx tx' : TransactionState}
    (h : ∀ address, tx'.getAccountOptional address = tx.getAccountOptional address)
    (hfit : tx.NoncesFit) : tx'.NoncesFit :=
  NoncesFit.of_nonceLe (NonceLe.of_getAccountOptional fun address => (h address).symm) hfit

section Meter

variable {Meter : Type} [GasMeter Meter]

/-- An authorization keeps every nonce within the bound, since it names a nonce below it. -/
private theorem noncesFit_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done')
    (hfit : done.state.NoncesFit) : done'.state.NoncesFit := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, hscope, -, ⟨-, rfl⟩ |
    ⟨haccept, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact hfit
  · exact hfit
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    obtain ⟨-, hself, hother⟩ := delegate_eq_ok hdelegate
    have hnonce : (done.state.getAccount authority).nonce = auth.nonce.toNat := by
      unfold authorityAccepts at haccept
      obtain ⟨code, -, haccept⟩ := bind_ok_iff.mp haccept
      simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at haccept
      exact haccept.2
    have hlt : auth.nonce.toNat < 2 ^ 64 - 1 := by
      simp only [authorizationInScope, Bool.and_eq_true, decide_eq_true_eq] at hscope
      exact hscope.2
    rw [hstate] at hself hother
    intro address
    by_cases hne : address = authority
    · subst hne
      rw [hself]
      simp only [State.TransactionState.getAccount_recordAccountRead, hnonce, MAX_NONCE]
      omega
    · unfold State.TransactionState.getAccount
      rw [hother address hne]
      exact hfit address

/-- Authorizations that succeed keep every nonce within the bound. -/
private theorem noncesFit_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      start.state.NoncesFit → done.state.NoncesFit
  | [], _, _, h, hfit => by
    cases h
    exact hfit
  | _ :: _, _, _, h, hfit => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact noncesFit_foldlM_applyAuthorization h (noncesFit_applyAuthorization hnext hfit)

/-- The first frame of a transaction keeps every nonce within the bound. -/
private theorem noncesFit_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first)
    (hfit : state.NoncesFit) : first.state.NoncesFit := by
  have reads := prepareFirstFrame_reads h
  split at reads
  · exact noncesFit_of_getAccountOptional
      (fun address => (reads.1 address List.not_mem_nil).1) hfit
  · obtain ⟨done, hdone, -, same, -⟩ := reads
    exact noncesFit_of_getAccountOptional
      (fun address => (same address List.not_mem_nil).1)
      (noncesFit_foldlM_applyAuthorization hdone hfit)

/-- The first frame of a creation runs at an address with nonce 0. -/
private theorem prepareFirstFrame_create_nonce {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first)
    (hnone : message.target = none) :
    (first.state.getAccount first.message.currentTarget).nonce = 0 := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hdeploy
      have hn := State.TransactionState.nonce_eq_zero_of_accountDeployable hdeploy
      split at h <;>
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact hn
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i t hsome
    rw [hsome] at hnone
    cases hnone

end Meter

/-- The message of a transaction keeps every nonce within the bound, with any lawful meter.

That holds whether or not the message ends with an error, or halts before its frame runs. -/
theorem noncesFit_processMessageCall {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (hfit : state.NoncesFit)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    output.state.NoncesFit := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      exact noncesFit_of_getAccountOptional
        (fun address => (State.TransactionState.sameOutside_withReadsOf state _ address
          List.not_mem_nil).1.symm) hfit
  rename_i first hfirst
  have fit := noncesFit_prepareFirstFrame hfirst hfit
  split at h
  · rename_i hnone
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    rw [state_ofFrame]
    refine noncesFit_processCreateMessage fit ?_ hrun
    rw [prepareFirstFrame_create_nonce hfirst hnone]
    decide
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    rw [state_ofFrame]
    exact noncesFit_processMessage fit hrun

/-- The removal of the empty touched accounts raises no nonce. -/
private theorem nonceLe_destroyTouchedEmptyAccounts (tx : TransactionState)
    (touched : List Address) : NonceLe (tx.destroyTouchedEmptyAccounts fork touched) tx := by
  unfold State.TransactionState.destroyTouchedEmptyAccounts
  split
  · exact NonceLe.refl _
  · induction touched generalizing tx with
    | nil => exact NonceLe.refl _
    | cons other rest ih =>
      rw [List.foldl_cons]
      refine (ih _).trans fun address => ?_
      split
      · rw [State.TransactionState.getAccount_destroyAccount]
        split
        · exact Nat.zero_le _
        · exact Nat.le_refl _
      · exact Nat.le_refl _

/-- The deletions at the end of a transaction raise no nonce. -/
private theorem nonceLe_deleteAccounts {state state' : TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') : NonceLe state' state := by
  have fold : ∀ (l : List Address) (init final : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      NonceLe final init := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact NonceLe.refl _
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      refine (ih mid final h).trans fun other => ?_
      split at hmid
      · by_cases hne : other = address
        · subst hne
          rw [State.TransactionState.getAccount_clearAccountPreservingBalance hmid]
          exact Nat.zero_le _
        · rw [State.TransactionState.getAccount_clearAccountPreservingBalance_of_ne hmid hne]
          exact Nat.le_refl _
      · cases hmid
        rw [State.TransactionState.getAccount_destroyAccount]
        split
        · exact Nat.zero_le _
        · exact Nat.le_refl _
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact (nonceLe_destroyTouchedEmptyAccounts _ _).trans (fold _ _ _ hdeleted)

/-- A run of a transaction with any lawful meter keeps every nonce within the bound.

The sender must start with a nonce below `2^64 - 1`. -/
private theorem noncesFit_runTransaction {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {out : TransactionOutput} (hfit : (TransactionState.ofBlock block).NoncesFit)
    (hsender : ((TransactionState.ofBlock block).getAccount included.sender).nonce < MAX_NONCE)
    (h : runTransaction Meter env block included tx = .ok out) : out.state.NoncesFit := by
  unfold runTransaction at h
  obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  have hbought := mapError_ok_iff.mp hbought
  obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, gasUsed⟩, hsettle, h⟩ := bind_ok_iff.mp h
  have hsettle := mapError_ok_iff.mp hsettle
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  have hdeleted := mapError_ok_iff.mp hdeleted
  cases h
  have fitBought : bought.NoncesFit := by
    intro address
    by_cases hs : address = included.sender
    · subst hs
      rw [(buyGas_sender rfl hbought).2.2]
      omega
    · unfold State.TransactionState.getAccount
      rw [(sameOutside_buyGas hbought address (by simpa using hs)).1]
      exact hfit address
  have fitOut := noncesFit_processMessageCall fitBought houtput
  have fitSettled : settled.NoncesFit := fun address => by
    rw [(settleGas_accounts hsettle address).2.1]
    exact fitOut address
  exact NoncesFit.of_nonceLe (nonceLe_deleteAccounts hdeleted) fitSettled

/-- A transaction that runs keeps every nonce within the bound.

The state of its block must be within the bound, and it must pass the inclusion check on it.

That holds whether or not its message ends with an error. -/
theorem noncesFit_processTransaction {env : BlockEnvironment fork} {block : State.BlockState}
    {chainId : UInt64} {used : BlockGas} {included : Included} {out : TransactionOutput}
    (hfit : (TransactionState.ofBlock block).NoncesFit)
    (hcheck : checkInclusion chainId env used (.ofBlock block) tx = .ok included)
    (h : processTransaction env block included tx = .ok out) :
    out.state.NoncesFit := by
  obtain ⟨hvalid, hnonce⟩ : validateTransaction fork included.sender tx =
      .ok included.intrinsicGas ∧
      tx.nonce.toNat = ((TransactionState.ofBlock block).getAccount included.sender).nonce := by
    obtain ⟨-, hv, -, -, -, -, -, -, hn, -⟩ := checkInclusion_ok hcheck
    exact ⟨hv, hn⟩
  have hsender : ((TransactionState.ofBlock block).getAccount included.sender).nonce <
      MAX_NONCE := by
    rw [← hnonce]
    exact (validateTransaction_ok hvalid).2.2.1
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  unfold processTransaction at h
  simp only [hhegota, ↓reduceIte] at h
  split at h
  · exact noncesFit_runTransaction hfit hsender h
  · exact noncesFit_runTransaction hfit hsender h

end EthLib.Execution.Transactions

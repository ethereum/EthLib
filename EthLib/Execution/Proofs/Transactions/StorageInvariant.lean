module

public import EthLib.Execution.Proofs.Evm.Call.Fresh
public import EthLib.Execution.Proofs.Evm.Call.StorageInvariant
public import EthLib.Execution.Proofs.Transactions.CodeRules
public import EthLib.Execution.Proofs.Transactions.Deletion

/-!
# Proofs: an invariant of the storage of a contract holds over every transaction

Take an account that holds a given code, and an invariant of its storage.

From Cancun, if each call that runs that code there keeps the invariant, so does every transaction.

From Hegotá no transaction runs, so the theorems say nothing there.

The proof assumes that no other code has the Keccak-256 hash of the given code.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (EMPTY_ACCOUNT EMPTY_CODE_HASH TransactionState)
open EthLib.Execution.State.TransactionState
open Cryptography.Hash.Keccak (keccak256)

variable {fork : Fork} {Meter : Type} [GasMeter Meter] {address : Address} {code : ByteArray}
  {Inv : (Bytes32 → U256) → Prop}

/-! ## The account of the contract -/

/-- A record of a read keeps the account that holds `code`. -/
theorem keepsAt_recordAccountRead (tx : TransactionState) (other : Address) :
    KeepsAt address code tx (tx.recordAccountRead other) :=
  .of_eq rfl (fun _ => rfl) rfl

/-- The deletion of another account keeps the account that holds `code`. -/
theorem keepsAt_destroyAccount {tx : TransactionState} {other : Address} (hne : address ≠ other) :
    KeepsAt address code tx (tx.destroyAccount other) :=
  .of_eq (by simp only [getAccount, destroyAccount, getAccountOptional_setAccount_of_ne _ _ hne,
      getAccountOptional_destroyStorage])
    (fun _ => rfl) (funext fun key => by rw [getStorage_destroyAccount, ite_eq_right hne])

/-! ## The steps around the message -/

/-- An authorization keeps the account that holds `code`, which refuses it. -/
theorem keepsAt_applyAuthorization (hyp : CodeHyp code) {chainId : Nat}
    {done done' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok done') :
    KeepsAt address code done.state done'.state := by
  intro hold
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨haccept, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact ⟨hold, rfl⟩
  · exact keepsAt_recordAccountRead _ _ hold
  · -- The account at `address` holds real code, so it refuses every authorization.
    have hne : address ≠ authority := by
      rintro rfl
      rw [authorityAccepts_of_code (by rw [hold.1]; exact hold.2) hyp.size_ne hyp.not_valid]
        at haccept
      cases haccept
    obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    obtain ⟨coded, hcode, hdelegate⟩ := bind_ok_iff.mp hdelegate
    obtain ⟨bumped, hnonce, hdelegate⟩ := bind_ok_iff.mp hdelegate
    cases hdelegate
    exact ((keepsAt_recordAccountRead _ _).trans
      ((keepsAt_setCode hyp hcode hne).trans (keepsAt_incrementNonce hyp hnonce))) hold

/-- Authorizations that succeed keep the account that holds `code`. -/
theorem keepsAt_foldlM_applyAuthorization (hyp : CodeHyp code) {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      KeepsAt address code start.state done.state
  | [], _, _, h => by
    cases h
    exact .refl _
  | _ :: _, _, _, h => by
    obtain ⟨next, hnext, h⟩ := bind_ok_iff.mp h
    exact (keepsAt_applyAuthorization hyp hnext).trans (keepsAt_foldlM_applyAuthorization hyp h)

/-- The first frame of a message keeps the account that holds `code`.

When the account holds `code` before it, the first frame runs `code` if it runs at `address`.

A call must run at its recipient, as the message of a transaction and a system call do. -/
theorem prepareFirstFrame_keepsAt (hyp : CodeHyp code) {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    KeepsAt address code state first.state ∧
      (HoldsCode address code state → RunsCode address code first.message) := by
  have hcur := (substate_prepareFirstFrame h).2.2.2
  have htgt := (substate_prepareFirstFrame h).2.2.1
  unfold prepareFirstFrame at h
  split at h
  · -- A creation runs at its new address, which holds no code.
    rename_i hnone
    dsimp only at h
    split at h
    · refine ⟨fun hold => ?_, fun hold hat => ?_⟩
      · split at h <;>
        · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
          cases h
          exact keepsAt_recordAccountRead _ _ hold
      · rename_i hdep
        rw [hcur] at hat
        subst hat
        rw [show (state.recordAccountRead message.currentTarget).accountDeployable
          message.currentTarget = state.accountDeployable message.currentTarget from rfl,
          hold.not_deployable hyp] at hdep
        cases hdep
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · rename_i target htarget
    dsimp only at h
    obtain ⟨done, hdone, h⟩ := bind_ok_iff.mp h
    have hauth : KeepsAt address code state done.state :=
      keepsAt_foldlM_applyAuthorization hyp hdone
    -- After the authorizations, the first frame only records reads.
    generalize hread : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = read0 at h
    have base : KeepsAt address code state read0 := by
      subst hread
      split
      · exact hauth.trans (keepsAt_recordAccountRead _ _)
      · exact hauth
    have base' : KeepsAt address code state (read0.recordAccountRead target) :=
      base.trans (keepsAt_recordAccountRead _ _)
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨c, hc, h⟩ := bind_ok_iff.mp h
      generalize hdel : (if fork ≥ .pectra then delegatedAddress c else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        refine ⟨base', fun hold hat => ?_⟩
        -- A call to `address` runs the code that the account holds.
        have hat' : target = address := (recipient target htarget).trans (hcur.symm.trans hat)
        subst hat'
        have hold' := (base' hold).1
        rw [hold'.1, hold'.2] at hc
        cases Base.mapError_ok_iff.mp hc
        exact ⟨rfl, by simp [FirstFrame.ofMeter, htarget]⟩
      · dsimp only at h
        refine ⟨fun hold => ?_, fun hold hat => ?_⟩
        · split at h <;>
          · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
            obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
            cases h
            exact (base'.trans (keepsAt_recordAccountRead _ _)) hold
        · -- A call to `address` finds no delegate, since its code names none.
          exfalso
          have hat' : target = address := (recipient target htarget).trans (hcur.symm.trans hat)
          subst hat'
          have hold' := (base' hold).1
          rw [hold'.1, hold'.2] at hc
          cases Base.mapError_ok_iff.mp hc
          rw [hyp.noDelegateAt] at hdel
          cases hdel

/-- The purchase of gas keeps the account that holds `code`. -/
theorem keepsAt_buyGas (hyp : CodeHyp code) {env : BlockEnvironment fork}
    {state bought : TransactionState} {sender : Address} {tx : Transaction}
    (h : buyGas env state sender tx = .ok bought) : KeepsAt address code state bought := by
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  refine (keepsAt_incrementNonce hyp h1).trans (keepsAt_modifyState hyp (fun _ _ hd => ?_) h2)
  split at hd
  · cases hd
    rfl
  · cases hd

/-- The settlement of gas keeps the account that holds `code`.

Before Paris, it may delete an empty beneficiary, and an account with code is not empty. -/
theorem keepsAt_settleGas (hyp : CodeHyp code) {env : BlockEnvironment fork}
    {state settled : TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter gasUsed : Nat}
    (h : settleGas env state sender tx gasLeft refundCounter = .ok (settled, gasUsed)) :
    KeepsAt address code state settled := by
  have credit : ∀ {s s' : TransactionState} {other : Address} {amount : Nat},
      creditEther fork s other amount = .ok s' → KeepsAt address code s s' := by
    intro s s' other amount hc
    unfold creditEther at hc
    split at hc
    · exact keepsAt_createEther hyp hc
    · cases hc
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := bind_ok_iff.mp h
  cases h
  refine (credit h1).trans ?_
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    intro hold
    split
    · rename_i hempty
      have hne : address ≠ env.coinbase := by
        rintro rfl
        rw [hold.not_empty hyp] at hempty
        cases hempty
      exact keepsAt_destroyAccount hne hold
    · exact ⟨hold, rfl⟩
  · exact credit h2

/-- The deletions at the end of a transaction keep every code. -/
theorem getCode_deleteAccounts {state state' : TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') (codeHash : Hash32) :
    state'.getCode codeHash = state.getCode codeHash := by
  have fold : ∀ (l : List Address) (init final : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      final.parent = init.parent := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      rfl
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      refine (ih mid final h).trans ?_
      split at hmid
      · dsimp only [clearAccountPreservingBalance] at hmid
        exact (State.TransactionState.parent_modifyState hmid).trans rfl
      · cases hmid
        rfl
  have destroy : ∀ (touched : List Address) (tx : TransactionState),
      (touched.foldl (fun tx address =>
        if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx)
        tx).parent = tx.parent := by
    intro touched
    induction touched with
    | nil => intro _; rfl
    | cons address rest ih =>
      intro tx
      refine (ih _).trans ?_
      dsimp only
      split <;> rfl
  have hparent : state'.parent = state.parent := by
    unfold deleteAccounts at h
    obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
    cases h
    rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
    refine Eq.trans ?_ (fold _ _ _ hdeleted)
    unfold destroyTouchedEmptyAccounts
    split
    · rfl
    · exact destroy _ _
  unfold getCode
  rw [codeWrites_deleteAccounts h, hparent]

/-! ## The message and the transaction -/

variable [LawfulGasMeter Meter]

/-- The message of a transaction keeps the invariant and the account at `address`.

Each call that runs `code` at `address` must keep them.

The transaction must not have created the account yet, and then it does not create it.

A call must run at its recipient, as the message of a transaction and a system call do. -/
theorem goodAt_processMessageCall (hyp : CodeHyp code)
    (frames : FramesKeepCode address code fork Meter Inv) {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (good : GoodAt address code Inv state) (fresh : address ∉ state.createdAccounts) :
    GoodAt address code Inv output.state ∧ address ∉ output.state.createdAccounts := by
  rw [processMessageCall_unfold] at h
  split at h
  · -- A halt before the first frame keeps the state, up to its reads.
    split at h
    · cases h
    · cases h
      exact ⟨good.of_keepsAt (.of_eq rfl (fun _ => rfl) rfl), fresh⟩
  · rename_i first hfirst
    obtain ⟨keeps, runs⟩ := prepareFirstFrame_keepsAt hyp recipient hfirst
    have good1 : GoodAt address code Inv first.state := good.of_keepsAt keeps
    -- The account holds code, so a message never creates it.
    have hcode1 : (first.state.getAccount address).codeHash ≠ EMPTY_CODE_HASH := by
      rw [good1.1.1]
      exact hyp.hash_ne
    have fresh1 : address ∉ first.state.createdAccounts := by
      rw [createdAccounts_prepareFirstFrame hfirst]
      exact fresh
    have runs1 := runs good.1
    split at h
    · -- A creation goes to an address without code.
      rename_i hnone
      obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      have hne : first.message.currentTarget ≠ address := fun hat =>
        absurd ((substate_prepareFirstFrame hfirst).2.2.1.trans hnone) (runs1 hat).2
      have fr := createsFresh_processCreateMessage hrun
      rw [state_ofFrame]
      refine ⟨goodAt_processCreateMessage hyp frames hrun good1 hne, fun mem => ?_⟩
      rcases fr.fresh address mem fresh1 with h0 | h0
      · exact hcode1 h0.2
      · exact hne h0.symm
    · obtain ⟨⟨evm, _⟩, hrun, h⟩ := bind_ok_iff.mp h
      cases h
      have fr := createsFresh_processMessage hrun
      rw [state_ofFrame]
      refine ⟨goodAt_processMessage hyp frames hrun good1 runs1, fun mem => ?_⟩
      rcases fr.fresh address mem fresh1 with h0 | h0
      · exact hcode1 h0.2
      · exact h0.elim

/-- From Cancun, a transaction keeps the invariant and the account at `address`.

Each call that runs `code` at `address` must keep them.

It runs with the gas meter `Meter`. -/
theorem goodAt_runTransaction (hyp : CodeHyp code)
    (frames : FramesKeepCode address code fork Meter Inv) (hfork : .dencun ≤ fork)
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out)
    (good : GoodAt address code Inv (.ofBlock block)) : GoodAt address code Inv out.state := by
  obtain ⟨target, bought, message, output, settled, htarget, hbought, hmessage, houtput, hsettle,
    hdelete, same⟩ := runTransaction_deletes_created hfork h
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
  have good1 := good.of_keepsAt (keepsAt_buyGas hyp hbought)
  -- A transaction starts with no created account, and the purchase of gas creates none.
  have fresh : address ∉ bought.createdAccounts := by
    obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp hbought
    rw [createdAccounts_modifyState h2, createdAccounts_modifyState h1]
    simp [TransactionState.ofBlock]
  obtain ⟨good2, fresh2⟩ := goodAt_processMessageCall hyp frames recipient houtput good1 fresh
  have good3 : GoodAt address code Inv settled := good2.of_keepsAt (keepsAt_settleGas hyp hsettle)
  -- From Cancun, the deletions change only accounts that the transaction created.
  have hout := same address (by
    rw [Std.ExtTreeSet.mem_toList, createdAccounts_settleGas hsettle]
    exact fresh2)
  have hacc : out.state.getAccount address = settled.getAccount address := by
    simp only [getAccount, hout.1]
  obtain ⟨⟨hhash, hcode⟩, hinv⟩ := good3
  refine ⟨⟨by rw [hacc]; exact hhash, (getCode_deleteAccounts hdelete _).trans hcode⟩, ?_⟩
  rw [show out.state.getStorage address = settled.getStorage address from funext hout.2.1]
  exact hinv

/-- From Cancun, a transaction keeps the invariant and the account at `address`.

Each call that runs `code` at `address` must keep them, with the gas meter of the fork. -/
theorem goodAt_processTransaction (hyp : CodeHyp code) (hfork : .dencun ≤ fork)
    (frames : fork < .glamsterdam → FramesKeepCode address code fork Nat Inv)
    (framesState : .glamsterdam ≤ fork → FramesKeepCode address code fork StateGasMeter Inv)
    {env : BlockEnvironment fork} {block : State.BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (h : processTransaction env block included tx = .ok out)
    (good : GoodAt address code Inv (.ofBlock block)) : GoodAt address code Inv out.state := by
  by_cases hhegota : .hegota ≤ fork
  · rw [processTransaction_of_hegota_le hhegota] at h
    cases h
  by_cases hglam : .glamsterdam ≤ fork
  · rw [processTransaction_of_glamsterdam hglam (Nat.lt_of_not_le hhegota)] at h
    exact goodAt_runTransaction hyp (framesState hglam) hfork h good
  · rw [processTransaction_of_lt_glamsterdam (Nat.lt_of_not_le hglam)] at h
    exact goodAt_runTransaction hyp (frames (Nat.lt_of_not_le hglam)) hfork h good

end EthLib.Execution.Transactions

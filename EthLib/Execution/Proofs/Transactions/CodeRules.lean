module

public import EthLib.Execution.Proofs.Evm.Call.CodeRules
public import EthLib.Execution.Proofs.Evm.Call.Delegation
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Process
public import EthLib.Execution.Proofs.Transactions.Replay
public import EthLib.Execution.Proofs.Transactions.Unfold

/-!
# Proofs: a transaction writes only code that meets the rules of its fork

A transaction writes code in two ways, through its message and through its authorizations.

From Pectra, its authorizations write delegation indicators of [EIP-7702][eip7702].

[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork Hash32)
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState TransactionState)

/-- A code that a transaction may write at `fork`.

It meets the rules of a deployed code, or from Pectra it is a delegation indicator. -/
def TxCodeRules (fork : Fork) (code : ByteArray) : Prop :=
  CodeRules fork code ∨ (.pectra ≤ fork ∧ isValidDelegation code = true)

section

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The authorizations -/

/-- From Pectra, the code that an authorization writes may be written by a transaction.

The empty code meets the rules, and a delegation indicator is valid. -/
private theorem txCodeRules_delegationCode (hp : .pectra ≤ fork) (auth : Authorization) :
    TxCodeRules fork (delegationCode auth) := by
  unfold delegationCode
  split
  -- A delegation to the null address writes the empty code, which meets the rules.
  · exact .inl ⟨fun _ _ => by simp, fun _ => by simp⟩
  · exact .inr ⟨hp, isValidDelegation_delegationIndicator _⟩

/-- From Pectra, an authorization that sets the code of its authority keeps the rules. -/
private theorem keepsCodeRules_delegate (hp : .pectra ≤ fork) {state state' : TransactionState}
    {authority : Address} {auth : Authorization} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    KeepsCodeRules (TxCodeRules fork) state state' := by
  obtain ⟨coded, hcode, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact (KeepsCodeRules.setCode (txCodeRules_delegationCode hp auth) hcode).trans
    (.of_codeWrites (codeWrites_modifyState hnonce))

/-- From Pectra, one authorization keeps the rules. -/
private theorem keepsCodeRules_applyAuthorization (hp : .pectra ≤ fork) {chainId : Nat}
    {done done' : Delegations Meter} {auth : Authorization}
    (h : applyAuthorization fork chainId done auth = .ok done') :
    KeepsCodeRules (TxCodeRules fork) done.state done'.state := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · exact .refl _
  · exact .of_codeWrites rfl
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    rw [hstate] at hdelegate
    exact (KeepsCodeRules.of_codeWrites (tx := done.state)
      (tx' := done.state.recordAccountRead authority) rfl).trans
      (keepsCodeRules_delegate hp hdelegate)

/-- A list of authorizations keeps the rules, when it is empty or the fork is Pectra or later. -/
private theorem keepsCodeRules_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      (auths = [] ∨ .pectra ≤ fork) →
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      KeepsCodeRules (TxCodeRules fork) start.state done.state
  | [], _, _, _, h => by
    cases h
    exact .refl _
  | _ :: _, _, _, hp, h => by
    -- A list that is not empty needs Pectra.
    have hp : .pectra ≤ fork := hp.resolve_left nofun
    obtain ⟨next, hnext, h⟩ := Base.bind_ok_iff.mp h
    exact (keepsCodeRules_applyAuthorization hp hnext).trans
      (keepsCodeRules_foldlM_applyAuthorization (.inr hp) h)

/-! ## The message -/

/-- Preparing the first frame of a message keeps the rules. -/
private theorem keepsCodeRules_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (hauth : auths = [] ∨ .pectra ≤ fork)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    KeepsCodeRules (TxCodeRules fork) state first.state := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · have hfin : first.state = state.recordAccountRead message.currentTarget := by
        split at h <;>
        · obtain ⟨m, -, h⟩ := Base.bind_ok_iff.mp h
          cases h
          rfl
      rw [hfin]
      exact .of_codeWrites rfl
    · obtain ⟨m, h, -⟩ := Base.bind_ok_iff.mp h
      cases h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := Base.bind_ok_iff.mp h
    have vdone : KeepsCodeRules (TxCodeRules fork) state done.state :=
      keepsCodeRules_foldlM_applyAuthorization hauth hdone
    dsimp only at h
    -- Every later step only records reads, which keep the written codes.
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have v1 : KeepsCodeRules (TxCodeRules fork) state s1 := by
      rw [← hs1]
      split
      · exact vdone.trans (.of_codeWrites rfl)
      · exact vdone
    have v2 : KeepsCodeRules (TxCodeRules fork) state (s1.recordAccountRead target) :=
      v1.trans (.of_codeWrites rfl)
    split at h
    all_goals
      obtain ⟨m, -, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact v2
      · dsimp only at h
        split at h
        all_goals
          obtain ⟨m', -, h⟩ := Base.bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := Base.bind_ok_iff.mp h
          cases h
          exact v2.trans (.of_codeWrites rfl)

/-- The message of a transaction keeps the rules.

It deploys code, which meets the rules of a deployed code at its fork. -/
theorem keepsCodeRules_processMessageCall [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (hauth : auths = [] ∨ .pectra ≤ fork)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    KeepsCodeRules (TxCodeRules fork) state output.state := by
  have hmono : ∀ code, CodeRules fork code → TxCodeRules fork code := fun _ => .inl
  rw [processMessageCall_unfold] at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact .of_codeWrites rfl
  · rw [hprep] at h
    dsimp only at h
    have vfirst := keepsCodeRules_prepareFirstFrame hauth hprep
    have hframe : ∀ {evm : Evm fork Meter} {r : Nat} {t : Std.ExtTreeSet Address},
        (CallOutput.ofFrame evm r t).state = evm.state := by
      intro evm r t
      unfold CallOutput.ofFrame
      dsimp only
      split <;> rfl
    split at h
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact vfirst.trans ((keepsCodeRules_processCreateMessage hrun).mono hmono)
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact vfirst.trans ((keepsCodeRules_processMessage hrun).mono hmono)

/-! ## The transaction -/

/-- Buying gas keeps the written codes, since it raises a nonce and takes a fee. -/
theorem codeWrites_buyGas {env : BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {lifted : LiftedRules} (h : buyGas env state sender tx lifted = .ok state') :
    state'.codeWrites = state.codeWrites := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (codeWrites_modifyState h2).trans (codeWrites_modifyState h1)

/-- A credit of ether keeps the written codes. -/
theorem codeWrites_creditEther {tx tx' : TransactionState} {address : Address}
    {amount : Nat} (h : creditEther fork tx address amount = .ok tx') :
    tx'.codeWrites = tx.codeWrites := by
  unfold creditEther at h
  split at h
  · exact codeWrites_modifyState h
  · cases h

/-- Settling gas keeps the written codes. -/
theorem codeWrites_settleGas {env : BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter used : Nat} {lifted : LiftedRules}
    (h : settleGas env state sender tx gasLeft refundCounter lifted = .ok (state', used)) :
    state'.codeWrites = state.codeWrites := by
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  refine Eq.trans ?_ (codeWrites_creditEther h1)
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split <;> rfl
  · exact codeWrites_creditEther h2

/-- The deletion of empty touched accounts keeps the written codes. -/
theorem codeWrites_foldl_destroy :
    ∀ (touched : List Address) (tx : TransactionState),
      (touched.foldl (fun tx address =>
        if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx)
        tx).codeWrites = tx.codeWrites
  | [], _ => rfl
  | address :: rest, tx => by
    refine (codeWrites_foldl_destroy rest _).trans ?_
    dsimp only
    split <;> rfl

/-- The deletions at the end of a transaction keep the written codes. -/
theorem codeWrites_deleteAccounts {state state' : TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') :
    state'.codeWrites = state.codeWrites := by
  have fold : ∀ (l : List Address) (init final : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      final.codeWrites = init.codeWrites := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      rfl
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
      refine (ih mid final h).trans ?_
      split at hmid
      · dsimp only [TransactionState.clearAccountPreservingBalance] at hmid
        have hw := codeWrites_modifyState hmid
        exact hw
      · cases hmid
        rfl
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  refine Eq.trans ?_ (fold _ _ _ hdeleted)
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · rfl
  · exact codeWrites_foldl_destroy _ _

/-- A run of a transaction keeps the rules from the state of its block. -/
private theorem keepsCodeRules_runTransaction [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {block : BlockState} {included : Included} {tx : Transaction}
    {precompiles : Address → Option Address} {lifted : LiftedRules}
    {output : TransactionOutput} (hauth : tx.authorizations = [] ∨ .pectra ≤ fork)
    (h : runTransaction Meter env block included tx precompiles lifted = .ok output) :
    KeepsCodeRules (TxCodeRules fork) (TransactionState.ofBlock block) output.state := by
  rw [runTransaction_unfold] at h
  obtain ⟨target, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨bought, hBought, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨message, -, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨out, hOutput, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hSettle, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨deleted, hDeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  -- Only the message writes code: the purchase, settlement and deletions keep the writes.
  --
  -- They change balances, nonces and accounts, and write no code.
  have hbuy := codeWrites_buyGas (Base.mapError_ok_iff.mp hBought)
  have hend := (codeWrites_deleteAccounts (Base.mapError_ok_iff.mp hDeleted)).trans
    (codeWrites_settleGas (Base.mapError_ok_iff.mp hSettle))
  exact (KeepsCodeRules.of_codeWrites hbuy).trans
    ((keepsCodeRules_processMessageCall hauth hOutput).trans (.of_codeWrites hend))

end

/-- Each code that a transaction writes at a fork meets the rules of that fork.

From Pectra, it may also be a delegation indicator.

The type of the transaction must exist at that fork, as the block checks. -/
theorem codeRules_processTransaction {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction}
    {precompiles : Address → Option Address} {lifted : LiftedRules}
    {output : TransactionOutput} (hfork : tx.fork ≤ fork)
    (h : processTransaction env block included tx precompiles lifted = .ok output) :
    ∀ (codeHash : Hash32) (code : ByteArray), output.state.codeWrites[codeHash]? = some code →
      TxCodeRules fork code := by
  -- Before Pectra, the transaction holds no authorization.
  have hauth : tx.authorizations = [] ∨ .pectra ≤ fork := by
    by_cases hp : .pectra ≤ fork
    · exact .inr hp
    · exact .inl (authorizations_eq_nil hfork (Nat.lt_of_not_le hp))
  have keeps : KeepsCodeRules (TxCodeRules fork) (TransactionState.ofBlock block)
      output.state := by
    rw [processTransaction_unfold] at h
    split at h
    · cases h
    split at h
    · exact keepsCodeRules_runTransaction hauth h
    · exact keepsCodeRules_runTransaction hauth h
  -- A transaction starts with no written code.
  intro codeHash code hc
  rcases keeps codeHash code hc with hb | hp
  · simp [TransactionState.ofBlock] at hb
  · exact hp

end EthLib.Execution.Transactions

module

public import EthLib.Execution.Proofs.Evm.Call.Codes
public import EthLib.Execution.Proofs.Transactions.Authorization
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: a transaction keeps the code of each account available

A block holds its codes when the code of each of its accounts is in it.

A transaction then keeps the code of each account available, from its block to its end.

Its authorizations store each delegation under the hash that the account receives.

Its message keeps the codes.

The purchase of gas raises a nonce and takes a fee, and the refunds change only balances.

Deletions leave the empty code.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork)
open EthLib.Execution.Evm
open EthLib.Execution.State (Account BlockState StateError TransactionState)

/-- Whether the state holds the code of every account, now and before the transaction. -/
private def AllCodes (state : TransactionState) : Prop :=
  HasCodes state ∧ HasPreCodes state

/-- A change that keeps the accounts, the codes and the block keeps every code. -/
private theorem AllCodes.of_same {state state' : TransactionState}
    (code : ∀ hash, state'.getCode hash = state.getCode hash)
    (account : ∀ address, state'.getAccount address = state.getAccount address)
    (parent : state'.parent = state.parent) (available : AllCodes state) : AllCodes state' :=
  ⟨hasCodes_of_getCode code (fun address => .inl (by rw [account])) available.1,
    hasPreCodes_of_getCode code parent available.2⟩

/-- A record of a read keeps every code. -/
private theorem AllCodes.recordAccountRead {state : TransactionState} (address : Address)
    (available : AllCodes state) : AllCodes (state.recordAccountRead address) :=
  .of_same (state := state) (fun _ => rfl) (fun _ => rfl) rfl available

/-- A change of one account that keeps its code hash keeps every code. -/
private theorem AllCodes.modifyState {fork : Fork} {state state' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (hf : ∀ account, f (state.getAccount address) = .ok account →
      account.codeHash = (state.getAccount address).codeHash)
    (h : state.modifyState fork address f = .ok state') (available : AllCodes state) :
    AllCodes state' :=
  ⟨hasCodes_modifyState h available.1 fun account hacc => .inl (hf account hacc),
    hasPreCodes_modifyState h available.2⟩

/-- A deletion of an account keeps every code. -/
private theorem AllCodes.destroyAccount {state : TransactionState} (address : Address)
    (available : AllCodes state) : AllCodes (state.destroyAccount address) :=
  ⟨hasCodes_destroyAccount address available.1, hasPreCodes_destroyAccount address available.2⟩

/-- A transaction starts with every code before it, when its block holds every code. -/
private theorem allCodes_ofBlock {block : BlockState}
    (available : HasCodes (TransactionState.ofBlock block)) :
    AllCodes (TransactionState.ofBlock block) := by
  refine ⟨available, fun address => ?_⟩
  have account : (TransactionState.ofBlock block).getPreStateAccount address =
      (TransactionState.ofBlock block).getAccount address := by
    simp only [TransactionState.ofBlock, TransactionState.getPreStateAccount,
      TransactionState.getPreStateAccountOptional, TransactionState.getAccount,
      TransactionState.getAccountOptional, Std.ExtTreeMap.getElem?_empty]
  rw [account]
  exact available address

section

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The authorizations -/

/-- One authorization keeps every code. -/
private theorem allCodes_applyAuthorization {chainId : Nat} {done done' : Delegations Meter}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done')
    (available : AllCodes done.state) : AllCodes done'.state :=
  ⟨hasCodes_applyAuthorization h available.1, hasPreCodes_applyAuthorization h available.2⟩

/-- A list of authorizations keeps every code. -/
private theorem allCodes_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Meter},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      AllCodes start.state → AllCodes done.state
  | [], _, _, h, available => by
    cases h
    exact available
  | _ :: _, _, _, h, available => by
    obtain ⟨next, hnext, h⟩ := Base.bind_ok_iff.mp h
    exact allCodes_foldlM_applyAuthorization h (allCodes_applyAuthorization hnext available)

/-! ## The message -/

/-- Preparing the first frame of a message keeps every code. -/
private theorem allCodes_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter} (available : AllCodes state)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    AllCodes first.state := by
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
      exact available.recordAccountRead _
    · obtain ⟨m, h, -⟩ := Base.bind_ok_iff.mp h
      cases h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := Base.bind_ok_iff.mp h
    have vdone := allCodes_foldlM_applyAuthorization hdone available
    dsimp only at h
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have v1 : AllCodes s1 := by
      rw [← hs1]
      split
      · exact vdone.recordAccountRead _
      · exact vdone
    have v2 : AllCodes (s1.recordAccountRead target) := v1.recordAccountRead _
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
          exact v2.recordAccountRead _

/-- The message of a transaction keeps every code. -/
private theorem allCodes_processMessageCall [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (available : AllCodes state)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    AllCodes output.state := by
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact .of_same (state := state) (fun _ => rfl) (fun _ => rfl) rfl available
  · rw [hprep] at h
    dsimp only at h
    have vfirst := allCodes_prepareFirstFrame available hprep
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
      exact ⟨hasCodes_processCreateMessage hrun vfirst.1,
        hasPreCodes_processCreateMessage hrun vfirst.2⟩
    · obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      rw [hframe]
      exact ⟨hasCodes_processMessage hrun vfirst.1, hasPreCodes_processMessage hrun vfirst.2⟩

/-! ## The transaction -/

/-- Buying gas keeps every code, since it raises a nonce and takes a fee. -/
private theorem allCodes_buyGas {env : BlockEnvironment fork} {state state' : TransactionState}
    {sender : Address} {tx : Transaction} (available : AllCodes state)
    (h : buyGas env state sender tx = .ok state') : AllCodes state' := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  have vmid : AllCodes mid := available.modifyState (fun _ hf => by cases hf; rfl) h1
  refine vmid.modifyState (fun updated hupd => ?_) h2
  split at hupd
  · cases hupd
    rfl
  · cases hupd

/-- A credit of ether keeps every code. -/
private theorem allCodes_creditEther {tx tx' : TransactionState} {address : Address}
    {amount : Nat} (available : AllCodes tx) (h : creditEther fork tx address amount = .ok tx') :
    AllCodes tx' := by
  unfold creditEther at h
  split at h
  · refine available.modifyState (fun updated hupd => ?_) h
    unfold Account.credit at hupd
    split at hupd <;> cases hupd
    rfl
  · cases h

/-- Settling gas keeps every code. -/
private theorem allCodes_settleGas {env : BlockEnvironment fork}
    {state state' : TransactionState} {sender : Address} {tx : Transaction}
    {gasLeft refundCounter used : Nat} (available : AllCodes state)
    (h : settleGas env state sender tx gasLeft refundCounter = .ok (state', used)) :
    AllCodes state' := by
  unfold settleGas at h
  obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨paid, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have vmid := allCodes_creditEther available h1
  unfold payBeneficiary at h2
  split at h2
  · cases h2
    split
    · exact vmid.destroyAccount _
    · exact vmid
  · exact allCodes_creditEther vmid h2

/-- The deletion of empty touched accounts keeps every code. -/
private theorem allCodes_foldl_destroy :
    ∀ (touched : List Address) {tx : TransactionState}, AllCodes tx →
      AllCodes (touched.foldl (fun tx address =>
        if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx) tx)
  | [], _, available => available
  | address :: rest, tx, available => by
    refine allCodes_foldl_destroy rest ?_
    dsimp only
    split
    · exact available.destroyAccount address
    · exact available

/-- The deletions at the end of a transaction keep every code. -/
private theorem allCodes_deleteAccounts {state state' : TransactionState} {output : CallOutput}
    (available : AllCodes state) (h : deleteAccounts fork state output = .ok state') :
    AllCodes state' := by
  have fold : ∀ (l : List Address) (init final : TransactionState), AllCodes init →
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      AllCodes final := by
    intro l
    induction l with
    | nil =>
      intro init final hinit h
      cases h
      exact hinit
    | cons address rest ih =>
      intro init final hinit h
      obtain ⟨mid, hmid, h⟩ := Base.bind_ok_iff.mp h
      refine ih mid final ?_ h
      split at hmid
      · exact ⟨hasCodes_clearAccountPreservingBalance hmid hinit.1,
          hasPreCodes_modifyState hmid (hasPreCodes_destroyStorage address hinit.2)⟩
      · cases hmid
        exact hinit.destroyAccount address
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  have vdel := fold _ _ _ available hdeleted
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact vdel
  · exact allCodes_foldl_destroy _ vdel

/-- A run of a transaction keeps every code, when its block holds every code. -/
private theorem allCodes_runTransaction [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {output : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok output)
    (available : HasCodes (TransactionState.ofBlock block)) : AllCodes output.state := by
  obtain ⟨target, bought, message, out, settled, -, hBought, -, hOutput, -,
    hSettle, hDeleted⟩ := runTransaction_eq_ok h
  have vb := allCodes_buyGas (allCodes_ofBlock available) hBought
  have vout := allCodes_processMessageCall vb hOutput
  exact allCodes_deleteAccounts (allCodes_settleGas vout hSettle) hDeleted

end

/-- A transaction keeps the code of each account available when its block holds every code.

That holds for the accounts at its end and for those before it. -/
theorem processTransaction_hasCodes {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {output : TransactionOutput}
    (h : processTransaction env block included tx = .ok output)
    (available : HasCodes (TransactionState.ofBlock block)) :
    HasCodes output.state ∧ HasPreCodes output.state := by
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · exact allCodes_runTransaction h available
  · exact allCodes_runTransaction h available

end EthLib.Execution.Transactions

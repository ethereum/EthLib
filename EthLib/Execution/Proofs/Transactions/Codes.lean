module

public import EthLib.Execution.Proofs.Evm.Call.MissingCode
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

Every lookup of code then succeeds, so such a transaction never aborts for a missing code.

The same holds for a call that runs on a block outside any transaction.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork Hash32)
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

/-! ## No missing code -/

/-- The result is not a failure for a missing code. -/
private def NoMiss {α : Type} (r : Except EvmError α) : Prop :=
  ∀ c, r ≠ .error (.state (.missingCode c))

/-- The result is not a failure for a missing code, whatever state comes with the error. -/
private def NoMissRead {α : Type} (r : Except (EvmError × TransactionState) α) : Prop :=
  ∀ c read, r ≠ .error (.state (.missingCode c), read)

/-- A failure after a change of error comes from a failure before it. -/
private theorem mapError_eq_error {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {e : ε'}
    (h : x.mapError f = .error e) : ∃ e', x = .error e' ∧ f e' = e := by
  cases x with
  | error e' => exact ⟨e', rfl, by cases h; rfl⟩
  | ok a => cases h

/-- The charge of an authorization on a state that holds every code has no missing code. -/
private theorem noMiss_chargeAuthorization [LawfulGasMeter Meter] {done : Delegations Meter}
    {authority : Address} {auth : Authorization} (available : HasPreCodes done.state) :
    NoMiss (chargeAuthorization done authority auth) := by
  intro c h
  obtain ⟨code, hcode⟩ := available authority
  unfold chargeAuthorization at h
  simp only [hcode] at h
  repeat' first
    | (rcases Base.bind_eq_error h with h | ⟨_, -, h⟩)
    | split at h
  all_goals first
    | cases h
    | cases LawfulGasMeter.charge_error h
    | cases LawfulGasMeter.chargeState_error h

/-- The payment of an authorization on a state that holds every code has no missing code. -/
private theorem noMiss_payAuthorization [LawfulGasMeter Meter] {done : Delegations Meter}
    {authority : Address} {auth : Authorization} (available : AllCodes done.state) :
    NoMiss (payAuthorization fork done authority auth) := by
  intro c h
  unfold payAuthorization at h
  split at h
  · rcases Base.bind_eq_error h with h | ⟨a, -, h⟩
    · exact noMiss_chargeAuthorization available.2 c h
    · cases h
  · cases h

/-- One authorization on a state that holds every code never fails for a missing code. -/
private theorem noMissRead_applyAuthorization [LawfulGasMeter Meter] {chainId : Nat}
    {done : Delegations Meter} {auth : Authorization} (available : AllCodes done.state) :
    NoMissRead (applyAuthorization fork chainId done auth) := by
  intro c read h
  unfold applyAuthorization at h
  split at h
  · split at h
    · rename_i authority _
      have v := available.recordAccountRead authority
      obtain ⟨code, hcode⟩ := v.1 authority
      dsimp only at h
      generalize hA : authorityAccepts (done.state.recordAccountRead authority) authority auth
        = A at h
      rcases A with e | b
      · unfold authorityAccepts at hA
        dsimp only at hA
        rw [hcode] at hA
        cases hA
      · rcases Base.bind_eq_error h with h | ⟨b', -, h⟩
        · cases h
        split at h
        · rcases Base.bind_eq_error h with h | ⟨d, -, h⟩
          · obtain ⟨e, he, hee⟩ := mapError_eq_error h
            cases hee
            refine noMiss_payAuthorization ?_ c he
            exact v
          · rcases Base.bind_eq_error h with h | ⟨⟨s, r⟩, -, h⟩
            · obtain ⟨e, he, hee⟩ := mapError_eq_error h
              cases hee
              unfold delegate at he
              rcases Base.bind_eq_error he with he | ⟨s1, -, he⟩
              · unfold TransactionState.setCode at he
                exact modifyState_ne_missingCode (fun _ _ h => by cases h) c he
              · rcases Base.bind_eq_error he with he | ⟨s2, -, he⟩
                · exact modifyState_ne_missingCode (fun _ _ h => by cases h) c he
                · cases he
            · cases h
        · cases h
    · cases h
  · cases h

/-- A list of authorizations on a state that holds every code never fails for a missing code. -/
private theorem noMissRead_foldlM_applyAuthorization [LawfulGasMeter Meter] {chainId : Nat} :
    ∀ {auths : List Authorization} {start : Delegations Meter}, AllCodes start.state →
      NoMissRead (auths.foldlM (applyAuthorization fork chainId) start)
  | [], _, _ => fun _ _ h => by cases h
  | _ :: _, _, available => by
    intro c read h
    rcases Base.bind_eq_error h with h | ⟨next, hnext, h⟩
    · exact noMissRead_applyAuthorization available c read h
    · exact noMissRead_foldlM_applyAuthorization (allCodes_applyAuthorization hnext available) c
        read h

/-- The first frame of a message on a state that holds every code has no missing code. -/
private theorem noMissRead_prepareFirstFrame [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (available : AllCodes state) :
    NoMissRead (prepareFirstFrame (Meter := Meter) chainId message state substate auths paid) := by
  intro c read h
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
        · obtain ⟨e, he, hee⟩ := mapError_eq_error h
          cases hee
          cases LawfulGasMeter.chargeState_error he
        · cases h
      · cases h
    · cases h
  · rename_i target _
    dsimp only at h
    rcases Base.bind_eq_error h with h | ⟨done, hdone, h⟩
    · exact noMissRead_foldlM_applyAuthorization available c read h
    have vdone := allCodes_foldlM_applyAuthorization hdone available
    generalize hs1 : (if message.value ≠ 0 then done.state.recordAccountRead target
      else done.state) = s1 at h
    have v1 : AllCodes s1 := by
      rw [← hs1]
      split
      · exact vdone.recordAccountRead _
      · exact vdone
    have v2 : AllCodes (s1.recordAccountRead target) := v1.recordAccountRead _
    obtain ⟨code, hcode⟩ := v2.1 target
    split at h
    all_goals
      rcases Base.bind_eq_error h with h | ⟨m, -, h⟩
      · first
          | cases h
          | (obtain ⟨e, he, hee⟩ := mapError_eq_error h
             cases hee
             cases LawfulGasMeter.chargeState_error he)
      try dsimp only at h
      rcases Base.bind_eq_error h with h | ⟨code', -, h⟩
      · rw [hcode] at h
        cases h
      generalize (if fork ≥ .pectra then delegatedAddress code' else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
      · obtain ⟨code'', hcode''⟩ := (v2.recordAccountRead delegate).1 delegate
        dsimp only at h
        split at h
        all_goals
          rcases Base.bind_eq_error h with h | ⟨m', -, h⟩
          · first
              | cases h
              | (obtain ⟨e, he, hee⟩ := mapError_eq_error h
                 cases hee
                 cases LawfulGasMeter.charge_error he)
          try dsimp only at h
          rcases Base.bind_eq_error h with h | ⟨code''', -, h⟩
          · rw [hcode''] at h
            cases h
          · cases h

/-- The message of a transaction on a state that holds every code has no missing code. -/
private theorem noMiss_processMessageCall [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} (available : AllCodes state) :
    NoMiss (processMessageCall (Meter := Meter) chainId message state substate auths paid) := by
  intro c h
  unfold processMessageCall at h
  rcases hprep : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hprep] at h
    dsimp only at h
    split at h
    · cases h
      exact noMissRead_prepareFirstFrame available c read hprep
    · cases h
  · rw [hprep] at h
    dsimp only at h
    have vfirst := allCodes_prepareFirstFrame available hprep
    split at h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processCreateMessage_ne_missingCode vfirst.1 c h
      · cases h
    · rcases Base.bind_eq_error h with h | ⟨_, -, h⟩
      · exact processMessage_ne_missingCode vfirst.1 c h
      · cases h

/-- A credit of ether never fails for a missing code. -/
private theorem creditEther_ne_missingCode (tx : TransactionState) (address : Address)
    (amount : Nat) (c : Hash32) : creditEther fork tx address amount ≠ .error (.missingCode c) := by
  unfold creditEther
  split
  · exact modifyState_ne_missingCode
      (fun _ _ h => by unfold Account.credit at h; split at h <;> cases h) c
  · nofun

/-- The deletions at the end of a transaction never fail for a missing code. -/
private theorem deleteAccounts_ne_missingCode (state : TransactionState) (output : CallOutput)
    (c : Hash32) : deleteAccounts fork state output ≠ .error (.missingCode c) := by
  have fold : ∀ (l : List Address) (init : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init ≠ .error (.missingCode c) := by
    intro l
    induction l with
    | nil => exact fun _ h => by cases h
    | cons address rest ih =>
      intro init h
      rcases Base.bind_eq_error h with h | ⟨mid, -, h⟩
      · split at h
        · exact modifyState_ne_missingCode (fun _ _ h => by cases h) c h
        · cases h
      · exact ih mid h
  intro h
  unfold deleteAccounts at h
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at h
    exact fold _ _ h
  · cases h

/-- A run of a transaction never aborts for a missing code, when its block holds every code. -/
private theorem noMiss_runTransaction [LawfulGasMeter Meter] {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction}
    (available : HasCodes (TransactionState.ofBlock block)) :
    NoMiss (runTransaction Meter env block included tx) := by
  intro c h
  unfold runTransaction at h
  rcases Base.bind_eq_error h with h | ⟨target, -, h⟩
  · unfold messageTarget at h
    split at h
    · cases h
    · obtain ⟨e, -, he⟩ := mapError_eq_error h
      cases he
  rcases Base.bind_eq_error h with h | ⟨bought, hBought, h⟩
  · obtain ⟨e, he, hee⟩ := mapError_eq_error h
    cases hee
    unfold buyGas at he
    rcases Base.bind_eq_error he with he | ⟨mid, -, he⟩
    · exact modifyState_ne_missingCode (fun _ _ h => by cases h) c he
    · exact modifyState_ne_missingCode (fun _ _ h => by split at h <;> cases h) c he
  have vb := allCodes_buyGas (allCodes_ofBlock available) (Base.mapError_ok_iff.mp hBought)
  dsimp only at h
  rcases Base.bind_eq_error h with h | ⟨message, -, h⟩
  · unfold transactionMessage at h
    split at h
    · rename_i to _
      obtain ⟨code, hcode⟩ := vb.1 to
      rw [hcode] at h
      cases h
    · cases h
  rcases Base.bind_eq_error h with h | ⟨output, hOutput, h⟩
  · exact noMiss_processMessageCall vb c h
  rcases Base.bind_eq_error h with h | ⟨⟨settled, used⟩, -, h⟩
  · obtain ⟨e, he, hee⟩ := mapError_eq_error h
    cases hee
    unfold settleGas at he
    rcases Base.bind_eq_error he with he | ⟨mid, -, he⟩
    · exact creditEther_ne_missingCode _ _ _ c he
    rcases Base.bind_eq_error he with he | ⟨paid, -, he⟩
    · unfold payBeneficiary at he
      split at he
      · cases he
      · exact creditEther_ne_missingCode _ _ _ c he
    · cases he
  rcases Base.bind_eq_error h with h | ⟨deleted, -, h⟩
  · obtain ⟨e, he, hee⟩ := mapError_eq_error h
    cases hee
    exact deleteAccounts_ne_missingCode _ _ c he
  · cases h

/-- A call on a block that holds every code keeps the code of each account available. -/
theorem processMessageCall_hasCodes [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {block : BlockState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (available : HasCodes (TransactionState.ofBlock block))
    (h : processMessageCall (Meter := Meter) chainId message (.ofBlock block) substate auths
      paid = .ok output) :
    HasCodes output.state :=
  (allCodes_processMessageCall (allCodes_ofBlock available) h).1

/-- A call on a block that holds every code never aborts for a missing code. -/
theorem processMessageCall_ne_missingCode [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {block : BlockState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    (available : HasCodes (TransactionState.ofBlock block)) (codeHash : Hash32) :
    processMessageCall (Meter := Meter) chainId message (.ofBlock block) substate auths paid ≠
      .error (.state (.missingCode codeHash)) :=
  noMiss_processMessageCall (allCodes_ofBlock available) codeHash

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

/-- A transaction never aborts for a missing code when its block holds the code of every account.

Each lookup of code reads an account of a state that holds every code, now and before it. -/
theorem processTransaction_ne_missingCode {fork : Fork} {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction}
    (available : HasCodes (TransactionState.ofBlock block)) (codeHash : Hash32) :
    processTransaction env block included tx ≠ .error (.state (.missingCode codeHash)) := by
  unfold processTransaction
  split
  · nofun
  split
  · exact noMiss_runTransaction available codeHash
  · exact noMiss_runTransaction available codeHash

end EthLib.Execution.Transactions

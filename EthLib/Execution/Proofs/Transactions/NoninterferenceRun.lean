module

public import EthLib.Execution.Proofs.Evm.Call.CreatedRead
public import EthLib.Execution.Proofs.Evm.Call.ToDelete
public import EthLib.Execution.Proofs.Evm.Call.Touched
public import EthLib.Execution.Proofs.State.CodeAvailability
public import EthLib.Execution.Proofs.Transactions.Noninterference

/-!
# Proofs: a transaction depends only on what it records

Run the same transaction on two block states that agree on four sets.

The sets name accounts, whole storages, slots and code hashes.

When the first run ends with its reads in the sets, the second gives the same gas, logs and error.

The state it leaves agrees with the first on the sets.

The sets must cover the first block, and the tracker sets of the first run do.

The second block must hold the code of every account.

Only the code of the recipient needs it: a call fetches it before it records the recipient.

The theorems hold from Paris, from which a message touches no account.

The sets play the part of a block access list in [EIP-7928, Scope and Inclusion][bal].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState (AgreesOn accessedAccount accessedCode accessedSlot
  candidateStorage)

variable {fork : Fork}

/-! ## Reads that only grow -/

section Reads

/-- A wipe of the storage of an account keeps every read. -/
private theorem readsLe_destroyStorage (tx : TransactionState) (address : Address) :
    tx.ReadsLe (tx.destroyStorage address) :=
  ⟨fun _ h => h, fun _ _ h => TransactionState.mem_storageReads_destroyStorage_of_mem h⟩

/-- A deletion of an account keeps every read. -/
private theorem readsLe_destroyAccount (tx : TransactionState) (address : Address) :
    tx.ReadsLe (tx.destroyAccount address) :=
  ⟨fun _ h => h, fun _ _ h => TransactionState.mem_storageReads_destroyStorage_of_mem h⟩

/-- A credit of ether keeps every read. -/
private theorem readsLe_creditEther {tx tx' : TransactionState} {address : Address}
    {amount : Nat} (h : creditEther fork tx address amount = .ok tx') : tx.ReadsLe tx' := by
  unfold creditEther at h
  split at h
  · exact readsLe_modifyState h
  · cases h

/-- A credit of ether reads the account it credits. -/
private theorem mem_creditEther {tx tx' : TransactionState} {address : Address}
    {amount : Nat} (h : creditEther fork tx address amount = .ok tx') :
    address ∈ tx'.accountReads := by
  unfold creditEther at h
  split at h
  · exact TransactionState.mem_accountReads_modifyState h
  · cases h

/-- From Paris, the payment of the beneficiary is a credit of ether. -/
private theorem payBeneficiary_of_paris (hfork : .paris ≤ fork) (tx : TransactionState)
    (coinbase : Address) (fee : Nat) :
    payBeneficiary fork tx coinbase fee = creditEther fork tx coinbase fee := by
  unfold payBeneficiary
  exact ite_eq_right_of_eq_false _ _ (eq_false fun h => absurd h.2.1 (Nat.not_lt.mpr hfork))

/-- From Paris, the settlement of gas keeps every read.

It also reads the sender and the beneficiary. -/
private theorem reads_settleGas (hfork : .paris ≤ fork) {env : BlockEnvironment fork}
    {tx tx' : TransactionState} {sender : Address} {t : Transaction} {gasLeft refund used : Nat}
    (h : settleGas env tx sender t gasLeft refund = .ok (tx', used)) :
    tx.ReadsLe tx' ∧ sender ∈ tx'.accountReads ∧ env.coinbase ∈ tx'.accountReads := by
  unfold settleGas at h
  obtain ⟨refunded, hrefund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, hpay, h⟩ := bind_ok_iff.mp h
  cases h
  rw [payBeneficiary_of_paris hfork] at hpay
  exact ⟨(readsLe_creditEther hrefund).trans (readsLe_creditEther hpay),
    (readsLe_creditEther hpay).accountReads _ (mem_creditEther hrefund), mem_creditEther hpay⟩

/-- A deletion of the touched empty accounts keeps every read. -/
private theorem readsLe_destroyTouchedEmptyAccounts (tx : TransactionState)
    (touched : List Address) : tx.ReadsLe (tx.destroyTouchedEmptyAccounts fork touched) := by
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact .refl tx
  · induction touched generalizing tx with
    | nil => exact .refl tx
    | cons address rest ih =>
      simp only [List.foldl_cons]
      split
      · exact (readsLe_destroyAccount tx address).trans (ih _)
      · exact ih tx

/-- The deletions at the end of a transaction keep every read. -/
private theorem readsLe_deleteAccounts {tx tx' : TransactionState} {output : CallOutput}
    (h : deleteAccounts fork tx output = .ok tx') : tx.ReadsLe tx' := by
  have step : ∀ (init mid : TransactionState) (address : Address),
      (if fork ≥ .glamsterdam then init.clearAccountPreservingBalance fork address
        else pure (init.destroyAccount address)) = .ok mid → init.ReadsLe mid := by
    intro init mid address hmid
    split at hmid
    · unfold TransactionState.clearAccountPreservingBalance at hmid
      exact TransactionState.ReadsLe.trans (readsLe_destroyStorage init address)
        (readsLe_modifyState hmid)
    · cases hmid
      exact readsLe_destroyAccount _ _
  have fold : ∀ (l : List Address) (init final : TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final → init.ReadsLe final := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact .refl _
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      exact (step init mid address hmid).trans (ih mid final h)
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact (fold _ _ _ hdeleted).trans (readsLe_destroyTouchedEmptyAccounts _ _)

end Reads

/-! ## Agreement of each step -/

section Steps

variable {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop}

/-- A success related to a result makes that result a success, with a related value. -/
private theorem exists_ok_of_exceptRel {ε α β : Type} {r : α → β → Prop} {x : Except ε α}
    {y : Except ε β} {a : α} (h : ExceptRel r x y) (hx : x = .ok a) :
    ∃ b, y = .ok b ∧ r a b := by
  subst hx
  cases y with
  | error e => exact (ExceptRel.ok_error h).elim
  | ok b => exact ⟨b, rfl, h⟩

/-- Buying gas for an agreed sender succeeds alike on an agreeing state. -/
private theorem buyGas_agrees {env : BlockEnvironment fork} {tx other bought : TransactionState}
    {sender : Address} {t : Transaction} (hagree : AgreesOn account allStorage slot code tx other)
    (hs : account sender) (h : buyGas env tx sender t = .ok bought) :
    ∃ bought', buyGas env other sender t = .ok bought' ∧
      AgreesOn account allStorage slot code bought bought' := by
  unfold buyGas at h ⊢
  obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
  obtain ⟨mid', hmid', hagree'⟩ := exists_ok_of_exceptRel (hagree.incrementNonce fork (.inr hs))
    hmid
  obtain ⟨bought', hb', hagreeB⟩ := exists_ok_of_exceptRel
    (hagree'.modifyState fork (.inr hs) _) h
  exact ⟨bought', by rw [hmid']; exact hb', hagreeB⟩

/-- A credit of ether to an agreed account succeeds alike on an agreeing state. -/
private theorem creditEther_agrees {tx other tx' : TransactionState} {address : Address}
    {amount : Nat} (hagree : AgreesOn account allStorage slot code tx other)
    (ha : account address) (h : creditEther fork tx address amount = .ok tx') :
    ∃ other', creditEther fork other address amount = .ok other' ∧
      AgreesOn account allStorage slot code tx' other' := by
  unfold creditEther at h ⊢
  split at h
  · rename_i hlt
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlt)]
    exact exists_ok_of_exceptRel (hagree.createEther fork (.inr ha) _) h
  · cases h

/-- From Paris, the settlement of gas succeeds alike on an agreeing state.

The sender and the beneficiary must be agreed. -/
private theorem settleGas_agrees (hfork : .paris ≤ fork) {env : BlockEnvironment fork}
    {tx other tx' : TransactionState} {sender : Address} {t : Transaction}
    {gasLeft refund used : Nat} (hagree : AgreesOn account allStorage slot code tx other)
    (hs : account sender) (hc : account env.coinbase)
    (h : settleGas env tx sender t gasLeft refund = .ok (tx', used)) :
    ∃ other', settleGas env other sender t gasLeft refund = .ok (other', used) ∧
      AgreesOn account allStorage slot code tx' other' := by
  unfold settleGas at h ⊢
  obtain ⟨refunded, hrefund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, hpay, h⟩ := bind_ok_iff.mp h
  cases h
  rw [payBeneficiary_of_paris hfork] at hpay
  obtain ⟨refunded', hrefund', hagreeR⟩ := creditEther_agrees hagree hs hrefund
  obtain ⟨paid', hpay', hagreeP⟩ := creditEther_agrees hagreeR hc hpay
  refine ⟨paid', ?_, hagreeP⟩
  dsimp only
  rw [hrefund']
  dsimp only [bind, Except.bind]
  rw [payBeneficiary_of_paris hfork, hpay']
  rfl

/-- The deletions at the end of a transaction succeed alike on an agreeing state.

Each account to delete and each touched account must be agreed. -/
private theorem deleteAccounts_agrees {tx other tx' : TransactionState} {output : CallOutput}
    (hagree : AgreesOn account allStorage slot code tx other)
    (hdel : fork ≥ .glamsterdam → ∀ address ∈ output.accountsToDelete, account address)
    (htouched : ∀ address ∈ output.touchedAccounts, account address)
    (h : deleteAccounts fork tx output = .ok tx') :
    ∃ other', deleteAccounts fork other output = .ok other' ∧
      AgreesOn account allStorage slot code tx' other' := by
  have step : ∀ (init init' mid : TransactionState) (address : Address),
      (fork ≥ .glamsterdam → account address) →
      AgreesOn account allStorage slot code init init' →
      (if fork ≥ .glamsterdam then init.clearAccountPreservingBalance fork address
        else pure (init.destroyAccount address)) = .ok mid →
      ∃ mid', (if fork ≥ .glamsterdam then init'.clearAccountPreservingBalance fork address
        else pure (init'.destroyAccount address)) = .ok mid' ∧
        AgreesOn account allStorage slot code mid mid' := by
    intro init init' mid address ha hinit hmid
    split at hmid
    · rename_i hglam
      rw [ite_eq_left_of_eq_true _ _ (eq_true hglam)]
      exact exists_ok_of_exceptRel (hinit.clearAccountPreservingBalance fork (.inr (ha hglam))) hmid
    · rename_i hglam
      rw [ite_eq_right_of_eq_false _ _ (eq_false hglam)]
      cases hmid
      exact ⟨_, rfl, hinit.destroyAccount address⟩
  have fold : ∀ (l : List Address) (init init' final : TransactionState),
      (fork ≥ .glamsterdam → ∀ address ∈ l, account address) →
      AgreesOn account allStorage slot code init init' →
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      ∃ final', l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init' = .ok final' ∧
        AgreesOn account allStorage slot code final final' := by
    intro l
    induction l with
    | nil =>
      intro init init' final _ hinit h
      cases h
      exact ⟨init', rfl, hinit⟩
    | cons address rest ih =>
      intro init init' final hl hinit h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      obtain ⟨mid', hmid', hagreeM⟩ := step init init' mid address
        (fun hg => hl hg address List.mem_cons_self) hinit hmid
      obtain ⟨final', hfinal', hagreeF⟩ := ih mid mid' final
        (fun hg x hx => hl hg x (List.mem_cons_of_mem _ hx)) hagreeM h
      exact ⟨final', bind_ok_iff.mpr ⟨mid', hmid', hfinal'⟩, hagreeF⟩
  unfold deleteAccounts at h ⊢
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted ⊢
  obtain ⟨deleted', hdeleted', hagreeD⟩ := fold _ _ _ _
    (fun hg x hx => hdel hg x (Std.ExtTreeSet.mem_toList.mp hx)) hagree hdeleted
  refine ⟨_, by rw [hdeleted']; rfl, hagreeD.destroyTouchedEmptyAccounts fork fun x hx =>
    .inr (htouched x (Std.ExtTreeSet.mem_toList.mp hx))⟩

end Steps

/-! ## The message of the transaction -/

section Message

variable {Meter : Type} [GasMeter Meter]

/-- On a state that holds every code, the message of a transaction is built. -/
private theorem exists_transactionMessage {env : BlockEnvironment fork}
    (txEnv : TransactionEnvironment fork) {state : TransactionState} (hcodes : HasCodes state)
    (sender target : Address) (gas : Nat) (t : Transaction) :
    ∃ message, transactionMessage env txEnv state sender target gas t = .ok message := by
  unfold transactionMessage
  split
  · rename_i to _
    obtain ⟨c, hc⟩ := hcodes to
    rw [hc]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Two messages of a transaction, built on two states, give the same run.

They differ at most in the code that a call fetches, which the run ignores. -/
private theorem processMessageCall_transactionMessage [LawfulGasMeter Meter]
    {env : BlockEnvironment fork} {txEnv : TransactionEnvironment fork}
    {state state' : TransactionState} {sender target : Address} {gas : Nat} {t : Transaction}
    {message message' : Message fork}
    (h : transactionMessage env txEnv state sender target gas t = .ok message)
    (h' : transactionMessage env txEnv state' sender target gas t = .ok message')
    (chainId reservoir : Nat) (start : TransactionState) (substate : Substate)
    (auths : List Authorization) (paid : Std.ExtTreeSet Address) :
    processMessageCall (Meter := Meter) chainId { message' with reservoir } start substate auths
        paid =
      processMessageCall (Meter := Meter) chainId { message with reservoir } start substate auths
        paid := by
  have htarget := (target_transactionMessage h).1
  unfold transactionMessage at h h'
  cases hto : t.to with
  | some to =>
    simp only [hto] at h h' htarget
    obtain ⟨c, -, hm⟩ := map_ok_iff.mp h
    obtain ⟨c', -, hm'⟩ := map_ok_iff.mp h'
    have hcode : message' = { message with code := c' } := by
      rw [← hm, ← hm']
    rw [hcode]
    exact processMessageCall_withCode (Meter := Meter) (message := { message with reservoir })
      htarget c' start substate auths paid
  | none =>
    simp only [hto] at h h'
    cases h
    cases h'
    rfl

/-- The message of a transaction keeps every created account among the reads.

It starts on a state that has created no account, and a call runs at its recipient. -/
private theorem createdRead_processMessageCall [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (hnone : ∀ address, address ∉ state.createdAccounts)
    (recipient : ∀ target, message.target = some target → target = message.currentTarget)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    CreatedRead output.state := by
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      exact fun address hmem => absurd hmem (hnone address)
  rename_i first hfirst
  have hstart : CreatedRead first.state := fun address hmem =>
    absurd (createdAccounts_prepareFirstFrame hfirst ▸ hmem) (hnone address)
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    rw [state_ofFrame]
    refine createdRead_processCreateMessage hstart ?_ hrun
    rw [(substate_prepareFirstFrame hfirst).2.2.2]
    exact currentRead_prepareFirstFrame recipient hfirst
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    rw [state_ofFrame]
    exact createdRead_processMessage hstart hrun

end Message

/-! ## The purchase of gas -/

/-- Buying gas keeps the block of the state and makes no created account. -/
private theorem parent_buyGas {env : BlockEnvironment fork} {tx tx' : TransactionState}
    {sender : Address} {t : Transaction} (h : buyGas env tx sender t = .ok tx') :
    tx'.parent = tx.parent ∧ tx'.createdAccounts = tx.createdAccounts := by
  unfold buyGas at h
  obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
  exact ⟨(TransactionState.parent_modifyState h).trans (TransactionState.parent_modifyState hmid),
    (TransactionState.createdAccounts_modifyState h).trans
      (TransactionState.createdAccounts_modifyState hmid)⟩

/-- Buying gas keeps the code of every account available. -/
private theorem hasCodes_buyGas {env : BlockEnvironment fork} {tx tx' : TransactionState}
    {sender : Address} {t : Transaction} (h : buyGas env tx sender t = .ok tx')
    (hcodes : HasCodes tx) : HasCodes tx' := by
  unfold buyGas at h
  obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
  refine hasCodes_modifyState h (hasCodes_incrementNonce hmid hcodes) fun _ hf => .inl ?_
  split at hf
  · cases hf
    rfl
  · cases hf

/-- A transaction that ends with its reads in the sets gives the same output on an agreeing block.

The two outputs differ only in their states, which agree.

The sets must cover the first block, and the second block must hold the code of every account.

It holds from Paris, for any lawful gas meter. -/
theorem runTransaction_agrees {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    (hfork : .paris ≤ fork) {env : BlockEnvironment fork} {block other : BlockState}
    {included : Included} {tx : Transaction} {account allStorage : Address → Prop}
    {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop}
    (covers : CoversBlock block account allStorage code)
    (hagree : BlockState.AgreesOn account allStorage slot code block other)
    (hcodes : HasCodes (TransactionState.ofBlock other)) {output : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok output)
    (hreads : ReadsIn account slot output.state) :
    ∃ output', runTransaction Meter env other included tx = .ok output' ∧
      output' = { output with state := output'.state } ∧
      AgreesOn account allStorage slot code output.state output'.state := by
  unfold runTransaction at h
  obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hsettle, h⟩ := bind_ok_iff.mp h
  obtain ⟨final, hfinal, h⟩ := bind_ok_iff.mp h
  cases h
  have hbought := mapError_ok_iff.mp hbought
  have hsettle := mapError_ok_iff.mp hsettle
  have hfinal := mapError_ok_iff.mp hfinal
  -- The reads of the settled state and of the message are in the sets.
  have hreadsSettled := ReadsIn.of_readsLe (readsLe_deleteAccounts hfinal) hreads
  obtain ⟨hleSettle, hsender, hcoinbase⟩ := reads_settleGas hfork hsettle
  have hreadsOut := ReadsIn.of_readsLe hleSettle hreadsSettled
  have hs := hreadsSettled.account _ hsender
  have hc := hreadsSettled.account _ hcoinbase
  -- The target and the purchase of gas.
  have hfresh := AgreesOn.ofBlock hagree
  have htarget' : messageTarget included.sender
      ((TransactionState.ofBlock other).getAccount included.sender).nonce tx = .ok target := by
    rw [hfresh.getAccount_eq (.inr hs)]
    exact htarget
  obtain ⟨bought', hbought', hagreeB⟩ := buyGas_agrees hfresh hs hbought
  -- The message.
  obtain ⟨message', hmessage'⟩ := exists_transactionMessage
    { origin := included.sender, gasPrice := included.gasPrice,
      blobVersionedHashes := fun _ => tx.blobHashes } (hasCodes_buyGas hbought' hcodes)
    included.sender target (allocateGas fork tx included.intrinsicGas).execution tx (env := env)
  have hrecipient : ∀ to, ({ message with
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
    exact (Except.ok.inj htarget)
  have ⟨hparent, hcreated⟩ := parent_buyGas hbought
  obtain ⟨out', hout', hsame, hagreeO⟩ := processMessageCall_agrees covers hagreeB
    (by rw [hparent]; rfl) ((CodeOrigin.ofBlock block).of_keepsCodeOrigin
      (keepsCodeOrigin_buyGas hbought)) (noNewCandidate_buyGas (.ofBlock block) hbought)
    hrecipient hout hreadsOut
  generalize out'.state = s' at hsame hagreeO
  subst hsame
  -- The settlement and the deletions.
  obtain ⟨settled', hsettle', hagreeS⟩ := settleGas_agrees hfork hagreeO hs hc hsettle
  have hcr := createdRead_processMessageCall (fun a ha => by
    rw [hcreated] at ha
    simp [TransactionState.ofBlock] at ha) hrecipient hout
  have hdel : fork ≥ .glamsterdam → ∀ a ∈ out.accountsToDelete, account a := fun hg a ha =>
    hreadsOut.account _ (hcr a (accountsToDelete_processMessageCall
      (Nat.le_trans (by decide) hg) hout (by simp) a ha))
  have htouched : ∀ a ∈ out.touchedAccounts, account a := fun a ha => by
    have := touchedAccounts_processMessageCall hfork hout a ha
    simp at this
  obtain ⟨final', hfinal', hagreeF⟩ := deleteAccounts_agrees hagreeS hdel htouched hfinal
  refine ⟨⟨final', used, transactionBlockGas fork included.sender tx (out.gasLeft + out.reservoir)
    out.refund out.stateGasUsed, out.logs, out.error⟩, ?_, rfl, hagreeF⟩
  unfold runTransaction
  dsimp only
  rw [htarget']
  dsimp only [bind, Except.bind]
  rw [hbought']
  dsimp only [Except.mapError]
  rw [hmessage']
  dsimp only
  rw [processMessageCall_transactionMessage hmessage hmessage', hout']
  dsimp only
  rw [hsettle']
  dsimp only [Except.mapError]
  rw [show deleteAccounts fork settled' { out with state := s' } = .ok final' from hfinal']
  rfl

/-- A transaction that ends with its reads in the sets gives the same output on an agreeing block.

The two outputs differ only in their states, which agree.

The sets must cover the first block, and the second block must hold the code of every account.

It holds from Paris, with the gas meter that each fork uses. -/
theorem processTransaction_agrees (hfork : .paris ≤ fork) {env : BlockEnvironment fork}
    {block other : BlockState} {included : Included} {tx : Transaction}
    {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
    {code : Hash32 → Prop} (covers : CoversBlock block account allStorage code)
    (hagree : BlockState.AgreesOn account allStorage slot code block other)
    (hcodes : HasCodes (TransactionState.ofBlock other)) {output : TransactionOutput}
    (h : processTransaction env block included tx = .ok output)
    (hreads : ReadsIn account slot output.state) :
    ∃ output', processTransaction env other included tx = .ok output' ∧
      output' = { output with state := output'.state } ∧
      AgreesOn account allStorage slot code output.state output'.state := by
  unfold processTransaction at h ⊢
  split at h
  · cases h
  rename_i hhegota
  rw [ite_eq_right_of_eq_false _ _ (eq_false hhegota)]
  split at h
  · rename_i hglam
    rw [ite_eq_left_of_eq_true _ _ (eq_true hglam)]
    exact runTransaction_agrees hfork covers hagree hcodes h hreads
  · rename_i hglam
    rw [ite_eq_right_of_eq_false _ _ (eq_false hglam)]
    exact runTransaction_agrees hfork covers hagree hcodes h hreads

/-- From Paris, a transaction that succeeds has read its sender. -/
theorem sender_mem_processTransaction (hfork : .paris ≤ fork) {env : BlockEnvironment fork}
    {block : BlockState} {included : Included} {tx : Transaction} {output : TransactionOutput}
    (h : processTransaction env block included tx = .ok output) :
    included.sender ∈ output.state.accountReads := by
  have run : ∀ {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter] {output : TransactionOutput},
      runTransaction Meter env block included tx = .ok output →
        included.sender ∈ output.state.accountReads := by
    intro Meter _ _ output h
    unfold runTransaction at h
    obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
    obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
    obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
    obtain ⟨out, hout, h⟩ := bind_ok_iff.mp h
    obtain ⟨⟨settled, used⟩, hsettle, h⟩ := bind_ok_iff.mp h
    obtain ⟨final, hfinal, h⟩ := bind_ok_iff.mp h
    cases h
    exact (readsLe_deleteAccounts (mapError_ok_iff.mp hfinal)).accountReads _
      (reads_settleGas hfork (mapError_ok_iff.mp hsettle)).2.1
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · exact run h
  · exact run h

/-- A transaction that succeeds gives the same output on a block that agrees on what it recorded.

The two outputs differ only in their states, which agree on those records.

The second block must hold the code of every account.

It holds from Paris. -/
theorem processTransaction_agrees_of_tracker (hfork : .paris ≤ fork)
    {env : BlockEnvironment fork} {block other : BlockState} {included : Included}
    {tx : Transaction} (hcodes : HasCodes (TransactionState.ofBlock other))
    {output : TransactionOutput} (h : processTransaction env block included tx = .ok output)
    (hagree : BlockState.AgreesOnTracker output.state block other) :
    ∃ output', processTransaction env other included tx = .ok output' ∧
      output' = { output with state := output'.state } ∧
      AgreesOn (accessedAccount output.state) (candidateStorage block output.state)
        (accessedSlot output.state) (accessedCode block output.state)
        output.state output'.state :=
  processTransaction_agrees hfork (CoversBlock.ofTracker block output.state) hagree hcodes h
    ⟨fun _ h => .inl h, fun _ _ h => .inl h⟩

end EthLib.Execution.Transactions

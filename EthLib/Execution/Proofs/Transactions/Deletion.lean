module

public import EthLib.Execution.Proofs.Evm.Call.Touched
public import EthLib.Execution.Proofs.Evm.Logic.Marks
public import EthLib.Execution.Proofs.Transactions.Failed

/-!
# Proofs: the accounts that the end of a transaction deletes

At the end of a transaction, its accounts to delete are cleared, then its empty touched accounts go.

From Cancun, SELFDESTRUCT marks its account for deletion only when the transaction created it.

[EIP-6780][e6780] sets this rule.

The first frame starts with no account to delete and no touched account.

A message that fails passes on no account to delete.

From Paris, a message touches no account beyond those of its substate.

A transaction starts with no touched account.

The settlement of gas keeps the created accounts.

So the deletions leave every other account, its storage and its transient storage as they were.

Before Glamsterdam, the deletions remove each account to delete.

A frame that no revert undoes passes its marks to the frame that ends the message.

So each account it marks is absent after a transaction whose message ends without an error.

Before Cancun, SELFDESTRUCT marks the account that runs it, so that account is absent too.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm

variable {fork : Fork} {tx : Transaction}

open State.TransactionState (SameOutside)

/-! ## The message of the transaction -/

section Meter

variable {Meter : Type} [GasMeter Meter]

/-- The first frame of a transaction keeps the accounts to delete of the substate it is given.

It keeps the touched accounts of that substate too.

It sends its message to the target of the message it is given. -/
theorem substate_prepareFirstFrame {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first) :
    first.substate.accountsToDelete = substate.accountsToDelete ∧
      first.substate.touchedAccounts = substate.touchedAccounts ∧
      first.message.target = message.target := by
  unfold prepareFirstFrame at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨rfl, rfl, rfl⟩
      · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
        cases h
        exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨m, h, -⟩ := bind_ok_iff.mp h
      cases h
  · dsimp only at h
    obtain ⟨done, -, h⟩ := bind_ok_iff.mp h
    generalize (if message.value ≠ 0 then _ else done.state) = read0 at h
    split at h <;>
    · obtain ⟨m, -, h⟩ := bind_ok_iff.mp h
      obtain ⟨code, -, h⟩ := bind_ok_iff.mp h
      generalize (if fork ≥ .pectra then delegatedAddress code else none) = delegate at h
      rcases delegate with _ | delegate
      · cases h
        exact ⟨rfl, rfl, rfl⟩
      · dsimp only at h
        split at h <;>
        · obtain ⟨m', -, h⟩ := bind_ok_iff.mp h
          obtain ⟨code', -, h⟩ := bind_ok_iff.mp h
          cases h
          exact ⟨rfl, rfl, rfl⟩

/-- From Cancun, the message of a transaction leaves only created accounts to delete.

Its substate must start with no account to delete. -/
theorem accountsToDelete_processMessageCall [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (empty : ∀ address, address ∉ substate.accountsToDelete) :
    ∀ address ∈ output.accountsToDelete, address ∈ output.state.createdAccounts := by
  intro address mem
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      simp [CallOutput.ofHalt] at mem
  rename_i first hfirst
  have start := (substate_prepareFirstFrame hfirst).1
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    by_cases herr : evm.error.isSome = true
    · simp [CallOutput.ofFrame, herr] at mem
    · simp only [CallOutput.ofFrame, herr] at mem ⊢
      exact ((deletesCreated_processCreateMessage hfork hrun).2 address mem).resolve_left
        (start ▸ empty address)
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    by_cases herr : evm.error.isSome = true
    · simp [CallOutput.ofFrame, herr] at mem
    · simp only [CallOutput.ofFrame, herr] at mem ⊢
      exact ((deletesCreated_processMessage hfork hrun).2 address mem).resolve_left
        (start ▸ empty address)

/-- From Paris, the message of a transaction touches no account beyond its substate. -/
theorem touchedAccounts_processMessageCall [LawfulGasMeter Meter] (hfork : .paris ≤ fork)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {output : CallOutput}
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output) :
    TouchedSubset output.touchedAccounts substate.touchedAccounts := by
  intro address mem
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      simp [CallOutput.ofHalt] at mem
  rename_i first hfirst
  have start := (substate_prepareFirstFrame hfirst).2.1
  split at h
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    by_cases herr : evm.error.isSome = true
    · simp [CallOutput.ofFrame, herr] at mem
    · simp only [CallOutput.ofFrame, herr] at mem
      exact start ▸ touchedAccounts_processCreateMessage hfork hrun address mem
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    by_cases herr : evm.error.isSome = true
    · simp [CallOutput.ofFrame, herr] at mem
    · have hlt : ¬fork < .paris := Nat.not_lt.mpr hfork
      simp only [CallOutput.ofFrame, herr, hlt, false_and, and_false, ite_false,
        Bool.false_eq_true] at mem
      exact start ▸ touchedAccounts_processMessage hfork hrun address mem

/-- A message of a transaction that ends without an error ends as the run of its first frame.

That call or creation ends without an error.

The message leaves to delete the accounts that the call or creation leaves to delete. -/
theorem processMessageCall_of_error_eq_none [LawfulGasMeter Meter] {chainId : Nat}
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    {output : CallOutput}
    (hfirst : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid =
      .ok first)
    (h : processMessageCall (Meter := Meter) chainId message state substate auths paid =
      .ok output)
    (ok : output.error = none) :
    ∃ ended, (match first.message.target with
      | some _ => processMessage fork first.message first.state first.substate first.meter
          first.held
      | none => processCreateMessage fork first.message first.state first.substate first.meter
          first.held) = .ok ended ∧
      ended.val.error = none ∧ output.accountsToDelete = ended.val.substate.accountsToDelete := by
  have htarget := (substate_prepareFirstFrame hfirst).2.2
  unfold processMessageCall at h
  split at h
  · split at h
    · cases h
    · cases h
      simp [CallOutput.ofHalt] at ok
  rename_i first' hfirst'
  rw [hfirst] at hfirst'
  cases hfirst'
  split at h
  · rename_i hnone
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    by_cases herr : evm.error.isSome = true
    · simp [CallOutput.ofFrame, herr] at ok
      simp [ok] at herr
    · refine ⟨⟨evm, used⟩, by rw [htarget, hnone]; exact hrun, by simpa using herr, ?_⟩
      simp only [CallOutput.ofFrame, herr]
      rfl
  · rename_i target hsome
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    by_cases herr : evm.error.isSome = true
    · simp [CallOutput.ofFrame, herr] at ok
      simp [ok] at herr
    · refine ⟨⟨evm, used⟩, by rw [htarget, hsome]; exact hrun, by simpa using herr, ?_⟩
      simp only [CallOutput.ofFrame, herr]
      rfl

end Meter

/-! ## The end of the transaction -/

/-- The settlement of gas keeps the created accounts. -/
theorem createdAccounts_settleGas {env : BlockEnvironment fork}
    {state state' : State.TransactionState} {sender : Address} {gasLeft refund used : Nat}
    (h : settleGas env state sender tx gasLeft refund = .ok (state', used)) :
    state'.createdAccounts = state.createdAccounts := by
  have credit : ∀ {state state' : State.TransactionState} {address : Address} {amount : Nat},
      creditEther fork state address amount = .ok state' →
        state'.createdAccounts = state.createdAccounts := by
    intro state state' address amount h
    unfold creditEther at h
    split at h
    · exact State.TransactionState.createdAccounts_modifyState h
    · cases h
  obtain ⟨refunded, hrefund, h⟩ := bind_ok_iff.mp h
  obtain ⟨paid, hpay, h⟩ := bind_ok_iff.mp h
  cases h
  refine Eq.trans ?_ (credit hrefund)
  unfold payBeneficiary at hpay
  split at hpay
  · cases hpay
    split <;> rfl
  · exact credit hpay

/-- The deletions at the end of a transaction change no address outside two sets.

Those are its accounts to delete and its touched accounts. -/
theorem sameOutside_deleteAccounts {state state' : State.TransactionState}
    {output : CallOutput} (h : deleteAccounts fork state output = .ok state') :
    SameOutside (output.accountsToDelete.toList ++ output.touchedAccounts.toList) state state' := by
  have fold : ∀ (l : List Address) (init final : State.TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      SameOutside l init final := by
    intro l
    induction l with
    | nil =>
      intro init final h
      cases h
      exact SameOutside.refl _ _
    | cons address rest ih =>
      intro init final h
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      have first : SameOutside [address] init mid := by
        split at hmid
        · exact State.TransactionState.sameOutside_clearAccountPreservingBalance hmid
        · cases hmid
          exact State.TransactionState.sameOutside_destroyAccount _ _
      exact (first.trans (ih mid final h)).mono (by simp)
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact (fold _ _ _ hdeleted).trans
    (State.TransactionState.sameOutside_destroyTouchedEmptyAccounts fork _ _)

/-- A transaction starts with no account to delete. -/
@[simp] theorem accountsToDelete_startSubstate (coinbase sender target : Address) :
    (startSubstate fork coinbase sender target tx).accountsToDelete = ∅ := rfl

/-- A transaction starts with no touched account. -/
@[simp] theorem touchedAccounts_startSubstate (coinbase sender target : Address) :
    (startSubstate fork coinbase sender target tx).touchedAccounts = ∅ := rfl

/-- From Cancun, the deletions at the end of a transaction change only created accounts.

Those are the created accounts of the settled state.

The message starts from the substate of a transaction, then the gas is settled.

The deletions run on the settled state.

Every other address keeps its account, its storage and its transient storage. -/
theorem sameOutside_deleteAccounts_of_dencun {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] (hfork : .dencun ≤ fork) {env : BlockEnvironment fork}
    {chainId : Nat} {message : Message fork} {state settled final : State.TransactionState}
    {coinbase sender target : Address} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {output : CallOutput} {gasLeft refund used : Nat}
    (hcall : processMessageCall (Meter := Meter) chainId message state
      (startSubstate fork coinbase sender target tx) auths paid = .ok output)
    (hsettle : settleGas env output.state sender tx gasLeft refund = .ok (settled, used))
    (hdelete : deleteAccounts fork settled output = .ok final) :
    SameOutside settled.createdAccounts.toList settled final := by
  refine (sameOutside_deleteAccounts hdelete).mono fun address mem => ?_
  rw [Std.ExtTreeSet.mem_toList, createdAccounts_settleGas hsettle]
  rcases List.mem_append.mp mem with mem | mem
  · exact accountsToDelete_processMessageCall hfork hcall (by simp) address
      (Std.ExtTreeSet.mem_toList.mp mem)
  · have touched := touchedAccounts_processMessageCall (Nat.le_trans (by decide) hfork) hcall
      address (Std.ExtTreeSet.mem_toList.mp mem)
    simp at touched

/-- From Cancun, a transaction that runs ends with deletions that change only accounts it created.

Its run names the target, the state after the purchase of gas, the message and its output.

It also names the state after the settlement of gas, on which the deletions run.

The state after the transaction agrees with that state outside the accounts it created. -/
theorem runTransaction_deletes_created {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    (hfork : .dencun ≤ fork) {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) :
    ∃ (target : Address) (bought : State.TransactionState) (message : Message fork)
      (output : CallOutput) (settled : State.TransactionState),
      messageTarget included.sender
          ((State.TransactionState.ofBlock block).getAccount included.sender).nonce tx =
        .ok target ∧
      buyGas env (State.TransactionState.ofBlock block) included.sender tx = .ok bought ∧
      transactionMessage env
          { origin := included.sender, gasPrice := included.gasPrice,
            blobVersionedHashes := fun _ => tx.blobHashes }
          bought included.sender target (allocateGas fork tx included.intrinsicGas).execution tx =
        .ok message ∧
      processMessageCall (Meter := Meter) env.chainId.toNat
          { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
          (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
          (paidWrites included.sender target tx) = .ok output ∧
      settleGas env output.state included.sender tx (output.gasLeft + output.reservoir)
          output.refund = .ok (settled, out.gasUsed) ∧
      deleteAccounts fork settled output = .ok out.state ∧
      SameOutside settled.createdAccounts.toList settled out.state := by
  unfold runTransaction at h
  obtain ⟨target, htarget, h⟩ := bind_ok_iff.mp h
  obtain ⟨bought, hbought, h⟩ := bind_ok_iff.mp h
  obtain ⟨message, hmessage, h⟩ := bind_ok_iff.mp h
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hsettle, h⟩ := bind_ok_iff.mp h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  have hs := mapError_ok_iff.mp hsettle
  have hd := mapError_ok_iff.mp hdeleted
  exact ⟨target, bought, message, output, settled, htarget, mapError_ok_iff.mp hbought,
    hmessage, houtput, hs, hd, sameOutside_deleteAccounts_of_dencun hfork houtput hs hd⟩

/-! ## Before Glamsterdam -/

/-- Before Glamsterdam, the deletions at the end of a transaction remove each account to delete.

No account is then left at its address. -/
theorem accountExists_deleteAccounts (hfork : fork < .glamsterdam)
    {state state' : State.TransactionState} {output : CallOutput}
    (h : deleteAccounts fork state output = .ok state') {address : Address}
    (mem : address ∈ output.accountsToDelete) : state'.accountExists address = false := by
  have fold : ∀ (l : List Address) (init final : State.TransactionState),
      l.foldlM (fun state address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else pure (state.destroyAccount address)) init = .ok final →
      address ∈ l ∨ init.accountExists address = false → final.accountExists address = false := by
    intro l
    induction l with
    | nil =>
      intro init final h hin
      cases h
      exact hin.resolve_left (List.not_mem_nil)
    | cons removed rest ih =>
      intro init final h hin
      obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
      split at hmid
      · exact absurd ‹_› (Nat.not_le.mpr hfork)
      cases hmid
      by_cases hrest : address ∈ rest
      · exact ih _ final h (.inl hrest)
      · refine ih _ final h (.inr ?_)
        by_cases heq : address = removed
        · subst heq
          exact State.TransactionState.accountExists_destroyAccount_self _ _
        · rw [State.TransactionState.accountExists_destroyAccount_of_ne _ heq]
          exact hin.resolve_left fun hin => heq ((List.mem_cons.mp hin).resolve_right hrest)
  unfold deleteAccounts at h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at hdeleted
  exact State.TransactionState.accountExists_destroyTouchedEmptyAccounts
    (fold _ _ _ hdeleted (.inl (Std.ExtTreeSet.mem_toList.mpr mem)))

/-- Before Glamsterdam, a frame that no revert undoes has each account it marks removed.

The frame is one that the run of the message of a transaction goes through.

Its run names the target, the state after the purchase of gas, the message and its first frame.

The message must end without an error, and the code it runs starts from the frame `start`.

Each account that the frame `inner` marks for deletion is then absent after the transaction. -/
theorem runTransaction_removes_marked {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter]
    (hfork : fork < .glamsterdam) {env : BlockEnvironment fork} {block : State.BlockState}
    {included : Included} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) (ok : out.error = none)
    {target : Address} {bought : State.TransactionState} {message : Message fork}
    {first : FirstFrame fork Meter} {start inner : Evm fork Meter}
    (htarget : messageTarget included.sender
        ((State.TransactionState.ofBlock block).getAccount included.sender).nonce tx = .ok target)
    (hbought : buyGas env (State.TransactionState.ofBlock block) included.sender tx = .ok bought)
    (hmessage : transactionMessage env
        { origin := included.sender, gasPrice := included.gasPrice,
          blobVersionedHashes := fun _ => tx.blobHashes }
        bought included.sender target (allocateGas fork tx included.intrinsicGas).execution tx =
      .ok message)
    (hfirst : prepareFirstFrame (Meter := Meter) env.chainId.toNat
        { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
        (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) = .ok first)
    (starts : CodeStarts fork first.message first.state first.substate first.meter start)
    (visits : Visits fork first.message.gas start inner) :
    ∀ address ∈ inner.substate.accountsToDelete, out.state.accountExists address = false := by
  unfold runTransaction at h
  obtain ⟨target', htarget', h⟩ := bind_ok_iff.mp h
  rw [htarget] at htarget'
  cases htarget'
  obtain ⟨bought', hbought', h⟩ := bind_ok_iff.mp h
  have hb := mapError_ok_iff.mp hbought'
  rw [hbought] at hb
  cases hb
  obtain ⟨message', hmessage', h⟩ := bind_ok_iff.mp h
  rw [hmessage] at hmessage'
  cases hmessage'
  obtain ⟨output, houtput, h⟩ := bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, -, h⟩ := bind_ok_iff.mp h
  obtain ⟨deleted, hdeleted, h⟩ := bind_ok_iff.mp h
  cases h
  obtain ⟨ended, hended, err, toDelete⟩ := processMessageCall_of_error_eq_none hfirst houtput ok
  intro address mem
  refine accountExists_deleteAccounts hfork (mapError_ok_iff.mp hdeleted) ?_
  rw [toDelete]
  exact toDeleteLe_of_codeStarts hended starts visits err address mem

/-- Before Cancun, an account whose SELFDESTRUCT no revert undoes is absent after the transaction.

The frame `after` is the result of SELFDESTRUCT on a frame `evm`, so both run one message.

The frame `after` is one that the run of the message of the transaction goes through.

Its run names the target, the state after the purchase of gas, the message and its first frame.

The message must end without an error, and the code it runs starts from the frame `start`.

The account that runs the SELFDESTRUCT is then absent after the transaction. -/
theorem runTransaction_removes_selfdestructed {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] (hfork : fork < .dencun) {env : BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {out : TransactionOutput}
    (h : runTransaction Meter env block included tx = .ok out) (ok : out.error = none)
    {target : Address} {bought : State.TransactionState} {message : Message fork}
    {first : FirstFrame fork Meter} {start evm after : Evm fork Meter} {beneficiary : Address}
    {refund : Nat}
    (htarget : messageTarget included.sender
        ((State.TransactionState.ofBlock block).getAccount included.sender).nonce tx = .ok target)
    (hbought : buyGas env (State.TransactionState.ofBlock block) included.sender tx = .ok bought)
    (hmessage : transactionMessage env
        { origin := included.sender, gasPrice := included.gasPrice,
          blobVersionedHashes := fun _ => tx.blobHashes }
        bought included.sender target (allocateGas fork tx included.intrinsicGas).execution tx =
      .ok message)
    (hfirst : prepareFirstFrame (Meter := Meter) env.chainId.toNat
        { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir } bought
        (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) = .ok first)
    (starts : CodeStarts fork first.message first.state first.substate first.meter start)
    (visits : Visits fork first.message.gas start after)
    (destructs : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    out.state.accountExists evm.message.currentTarget = false :=
  runTransaction_removes_marked (Nat.lt_of_lt_of_le hfork (by decide)) h ok htarget hbought
    hmessage hfirst starts visits _ (finishSelfdestruct_deletes hfork destructs)

end EthLib.Execution.Transactions

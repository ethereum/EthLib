module

public import EthLib.Execution.Blocks.SystemCall
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Proofs.Transactions.Noninterference

/-!
# Proofs: the system calls and withdrawals depend only on what they read

Run a system call, or the withdrawals, on two block states that agree on four sets.

The sets name accounts, whole storages, slots and code hashes.

When the first run ends with every read in the sets, the second gives the same output.

Only the states of the two outputs differ, and they agree.

A system call runs one message with no authorization, so the result for a message applies.

A call that must succeed first checks that its contract has code.

The run records that contract as read, so the sets name its code hash.

The withdrawals only credit balances, and each credit reads the account it credits.

The sets play the part of a block access list in [EIP-7928, Scope and Inclusion][bal].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State
open EthLib.Execution.State.TransactionState (AgreesOn)
open EthLib.Execution.Transactions (CallOutput prepareFirstFrame processMessageCall)

variable {fork : Fork} {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop}

/-! ## System calls -/

/-- A system message whose first frame fails to start has still read its target. -/
private theorem mem_accountReads_prepareFirstFrame_error {Meter : Type} [GasMeter Meter]
    {env : BlockEnvironment fork} {state : TransactionState} {target : Address}
    {data : ByteArray} {e : EvmError} {read : TransactionState}
    (h : prepareFirstFrame (Meter := Meter) env.chainId.toNat (systemMessage env target data)
      state Substate.empty [] ∅ = .error (e, read)) :
    target ∈ read.accountReads := by
  have htarget : (systemMessage env target data).target = some target := rfl
  have hvalue : (systemMessage env target data).value = 0 := rfl
  have key : ∀ {α ε : Type} {x : Except ε α} {f : ε → EvmError} {s : TransactionState},
      x.mapError (fun y => (f y, s)) = .error (e, read) → read = s := by
    intro α ε x f s hx
    cases x <;> simp_all [Except.mapError]
  have hmem : ∀ s : TransactionState, target ∈ (s.recordAccountRead target).accountReads :=
    fun s => (TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)
  unfold prepareFirstFrame at h
  simp only [htarget, hvalue, Transactions.applyAuthorizations, List.foldlM_nil] at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  simp only [ne_eq, not_true_eq_false, false_and, and_false, ↓reduceIte] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       rw [key ‹_›]
       first
       | exact hmem _
       | exact (TransactionState.mem_accountReads_recordAccountRead _ _ _).mpr (.inr (hmem _)))

/-- A system message that runs to its end has read its target. -/
private theorem mem_accountReads_processMessageCall {Meter : Type} [GasMeter Meter]
    [LawfulGasMeter Meter] {env : BlockEnvironment fork} {state : TransactionState}
    {target : Address} {data : ByteArray} {out : CallOutput}
    (h : processMessageCall (Meter := Meter) env.chainId.toNat (systemMessage env target data)
      state Substate.empty = .ok out) :
    target ∈ out.state.accountReads := by
  unfold processMessageCall at h
  split at h
  · rename_i hprep
    split at h
    · cases h
    · cases h
      have := mem_accountReads_prepareFirstFrame_error hprep
      exact this
  rename_i first hfirst
  have hcur := Transactions.currentRead_prepareFirstFrame (fun _ ht => by cases ht; rfl) hfirst
  split at h
  · rename_i hnone
    cases hnone
  · obtain ⟨⟨evm, used⟩, hrun, h⟩ := bind_ok_iff.mp h
    cases h
    have hle := readsLe_processMessage hrun
    unfold CallOutput.ofFrame
    split <;> exact hle.accountReads _ hcur

/-- A system call that succeeds has read its contract. -/
theorem mem_accountReads_systemCall {env : BlockEnvironment fork} {block : BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out) : target ∈ out.state.accountReads := by
  unfold systemCall at h
  split at h <;>
  · obtain ⟨o, ho, h⟩ := bind_ok_iff.mp h
    cases h
    exact mem_accountReads_processMessageCall ho

/-- A system call with its reads in the sets gives the same output on an agreeing block state.

The two outputs differ only in their states, which agree.

The sets must cover the first block state. -/
theorem systemCall_agrees {env : BlockEnvironment fork} {block other : BlockState}
    {target : Address} {data : ByteArray} (covers : CoversBlock block account allStorage code)
    (hagree : BlockState.AgreesOn account allStorage slot code block other)
    {out : SystemCallOutput} (h : systemCall env block target data = .ok out)
    (hreads : ReadsIn account slot out.state) :
    ∃ out', systemCall env other target data = .ok out' ∧
      out' = { out with state := out'.state } ∧
      AgreesOn account allStorage slot code out.state out'.state := by
  unfold systemCall at h ⊢
  split at h <;>
  · rename_i hfork
    simp only [hfork, ↓reduceIte]
    obtain ⟨o, ho, h⟩ := bind_ok_iff.mp h
    cases h
    obtain ⟨o', ho', hsame, hag⟩ := Transactions.processMessageCall_agrees covers
      (AgreesOn.ofBlock hagree) rfl (CodeOrigin.ofBlock block)
      (TransactionState.NoNewCandidate.ofBlock block) (fun _ ht => by cases ht; rfl) ho hreads
    generalize o'.state = s' at hsame hag
    subst hsame
    exact ⟨_, by rw [ho']; rfl, rfl, hag⟩

/-- A system call that must succeed, with its reads in the sets, succeeds alike elsewhere.

The other block state must agree with the first on the sets.

The two outputs differ only in their states, which agree.

The sets must cover the first block state. -/
theorem checkedSystemCall_agrees {env : BlockEnvironment fork} {block other : BlockState}
    {target : Address} {data : ByteArray} (covers : CoversBlock block account allStorage code)
    (hagree : BlockState.AgreesOn account allStorage slot code block other)
    {out : SystemCallOutput} (h : checkedSystemCall env block target data = .ok out)
    (hreads : ReadsIn account slot out.state) :
    ∃ out', checkedSystemCall env other target data = .ok out' ∧
      out' = { out with state := out'.state } ∧
      AgreesOn account allStorage slot code out.state out'.state := by
  unfold checkedSystemCall at h ⊢
  obtain ⟨c, hc, h⟩ := bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
  rename_i hsize
  obtain ⟨s, hs, h⟩ := bind_ok_iff.mp h
  have hsc := mapError_ok_iff.mp hs
  split at h
  · cases h
  rename_i herr
  cases h
  have ha : account target := hreads.account _ (mem_accountReads_systemCall hsc)
  have hfresh := AgreesOn.ofBlock hagree
  have hcode : codeAt other target = codeAt block target := by
    unfold codeAt
    dsimp only
    rw [hfresh.getAccount_eq (.inr ha), hfresh.getCode_eq (.inr (.inr (covers.code _ ha)))]
  obtain ⟨out', ho', hsame, hag⟩ := systemCall_agrees covers hagree hsc hreads
  refine ⟨out', ?_, hsame, hag⟩
  have herr' : out'.error = none := by rw [hsame]; exact herr
  rw [hcode, hc]
  simp only [bind, Except.bind, hsize, ↓reduceIte, ho', Except.mapError, herr', pure,
    Except.pure]

/-! ## Withdrawals -/

/-- Credits of new ether to a list of withdrawals keep every read. -/
private theorem readsLe_foldlM_createEther (amount : Withdrawal → U256) :
    ∀ (withdrawals : List Withdrawal) {tx tx' : TransactionState},
      withdrawals.foldlM (fun tx w => tx.createEther fork w.address (amount w)) tx = .ok tx' →
      tx.ReadsLe tx'
  | [], _, _, h => by
    cases h
    exact .refl _
  | w :: rest, _, _, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    exact (readsLe_modifyState hmid).trans (readsLe_foldlM_createEther amount rest h)

/-- Credits with their reads in the sets give an agreeing state on an agreeing state. -/
private theorem foldlM_createEther_agrees (amount : Withdrawal → U256) :
    ∀ (withdrawals : List Withdrawal) {tx other tx' : TransactionState},
      AgreesOn account allStorage slot code tx other →
      withdrawals.foldlM (fun tx w => tx.createEther fork w.address (amount w)) tx = .ok tx' →
      ReadsIn account slot tx' →
      ∃ other', withdrawals.foldlM (fun tx w => tx.createEther fork w.address (amount w))
          other = .ok other' ∧ AgreesOn account allStorage slot code tx' other'
  | [], _, _, _, hagree, h, _ => by
    cases h
    exact ⟨_, rfl, hagree⟩
  | w :: rest, _, other, _, hagree, h, hreads => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨mid, hmid, h⟩ := bind_ok_iff.mp h
    have ha : account w.address := hreads.account _
      ((readsLe_foldlM_createEther amount rest h).accountReads _
        (TransactionState.mem_accountReads_modifyState hmid))
    have hrel := hagree.createEther fork (.inr ha) (amount w)
    rw [hmid] at hrel
    cases hmid' : other.createEther fork w.address (amount w) with
    | error _ =>
      rw [hmid'] at hrel
      exact hrel.elim
    | ok mid' =>
      rw [hmid'] at hrel
      obtain ⟨other', h', hagree'⟩ := foldlM_createEther_agrees amount rest hrel h hreads
      exact ⟨other', by rw [bind_ok_iff]; exact ⟨mid', rfl, h'⟩, hagree'⟩

/-- Withdrawals with their reads in the sets give an agreeing state on an agreeing block state. -/
theorem withdrawalState_agrees {block other : BlockState} {withdrawals : List Withdrawal}
    (hagree : BlockState.AgreesOn account allStorage slot code block other)
    {tx : TransactionState} (h : withdrawalState fork block withdrawals = .ok tx)
    (hreads : ReadsIn account slot tx) :
    ∃ tx', withdrawalState fork other withdrawals = .ok tx' ∧
      AgreesOn account allStorage slot code tx tx' :=
  foldlM_createEther_agrees _ withdrawals (AgreesOn.ofBlock hagree) h hreads

end EthLib.Execution.Blocks

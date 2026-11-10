module

public import EthLib.Execution.Proofs.Evm.Call.Nonce

/-!
# Proofs: from Cancun, a message marks for deletion only the accounts created in its transaction

From Cancun, [EIP-6780][e6780] lets SELFDESTRUCT mark its account for deletion only when the same
transaction created it.

The created accounts of a transaction only grow: a creation adds its address, and a rollback
keeps them.

A child that succeeds passes its accounts to delete to its caller.

A child that fails passes none, and its caller keeps its own.

So every successful call and creation ends with each account to delete either marked before it
started or created in the transaction.

The deletion at the end of the transaction then removes only created accounts.

[e6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## The relation -/

/-- Every account created in the first state is created in the second. -/
def CreatedLe (tx tx' : TransactionState) : Prop :=
  ∀ address ∈ tx.createdAccounts, address ∈ tx'.createdAccounts

/-- From `evm` to `after`, the created accounts only grow.

Each account that `after` marks for deletion was marked by `evm`, or is created in `after`. -/
def DeletesCreated (evm after : Evm fork Meter) : Prop :=
  CreatedLe evm.state after.state ∧
    ∀ address ∈ after.substate.accountsToDelete,
      address ∈ evm.substate.accountsToDelete ∨ address ∈ after.state.createdAccounts

omit [GasMeter Meter] in
/-- A frame is related to itself. -/
theorem DeletesCreated.refl (evm : Evm fork Meter) : DeletesCreated evm evm :=
  ⟨fun _ h => h, fun _ h => .inl h⟩

omit [GasMeter Meter] in
/-- Two related steps make one. -/
theorem DeletesCreated.trans {a b c : Evm fork Meter} (hab : DeletesCreated a b)
    (hbc : DeletesCreated b c) : DeletesCreated a c :=
  ⟨fun x h => hbc.1 x (hab.1 x h), fun x h => (hbc.2 x h).elim
    (fun hb => (hab.2 x hb).elim .inl fun hc => .inr (hbc.1 x hc)) .inr⟩

omit [GasMeter Meter] in
/-- A step that keeps the created accounts and the accounts to delete keeps the relation. -/
theorem DeletesCreated.of_eq {a b : Evm fork Meter}
    (created : b.state.createdAccounts = a.state.createdAccounts)
    (toDelete : b.substate.accountsToDelete = a.substate.accountsToDelete) :
    DeletesCreated a b :=
  ⟨fun _ h => created ▸ h, fun _ h => .inl (toDelete ▸ h)⟩

omit [GasMeter Meter] in
/-- A step that keeps the state and the substate keeps the relation. -/
theorem DeletesCreated.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) :
    DeletesCreated a b :=
  of_eq (by rw [h.state]) (by rw [h.substate])

/-! ## The writes of the state -/

/-- A write of storage keeps the created accounts. -/
theorem createdAccounts_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Base.Bytes32} {value : Base.U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold TransactionState.setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- A new code keeps the created accounts. -/
theorem createdAccounts_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold TransactionState.setCode at h
  rw [TransactionState.createdAccounts_modifyState h]
  split <;> rfl

/-- A touch of an account keeps the created accounts. -/
theorem createdAccounts_touchAccount (tx : TransactionState) (address : Address) :
    (tx.touchAccount address).createdAccounts = tx.createdAccounts := by
  unfold TransactionState.touchAccount
  split <;> rfl

/-- A successful move of the balance of a destroyed account keeps the created accounts. -/
theorem createdAccounts_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (TransactionState.createdAccounts_modifyState h).trans
        (TransactionState.createdAccounts_moveEther h1)
    · cases h
      exact TransactionState.createdAccounts_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (TransactionState.createdAccounts_modifyState h).trans
      (TransactionState.createdAccounts_modifyState h1)

/-! ## The frames that keep the relation -/

omit [GasMeter Meter] in
/-- A record of the read of an account keeps the relation. -/
theorem deletesCreated_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    DeletesCreated evm (recordAccountRead evm address) :=
  .of_eq rfl rfl

omit [GasMeter Meter] in
/-- A record of the read of a storage key keeps the relation. -/
theorem deletesCreated_recordStorageRead (evm : Evm fork Meter) (address : Address)
    (key : Base.Bytes32) : DeletesCreated evm (recordStorageRead evm address key) :=
  .of_eq rfl rfl

omit [GasMeter Meter] in
/-- An access to an address keeps the relation. -/
theorem deletesCreated_accessAddress (evm : Evm fork Meter) (address : Address) :
    DeletesCreated evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]
  exact .of_eq rfl rfl

omit [GasMeter Meter] in
/-- An access to a storage key keeps the relation. -/
theorem deletesCreated_accessStorageKey (evm : Evm fork Meter) (address : Address)
    (key : Base.Bytes32) : DeletesCreated evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  rw [h]
  exact .of_eq rfl rfl

/-- An exceptional halt keeps the relation. -/
theorem deletesCreated_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    DeletesCreated evm (exceptionalHalt evm e) :=
  .of_eq rfl rfl

/-- A call that runs no message keeps the relation. -/
theorem deletesCreated_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : DeletesCreated evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact .of_eq rfl rfl

/-- A precompile keeps the relation. -/
theorem deletesCreated_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : DeletesCreated evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact .of_eq rfl rfl
  · split at h
    · cases h
      exact .of_eq rfl rfl
    · cases h
      exact .of_eq rfl rfl

/-- A caller that takes in a child related to it is related to the caller.

A child that succeeds passes its accounts to delete, and one that fails passes none. -/
theorem deletesCreated_incorporateChild {caller child : Evm fork Meter}
    (h : DeletesCreated caller child) :
    DeletesCreated caller (incorporateChild fork caller child) := by
  unfold incorporateChild
  split
  · refine ⟨h.1, fun x hx => ?_⟩
    rw [Std.ExtTreeSet.mem_insertMany_list] at hx
    rcases hx with hx | hx
    · exact .inl hx
    · exact h.2 x (by simpa using hx)
  · exact ⟨h.1, fun _ hx => .inl hx⟩

/-! ## A step -/

/-- A caller that resumes after a call is related to the caller, when the child is. -/
theorem deletesCreated_resumeCall {caller child after : Evm fork Meter} {newAccount : Nat}
    {outputStart outputSize : Base.U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (hc : DeletesCreated caller child) : DeletesCreated caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have s := pushWord_sameContext h1
  refine (deletesCreated_incorporateChild hc).trans (.of_eq ?_ ?_)
  · show e.state.createdAccounts = _
    rw [s.state]
    split <;> rfl
  · show e.substate.accountsToDelete = _
    rw [s.substate]
    split <;> rfl

/-- A creator that resumes after a creation is related to the creator, when the child is. -/
theorem deletesCreated_resumeCreate {caller child after : Evm fork Meter} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after)
    (hc : DeletesCreated caller child) : DeletesCreated caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have s := pushWord_sameContext h1
  refine (deletesCreated_incorporateChild hc).trans (.of_eq ?_ ?_)
  · show e.state.createdAccounts = _
    rw [s.state]
    split <;> rfl
  · show e.substate.accountsToDelete = _
    rw [s.substate]
    split <;> rfl

/-- A successful SSTORE keeps the relation. -/
theorem deletesCreated_sstoreStep {evm after : Evm fork Meter} (h : sstoreStep evm = .ok after) :
    DeletesCreated evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : DeletesCreated evm e2 :=
    DeletesCreated.of_sameContext ((popWord_sameContext h1).trans (popWord_sameContext h2))
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (Base.U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : DeletesCreated evm
        (recordStorageRead e3 e2.message.currentTarget (Base.U256.toBeBytes k)) := by
      have := deletesCreated_accessStorageKey e2 e2.message.currentTarget
        (Base.U256.toBeBytes k)
      rw [hpair] at this
      exact (c2.trans this).trans (deletesCreated_recordStorageRead _ _ _)
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : DeletesCreated evm e5 := by
        have s := (chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5)
        exact ha.trans (.of_eq (by rw [s.state]; rfl) (by rw [s.substate]; rfl))
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact m5.trans (.of_eq (createdAccounts_setStorage (Base.mapError_ok_iff.mp hst)) rfl)
    · exact ha.trans (deletesCreated_exceptionalHalt _ _)

/-- A successful TSTORE keeps the relation. -/
theorem deletesCreated_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    DeletesCreated evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact (DeletesCreated.of_sameContext ((popWord_sameContext h1).trans
      ((popWord_sameContext h2).trans (chargeGas_sameContext h3)))).trans (.of_eq rfl rfl)

/-- From Cancun, a successful SELFDESTRUCT keeps the relation.

It marks for deletion only an account created in the transaction. -/
theorem deletesCreated_selfdestructStep (hfork : .dencun ≤ fork) {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : DeletesCreated evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (Base.toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : DeletesCreated e1 e2 := by
    have := deletesCreated_accessAddress e1 (Base.toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c : DeletesCreated evm (recordAccountRead e2 (Base.toAddressMasked w)) :=
    ((DeletesCreated.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (deletesCreated_recordAccountRead _ _)
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : DeletesCreated evm e4 := c.trans (DeletesCreated.of_sameContext
      ((chargeGas_sameContext h3).trans (chargeStateGas_sameContext h4)))
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have hc := createdAccounts_selfdestructTransfer (Base.mapError_ok_iff.mp hst)
      refine m4.trans ⟨fun x hx => hc ▸ hx, fun x hx => ?_⟩
      dsimp only at hx ⊢
      split at hx
      · rename_i hd
        rcases Std.ExtTreeSet.mem_insert.mp hx with heq | hx
        · cases Std.LawfulEqCmp.eq_of_compare heq
          exact .inr (hd.resolve_left (Nat.not_lt.mpr hfork))
        · exact .inl hx
      · exact .inl hx
  · exact c.trans (deletesCreated_exceptionalHalt _ _)

omit [GasMeter Meter] in
/-- An access to an address, after a pop, keeps the relation. -/
theorem deletesCreated_popAccess {evm e1 e2 : Evm fork Meter} {w : Base.U256} {cold : Bool}
    (h1 : popWord evm = .ok (w, e1))
    (hacc : accessAddress e1 (Base.toAddressMasked w) = (cold, e2)) :
    DeletesCreated evm e2 := by
  have := deletesCreated_accessAddress e1 (Base.toAddressMasked w)
  rw [hacc] at this
  exact (DeletesCreated.of_sameContext (popWord_sameContext h1)).trans this

/-- Each instruction that reads another account keeps the relation. -/
theorem deletesCreated_accountStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : DeletesCreated evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e1 (Base.toAddressMasked w) with ⟨cold, e2⟩
    simp only [hacc] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((((deletesCreated_popAccess h1 hacc).trans
      (.of_sameContext (chargeGas_sameContext h3))).trans
      (deletesCreated_recordAccountRead _ _)).trans
      (.of_sameContext (pushWord_sameContext h4))).trans (.of_eq rfl rfl)
  case extcodesize =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e1 (Base.toAddressMasked w) with ⟨cold, e2⟩
    simp only [hacc] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨code, h4, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((((deletesCreated_popAccess h1 hacc).trans
      (.of_sameContext (chargeGas_sameContext h3))).trans
      (deletesCreated_recordAccountRead _ _)).trans
      (.of_sameContext (pushWord_sameContext h5))).trans (.of_eq rfl rfl)
  case extcodecopy =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨st, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨off, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨sz, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e4 (Base.toAddressMasked w) with ⟨cold, e5⟩
    simp only [hacc] at h
    obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨code, h7, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : DeletesCreated e4 e5 := by
      have := deletesCreated_accessAddress e4 (Base.toAddressMasked w)
      rwa [hacc] at this
    exact (((((DeletesCreated.of_sameContext ((((popWord_sameContext h1).trans
      (popWord_sameContext h2)).trans (popWord_sameContext h3)).trans
      (popWord_sameContext h4))).trans ha).trans
      (.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
      (deletesCreated_recordAccountRead _ _))).trans (.of_eq rfl rfl)
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (deletesCreated_recordAccountRead _ _).trans
        (.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep
      obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      rcases hacc : accessAddress e1 (Base.toAddressMasked w) with ⟨cold, e2⟩
      simp only [hacc] at h
      obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact ((((deletesCreated_popAccess h1 hacc).trans
        (.of_sameContext (chargeGas_sameContext h3))).trans
        (deletesCreated_recordAccountRead _ _)).trans
        (.of_sameContext (pushWord_sameContext h4))).trans (.of_eq rfl rfl)
    · cases hstep

/-- SLOAD keeps the relation. -/
theorem deletesCreated_sloadStep {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    DeletesCreated evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (Base.U256.toBeBytes w) with
    ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : DeletesCreated e1 e2 := by
    have := deletesCreated_accessStorageKey e1 e1.message.currentTarget (Base.U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((DeletesCreated.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (.of_sameContext (chargeGas_sameContext h3))).trans
    (deletesCreated_recordStorageRead _ _ _)).trans
    (.of_sameContext (pushWord_sameContext h4)) |>.trans (.of_eq rfl rfl)

/-- From Cancun, each successful instruction that gives the next frame keeps the relation. -/
theorem deletesCreated_instruction (hfork : .dencun ≤ fork) {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    DeletesCreated evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hf
    case «return» => subst hf; exact .of_sameContext (returnStep_sameContext h)
    case revert =>
      split at hf
      · cases hf; exact .of_sameContext (revertStep_sameContext h)
      · cases hf
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact deletesCreated_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact deletesCreated_sloadStep h
    case sstore => subst hf; exact deletesCreated_sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, hfork, ↓reduceIte, Option.some.injEq,
      reduceCtorEq] at hf
    case tload => subst hf; exact .of_sameContext (tloadStep_sameContext h)
    case tstore => subst hf; exact deletesCreated_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, -, hs, hsub⟩ := logStep_eq_ok h
    exact .of_eq (by rw [hs]) (by rw [hsub])
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact deletesCreated_selfdestructStep hfork h

/-- The access to a delegate keeps the relation. -/
theorem deletesCreated_accessDelegation {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    DeletesCreated evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (deletesCreated_accessAddress _ _).trans (deletesCreated_recordAccountRead _ _)
  · cases h
    exact .refl _

/-- The payment of a call keeps the relation. -/
theorem deletesCreated_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    DeletesCreated evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact .of_sameContext (((chargeGas_sameContext h1).trans
      (chargeStateGas_sameContext h2)).trans (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact .of_sameContext (chargeGas_sameContext h1)

omit [GasMeter Meter] in
/-- A result that keeps the relation from a frame keeps it from each frame before it. -/
theorem deletesCreated_keeps_lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : DeletesCreated evm evm')
    (r : result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm') :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm :=
  StepResult.Keeps.lift (fun hab hbc => hab.trans hbc) h r

/-- A successful send of a message keeps the relation. -/
theorem deletesCreated_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : Base.U256} {result : StepResult fork Meter}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact DeletesCreated.trans (by exact .of_eq rfl rfl) (deletesCreated_skipCall hs)
  · cases h
    exact ⟨.of_eq rfl rfl, fun child after hres p =>
      DeletesCreated.trans (by exact .of_eq rfl rfl) (deletesCreated_resumeCall hres p)⟩

/-- The successful end of a call instruction keeps the relation. -/
theorem deletesCreated_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact DeletesCreated.trans (by exact .of_eq rfl rfl) (deletesCreated_skipCall hs)
  · exact deletesCreated_keeps_lift (by exact .of_eq rfl rfl) (deletesCreated_genericCall h)

/-- A successful step of a call instruction keeps the relation. -/
theorem deletesCreated_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 : DeletesCreated evm e1 := by
    have he := popCallOperands_eq_ok h1
    exact .of_eq (by rw [he]) (by rw [he])
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : DeletesCreated e1 e2 := by
    have := deletesCreated_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : DeletesCreated evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (deletesCreated_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : DeletesCreated evm e4 := s3.trans (deletesCreated_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact deletesCreated_keeps_lift (s4.trans (deletesCreated_payCall h5))
        (deletesCreated_finishCall h)
    · exact s4.trans (deletesCreated_exceptionalHalt _ _)
  · exact s3.trans (deletesCreated_exceptionalHalt _ _)

/-- A successful launch of a creation keeps the relation. -/
theorem deletesCreated_launchCreate {evm : Evm fork Meter} {value : Base.U256}
    {initCode : ByteArray} {salt : Option Base.U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact DeletesCreated.trans (by exact .of_eq rfl rfl) (deletesCreated_skipCall hs)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : DeletesCreated evm (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2 address) :=
    ((DeletesCreated.of_eq rfl rfl).trans (deletesCreated_accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address)).trans
      (deletesCreated_recordAccountRead _ address)
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have m2 : DeletesCreated evm e2 := c0.trans (DeletesCreated.of_sameContext
      ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)))
    have ms : DeletesCreated evm { e2 with state } := m2.trans (.of_eq
      (TransactionState.createdAccounts_modifyState (Base.mapError_ok_iff.mp hst)) rfl)
    split at hr
    · cases hr
      exact ⟨ms.trans (.of_eq rfl rfl), fun child after hres p =>
        ms.trans (DeletesCreated.trans (by exact .of_eq rfl rfl)
          (deletesCreated_resumeCreate hres p))⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact (ms.trans (.of_sameContext (pushWord_sameContext h3))).trans (.of_eq rfl rfl)
  · exact c0.trans (deletesCreated_exceptionalHalt _ _)

/-- A successful step of CREATE or CREATE2 keeps the relation. -/
theorem deletesCreated_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : SameContext e3 e4 := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact popWord_sameContext he
    · cases h4
      exact SameContext.refl _
  have m5 : DeletesCreated evm e5 := .of_sameContext (((((popWord_sameContext h1).trans
    (popWord_sameContext h2)).trans (popWord_sameContext h3)).trans m4).trans
    (chargeGasAndMemory_sameContext h5))
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact deletesCreated_keeps_lift m5 (deletesCreated_launchCreate h)

/-- A successful instruction that may send a message keeps the relation. -/
theorem deletesCreated_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact deletesCreated_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact deletesCreated_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact deletesCreated_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact deletesCreated_createStep h
         · cases hrun)

/-- From Cancun, every successful step of every frame keeps the relation.

A message that the step sends must end in a frame related to its caller. -/
theorem deletesCreated_step (hfork : .dencun ≤ fork) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : step fork evm = .ok result) :
    result.Keeps DeletesCreated (fun caller _ child => DeletesCreated caller child) evm := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact deletesCreated_instruction hfork hop hr
      · split at h
        · rename_i hcall
          exact deletesCreated_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact .of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

/-! ## Messages -/

/-- A successful preparation of a creation keeps every created account, and adds the new one. -/
theorem createdLe_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : CreatedLe tx tx' := by
  unfold prepareCreation at h
  have h0 : CreatedLe tx ((tx.destroyStorage address).markAccountCreated address) :=
    fun _ hx => Std.ExtTreeSet.mem_insert.mpr (.inr hx)
  split at h
  · intro x hx
    rw [TransactionState.createdAccounts_modifyState (Base.mapError_ok_iff.mp h)]
    exact h0 x hx
  · cases h
    exact h0

/-- The state that a message starts its frame from has the created accounts of the state before. -/
theorem createdAccounts_startState (message : Message fork) (state : TransactionState) :
    (startState fork message state).createdAccounts = state.createdAccounts := by
  unfold startState
  split
  · exact createdAccounts_touchAccount _ _
  · rfl

/-- A rollback keeps the created accounts and the substate of the frame. -/
theorem rollbackOnError_createdAccounts (snapshot : TransactionState) (evm : Evm fork Meter) :
    (rollbackOnError snapshot evm).state.createdAccounts = evm.state.createdAccounts ∧
      (rollbackOnError snapshot evm).substate = evm.substate := by
  unfold rollbackOnError
  split <;> exact ⟨rfl, rfl⟩

/-- A successful deposit of code keeps the created accounts and the substate of the frame. -/
theorem depositCode_createdAccounts {snapshot : TransactionState} {evm after : Evm fork Meter}
    (h : depositCode fork snapshot evm = .ok after) :
    after.state.createdAccounts = evm.state.createdAccounts ∧ after.substate = evm.substate := by
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  split at h
  · cases h
    split <;> exact ⟨rfl, rfl⟩
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ⟨createdAccounts_setCode (Base.mapError_ok_iff.mp hst), rfl⟩

/-- From Cancun, every successful call and creation keeps the created accounts of its start.

Each account it marks for deletion was marked before it started, or is created at its end.

The proof is by strong induction on the gas of the message, for calls and creations together. -/
theorem processMessage_deletesCreated [LawfulGasMeter Meter] (hfork : .dencun ≤ fork) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CreatedLe state ended.val.state ∧
          ∀ address ∈ ended.val.substate.accountsToDelete,
            address ∈ substate.accountsToDelete ∨
              address ∈ ended.val.state.createdAccounts) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreatedLe state ended.val.state ∧
          ∀ address ∈ ended.val.substate.accountsToDelete,
            address ∈ substate.accountsToDelete ∨
              address ∈ ended.val.state.createdAccounts) :=
  processMessage_rel (fork := fork) (Meter := Meter) (R := DeletesCreated) (Inv := fun _ => True)
    (M := fun _ state substate _ ended => CreatedLe state ended.state ∧
      ∀ address ∈ ended.substate.accountsToDelete,
        address ∈ substate.accountsToDelete ∨ address ∈ ended.state.createdAccounts)
    DeletesCreated.refl (fun hab hbc => hab.trans hbc) (fun _ _ => trivial)
    (fun _ _ _ => .of_eq rfl rfl) (fun _ h => deletesCreated_step hfork h)
    (fun _ _ => .of_eq rfl rfl) (fun h _ => deletesCreated_runPrecompile h)
    (fun {message state state1 substate substate1 _ ended} hstate hrun => by
      have hd := hrun trivial
      have h12 : state1.createdAccounts = state.createdAccounts ∧
          substate1.accountsToDelete = substate.accountsToDelete := by
        rcases hstate with ⟨rfl, rfl, -⟩ | ⟨-, hm, rfl⟩
        · exact ⟨createdAccounts_startState message state, rfl⟩
        · exact ⟨(TransactionState.createdAccounts_moveEther hm).trans
            (createdAccounts_startState message state), rfl⟩
      obtain ⟨hc, hs⟩ := rollbackOnError_createdAccounts state ended
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hc]
        exact hd.1 x (h12.1 ▸ hx)
      · rw [hs] at hx
        rw [hc]
        exact (hd.2 x hx).imp_left fun hx => h12.2 ▸ hx)
    (fun hp hm hd => by
      obtain ⟨hc, hs⟩ := depositCode_createdAccounts hd
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [hc]
        exact hm.1 x (createdLe_prepareCreation hp x hx)
      · rw [hs] at hx
        rw [hc]
        exact hm.2 x hx) n

/-- From Cancun, every successful call ends with the created accounts of its start, or more.

Each account it marks for deletion was marked before it started, or is created at its end.

That holds whether or not the call ends with an error. -/
theorem deletesCreated_processMessage [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    CreatedLe state ended.val.state ∧
      ∀ address ∈ ended.val.substate.accountsToDelete,
        address ∈ substate.accountsToDelete ∨ address ∈ ended.val.state.createdAccounts :=
  (processMessage_deletesCreated hfork message.gas).1 message state substate meter held rfl ended h

/-- From Cancun, every successful creation ends with the created accounts of its start, or more.

Each account it marks for deletion was marked before it started, or is created at its end.

That holds whether or not the creation ends with an error. -/
theorem deletesCreated_processCreateMessage [LawfulGasMeter Meter] (hfork : .dencun ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    CreatedLe state ended.val.state ∧
      ∀ address ∈ ended.val.substate.accountsToDelete,
        address ∈ substate.accountsToDelete ∨ address ∈ ended.val.state.createdAccounts :=
  (processMessage_deletesCreated hfork message.gas).2 message state substate meter held rfl ended h

end EthLib.Execution.Evm

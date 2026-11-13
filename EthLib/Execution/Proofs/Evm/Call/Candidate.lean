module

public import EthLib.Execution.Proofs.Evm.Call.Parent
public import EthLib.Execution.Proofs.State.Agreement
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: a message makes no new deployment candidate

A deployment candidate is an address with nonce 0 and no code, where a creation may deploy.

Whether a creation succeeds there depends on the account, so the block access list must name it.

Take a transaction state where every candidate was one in the block, or had its storage wiped.

Every call and every creation keeps that, whether its frame ends with an error or not.

A step never lowers a nonce, and gives code only to the address of a creation.

That address had its storage wiped when the creation started, and a rollback restores a snapshot.

Source: [EIP-7928, Scope and Inclusion][eip7928].

[eip7928]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (Account BlockState EMPTY_CODE_HASH StateError TransactionState)
open EthLib.Execution.State.TransactionState (NoNewCandidate)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A relation of states -/

/-- The second state has the block of the first, and every address that the first wiped.

Each address with nonce 0 and no code in it had both in the first, or had its storage wiped. -/
def KeepsCandidates (tx tx' : TransactionState) : Prop :=
  tx'.parent = tx.parent ∧ (∀ address, address ∈ tx.storageClears → address ∈ tx'.storageClears) ∧
    ∀ address, (tx'.getAccount address).nonce = 0 →
      (tx'.getAccount address).codeHash = EMPTY_CODE_HASH →
      address ∈ tx'.storageClears ∨
        ((tx.getAccount address).nonce = 0 ∧ (tx.getAccount address).codeHash = EMPTY_CODE_HASH)

/-- A state keeps its own candidates. -/
theorem KeepsCandidates.refl (tx : TransactionState) : KeepsCandidates tx tx :=
  ⟨rfl, fun _ h => h, fun _ hn hc => .inr ⟨hn, hc⟩⟩

/-- Two states in a row that each keep the candidates keep them together. -/
theorem KeepsCandidates.trans {a b c : TransactionState} (hab : KeepsCandidates a b)
    (hbc : KeepsCandidates b c) : KeepsCandidates a c :=
  ⟨hbc.1.trans hab.1, fun x hx => hbc.2.1 x (hab.2.1 x hx), fun x hn hc =>
    (hbc.2.2 x hn hc).elim .inl fun ⟨hn', hc'⟩ => (hab.2.2 x hn' hc').imp_left (hbc.2.1 x)⟩

/-- A state with the writes and the block of another keeps its candidates. -/
private theorem KeepsCandidates.of_sameWrites {tx tx' : TransactionState} (h : SameWrites tx' tx)
    (hp : tx'.parent = tx.parent) : KeepsCandidates tx tx' :=
  ⟨hp, fun _ hx => h.storageClears ▸ hx, fun x hn hc => .inr (h.getAccount hp x ▸ ⟨hn, hc⟩)⟩

/-- A change of one account keeps the candidates when it makes none there.

The new account has a nonce or code, or the address was wiped, or the old account had neither. -/
private theorem KeepsCandidates.modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account}
    (hf : ∀ updated, f (tx.getAccount address) = .ok updated → updated.nonce = 0 →
      updated.codeHash = EMPTY_CODE_HASH →
      address ∈ tx.storageClears ∨
        ((tx.getAccount address).nonce = 0 ∧ (tx.getAccount address).codeHash = EMPTY_CODE_HASH))
    (h : tx.modifyState fork address f = .ok tx') : KeepsCandidates tx tx' := by
  have hclears : ∀ x, x ∈ tx.storageClears → x ∈ tx'.storageClears := by
    obtain ⟨updated, -, rfl⟩ := TransactionState.modifyState_eq_ok_iff.mp h
    intro x hx
    split
    · simp [TransactionState.destroyAccount, TransactionState.destroyStorage,
        TransactionState.setAccount, TransactionState.recordAccountRead, hx]
    · exact hx
  obtain ⟨updated, hupd, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  refine ⟨TransactionState.parent_modifyState h, hclears, fun x hn hc => ?_⟩
  by_cases hx : x = address
  · subst hx
    rw [hself] at hn hc
    exact (hf updated hupd hn hc).imp_left (hclears x)
  · rw [hother x hx] at hn hc
    exact .inr ⟨hn, hc⟩

/-- A change of one account that keeps its nonce and its code keeps the candidates. -/
private theorem KeepsCandidates.modifyState_of_keeps {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (hf : ∀ account updated, f account = .ok updated →
      updated.nonce = account.nonce ∧ updated.codeHash = account.codeHash)
    (h : tx.modifyState fork address f = .ok tx') : KeepsCandidates tx tx' :=
  .modifyState (fun updated hupd hn hc => by
    obtain ⟨hn', hc'⟩ := hf _ _ hupd
    exact .inr ⟨hn' ▸ hn, hc' ▸ hc⟩) h

/-- A debit keeps the nonce and the code of an account. -/
private theorem debit_keeps {address : Address} {amount : U256} {account updated : Account}
    (h : Account.debit address amount account = .ok updated) :
    updated.nonce = account.nonce ∧ updated.codeHash = account.codeHash := by
  unfold Account.debit at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

/-- A credit keeps the nonce and the code of an account. -/
private theorem credit_keeps {address : Address} {amount : U256} {account updated : Account}
    (h : Account.credit address amount account = .ok updated) :
    updated.nonce = account.nonce ∧ updated.codeHash = account.codeHash := by
  unfold Account.credit at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

/-- A move of ether keeps the candidates. -/
private theorem KeepsCandidates.moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    KeepsCandidates tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (KeepsCandidates.modifyState_of_keeps (fun _ _ hf => debit_keeps hf) h1).trans
    (KeepsCandidates.modifyState_of_keeps (fun _ _ hf => credit_keeps hf) h2)

/-- A write of a balance keeps the candidates. -/
private theorem KeepsCandidates.setAccountBalance {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    KeepsCandidates tx tx' :=
  .modifyState_of_keeps (fun _ _ hf => by cases hf; exact ⟨rfl, rfl⟩) h

/-- A rise of a nonce keeps the candidates. -/
private theorem KeepsCandidates.incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : KeepsCandidates tx tx' :=
  .modifyState (fun _ hupd hn _ => by cases hupd; exact absurd hn (Nat.succ_ne_zero _)) h

/-- A successful move of the balance of a self-destructing account keeps the candidates. -/
private theorem KeepsCandidates.selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeepsCandidates tx tx' := by
  unfold Evm.selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (KeepsCandidates.moveEther h1).trans (KeepsCandidates.setAccountBalance h)
    · cases h
      exact KeepsCandidates.moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (KeepsCandidates.modifyState_of_keeps (fun _ _ hf => credit_keeps hf) h1).trans
      (KeepsCandidates.setAccountBalance h)

/-- A write of storage keeps the candidates. -/
private theorem KeepsCandidates.setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    KeepsCandidates tx tx' := by
  unfold TransactionState.setStorage at h
  split at h
  · cases h
  · cases h
    exact KeepsCandidates.refl tx

/-- A rollback to a snapshot on the same block keeps the candidates of the snapshot. -/
private theorem KeepsCandidates.restoreTxState {tx snapshot : TransactionState}
    (hp : tx.parent = snapshot.parent) : KeepsCandidates snapshot (tx.restoreTxState snapshot) :=
  .of_sameWrites (sameWrites_restoreTxState tx snapshot) hp

/-- A touch of an account keeps the candidates. -/
private theorem KeepsCandidates.touchAccount (tx : TransactionState) (address : Address) :
    KeepsCandidates tx (tx.touchAccount address) := by
  refine ⟨TransactionState.parent_touchAccount tx address, fun x hx => ?_, fun x hn hc => .inr ?_⟩
  · unfold TransactionState.touchAccount
    split
    · exact hx
    · exact hx
  · by_cases hne : x = address
    · subst hne
      rw [TransactionState.getAccount_touchAccount_self] at hn hc
      exact ⟨hn, hc⟩
    · rw [TransactionState.getAccount_touchAccount hne] at hn hc
      exact ⟨hn, hc⟩

/-- Under the condition on candidates, a state that keeps them meets it too. -/
theorem _root_.EthLib.Execution.State.TransactionState.NoNewCandidate.of_keepsCandidates
    {block : BlockState}
    {tx tx' : TransactionState} (hinv : NoNewCandidate block tx) (hk : KeepsCandidates tx tx') :
    NoNewCandidate block tx' := fun x hn hc =>
  (hk.2.2 x hn hc).elim .inl fun ⟨hn', hc'⟩ => (hinv x hn' hc').imp_left (hk.2.1 x)

/-! ## Starts, rollbacks and creations -/

/-- The state that a message enters keeps the candidates of the state it is sent from. -/
private theorem keepsCandidates_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (hentry : Entered fork message state substate entry entrySubstate) :
    KeepsCandidates state entry := by
  have hstart : KeepsCandidates state (startState fork message state) := by
    unfold startState
    split
    · exact .touchAccount state message.currentTarget
    · exact .refl state
  rcases hentry with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact hstart
  · exact hstart.trans (.moveEther hm)

/-- A rollback on error keeps the candidates of the snapshot, when the frame keeps them. -/
private theorem keepsCandidates_rollbackOnError {snapshot : TransactionState}
    {ended : Evm fork Meter} (hk : KeepsCandidates snapshot ended.state) :
    KeepsCandidates snapshot (rollbackOnError snapshot ended).state := by
  unfold rollbackOnError
  split
  · exact .restoreTxState hk.1
  · exact hk

/-- A preparation of a creation keeps the candidates, and wipes the storage of its address. -/
private theorem keepsCandidates_prepareCreation {state prepared : TransactionState}
    {address : Address} (hp : prepareCreation fork state address = .ok prepared) :
    KeepsCandidates state prepared ∧ address ∈ prepared.storageClears := by
  have hwipe : KeepsCandidates state ((state.destroyStorage address).markAccountCreated address) :=
    ⟨rfl, fun x hx => by simp [TransactionState.markAccountCreated,
      TransactionState.destroyStorage, hx], fun x hn hc => .inr ⟨hn, hc⟩⟩
  have hmem : address ∈ ((state.destroyStorage address).markAccountCreated address).storageClears :=
    by simp [TransactionState.markAccountCreated, TransactionState.destroyStorage]
  unfold prepareCreation at hp
  split at hp
  · have h := Base.mapError_ok_iff.mp hp
    have hk := KeepsCandidates.incrementNonce h
    exact ⟨hwipe.trans hk, hk.2.1 _ hmem⟩
  · cases hp
    exact ⟨hwipe, hmem⟩

/-- A write of code at a wiped address keeps the candidates. -/
private theorem keepsCandidates_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (hmem : address ∈ tx.storageClears)
    (h : tx.setCode fork address code = .ok tx') : KeepsCandidates tx tx' := by
  dsimp only [TransactionState.setCode] at h
  split at h
  · exact .modifyState (fun _ _ _ _ => .inl hmem) h
  · have hk := KeepsCandidates.modifyState (h := h) fun _ _ _ _ => .inl (by exact hmem)
    exact KeepsCandidates.trans ⟨rfl, fun _ hx => hx, fun _ hn hc => .inr ⟨hn, hc⟩⟩ hk

/-- A deposit of code keeps the candidates of the state before the creation.

The init code must keep those of the prepared state, and run at the address of the creation. -/
private theorem keepsCandidates_depositCode {state prepared : TransactionState} {address : Address}
    {evm after : Evm fork Meter} (hp : prepareCreation fork state address = .ok prepared)
    (hk : KeepsCandidates prepared evm.state) (ht : evm.message.currentTarget = address)
    (hd : depositCode fork state evm = .ok after) : KeepsCandidates state after.state := by
  obtain ⟨hprep, hmem⟩ := keepsCandidates_prepareCreation hp
  rcases (depositCode_cases hd).2.2 with hs | hs | hs
  · rw [hs]
    exact .restoreTxState (hk.1.trans hprep.1)
  · rw [hs]
    exact hprep.trans hk
  · exact (hprep.trans hk).trans (keepsCandidates_setCode (ht ▸ hk.2.1 _ hmem) hs)

/-! ## Steps of a frame -/

/-- A step that keeps the candidates, the message and the code. -/
def CandidateStep (a b : Evm fork Meter) : Prop :=
  KeepsCandidates a.state b.state ∧ b.message = a.message ∧ b.code = a.code

omit [GasMeter Meter] in
/-- A frame keeps its own candidates, message and code. -/
theorem CandidateStep.refl (evm : Evm fork Meter) : CandidateStep evm evm :=
  ⟨.refl _, rfl, rfl⟩

omit [GasMeter Meter] in
/-- Two steps that each keep the candidates, message and code keep them together. -/
theorem CandidateStep.trans {a b c : Evm fork Meter} (hab : CandidateStep a b)
    (hbc : CandidateStep b c) : CandidateStep a c :=
  ⟨hab.1.trans hbc.1, hbc.2.1.trans hab.2.1, hbc.2.2.trans hab.2.2⟩

omit [GasMeter Meter] in
/-- A step with the writes and the block of the frame before keeps its candidates. -/
private theorem CandidateStep.of_sameWrites {a b : Evm fork Meter}
    (hsw : SameWrites b.state a.state) (hp : b.state.parent = a.state.parent)
    (hm : b.message = a.message) (hc : b.code = a.code) : CandidateStep a b :=
  ⟨.of_sameWrites hsw hp, hm, hc⟩

omit [GasMeter Meter] in
/-- A step that keeps the message, state, substate and code keeps the candidates. -/
private theorem CandidateStep.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) :
    CandidateStep a b :=
  ⟨by rw [h.state]; exact .refl _, h.message, h.code⟩

omit [GasMeter Meter] in
/-- A move of the program counter keeps the candidates. -/
private theorem CandidateStep.advance {a b : Evm fork Meter} (h : CandidateStep a b)
    (n : Nat := 1) :
    CandidateStep a (Evm.advance b n) :=
  h

omit [GasMeter Meter] in
/-- A record of an account read keeps the candidates. -/
private theorem candStep_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    CandidateStep evm (recordAccountRead evm address) :=
  .of_sameWrites (SameWrites.recordAccountRead evm.state address) rfl rfl rfl

omit [GasMeter Meter] in
/-- A record of a storage read keeps the candidates. -/
private theorem candStep_recordStorageRead (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) : CandidateStep evm (recordStorageRead evm address key) :=
  .of_sameWrites (SameWrites.recordStorageRead evm.state address key) rfl rfl rfl

omit [GasMeter Meter] in
/-- An access to an address keeps the candidates. -/
private theorem candStep_accessAddress (evm : Evm fork Meter) (address : Address) :
    CandidateStep evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  rw [h]
  exact .refl _

omit [GasMeter Meter] in
/-- An access to a storage key keeps the candidates. -/
private theorem candStep_accessStorageKey (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) : CandidateStep evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  rw [h]
  exact .refl _

/-- An exceptional halt keeps the candidates. -/
private theorem candStep_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    CandidateStep evm (exceptionalHalt evm e) :=
  .of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

/-- A call that runs no message keeps the candidates. -/
private theorem candStep_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : CandidateStep evm after := by
  obtain ⟨_, -, rfl⟩ := skipCall_eq_ok h
  exact .of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

/-- A precompile keeps the candidates. -/
private theorem candStep_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : CandidateStep evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact candStep_exceptionalHalt evm .precompile
  · split at h
    · cases h
      exact candStep_exceptionalHalt evm _
    · cases h
      exact .of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl

/-- RETURN and REVERT keep the candidates. -/
private theorem candStep_returnOpStep {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some run) {evm after : Evm fork Meter}
    (h : run evm = .ok after) : CandidateStep evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» =>
    subst hstep
    exact .of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep
      exact .of_sameContext (revertStep_sameContext h)
    · cases hstep

/-- Each instruction that reads an account keeps the candidates. -/
private theorem candStep_accountStep {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some run) {evm after : Evm fork Meter}
    (h : run evm = .ok after) : CandidateStep evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
    simp only [hacc] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : CandidateStep e1 e2 := by
      have := candStep_accessAddress e1 (toAddressMasked w)
      rwa [hacc] at this
    exact ((((CandidateStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (.of_sameContext (chargeGas_sameContext h3))).trans
      (candStep_recordAccountRead _ _)).trans
      (.of_sameContext (pushWord_sameContext h4)) |>.advance
  case extcodesize =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
    simp only [hacc] at h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : CandidateStep e1 e2 := by
      have := candStep_accessAddress e1 (toAddressMasked w)
      rwa [hacc] at this
    exact ((((CandidateStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (.of_sameContext (chargeGas_sameContext h3))).trans
      (candStep_recordAccountRead _ _)).trans
      (.of_sameContext (pushWord_sameContext h5)) |>.advance
  case extcodecopy =>
    subst hstep
    obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
    simp only [hacc] at h
    obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, _, h⟩ := Base.bind_ok_iff.mp h
    cases h
    have ha : CandidateStep e4 e5 := by
      have := candStep_accessAddress e4 (toAddressMasked w)
      rwa [hacc] at this
    exact (((((((CandidateStep.of_sameContext (popWord_sameContext h1)).trans
      (.of_sameContext (popWord_sameContext h2))).trans
      (.of_sameContext (popWord_sameContext h3))).trans
      (.of_sameContext (popWord_sameContext h4))).trans ha).trans
      (.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
      (candStep_recordAccountRead _ _)).trans
      (CandidateStep.of_sameWrites ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl) |>.advance
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (candStep_recordAccountRead _ _).trans (.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep
      obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
      rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
      simp only [hacc] at h
      obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have ha : CandidateStep e1 e2 := by
        have := candStep_accessAddress e1 (toAddressMasked w)
        rwa [hacc] at this
      exact ((((CandidateStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
        (.of_sameContext (chargeGas_sameContext h3))).trans
        (candStep_recordAccountRead _ _)).trans
        (.of_sameContext (pushWord_sameContext h4)) |>.advance
    · cases hstep

/-- SLOAD keeps the candidates. -/
private theorem candStep_sloadStep {evm after : Evm fork Meter}
    (h : sloadStep evm = .ok after) : CandidateStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : CandidateStep e1 e2 := by
    have := candStep_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((CandidateStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (.of_sameContext (chargeGas_sameContext h3))).trans
    (candStep_recordStorageRead _ _ _)).trans
    (.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- SSTORE keeps the candidates. -/
private theorem candStep_sstoreStep {evm after : Evm fork Meter}
    (h : sstoreStep evm = .ok after) : CandidateStep evm after := by
  unfold Evm.sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : CandidateStep evm e2 :=
    .of_sameContext ((popWord_sameContext h1).trans (popWord_sameContext h2))
  dsimp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : CandidateStep evm
        (recordStorageRead e3 e2.message.currentTarget (U256.toBeBytes k)) := by
      have := candStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
      rw [hpair] at this
      exact (c2.trans this).trans (candStep_recordStorageRead _ _ _)
    simp only [hpair] at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : CandidateStep evm e5 :=
        ha.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
          ((chargeGas_sameContext h4).trans (chargeStateGas_sameContext h5))))
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact m5.trans ⟨.setStorage (Base.mapError_ok_iff.mp hst), rfl, rfl⟩
    · exact ha.trans (candStep_exceptionalHalt _ _)

/-- TSTORE keeps the candidates. -/
private theorem candStep_tstoreStep {evm after : Evm fork Meter}
    (h : tstoreStep evm = .ok after) : CandidateStep evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact (CandidateStep.of_sameContext ((popWord_sameContext h1).trans
      ((popWord_sameContext h2).trans (chargeGas_sameContext h3)))).trans
      ⟨⟨rfl, fun _ hx => hx, fun _ hn hc => .inr ⟨hn, hc⟩⟩, rfl, rfl⟩

/-- SELFDESTRUCT keeps the candidates, since it only moves ether. -/
private theorem candStep_selfdestructStep {evm after : Evm fork Meter}
    (h : selfdestructStep fork evm = .ok after) : CandidateStep evm after := by
  obtain ⟨word, -, paid, -, hpaid_static, hpaid_state, -, ⟨refund, finished⟩ | ⟨error, rfl⟩⟩ :=
    selfdestructStep_eq_ok h
  · have hpaid : CandidateStep evm paid :=
      CandidateStep.of_sameWrites
        (hpaid_state ▸ SameWrites.recordAccountRead evm.state (toAddressMasked word))
        (by rw [hpaid_state]; rfl) hpaid_static.message hpaid_static.code
    unfold finishSelfdestruct at finished
    split at finished
    · cases finished
    · obtain ⟨state, hst, finished⟩ := Base.bind_ok_iff.mp finished
      cases finished
      exact hpaid.trans ⟨.selfdestructTransfer (Base.mapError_ok_iff.mp hst), rfl, rfl⟩
  · have hpaid : CandidateStep evm paid :=
      CandidateStep.of_sameWrites
        (hpaid_state ▸ SameWrites.recordAccountRead evm.state (toAddressMasked word))
        (by rw [hpaid_state]; rfl) hpaid_static.message hpaid_static.code
    exact hpaid.trans (candStep_exceptionalHalt paid error)

/-- Each instruction that gives the next frame keeps the candidates. -/
private theorem candStep_instruction {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    CandidateStep evm after := by
  unfold Evm.instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact candStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact .of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact candStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact candStep_sloadStep h
    case sstore => subst hf; exact candStep_sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact .of_sameContext (tloadStep_sameContext h)
    · exact candStep_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, hm, hc, hs, -⟩ := logStep_eq_ok h
    exact ⟨by rw [hs]; exact .refl _, hm, hc⟩
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact candStep_selfdestructStep h

/-! ## Calls and creations sent by a step -/

/-- A child ends in a state that keeps the candidates of its caller. -/
def CandidateChild (caller : Evm fork Meter) (_message : Message fork)
    (child : Evm fork Meter) : Prop :=
  KeepsCandidates caller.state child.state

/-- Resolving a delegation keeps the candidates. -/
private theorem candStep_accessDelegation {evm after : Evm fork Meter}
    {address : Address} {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after)) : CandidateStep evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (candStep_accessAddress _ _).trans (candStep_recordAccountRead _ _)
  · cases h
    exact .refl _

/-- Paying for a call keeps the candidates. -/
private theorem candStep_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    CandidateStep evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((CandidateStep.of_sameContext (chargeGas_sameContext h1)).trans
      (.of_sameContext (chargeStateGas_sameContext h2))).trans
      (.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact .of_sameContext (chargeGas_sameContext h1)

omit [GasMeter Meter] in
/-- Popping the operands of a call keeps the candidates. -/
private theorem candStep_popCallOperands {kind : CallKind}
    {evm after : Evm fork Meter} {call : CallOperands}
    (h : popCallOperands kind evm = .ok (call, after)) : CandidateStep evm after := by
  have hs := (staticStep_popCallOperands h).1
  have hst : after.state = evm.state := by rw [popCallOperands_eq_ok h]
  exact ⟨by rw [hst]; exact .refl _, hs.message, hs.code⟩

/-- Taking in a child that keeps the candidates of the caller keeps them. -/
private theorem candStep_incorporateChild {caller child : Evm fork Meter}
    (hc : KeepsCandidates caller.state child.state) :
    CandidateStep caller (incorporateChild fork caller child) :=
  ⟨by rw [state_incorporateChild]; exact hc,
    message_incorporateChild caller child, code_incorporateChild caller child⟩

/-- The end of a call instruction keeps the candidates, when its child does. -/
private theorem candStep_finishCall {kind : CallKind} {call : CallOperands}
    {callee : Callee} {subCall newAccount expandBy : Nat} {evm : Evm fork Meter}
    {result : StepResult fork Meter}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    result.Keeps CandidateStep CandidateChild evm := by
  unfold Evm.finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : CandidateStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) :=
    .of_sameWrites (SameWrites.recordAccountRead evm.state evm.message.currentTarget) rfl rfl rfl
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact (pre.trans (.of_sameContext (sameContext_refillStateGas _ _))).trans
      (candStep_skipCall hs)
  · unfold Evm.genericCall at h
    dsimp only at h
    split at h
    · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
      exact (((pre.trans (.of_sameContext (sameContext_returnData _ .empty))).trans
        (.of_sameContext (sameContext_refillStateGas _ newAccount))).trans
        (candStep_skipCall hs))
    · cases h
      have callerStep : CandidateStep evm _ :=
        pre.trans (.of_sameContext (sameContext_returnData _ .empty))
      refine ⟨callerStep, fun child after hres hc => ?_⟩
      obtain ⟨e, h1, hpure⟩ := Base.bind_ok_iff.mp hres
      cases hpure
      refine callerStep.trans ((candStep_incorporateChild hc).trans
        (.of_sameContext (SameContext.trans ?_
          ((pushWord_sameContext h1).trans ⟨rfl, rfl, rfl, rfl⟩))))
      constructor <;> split <;> rfl

/-- A call instruction keeps the candidates, when its child does. -/
private theorem candStep_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : callStep kind evm = .ok result) :
    result.Keeps CandidateStep CandidateChild evm := by
  unfold Evm.callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 : CandidateStep evm e1 := candStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : CandidateStep e1 e2 := by
    have := candStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : CandidateStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (candStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : CandidateStep evm e4 := s3.trans (candStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact StepResult.Keeps.lift (R := CandidateStep) (C := CandidateChild)
        CandidateStep.trans (s4.trans (candStep_payCall h5)) (candStep_finishCall h)
    · exact s4.trans (candStep_exceptionalHalt _ _)
  · exact s3.trans (candStep_exceptionalHalt _ _)

/-- A launch of a creation keeps the candidates, when its child does. -/
private theorem candStep_launchCreate {evm : Evm fork Meter} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Meter}
    (h : launchCreate evm value initCode salt = .ok result) :
    result.Keeps CandidateStep CandidateChild evm := by
  unfold Evm.launchCreate at h
  dsimp only at h
  have pre : CandidateStep evm
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    (CandidateStep.of_sameContext (sameContext_returnData evm .empty)).trans
      (candStep_recordAccountRead _ _)
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    exact pre.trans (candStep_skipCall hs)
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 : CandidateStep evm (recordAccountRead (accessAddress (recordAccountRead
      { evm with returnData := .empty } evm.message.currentTarget) address).2 address) :=
    (pre.trans (candStep_accessAddress _ address)).trans (candStep_recordAccountRead _ address)
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have c2 : CandidateStep evm e2 := c0.trans (.of_sameContext
      ((chargeStateGas_sameContext h1).trans (chargeGas_sameContext h2)))
    have ms : CandidateStep evm { e2 with state } :=
      c2.trans ⟨.incrementNonce (Base.mapError_ok_iff.mp hst), rfl, rfl⟩
    split at hr
    · cases hr
      have md : CandidateStep evm { e2 with state, gas := GasMeter.drain e2.gas } :=
        ms.trans (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩)
      refine ⟨md, fun child after hres hc => ?_⟩
      obtain ⟨e, hpush, hpure⟩ := Base.bind_ok_iff.mp hres
      cases hpure
      refine md.trans ((candStep_incorporateChild hc).trans
        (.of_sameContext (SameContext.trans ?_
          ((pushWord_sameContext hpush).trans ⟨rfl, rfl, rfl, rfl⟩))))
      constructor <;> split <;> rfl
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      exact ms.trans (.of_sameContext ((sameContext_refillStateGas _ _).trans
        ((pushWord_sameContext h3).trans ⟨rfl, rfl, rfl, rfl⟩)))
  · exact c0.trans (candStep_exceptionalHalt _ _)

/-- CREATE and CREATE2 keep the candidates, when their child does. -/
private theorem candStep_createStep {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (h : createStep create2 evm = .ok result) :
    result.Keeps CandidateStep CandidateChild evm := by
  obtain ⟨_, _, _, _, _, _, -, sc, -, -, -, launched⟩ := createStep_eq_ok h
  exact StepResult.Keeps.lift (R := CandidateStep) (C := CandidateChild)
    CandidateStep.trans (.of_sameContext sc) (candStep_launchCreate launched)

/-- An instruction that may send a message keeps the candidates, when its child does. -/
private theorem candStep_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : result.Keeps CandidateStep CandidateChild evm := by
  unfold Evm.messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact candStep_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact candStep_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact candStep_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact candStep_createStep h
         · cases hrun)

/-- A step keeps the candidates, its message and its code, when the child it sends does. -/
theorem step_keepsCandidates {evm : Evm fork Meter} {result : StepResult fork Meter}
    (h : step fork evm = .ok result) : result.Keeps CandidateStep CandidateChild evm := by
  unfold Evm.step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i run hop
        cases hr : run evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact candStep_instruction hop hr
      · split at h
        · rename_i hcall
          exact candStep_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact .of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

/-! ## Messages -/

/-- What a call keeps: the candidates of the state it is sent from, and its message. -/
private def CallKeeps (message : Message fork) (state : TransactionState) (_substate : Substate)
    (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsCandidates state ended.state ∧ ended.message = message

/-- What a creation keeps: the candidates of the state it is sent from. -/
private def CreateKeeps (_message : Message fork) (state : TransactionState)
    (_substate : Substate) (_meter : Meter) (ended : Evm fork Meter) : Prop :=
  KeepsCandidates state ended.state

/-- By induction on gas, calls and creations keep the candidates of the state they start from. -/
private theorem keepsCandidates_induction [LawfulGasMeter Meter] (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        CallKeeps message state substate meter ended.val) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Meter)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CreateKeeps message state substate meter ended.val) := by
  refine processMessage_rel_byKind (R := CandidateStep) (Inv := fun _ => True)
    (Mcall := CallKeeps) (Mcreate := CreateKeeps)
    CandidateStep.refl CandidateStep.trans (fun _ _ => trivial) ?_ ?_ ?_ ?_ ?_ ?_ n
  · intro evm error _
    exact candStep_exceptionalHalt evm error
  · intro evm result _ h
    refine (step_keepsCandidates h).of_child fun {caller message child} hc => ?_
    unfold ChildRelByKind ChildRel at hc
    unfold CandidateChild
    rcases ht : message.target with _ | target
    · simp only [ht] at hc
      exact hc
    · simp only [ht] at hc
      exact hc.1
  · intro evm _
    exact .of_sameContext ⟨rfl, rfl, rfl, rfl⟩
  · intro address evm after h _
    exact candStep_runPrecompile h
  · intro message state entry substate entrySubstate meter ended hentered hrun
    have hk := hrun trivial
    exact ⟨keepsCandidates_rollbackOnError ((keepsCandidates_entered hentered).trans hk.1),
      (message_rollbackOnError state ended).trans hk.2.1⟩
  · intro message state prepared substate meter evm after hprep hmcall hdep
    exact keepsCandidates_depositCode hprep hmcall.1 (congrArg (·.currentTarget) hmcall.2) hdep

/-- A call that returns a frame keeps the candidates of the state it starts from. -/
theorem keepsCandidates_processMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended) :
    KeepsCandidates state ended.val.state :=
  ((keepsCandidates_induction message.gas).1 message state substate meter held rfl ended h).1

/-- A creation that returns a frame keeps the candidates of the state it starts from. -/
theorem keepsCandidates_processCreateMessage [LawfulGasMeter Meter] {message : Message fork}
    {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    KeepsCandidates state ended.val.state :=
  (keepsCandidates_induction message.gas).2 message state substate meter held rfl ended h

/-- A call that returns a frame, from a state with no new candidate, ends with none.

A new candidate is still allowed at an address whose storage was wiped. -/
theorem processMessage_noNewCandidate [LawfulGasMeter Meter] {block : BlockState}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hinv : NoNewCandidate block state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    NoNewCandidate block ended.val.state :=
  hinv.of_keepsCandidates (keepsCandidates_processMessage h)

/-- A creation that returns a frame, from a state with no new candidate, ends with none.

A new candidate is still allowed at an address whose storage was wiped. -/
theorem processCreateMessage_noNewCandidate [LawfulGasMeter Meter] {block : BlockState}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Meter // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hinv : NoNewCandidate block state)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    NoNewCandidate block ended.val.state :=
  hinv.of_keepsCandidates (keepsCandidates_processCreateMessage h)

end EthLib.Execution.Evm

module

public import EthLib.Execution.Proofs.Evm.Call.Nonce
public import EthLib.Execution.Proofs.Evm.Call.Run

/-!
# Proofs: each write of a transaction state keeps each nonce or code

A write keeps each nonce or code when it lowers no nonce, and each account with one keeps one.

The writes below do on any state, with two exceptions.

New code needs a nonce at its account, or neither a nonce nor code there.

A rollback or a deposit of code needs a frame that kept them.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (Account EMPTY_ACCOUNT EMPTY_CODE_HASH StateError TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## Accounts with a nonce or code -/

/-- Whether the account at `address` in `tx` has a positive nonce or holds code. -/
def HasNonceOrCode (tx : TransactionState) (address : Address) : Prop :=
  1 ≤ (tx.getAccount address).nonce ∨ (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH

/-- An account with a nonce or code is not the empty account. -/
theorem HasNonceOrCode.ne_empty {tx : TransactionState} {address : Address}
    (h : HasNonceOrCode tx address) : tx.getAccount address ≠ EMPTY_ACCOUNT := by
  intro hempty
  rcases h with hn | hc
  · rw [hempty] at hn
    exact Nat.not_succ_le_zero 0 hn
  · rw [hempty] at hc
    exact hc rfl

/-- Two states with the same account at `address` agree on whether it has a nonce or code. -/
theorem HasNonceOrCode.congr {tx tx' : TransactionState} {address : Address}
    (h : tx'.getAccount address = tx.getAccount address) :
    HasNonceOrCode tx' address ↔ HasNonceOrCode tx address := by
  simp only [HasNonceOrCode, h]

/-- Whether `tx'` lowers no nonce of `tx`, and keeps a nonce or code wherever `tx` has one. -/
def KeepsNonceOrCode (tx tx' : TransactionState) : Prop :=
  NonceLe tx tx' ∧ ∀ address, HasNonceOrCode tx address → HasNonceOrCode tx' address

/-- Every state keeps its own nonces, and a nonce or code wherever it has one. -/
theorem KeepsNonceOrCode.refl (tx : TransactionState) : KeepsNonceOrCode tx tx :=
  ⟨NonceLe.refl tx, fun _ h => h⟩

/-- Two transitions that lower no nonce and keep each nonce or code compose. -/
theorem KeepsNonceOrCode.trans {a b c : TransactionState}
    (hab : KeepsNonceOrCode a b) (hbc : KeepsNonceOrCode b c) : KeepsNonceOrCode a c :=
  ⟨hab.1.trans hbc.1, fun address h => hbc.2 address (hab.2 address h)⟩

/-- A state with the accounts of another keeps each nonce or code of it. -/
theorem keepsNonceOrCode_of_getAccountOptional {tx tx' : TransactionState}
    (h : ∀ address, tx'.getAccountOptional address = tx.getAccountOptional address) :
    KeepsNonceOrCode tx tx' :=
  ⟨NonceLe.of_getAccountOptional h, fun address hc =>
    (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [h])).mpr hc⟩

/-- Same writes on the same block lower no nonce and keep each nonce or code. -/
theorem SameWrites.keepsNonceOrCode {tx snapshot : TransactionState}
    (h : SameWrites snapshot tx) (hp : snapshot.parent = tx.parent) :
    KeepsNonceOrCode tx snapshot := by
  refine ⟨fun address => ?_, fun address hnc => ?_⟩
  · rw [h.getAccount hp address]
    exact Nat.le_refl _
  · exact (HasNonceOrCode.congr (h.getAccount hp address)).mpr hnc

/-! ## The writes of the state

A write of storage, transient storage or a balance keeps the nonce and the code of every account.
-/

/-- A change of an account that keeps its nonce and its code keeps each nonce or code.

From Paris, such a change may delete an empty account, which had no nonce and no code. -/
theorem keepsNonceOrCode_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.nonce = (tx.getAccount address).nonce ∧
        account.codeHash = (tx.getAccount address).codeHash) :
    KeepsNonceOrCode tx tx' := by
  obtain ⟨account, hf, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  obtain ⟨hn, hc⟩ := keeps account hf
  -- The changed account reads with the nonce and the code hash it had; the others are kept.
  have hacc : ∀ other, (tx'.getAccount other).nonce = (tx.getAccount other).nonce ∧
      (tx'.getAccount other).codeHash = (tx.getAccount other).codeHash := by
    intro other
    by_cases hne : other = address
    · subst hne
      rw [hself]
      exact ⟨hn, hc⟩
    · rw [hother other hne]
      exact ⟨rfl, rfl⟩
  refine ⟨fun other => (hacc other).1 ▸ Nat.le_refl _, fun other hnc => ?_⟩
  unfold HasNonceOrCode
  rw [(hacc other).1, (hacc other).2]
  exact hnc

/-- A write of storage keeps each nonce or code. -/
theorem keepsNonceOrCode_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    KeepsNonceOrCode tx tx' :=
  keepsNonceOrCode_of_getAccountOptional fun _ => TransactionState.getAccountOptional_setStorage h

/-- A write of transient storage keeps each nonce or code. -/
theorem keepsNonceOrCode_setTransientStorage (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    KeepsNonceOrCode tx (tx.setTransientStorage address key value) :=
  keepsNonceOrCode_of_getAccountOptional fun _ => rfl

/-- A touch of an account keeps each nonce or code. -/
theorem keepsNonceOrCode_touchAccount (tx : TransactionState) (address : Address) :
    KeepsNonceOrCode tx (tx.touchAccount address) := by
  refine ⟨nonceLe_touchAccount tx address, fun other hnc => (HasNonceOrCode.congr ?_).mpr hnc⟩
  by_cases hne : other = address
  · subst hne
    exact TransactionState.getAccount_touchAccount_self tx other
  · exact TransactionState.getAccount_touchAccount hne

/-- A credit of ether keeps each nonce or code. -/
theorem keepsNonceOrCode_createEther {tx tx' : TransactionState} {target : Address}
    {amount : U256} (h : tx.createEther fork target amount = .ok tx') :
    KeepsNonceOrCode tx tx' := by
  refine ⟨nonceLe_createEther h, fun other hc => ?_⟩
  -- Every account keeps its nonce and its code hash.
  obtain ⟨-, hn, hcode⟩ := TransactionState.getAccount_createEther h other
  rcases hc with h1 | h2
  · exact .inl (hn ▸ h1)
  · exact .inr (hcode ▸ h2)

/-- A new balance keeps each nonce or code. -/
theorem keepsNonceOrCode_setAccountBalance {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    KeepsNonceOrCode tx tx' :=
  keepsNonceOrCode_modifyState h fun _ hf => by cases hf; exact ⟨rfl, rfl⟩

/-- A move of ether keeps each nonce or code. -/
theorem keepsNonceOrCode_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    KeepsNonceOrCode tx tx' := by
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  -- The debit keeps the nonce and the code hash of the sender.
  --
  -- The credit of the recipient is a credit of ether.
  refine (keepsNonceOrCode_modifyState h1 fun account hf => ?_).trans
    (keepsNonceOrCode_createEther h2)
  unfold Account.debit at hf
  split at hf <;> cases hf
  exact ⟨rfl, rfl⟩

/-- The move of the balance of an account by SELFDESTRUCT keeps each nonce or code. -/
theorem keepsNonceOrCode_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    KeepsNonceOrCode tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (keepsNonceOrCode_moveEther h1).trans (keepsNonceOrCode_setAccountBalance h)
    · cases h
      exact keepsNonceOrCode_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (keepsNonceOrCode_createEther h1).trans (keepsNonceOrCode_setAccountBalance h)

/-- The rise of a nonce keeps each nonce or code. -/
theorem keepsNonceOrCode_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : KeepsNonceOrCode tx tx' := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h
  refine ⟨nonceLe_incrementNonce h, fun other hnc => ?_⟩
  by_cases hne : other = address
  · -- The raised nonce is positive, so the rise leaves a nonce at that account.
    subst hne
    left
    rw [hself]
    exact Nat.succ_le_of_lt (Nat.succ_pos _)
  · exact (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [hother other hne])).mpr
      hnc

/-- New code at an account with a nonce keeps each nonce or code. -/
theorem keepsNonceOrCode_setCode {tx tx' : TransactionState} {address : Address}
    -- A creation from Spurious Dragon meets the nonce hypothesis: it sets the nonce first.
    {code : ByteArray} (hnonce : 1 ≤ (tx.getAccount address).nonce)
    (h : tx.setCode fork address code = .ok tx') : KeepsNonceOrCode tx tx' := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_setCode h
  refine ⟨nonceLe_setCode h, fun other hnc => ?_⟩
  by_cases hne : other = address
  · -- The account keeps its positive nonce, so new code leaves a nonce there.
    subst hne
    left
    rw [hself]
    exact hnonce
  · exact (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [hother other hne])).mpr
      hnc

/-- New code at an account with neither a nonce nor code keeps each nonce or code.

That account had none to keep, and every other account stays. -/
theorem keepsNonceOrCode_setCode_of_not_hasNonceOrCode {tx tx' : TransactionState}
    -- A delegation meets this hypothesis when it finds its authority with neither.
    {address : Address} {code : ByteArray} (hplain : ¬HasNonceOrCode tx address)
    (h : tx.setCode fork address code = .ok tx') : KeepsNonceOrCode tx tx' := by
  obtain ⟨-, hother⟩ := TransactionState.getAccount_setCode h
  refine ⟨nonceLe_setCode h, fun other hnc => ?_⟩
  by_cases hne : other = address
  · subst hne
    exact absurd hnc hplain
  · exact (HasNonceOrCode.congr (by unfold TransactionState.getAccount; rw [hother other hne])).mpr
      hnc

/-! ## The writes of a message -/

/-- The start of a creation keeps each nonce or code. -/
theorem keepsNonceOrCode_prepareCreation {state prepared : TransactionState} {address : Address}
    (h : prepareCreation fork state address = .ok prepared) : KeepsNonceOrCode state prepared := by
  unfold prepareCreation at h
  -- The wipe of storage and the record of the creation keep every account.
  have h0 : KeepsNonceOrCode state ((state.destroyStorage address).markAccountCreated address) :=
    keepsNonceOrCode_of_getAccountOptional fun _ => rfl
  split at h
  · exact h0.trans (keepsNonceOrCode_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact h0

/-- A deposit of code keeps each nonce or code of the snapshot before a creation.

The frame of the creation must keep them, on the block of the snapshot.

The address of the creation must have a positive nonce when the frame ends. -/
theorem keepsNonceOrCode_depositCode {snapshot : TransactionState} {evm after : Evm fork Meter}
    (hk : KeepsNonceOrCode snapshot evm.state) (hp : evm.state.parent = snapshot.parent)
    (hnonce : 1 ≤ (evm.state.getAccount evm.message.currentTarget).nonce)
    (h : depositCode fork snapshot evm = .ok after) :
    KeepsNonceOrCode snapshot after.state := by
  rcases (depositCode_cases h).2.2 with hs | hs | hs
  · -- The restored state has the accounts of the snapshot.
    rw [hs]
    exact (sameWrites_restoreTxState evm.state snapshot).keepsNonceOrCode hp
  · rw [hs]
    exact hk
  · -- The code goes to the address of the creation, whose nonce is positive.
    exact hk.trans (keepsNonceOrCode_setCode hnonce hs)

/-- The start state of a message keeps each nonce or code. -/
theorem keepsNonceOrCode_startState (message : Message fork) (state : TransactionState) :
    KeepsNonceOrCode state (startState fork message state) := by
  unfold startState
  split
  · -- The start state touches at most the target.
    exact keepsNonceOrCode_touchAccount state message.currentTarget
  · exact .refl _

/-- The state that a message enters keeps each nonce or code of the state it is sent from. -/
theorem keepsNonceOrCode_entered {message : Message fork} {state entry : TransactionState}
    {substate entrySubstate : Substate}
    (h : Entered fork message state substate entry entrySubstate) :
    KeepsNonceOrCode state entry := by
  rcases h with ⟨-, rfl, -⟩ | ⟨-, hm, -⟩
  · exact keepsNonceOrCode_startState message state
  · exact (keepsNonceOrCode_startState message state).trans (keepsNonceOrCode_moveEther hm)

/-- A rollback to a snapshot keeps each nonce or code of it, when the frame kept them.

The frame must end on the block of the snapshot. -/
theorem keepsNonceOrCode_rollbackOnError {snapshot : TransactionState} {ended : Evm fork Meter}
    (hk : KeepsNonceOrCode snapshot ended.state) (hp : ended.state.parent = snapshot.parent) :
    KeepsNonceOrCode snapshot (rollbackOnError snapshot ended).state := by
  unfold rollbackOnError
  split
  · -- The restored state has the accounts of the snapshot.
    exact (sameWrites_restoreTxState ended.state snapshot).keepsNonceOrCode hp
  · exact hk

end EthLib.Execution.Evm

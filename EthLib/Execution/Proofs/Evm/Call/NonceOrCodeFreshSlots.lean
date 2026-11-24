module

public import EthLib.Execution.Proofs.Evm.Call.Rebuild
public import EthLib.Execution.Proofs.Evm.Instructions.StorageStateGas

/-!
# Proofs: the fresh slots of the accounts where code can run

The slots counted here are the fresh slots of the accounts with a nonce or code.

Source: [EIP-8037][eip8037], the state gas of a new slot and its refill.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open EthLib.Execution.State (Account BlockState EMPTY_ACCOUNT StateError TransactionState)
open GasCosts

variable {fork : Fork}

instance instDecidableHasNonceOrCode (tx : TransactionState) (address : Address) :
    Decidable (HasNonceOrCode tx address) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The fresh slots of the accounts with a nonce or code.

From Spurious Dragon, code runs only at an account with a nonce or code.

So only such an account writes its storage. -/
def nonceOrCodeFreshSlots (tx : TransactionState) : Finset (Address × Bytes32) :=
  -- A slot is fresh when its word was zero before the transaction and is not zero now.
  tx.freshSlots.filter fun slot => HasNonceOrCode tx slot.1

/-- A slot is counted exactly when its account has a nonce or code and the slot is fresh. -/
theorem mem_nonceOrCodeFreshSlots {tx : TransactionState} {address : Address} {key : Bytes32} :
    (address, key) ∈ nonceOrCodeFreshSlots tx ↔ HasNonceOrCode tx address ∧
      tx.getStorageOriginal address key = 0 ∧ tx.getStorage address key ≠ 0 := by
  simp only [nonceOrCodeFreshSlots, Finset.mem_filter, TransactionState.mem_freshSlots]
  tauto

/-- Two states count the same slots when they agree where an account has a nonce or code.

They must agree on which accounts have a nonce or code.

At each such account, they must agree on every word, now and before the transaction. -/
theorem nonceOrCodeFreshSlots_congr {tx tx' : TransactionState}
    (hcode : ∀ address, HasNonceOrCode tx' address ↔ HasNonceOrCode tx address)
    (hwords : ∀ address, HasNonceOrCode tx address → ∀ key,
      tx'.getStorage address key = tx.getStorage address key ∧
        tx'.getStorageOriginal address key = tx.getStorageOriginal address key) :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  ext ⟨address, key⟩
  rw [mem_nonceOrCodeFreshSlots, mem_nonceOrCodeFreshSlots, hcode address]
  by_cases hc : HasNonceOrCode tx address
  · -- At an account with a nonce or code, both states hold the same words.
    obtain ⟨h1, h2⟩ := hwords address hc key
    rw [h1, h2]
  · simp only [hc, false_and]

/-- A transaction with no write counts no slot. -/
theorem nonceOrCodeFreshSlots_ofBlock (block : BlockState) :
    nonceOrCodeFreshSlots (.ofBlock block) = ∅ := by
  ext slot
  simp [nonceOrCodeFreshSlots, TransactionState.freshSlots_ofBlock]

/-- A state with more reads counts the same slots. -/
theorem nonceOrCodeFreshSlots_of_readsMore {tx tx' : TransactionState} (h : tx.ReadsMore tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  rw [h.rest]
  rfl

/-- A write of transient storage counts the same slots. -/
theorem nonceOrCodeFreshSlots_setTransientStorage (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    nonceOrCodeFreshSlots (tx.setTransientStorage address key value) =
      nonceOrCodeFreshSlots tx := by
  rfl

/-- A storage write at an account with a nonce or code changes the count as the fresh slots. -/
theorem card_nonceOrCodeFreshSlots_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (hcode : HasNonceOrCode tx address)
    (h : tx.setStorage address key value = .ok tx') :
    ((nonceOrCodeFreshSlots tx').card : Int) - (nonceOrCodeFreshSlots tx).card =
      (tx'.freshSlots.card : Int) - tx.freshSlots.card := by
  -- The write keeps every account.
  have hacc : ∀ other, tx'.getAccount other = tx.getAccount other := by
    intro other
    simp only [TransactionState.getAccount, TransactionState.getAccountOptional_setStorage h]
  have hfilter : nonceOrCodeFreshSlots tx' =
      tx'.freshSlots.filter fun slot => HasNonceOrCode tx slot.1 :=
    Finset.filter_congr fun slot _ => HasNonceOrCode.congr (hacc slot.1)
  have hmem : (address, key) ∈ nonceOrCodeFreshSlots tx ↔ (address, key) ∈ tx.freshSlots := by
    simp only [nonceOrCodeFreshSlots, Finset.mem_filter, hcode, and_true]
  -- The count changes at the slot of the write as the fresh slots do.
  have hset : nonceOrCodeFreshSlots tx' =
      if tx.getStorageOriginal address key = 0 ∧ value ≠ 0 then
        insert (address, key) (nonceOrCodeFreshSlots tx)
      else (nonceOrCodeFreshSlots tx).erase (address, key) := by
    rw [hfilter, TransactionState.freshSlots_setStorage h]
    split_ifs <;> ext ⟨other, otherKey⟩ <;> by_cases hs : other = address ∧ otherKey = key
    · obtain ⟨rfl, rfl⟩ := hs
      simp [nonceOrCodeFreshSlots, hcode]
    · simp [nonceOrCodeFreshSlots, hs]
    · obtain ⟨rfl, rfl⟩ := hs
      simp
    · simp [nonceOrCodeFreshSlots, hs]
  rw [hset, TransactionState.card_freshSlots_setStorage h]
  rw [TransactionState.mem_freshSlots] at hmem
  clear hset hfilter hacc h
  by_cases hin : (address, key) ∈ nonceOrCodeFreshSlots tx
  · -- The slot was counted: the write keeps it counted, or clears it.
    have hpos : 0 < (nonceOrCodeFreshSlots tx).card := Finset.card_pos.mpr ⟨_, hin⟩
    split_ifs <;> simp_all [Finset.insert_eq_of_mem, Finset.card_erase_of_mem, -Finset.card_pos]
    omega
  · -- The slot was not counted: the write makes it counted, or leaves it out.
    split_ifs <;> simp_all [Finset.card_insert_of_notMem, Finset.erase_eq_of_notMem]
    omega

/-- From Glamsterdam, the state gas of a storage write, net of its refill, pays for its slots.

The write is at an account with a nonce or code.

Its net state gas is the state gas of a new slot times the change in the counted slots. -/
theorem sstoreStateGas_sub_sstoreStateRefill_of_hasNonceOrCode (h : fork ≥ .glamsterdam)
    {tx tx' : TransactionState} {address : Address} {key : Bytes32} {new : U256}
    (hcode : HasNonceOrCode tx address) (hw : tx.setStorage address key new = .ok tx') :
    (sstoreStateGas fork (tx.getStorageOriginal address key) (tx.getStorage address key) new :
        Int) -
      sstoreStateRefill fork (tx.getStorageOriginal address key) (tx.getStorage address key) new =
      STORAGE_SET_STATE_GAS *
        (((nonceOrCodeFreshSlots tx').card : Int) - (nonceOrCodeFreshSlots tx).card) := by
  rw [card_nonceOrCodeFreshSlots_setStorage hcode hw]
  exact sstoreStateGas_sub_sstoreStateRefill h hw

/-- A change of an account keeps every word of an account with a nonce or code after it. -/
private theorem getStorage_modifyState_of_hasNonceOrCode {tx tx' : TransactionState}
    {address other : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') (hc : HasNonceOrCode tx' other) (key : Bytes32) :
    tx'.getStorage other key = tx.getStorage other key := by
  -- A deleted account reads as the empty account, which has no nonce or code.
  have hkept : ¬(other = address ∧ tx'.getAccountOptional address = none) := by
    rintro ⟨rfl, hnone⟩
    exact hc.ne_empty (by simp only [TransactionState.getAccount, hnone, Option.getD_none])
  rw [TransactionState.getStorage_modifyState h]
  simp only [hkept, ↓reduceIte]

/-- A change of an account counts the same slots when it keeps which accounts have a nonce or code.
-/
private theorem nonceOrCodeFreshSlots_modifyState_of_iff {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx')
    (hcode : ∀ other, HasNonceOrCode tx' other ↔ HasNonceOrCode tx other) :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeFreshSlots_congr hcode fun other hc key =>
    ⟨getStorage_modifyState_of_hasNonceOrCode h ((hcode other).mpr hc) key,
      by rw [TransactionState.getStorageOriginal_modifyState h]⟩

/-- A debit keeps the nonce and the code. -/
private theorem keeps_debit (address : Address) (amount : U256) (account account' : Account)
    (h : Account.debit address amount account = .ok account') :
    account'.nonce = account.nonce ∧ account'.codeHash = account.codeHash := by
  unfold Account.debit at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

/-- A credit keeps the nonce and the code. -/
private theorem keeps_credit (address : Address) (amount : U256) (account account' : Account)
    (h : Account.credit address amount account = .ok account') :
    account'.nonce = account.nonce ∧ account'.codeHash = account.codeHash := by
  unfold Account.credit at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- A change of an account that keeps its nonce and its code counts the same slots.

From Paris, such a change may delete an empty account, whose slots are not counted. -/
theorem nonceOrCodeFreshSlots_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.nonce = (tx.getAccount address).nonce ∧
        account.codeHash = (tx.getAccount address).codeHash) :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  obtain ⟨account, hf, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  refine nonceOrCodeFreshSlots_modifyState_of_iff h fun other => ?_
  by_cases ho : other = address
  · -- The changed account keeps its nonce and its code.
    subst ho
    obtain ⟨hn, hh⟩ := keeps account hf
    simp only [HasNonceOrCode, hself, hn, hh]
  · exact HasNonceOrCode.congr (hother other ho)

/-- A move of ether counts the same slots. -/
theorem nonceOrCodeFreshSlots_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  unfold TransactionState.moveEther at h
  cases h1 : tx.modifyState fork sender (Account.debit sender amount) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok mid =>
    -- The debit and the credit each keep every nonce and every code.
    simp only [h1, bind, Except.bind] at h
    rw [nonceOrCodeFreshSlots_modifyState h fun _ => keeps_credit _ _ _ _,
      nonceOrCodeFreshSlots_modifyState h1 fun _ => keeps_debit _ _ _ _]

/-- The move of the balance of an account that SELFDESTRUCT destroys counts the same slots. -/
theorem nonceOrCodeFreshSlots_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  -- A new balance keeps the nonce and the code.
  have hbal : ∀ (state state' : TransactionState) (address : Address) (amount : U256),
      state.setAccountBalance fork address amount = .ok state' →
        nonceOrCodeFreshSlots state' = nonceOrCodeFreshSlots state :=
    fun _ _ _ _ hs => nonceOrCodeFreshSlots_modifyState hs fun _ hf => by
      cases hf
      exact ⟨rfl, rfl⟩
  unfold selfdestructTransfer at h
  split at h
  · -- From Cancun, the balance moves, and may then be set to zero.
    cases h1 : tx.moveEther fork originator beneficiary (tx.getAccount originator).balance with
    | error e => simp [h1, bind, Except.bind] at h
    | ok mid =>
      simp only [h1, bind, Except.bind] at h
      rw [← nonceOrCodeFreshSlots_moveEther h1]
      split at h
      · exact hbal _ _ _ _ h
      · cases h
        rfl
  · -- Before Cancun, the beneficiary gets the balance, and the account then has none.
    cases h1 : tx.createEther fork beneficiary (tx.getAccount originator).balance with
    | error e => simp [h1, bind, Except.bind] at h
    | ok mid =>
      simp only [h1, bind, Except.bind] at h
      rw [hbal _ _ _ _ h]
      exact nonceOrCodeFreshSlots_modifyState h1 fun _ => keeps_credit _ _ _ _

/-- The rise of the nonce of an account with a nonce or code counts the same slots. -/
theorem nonceOrCodeFreshSlots_incrementNonce {tx tx' : TransactionState} {address : Address}
    (hcode : HasNonceOrCode tx address) (h : tx.incrementNonce fork address = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h
  refine nonceOrCodeFreshSlots_modifyState_of_iff h fun other => ?_
  by_cases ho : other = address
  · -- The account keeps a nonce.
    subst ho
    exact iff_of_true (Or.inl (by rw [hself]; exact Nat.le_add_left 1 _)) hcode
  · exact HasNonceOrCode.congr (by simp only [TransactionState.getAccount, hother other ho])

/-- New code at an account with a nonce counts the same slots. -/
theorem nonceOrCodeFreshSlots_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (hnonce : 1 ≤ (tx.getAccount address).nonce)
    (h : tx.setCode fork address code = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_setCode h
  have hcode : ∀ other, HasNonceOrCode tx' other ↔ HasNonceOrCode tx other := by
    intro other
    by_cases ho : other = address
    · -- The account keeps its nonce.
      subst ho
      exact iff_of_true (Or.inl (by rw [hself]; exact hnonce)) (Or.inl hnonce)
    · exact HasNonceOrCode.congr (by simp only [TransactionState.getAccount, hother other ho])
  -- Storing the code changes no account and no word.
  dsimp only [TransactionState.setCode] at h
  split at h <;> exact (nonceOrCodeFreshSlots_modifyState_of_iff h hcode).trans rfl

/-- A touch of an account counts the same slots. -/
theorem nonceOrCodeFreshSlots_touchAccount (tx : TransactionState) (address : Address) :
    nonceOrCodeFreshSlots (tx.touchAccount address) = nonceOrCodeFreshSlots tx := by
  refine nonceOrCodeFreshSlots_congr (fun other => HasNonceOrCode.congr ?_) fun other _ key => ?_
  · by_cases ho : other = address
    · subst ho
      exact TransactionState.getAccount_touchAccount_self tx other
    · exact TransactionState.getAccount_touchAccount ho
  · -- A touch writes no word.
    unfold TransactionState.touchAccount
    split <;> exact ⟨rfl, rfl⟩

/-- The start of a creation at an account with no nonce or code counts the same slots.

It wipes the storage of the account before it may give it a nonce. -/
theorem nonceOrCodeFreshSlots_prepareCreation {state prepared : TransactionState}
    {address : Address} (hcode : ¬HasNonceOrCode state address)
    (h : prepareCreation fork state address = .ok prepared) :
    nonceOrCodeFreshSlots prepared = nonceOrCodeFreshSlots state := by
  -- The wipe and the record of the creation change no account and no other word.
  have hst : ∀ other, other ≠ address → ∀ key,
      ((state.destroyStorage address).markAccountCreated address).getStorage other key =
          state.getStorage other key ∧
        ((state.destroyStorage address).markAccountCreated address).getStorageOriginal other key =
          state.getStorageOriginal other key := fun other ho key =>
    ⟨TransactionState.getStorage_destroyStorage_of_ne state ho key, by
      rw [TransactionState.getStorageOriginal_markAccountCreated]
      simp only [ho, ↓reduceIte, TransactionState.getStorageOriginal_destroyStorage]⟩
  -- The new account holds no word, and every other account and word stays.
  have hfacts : (∀ key, prepared.getStorage address key = 0) ∧ ∀ other, other ≠ address →
      prepared.getAccount other = state.getAccount other ∧ ∀ key,
        prepared.getStorage other key = state.getStorage other key ∧
          prepared.getStorageOriginal other key = state.getStorageOriginal other key := by
    unfold prepareCreation at h
    split at h
    · cases h1 : ((state.destroyStorage address).markAccountCreated address).incrementNonce
          fork address with
      | error e => simp [h1, Except.mapError] at h
      | ok mid =>
        simp only [h1, Except.mapError, Except.ok.injEq] at h
        subst h
        obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h1
        -- The account gets a nonce, so the change keeps every word.
        have hkeep : mid.getAccount address ≠ EMPTY_ACCOUNT := fun he => by
          have hn := congrArg Account.nonce (hself.symm.trans he)
          simp [EMPTY_ACCOUNT] at hn
        refine ⟨fun key => ?_, fun other ho => ⟨?_, fun key => ?_⟩⟩
        · rw [TransactionState.getStorage_modifyState_self h1 (Or.inr hkeep)]
          exact TransactionState.getStorage_destroyStorage state address key
        · simp only [TransactionState.getAccount, hother other ho]
          rfl
        · rw [TransactionState.getStorage_modifyState h1,
            TransactionState.getStorageOriginal_modifyState h1]
          simp only [ho, false_and, ↓reduceIte]
          exact hst other ho key
    · cases h
      exact ⟨TransactionState.getStorage_destroyStorage state address, fun other ho =>
        ⟨rfl, hst other ho⟩⟩
  obtain ⟨hzero, hrest⟩ := hfacts
  ext ⟨other, key⟩
  rw [mem_nonceOrCodeFreshSlots, mem_nonceOrCodeFreshSlots]
  by_cases ho : other = address
  · -- The new account has no fresh slot, and had no nonce or code.
    subst ho
    simp only [hzero, hcode, false_and, ne_eq, not_true_eq_false, and_false]
  · obtain ⟨hacc, hw⟩ := hrest other ho
    obtain ⟨h1, h2⟩ := hw key
    rw [HasNonceOrCode.congr hacc, h1, h2]

/-- A rollback to a snapshot on the same block counts the slots of the snapshot.

The rolled-back state must keep every account that the snapshot created.

Each account that it created and the snapshot did not must have no nonce or code in the snapshot.
-/
theorem nonceOrCodeFreshSlots_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent)
    (hkept : ∀ address, address ∈ snapshot.createdAccounts → address ∈ tx.createdAccounts)
    -- The words before the transaction may differ at an account created since the snapshot.
    --
    -- But none of the slots of such an account is counted.
    (hnew : ∀ address, address ∈ tx.createdAccounts → address ∉ snapshot.createdAccounts →
      ¬HasNonceOrCode snapshot address) :
    nonceOrCodeFreshSlots (tx.restoreTxState snapshot) = nonceOrCodeFreshSlots snapshot := by
  refine nonceOrCodeFreshSlots_congr (fun other => HasNonceOrCode.congr ?_)
    fun other hc key => ⟨TransactionState.getStorage_restoreTxState hparent other key, ?_⟩
  · simp only [TransactionState.getAccount,
      TransactionState.getAccountOptional_restoreTxState hparent]
  · -- The words before the transaction agree, except at accounts created since the snapshot.
    rw [TransactionState.getStorageOriginal_restoreTxState]
    unfold TransactionState.getStorageOriginal
    by_cases hs : other ∈ snapshot.createdAccounts
    · simp only [hs, hkept other hs, ↓reduceIte]
    · have ht : other ∉ tx.createdAccounts := fun ht => hnew other ht hs hc
      simp only [hs, ht, hparent, ↓reduceIte]

end EthLib.Execution.Evm

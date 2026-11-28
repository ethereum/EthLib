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

/-- The slots of a set of slots that lie at accounts with a nonce or code.

From Spurious Dragon, code runs only at an account with a nonce or code.

So only such an account writes its storage. -/
def nonceOrCodeSlots (slots : TransactionState → Finset (Address × Bytes32))
    (tx : TransactionState) : Finset (Address × Bytes32) :=
  (slots tx).filter fun slot => HasNonceOrCode tx slot.1

/-- A set of slots holds exactly the slots whose word before the transaction and now satisfy `P`.
-/
def SlotsOf (slots : TransactionState → Finset (Address × Bytes32)) (P : U256 → U256 → Prop) :
    Prop :=
  ∀ tx address key,
    (address, key) ∈ slots tx ↔ P (tx.getStorageOriginal address key) (tx.getStorage address key)

/-- The fresh slots of the accounts with a nonce or code. -/
def nonceOrCodeFreshSlots (tx : TransactionState) : Finset (Address × Bytes32) :=
  -- A slot is fresh when its word was zero before the transaction and is not zero now.
  nonceOrCodeSlots TransactionState.freshSlots tx

/-- The cleared slots of the accounts with a nonce or code. -/
def nonceOrCodeClearedSlots (tx : TransactionState) : Finset (Address × Bytes32) :=
  -- A slot is cleared when its word was not zero before the transaction and is zero now.
  nonceOrCodeSlots TransactionState.clearedSlots tx

/-- The fresh slots are those with a zero word before the transaction and a nonzero word now. -/
theorem slotsOf_freshSlots : SlotsOf TransactionState.freshSlots fun original current =>
    original = 0 ∧ current ≠ 0 :=
  fun _ _ _ => TransactionState.mem_freshSlots

/-- The cleared slots are those with a nonzero word before the transaction and a zero word now. -/
theorem slotsOf_clearedSlots : SlotsOf TransactionState.clearedSlots fun original current =>
    original ≠ 0 ∧ current = 0 :=
  fun _ _ _ => TransactionState.mem_clearedSlots

section Slots

variable {slots : TransactionState → Finset (Address × Bytes32)} {P : U256 → U256 → Prop}

/-- A slot is counted exactly when its account has a nonce or code and its words satisfy `P`. -/
theorem mem_nonceOrCodeSlots (hs : SlotsOf slots P) {tx : TransactionState} {address : Address}
    {key : Bytes32} :
    (address, key) ∈ nonceOrCodeSlots slots tx ↔ HasNonceOrCode tx address ∧
      P (tx.getStorageOriginal address key) (tx.getStorage address key) := by
  simp only [nonceOrCodeSlots, Finset.mem_filter, hs tx address key]
  tauto

/-- Two states count the same slots when they agree where an account has a nonce or code.

They must agree on which accounts have a nonce or code.

At each such account, they must agree on every word, now and before the transaction. -/
theorem nonceOrCodeSlots_congr (hs : SlotsOf slots P) {tx tx' : TransactionState}
    (hcode : ∀ address, HasNonceOrCode tx' address ↔ HasNonceOrCode tx address)
    (hwords : ∀ address, HasNonceOrCode tx address → ∀ key,
      tx'.getStorage address key = tx.getStorage address key ∧
        tx'.getStorageOriginal address key = tx.getStorageOriginal address key) :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
  ext ⟨address, key⟩
  rw [mem_nonceOrCodeSlots hs, mem_nonceOrCodeSlots hs, hcode address]
  by_cases hc : HasNonceOrCode tx address
  · -- At an account with a nonce or code, both states hold the same words.
    obtain ⟨h1, h2⟩ := hwords address hc key
    rw [h1, h2]
  · simp only [hc, false_and]

/-- A transaction with no write counts no slot, when no word satisfies `P` with itself. -/
theorem nonceOrCodeSlots_ofBlock (hs : SlotsOf slots P) (hP : ∀ word, ¬P word word)
    (block : BlockState) : nonceOrCodeSlots slots (.ofBlock block) = ∅ := by
  ext ⟨address, key⟩
  simp only [mem_nonceOrCodeSlots hs, Finset.notMem_empty, iff_false, not_and]
  -- With no write, no wipe and no creation, every word is the word before the transaction.
  have h : (TransactionState.ofBlock block).getStorage address key =
      (TransactionState.ofBlock block).getStorageOriginal address key := by
    simp [TransactionState.getStorage, TransactionState.getStorageOriginal,
      TransactionState.ofBlock, State.StorageMap.slot]
  rw [h]
  exact fun _ => hP _

/-- A state with more reads counts the same slots. -/
theorem nonceOrCodeSlots_of_readsMore (hs : SlotsOf slots P) {tx tx' : TransactionState}
    (h : tx.ReadsMore tx') : nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
  refine nonceOrCodeSlots_congr hs (fun address => HasNonceOrCode.congr ?_)
    fun address _ key => ⟨by rw [h.getStorage], by rw [h.getStorageOriginal]⟩
  rw [h.rest]
  rfl

/-- A write of transient storage counts the same slots. -/
theorem nonceOrCodeSlots_setTransientStorage (hs : SlotsOf slots P) (tx : TransactionState)
    (address : Address) (key : Bytes32) (value : U256) :
    nonceOrCodeSlots slots (tx.setTransientStorage address key value) =
      nonceOrCodeSlots slots tx :=
  nonceOrCodeSlots_congr hs (fun _ => HasNonceOrCode.congr rfl) fun _ _ _ => ⟨rfl, rfl⟩

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
theorem nonceOrCodeSlots_modifyState_of_iff (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx')
    (hcode : ∀ other, HasNonceOrCode tx' other ↔ HasNonceOrCode tx other) :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx :=
  nonceOrCodeSlots_congr hs hcode fun other hc key =>
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
theorem nonceOrCodeSlots_modifyState (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.nonce = (tx.getAccount address).nonce ∧
        account.codeHash = (tx.getAccount address).codeHash) :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
  obtain ⟨account, hf, hself, hother⟩ := TransactionState.modifyState_eq_ok h
  refine nonceOrCodeSlots_modifyState_of_iff hs h fun other => ?_
  by_cases ho : other = address
  · -- The changed account keeps its nonce and its code.
    subst ho
    obtain ⟨hn, hh⟩ := keeps account hf
    simp only [HasNonceOrCode, hself, hn, hh]
  · exact HasNonceOrCode.congr (hother other ho)

/-- A move of ether counts the same slots. -/
theorem nonceOrCodeSlots_moveEther (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
  unfold TransactionState.moveEther at h
  cases h1 : tx.modifyState fork sender (Account.debit sender amount) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok mid =>
    -- The debit and the credit each keep every nonce and every code.
    simp only [h1, bind, Except.bind] at h
    rw [nonceOrCodeSlots_modifyState hs h fun _ => keeps_credit _ _ _ _,
      nonceOrCodeSlots_modifyState hs h1 fun _ => keeps_debit _ _ _ _]

/-- The move of the balance of an account that SELFDESTRUCT destroys counts the same slots. -/
theorem nonceOrCodeSlots_selfdestructTransfer (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
  -- A new balance keeps the nonce and the code.
  have hbal : ∀ (state state' : TransactionState) (address : Address) (amount : U256),
      state.setAccountBalance fork address amount = .ok state' →
        nonceOrCodeSlots slots state' = nonceOrCodeSlots slots state :=
    fun _ _ _ _ hb => nonceOrCodeSlots_modifyState hs hb fun _ hf => by
      cases hf
      exact ⟨rfl, rfl⟩
  unfold selfdestructTransfer at h
  split at h
  · -- From Cancun, the balance moves, and may then be set to zero.
    cases h1 : tx.moveEther fork originator beneficiary (tx.getAccount originator).balance with
    | error e => simp [h1, bind, Except.bind] at h
    | ok mid =>
      simp only [h1, bind, Except.bind] at h
      rw [← nonceOrCodeSlots_moveEther hs h1]
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
      exact nonceOrCodeSlots_modifyState hs h1 fun _ => keeps_credit _ _ _ _

/-- The rise of the nonce of an account with a nonce or code counts the same slots. -/
theorem nonceOrCodeSlots_incrementNonce (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {address : Address} (hcode : HasNonceOrCode tx address)
    (h : tx.incrementNonce fork address = .ok tx') :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
  obtain ⟨hself, hother⟩ := TransactionState.getAccount_incrementNonce h
  refine nonceOrCodeSlots_modifyState_of_iff hs h fun other => ?_
  by_cases ho : other = address
  · -- The account keeps a nonce.
    subst ho
    exact iff_of_true (Or.inl (by rw [hself]; exact Nat.le_add_left 1 _)) hcode
  · exact HasNonceOrCode.congr (by simp only [TransactionState.getAccount, hother other ho])

/-- New code at an account with a nonce counts the same slots. -/
theorem nonceOrCodeSlots_setCode (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {address : Address} {code : ByteArray} (hnonce : 1 ≤ (tx.getAccount address).nonce)
    (h : tx.setCode fork address code = .ok tx') :
    nonceOrCodeSlots slots tx' = nonceOrCodeSlots slots tx := by
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
  split at h <;> exact (nonceOrCodeSlots_modifyState_of_iff hs h hcode).trans
    (nonceOrCodeSlots_congr hs (fun _ => HasNonceOrCode.congr rfl) fun _ _ _ => ⟨rfl, rfl⟩)

/-- A touch of an account counts the same slots. -/
theorem nonceOrCodeSlots_touchAccount (hs : SlotsOf slots P) (tx : TransactionState)
    (address : Address) :
    nonceOrCodeSlots slots (tx.touchAccount address) = nonceOrCodeSlots slots tx := by
  refine nonceOrCodeSlots_congr hs (fun other => HasNonceOrCode.congr ?_) fun other _ key => ?_
  · by_cases ho : other = address
    · subst ho
      exact TransactionState.getAccount_touchAccount_self tx other
    · exact TransactionState.getAccount_touchAccount ho
  · -- A touch writes no word.
    unfold TransactionState.touchAccount
    split <;> exact ⟨rfl, rfl⟩

/-- The start of a creation at an account with no nonce or code counts the same slots.

It wipes the storage of the account before it may give it a nonce.

No zero word before the transaction and now may satisfy `P`. -/
theorem nonceOrCodeSlots_prepareCreation (hs : SlotsOf slots P) (hP : ¬P 0 0)
    {state prepared : TransactionState} {address : Address}
    (hcode : ¬HasNonceOrCode state address)
    (h : prepareCreation fork state address = .ok prepared) :
    nonceOrCodeSlots slots prepared = nonceOrCodeSlots slots state := by
  -- The wipe and the record of the creation change no account and no other word.
  have hst : ∀ other, other ≠ address → ∀ key,
      ((state.destroyStorage address).markAccountCreated address).getStorage other key =
          state.getStorage other key ∧
        ((state.destroyStorage address).markAccountCreated address).getStorageOriginal other key =
          state.getStorageOriginal other key := fun other ho key =>
    ⟨TransactionState.getStorage_destroyStorage_of_ne state ho key, by
      rw [TransactionState.getStorageOriginal_markAccountCreated]
      simp only [ho, ↓reduceIte, TransactionState.getStorageOriginal_destroyStorage]⟩
  -- The new account holds no word and had none, and every other account and word stays.
  have hfacts : (∀ key, prepared.getStorage address key = 0 ∧
      prepared.getStorageOriginal address key = 0) ∧ ∀ other, other ≠ address →
      prepared.getAccount other = state.getAccount other ∧ ∀ key,
        prepared.getStorage other key = state.getStorage other key ∧
          prepared.getStorageOriginal other key = state.getStorageOriginal other key := by
    have horig : ∀ key,
        ((state.destroyStorage address).markAccountCreated address).getStorageOriginal address
          key = 0 := fun key => by
      rw [TransactionState.getStorageOriginal_markAccountCreated]
      simp only [↓reduceIte]
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
        refine ⟨fun key => ⟨?_, ?_⟩, fun other ho => ⟨?_, fun key => ?_⟩⟩
        · rw [TransactionState.getStorage_modifyState_self h1 (Or.inr hkeep)]
          exact TransactionState.getStorage_destroyStorage state address key
        · rw [TransactionState.getStorageOriginal_modifyState h1]
          exact horig key
        · simp only [TransactionState.getAccount, hother other ho]
          rfl
        · rw [TransactionState.getStorage_modifyState h1,
            TransactionState.getStorageOriginal_modifyState h1]
          simp only [ho, false_and, ↓reduceIte]
          exact hst other ho key
    · cases h
      exact ⟨fun key => ⟨TransactionState.getStorage_destroyStorage state address key, horig key⟩,
        fun other ho => ⟨rfl, hst other ho⟩⟩
  obtain ⟨hzero, hrest⟩ := hfacts
  ext ⟨other, key⟩
  rw [mem_nonceOrCodeSlots hs, mem_nonceOrCodeSlots hs]
  by_cases ho : other = address
  · -- The new account counts no slot, and had no nonce or code.
    subst ho
    simp only [(hzero key).1, (hzero key).2, hP, hcode, and_false, false_and]
  · obtain ⟨hacc, hw⟩ := hrest other ho
    obtain ⟨h1, h2⟩ := hw key
    rw [HasNonceOrCode.congr hacc, h1, h2]

/-- A rollback to a snapshot on the same block counts the slots of the snapshot.

The rolled-back state must keep every account that the snapshot created.

Each account that it created and the snapshot did not must have no nonce or code in the snapshot.
-/
theorem nonceOrCodeSlots_restoreTxState (hs : SlotsOf slots P) {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent)
    (hkept : ∀ address, address ∈ snapshot.createdAccounts → address ∈ tx.createdAccounts)
    -- The words before the transaction may differ at an account created since the snapshot.
    --
    -- But none of the slots of such an account is counted.
    (hnew : ∀ address, address ∈ tx.createdAccounts → address ∉ snapshot.createdAccounts →
      ¬HasNonceOrCode snapshot address) :
    nonceOrCodeSlots slots (tx.restoreTxState snapshot) = nonceOrCodeSlots slots snapshot := by
  refine nonceOrCodeSlots_congr hs (fun other => HasNonceOrCode.congr ?_)
    fun other hc key => ⟨TransactionState.getStorage_restoreTxState hparent other key, ?_⟩
  · simp only [TransactionState.getAccount,
      TransactionState.getAccountOptional_restoreTxState hparent]
  · -- The words before the transaction agree, except at accounts created since the snapshot.
    rw [TransactionState.getStorageOriginal_restoreTxState]
    unfold TransactionState.getStorageOriginal
    by_cases hsnap : other ∈ snapshot.createdAccounts
    · simp only [hsnap, hkept other hsnap, ↓reduceIte]
    · have ht : other ∉ tx.createdAccounts := fun ht => hnew other ht hsnap hc
      simp only [hsnap, ht, hparent, ↓reduceIte]

/-- A storage write at an account with a nonce or code changes the count as the whole set does.
-/
theorem card_nonceOrCodeSlots_setStorage (hs : SlotsOf slots P) {tx tx' : TransactionState}
    {address : Address} {key : Bytes32} {value : U256} (hcode : HasNonceOrCode tx address)
    (h : tx.setStorage address key value = .ok tx') :
    ((nonceOrCodeSlots slots tx').card : Int) - (nonceOrCodeSlots slots tx).card =
      ((slots tx').card : Int) - (slots tx).card := by
  -- The write keeps every account.
  have hacc : ∀ other, tx'.getAccount other = tx.getAccount other := by
    intro other
    simp only [TransactionState.getAccount, TransactionState.getAccountOptional_setStorage h]
  -- The slots at accounts with no nonce or code stay, since the write is at another account.
  have hrest : (slots tx').filter (fun slot => ¬HasNonceOrCode tx' slot.1) =
      (slots tx).filter (fun slot => ¬HasNonceOrCode tx slot.1) := by
    ext ⟨other, otherKey⟩
    simp only [Finset.mem_filter, hs tx' other otherKey, hs tx other otherKey,
      HasNonceOrCode.congr (hacc other)]
    by_cases ho : HasNonceOrCode tx other
    · simp only [ho, not_true_eq_false, and_false]
    · have hne : other ≠ address := fun e => ho (e ▸ hcode)
      rw [TransactionState.getStorage_setStorage_of_ne h (.inl hne),
        TransactionState.getStorageOriginal_setStorage h]
  have e1 := Finset.card_filter_add_card_filter_not (s := slots tx')
    (p := fun slot => HasNonceOrCode tx' slot.1)
  have e2 := Finset.card_filter_add_card_filter_not (s := slots tx)
    (p := fun slot => HasNonceOrCode tx slot.1)
  rw [hrest] at e1
  unfold nonceOrCodeSlots
  omega

end Slots

/-! ## The fresh slots -/

/-- A slot is counted exactly when its account has a nonce or code and the slot is fresh. -/
theorem mem_nonceOrCodeFreshSlots {tx : TransactionState} {address : Address} {key : Bytes32} :
    (address, key) ∈ nonceOrCodeFreshSlots tx ↔ HasNonceOrCode tx address ∧
      tx.getStorageOriginal address key = 0 ∧ tx.getStorage address key ≠ 0 :=
  mem_nonceOrCodeSlots slotsOf_freshSlots

/-- Two states count the same slots when they agree where an account has a nonce or code.

They must agree on which accounts have a nonce or code.

At each such account, they must agree on every word, now and before the transaction. -/
theorem nonceOrCodeFreshSlots_congr {tx tx' : TransactionState}
    (hcode : ∀ address, HasNonceOrCode tx' address ↔ HasNonceOrCode tx address)
    (hwords : ∀ address, HasNonceOrCode tx address → ∀ key,
      tx'.getStorage address key = tx.getStorage address key ∧
        tx'.getStorageOriginal address key = tx.getStorageOriginal address key) :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_congr slotsOf_freshSlots hcode hwords

/-- A transaction with no write counts no slot. -/
theorem nonceOrCodeFreshSlots_ofBlock (block : BlockState) :
    nonceOrCodeFreshSlots (.ofBlock block) = ∅ :=
  nonceOrCodeSlots_ofBlock slotsOf_freshSlots (fun _ h => h.2 h.1) block

/-- A state with more reads counts the same slots. -/
theorem nonceOrCodeFreshSlots_of_readsMore {tx tx' : TransactionState} (h : tx.ReadsMore tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_of_readsMore slotsOf_freshSlots h

/-- A write of transient storage counts the same slots. -/
theorem nonceOrCodeFreshSlots_setTransientStorage (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    nonceOrCodeFreshSlots (tx.setTransientStorage address key value) =
      nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_setTransientStorage slotsOf_freshSlots tx address key value

/-- A storage write at an account with a nonce or code changes the count as the fresh slots. -/
theorem card_nonceOrCodeFreshSlots_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (hcode : HasNonceOrCode tx address)
    (h : tx.setStorage address key value = .ok tx') :
    ((nonceOrCodeFreshSlots tx').card : Int) - (nonceOrCodeFreshSlots tx).card =
      (tx'.freshSlots.card : Int) - tx.freshSlots.card :=
  card_nonceOrCodeSlots_setStorage slotsOf_freshSlots hcode h

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

/-- A change of an account that keeps its nonce and its code counts the same slots.

From Paris, such a change may delete an empty account, whose slots are not counted. -/
theorem nonceOrCodeFreshSlots_modifyState {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.nonce = (tx.getAccount address).nonce ∧
        account.codeHash = (tx.getAccount address).codeHash) :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_modifyState slotsOf_freshSlots h keeps

/-- A move of ether counts the same slots. -/
theorem nonceOrCodeFreshSlots_moveEther {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_moveEther slotsOf_freshSlots h

/-- The move of the balance of an account that SELFDESTRUCT destroys counts the same slots. -/
theorem nonceOrCodeFreshSlots_selfdestructTransfer {tx tx' : TransactionState}
    {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_selfdestructTransfer slotsOf_freshSlots h

/-- The rise of the nonce of an account with a nonce or code counts the same slots. -/
theorem nonceOrCodeFreshSlots_incrementNonce {tx tx' : TransactionState} {address : Address}
    (hcode : HasNonceOrCode tx address) (h : tx.incrementNonce fork address = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_incrementNonce slotsOf_freshSlots hcode h

/-- New code at an account with a nonce counts the same slots. -/
theorem nonceOrCodeFreshSlots_setCode {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (hnonce : 1 ≤ (tx.getAccount address).nonce)
    (h : tx.setCode fork address code = .ok tx') :
    nonceOrCodeFreshSlots tx' = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_setCode slotsOf_freshSlots hnonce h

/-- A touch of an account counts the same slots. -/
theorem nonceOrCodeFreshSlots_touchAccount (tx : TransactionState) (address : Address) :
    nonceOrCodeFreshSlots (tx.touchAccount address) = nonceOrCodeFreshSlots tx :=
  nonceOrCodeSlots_touchAccount slotsOf_freshSlots tx address

/-- The start of a creation at an account with no nonce or code counts the same slots.

It wipes the storage of the account before it may give it a nonce. -/
theorem nonceOrCodeFreshSlots_prepareCreation {state prepared : TransactionState}
    {address : Address} (hcode : ¬HasNonceOrCode state address)
    (h : prepareCreation fork state address = .ok prepared) :
    nonceOrCodeFreshSlots prepared = nonceOrCodeFreshSlots state :=
  nonceOrCodeSlots_prepareCreation slotsOf_freshSlots (fun h => h.2 rfl) hcode h

/-- A rollback to a snapshot on the same block counts the slots of the snapshot.

The rolled-back state must keep every account that the snapshot created.

Each account that it created and the snapshot did not must have no nonce or code in the snapshot.
-/
theorem nonceOrCodeFreshSlots_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent)
    (hkept : ∀ address, address ∈ snapshot.createdAccounts → address ∈ tx.createdAccounts)
    (hnew : ∀ address, address ∈ tx.createdAccounts → address ∉ snapshot.createdAccounts →
      ¬HasNonceOrCode snapshot address) :
    nonceOrCodeFreshSlots (tx.restoreTxState snapshot) = nonceOrCodeFreshSlots snapshot :=
  nonceOrCodeSlots_restoreTxState slotsOf_freshSlots hparent hkept hnew

end EthLib.Execution.Evm

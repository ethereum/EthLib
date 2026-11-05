module

public import EthLib.Execution.State.Tracker

/-!
# Proofs: the transaction state

A read after a write returns the written value, and a write leaves every other place alone.

A storage write leaves the words before the transaction unchanged.

Restoring a snapshot restores every read of the snapshot.

A move of ether keeps the sum of the two balances, and fails when the sender lacks the amount.

A move of ether between two addresses fails exactly in two cases.

The sender lacks the amount, or the recipient's balance would reach 2^256.

Otherwise it moves the amount exactly.

A change of an account keeps every code.

It keeps the storage too, unless it deletes the account.

An account that the transaction created has zero words before the transaction.

Each new transaction starts with an empty transient storage.

The end of a transaction keeps every read of the transaction.

A record of a read changes no read, and a rollback keeps the record.

A wipe of the storage records the keys it drops as reads.

Clearing an account keeps its balance, and zeroes its nonce, its code and its storage.

Setting the code or the nonce of an account changes no other field and no other account.

The state after a block reads as the block does at the start of its next transaction.
-/

@[expose] public section

namespace EthLib.Execution.State.TransactionState

open EthLib.Base

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Execution.State.StateError.code_injective (e₁ e₂ : StateError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [StateError.code] at h; exact absurd h (by decide))

/-! ## Accounts -/

/-- A record of an account read changes no account. -/
@[simp] theorem getAccountOptional_recordAccountRead (tx : TransactionState)
    (address other : Address) :
    (tx.recordAccountRead address).getAccountOptional other = tx.getAccountOptional other := rfl

/-- A record of an account read changes no account. -/
@[simp] theorem getAccount_recordAccountRead (tx : TransactionState) (address other : Address) :
    (tx.recordAccountRead address).getAccount other = tx.getAccount other := rfl

/-- A record of an account read changes no record of created accounts. -/
@[simp] theorem createdAccounts_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).createdAccounts = tx.createdAccounts := rfl

/-- Reading the account just set gives it. -/
theorem getAccountOptional_setAccount_self (tx : TransactionState) (address : Address)
    (account : Option Account) :
    (tx.setAccount address account).getAccountOptional address = account := by
  simp [setAccount, getAccountOptional]

/-- Setting an account leaves the account at every other address. -/
theorem getAccountOptional_setAccount_of_ne (tx : TransactionState) {address other : Address}
    (account : Option Account) (h : other ≠ address) :
    (tx.setAccount address account).getAccountOptional other = tx.getAccountOptional other := by
  simp [setAccount, getAccountOptional, Std.ExtTreeMap.getElem?_insert, Ne.symm h]

/-- Deleting the storage of an address leaves every account. -/
theorem getAccountOptional_destroyStorage (tx : TransactionState) (address other : Address) :
    (tx.destroyStorage address).getAccountOptional other = tx.getAccountOptional other := rfl

/-! ## Storage -/

/-- A storage write needs an account, and then succeeds. -/
theorem setStorage_eq_error_iff (tx : TransactionState) (address : Address) (key : Bytes32)
    (value : U256) (e : StateError) :
    tx.setStorage address key value = .error e ↔
      tx.getAccountOptional address = none ∧ e = .noAccount address := by
  unfold setStorage
  split
  · rename_i hnone
    simp only [Option.isNone_iff_eq_none] at hnone
    simp only [Except.error.injEq, hnone, true_and]
    exact eq_comm
  · rename_i hsome
    simp only [Option.isNone_iff_eq_none] at hsome
    simp [reduceCtorEq, hsome]

/-- Reading the word just written gives it. -/
theorem getStorage_setStorage_self {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.getStorage address key = value := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    simp [getStorage, StorageMap.slot]

/-- A storage write leaves every other key of every address. -/
theorem getStorage_setStorage_of_ne {tx tx' : TransactionState} {address other : Address}
    {key otherKey : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx')
    (hne : other ≠ address ∨ otherKey ≠ key) :
    tx'.getStorage other otherKey = tx.getStorage other otherKey := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rcases hne with hne | hne
    · simp [getStorage, StorageMap.slot, recordAccountRead, Std.ExtTreeMap.getElem?_insert,
        Ne.symm hne] <;> rfl
    · by_cases haddress : other = address
      · subst haddress
        simp [getStorage, StorageMap.slot, recordAccountRead, Std.ExtTreeMap.getElem?_insert,
          Ne.symm hne, Std.ExtTreeMap.getD_eq_getD_getElem?] <;> try rfl
        cases tx.storageWrites[other]? <;> simp <;> rfl
      · simp [getStorage, StorageMap.slot, recordAccountRead, Std.ExtTreeMap.getElem?_insert,
          Ne.symm haddress] <;> rfl

/-- A storage write leaves the words before the transaction. -/
theorem getStorageOriginal_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.getStorageOriginal = tx.getStorageOriginal := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- After a wipe, every word of the storage of the address is zero. -/
theorem getStorage_destroyStorage (tx : TransactionState) (address : Address) (key : Bytes32) :
    (tx.destroyStorage address).getStorage address key = 0 := by
  simp [destroyStorage, getStorage, StorageMap.slot]

/-! ## Transient storage -/

/-- Reading the transient word just written gives it. -/
theorem getTransientStorage_setTransientStorage_self (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    (tx.setTransientStorage address key value).getTransientStorage address key = value := by
  unfold setTransientStorage getTransientStorage
  simp only [StorageMap.slot, Std.ExtTreeMap.getElem?_insert_self, Option.bind_some]
  split
  · rename_i hzero
    simp [hzero]
  · simp

/-- A transient write leaves every other key of every address. -/
theorem getTransientStorage_setTransientStorage_of_ne (tx : TransactionState)
    {address other : Address} {key otherKey : Bytes32} (value : U256)
    (hne : other ≠ address ∨ otherKey ≠ key) :
    (tx.setTransientStorage address key value).getTransientStorage other otherKey =
      tx.getTransientStorage other otherKey := by
  rcases hne with hne | hne
  · simp [setTransientStorage, getTransientStorage, StorageMap.slot,
      Std.ExtTreeMap.getElem?_insert, Ne.symm hne]
  · by_cases haddress : other = address
    · subst haddress
      unfold setTransientStorage getTransientStorage
      simp only [StorageMap.slot, Std.ExtTreeMap.getElem?_insert_self, Option.bind_some,
        Std.ExtTreeMap.getD_eq_getD_getElem?]
      cases tx.transientStorage[other]? <;> split <;>
        simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, Ne.symm hne]
    · simp [setTransientStorage, getTransientStorage, StorageMap.slot,
        Std.ExtTreeMap.getElem?_insert, Ne.symm haddress]

/-- A transaction with no write has an empty transient storage. -/
theorem getTransientStorage_ofBlock (block : BlockState) (address : Address) (key : Bytes32) :
    (ofBlock block).getTransientStorage address key = 0 := by
  simp [ofBlock, getTransientStorage, StorageMap.slot]

/-- The transaction after the end of another starts with an empty transient storage. -/
theorem getTransientStorage_incorporateTxIntoBlock (tx : TransactionState) (address : Address)
    (key : Bytes32) : tx.incorporateTxIntoBlock.getTransientStorage address key = 0 :=
  getTransientStorage_ofBlock _ address key

/-! ## Rollback -/

/-- After a rollback, every account reads as in the snapshot. -/
theorem getAccountOptional_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent) (address : Address) :
    (tx.restoreTxState snapshot).getAccountOptional address =
      snapshot.getAccountOptional address := by
  simp [restoreTxState, getAccountOptional, hparent]

/-- After a rollback, every word of storage reads as in the snapshot. -/
theorem getStorage_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent) (address : Address) (key : Bytes32) :
    (tx.restoreTxState snapshot).getStorage address key = snapshot.getStorage address key := by
  simp [restoreTxState, getStorage, hparent]

/-- After a rollback, every code reads as in the snapshot. -/
theorem getCode_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent) (codeHash : Hash32) :
    (tx.restoreTxState snapshot).getCode codeHash = snapshot.getCode codeHash := by
  simp [restoreTxState, getCode, hparent]

/-- After a rollback, every transient word reads as in the snapshot. -/
theorem getTransientStorage_restoreTxState (tx snapshot : TransactionState) (address : Address)
    (key : Bytes32) :
    (tx.restoreTxState snapshot).getTransientStorage address key =
      snapshot.getTransientStorage address key := rfl

/-- A rollback keeps the accounts that the transaction created. -/
theorem createdAccounts_restoreTxState (tx snapshot : TransactionState) :
    (tx.restoreTxState snapshot).createdAccounts = tx.createdAccounts := rfl

/-! ## Changing an account -/

/-- An account that exists and is empty is the empty account. -/
theorem eq_empty_of_accountExistsAndIsEmpty {tx : TransactionState} {address : Address}
    (h : tx.accountExistsAndIsEmpty address = true) : tx.getAccount address = EMPTY_ACCOUNT := by
  unfold accountExistsAndIsEmpty at h
  unfold getAccount
  split at h
  · rename_i account haccount
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hnonce, hcode⟩, hbalance⟩ := h
    cases account
    simp_all [EMPTY_ACCOUNT]
  · cases h

/-- A deleted account reads as the empty account, and every other account is unchanged. -/
theorem getAccount_destroyAccount (tx : TransactionState) (address other : Address) :
    (tx.destroyAccount address).getAccount other =
      if other = address then EMPTY_ACCOUNT else tx.getAccount other := by
  unfold destroyAccount getAccount
  split
  · subst other
    rw [getAccountOptional_setAccount_self]
    rfl
  · rename_i hne
    rw [getAccountOptional_setAccount_of_ne _ _ hne, getAccountOptional_destroyStorage]

/-- A change by `f` succeeds exactly when `f` does on the account.

The account then reads as the result of `f`, and every other account is unchanged. -/
theorem modifyState_eq_ok {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    ∃ account, f (tx.getAccount address) = .ok account ∧ tx'.getAccount address = account ∧
      ∀ other, other ≠ address → tx'.getAccount other = tx.getAccount other := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    refine ⟨account, rfl, ?_⟩
    have hset : ∀ other,
        ((tx.recordAccountRead address).setAccount address (some account)).getAccount other =
        if other = address then account else tx.getAccount other := by
      intro other
      unfold getAccount
      split
      · subst other
        rw [getAccountOptional_setAccount_self]
        rfl
      · rename_i hne
        rw [getAccountOptional_setAccount_of_ne _ _ hne]
        rfl
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h
    · -- From Paris, the empty result is deleted, and reads as the empty account it was.
      rename_i hempty
      cases h
      have heq := eq_empty_of_accountExistsAndIsEmpty
        (Bool.and_eq_true_iff.mp hempty).2
      simp only [hset, ↓reduceIte] at heq
      refine ⟨?_, fun other hne => ?_⟩
      · simp only [getAccount_destroyAccount, ↓reduceIte, heq]
      · simp only [getAccount_destroyAccount, hset, hne, ↓reduceIte]
    · cases h
      exact ⟨by simp only [hset, ↓reduceIte], fun other hne => by simp only [hset, hne, ↓reduceIte]⟩

/-- From Paris, no change leaves an empty account behind. -/
theorem accountExistsAndIsEmpty_modifyState {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account} (hfork : fork ≥ .paris)
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.accountExistsAndIsEmpty address = false := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h
    · -- The empty account is deleted, so no account remains.
      cases h
      simp [accountExistsAndIsEmpty, destroyAccount, getAccountOptional_setAccount_self]
    · rename_i hkeep
      cases h
      simpa [decide_eq_true hfork] using hkeep

/-- Before Paris, a change keeps the account it computes, even an empty one. -/
theorem getAccountOptional_modifyState {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account} {account : Account}
    (hfork : fork < .paris) (hf : f (tx.getAccount address) = .ok account)
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.getAccountOptional address = some account := by
  have hlt : ¬ fork ≥ .paris := fun hge => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hfork hge)
  simp only [modifyState, getAccount_recordAccountRead, hf, bind, Except.bind, pure, Except.pure,
    decide_eq_false hlt,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  subst h
  exact getAccountOptional_setAccount_self _ _ _

/-- A change succeeds whenever `f` succeeds on the account. -/
theorem modifyState_isOk {fork : Fork} {tx : TransactionState} {address : Address}
    {f : Account → Except StateError Account} {account : Account}
    (hf : f (tx.getAccount address) = .ok account) :
    ∃ tx', tx.modifyState fork address f = .ok tx' := by
  simp only [modifyState, getAccount_recordAccountRead, hf, bind, Except.bind, pure, Except.pure]
  split <;> exact ⟨_, rfl⟩

/-- A change leaves the account at every other address, or its absence. -/
theorem getAccountOptional_modifyState_of_ne {fork : Fork} {tx tx' : TransactionState}
    {address other : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') (hne : other ≠ address) :
    tx'.getAccountOptional other = tx.getAccountOptional other := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h <;> cases h <;>
      simp only [destroyAccount, getAccountOptional_setAccount_of_ne _ _ hne,
        getAccountOptional_destroyStorage, getAccountOptional_recordAccountRead]

/-- Setting the code of an address gives it the hash of that code.

Every other field and every other account is unchanged. -/
theorem getAccount_setCode {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    tx'.getAccount address =
        { tx.getAccount address with codeHash := Cryptography.Hash.Keccak.keccak256 code } ∧
      ∀ other, other ≠ address → tx'.getAccountOptional other = tx.getAccountOptional other := by
  dsimp only [setCode] at h
  -- Storing the code changes no account, so both branches read as `tx` does.
  split at h <;>
  · obtain ⟨account, hf, hself, -⟩ := modifyState_eq_ok h
    cases hf
    exact ⟨hself, fun other hne => by rw [getAccountOptional_modifyState_of_ne h hne] <;> rfl⟩

/-- Setting the code of an address never fails. -/
theorem setCode_isOk (fork : Fork) (tx : TransactionState) (address : Address)
    (code : ByteArray) : ∃ tx', tx.setCode fork address code = .ok tx' := by
  dsimp only [setCode]
  split <;> exact modifyState_isOk rfl

/-- Adding one to the nonce of an address changes no other field and no other account. -/
theorem getAccount_incrementNonce {fork : Fork} {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') :
    tx'.getAccount address =
        { tx.getAccount address with nonce := (tx.getAccount address).nonce + 1 } ∧
      ∀ other, other ≠ address → tx'.getAccountOptional other = tx.getAccountOptional other := by
  obtain ⟨account, hf, hself, -⟩ := modifyState_eq_ok h
  cases hf
  exact ⟨hself, fun other hne => getAccountOptional_modifyState_of_ne h hne⟩

/-- Adding one to the nonce of an address never fails. -/
theorem incrementNonce_isOk (fork : Fork) (tx : TransactionState) (address : Address) :
    ∃ tx', tx.incrementNonce fork address = .ok tx' :=
  modifyState_isOk rfl

/-! ## The record of reads -/

/-- A record of an account read changes no read of the state. -/
theorem recordAccountRead_reads (tx : TransactionState) (address other : Address)
    (key : Bytes32) (codeHash : Hash32) :
    (tx.recordAccountRead address).getAccountOptional other = tx.getAccountOptional other ∧
      (tx.recordAccountRead address).getStorage other key = tx.getStorage other key ∧
      (tx.recordAccountRead address).getStorageOriginal other key =
        tx.getStorageOriginal other key ∧
      (tx.recordAccountRead address).getCode codeHash = tx.getCode codeHash ∧
      (tx.recordAccountRead address).getTransientStorage other key =
        tx.getTransientStorage other key :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A record of a storage read changes no read of the state. -/
theorem recordStorageRead_reads (tx : TransactionState) (address other : Address)
    (slot key : Bytes32) (codeHash : Hash32) :
    (tx.recordStorageRead address slot).getAccountOptional other = tx.getAccountOptional other ∧
      (tx.recordStorageRead address slot).getStorage other key = tx.getStorage other key ∧
      (tx.recordStorageRead address slot).getStorageOriginal other key =
        tx.getStorageOriginal other key ∧
      (tx.recordStorageRead address slot).getCode codeHash = tx.getCode codeHash ∧
      (tx.recordStorageRead address slot).getTransientStorage other key =
        tx.getTransientStorage other key :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A recorded account read is in the reads, with every earlier one. -/
theorem mem_accountReads_recordAccountRead (tx : TransactionState) (address other : Address) :
    other ∈ (tx.recordAccountRead address).accountReads ↔
      other = address ∨ other ∈ tx.accountReads := by
  simp only [recordAccountRead, Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq]
  exact or_congr_left eq_comm

/-- A recorded storage read is in the reads, with every earlier one. -/
theorem mem_storageReads_recordStorageRead (tx : TransactionState) (address other : Address)
    (key slot : Bytes32) :
    slot ∈ (tx.recordStorageRead address key).storageReads.getD other ∅ ↔
      (other = address ∧ slot = key) ∨ slot ∈ tx.storageReads.getD other ∅ := by
  by_cases h : other = address
  · subst h
    simp only [recordStorageRead, Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insert,
      Std.compare_eq_iff_eq, true_and]
    exact or_congr_left eq_comm
  · simp [recordStorageRead, Std.ExtTreeMap.getD_insert, Ne.symm h, h]

/-- Taking the reads of another state changes no account, word, code or write. -/
theorem withReadsOf_reads (tx other : TransactionState) (address : Address) (key : Bytes32)
    (codeHash : Hash32) :
    (tx.withReadsOf other).getAccountOptional address = tx.getAccountOptional address ∧
      (tx.withReadsOf other).getStorage address key = tx.getStorage address key ∧
      (tx.withReadsOf other).getCode codeHash = tx.getCode codeHash ∧
      (tx.withReadsOf other).accountWrites = tx.accountWrites ∧
      (tx.withReadsOf other).storageWrites = tx.storageWrites :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A change to an account reads it, so the account joins the reads. -/
theorem mem_accountReads_modifyState {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') : address ∈ tx'.accountReads := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  have hmem : address ∈ (tx.recordAccountRead address).accountReads :=
    (mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h <;> cases h <;> exact hmem

/-- A rollback keeps the reads of the transaction, not those of the snapshot. -/
theorem reads_restoreTxState (tx snapshot : TransactionState) :
    (tx.restoreTxState snapshot).accountReads = tx.accountReads ∧
      (tx.restoreTxState snapshot).storageReads = tx.storageReads :=
  ⟨rfl, rfl⟩

/-- A wipe of the storage turns each key it drops into a read. -/
theorem mem_storageReads_destroyStorage {tx : TransactionState} {address : Address}
    {key : Bytes32} (h : key ∈ tx.storageWrites.getD address ∅) :
    key ∈ (tx.destroyStorage address).storageReads.getD address ∅ := by
  simp [destroyStorage, Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insertMany_list, h]

/-- A wipe of the storage keeps every earlier read. -/
theorem mem_storageReads_destroyStorage_of_mem {tx : TransactionState} {address other : Address}
    {key : Bytes32} (h : key ∈ tx.storageReads.getD other ∅) :
    key ∈ (tx.destroyStorage address).storageReads.getD other ∅ := by
  by_cases hother : other = address
  · subst hother
    simp [destroyStorage, Std.ExtTreeMap.getD_insert_self, Std.ExtTreeSet.mem_insertMany_list, h]
  · simpa [destroyStorage, Std.ExtTreeMap.getD_insert, Ne.symm hother] using h

/-! ## Clearing an account and keeping its balance -/

/-- Clearing an account keeps its balance and zeroes its nonce and its code. -/
theorem getAccount_clearAccountPreservingBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx') :
    tx'.getAccount address =
      { tx.getAccount address with nonce := 0, codeHash := EMPTY_CODE_HASH } := by
  obtain ⟨account, hf, hread, -⟩ := modifyState_eq_ok h
  cases hf
  exact hread

/-- Clearing an account leaves every other account unchanged. -/
theorem getAccount_clearAccountPreservingBalance_of_ne {fork : Fork} {tx tx' : TransactionState}
    {address other : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx')
    (hne : other ≠ address) : tx'.getAccount other = tx.getAccount other := by
  obtain ⟨-, -, -, hother⟩ := modifyState_eq_ok h
  exact hother other hne

/-- Clearing an account wipes its storage. -/
theorem getStorage_clearAccountPreservingBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx')
    (key : Bytes32) : tx'.getStorage address key = 0 := by
  simp only [clearAccountPreservingBalance, modifyState, bind, Except.bind, pure,
    Except.pure] at h
  split at h
  · cases h
    exact getStorage_destroyStorage _ _ _
  · cases h
    exact getStorage_destroyStorage _ _ _

/-! ## Moving ether -/

/-- Moving ether fails when the sender holds less than the amount. -/
theorem moveEther_insufficient (fork : Fork) (tx : TransactionState) (sender recipient : Address)
    (amount : U256) (h : (tx.getAccount sender).balance < amount) :
    tx.moveEther fork sender recipient amount = .error (.insufficientBalance sender) := by
  simp [moveEther, modifyState, h, bind, Except.bind]

/-- Moving ether between two addresses keeps the sum of their balances.

Every other balance is unchanged. -/
theorem moveEther_balance {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (hne : sender ≠ recipient)
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    (tx'.getAccount sender).balance.toNat + (tx'.getAccount recipient).balance.toNat =
        (tx.getAccount sender).balance.toNat + (tx.getAccount recipient).balance.toNat ∧
      ∀ other, other ≠ sender → other ≠ recipient →
        tx'.getAccount other = tx.getAccount other := by
  unfold moveEther at h
  cases hmid : tx.modifyState fork sender (fun account =>
      if account.balance < amount then .error (.insufficientBalance sender)
      else .ok { account with balance := account.balance - amount }) with
  | error e => simp [hmid, bind, Except.bind] at h
  | ok mid =>
    simp only [hmid, bind, Except.bind] at h
    obtain ⟨debited, hdebit, hsender, hrest⟩ := modifyState_eq_ok hmid
    obtain ⟨credited, hcredit, hrecipient, hrest'⟩ := modifyState_eq_ok h
    -- The sender loses the amount without wrapping, and the recipient gains it.
    split at hdebit
    · cases hdebit
    · rename_i hfunds
      cases hdebit
      rw [hrest recipient (Ne.symm hne)] at hcredit
      split at hcredit
      · rename_i hfit
        cases hcredit
        refine ⟨?_, fun other hs hr => by rw [hrest' other hr, hrest other hs]⟩
        rw [hrest' sender hne, hsender, hrecipient]
        have hle : amount.toNat ≤ (tx.getAccount sender).balance.toNat := by
          simpa [BitVec.lt_def] using hfunds
        simp only [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), BitVec.toNat_add,
          Nat.mod_eq_of_lt hfit]
        omega
      · cases hcredit

/-- A change of an account keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h <;> cases h <;> rfl

/-- Moving ether keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold moveEther at h
  cases hmid : tx.modifyState fork sender (fun account =>
      if account.balance < amount then .error (.insufficientBalance sender)
      else .ok { account with balance := account.balance - amount }) with
  | error e => simp [hmid, bind, Except.bind] at h
  | ok mid =>
    simp only [hmid, bind, Except.bind] at h
    rw [createdAccounts_modifyState h, createdAccounts_modifyState hmid]

/-- Moving ether from an address to itself keeps its balance. -/
theorem moveEther_self {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.moveEther fork address address amount = .ok tx') :
    (tx'.getAccount address).balance = (tx.getAccount address).balance := by
  unfold moveEther at h
  cases hmid : tx.modifyState fork address (fun account =>
      if account.balance < amount then .error (.insufficientBalance address)
      else .ok { account with balance := account.balance - amount }) with
  | error e => simp [hmid, bind, Except.bind] at h
  | ok mid =>
    simp only [hmid, bind, Except.bind] at h
    obtain ⟨debited, hdebit, hread, -⟩ := modifyState_eq_ok hmid
    obtain ⟨credited, hcredit, hread', -⟩ := modifyState_eq_ok h
    split at hdebit
    · cases hdebit
    · cases hdebit
      rw [hread] at hcredit
      split at hcredit
      · cases hcredit
        rw [hread']
        exact BitVec.sub_add_cancel _ _
      · cases hcredit

/-! ## Failure, storage and code of a change of an account -/

/-- A change fails exactly when `f` fails on the account, with the same error. -/
theorem modifyState_eq_error {fork : Fork} {tx : TransactionState} {address : Address}
    {f : Account → Except StateError Account} {e : StateError} :
    tx.modifyState fork address f = .error e ↔ f (tx.getAccount address) = .error e := by
  unfold modifyState
  simp only [getAccount_recordAccountRead]
  cases hf : f (tx.getAccount address) with
  | error e' => simp [bind, Except.bind]
  | ok account =>
    simp only [bind, Except.bind, pure, Except.pure]
    split <;> simp

/-- A record of an account read changes no word of the storage. -/
@[simp] theorem getStorage_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).getStorage = tx.getStorage := rfl

/-- Setting an account changes no word of the storage, even when it removes the account. -/
@[simp] theorem getStorage_setAccount (tx : TransactionState) (address : Address)
    (account : Option Account) : (tx.setAccount address account).getStorage = tx.getStorage := rfl

/-- A wipe of the storage of an address leaves the storage of every other address. -/
theorem getStorage_destroyStorage_of_ne (tx : TransactionState) {address other : Address}
    (hne : other ≠ address) (key : Bytes32) :
    (tx.destroyStorage address).getStorage other key = tx.getStorage other key := by
  have hcmp : compare address other ≠ .eq := fun h => hne (Std.LawfulEqCmp.eq_of_compare h).symm
  simp [destroyStorage, getStorage, StorageMap.slot, Std.ExtTreeMap.getElem?_erase, hcmp,
    Std.ExtTreeSet.mem_insert]
  rfl

/-- Deleting an account zeroes its storage and leaves the storage of every other address. -/
theorem getStorage_destroyAccount (tx : TransactionState) (address other : Address)
    (key : Bytes32) :
    (tx.destroyAccount address).getStorage other key =
      if other = address then 0 else tx.getStorage other key := by
  unfold destroyAccount
  rw [getStorage_setAccount]
  split
  · subst other; exact getStorage_destroyStorage _ _ _
  · rename_i hne; exact getStorage_destroyStorage_of_ne _ hne _

/-- A change of an account keeps every word of the storage, unless it deletes the account.

From Paris, a change that leaves the account empty deletes it, and its storage reads as zero. -/
theorem getStorage_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (other : Address) (key : Bytes32) :
    tx'.getStorage other key =
      if other = address ∧ tx'.getAccountOptional address = none then 0
      else tx.getStorage other key := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
      have hnone :
          (((tx.recordAccountRead address).setAccount address (some account)).destroyAccount
            address).getAccountOptional address = none := by
        simp [destroyAccount, getAccountOptional_setAccount_self]
      rw [getStorage_destroyAccount]
      by_cases ho : other = address <;> simp [ho, hnone]
    · cases h
      simp [getAccountOptional_setAccount_self]

/-- A change of an account changes no code. -/
theorem getCode_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.getCode = tx.getCode := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h <;> cases h <;> rfl

/-- Setting the code of an address keeps the code under its hash. -/
theorem getCode_setCode_self {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx')
    (hne : Cryptography.Hash.Keccak.keccak256 code ≠ EMPTY_CODE_HASH) :
    tx'.getCode (Cryptography.Hash.Keccak.keccak256 code) = .ok code := by
  dsimp only [setCode] at h
  split at h
  · contradiction
  · rw [getCode_modifyState h]
    unfold getCode
    split
    · rename_i he
      exact absurd he hne
    · dsimp only
      erw [Std.ExtTreeMap.getElem?_insert_self]

/-- Setting the code of an address leaves the code under every other hash. -/
theorem getCode_setCode_of_ne {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') {codeHash : Hash32}
    (hne : codeHash ≠ Cryptography.Hash.Keccak.keccak256 code) :
    tx'.getCode codeHash = tx.getCode codeHash := by
  dsimp only [setCode] at h
  obtain ⟨k, hk⟩ : ∃ k : Hash32, k = Cryptography.Hash.Keccak.keccak256 code := ⟨_, rfl⟩
  rw [← hk] at h hne
  split at h
  · rw [getCode_modifyState h]
  · rw [getCode_modifyState h]
    simp [getCode, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]

/-! ## The words before the transaction -/

/-- A created account has zero words before the transaction, and other accounts keep theirs. -/
theorem getStorageOriginal_markAccountCreated (tx : TransactionState) (address other : Address)
    (key : Bytes32) :
    (tx.markAccountCreated address).getStorageOriginal other key =
      if other = address then 0 else tx.getStorageOriginal other key := by
  by_cases ho : other = address
  · subst ho; simp [markAccountCreated, getStorageOriginal]
  · have hcmp : compare address other ≠ .eq := fun h => ho (Std.LawfulEqCmp.eq_of_compare h).symm
    simp [markAccountCreated, getStorageOriginal, Std.ExtTreeSet.mem_insert, hcmp, ho]
    rfl

/-- A change of an account keeps every word before the transaction. -/
theorem getStorageOriginal_modifyState {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.getStorageOriginal = tx.getStorageOriginal := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    split at h <;> cases h <;> rfl

/-- A rollback keeps every word before the transaction. -/
theorem getStorageOriginal_restoreTxState (tx snapshot : TransactionState) :
    (tx.restoreTxState snapshot).getStorageOriginal = tx.getStorageOriginal := rfl

/-- A wipe of the storage keeps every word before the transaction. -/
theorem getStorageOriginal_destroyStorage (tx : TransactionState) (address : Address) :
    (tx.destroyStorage address).getStorageOriginal = tx.getStorageOriginal := rfl

/-! ## The outcomes of moving ether -/

/-- The debit of the sender in a move of ether, named for the proofs below. -/
private abbrev debit (sender : Address) (amount : U256) (account : Account) :
    Except StateError Account :=
  if account.balance < amount then .error (.insufficientBalance sender)
  else .ok { account with balance := account.balance - amount }

/-- A move of ether between two addresses that succeeds meets two conditions.

The sender held the amount, and the recipient's balance stays below 2^256.

The two accounts then hold the moved balances and keep every other field.

Every other account is unchanged. -/
theorem moveEther_eq_ok {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (hne : sender ≠ recipient)
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    ¬ (tx.getAccount sender).balance < amount ∧
      (tx.getAccount recipient).balance.toNat + amount.toNat < 2 ^ 256 ∧
      tx'.getAccount sender =
        { tx.getAccount sender with balance := (tx.getAccount sender).balance - amount } ∧
      tx'.getAccount recipient =
        { tx.getAccount recipient with balance := (tx.getAccount recipient).balance + amount } ∧
      ∀ other, other ≠ sender → other ≠ recipient → tx'.getAccount other = tx.getAccount other := by
  unfold moveEther at h
  cases hmid : tx.modifyState fork sender (debit sender amount) with
  | error e => simp [hmid, bind, Except.bind] at h
  | ok mid =>
    simp only [hmid, bind, Except.bind] at h
    obtain ⟨debited, hdebit, hsender, hrest⟩ := modifyState_eq_ok hmid
    obtain ⟨credited, hcredit, hrecipient, hrest'⟩ := modifyState_eq_ok h
    simp only [debit] at hdebit
    split at hdebit
    · cases hdebit
    · rename_i hfunds
      cases hdebit
      rw [hrest recipient (Ne.symm hne)] at hcredit
      split at hcredit
      · rename_i hfit
        cases hcredit
        refine ⟨hfunds, hfit, ?_, hrecipient, fun other hs hr => ?_⟩
        · rw [hrest' sender hne, hsender]
        · rw [hrest' other hr, hrest other hs]
      · cases hcredit

/-- Moving ether between two addresses fails exactly in two cases, each with its error.

The sender holds less than the amount.

Or the sender holds the amount, and the recipient's balance would reach 2^256. -/
theorem moveEther_eq_error {fork : Fork} {tx : TransactionState} {sender recipient : Address}
    {amount : U256} {e : StateError} (hne : sender ≠ recipient) :
    tx.moveEther fork sender recipient amount = .error e ↔
      ((tx.getAccount sender).balance < amount ∧ e = .insufficientBalance sender) ∨
      (¬ (tx.getAccount sender).balance < amount ∧
        2 ^ 256 ≤ (tx.getAccount recipient).balance.toNat + amount.toNat ∧
        e = .balanceOverflow recipient) := by
  unfold moveEther
  cases hmid : tx.modifyState fork sender (debit sender amount) with
  | error e' =>
    have hf := modifyState_eq_error.mp hmid
    simp only [debit] at hf
    simp only [bind, Except.bind, Except.error.injEq]
    split at hf
    · rename_i hlt
      cases hf
      constructor
      · rintro rfl
        exact Or.inl ⟨hlt, rfl⟩
      · rintro (⟨-, rfl⟩ | ⟨hge, -⟩)
        · rfl
        · exact absurd hlt hge
    · cases hf
  | ok mid =>
    obtain ⟨debited, hdebit, -, hrest⟩ := modifyState_eq_ok hmid
    simp only [bind, Except.bind]
    rw [modifyState_eq_error, hrest recipient (Ne.symm hne)]
    simp only [debit] at hdebit
    split at hdebit
    · cases hdebit
    · rename_i hfunds
      by_cases hfit : (tx.getAccount recipient).balance.toNat + amount.toNat < 2 ^ 256
      · simp only [hfit, ↓reduceIte, reduceCtorEq, false_iff, not_or, not_and]
        exact ⟨fun h _ => hfunds h, fun _ h _ => Nat.not_le_of_gt hfit h⟩
      · simp only [hfit, ↓reduceIte, Except.error.injEq]
        constructor
        · rintro rfl
          exact Or.inr ⟨hfunds, Nat.le_of_not_gt hfit, rfl⟩
        · rintro (⟨hlt, -⟩ | ⟨-, -, rfl⟩)
          · exact absurd hlt hfunds
          · rfl

/-- Moving ether between two addresses succeeds exactly when two conditions hold.

The sender holds the amount, and the recipient's balance stays below 2^256. -/
theorem moveEther_isOk_iff {fork : Fork} {tx : TransactionState} {sender recipient : Address}
    {amount : U256} (hne : sender ≠ recipient) :
    (∃ tx', tx.moveEther fork sender recipient amount = .ok tx') ↔
      ¬ (tx.getAccount sender).balance < amount ∧
        (tx.getAccount recipient).balance.toNat + amount.toNat < 2 ^ 256 := by
  cases hm : tx.moveEther fork sender recipient amount with
  | ok tx' =>
    obtain ⟨hfunds, hfit, -⟩ := moveEther_eq_ok hne hm
    exact ⟨fun _ => ⟨hfunds, hfit⟩, fun _ => ⟨tx', rfl⟩⟩
  | error e =>
    simp only [reduceCtorEq, exists_false, false_iff, not_and]
    intro hfunds hfit
    rcases (moveEther_eq_error hne).mp hm with ⟨hlt, -⟩ | ⟨-, hover, -⟩
    · exact hfunds hlt
    · exact Nat.not_le_of_gt hfit hover

/-- Moving ether from an address to itself fails exactly when its balance is below the amount. -/
theorem moveEther_self_eq_error {fork : Fork} {tx : TransactionState} {address : Address}
    {amount : U256} {e : StateError} :
    tx.moveEther fork address address amount = .error e ↔
      (tx.getAccount address).balance < amount ∧ e = .insufficientBalance address := by
  unfold moveEther
  cases hmid : tx.modifyState fork address (debit address amount) with
  | error e' =>
    have hf := modifyState_eq_error.mp hmid
    simp only [debit] at hf
    simp only [bind, Except.bind, Except.error.injEq]
    split at hf
    · rename_i hlt
      cases hf
      exact ⟨fun h => ⟨hlt, h.symm⟩, fun h => h.2.symm⟩
    · cases hf
  | ok mid =>
    obtain ⟨debited, hdebit, hread, -⟩ := modifyState_eq_ok hmid
    simp only [bind, Except.bind]
    rw [modifyState_eq_error, hread]
    simp only [debit] at hdebit
    split at hdebit
    · cases hdebit
    · rename_i hfunds
      cases hdebit
      have hle : amount.toNat ≤ (tx.getAccount address).balance.toNat := by
        simpa [BitVec.lt_def] using hfunds
      have hfit :
          ((tx.getAccount address).balance - amount).toNat + amount.toNat < 2 ^ 256 := by
        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
        have := (tx.getAccount address).balance.isLt
        omega
      simp only [hfit, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      exact fun h => absurd h hfunds

/-- Moving ether from an address to itself succeeds exactly when the address holds the amount. -/
theorem moveEther_self_isOk_iff {fork : Fork} {tx : TransactionState} {address : Address}
    {amount : U256} :
    (∃ tx', tx.moveEther fork address address amount = .ok tx') ↔
      ¬ (tx.getAccount address).balance < amount := by
  cases hm : tx.moveEther fork address address amount with
  | ok tx' =>
    refine ⟨fun _ hlt => ?_, fun _ => ⟨tx', rfl⟩⟩
    have herr := (moveEther_self_eq_error (fork := fork)).mpr ⟨hlt, rfl⟩
    rw [hm] at herr
    cases herr
  | error e =>
    simp only [reduceCtorEq, exists_false, false_iff, Classical.not_not]
    exact (moveEther_self_eq_error.mp hm).1

/-- Moving ether keeps every code and every word before the transaction.

It also keeps the storage of every address other than the two parties. -/
theorem moveEther_preserves {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.getCode = tx.getCode ∧ tx'.getStorageOriginal = tx.getStorageOriginal ∧
      ∀ other, other ≠ sender → other ≠ recipient → ∀ key,
        tx'.getStorage other key = tx.getStorage other key := by
  unfold moveEther at h
  cases hmid : tx.modifyState fork sender (debit sender amount) with
  | error e => simp [hmid, bind, Except.bind] at h
  | ok mid =>
    simp only [hmid, bind, Except.bind] at h
    refine ⟨by rw [getCode_modifyState h, getCode_modifyState hmid],
      by rw [getStorageOriginal_modifyState h, getStorageOriginal_modifyState hmid],
      fun other hs hr key => ?_⟩
    rw [getStorage_modifyState h, getStorage_modifyState hmid]
    simp [hs, hr]

end EthLib.Execution.State.TransactionState

/-! ## Folds of writes -/

namespace EthLib.Execution.State

open Std

section Fold

variable {α β γ : Type} [Ord α] [TransOrd α] [LawfulEqOrd α] [DecidableEq α]

/-- A fold over a list with distinct keys, whose step changes only the key it reads. -/
private theorem getElem?_foldl_list
    {step : ExtTreeMap α γ compare → α → β → ExtTreeMap α γ compare}
    {F : α → β → Option γ → Option γ}
    (hstep : ∀ acc k v k', (step acc k v)[k']? = if k = k' then F k v acc[k]? else acc[k']?)
    (k : α) : ∀ (l : List (α × β)) (base : ExtTreeMap α γ compare),
      l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) →
      (∀ v, (k, v) ∈ l → (l.foldl (fun acc p => step acc p.1 p.2) base)[k]? = F k v base[k]?) ∧
      ((∀ v, (k, v) ∉ l) → (l.foldl (fun acc p => step acc p.1 p.2) base)[k]? = base[k]?)
  | [], _, _ => ⟨by simp, fun _ => rfl⟩
  | (k', v') :: rest, base, hl => by
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hl
    have ih := getElem?_foldl_list hstep k rest (step base k' v') hrest
    simp only [List.foldl_cons]
    refine ⟨fun v hv => ?_, fun hv => ?_⟩
    · rcases List.mem_cons.mp hv with hv | hv
      · -- The key is the head, so the rest never changes it again.
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
        rw [ih.2 fun w hw => hhead _ hw (by simp), hstep]
        simp
      · -- The key is in the rest, so the head is another key.
        have hne : k' ≠ k := fun h => hhead _ hv (by simp [h])
        rw [ih.1 v hv, hstep]
        simp [hne]
    · have hne : k' ≠ k := fun h => hv v' (by simp [h])
      rw [ih.2 fun w hw => hv w (List.mem_cons_of_mem _ hw), hstep]
      simp [hne]

/-- A fold whose step changes only the key it reads gives, at each key, the change of that key. -/
theorem getElem?_foldl_of_step (m : ExtTreeMap α β compare) (base : ExtTreeMap α γ compare)
    {step : ExtTreeMap α γ compare → α → β → ExtTreeMap α γ compare}
    {F : α → β → Option γ → Option γ}
    (hstep : ∀ acc k v k', (step acc k v)[k']? = if k = k' then F k v acc[k]? else acc[k']?)
    (k : α) :
    (m.foldl step base)[k]? = match m[k]? with
      | some v => F k v base[k]?
      | none => base[k]? := by
  have h := getElem?_foldl_list hstep k m.toList base m.distinct_keys_toList
  rw [ExtTreeMap.foldl_eq_foldl_toList]
  split
  · rename_i v hv
    exact h.1 v (ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hv)
  · rename_i hv
    exact h.2 fun v hmem => by simp [ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem] at hv

/-- Erasing each key of a set from a map removes those keys and keeps every other. -/
theorem getElem?_foldl_erase (s : ExtTreeSet α compare) (m : ExtTreeMap α γ compare) (k : α) :
    (s.foldl (fun acc a => acc.erase a) m)[k]? = if k ∈ s then none else m[k]? := by
  have h : ∀ (l : List α) (m : ExtTreeMap α γ compare),
      (l.foldl (fun acc a => acc.erase a) m)[k]? = if k ∈ l then none else m[k]? := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih =>
      intro m
      by_cases h : a = k
      · subst h
        simp [ih]
      · simp [ih, ExtTreeMap.getElem?_erase, h, Ne.symm h]
  simp [ExtTreeSet.foldl_eq_foldl_toList, h]

omit [DecidableEq α] in
/-- Inserting each key of a set into another gives their union. -/
theorem mem_foldl_insert (s t : ExtTreeSet α compare) (k : α) :
    k ∈ s.foldl (fun acc a => acc.insert a) t ↔ k ∈ s ∨ k ∈ t := by
  have h : ∀ (l : List α) (t : ExtTreeSet α compare),
      k ∈ l.foldl (fun acc a => acc.insert a) t ↔ k ∈ l ∨ k ∈ t := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih =>
      intro t
      simp only [List.foldl_cons, ih, ExtTreeSet.mem_insert, List.mem_cons, compare_eq_iff_eq]
      constructor
      · rintro (h | h | h) <;> simp_all
      · rintro ((h | h) | h) <;> simp_all
  simp [ExtTreeSet.foldl_eq_foldl_toList, h]

end Fold

/-! ## The state after a block -/

open EthLib.Base

namespace BlockState

/-- The words written by a block over a storage: each written key reads its word, zero or not. -/
theorem getElem?_applySlots (base slots : Std.ExtTreeMap Bytes32 U256) (key : Bytes32) :
    (applySlots base slots)[key]? = match slots[key]? with
      | some value => if value = 0 then none else some value
      | none => base[key]? := by
  unfold applySlots
  rw [getElem?_foldl_of_step (F := fun _ value _ =>
    if value = 0 then none else some value)]
  · cases slots[key]? <;> rfl
  intro acc k v k'
  by_cases hk : k = k' <;> split <;> simp_all [Std.ExtTreeMap.getElem?_erase,
    Std.ExtTreeMap.getElem?_insert]

/-- After a block, each account reads as it does at the start of a transaction of the block. -/
theorem getAccountOptional_applyChanges (block : BlockState) (address : Address) :
    block.applyChanges.getAccountOptional address =
      (TransactionState.ofBlock block).getAccountOptional address := by
  simp only [applyChanges, State.getAccountOptional, TransactionState.getAccountOptional,
    TransactionState.ofBlock, Std.ExtTreeMap.getElem?_empty]
  rw [getElem?_foldl_of_step (F := fun _ account _ => account)]
  · cases block.accountWrites[address]? <;> rfl
  · intro acc k v k'
    by_cases hk : k = k' <;> cases v <;> simp_all [Std.ExtTreeMap.getElem?_erase,
      Std.ExtTreeMap.getElem?_insert]

/-- After a block, each code reads as it does at the start of a transaction of the block. -/
theorem getCode_applyChanges (block : BlockState) (codeHash : Hash32) :
    block.applyChanges.getCode codeHash = (TransactionState.ofBlock block).getCode codeHash := by
  simp only [applyChanges, State.getCode, TransactionState.getCode, TransactionState.ofBlock,
    Std.ExtTreeMap.getElem?_empty]
  rw [getElem?_foldl_of_step (F := fun _ code _ => some code)]
  · cases block.codeWrites[codeHash]? <;> split <;> simp_all
  · intro acc k v k'
    by_cases hk : k = k' <;> simp_all [Std.ExtTreeMap.getElem?_insert]

/-- After a block, each word of storage reads as it does at the start of a transaction of it. -/
theorem getStorage_applyChanges (block : BlockState) (address : Address) (key : Bytes32) :
    block.applyChanges.getStorage address key =
      (TransactionState.ofBlock block).getStorage address key := by
  simp only [applyChanges, State.getStorage, TransactionState.getStorage,
    TransactionState.ofBlock, StorageMap.slot, Std.ExtTreeMap.getElem?_empty, Option.bind_none,
    Std.ExtTreeSet.not_mem_empty, ↓reduceIte]
  rw [getElem?_foldl_of_step (F := fun _ slots old =>
    let merged := applySlots (old.getD ∅) slots
    if merged.isEmpty then none else some merged)]
  · rw [getElem?_foldl_erase]
    cases hw : block.storageWrites[address]? with
    | none => by_cases hc : address ∈ block.storageClears <;> simp [hc]
    | some slots =>
      -- An address with no key left reads as no storage, which holds no word either.
      have hbind : ∀ merged : Std.ExtTreeMap Bytes32 U256,
          (if merged.isEmpty then none else some merged).bind (·[key]?) = merged[key]? := by
        intro merged
        split
        · rename_i hempty
          simp_all [Std.ExtTreeMap.isEmpty_iff]
        · rfl
      simp only [hbind, getElem?_applySlots]
      cases hk : slots[key]? with
      | some value =>
        by_cases hv : value = 0
        · simp [hv, hk]
        · simp only [Option.bind_some, hk]
          split <;> simp_all
      | none =>
        by_cases hc : address ∈ block.storageClears
        · simp [hc, hk]
        · cases block.preState.storage[address]? <;> simp [hc, hk]
  · intro acc k v k'
    by_cases hk : k = k' <;> split <;> simp_all [Std.ExtTreeMap.getElem?_erase,
      Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getD_eq_getD_getElem?]

/-- A block with no write leaves the state before it. -/
theorem applyChanges_ofPreState (pre : State) :
    (BlockState.mk pre ∅ ∅ ∅ ∅).applyChanges = pre := by
  simp [applyChanges, Std.ExtTreeMap.foldl_eq_foldl_toList, Std.ExtTreeSet.foldl_eq_foldl_toList,
    Std.ExtTreeMap.toList_eq_nil_iff.mpr, Std.ExtTreeSet.toList_eq_nil_iff.mpr]

end BlockState

namespace TransactionState

/-- The words written over a storage: each written key reads its word. -/
theorem getElem?_writeSlots (base slots : Std.ExtTreeMap Bytes32 U256) (key : Bytes32) :
    (writeSlots base slots)[key]? = slots[key]?.or base[key]? := by
  unfold writeSlots
  rw [getElem?_foldl_of_step (F := fun _ value _ => some value)]
  · cases slots[key]? <;> rfl
  · intro acc k v k'
    by_cases hk : k = k' <;> simp_all [Std.ExtTreeMap.getElem?_insert]

/-- After the end of a transaction, each account reads as it did in the transaction. -/
theorem getAccountOptional_incorporateTxIntoBlock (tx : TransactionState) (address : Address) :
    tx.incorporateTxIntoBlock.getAccountOptional address = tx.getAccountOptional address := by
  simp only [incorporateTxIntoBlock, ofBlock, getAccountOptional, Std.ExtTreeMap.getElem?_empty]
  rw [getElem?_foldl_of_step (F := fun _ account _ => some account)]
  · cases tx.accountWrites[address]? <;> rfl
  · intro acc k v k'
    by_cases hk : k = k' <;> simp_all [Std.ExtTreeMap.getElem?_insert]

/-- After the end of a transaction, each code reads as it did in the transaction. -/
theorem getCode_incorporateTxIntoBlock (tx : TransactionState) (codeHash : Hash32) :
    tx.incorporateTxIntoBlock.getCode codeHash = tx.getCode codeHash := by
  simp only [incorporateTxIntoBlock, ofBlock, getCode, Std.ExtTreeMap.getElem?_empty]
  rw [getElem?_foldl_of_step (F := fun _ code _ => some code)]
  · cases tx.codeWrites[codeHash]? <;> rfl
  · intro acc k v k'
    by_cases hk : k = k' <;> simp_all [Std.ExtTreeMap.getElem?_insert]

/-- After the end of a transaction, each word of storage reads as it did in the transaction. -/
theorem getStorage_incorporateTxIntoBlock (tx : TransactionState) (address : Address)
    (key : Bytes32) :
    tx.incorporateTxIntoBlock.getStorage address key = tx.getStorage address key := by
  simp only [incorporateTxIntoBlock, ofBlock, getStorage, StorageMap.slot,
    Std.ExtTreeMap.getElem?_empty, Option.bind_none, Std.ExtTreeSet.not_mem_empty, ↓reduceIte,
    mem_foldl_insert]
  rw [getElem?_foldl_of_step (F := fun _ slots old =>
    some (writeSlots (old.getD ∅) slots))]
  · rw [getElem?_foldl_erase]
    -- A wipe in the transaction hides the block's words; otherwise they show through.
    cases hw : tx.storageWrites[address]? with
    | none =>
      by_cases hc : address ∈ tx.storageClears <;> simp [hc]
    | some slots =>
      simp only [Option.bind_some, getElem?_writeSlots]
      cases hk : slots[key]? with
      | some value => simp
      | none =>
        by_cases hc : address ∈ tx.storageClears
        · simp [hc]
        · cases tx.parent.storageWrites[address]? <;> simp [hc]
  · intro acc k v k'
    by_cases hk : k = k' <;> simp_all [Std.ExtTreeMap.getElem?_insert,
      Std.ExtTreeMap.getD_eq_getD_getElem?]

end TransactionState

end EthLib.Execution.State

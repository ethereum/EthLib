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

A storage write and a change to an account record a read of the account.

A move of ether records a read of the sender and of the recipient.

A write of an account, a touch, a write of transient storage and a record of creation read nothing.

A change of the nonce never deletes the account, so it keeps every storage read.

The deletion of the touched empty accounts reads no account and keeps every storage read.

From Paris, a change that deletes an account clears its written keys and reads them.

The next transaction starts with an empty record of reads.

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

/-- A record of an account read changes no code. -/
@[simp] theorem getCode_recordAccountRead (tx : TransactionState) (address : Address)
    (codeHash : Hash32) : (tx.recordAccountRead address).getCode codeHash = tx.getCode codeHash :=
  rfl

/-- A record of an account read leaves every account alive or dead as it was. -/
@[simp] theorem isAccountAlive_recordAccountRead (tx : TransactionState) (address other : Address) :
    (tx.recordAccountRead address).isAccountAlive other = tx.isAccountAlive other := rfl

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

/-- A storage write keeps the block of the state. -/
theorem parent_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') : tx'.parent = tx.parent := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- A storage write keeps the code of every code hash. -/
theorem getCode_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') (codeHash : Hash32) :
    tx'.getCode codeHash = tx.getCode codeHash := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rfl

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

/-- A storage write leaves every word of the transient storage. -/
theorem getTransientStorage_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx')
    (other : Address) (otherKey : Bytes32) :
    tx'.getTransientStorage other otherKey = tx.getTransientStorage other otherKey := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rfl

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

/-- A wipe of the storage of an address leaves the storage of every other address. -/
theorem getStorage_destroyStorage_of_ne (tx : TransactionState) {address other : Address}
    (hne : other ≠ address) (key : Bytes32) :
    (tx.destroyStorage address).getStorage other key = tx.getStorage other key := by
  have hcmp : compare address other ≠ .eq := fun h => hne (Std.LawfulEqCmp.eq_of_compare h).symm
  simp [destroyStorage, getStorage, StorageMap.slot, Std.ExtTreeMap.getElem?_erase, hcmp,
    Std.ExtTreeSet.mem_insert]
  -- The two sides differ only in hidden arguments of the match, which `rfl` unfolds.
  rfl

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

/-- A rollback keeps every word before the transaction. -/
theorem getStorageOriginal_restoreTxState (tx snapshot : TransactionState) :
    (tx.restoreTxState snapshot).getStorageOriginal = tx.getStorageOriginal := rfl

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

/-- The removal of an account leaves no account at its address. -/
theorem accountExists_destroyAccount_self (tx : TransactionState) (address : Address) :
    (tx.destroyAccount address).accountExists address = false := by
  unfold accountExists destroyAccount
  rw [getAccountOptional_setAccount_self]
  rfl

/-- The removal of an account does not change whether another address has an account. -/
theorem accountExists_destroyAccount_of_ne (tx : TransactionState) {address other : Address}
    (hne : other ≠ address) :
    (tx.destroyAccount address).accountExists other = tx.accountExists other := by
  unfold accountExists destroyAccount
  rw [getAccountOptional_setAccount_of_ne _ _ hne, getAccountOptional_destroyStorage]

/-- The removal of the empty touched accounts leaves no account where there was none. -/
theorem accountExists_destroyTouchedEmptyAccounts {fork : Fork} {tx : TransactionState}
    {touched : List Address} {address : Address} (h : tx.accountExists address = false) :
    (tx.destroyTouchedEmptyAccounts fork touched).accountExists address = false := by
  unfold destroyTouchedEmptyAccounts
  split
  · exact h
  · induction touched generalizing tx with
    | nil => exact h
    | cons removed rest ih =>
      refine ih ?_
      dsimp only
      split
      · by_cases hne : address = removed
        · subst hne
          exact accountExists_destroyAccount_self _ _
        · rw [accountExists_destroyAccount_of_ne _ hne]
          exact h
      · exact h

/-- The removal of the empty touched accounts keeps an account with a nonce above 0. -/
theorem getAccount_destroyTouchedEmptyAccounts {fork : Fork} {tx : TransactionState}
    {touched : List Address} {address : Address} (nonce : 1 ≤ (tx.getAccount address).nonce) :
    (tx.destroyTouchedEmptyAccounts fork touched).getAccount address = tx.getAccount address := by
  unfold destroyTouchedEmptyAccounts
  split
  · rfl
  · induction touched generalizing tx with
    | nil => rfl
    | cons other rest ih =>
      have step : (if tx.accountExistsAndIsEmpty other then tx.destroyAccount other
          else tx).getAccount address = tx.getAccount address := by
        split
        · rename_i hempty
          rw [getAccount_destroyAccount]
          split
          · rename_i heq
            subst heq
            rw [eq_empty_of_accountExistsAndIsEmpty hempty] at nonce
            simp [EMPTY_ACCOUNT] at nonce
          · rfl
        · rfl
      rw [List.foldl_cons, ih (step ▸ nonce), step]

/-- A key that a storage map holds at an address is a key of the slots at that address. -/
private theorem mem_keys_of_slot {storage : StorageMap} {address : Address} {key : Bytes32}
    {value : U256} (h : storage.slot address key = some value) :
    key ∈ (storage.getD address ∅).keys := by
  unfold StorageMap.slot at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨slots, hslots, hkey⟩ := h
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hslots, Option.getD_some, Std.ExtTreeMap.mem_keys,
    Std.ExtTreeMap.mem_iff_isSome_getElem?, hkey, Option.isSome_some]

/-- The storage of an address holds a word other than zero exactly when some key reads one. -/
theorem accountHasStorage_eq_true_iff {tx : TransactionState} {address : Address} :
    tx.accountHasStorage address = true ↔ ∃ key, tx.getStorage address key ≠ 0 := by
  unfold accountHasStorage
  simp only [List.any_eq_true, bne_iff_ne, ne_eq]
  refine ⟨fun ⟨key, _, h⟩ => ⟨key, h⟩, fun ⟨key, h⟩ => ⟨key, ?_, h⟩⟩
  simp only [List.mem_append]
  unfold getStorage at h
  split at h
  · exact .inl (.inl (mem_keys_of_slot ‹_›))
  · split at h
    · exact absurd rfl h
    · split at h
      · exact .inl (.inr (mem_keys_of_slot ‹_›))
      · split at h
        · exact absurd rfl h
        · unfold State.getStorage at h
          cases hslot : StorageMap.slot tx.parent.preState.storage address key with
          | none => simp [hslot] at h
          | some value => exact .inr (mem_keys_of_slot hslot)

/-- A contract may be deployed at an address exactly when it has no nonce, code or storage.

Its account has nonce 0 and no code, by EIP-684.

Every key of its storage reads zero, by EIP-7610, at every fork. -/
theorem accountDeployable_eq_true_iff {tx : TransactionState} {address : Address} :
    tx.accountDeployable address = true ↔ (tx.getAccount address).nonce = 0 ∧
      (tx.getAccount address).codeHash = EMPTY_CODE_HASH ∧
      ∀ key, tx.getStorage address key = 0 := by
  unfold accountDeployable
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc]
  rw [← Bool.not_eq_true, accountHasStorage_eq_true_iff]
  simp

/-- An address where an account can be deployed has nonce 0. -/
theorem nonce_eq_zero_of_accountDeployable {tx : TransactionState} {address : Address}
    (h : tx.accountDeployable address = true) : (tx.getAccount address).nonce = 0 :=
  (accountDeployable_eq_true_iff.mp h).1

/-- Two states agree on whether a contract may be deployed at an address they read alike.

They must have the same account there and the same word at every key of its storage. -/
theorem accountDeployable_congr {tx tx' : TransactionState} {address : Address}
    (haccount : tx'.getAccount address = tx.getAccount address)
    (hstorage : ∀ key, tx'.getStorage address key = tx.getStorage address key) :
    tx'.accountDeployable address = tx.accountDeployable address := by
  rw [Bool.eq_iff_iff, accountDeployable_eq_true_iff, accountDeployable_eq_true_iff, haccount]
  simp only [hstorage]

/-- A change by `f` succeeds exactly when `f` does on the account.

The result then records the read and sets the account that `f` computes.

From Paris, the result deletes that account instead when it is empty. -/
theorem modifyState_eq_ok_iff {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} :
    tx.modifyState fork address f = .ok tx' ↔ ∃ account, f (tx.getAccount address) = .ok account ∧
      tx' = if fork ≥ .paris && ((tx.recordAccountRead address).setAccount address
          (some account)).accountExistsAndIsEmpty address then
        ((tx.recordAccountRead address).setAccount address (some account)).destroyAccount address
      else (tx.recordAccountRead address).setAccount address (some account) := by
  unfold modifyState
  simp only [getAccount_recordAccountRead]
  cases f (tx.getAccount address) with
  | error e => simp [bind, Except.bind]
  | ok account =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, exists_eq_left']
    split <;> rw [Except.ok.injEq, eq_comm]

/-- A change by `f` succeeds exactly when `f` does on the account.

The account then reads as the result of `f`, and every other account is unchanged. -/
theorem modifyState_eq_ok {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    ∃ account, f (tx.getAccount address) = .ok account ∧ tx'.getAccount address = account ∧
      ∀ other, other ≠ address → tx'.getAccount other = tx.getAccount other := by
  obtain ⟨account, hf, rfl⟩ := modifyState_eq_ok_iff.mp h
  refine ⟨account, hf, ?_⟩
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
  split
  · -- From Paris, the empty result is deleted, and reads as the empty account it was.
    rename_i hempty
    have heq := eq_empty_of_accountExistsAndIsEmpty (Bool.and_eq_true_iff.mp hempty).2
    simp only [hset, ↓reduceIte] at heq
    refine ⟨?_, fun other hne => ?_⟩
    · simp only [getAccount_destroyAccount, ↓reduceIte, heq]
    · simp only [getAccount_destroyAccount, hset, hne, ↓reduceIte]
  · exact ⟨by simp only [hset, ↓reduceIte], fun other hne => by simp only [hset, hne, ↓reduceIte]⟩

/-- From Paris, no change leaves an empty account behind. -/
theorem accountExistsAndIsEmpty_modifyState {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account} (hfork : fork ≥ .paris)
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.accountExistsAndIsEmpty address = false := by
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split
  · -- The empty account is deleted, so no account remains.
    simp [accountExistsAndIsEmpty, destroyAccount, getAccountOptional_setAccount_self]
  · rename_i hkeep
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
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split <;>
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
  have hmem : address ∈ (tx.recordAccountRead address).accountReads :=
    (mem_accountReads_recordAccountRead _ _ _).mpr (.inl rfl)
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split <;> exact hmem

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
  simp [moveEther, modifyState, Account.debit, h, bind, Except.bind]

/-- The debit of the sender, the first step of a move of ether, has two outcomes.

It fails when the sender holds less than the amount.

Otherwise it takes the amount from the sender, and every other account is unchanged. -/
theorem modifyState_debit (fork : Fork) (tx : TransactionState) (sender : Address)
    (amount : U256) :
    ((tx.getAccount sender).balance < amount ∧
        tx.modifyState fork sender (Account.debit sender amount) =
          .error (.insufficientBalance sender)) ∨
      (¬ (tx.getAccount sender).balance < amount ∧ ∃ mid,
        tx.modifyState fork sender (Account.debit sender amount) = .ok mid ∧
        mid.getAccount sender =
          { tx.getAccount sender with balance := (tx.getAccount sender).balance - amount } ∧
        ∀ other, other ≠ sender → mid.getAccount other = tx.getAccount other) := by
  by_cases hlt : (tx.getAccount sender).balance < amount
  · exact .inl ⟨hlt, by simp [modifyState, Account.debit, hlt, bind, Except.bind]⟩
  · -- A change by a step that succeeds gives the account that the step computes.
    have hok : ∀ {f : Account → Except StateError Account} {account : Account},
        f (tx.getAccount sender) = .ok account → ∃ mid, tx.modifyState fork sender f = .ok mid ∧
          mid.getAccount sender = account ∧
          ∀ other, other ≠ sender → mid.getAccount other = tx.getAccount other := by
      intro f account hf
      obtain ⟨mid, hmid⟩ := modifyState_isOk (fork := fork) hf
      obtain ⟨account', hf', hsender, hrest⟩ := modifyState_eq_ok hmid
      rw [hf, Except.ok.injEq] at hf'
      exact ⟨mid, hmid, hf' ▸ hsender, hrest⟩
    exact .inr ⟨hlt, hok (by simp only [Account.debit, hlt, ↓reduceIte])⟩

/-- A change of an account keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split <;> rfl

/-- Moving ether keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold moveEther at h
  rcases modifyState_debit fork tx sender amount with ⟨-, hmid⟩ | ⟨-, mid, hmid, -⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    rw [createdAccounts_modifyState h, createdAccounts_modifyState hmid]

/-- A write of storage keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- A new code keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_setCode {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold setCode at h
  rw [createdAccounts_modifyState h]
  split <;> rfl

/-- A touch of an account keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_touchAccount (tx : TransactionState) (address : Address) :
    (tx.touchAccount address).createdAccounts = tx.createdAccounts := by
  unfold touchAccount
  split <;> rfl

/-- Moving ether from an address to itself leaves every account reading as it did. -/
theorem moveEther_self {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.moveEther fork address address amount = .ok tx') :
    tx'.getAccount address = tx.getAccount address ∧
      ∀ other, other ≠ address → tx'.getAccount other = tx.getAccount other := by
  unfold moveEther at h
  rcases modifyState_debit fork tx address amount with ⟨-, hmid⟩ | ⟨-, mid, hmid, hread, hrest⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    obtain ⟨credited, hcredit, hread', hrest'⟩ := modifyState_eq_ok h
    rw [hread] at hcredit
    unfold Account.credit at hcredit
    split at hcredit
    · cases hcredit
      refine ⟨?_, fun other hne => ?_⟩
      · rw [hread', BitVec.sub_add_cancel]
      · rw [hrest' other hne, hrest other hne]
    · cases hcredit

/-! ## Failure, storage and code of a change of an account -/

/-- A change fails exactly when `f` fails on the account, with the same error. -/
theorem modifyState_eq_error {fork : Fork} {tx : TransactionState} {address : Address}
    {f : Account → Except StateError Account} {e : StateError} :
    tx.modifyState fork address f = .error e ↔ f (tx.getAccount address) = .error e := by
  cases hf : f (tx.getAccount address) with
  | error e' => simp [modifyState, getAccount_recordAccountRead, hf, bind, Except.bind]
  | ok account => simp [modifyState_eq_ok_iff.mpr ⟨account, hf, rfl⟩]

/-- A record of an account read changes no word of the storage. -/
@[simp] theorem getStorage_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).getStorage = tx.getStorage := rfl

/-- Setting an account changes no word of the storage, even when it removes the account. -/
@[simp] theorem getStorage_setAccount (tx : TransactionState) (address : Address)
    (account : Option Account) : (tx.setAccount address account).getStorage = tx.getStorage := rfl

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
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split
  · have hnone :
        (((tx.recordAccountRead address).setAccount address (some account)).destroyAccount
          address).getAccountOptional address = none := by
      simp [destroyAccount, getAccountOptional_setAccount_self]
    rw [getStorage_destroyAccount]
    by_cases ho : other = address <;> simp [ho, hnone]
  · simp [getAccountOptional_setAccount_self]

/-- A change of an account keeps its storage when it leaves an account that is not empty.

Before Paris no change deletes an account, so the storage stays whatever the account. -/
theorem getStorage_modifyState_self {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx')
    (hkeep : fork < .paris ∨ tx'.getAccount address ≠ EMPTY_ACCOUNT) (key : Bytes32) :
    tx'.getStorage address key = tx.getStorage address key := by
  rw [getStorage_modifyState h]
  split
  · rename_i hc
    exfalso
    rcases hkeep with hp | hne
    · obtain ⟨account, hf, -⟩ := modifyState_eq_ok_iff.mp h
      simp [getAccountOptional_modifyState hp hf h] at hc
    · exact hne (by simp [getAccount, hc.2])
  · rfl

/-- Setting the code of an address keeps its storage when it leaves an account that is not empty.

Before Paris it always keeps it. -/
theorem getStorage_setCode_self {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx')
    (hkeep : fork < .paris ∨ tx'.getAccount address ≠ EMPTY_ACCOUNT) (key : Bytes32) :
    tx'.getStorage address key = tx.getStorage address key := by
  dsimp only [setCode] at h
  split at h <;> exact getStorage_modifyState_self h hkeep key

/-- A change of an account changes no code. -/
theorem getCode_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.getCode = tx.getCode := by
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split <;> rfl

/-- Setting the code of an address keeps the code under its hash.

The hash must differ from the hash of the empty code. -/
theorem getCode_setCode_self {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx')
    (hne : Cryptography.Hash.Keccak.keccak256 code ≠ EMPTY_CODE_HASH) :
    tx'.getCode (Cryptography.Hash.Keccak.keccak256 code) = .ok code := by
  dsimp only [setCode] at h
  -- Naming the hash at the key type of the code map lets the insert lemma match it.
  obtain ⟨k, hk⟩ : ∃ k : Hash32, k = Cryptography.Hash.Keccak.keccak256 code := ⟨_, rfl⟩
  rw [← hk] at h hne ⊢
  split at h
  · contradiction
  · rw [getCode_modifyState h]
    simp only [getCode, Std.ExtTreeMap.getElem?_insert_self]
    exact ite_eq_right_iff.mpr fun he => absurd he hne

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
    -- The two sides differ only in the hidden instance that decides membership.
    rfl

/-- A change of an account keeps every word before the transaction. -/
theorem getStorageOriginal_modifyState {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.getStorageOriginal = tx.getStorageOriginal := by
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split <;> rfl

/-- A wipe of the storage keeps every word before the transaction. -/
theorem getStorageOriginal_destroyStorage (tx : TransactionState) (address : Address) :
    (tx.destroyStorage address).getStorageOriginal = tx.getStorageOriginal := rfl

/-! ## The outcomes of moving ether -/

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
  rcases modifyState_debit fork tx sender amount with
    ⟨-, hmid⟩ | ⟨hfunds, mid, hmid, hsender, hrest⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    obtain ⟨credited, hcredit, hrecipient, hrest'⟩ := modifyState_eq_ok h
    rw [hrest recipient (Ne.symm hne)] at hcredit
    unfold Account.credit at hcredit
    split at hcredit
    · rename_i hfit
      cases hcredit
      refine ⟨hfunds, hfit, ?_, hrecipient, fun other hs hr => ?_⟩
      · rw [hrest' sender hne, hsender]
      · rw [hrest' other hr, hrest other hs]
    · cases hcredit

/-- Moving ether keeps the sum of the balances of the sender and the recipient.

When they are one address, its balance is counted once for each name.

Every other balance is unchanged. -/
theorem moveEther_balance {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    (tx'.getAccount sender).balance.toNat + (tx'.getAccount recipient).balance.toNat =
        (tx.getAccount sender).balance.toNat + (tx.getAccount recipient).balance.toNat ∧
      ∀ other, other ≠ sender → other ≠ recipient →
        tx'.getAccount other = tx.getAccount other := by
  by_cases hne : sender = recipient
  · subst hne
    obtain ⟨hself, hrest⟩ := moveEther_self h
    exact ⟨by rw [hself], fun other hs _ => hrest other hs⟩
  obtain ⟨hfunds, hfit, hsender, hrecipient, hrest⟩ := moveEther_eq_ok hne h
  refine ⟨?_, hrest⟩
  rw [hsender, hrecipient]
  have hle : amount.toNat ≤ (tx.getAccount sender).balance.toNat := by
    simpa [BitVec.lt_def] using hfunds
  simp only [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle), BitVec.toNat_add,
    Nat.mod_eq_of_lt hfit]
  omega

/-- A move of ether keeps every nonce and every code hash, even from an address to itself. -/
theorem moveEther_nonce_codeHash {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') (address : Address) :
    (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
      (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash := by
  by_cases hne : sender = recipient
  · subst hne
    obtain ⟨hs, hrest⟩ := moveEther_self h
    by_cases ha : address = sender
    · rw [ha, hs]
      exact ⟨rfl, rfl⟩
    · rw [hrest address ha]
      exact ⟨rfl, rfl⟩
  · obtain ⟨-, -, hs, hrec, hrest⟩ := moveEther_eq_ok hne h
    by_cases ha : address = sender
    · rw [ha, hs]
      exact ⟨rfl, rfl⟩
    · by_cases hb : address = recipient
      · rw [hb, hrec]
        exact ⟨rfl, rfl⟩
      · rw [hrest address ha hb]
        exact ⟨rfl, rfl⟩

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
  rcases modifyState_debit fork tx sender amount with ⟨hlt, hmid⟩ | ⟨hfunds, mid, hmid, -, hrest⟩
  · simp only [hmid, bind, Except.bind, Except.error.injEq]
    constructor
    · rintro rfl
      exact Or.inl ⟨hlt, rfl⟩
    · rintro (⟨-, rfl⟩ | ⟨hge, -⟩)
      · rfl
      · exact absurd hlt hge
  · simp only [hmid, bind, Except.bind]
    rw [modifyState_eq_error, hrest recipient (Ne.symm hne), Account.credit]
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
  rcases modifyState_debit fork tx address amount with
    ⟨hlt, hmid⟩ | ⟨hfunds, mid, hmid, hread, -⟩
  · simp only [hmid, bind, Except.bind, Except.error.injEq]
    exact ⟨fun h => ⟨hlt, h.symm⟩, fun h => h.2.symm⟩
  · simp only [hmid, bind, Except.bind]
    rw [modifyState_eq_error, hread, Account.credit]
    have hle : amount.toNat ≤ (tx.getAccount address).balance.toNat := by
      simpa [BitVec.lt_def] using hfunds
    have hfit : ((tx.getAccount address).balance - amount).toNat + amount.toNat < 2 ^ 256 := by
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

/-- Creating ether at an address succeeds exactly when its balance stays below 2^256. -/
theorem createEther_isOk_iff {fork : Fork} {tx : TransactionState} {address : Address}
    {amount : U256} :
    (∃ tx', tx.createEther fork address amount = .ok tx') ↔
      (tx.getAccount address).balance.toNat + amount.toNat < 2 ^ 256 := by
  unfold createEther
  constructor
  · rintro ⟨tx', h⟩
    obtain ⟨account, hf, -⟩ := modifyState_eq_ok h
    unfold Account.credit at hf
    split at hf
    · assumption
    · cases hf
  · intro hfit
    exact modifyState_isOk (by simp only [Account.credit, hfit, ↓reduceIte]; rfl)

/-- Creating ether at one address adds it to that balance, and leaves every nonce and code. -/
theorem getAccount_createEther {fork : Fork} {tx tx' : TransactionState}
    {target : Address} {amount : U256} (h : tx.createEther fork target amount = .ok tx')
    (address : Address) :
    (tx'.getAccount address).balance.toNat = (tx.getAccount address).balance.toNat +
        (if target = address then amount.toNat else 0) ∧
      (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
      (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash := by
  obtain ⟨account, hf, hread, hother⟩ := modifyState_eq_ok h
  by_cases hsame : target = address
  · subst hsame
    rw [hread]
    unfold Account.credit at hf
    split at hf
    · rename_i hfit
      cases hf
      simp only [↓reduceIte, BitVec.toNat_add, Nat.mod_eq_of_lt hfit, and_self]
    · cases hf
  · rw [hother address (Ne.symm hsame)]
    simp [hsame]

/-- Creating ether for each item of a list, in order, adds to each balance the amounts of its items.

Every nonce and every code hash stays the same. -/
theorem getAccount_foldlM_createEther {α : Type} {fork : Fork} (target : α → Address)
    (amount : α → U256) (items : List α) :
    ∀ {tx tx' : TransactionState},
      items.foldlM (fun tx x => tx.createEther fork (target x) (amount x)) tx = .ok tx' →
      ∀ address, (tx'.getAccount address).balance.toNat = (tx.getAccount address).balance.toNat +
          ((items.filter (target · = address)).map fun x => (amount x).toNat).sum ∧
        (tx'.getAccount address).nonce = (tx.getAccount address).nonce ∧
        (tx'.getAccount address).codeHash = (tx.getAccount address).codeHash := by
  induction items with
  | nil =>
    intro tx tx' h address
    cases h
    simp
  | cons x rest ih =>
    intro tx tx' h address
    rw [List.foldlM_cons] at h
    cases hmid : tx.createEther fork (target x) (amount x) with
    | error e =>
      rw [hmid] at h
      cases h
    | ok mid =>
      rw [hmid] at h
      obtain ⟨hb, hn, hc⟩ := getAccount_createEther hmid address
      obtain ⟨hb', hn', hc'⟩ := ih h address
      refine ⟨?_, hn'.trans hn, hc'.trans hc⟩
      rw [hb', hb]
      by_cases hsame : target x = address <;> simp [hsame] <;> omega

/-- Creating ether for each item of a list succeeds exactly when no balance would reach 2^256.

The balance of an address counts the amounts of all its items. -/
theorem foldlM_createEther_isOk_iff {α : Type} {fork : Fork} (target : α → Address)
    (amount : α → U256) (items : List α) :
    ∀ {tx : TransactionState},
      (∃ tx', items.foldlM (fun tx x => tx.createEther fork (target x) (amount x)) tx = .ok tx') ↔
        ∀ address, (tx.getAccount address).balance.toNat +
          ((items.filter (target · = address)).map fun x => (amount x).toNat).sum < 2 ^ 256 := by
  induction items with
  | nil =>
    intro tx
    simp only [List.foldlM_nil, List.filter_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact ⟨fun _ address => (tx.getAccount address).balance.isLt, fun _ => ⟨tx, rfl⟩⟩
  | cons x rest ih =>
    intro tx
    rw [List.foldlM_cons]
    cases hmid : tx.createEther fork (target x) (amount x) with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, exists_false, false_iff, Classical.not_forall,
        Nat.not_lt]
      -- The first item already overflows the balance of its address.
      have hover : ¬ (tx.getAccount (target x)).balance.toNat + (amount x).toNat < 2 ^ 256 :=
        fun hfit => by
          obtain ⟨tx', h⟩ := createEther_isOk_iff.mpr hfit
          rw [hmid] at h
          cases h
      refine ⟨target x, ?_⟩
      simp only [List.filter_cons, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega
    | ok mid =>
      simp only [bind, Except.bind]
      rw [ih]
      refine forall_congr' fun address => ?_
      rw [(getAccount_createEther hmid address).1]
      by_cases hsame : target x = address <;> simp [hsame] <;> omega

/-- Moving ether keeps every code. -/
theorem getCode_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.getCode = tx.getCode := by
  unfold moveEther at h
  rcases modifyState_debit fork tx sender amount with ⟨-, hmid⟩ | ⟨-, mid, hmid, -⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    rw [getCode_modifyState h, getCode_modifyState hmid]

/-- Moving ether keeps every word before the transaction. -/
theorem getStorageOriginal_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.getStorageOriginal = tx.getStorageOriginal := by
  unfold moveEther at h
  rcases modifyState_debit fork tx sender amount with ⟨-, hmid⟩ | ⟨-, mid, hmid, -⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    rw [getStorageOriginal_modifyState h, getStorageOriginal_modifyState hmid]

/-! ## The exact record of reads -/

/-- A record of an account read adds the address to the account reads.

It keeps the storage reads. -/
theorem reads_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).accountReads = tx.accountReads.insert address ∧
      (tx.recordAccountRead address).storageReads = tx.storageReads :=
  ⟨rfl, rfl⟩

/-- A record of a storage read adds the key to the storage reads of the address.

It keeps the account reads. -/
theorem reads_recordStorageRead (tx : TransactionState) (address : Address) (key : Bytes32) :
    (tx.recordStorageRead address key).accountReads = tx.accountReads ∧
      (tx.recordStorageRead address key).storageReads =
        tx.storageReads.insert address ((tx.storageReads.getD address ∅).insert key) :=
  ⟨rfl, rfl⟩

/-- Taking the reads of another state gives exactly the reads of that state. -/
theorem reads_withReadsOf (tx other : TransactionState) :
    (tx.withReadsOf other).accountReads = other.accountReads ∧
      (tx.withReadsOf other).storageReads = other.storageReads :=
  ⟨rfl, rfl⟩

/-- A wipe of the storage of an address keeps the account reads.

It adds each key that the transaction wrote at the address to the storage reads of the address. -/
theorem reads_destroyStorage (tx : TransactionState) (address : Address) :
    (tx.destroyStorage address).accountReads = tx.accountReads ∧
      (tx.destroyStorage address).storageReads = tx.storageReads.insert address
        ((tx.storageReads.getD address ∅).insertMany (tx.storageWrites.getD address ∅).keys) :=
  ⟨rfl, rfl⟩

/-- A deletion of an account records the reads of the wipe of its storage, and no other read. -/
theorem reads_destroyAccount (tx : TransactionState) (address : Address) :
    (tx.destroyAccount address).accountReads = tx.accountReads ∧
      (tx.destroyAccount address).storageReads = (tx.destroyStorage address).storageReads :=
  ⟨rfl, rfl⟩

/-- A storage write that succeeds adds the address to the account reads.

It keeps the storage reads. -/
theorem reads_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧ tx'.storageReads = tx.storageReads := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

/-- A change by `f` that succeeds adds the address to the account reads.

From Paris, a result of `f` that is the empty account deletes the account.

The storage reads then gain the keys that the wipe of its storage drops.

Otherwise the change keeps the storage reads. -/
theorem reads_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    ∃ account, f (tx.getAccount address) = .ok account ∧
      tx'.accountReads = tx.accountReads.insert address ∧
      tx'.storageReads =
        if fork ≥ .paris ∧ account = EMPTY_ACCOUNT then (tx.destroyStorage address).storageReads
        else tx.storageReads := by
  unfold modifyState at h
  simp only [getAccount_recordAccountRead] at h
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    refine ⟨account, rfl, ?_⟩
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    -- The written account exists, so it is empty exactly when it is the empty account.
    have hempty : ((tx.recordAccountRead address).setAccount address
        (some account)).accountExistsAndIsEmpty address = decide (account = EMPTY_ACCOUNT) := by
      simp only [accountExistsAndIsEmpty, getAccountOptional_setAccount_self]
      cases account
      simp only [EMPTY_ACCOUNT, Account.mk.injEq, Bool.decide_and]
      ac_rfl
    rw [hempty] at h
    split at h <;> cases h
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨rfl, by rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)]; rfl⟩
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨rfl, by rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]; rfl⟩

/-- Before Paris, a change of an account that succeeds keeps the storage reads. -/
theorem storageReads_modifyState_of_lt_paris {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account} (hfork : fork < .paris)
    (h : tx.modifyState fork address f = .ok tx') : tx'.storageReads = tx.storageReads := by
  obtain ⟨_, _, _, hreads⟩ := reads_modifyState h
  rw [hreads, ite_eq_right_of_eq_false _ _
    (eq_false fun hcond => absurd hcond.1 (Nat.not_le_of_lt hfork))]

/-- A change of an account that succeeds keeps the storage reads of every other address. -/
theorem getElem?_storageReads_modifyState_of_ne {fork : Fork} {tx tx' : TransactionState}
    {address other : Address} {f : Account → Except StateError Account} (hne : other ≠ address)
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.storageReads[other]? = tx.storageReads[other]? := by
  obtain ⟨_, _, _, hreads⟩ := reads_modifyState h
  rw [hreads]
  split
  · simp [destroyStorage, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]
  · rfl

/-- A change of an account that succeeds gives the storage reads at that address.

From Paris, an empty result deletes the account and turns its written keys into reads.

Otherwise the storage reads at the address stay as they were. -/
theorem getElem?_storageReads_modifyState_self {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.storageReads[address]? =
      if fork ≥ .paris ∧ tx'.getAccount address = EMPTY_ACCOUNT then
        (tx.destroyStorage address).storageReads[address]?
      else tx.storageReads[address]? := by
  obtain ⟨account, hf, rfl, -⟩ := modifyState_eq_ok h
  obtain ⟨account', hf', -, hreads⟩ := reads_modifyState h
  rw [hf, Except.ok.injEq] at hf'
  subst hf'
  rw [hreads]
  split <;> rfl

/-- A change of an account that succeeds keeps its storage writes at every other address. -/
theorem getD_storageWrites_modifyState_of_ne {fork : Fork} {tx tx' : TransactionState}
    {address other : Address} {f : Account → Except StateError Account} (hne : other ≠ address)
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.storageWrites.getD other ∅ = tx.storageWrites.getD other ∅ := by
  obtain ⟨_, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  split
  · simp [destroyAccount, setAccount, destroyStorage, Std.ExtTreeMap.getD_erase, Ne.symm hne,
      recordAccountRead]
  · rfl

/-- A change of an account that succeeds clears its storage writes when it deletes the account.

Otherwise its storage writes at the address stay as they were. -/
theorem getD_storageWrites_modifyState_self {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork address f = .ok tx') :
    tx'.storageWrites.getD address ∅ =
      if fork ≥ .paris ∧ tx'.getAccount address = EMPTY_ACCOUNT then ∅
      else tx.storageWrites.getD address ∅ := by
  obtain ⟨account, hf, hread, -⟩ := modifyState_eq_ok h
  rw [hread]
  obtain ⟨account', hf', rfl⟩ := modifyState_eq_ok_iff.mp h
  rw [hf, Except.ok.injEq] at hf'
  subst hf'
  have hempty : ((tx.recordAccountRead address).setAccount address
      (some account)).accountExistsAndIsEmpty address = decide (account = EMPTY_ACCOUNT) := by
    simp only [accountExistsAndIsEmpty, getAccountOptional_setAccount_self]
    cases account
    simp only [EMPTY_ACCOUNT, Account.mk.injEq, Bool.decide_and]
    ac_rfl
  rw [hempty]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    simp [destroyAccount, setAccount, destroyStorage]
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    rfl

/-- At one address, two changes in sequence give the storage reads of a wipe when either wipes.

Otherwise they keep the storage reads at that address. -/
theorem getElem?_storageReads_modifyState_modifyState {fork : Fork}
    {tx mid tx' : TransactionState} {address other : Address}
    {f g : Account → Except StateError Account}
    (h1 : tx.modifyState fork address f = .ok mid)
    (h2 : mid.modifyState fork other g = .ok tx') (z : Address) :
    tx'.storageReads[z]? =
      if fork ≥ .paris ∧ ((z = address ∧ mid.getAccount address = EMPTY_ACCOUNT) ∨
          (z = other ∧ tx'.getAccount other = EMPTY_ACCOUNT)) then
        (tx.destroyStorage z).storageReads[z]?
      else tx.storageReads[z]? := by
  by_cases hz2 : z = other
  · subst hz2
    rw [getElem?_storageReads_modifyState_self h2]
    by_cases hz1 : z = address
    · subst hz1
      by_cases hp : fork ≥ .paris
      · by_cases he1 : mid.getAccount z = EMPTY_ACCOUNT
        · have hw : mid.storageWrites.getD z ∅ = ∅ := by
            rw [getD_storageWrites_modifyState_self h1]
            simp [hp, he1]
          have hr : mid.storageReads[z]? = (tx.destroyStorage z).storageReads[z]? := by
            rw [getElem?_storageReads_modifyState_self h1]
            simp [hp, he1]
          have hd : (mid.destroyStorage z).storageReads[z]? = mid.storageReads[z]? := by
            simp [destroyStorage, hw, Std.ExtTreeMap.keys_eq_nil_iff.mpr rfl,
              Std.ExtTreeSet.insertMany_nil, Std.ExtTreeMap.getD_eq_getD_getElem?, hr]
          by_cases he2 : tx'.getAccount z = EMPTY_ACCOUNT <;> simp [hp, he1, he2, hd, hr]
        · have hw : mid.storageWrites.getD z ∅ = tx.storageWrites.getD z ∅ := by
            rw [getD_storageWrites_modifyState_self h1]
            simp [hp, he1]
          have hr : mid.storageReads[z]? = tx.storageReads[z]? := by
            rw [getElem?_storageReads_modifyState_self h1]
            simp [hp, he1]
          have hd : (mid.destroyStorage z).storageReads[z]? =
              (tx.destroyStorage z).storageReads[z]? := by
            simp [destroyStorage, hw, Std.ExtTreeMap.getD_eq_getD_getElem?, hr]
          by_cases he2 : tx'.getAccount z = EMPTY_ACCOUNT <;> simp [hp, he1, he2, hd, hr]
      · rw [getElem?_storageReads_modifyState_self h1]
        simp [hp]
    · have hw : mid.storageWrites.getD z ∅ = tx.storageWrites.getD z ∅ :=
        getD_storageWrites_modifyState_of_ne hz1 h1
      have hr : mid.storageReads[z]? = tx.storageReads[z]? :=
        getElem?_storageReads_modifyState_of_ne hz1 h1
      have hd : (mid.destroyStorage z).storageReads[z]? =
          (tx.destroyStorage z).storageReads[z]? := by
        simp [destroyStorage, hw, Std.ExtTreeMap.getD_eq_getD_getElem?, hr]
      by_cases hp : fork ≥ .paris <;> by_cases he2 : tx'.getAccount z = EMPTY_ACCOUNT <;>
        simp [hp, hz1, he2, hd, hr]
  · rw [getElem?_storageReads_modifyState_of_ne hz2 h2]
    by_cases hz1 : z = address
    · subst hz1
      rw [getElem?_storageReads_modifyState_self h1]
      by_cases hp : fork ≥ .paris <;> by_cases he1 : mid.getAccount z = EMPTY_ACCOUNT <;>
        simp [hp, hz2, he1]
    · rw [getElem?_storageReads_modifyState_of_ne hz1 h1]
      simp [hz1, hz2]

/-- A move of ether that succeeds adds the sender and the recipient to the account reads.

It keeps the storage reads of every other address.

Before Paris, it keeps every storage read. -/
theorem reads_moveEther {fork : Fork} {tx tx' : TransactionState} {sender recipient : Address}
    {amount : U256} (h : tx.moveEther fork sender recipient amount = .ok tx') :
    tx'.accountReads = (tx.accountReads.insert sender).insert recipient ∧
      (∀ other, other ≠ sender → other ≠ recipient →
        tx'.storageReads[other]? = tx.storageReads[other]?) ∧
      (fork < .paris → tx'.storageReads = tx.storageReads) := by
  unfold moveEther at h
  cases hmid : tx.modifyState fork sender (Account.debit sender amount) with
  | error e => simp [hmid, bind, Except.bind] at h
  | ok mid =>
    simp only [hmid, bind, Except.bind] at h
    obtain ⟨_, _, hmidReads, _⟩ := reads_modifyState hmid
    obtain ⟨_, _, hReads, _⟩ := reads_modifyState h
    refine ⟨by rw [hReads, hmidReads], fun other hs hr => ?_, fun hfork => ?_⟩
    · rw [getElem?_storageReads_modifyState_of_ne hr h,
        getElem?_storageReads_modifyState_of_ne hs hmid]
    · rw [storageReads_modifyState_of_lt_paris hfork h,
        storageReads_modifyState_of_lt_paris hfork hmid]

/-- A move of ether gives the storage reads at every address.

From Paris, an address that the debit or the credit leaves empty has its written keys read. -/
theorem getElem?_storageReads_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') (address : Address) :
    tx'.storageReads[address]? =
      if fork ≥ .paris ∧
          ((address = sender ∧
              { tx.getAccount sender with balance := (tx.getAccount sender).balance - amount } =
                EMPTY_ACCOUNT) ∨
            (address = recipient ∧ tx'.getAccount recipient = EMPTY_ACCOUNT)) then
        (tx.destroyStorage address).storageReads[address]?
      else tx.storageReads[address]? := by
  unfold moveEther at h
  rcases modifyState_debit fork tx sender amount with
    ⟨-, hmid⟩ | ⟨-, mid, hmid, hsender, -⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    rw [getElem?_storageReads_modifyState_modifyState hmid h address, hsender]

/-- Moving ether clears the storage writes of an address that it deletes, and keeps the rest. -/
theorem getD_storageWrites_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') (address : Address) :
    tx'.storageWrites.getD address ∅ =
      if fork ≥ .paris ∧
          ((address = sender ∧
              { tx.getAccount sender with balance := (tx.getAccount sender).balance - amount } =
                EMPTY_ACCOUNT) ∨
            (address = recipient ∧ tx'.getAccount recipient = EMPTY_ACCOUNT)) then ∅
      else tx.storageWrites.getD address ∅ := by
  unfold moveEther at h
  rcases modifyState_debit fork tx sender amount with
    ⟨-, hmid⟩ | ⟨-, mid, hmid, hsender, -⟩
  · simp [hmid, bind, Except.bind] at h
  · simp only [hmid, bind, Except.bind] at h
    by_cases hra : address = recipient
    · subst hra
      rw [getD_storageWrites_modifyState_self h]
      by_cases hsa : address = sender
      · subst hsa
        rw [getD_storageWrites_modifyState_self hmid, hsender]
        by_cases hp : fork ≥ .paris <;>
          by_cases he1 : { tx.getAccount address with
              balance := (tx.getAccount address).balance - amount } = EMPTY_ACCOUNT <;>
          by_cases he2 : tx'.getAccount address = EMPTY_ACCOUNT <;>
          simp [hp, he1, he2]
      · rw [getD_storageWrites_modifyState_of_ne hsa hmid]
        by_cases hp : fork ≥ .paris <;> by_cases he2 : tx'.getAccount address = EMPTY_ACCOUNT <;>
          simp [hp, hsa, he2]
    · rw [getD_storageWrites_modifyState_of_ne hra h]
      by_cases hsa : address = sender
      · subst hsa
        rw [getD_storageWrites_modifyState_self hmid, hsender]
        by_cases hp : fork ≥ .paris <;>
          by_cases he1 : { tx.getAccount address with
              balance := (tx.getAccount address).balance - amount } = EMPTY_ACCOUNT <;>
          simp [hp, hra, he1]
      · rw [getD_storageWrites_modifyState_of_ne hsa hmid]
        simp [hsa, hra]

/-- A write of an account keeps the account reads and the storage reads. -/
theorem reads_setAccount (tx : TransactionState) (address : Address) (account : Option Account) :
    (tx.setAccount address account).accountReads = tx.accountReads ∧
      (tx.setAccount address account).storageReads = tx.storageReads :=
  ⟨rfl, rfl⟩

/-- A record of a created account keeps the account reads and the storage reads. -/
theorem reads_markAccountCreated (tx : TransactionState) (address : Address) :
    (tx.markAccountCreated address).accountReads = tx.accountReads ∧
      (tx.markAccountCreated address).storageReads = tx.storageReads :=
  ⟨rfl, rfl⟩

/-- A write of transient storage keeps the account reads and the storage reads. -/
theorem reads_setTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32)
    (value : U256) :
    (tx.setTransientStorage address key value).accountReads = tx.accountReads ∧
      (tx.setTransientStorage address key value).storageReads = tx.storageReads :=
  ⟨rfl, rfl⟩

/-- A touch of an account keeps the account reads and the storage reads. -/
theorem reads_touchAccount (tx : TransactionState) (address : Address) :
    (tx.touchAccount address).accountReads = tx.accountReads ∧
      (tx.touchAccount address).storageReads = tx.storageReads := by
  unfold touchAccount
  split <;> exact ⟨rfl, rfl⟩

/-- A change by `f` that succeeds adds the address to the account reads.

It keeps the storage reads of every other address.

Before Paris, it keeps every storage read. -/
theorem reads_modifyState_eq_insert {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧
      (∀ other, other ≠ address → tx'.storageReads[other]? = tx.storageReads[other]?) ∧
      (fork < .paris → tx'.storageReads = tx.storageReads) := by
  obtain ⟨_, _, hreads, _⟩ := reads_modifyState h
  exact ⟨hreads, fun _ hne => getElem?_storageReads_modifyState_of_ne hne h,
    fun hfork => storageReads_modifyState_of_lt_paris hfork h⟩

/-- A credit of ether that succeeds adds the address to the account reads.

It keeps the storage reads of every other address.

Before Paris, it keeps every storage read. -/
theorem reads_createEther {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.createEther fork address amount = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧
      (∀ other, other ≠ address → tx'.storageReads[other]? = tx.storageReads[other]?) ∧
      (fork < .paris → tx'.storageReads = tx.storageReads) :=
  reads_modifyState_eq_insert h

/-- A change of the balance adds the address to the account reads.

It keeps the storage reads of every other address.

Before Paris, it keeps every storage read. -/
theorem reads_setAccountBalance {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧
      (∀ other, other ≠ address → tx'.storageReads[other]? = tx.storageReads[other]?) ∧
      (fork < .paris → tx'.storageReads = tx.storageReads) :=
  reads_modifyState_eq_insert h

/-- A change of the nonce adds the address to the account reads, and keeps the storage reads.

The account it leaves has a nonce that is not zero, so it is never deleted. -/
theorem reads_incrementNonce {fork : Fork} {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧ tx'.storageReads = tx.storageReads := by
  obtain ⟨account, hf, hacc, hst⟩ := reads_modifyState h
  cases hf
  refine ⟨hacc, ?_⟩
  rw [hst, ite_eq_right_of_eq_false _ _ (eq_false fun hc => ?_)]
  have := congrArg Account.nonce hc.2
  simp [EMPTY_ACCOUNT] at this

/-- A write of code adds the address to the account reads.

It keeps the storage reads of every other address.

Before Paris, it keeps every storage read. -/
theorem reads_setCode {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧
      (∀ other, other ≠ address → tx'.storageReads[other]? = tx.storageReads[other]?) ∧
      (fork < .paris → tx'.storageReads = tx.storageReads) := by
  unfold setCode at h
  dsimp only at h
  have := reads_modifyState_eq_insert h
  -- The code goes into the store of codes, which holds no read.
  split at this <;> exact this

/-- A second wipe of the storage of an address records no new read. -/
theorem storageReads_destroyStorage_destroyStorage (tx : TransactionState) (address : Address) :
    ((tx.destroyStorage address).destroyStorage address).storageReads =
      (tx.destroyStorage address).storageReads := by
  apply Std.ExtTreeMap.ext_getElem?
  intro other
  by_cases hother : other = address
  · subst hother
    simp [destroyStorage, Std.ExtTreeMap.keys_eq_nil_iff.mpr rfl, Std.ExtTreeSet.insertMany_nil]
  · simp [destroyStorage, Std.ExtTreeMap.getElem?_insert, Ne.symm hother]

/-- Clearing an account adds the address to the account reads.

Its storage reads are those of the wipe of the storage of the address. -/
theorem reads_clearAccountPreservingBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx') :
    tx'.accountReads = tx.accountReads.insert address ∧
      tx'.storageReads = (tx.destroyStorage address).storageReads := by
  obtain ⟨_, _, hacc, hst⟩ := reads_modifyState h
  refine ⟨hacc, ?_⟩
  rw [hst]
  split
  · exact storageReads_destroyStorage_destroyStorage tx address
  · rfl

/-- The deletion of the touched empty accounts keeps the account reads and every storage read.

It keeps the storage reads of every address that is not touched. -/
theorem reads_destroyTouchedEmptyAccounts (fork : Fork) (tx : TransactionState)
    (touched : List Address) :
    (tx.destroyTouchedEmptyAccounts fork touched).accountReads = tx.accountReads ∧
      (∀ other, other ∉ touched →
        (tx.destroyTouchedEmptyAccounts fork touched).storageReads[other]? =
          tx.storageReads[other]?) ∧
      (∀ other key, key ∈ tx.storageReads.getD other ∅ →
        key ∈ (tx.destroyTouchedEmptyAccounts fork touched).storageReads.getD other ∅) := by
  unfold destroyTouchedEmptyAccounts
  split
  · exact ⟨rfl, fun _ _ => rfl, fun _ _ h => h⟩
  induction touched generalizing tx with
  | nil => exact ⟨rfl, fun _ _ => rfl, fun _ _ h => h⟩
  | cons address rest ih =>
    by_cases he : tx.accountExistsAndIsEmpty address = true
    · simp only [List.foldl_cons, he, ite_true]
      obtain ⟨hacc, hother, hmem⟩ := ih (tx.destroyAccount address)
      refine ⟨hacc, fun other hn => ?_, fun other key hk => hmem other key
        (mem_storageReads_destroyStorage_of_mem hk)⟩
      rw [hother other (fun hm => hn (List.mem_cons_of_mem _ hm))]
      have hne : address ≠ other := fun he => hn (he ▸ List.mem_cons_self)
      simp [destroyAccount, setAccount, destroyStorage, Std.ExtTreeMap.getElem?_insert, hne]
    · simp only [List.foldl_cons, he, Bool.false_eq_true, ite_false]
      obtain ⟨hacc, hother, hmem⟩ := ih tx
      exact ⟨hacc, fun other hn => hother other (fun hm => hn (List.mem_cons_of_mem _ hm)),
        hmem⟩

/-- The next transaction starts with no account read and no storage read. -/
theorem reads_incorporateTxIntoBlock (tx : TransactionState) :
    tx.incorporateTxIntoBlock.accountReads = ∅ ∧ tx.incorporateTxIntoBlock.storageReads = ∅ :=
  ⟨rfl, rfl⟩

/-! ## A write to a slot of an account that exists -/

/-- A storage write to an address with an account succeeds. -/
theorem exists_setStorage {tx : TransactionState} {address : Address} (key : Bytes32)
    (value : U256) (h : (tx.getAccountOptional address).isSome = true) :
    ∃ tx', tx.setStorage address key value = .ok tx' := by
  unfold setStorage
  rw [ite_eq_right (by simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using h)]
  exact ⟨_, rfl⟩

/-- A storage write leaves the account of every address. -/
theorem getAccountOptional_setStorage {tx tx' : TransactionState} {address other : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.getAccountOptional other = tx.getAccountOptional other := by
  unfold setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- Recording a storage read twice records it once. -/
theorem recordStorageRead_recordStorageRead (tx : TransactionState) (address : Address)
    (key : Bytes32) :
    (tx.recordStorageRead address key).recordStorageRead address key =
      tx.recordStorageRead address key := by
  simp only [recordStorageRead]
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro other
  by_cases h : other = address
  · subst h
    simp only [Std.ExtTreeMap.getElem?_insert_self, Std.ExtTreeMap.getD_insert_self]
    congr 1
    ext x
    simp only [Std.ExtTreeSet.mem_insert]
    exact or_self_left
  · simp [Std.ExtTreeMap.getElem?_insert, Ne.symm h]

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

/-- A block that starts from the state after a block reads each account as that block does. -/
theorem getAccount_applyChanges (block : BlockState) (address : Address) :
    (TransactionState.ofBlock ⟨block.applyChanges, ∅, ∅, ∅, ∅⟩).getAccount address =
      (TransactionState.ofBlock block).getAccount address := by
  unfold TransactionState.getAccount
  rw [← getAccountOptional_applyChanges block address]
  simp [TransactionState.getAccountOptional, TransactionState.ofBlock]

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

/-- The block that a transaction joins reads each account as the transaction left it. -/
theorem getAccount_ofBlock_incorporateTxIntoBlock (tx : TransactionState) (address : Address) :
    (ofBlock tx.incorporateTxIntoBlock.parent).getAccount address = tx.getAccount address := by
  unfold getAccount
  rw [← getAccountOptional_incorporateTxIntoBlock tx address]
  rfl

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

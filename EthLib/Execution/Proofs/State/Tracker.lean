module

public import EthLib.Execution.State.Tracker

/-!
# Proofs: the transaction state

A read after a write returns the written value, and a write leaves every other place alone.

A storage write leaves the words before the transaction unchanged.

Restoring a snapshot restores every read of the snapshot.

A move of ether keeps the sum of the two balances, and fails when the sender lacks the amount.

Each new transaction starts with an empty transient storage.

The end of a transaction keeps every read of the transaction.

The state after a block reads as the block does at the start of its next transaction.
-/

@[expose] public section

namespace EthLib.Execution.State.TransactionState

open EthLib.Base

/-! ## Accounts -/

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
    · simp [getStorage, StorageMap.slot, Std.ExtTreeMap.getElem?_insert, Ne.symm hne]
    · by_cases haddress : other = address
      · subst haddress
        simp [getStorage, StorageMap.slot, Std.ExtTreeMap.getElem?_insert, Ne.symm hne,
          Std.ExtTreeMap.getD_eq_getD_getElem?]
        cases tx.storageWrites[other]? <;> simp
      · simp [getStorage, StorageMap.slot, Std.ExtTreeMap.getElem?_insert, Ne.symm haddress]

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
  cases hf : f (tx.getAccount address) with
  | error e => simp [hf, bind, Except.bind] at h
  | ok account =>
    refine ⟨account, rfl, ?_⟩
    have hset : ∀ other, (tx.setAccount address (some account)).getAccount other =
        if other = address then account else tx.getAccount other := by
      intro other
      unfold getAccount
      split
      · subst other
        rw [getAccountOptional_setAccount_self]
        rfl
      · rename_i hne
        rw [getAccountOptional_setAccount_of_ne _ _ hne]
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
  simp only [modifyState, hf, bind, Except.bind, pure, Except.pure, decide_eq_false hlt,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  subst h
  exact getAccountOptional_setAccount_self _ _ _

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

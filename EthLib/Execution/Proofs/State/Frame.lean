module

public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the addresses that a write of the transaction state touches

Each write of a transaction's state names the addresses it changes.

It leaves the account, the storage and the transient storage of every other address as they were.

Two runs of writes compose, so a run changes nothing outside the union of the addresses it names.

A move of ether from an account that holds code to itself changes no account and no storage.

A rollback to a snapshot of the same block gives back the snapshot's accounts and storage.

The statements cover the account, the storage and the transient storage only.

They say nothing about the original words of storage, the created accounts or the records of reads.

The end of a transaction clears the transient storage of every address, so it is left out.

Code is kept under its hash and not under an address, so the statements leave it out.

A touch of an account keeps every code, and the account at every other address.
-/

@[expose] public section

namespace EthLib.Execution.State.TransactionState

open EthLib.Base

/-- The state `tx'` reads as `tx` at every address outside `touched`.

That holds for the account, every word of storage and every word of transient storage. -/
def SameOutside (touched : List Address) (tx tx' : TransactionState) : Prop :=
  ∀ address, address ∉ touched →
    tx'.getAccountOptional address = tx.getAccountOptional address ∧
    (∀ key, tx'.getStorage address key = tx.getStorage address key) ∧
    ∀ key, tx'.getTransientStorage address key = tx.getTransientStorage address key

/-! ## The relation -/

/-- A state reads as itself outside every list of addresses. -/
theorem SameOutside.refl (touched : List Address) (tx : TransactionState) :
    SameOutside touched tx tx :=
  fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- The relation composes, over the union of the two lists. -/
theorem SameOutside.trans {first second : List Address} {tx tx' tx'' : TransactionState}
    (h : SameOutside first tx tx') (h' : SameOutside second tx' tx'') :
    SameOutside (first ++ second) tx tx'' := by
  intro address hmem
  rw [List.mem_append, not_or] at hmem
  obtain ⟨a, s, t⟩ := h address hmem.1
  obtain ⟨a', s', t'⟩ := h' address hmem.2
  exact ⟨a'.trans a, fun key => (s' key).trans (s key), fun key => (t' key).trans (t key)⟩

/-- The relation still holds for a list that contains the first one. -/
theorem SameOutside.mono {first second : List Address} {tx tx' : TransactionState}
    (h : SameOutside first tx tx') (sub : ∀ address, address ∈ first → address ∈ second) :
    SameOutside second tx tx' :=
  fun address hmem => h address fun hfirst => hmem (sub address hfirst)

/-! ## Each write -/

/-- Setting an account touches that address only. -/
theorem sameOutside_setAccount (tx : TransactionState) (address : Address)
    (account : Option Account) : SameOutside [address] tx (tx.setAccount address account) :=
  fun other hmem =>
    ⟨getAccountOptional_setAccount_of_ne tx account (by simpa using hmem), fun _ => rfl,
      fun _ => rfl⟩

/-- A record of an account read touches no address. -/
theorem sameOutside_recordAccountRead (tx : TransactionState) (address : Address) :
    SameOutside [] tx (tx.recordAccountRead address) :=
  fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- A record of a storage read touches no address. -/
theorem sameOutside_recordStorageRead (tx : TransactionState) (address : Address)
    (key : Bytes32) : SameOutside [] tx (tx.recordStorageRead address key) :=
  fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- Taking the records of reads of another state touches no address. -/
theorem sameOutside_withReadsOf (tx other : TransactionState) :
    SameOutside [] tx (tx.withReadsOf other) :=
  fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- Wiping the storage of an address touches that address only. -/
theorem sameOutside_destroyStorage (tx : TransactionState) (address : Address) :
    SameOutside [address] tx (tx.destroyStorage address) :=
  fun other hmem =>
    ⟨rfl, fun key => getStorage_destroyStorage_of_ne tx (by simpa using hmem) key, fun _ => rfl⟩

/-- Deleting an account touches that address only. -/
theorem sameOutside_destroyAccount (tx : TransactionState) (address : Address) :
    SameOutside [address] tx (tx.destroyAccount address) :=
  ((sameOutside_destroyStorage tx address).trans
    (sameOutside_setAccount _ address none)).mono (by simp)

/-- A record of the creation of an account touches no address.

It changes the original words of storage at that address, which the relation leaves out. -/
theorem sameOutside_markAccountCreated (tx : TransactionState) (address : Address) :
    SameOutside [] tx (tx.markAccountCreated address) :=
  fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩

/-- Giving an address the empty account touches that address only. -/
theorem sameOutside_touchAccount (tx : TransactionState) (address : Address) :
    SameOutside [address] tx (tx.touchAccount address) := by
  unfold touchAccount
  split
  · exact SameOutside.refl _ tx
  · exact sameOutside_setAccount tx address _

/-- A touch of an account keeps the code of every code hash. -/
theorem getCode_touchAccount (tx : TransactionState) (address : Address) (hash : Hash32) :
    (tx.touchAccount address).getCode hash = tx.getCode hash := by
  unfold touchAccount
  split <;> rfl

/-- A touch of an account keeps the block of the state. -/
theorem parent_touchAccount (tx : TransactionState) (address : Address) :
    (tx.touchAccount address).parent = tx.parent := by
  unfold touchAccount
  split <;> rfl

/-- After a touch, the address has an account. -/
theorem isSome_getAccountOptional_touchAccount (tx : TransactionState) (address : Address) :
    ((tx.touchAccount address).getAccountOptional address).isSome := by
  unfold touchAccount
  split
  · assumption
  · simp [setAccount, getAccountOptional]

/-- A touch of an account keeps the account at every other address. -/
theorem getAccount_touchAccount {tx : TransactionState} {address other : Address}
    (hne : other ≠ address) : (tx.touchAccount address).getAccount other = tx.getAccount other := by
  unfold getAccount
  rw [(sameOutside_touchAccount tx address other (by simpa using hne)).1]

/-- A touch of an account keeps the account it reads at that address.

An address with no account reads as the empty account before and after. -/
theorem getAccount_touchAccount_self (tx : TransactionState) (address : Address) :
    (tx.touchAccount address).getAccount address = tx.getAccount address := by
  unfold touchAccount
  split
  · rfl
  · rename_i hnot
    have hnone : tx.getAccountOptional address = none := by
      simpa [accountExists, Option.isSome_iff_ne_none] using hnot
    simp [getAccount, getAccountOptional_setAccount_self, hnone]

/-- A write of transient storage touches the address it names only. -/
theorem sameOutside_setTransientStorage (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    SameOutside [address] tx (tx.setTransientStorage address key value) :=
  fun other hmem =>
    ⟨rfl, fun _ => rfl, fun otherKey =>
      getTransientStorage_setTransientStorage_of_ne tx value (Or.inl (by simpa using hmem))⟩

/-- A successful write of storage touches the address it names only. -/
theorem sameOutside_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') :
    SameOutside [address] tx tx' := by
  intro other hmem
  have hne : other ≠ address := by simpa using hmem
  refine ⟨?_, fun otherKey =>
    getStorage_setStorage_of_ne h (Or.inl hne) , fun _ => ?_⟩
  all_goals
    unfold setStorage at h
    split at h
    · cases h
    · cases h
      rfl

/-- A successful change of an account touches that address only. -/
theorem sameOutside_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    SameOutside [address] tx tx' := by
  obtain ⟨account, -, rfl⟩ := modifyState_eq_ok_iff.mp h
  have base : SameOutside [address] tx
      ((tx.recordAccountRead address).setAccount address (some account)) :=
    ((sameOutside_recordAccountRead tx address).trans
      (sameOutside_setAccount _ address (some account))).mono (by simp)
  split
  · exact (base.trans (sameOutside_destroyAccount _ address)).mono (by simp)
  · exact base

/-- A successful increment of a nonce touches that address only. -/
theorem sameOutside_incrementNonce {fork : Fork} {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : SameOutside [address] tx tx' :=
  sameOutside_modifyState h

/-- A successful write of a balance touches that address only. -/
theorem sameOutside_setAccountBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    SameOutside [address] tx tx' :=
  sameOutside_modifyState h

/-- A successful creation of ether at an address touches that address only. -/
theorem sameOutside_createEther {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.createEther fork address amount = .ok tx') :
    SameOutside [address] tx tx' :=
  sameOutside_modifyState h

/-- A successful write of the code of an address touches that address only.

The code itself is kept under its hash, so the statement leaves it out. -/
theorem sameOutside_setCode {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    SameOutside [address] tx tx' := by
  dsimp only [setCode] at h
  split at h
  · exact sameOutside_modifyState h
  · -- Storing the code changes no account, storage or transient storage.
    have base : ∀ codeWrites, SameOutside [] tx { tx with codeWrites } :=
      fun _ _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩
    exact (base _ |>.trans (sameOutside_modifyState h)).mono (by simp)

/-- A successful clear of an account touches that address only. -/
theorem sameOutside_clearAccountPreservingBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx') :
    SameOutside [address] tx tx' :=
  ((sameOutside_destroyStorage tx address).trans (sameOutside_modifyState h)).mono (by simp)

/-- A successful move of ether touches the sender and the recipient only. -/
theorem sameOutside_moveEther {fork : Fork} {tx tx' : TransactionState}
    {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') :
    SameOutside [sender, recipient] tx tx' := by
  unfold moveEther at h
  cases h1 : tx.modifyState fork sender (Account.debit sender amount) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok mid =>
    rw [h1] at h
    exact ((sameOutside_modifyState h1).trans (sameOutside_modifyState h)).mono (by simp)

/-- The account at an address that holds code is not empty, so no change of it deletes it. -/
theorem accountExistsAndIsEmpty_setAccount_of_code {tx : TransactionState} {address : Address}
    {account : Account} (hcode : account.codeHash ≠ EMPTY_CODE_HASH) :
    (tx.setAccount address (some account)).accountExistsAndIsEmpty address = false := by
  simp [accountExistsAndIsEmpty, getAccountOptional_setAccount_self, hcode]

/-- A change whose result holds code records a read of the account, then sets it. -/
theorem modifyState_eq_of_code {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx')
    (keeps : ∀ account, f (tx.getAccount address) = .ok account →
      account.codeHash ≠ EMPTY_CODE_HASH) :
    ∃ account, f (tx.getAccount address) = .ok account ∧
      tx' = (tx.recordAccountRead address).setAccount address (some account) := by
  obtain ⟨account, hf, rfl⟩ := modifyState_eq_ok_iff.mp h
  refine ⟨account, hf, ?_⟩
  split
  · rename_i hc
    simp [accountExistsAndIsEmpty_setAccount_of_code (keeps account hf)] at hc
  · rfl

/-- A move of ether from an account that holds code to itself touches no address. -/
theorem sameOutside_moveEther_self {fork : Fork}
    {tx tx' : TransactionState} {address : Address} {amount : U256}
    (hcode : (tx.getAccount address).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork address address amount = .ok tx') : SameOutside [] tx tx' := by
  unfold moveEther at h
  cases h1 : tx.modifyState fork address (Account.debit address amount) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok mid =>
    rw [h1] at h
    have debit : ∀ account, Account.debit address amount (tx.getAccount address) = .ok account →
        account.codeHash ≠ EMPTY_CODE_HASH := by
      intro account hf
      simp only [Account.debit] at hf
      split at hf
      · cases hf
      · cases hf; exact hcode
    obtain ⟨acc1, hf1, rfl⟩ := modifyState_eq_of_code h1 debit
    simp only [Account.debit] at hf1
    split at hf1
    · cases hf1
    · cases hf1
      have hget : ((tx.recordAccountRead address).setAccount address
          (some { tx.getAccount address with balance := (tx.getAccount address).balance - amount
            })).getAccount address =
          { tx.getAccount address with balance := (tx.getAccount address).balance - amount } := by
        simp [getAccount, getAccountOptional_setAccount_self]
      change modifyState fork _ address (Account.credit address amount) = .ok tx' at h
      have credit : ∀ account, Account.credit address amount
          (((tx.recordAccountRead address).setAccount address (some { tx.getAccount address with
            balance := (tx.getAccount address).balance - amount })).getAccount address) =
            .ok account → account.codeHash ≠ EMPTY_CODE_HASH := by
        intro account hf
        rw [hget] at hf
        simp only [Account.credit] at hf
        split at hf
        · cases hf; exact hcode
        · cases hf
      obtain ⟨acc2, hf2, rfl⟩ := modifyState_eq_of_code h credit
      rw [hget] at hf2
      simp only [Account.credit] at hf2
      split at hf2
      · cases hf2
        intro b _
        refine ⟨?_, fun _ => rfl, fun _ => rfl⟩
        by_cases hb : b = address
        · subst hb
          have hsome : tx.getAccountOptional b = some (tx.getAccount b) := by
            cases hx : tx.getAccountOptional b with
            | some account => simp [getAccount, hx]
            | none => exact absurd (by simp [getAccount, hx, EMPTY_ACCOUNT]) hcode
          rw [hsome, getAccountOptional_setAccount_self]
          congr 1
          cases hacc : tx.getAccount b
          simp [BitVec.sub_add_cancel]
        · simp [getAccountOptional_setAccount_of_ne _ _ hb]
      · cases hf2

/-- The deletion of the touched empty accounts touches those accounts only. -/
theorem sameOutside_destroyTouchedEmptyAccounts (fork : Fork) (tx : TransactionState)
    (touched : List Address) :
    SameOutside touched tx (tx.destroyTouchedEmptyAccounts fork touched) := by
  unfold destroyTouchedEmptyAccounts
  split
  · exact SameOutside.refl _ tx
  · -- Each step deletes at most the account it visits, which `touched` lists.
    suffices ∀ (rest : List Address) (acc : TransactionState), (∀ a ∈ rest, a ∈ touched) →
        SameOutside touched acc (rest.foldl (fun tx address =>
          if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx) acc) from
      this touched tx fun _ h => h
    intro rest
    induction rest with
    | nil => exact fun acc _ => SameOutside.refl _ acc
    | cons head rest ih =>
      intro acc hsub
      simp only [List.foldl_cons]
      have step : SameOutside touched acc
          (if acc.accountExistsAndIsEmpty head then acc.destroyAccount head else acc) := by
        split
        · exact (sameOutside_destroyAccount acc head).mono
            (by simpa using hsub head (by simp))
        · exact SameOutside.refl _ acc
      exact (step.trans (ih _ fun a ha => hsub a (by simp [ha]))).mono (by simp)

/-! ## A rollback -/

/-- A rollback to a snapshot of the same block gives back the snapshot's accounts and storage.

That holds for the account, the storage and the transient storage at every address. -/
theorem sameOutside_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent) :
    SameOutside [] snapshot (tx.restoreTxState snapshot) :=
  fun address _ =>
    ⟨getAccountOptional_restoreTxState hparent address,
      getStorage_restoreTxState hparent address,
      getTransientStorage_restoreTxState tx snapshot address⟩

end EthLib.Execution.State.TransactionState

module

public import EthLib.Execution.Proofs.State.Tracker

/-!
# Proofs: the addresses that a write of the transaction state touches

A write of the transaction state names the addresses it changes.

It leaves the account, the storage and the transient storage of every other address as they were.

So a run of writes changes nothing outside the addresses that its writes name.

A rollback to a snapshot makes every address read as in the snapshot.

The statements are about the writes of the state alone.

They say nothing about the opcodes, the messages or the records of reads.

Code is kept under its hash and not under an address, so they leave it out.
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

/-- Two runs of writes change nothing outside the addresses that either names. -/
theorem SameOutside.trans {first second : List Address} {tx tx' tx'' : TransactionState}
    (h : SameOutside first tx tx') (h' : SameOutside second tx' tx'') :
    SameOutside (first ++ second) tx tx'' := by
  intro address hmem
  rw [List.mem_append, not_or] at hmem
  obtain ⟨a, s, t⟩ := h address hmem.1
  obtain ⟨a', s', t'⟩ := h' address hmem.2
  exact ⟨a'.trans a, fun key => (s' key).trans (s key), fun key => (t' key).trans (t key)⟩

/-- A longer list of addresses says less. -/
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

/-- A record of the creation of an account touches no address. -/
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

/-- A write of transient storage touches the address it names only. -/
theorem sameOutside_setTransientStorage (tx : TransactionState) (address : Address)
    (key : Bytes32) (value : U256) :
    SameOutside [address] tx (tx.setTransientStorage address key value) :=
  fun other hmem =>
    ⟨rfl, fun _ => rfl, fun otherKey =>
      getTransientStorage_setTransientStorage_of_ne tx value (Or.inl (by simpa using hmem))⟩

/-- A write of storage touches the address it names only. -/
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

/-- A change of an account touches that address only. -/
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

/-- Adding one to a nonce touches that address only. -/
theorem sameOutside_incrementNonce {fork : Fork} {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : SameOutside [address] tx tx' :=
  sameOutside_modifyState h

/-- Setting a balance touches that address only. -/
theorem sameOutside_setAccountBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} {amount : U256} (h : tx.setAccountBalance fork address amount = .ok tx') :
    SameOutside [address] tx tx' :=
  sameOutside_modifyState h

/-- Creating ether at an address touches that address only. -/
theorem sameOutside_createEther {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {amount : U256} (h : tx.createEther fork address amount = .ok tx') :
    SameOutside [address] tx tx' :=
  sameOutside_modifyState h

/-- Setting the code of an address touches that address only.

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

/-- Clearing an account touches that address only. -/
theorem sameOutside_clearAccountPreservingBalance {fork : Fork} {tx tx' : TransactionState}
    {address : Address} (h : tx.clearAccountPreservingBalance fork address = .ok tx') :
    SameOutside [address] tx tx' :=
  ((sameOutside_destroyStorage tx address).trans (sameOutside_modifyState h)).mono (by simp)

/-- A move of ether touches the sender and the recipient only. -/
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

/-- After a rollback, every address reads as in the snapshot. -/
theorem sameOutside_restoreTxState {tx snapshot : TransactionState}
    (hparent : tx.parent = snapshot.parent) :
    SameOutside [] snapshot (tx.restoreTxState snapshot) :=
  fun address _ =>
    ⟨getAccountOptional_restoreTxState hparent address ▸ rfl,
      fun key => getStorage_restoreTxState hparent address key,
      fun key => getTransientStorage_restoreTxState tx snapshot address key⟩

end EthLib.Execution.State.TransactionState

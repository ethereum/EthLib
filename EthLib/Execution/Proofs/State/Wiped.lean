module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: the writes that keep or wipe the storage of an address

Only a write of storage at an address changes some words of its storage.

Every other write of the transaction state keeps the storage of each address, or wipes it whole.

A wipe comes from the deletion of an account, or from the creation of a contract.

A write wipes the storage of an empty account, or of an account that SELFDESTRUCT marked.

The creation of a contract wipes the storage of the new account too.
-/

@[expose] public section

namespace EthLib.Execution.State.TransactionState

open EthLib.Base

/-- The storage of `address` in `tx'` reads as in `tx`, or reads 0 at every key. -/
def KeptOrWiped (address : Address) (tx tx' : TransactionState) : Prop :=
  tx'.getStorage address = tx.getStorage address ∨ tx'.getStorage address = fun _ => 0

namespace KeptOrWiped

variable {address : Address} {tx tx' tx'' : TransactionState}

/-- A state keeps its own storage. -/
theorem refl (address : Address) (tx : TransactionState) : KeptOrWiped address tx tx :=
  .inl rfl

/-- Two writes that each keep or wipe the storage keep or wipe it together. -/
theorem trans (h : KeptOrWiped address tx tx') (h' : KeptOrWiped address tx' tx'') :
    KeptOrWiped address tx tx'' := by
  rcases h' with h' | h'
  · rcases h with h | h
    · exact .inl (h'.trans h)
    · exact .inr (h'.trans h)
  · exact .inr h'

/-- A state with the same storage keeps it. -/
theorem of_eq (h : ∀ key, tx'.getStorage address key = tx.getStorage address key) :
    KeptOrWiped address tx tx' :=
  .inl (funext h)

/-- A state that reads as another outside some addresses keeps the storage of the others. -/
theorem of_sameOutside {touched : List Address} (h : SameOutside touched tx tx')
    (hout : address ∉ touched) : KeptOrWiped address tx tx' :=
  of_eq (h address hout).2.1

end KeptOrWiped

variable {fork : Fork} {address : Address} {tx tx' : TransactionState}

/-- A change of an account keeps the storage of every address, or wipes it by a deletion. -/
theorem keptOrWiped_modifyState {other : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork other f = .ok tx') : KeptOrWiped address tx tx' := by
  -- The change deletes its account from Paris, when it leaves it empty.
  by_cases hd : address = other ∧ tx'.getAccountOptional other = none
  · exact .inr (funext fun key => by rw [getStorage_modifyState h, ite_eq_left hd])
  · exact .of_eq fun key => by rw [getStorage_modifyState h, ite_eq_right hd]

/-- A move of ether keeps the storage of every address, or wipes it by a deletion. -/
theorem keptOrWiped_moveEther {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') : KeptOrWiped address tx tx' := by
  unfold moveEther at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  exact (keptOrWiped_modifyState h1).trans (keptOrWiped_modifyState h2)

/-- New ether keeps the storage of every address, or wipes it by a deletion. -/
theorem keptOrWiped_createEther {other : Address} {amount : U256}
    (h : tx.createEther fork other amount = .ok tx') : KeptOrWiped address tx tx' :=
  keptOrWiped_modifyState h

/-- A rise of a nonce keeps the storage of every address, or wipes it by a deletion. -/
theorem keptOrWiped_incrementNonce {other : Address}
    (h : tx.incrementNonce fork other = .ok tx') : KeptOrWiped address tx tx' :=
  keptOrWiped_modifyState h

/-- A new balance keeps the storage of every address, or wipes it by a deletion. -/
theorem keptOrWiped_setAccountBalance {other : Address} {amount : U256}
    (h : tx.setAccountBalance fork other amount = .ok tx') : KeptOrWiped address tx tx' :=
  keptOrWiped_modifyState h

/-- New code keeps the storage of every address, or wipes it by a deletion. -/
theorem keptOrWiped_setCode {other : Address} {code : ByteArray}
    (h : tx.setCode fork other code = .ok tx') : KeptOrWiped address tx tx' := by
  dsimp only [setCode] at h
  split at h
  · exact keptOrWiped_modifyState h
  · -- The new code joins the store of codes, which holds no storage.
    have k := keptOrWiped_modifyState (address := address) h
    exact k

/-- A wipe of the storage of an address keeps or wipes the storage of every address. -/
theorem keptOrWiped_destroyStorage (other : Address) :
    KeptOrWiped address tx (tx.destroyStorage other) := by
  by_cases ho : address = other
  · subst ho
    exact .inr (funext fun key => getStorage_destroyStorage _ _ key)
  · exact .of_eq fun key => getStorage_destroyStorage_of_ne _ ho key

/-- A deletion of an account keeps or wipes the storage of every address. -/
theorem keptOrWiped_destroyAccount (other : Address) :
    KeptOrWiped address tx (tx.destroyAccount other) := by
  by_cases ho : address = other
  · exact .inr (funext fun key => by rw [getStorage_destroyAccount, ite_eq_left ho])
  · exact .of_eq fun key => by rw [getStorage_destroyAccount, ite_eq_right ho]

/-- The clearing of an account that keeps its balance keeps or wipes the storage of every address.
-/
theorem keptOrWiped_clearAccountPreservingBalance {other : Address}
    (h : tx.clearAccountPreservingBalance fork other = .ok tx') : KeptOrWiped address tx tx' :=
  (keptOrWiped_destroyStorage other).trans (keptOrWiped_modifyState h)

/-- A write of storage at another address keeps the storage of `address`. -/
theorem keptOrWiped_setStorage {other : Address} {key : Bytes32} {value : U256}
    (h : tx.setStorage other key value = .ok tx') (hne : address ≠ other) :
    KeptOrWiped address tx tx' :=
  .of_eq fun _ => getStorage_setStorage_of_ne h (.inl hne)

/-- A new account at an address with none keeps the storage of every address. -/
theorem keptOrWiped_touchAccount (other : Address) :
    KeptOrWiped address tx (tx.touchAccount other) := by
  unfold touchAccount
  split
  · exact .refl _ _
  · exact .of_eq fun _ => rfl

/-- The deletion of the touched empty accounts keeps or wipes the storage of every address. -/
theorem keptOrWiped_destroyTouchedEmptyAccounts (touched : List Address) :
    KeptOrWiped address tx (tx.destroyTouchedEmptyAccounts fork touched) := by
  unfold destroyTouchedEmptyAccounts
  split
  · exact .refl _ _
  · induction touched generalizing tx with
    | nil => exact .refl _ _
    | cons other rest ih =>
      simp only [List.foldl_cons]
      refine KeptOrWiped.trans ?_ ih
      by_cases hx : tx.accountExistsAndIsEmpty other = true
      · rw [ite_eq_left hx]
        exact keptOrWiped_destroyAccount other
      · rw [ite_eq_right hx]
        exact .refl _ _

/-! ## Wipes of an empty account -/

/-- The account at `address` is empty: nonce 0, no code and balance 0.

An address with no account reads as the empty account. -/
def EmptyAt (address : Address) (tx : TransactionState) : Prop :=
  (tx.getAccount address).nonce = 0 ∧ (tx.getAccount address).codeHash = EMPTY_CODE_HASH ∧
    (tx.getAccount address).balance = 0

/-- The storage of `address` in `tx'` reads as in `tx`, or reads 0 from an account empty in `tx`.

An account that is empty in `tx'` was empty in `tx` too. -/
def KeptOrWipedEmpty (address : Address) (tx tx' : TransactionState) : Prop :=
  (tx'.getStorage address = tx.getStorage address ∨
    (tx'.getStorage address = fun _ => 0) ∧ EmptyAt address tx) ∧
  (EmptyAt address tx' → EmptyAt address tx)

namespace KeptOrWipedEmpty

variable {address : Address} {tx tx' tx'' : TransactionState}

/-- A state keeps its own storage. -/
theorem refl (address : Address) (tx : TransactionState) : KeptOrWipedEmpty address tx tx :=
  ⟨.inl rfl, id⟩

/-- Two changes that each keep the storage or wipe an empty account do so together. -/
theorem trans (h : KeptOrWipedEmpty address tx tx') (h' : KeptOrWipedEmpty address tx' tx'') :
    KeptOrWipedEmpty address tx tx'' := by
  refine ⟨?_, fun e => h.2 (h'.2 e)⟩
  rcases h'.1 with h1 | ⟨h1, e1⟩
  · rcases h.1 with h0 | ⟨h0, e0⟩
    · exact .inl (h1.trans h0)
    · exact .inr ⟨h1.trans h0, e0⟩
  · exact .inr ⟨h1, h.2 e1⟩

/-- A state with the same account and storage at `address` keeps them. -/
theorem of_eq (hacc : tx'.getAccount address = tx.getAccount address)
    (hs : ∀ key, tx'.getStorage address key = tx.getStorage address key) :
    KeptOrWipedEmpty address tx tx' :=
  ⟨.inl (funext hs), fun e => by
    unfold EmptyAt at e ⊢
    rw [← hacc]
    exact e⟩

/-- A state that reads as another outside some addresses keeps the others. -/
theorem of_sameOutside {touched : List Address} (h : SameOutside touched tx tx')
    (hout : address ∉ touched) : KeptOrWipedEmpty address tx tx' :=
  of_eq (h.getAccount_eq hout) (h address hout).2.1

/-- A change that keeps the storage or wipes an empty account keeps or wipes it. -/
theorem keptOrWiped (h : KeptOrWipedEmpty address tx tx') : KeptOrWiped address tx tx' :=
  h.1.imp id And.left

end KeptOrWipedEmpty

/-- An account that exists and is empty is empty. -/
theorem emptyAt_of_accountExistsAndIsEmpty (h : tx.accountExistsAndIsEmpty address = true) :
    EmptyAt address tx := by
  unfold accountExistsAndIsEmpty at h
  unfold EmptyAt getAccount
  split at h
  · rename_i account hacc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp [hacc, h]
  · cases h

/-- A change that gives an account a nonce keeps that account, as the change computes it. -/
theorem getAccount_modifyState_of_nonce {other : Address}
    {f : Account → Except StateError Account} {account : Account}
    (h : tx.modifyState fork other f = .ok tx') (hf : f (tx.getAccount other) = .ok account)
    (hn : account.nonce ≠ 0) : tx'.getAccount other = account := by
  obtain ⟨account', hf', rfl⟩ := modifyState_eq_ok_iff.mp h
  rw [hf] at hf'
  cases hf'
  split
  · rename_i hdel
    obtain ⟨-, ⟨h0, -⟩, -⟩ := by
      simpa [accountExistsAndIsEmpty, getAccountOptional_setAccount_self] using hdel
    exact absurd h0 hn
  · simp [getAccount, getAccountOptional_setAccount_self]

/-- A change of an account keeps the storage of `address`, or wipes it from an empty account.

A change of the account at `address` must leave it empty only if it was empty. -/
theorem keptOrWipedEmpty_modifyState {other : Address} {f : Account → Except StateError Account}
    (h : tx.modifyState fork other f = .ok tx')
    (keeps : other = address → ∀ account, f (tx.getAccount address) = .ok account →
      account.nonce = 0 → account.codeHash = EMPTY_CODE_HASH → account.balance = 0 →
        EmptyAt address tx) :
    KeptOrWipedEmpty address tx tx' := by
  by_cases ho : other = address
  · subst ho
    obtain ⟨account, hf, rfl⟩ := modifyState_eq_ok_iff.mp h
    split
    · -- From Paris, an account that the change leaves empty is deleted with its storage.
      rename_i hdel
      obtain ⟨-, ⟨hn, hc⟩, hb⟩ := by
        simpa [accountExistsAndIsEmpty, getAccountOptional_setAccount_self] using hdel
      have E := keeps rfl account hf hn hc hb
      exact ⟨.inr ⟨funext fun key => by rw [getStorage_destroyAccount, ite_eq_left rfl], E⟩,
        fun _ => E⟩
    · refine ⟨.inl (by simp), fun e => ?_⟩
      have ha : ((tx.recordAccountRead other).setAccount other (some account)).getAccount other =
          account := by
        simp [getAccount, getAccountOptional_setAccount_self]
      unfold EmptyAt at e
      rw [ha] at e
      exact keeps rfl account hf e.1 e.2.1 e.2.2
  · exact .of_sameOutside (sameOutside_modifyState h) (by simpa using Ne.symm ho)

/-- New ether keeps the storage of `address`, or wipes it from an empty account. -/
theorem keptOrWipedEmpty_createEther {other : Address} {amount : U256}
    (h : tx.createEther fork other amount = .ok tx') : KeptOrWipedEmpty address tx tx' := by
  refine keptOrWipedEmpty_modifyState h fun _ account hf hn hc hb => ?_
  unfold Account.credit at hf
  split at hf
  · rename_i hfit
    cases hf
    -- The sum fits in 256 bits, so a sum of 0 has two terms of 0.
    have hsum := congrArg BitVec.toNat hb
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit] at hsum
    refine ⟨hn, hc, BitVec.eq_of_toNat_eq ?_⟩
    simp at hsum ⊢
    omega
  · cases hf

/-- A move of ether keeps the storage of `address`, or wipes it from an empty account.

A move from `address` must start where the account has a nonce. -/
theorem keptOrWipedEmpty_moveEther {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx')
    (funded : sender = address → (tx.getAccount address).nonce ≠ 0) :
    KeptOrWipedEmpty address tx tx' := by
  unfold moveEther at h
  obtain ⟨mid, h1, h2⟩ := bind_ok_iff.mp h
  refine KeptOrWipedEmpty.trans (keptOrWipedEmpty_modifyState h1 fun hs account hf hn _ _ => ?_)
    (keptOrWipedEmpty_createEther (other := recipient) h2)
  -- A debit keeps the nonce.
  unfold Account.debit at hf
  split at hf
  · cases hf
  · cases hf
    exact absurd hn (funded hs)

/-- A rise of a nonce keeps the storage of `address`, or wipes it from an empty account. -/
theorem keptOrWipedEmpty_incrementNonce {other : Address}
    (h : tx.incrementNonce fork other = .ok tx') : KeptOrWipedEmpty address tx tx' :=
  keptOrWipedEmpty_modifyState h fun _ account hf hn _ _ => by
    cases hf
    simp at hn

/-- New code keeps the storage of `address`, or wipes it from an empty account.

At `address`, the account must hold no code while its nonce is 0. -/
theorem keptOrWipedEmpty_setCode {other : Address} {code : ByteArray}
    (h : tx.setCode fork other code = .ok tx')
    (keeps : other = address → (tx.getAccount address).nonce = 0 →
      (tx.getAccount address).codeHash = EMPTY_CODE_HASH) :
    KeptOrWipedEmpty address tx tx' := by
  dsimp only [setCode] at h
  split at h
  · refine keptOrWipedEmpty_modifyState h fun ho account hf hn _ hb => ?_
    cases hf
    exact ⟨hn, keeps ho hn, hb⟩
  · -- The new code joins the store of codes, which holds no account.
    have k := keptOrWipedEmpty_modifyState (address := address) h fun ho account hf hn _ hb => by
      cases hf
      exact ⟨hn, keeps ho hn, hb⟩
    exact (KeptOrWipedEmpty.of_eq rfl fun _ => rfl).trans k

/-- The deletion of an account keeps the storage of `address`, or wipes it from an empty account.

The account at `address` must be empty, if the deletion is at `address`. -/
theorem keptOrWipedEmpty_destroyAccount {other : Address}
    (empty : other = address → EmptyAt address tx) :
    KeptOrWipedEmpty address tx (tx.destroyAccount other) := by
  by_cases ho : other = address
  · subst ho
    have E := empty rfl
    exact ⟨.inr ⟨funext fun key => by rw [getStorage_destroyAccount, ite_eq_left rfl], E⟩,
      fun _ => E⟩
  · exact .of_sameOutside (sameOutside_destroyAccount tx other) (by simpa using Ne.symm ho)

/-- A new account at an address with none keeps the storage of `address`. -/
theorem keptOrWipedEmpty_touchAccount (other : Address) :
    KeptOrWipedEmpty address tx (tx.touchAccount other) := by
  by_cases ho : other = address
  · subst ho
    exact .of_eq (getAccount_touchAccount_self tx other) fun key => by
      unfold touchAccount
      split <;> rfl
  · exact .of_sameOutside (sameOutside_touchAccount tx other) (by simpa using Ne.symm ho)

/-- The deletion of the touched empty accounts keeps the storage of `address`, or wipes it.

It wipes it only from an empty account. -/
theorem keptOrWipedEmpty_destroyTouchedEmptyAccounts (touched : List Address) :
    KeptOrWipedEmpty address tx (tx.destroyTouchedEmptyAccounts fork touched) := by
  unfold destroyTouchedEmptyAccounts
  split
  · exact .refl _ _
  · induction touched generalizing tx with
    | nil => exact .refl _ _
    | cons other rest ih =>
      simp only [List.foldl_cons]
      refine KeptOrWipedEmpty.trans ?_ ih
      by_cases hx : tx.accountExistsAndIsEmpty other = true
      · rw [ite_eq_left hx]
        exact keptOrWipedEmpty_destroyAccount fun ho =>
          ho ▸ emptyAt_of_accountExistsAndIsEmpty hx
      · rw [ite_eq_right hx]
        exact .refl _ _

end EthLib.Execution.State.TransactionState

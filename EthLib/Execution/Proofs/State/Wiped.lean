module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: the writes that keep or wipe the storage of an address

Only a write of storage at an address changes some words of its storage.

Every other write of the transaction state keeps the storage of each address, or wipes it whole.

A wipe comes from the deletion of an account, or from the creation of a contract.
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

end EthLib.Execution.State.TransactionState

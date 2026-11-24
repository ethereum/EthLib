module

public import EthLib.Execution.Proofs.State.Tracker
public import Mathlib.Data.Finset.Card

/-!
# Proofs: the fresh slots of a transaction

A slot is fresh when its word was zero before the transaction and is not zero now.

From Glamsterdam, a write that makes a slot fresh pays the state gas of a new slot.

A write that clears a fresh slot refills that state gas, by [EIP-8037][eip8037].

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#specification
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base

/-- The pairs of an address and a key that a storage map holds. -/
def StorageMap.entries (storage : StorageMap) : Finset (Address × Bytes32) :=
  (storage.toList.flatMap fun entry => entry.2.keys.map fun key => (entry.1, key)).toFinset

namespace TransactionState

/-- The slots whose word was zero before the transaction and is not zero now.

A word that no layer holds reads zero, so the keys of the layers hold every such slot. -/
def freshSlots (tx : TransactionState) : Finset (Address × Bytes32) :=
  (StorageMap.entries tx.storageWrites ∪ StorageMap.entries tx.parent.storageWrites ∪
      StorageMap.entries tx.parent.preState.storage).filter
    fun slot => tx.getStorageOriginal slot.1 slot.2 = 0 ∧ tx.getStorage slot.1 slot.2 ≠ 0

end TransactionState

/-- A storage map holds a pair exactly when it holds a word at that address and key. -/
theorem StorageMap.mem_entries {storage : StorageMap} {address : Address} {key : Bytes32} :
    (address, key) ∈ StorageMap.entries storage ↔ (storage.slot address key).isSome := by
  simp only [StorageMap.entries, StorageMap.slot, List.mem_toFinset, List.mem_flatMap,
    List.mem_map, Prod.mk.injEq, Std.ExtTreeMap.mem_keys]
  constructor
  · rintro ⟨⟨a, slots⟩, h1, k, h2, rfl, rfl⟩
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at h1
    simp [h1, h2]
  · intro h
    cases hs : storage[address]? with
    | none => simp [hs] at h
    | some slots =>
      simp only [hs, Option.bind_some, Std.ExtTreeMap.isSome_getElem?_iff_mem] at h
      exact ⟨(address, slots), Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hs, key, h,
        rfl, rfl⟩

namespace TransactionState

/-- A slot is fresh exactly when its word was zero before the transaction and is not zero now. -/
theorem mem_freshSlots {tx : TransactionState} {address : Address} {key : Bytes32} :
    (address, key) ∈ tx.freshSlots ↔
      tx.getStorageOriginal address key = 0 ∧ tx.getStorage address key ≠ 0 := by
  simp only [freshSlots, Finset.mem_filter, Finset.mem_union, StorageMap.mem_entries]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- A word that is not zero comes from one of the three layers.
  have h1 := h.2
  unfold getStorage at h1
  cases hw : tx.storageWrites.slot address key with
  | some _ => exact Or.inl (Or.inl (by simp))
  | none =>
    cases hp : tx.parent.storageWrites.slot address key with
    | some _ => exact Or.inl (Or.inr (by simp))
    | none =>
      cases hs : StorageMap.slot tx.parent.preState.storage address key with
      | some _ => exact Or.inr (by simp)
      | none => simp [hw, hp, State.getStorage, hs] at h1

/-- A transaction with no write has no fresh slot. -/
theorem freshSlots_ofBlock (block : BlockState) : (ofBlock block).freshSlots = ∅ := by
  ext ⟨address, key⟩
  simp only [mem_freshSlots, Finset.notMem_empty, iff_false, not_and, not_not]
  -- With no write, no wipe and no creation, every word is the word before the transaction.
  have h : (ofBlock block).getStorage address key =
      (ofBlock block).getStorageOriginal address key := by
    simp [getStorage, getStorageOriginal, ofBlock, StorageMap.slot]
  rw [h]
  exact id

/-- A storage write makes its slot fresh, or not, and leaves every other slot as it was.

Its slot is fresh after it when the word before the transaction was zero and the new word is not.
-/
theorem freshSlots_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.freshSlots =
      if tx.getStorageOriginal address key = 0 ∧ value ≠ 0 then
        insert (address, key) tx.freshSlots
      else tx.freshSlots.erase (address, key) := by
  ext ⟨other, otherKey⟩
  -- The write keeps every word before the transaction.
  rw [mem_freshSlots, getStorageOriginal_setStorage h]
  by_cases hs : other = address ∧ otherKey = key
  · -- The slot of the write now holds the new word.
    obtain ⟨rfl, rfl⟩ := hs
    rw [getStorage_setStorage_self h]
    split_ifs with hc
    · simpa using hc
    · simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false]
      exact hc
  · -- Every other slot keeps its word.
    have hne : other ≠ address ∨ otherKey ≠ key := by tauto
    have hp : (other, otherKey) ≠ (address, key) := by
      simp only [ne_eq, Prod.mk.injEq]
      tauto
    rw [getStorage_setStorage_of_ne h hne]
    split_ifs <;> simp [Finset.mem_insert, Finset.mem_erase, hp, mem_freshSlots]

/-- A storage write adds one fresh slot, removes one, or keeps their number.

It adds one when a zero slot, zero before the transaction, gets a word that is not zero.

It removes one when such a slot, not zero now, goes back to zero. -/
theorem card_freshSlots_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    (tx'.freshSlots.card : Int) =
      tx.freshSlots.card +
        (if tx.getStorageOriginal address key = 0 ∧ tx.getStorage address key = 0 ∧ value ≠ 0
          then 1 else 0) -
        (if tx.getStorageOriginal address key = 0 ∧ tx.getStorage address key ≠ 0 ∧ value = 0
          then 1 else 0) := by
  rw [freshSlots_setStorage h]
  have hmem : (address, key) ∈ tx.freshSlots ↔
      tx.getStorageOriginal address key = 0 ∧ tx.getStorage address key ≠ 0 := mem_freshSlots
  by_cases hin : (address, key) ∈ tx.freshSlots
  · -- The slot was fresh: the write keeps it fresh, or clears it.
    obtain ⟨h0, h1⟩ := hmem.mp hin
    have hpos : 1 ≤ tx.freshSlots.card := Finset.card_pos.mpr ⟨_, hin⟩
    split_ifs <;> simp_all [Finset.insert_eq_of_mem, Finset.card_erase_of_mem, Int.ofNat_sub hpos]
  · -- The slot was not fresh: the write makes it fresh, or leaves it out.
    split_ifs <;> simp_all [Finset.card_insert_of_notMem, Finset.erase_eq_of_notMem]

/-- A change of an account adds no fresh slot: it keeps every word, or deletes the account. -/
theorem freshSlots_modifyState {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {f : Account → Except StateError Account} (h : tx.modifyState fork address f = .ok tx') :
    tx'.freshSlots ⊆ tx.freshSlots := by
  rintro ⟨other, key⟩ hmem
  rw [mem_freshSlots] at hmem ⊢
  rw [getStorageOriginal_modifyState h, getStorage_modifyState h] at hmem
  split_ifs at hmem
  · exact absurd rfl hmem.2
  · exact hmem

/-- New code at an address adds no fresh slot. -/
theorem freshSlots_setCode {fork : Fork} {tx tx' : TransactionState} {address : Address}
    {code : ByteArray} (h : tx.setCode fork address code = .ok tx') :
    tx'.freshSlots ⊆ tx.freshSlots := by
  dsimp only [setCode] at h
  split at h
  · exact freshSlots_modifyState h
  · -- A new entry of code is no word of the storage.
    exact fun _ hslot => freshSlots_modifyState h hslot

/-- A record of the read of an account keeps the fresh slots. -/
theorem freshSlots_recordAccountRead (tx : TransactionState) (address : Address) :
    (tx.recordAccountRead address).freshSlots = tx.freshSlots :=
  rfl

end TransactionState

end EthLib.Execution.State

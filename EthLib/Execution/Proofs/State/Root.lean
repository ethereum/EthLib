module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.State.Root
public import EthLib.Execution.Proofs.Trie.Binding

/-!
# Proofs: the state and storage roots

A zero word changes no storage root, because the trie leaves it out.

The empty state has the root of the empty trie.

A client may hold the entries of a trie in any order, such as the order it set them in.

Every such order gives the same root.

Otherwise a search over the keys returns two keys with one hash.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

/-! ## Zero words and the empty state -/

/-- Setting a key to the word zero gives the storage root of removing the key. -/
theorem storageRoot_insert_zero (hash : ByteArray → Hash32)
    (storage : Std.ExtTreeMap Bytes32 U256) (key : Bytes32) :
    storageRoot hash (storage.insert key 0) = storageRoot hash (storage.erase key) := by
  -- The two storages hold the same nonzero words.
  have hfilter : (storage.insert key 0).filter (fun _ value => value != 0) =
      (storage.erase key).filter (fun _ value => value != 0) := by
    apply Std.ExtTreeMap.ext_getElem?
    intro other
    simp only [Std.ExtTreeMap.getElem?_filter, Std.ExtTreeMap.getElem?_insert,
      Std.ExtTreeMap.getElem?_erase]
    split <;> simp [Option.filter_some]
  simp only [storageRoot, storageEntries, hfilter]

/-- The empty storage has the root of the empty trie, the hash of `0x80`. -/
theorem storageRoot_empty (hash : ByteArray → Hash32) :
    storageRoot hash ∅ = .ok (hash ⟨#[0x80]⟩) := by
  simp [storageRoot, storageEntries, bind, Except.bind, Except.mapError, pure,
    Except.pure]
  rfl

/-- A state with no account has the root of the empty trie, whatever storage and code it holds. -/
theorem stateRoot_empty (hash : ByteArray → Hash32)
    (storage : Std.ExtTreeMap Address (Std.ExtTreeMap Bytes32 U256))
    (code : Std.ExtTreeMap Hash32 ByteArray) :
    stateRoot hash ⟨∅, storage, code⟩ = .ok (hash ⟨#[0x80]⟩) := by
  simp [stateRoot, stateEntries, bind, Except.bind, pure, Except.pure]
  rfl

/-! ## Any order of the entries -/

/-- The bytes of a fixed-length byte string determine it. -/
theorem bytes_injective {n : Nat} :
    Function.Injective fun v : Vector UInt8 n => (⟨v.toArray⟩ : ByteArray) := by
  intro a b h
  simp only [ByteArray.mk.injEq] at h
  exact Vector.toArray_inj.mp h

/-- The keys of a map, as bytes, are distinct. -/
theorem nodup_bytes_keys {n : Nat} {β : Type} (map : Std.ExtTreeMap (Vector UInt8 n) β) :
    (map.toList.map fun entry => (⟨entry.1.toArray⟩ : ByteArray)).Nodup := by
  have hkeys := nodup_map_of_injective bytes_injective (map.nodup_keys)
  rwa [← Std.ExtTreeMap.map_fst_toList_eq_keys, List.map_map] at hkeys

/-- The storage entries have distinct keys. -/
theorem storageEntries_nodup {storage : Std.ExtTreeMap Bytes32 U256}
    {entries : List (ByteArray × ByteArray)} (h : storageEntries storage = .ok entries) :
    (entries.map Prod.fst).Nodup := by
  unfold storageEntries at h
  rw [map_of_mapM_ok (q := fun entry => (⟨entry.1.toArray⟩ : ByteArray)) ?_ h]
  · exact nodup_bytes_keys _
  · -- Each entry keeps the bytes of its key.
    intro entry result hentry
    cases hencode : (Codec.encode entry.2 : Except RlpError ByteArray) with
    | error e => simp [hencode, bind, Except.bind] at hentry
    | ok encoded =>
      simp only [hencode, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hentry
      rw [← hentry]

/-- The state entries have distinct keys. -/
theorem stateEntries_nodup {hash : ByteArray → Hash32} {state : State}
    {entries : List (ByteArray × ByteArray)} (h : stateEntries hash state = .ok entries) :
    (entries.map Prod.fst).Nodup := by
  unfold stateEntries at h
  rw [map_of_mapM_ok (q := fun entry => (⟨entry.1.toArray⟩ : ByteArray)) ?_ h]
  · exact nodup_bytes_keys _
  · -- Each entry keeps the bytes of its address.
    intro entry result hentry
    cases hroot : storageRoot hash (state.storage.getD entry.1 ∅) with
    | error e => simp [hroot, bind, Except.bind] at hentry
    | ok storageHash =>
      cases hencode : encodeAccount entry.2 storageHash with
      | error e => simp [hroot, hencode, bind, Except.bind, Except.mapError] at hentry
      | ok encoded =>
        simp only [hroot, hencode, bind, Except.bind, pure, Except.pure, Except.mapError,
          Except.ok.injEq] at hentry
        rw [← hentry]

/-- Order of the storage trie: any order of the storage entries gives the storage root.

Otherwise the search over their keys returns two keys with one hash. -/
theorem storageRoot_perm (hash : ByteArray → Hash32) {storage : Std.ExtTreeMap Bytes32 U256}
    {entries data : List (ByteArray × ByteArray)} (hentries : storageEntries storage = .ok entries)
    (hperm : entries.Perm data) :
    storageRoot hash storage = root hash ⟨true, data⟩ ∨
      ∃ pair, findKeyCollision hash (entries.map Prod.fst) = some pair ∧ IsCollision hash pair := by
  have hroot : storageRoot hash storage = root hash ⟨true, entries⟩ := by
    simp [storageRoot, hentries, Except.mapError, bind, Except.bind]
  rw [hroot]
  exact root_secured_perm hash hperm (storageEntries_nodup hentries)

/-- Order of the state trie: any order of the state entries gives the state root.

Otherwise the search over their keys returns two keys with one hash. -/
theorem stateRoot_perm (hash : ByteArray → Hash32) {state : State}
    {entries data : List (ByteArray × ByteArray)} (hentries : stateEntries hash state = .ok entries)
    (hperm : entries.Perm data) :
    stateRoot hash state = root hash ⟨true, data⟩ ∨
      ∃ pair, findKeyCollision hash (entries.map Prod.fst) = some pair ∧ IsCollision hash pair := by
  have hroot : stateRoot hash state = root hash ⟨true, entries⟩ := by
    simp [stateRoot, hentries, bind, Except.bind]
  rw [hroot]
  exact root_secured_perm hash hperm (stateEntries_nodup hentries)

end EthLib.Execution.State

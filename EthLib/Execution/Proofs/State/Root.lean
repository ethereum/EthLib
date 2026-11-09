module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.State.Root
public import EthLib.Execution.Proofs.Trie.Binding
import EthLib.Execution.Proofs.State.Account
import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the state and storage roots

A zero word changes no storage root, because the trie leaves it out.

The empty state has the root of the empty trie.

A client may hold the entries of a trie in any order, such as the order it set them in.

Every such order gives the same root.

Otherwise a search over the keys returns two keys with one hash.

Two storages with one storage root give every key the same word, with `0` for an unset key.

Two states with one state root give every address the same account.

At every address that has an account, the two states also give every key the same word.

Otherwise a search over the tries returns a collision of the hash.

A 32-byte hash of byte strings has collisions, so no theorem can rule one out.

The theorems give no bound on the cost of finding one.
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

/-! ## Binding of the storage and state roots -/

/-- A collision in two secured tries that have one root and disagree at a key, if any.

First, the search checks the proofs of the key in both tries.

When the two entry lists differ, the search then checks all keys for two with one hash. -/
def findSecuredCollision (hash : ByteArray → Hash32)
    (entries₁ entries₂ : List (ByteArray × ByteArray)) (key : ByteArray) :
    Option (ByteArray × ByteArray) :=
  (findCollision hash ⟨true, entries₁⟩ ⟨true, entries₂⟩ key).or
    (if entries₁ = entries₂ then none
     else findKeyCollision hash (key :: entries₁.map Prod.fst ++ entries₂.map Prod.fst))

/-- Every pair that the secured-trie search returns is a collision. -/
theorem findSecuredCollision_valid (hash : ByteArray → Hash32)
    {entries₁ entries₂ : List (ByteArray × ByteArray)} {key : ByteArray}
    {pair : ByteArray × ByteArray}
    (h : findSecuredCollision hash entries₁ entries₂ key = some pair) :
    IsCollision hash pair := by
  unfold findSecuredCollision at h
  rcases Option.or_eq_some_iff.mp h with hcol | ⟨-, hkey⟩
  · exact findCollision_valid hash hcol
  · split at hkey
    · cases hkey
    · exact findKeyCollision_valid hash _ hkey

/-- A secured trie compared with itself has no collision. -/
theorem findSecuredCollision_self (hash : ByteArray → Hash32)
    (entries : List (ByteArray × ByteArray)) (key : ByteArray) :
    findSecuredCollision hash entries entries key = none := by
  simp [findSecuredCollision, findCollision_self]

/-- A key absent from `findKeyCollision` has no different key in the list with its hash. -/
private theorem hash_ne_of_findKeyCollision_none (hash : ByteArray → Hash32) :
    {keys : List ByteArray} → findKeyCollision hash keys = none →
      ∀ x ∈ keys, ∀ y ∈ keys, x ≠ y → hash x ≠ hash y
  | [], _, _, hmem, _, _, _ => by cases hmem
  | first :: rest, h, x, hx, y, hy, hne => by
    unfold findKeyCollision at h
    split at h
    · cases h
    · rename_i hfind
      have hno : ∀ z ∈ rest, z ≠ first → hash z ≠ hash first := by
        intro z hz hzne hzhash
        exact absurd (List.find?_eq_none.mp hfind z hz) (by simp [hzne, hzhash])
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd rfl hne
        · exact fun heq => hno y hy' hne.symm heq.symm
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exact hno x hx' hne
        · exact hash_ne_of_findKeyCollision_none hash h x hx' y hy' hne

/-- In a secured trie, `valueAt` reads the first entry of `key` if no other key shares its hash. -/
private theorem valueAt_secured_eq (hash : ByteArray → Hash32)
    {entries : List (ByteArray × ByteArray)} {key : ByteArray}
    (hno : ∀ k ∈ entries.map Prod.fst, k ≠ key → hash k ≠ hash key) :
    valueAt hash ⟨true, entries⟩ key =
      (entries.find? fun entry => entry.1 = key).map Prod.snd := by
  unfold valueAt
  congr 1
  apply find?_congr
  intro entry hmem
  simp only [keyPath_eq, ↓reduceIte]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hhash := hashBytes_injective (bytesToNibbleList_injective h)
  exact Decidable.byContradiction fun hne => hno entry.1 (List.mem_map_of_mem hmem) hne hhash

/-- Distinct keys whose hashes never collide have distinct hashes. -/
private theorem nodup_map_of_hash_ne (hash : ByteArray → Hash32) :
    {keys : List ByteArray} → keys.Nodup →
      (∀ x ∈ keys, ∀ y ∈ keys, x ≠ y → hash x ≠ hash y) → (keys.map hash).Nodup
  | [], _, _ => List.nodup_nil
  | key :: rest, hnodup, hdisj => by
    rw [List.nodup_cons] at hnodup
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    refine ⟨fun other hmem heq => ?_, nodup_map_of_hash_ne hash hnodup.2
      (fun x hx y hy => hdisj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    exact hnodup.1 (Decidable.byContradiction (fun hne =>
      hdisj other (List.mem_cons_of_mem _ hmem) key List.mem_cons_self hne heq) ▸ hmem)

/-- Two secured tries with distinct keys and one root agree on `key` when the search finds none. -/
private theorem find_eq_of_findSecuredCollision_none (hash : ByteArray → Hash32)
    {entries₁ entries₂ : List (ByteArray × ByteArray)} {root' : Hash32} {key : ByteArray}
    (hnodup₁ : (entries₁.map Prod.fst).Nodup) (hnodup₂ : (entries₂.map Prod.fst).Nodup)
    (hroot₁ : root hash ⟨true, entries₁⟩ = .ok root')
    (hroot₂ : root hash ⟨true, entries₂⟩ = .ok root')
    (hnone : findSecuredCollision hash entries₁ entries₂ key = none) :
    (entries₁.find? fun entry => entry.1 = key).map Prod.snd =
      (entries₂.find? fun entry => entry.1 = key).map Prod.snd := by
  unfold findSecuredCollision at hnone
  obtain ⟨hcol, hkeys_branch⟩ := Option.or_eq_none_iff.mp hnone
  by_cases hsame : entries₁ = entries₂
  · rw [hsame]
  · simp only [hsame, ↓reduceIte] at hkeys_branch
    have hdisj := hash_ne_of_findKeyCollision_none hash hkeys_branch
    have hpath₁ : findPathCollision hash ⟨true, entries₁⟩ = none := by
      simp only [findPathCollision, ↓reduceIte]
      exact findKeyCollision_of_nodup hash _ (nodup_map_of_hash_ne hash hnodup₁
        fun x hx y hy => hdisj x (by simp [hx]) y (by simp [hy]))
    have hpath₂ : findPathCollision hash ⟨true, entries₂⟩ = none := by
      simp only [findPathCollision, ↓reduceIte]
      exact findKeyCollision_of_nodup hash _ (nodup_map_of_hash_ne hash hnodup₂
        fun x hx y hy => hdisj x (by simp [hx]) y (by simp [hy]))
    rw [← valueAt_secured_eq hash (fun k hk hne => hdisj k (by simp [hk]) key (by simp) hne),
      ← valueAt_secured_eq hash (fun k hk hne => hdisj k (by simp [hk]) key (by simp) hne)]
    rcases root_binding hash (trie₁ := ⟨true, entries₁⟩) (trie₂ := ⟨true, entries₂⟩) rfl
        hroot₁ hroot₂ hnodup₁ hnodup₂ key with hval | ⟨_, hf, -⟩ | ⟨_, hf, -⟩ | ⟨_, hf, -⟩
    · exact hval
    · simp [hcol] at hf
    · simp [hpath₁] at hf
    · simp [hpath₂] at hf

/-- A storage has a root exactly when its entries have that root, as a secured trie. -/
theorem storageRoot_eq_ok_iff {hash : ByteArray → Hash32}
    {storage : Std.ExtTreeMap Bytes32 U256} {root' : Hash32} :
    storageRoot hash storage = .ok root' ↔
      ∃ entries, storageEntries storage = .ok entries ∧ root hash ⟨true, entries⟩ = .ok root' := by
  unfold storageRoot
  cases storageEntries storage <;> simp [Except.mapError, bind, Except.bind]

/-- The entry of a key in `storageEntries` holds the encoding of its nonzero word.

No entry holds a zero or unset key. -/
private theorem find_storageEntries {storage : Std.ExtTreeMap Bytes32 U256}
    {entries : List (ByteArray × ByteArray)} (h : storageEntries storage = .ok entries)
    (key : Bytes32) :
    match (entries.find? fun entry => entry.1 = ⟨key.toArray⟩).map Prod.snd with
    | some bytes =>
      ∃ word, storage.getD key 0 = word ∧ word ≠ 0 ∧ Codec.encode word = .ok bytes
    | none => storage.getD key 0 = 0 := by
  unfold storageEntries at h
  cases hfind : entries.find? fun entry => entry.1 = ⟨key.toArray⟩ with
  | some entry =>
    simp only [Option.map_some]
    obtain ⟨⟨k, word⟩, hmem, hstep⟩ := mapM_ok_mem h entry (List.mem_of_find?_eq_some hfind)
    have hkey_eq : entry.1 = ⟨key.toArray⟩ := by
      simpa using List.find?_some hfind
    cases henc : (Codec.encode word : Except RlpError ByteArray) with
    | error e => simp [henc, bind, Except.bind] at hstep
    | ok bytes =>
      simp only [henc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep
      have hk : k = key := bytes_injective hkey_eq
      subst hk
      have hget := Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
      simp only [Std.ExtTreeMap.getElem?_filter] at hget
      cases hsk : storage[k]? with
      | none => simp [hsk] at hget
      | some w =>
        rw [hsk] at hget
        dsimp only [Option.pfilter] at hget
        cases hne : (w != (0 : U256)) with
        | false =>
          rw [hne] at hget
          cases hget
        | true =>
          rw [hne] at hget
          cases hget
          exact ⟨word, by simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hsk], bne_iff_ne.mp hne,
            henc⟩
  | none =>
    simp only [Option.map_none]
    by_cases hzero : storage.getD key (0 : U256) = (0 : U256)
    · exact hzero
    · rw [Std.ExtTreeMap.getD_eq_getD_getElem?] at hzero
      cases hsk : storage[key]? with
      | none => simp [hsk] at hzero
      | some word =>
        simp only [hsk, Option.getD_some] at hzero
        have hmem_filter : (key, word) ∈ (storage.filter fun _ value => value != 0).toList := by
          rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, Std.ExtTreeMap.getElem?_filter, hsk]
          dsimp only [Option.pfilter]
          rw [bne_iff_ne.mpr hzero]
          rfl
        obtain ⟨entry, hentry_mem, hstep⟩ := exists_mem_of_mapM_ok h hmem_filter
        cases henc : (Codec.encode word : Except RlpError ByteArray) with
        | error e => simp [henc, bind, Except.bind] at hstep
        | ok bytes =>
          simp only [henc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hstep
          subst hstep
          exact absurd (List.find?_eq_none.mp hfind _ hentry_mem) (by simp)

/-- Two storage entry lists with the same value at a key give that key the same word. -/
private theorem storage_getD_eq_of_find_eq {storage₁ storage₂ : Std.ExtTreeMap Bytes32 U256}
    {entries₁ entries₂ : List (ByteArray × ByteArray)} {key : Bytes32}
    (h₁ : storageEntries storage₁ = .ok entries₁) (h₂ : storageEntries storage₂ = .ok entries₂)
    (heq : (entries₁.find? fun entry => entry.1 = ⟨key.toArray⟩).map Prod.snd =
      (entries₂.find? fun entry => entry.1 = ⟨key.toArray⟩).map Prod.snd) :
    storage₁.getD key 0 = storage₂.getD key 0 := by
  have hf₁ := find_storageEntries h₁ key
  have hf₂ := find_storageEntries h₂ key
  rw [heq] at hf₁
  cases hres : (entries₂.find? fun entry => entry.1 = ⟨key.toArray⟩).map Prod.snd with
  | none =>
    rw [hres] at hf₁ hf₂
    exact hf₁.trans hf₂.symm
  | some bytes =>
    rw [hres] at hf₁ hf₂
    obtain ⟨w₁, hw₁, -, henc₁⟩ := hf₁
    obtain ⟨w₂, hw₂, -, henc₂⟩ := hf₂
    rw [hw₁, hw₂, Codec.encode_injective henc₁ henc₂]

/-- The collision of `hash` from the first key where two storages disagree on a word, if any. -/
def findStorageCollision (hash : ByteArray → Hash32)
    (storage₁ storage₂ : Std.ExtTreeMap Bytes32 U256) : Option (ByteArray × ByteArray) :=
  match storageEntries storage₁, storageEntries storage₂ with
  | .ok entries₁, .ok entries₂ =>
    (storage₁.keys ++ storage₂.keys).findSome? fun key =>
      if storage₁.getD key 0 ≠ storage₂.getD key 0 then
        findSecuredCollision hash entries₁ entries₂ ⟨key.toArray⟩
      else none
  | _, _ => none

/-- Every pair that the storage search returns is a collision. -/
theorem findStorageCollision_valid (hash : ByteArray → Hash32)
    {storage₁ storage₂ : Std.ExtTreeMap Bytes32 U256} {pair : ByteArray × ByteArray}
    (h : findStorageCollision hash storage₁ storage₂ = some pair) :
    IsCollision hash pair := by
  unfold findStorageCollision at h
  split at h
  · obtain ⟨-, key, -, -, hfound, -⟩ := List.findSome?_eq_some_iff.mp h
    split at hfound
    · exact findSecuredCollision_valid hash hfound
    · cases hfound
  · cases h

/-- A storage compared with itself has no collision. -/
theorem findStorageCollision_self (hash : ByteArray → Hash32)
    (storage : Std.ExtTreeMap Bytes32 U256) :
    findStorageCollision hash storage storage = none := by
  unfold findStorageCollision
  split
  · exact List.findSome?_eq_none_iff.mpr fun _ _ => by simp
  · rfl

/-- Binding of the storage root: two storages with one root give every key the same word.

An unset key has the word `0`.

Otherwise `findStorageCollision` returns a collision of `hash`. -/
theorem storageRoot_binding (hash : ByteArray → Hash32)
    {storage₁ storage₂ : Std.ExtTreeMap Bytes32 U256} {root' : Hash32}
    (hroot₁ : storageRoot hash storage₁ = .ok root')
    (hroot₂ : storageRoot hash storage₂ = .ok root') :
    (∀ key : Bytes32, storage₁.getD key 0 = storage₂.getD key 0) ∨
      ∃ pair, findStorageCollision hash storage₁ storage₂ = some pair ∧ IsCollision hash pair := by
  cases hsearch : findStorageCollision hash storage₁ storage₂ with
  | some pair => exact .inr ⟨pair, rfl, findStorageCollision_valid hash hsearch⟩
  | none =>
  obtain ⟨entries₁, hentries₁, htrie₁⟩ := storageRoot_eq_ok_iff.mp hroot₁
  obtain ⟨entries₂, hentries₂, htrie₂⟩ := storageRoot_eq_ok_iff.mp hroot₂
  refine .inl fun key => ?_
  by_cases hdiff : storage₁.getD key 0 = storage₂.getD key 0
  · exact hdiff
  · have hmem : key ∈ storage₁.keys ++ storage₂.keys := by
      rw [List.mem_append, Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_keys]
      exact Decidable.byContradiction fun hneither => hdiff (by
        simp [Std.ExtTreeMap.getD_eq_getD_getElem?,
          Std.ExtTreeMap.getElem?_eq_none (fun h => hneither (.inl h)),
          Std.ExtTreeMap.getElem?_eq_none (fun h => hneither (.inr h))])
    unfold findStorageCollision at hsearch
    rw [hentries₁, hentries₂] at hsearch
    have hnone := List.findSome?_eq_none_iff.mp hsearch key hmem
    rw [ite_eq_left hdiff] at hnone
    exact storage_getD_eq_of_find_eq hentries₁ hentries₂
      (find_eq_of_findSecuredCollision_none hash (storageEntries_nodup hentries₁)
        (storageEntries_nodup hentries₂) htrie₁ htrie₂ hnone)

/-- A state has a root exactly when its entries have that root, as a secured trie. -/
theorem stateRoot_eq_ok_iff {hash : ByteArray → Hash32} {state : State} {root' : Hash32} :
    stateRoot hash state = .ok root' ↔
      ∃ entries, stateEntries hash state = .ok entries ∧ root hash ⟨true, entries⟩ = .ok root' := by
  unfold stateRoot
  cases stateEntries hash state <;> simp [bind, Except.bind]

/-- The entry of an address in `stateEntries` holds the encoding of its account and storage root.

No entry holds an address without an account. -/
private theorem find_stateEntries {hash : ByteArray → Hash32} {state : State}
    {entries : List (ByteArray × ByteArray)} (h : stateEntries hash state = .ok entries)
    (address : Address) :
    match (entries.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd with
    | some bytes =>
      ∃ account storageHash, state.accounts[address]? = some account ∧
        storageRoot hash (state.storage.getD address ∅) = .ok storageHash ∧
        encodeAccount account storageHash = .ok bytes
    | none => state.accounts[address]? = none := by
  unfold stateEntries at h
  cases hfind : entries.find? fun entry => entry.1 = ⟨address.toArray⟩ with
  | some entry =>
    simp only [Option.map_some]
    obtain ⟨⟨addr, account⟩, hmem, hstep⟩ := mapM_ok_mem h entry (List.mem_of_find?_eq_some hfind)
    have hkey_eq : entry.1 = ⟨address.toArray⟩ := by simpa using List.find?_some hfind
    cases hsroot : storageRoot hash (state.storage.getD addr ∅) with
    | error e => simp [hsroot, bind, Except.bind] at hstep
    | ok storageHash =>
      cases henc : encodeAccount account storageHash with
      | error e => simp [hsroot, henc, bind, Except.bind, Except.mapError] at hstep
      | ok bytes =>
        simp only [hsroot, henc, bind, Except.bind, pure, Except.pure, Except.mapError,
          Except.ok.injEq] at hstep
        subst hstep
        cases bytes_injective hkey_eq
        exact ⟨account, storageHash, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem,
          hsroot, henc⟩
  | none =>
    simp only [Option.map_none]
    cases hacc : state.accounts[address]? with
    | none => rfl
    | some account =>
      obtain ⟨entry, hentry_mem, hstep⟩ := exists_mem_of_mapM_ok h
        (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hacc)
      cases hsroot : storageRoot hash (state.storage.getD address ∅) with
      | error e => simp [hsroot, bind, Except.bind] at hstep
      | ok storageHash =>
        cases henc : encodeAccount account storageHash with
        | error e => simp [hsroot, henc, bind, Except.bind, Except.mapError] at hstep
        | ok bytes =>
          simp only [hsroot, henc, bind, Except.bind, pure, Except.pure, Except.mapError,
            Except.ok.injEq] at hstep
          subst hstep
          exact absurd (List.find?_eq_none.mp hfind _ hentry_mem) (by simp)

/-- Two state entry lists with the same value at an address give the address the same account.

When the address has an account, the two lists also give it one storage root. -/
private theorem account_and_storageRoot_of_find_eq {hash : ByteArray → Hash32}
    {state₁ state₂ : State} {entries₁ entries₂ : List (ByteArray × ByteArray)} {address : Address}
    (h₁ : stateEntries hash state₁ = .ok entries₁) (h₂ : stateEntries hash state₂ = .ok entries₂)
    (heq : (entries₁.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd =
      (entries₂.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd) :
    state₁.accounts[address]? = state₂.accounts[address]? ∧
      (address ∈ state₁.accounts → ∃ storageHash,
        storageRoot hash (state₁.storage.getD address ∅) = .ok storageHash ∧
        storageRoot hash (state₂.storage.getD address ∅) = .ok storageHash) := by
  have hf₁ := find_stateEntries h₁ address
  have hf₂ := find_stateEntries h₂ address
  rw [heq] at hf₁
  cases hres : (entries₂.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd with
  | none =>
    rw [hres] at hf₁ hf₂
    refine ⟨hf₁.trans hf₂.symm, fun hmem => ?_⟩
    obtain ⟨acc, hget⟩ := Option.isSome_iff_exists.mp
      (Std.ExtTreeMap.isSome_getElem?_iff_mem.mpr hmem)
    rw [hf₁] at hget
    cases hget
  | some bytes =>
    rw [hres] at hf₁ hf₂
    obtain ⟨acc₁, sr₁, hacc₁, hsr₁, henc₁⟩ := hf₁
    obtain ⟨acc₂, sr₂, hacc₂, hsr₂, henc₂⟩ := hf₂
    have hdec := (decodeAccount_encodeAccount henc₁).symm.trans (decodeAccount_encodeAccount henc₂)
    simp only [Except.ok.injEq, Prod.mk.injEq] at hdec
    obtain ⟨rfl, rfl⟩ := hdec
    exact ⟨hacc₁.trans hacc₂.symm, fun _ => ⟨sr₁, hsr₁, hsr₂⟩⟩

/-- The collision from the first address where two states differ on an account or its storage. -/
def findStateCollision (hash : ByteArray → Hash32) (state₁ state₂ : State) :
    Option (ByteArray × ByteArray) :=
  match stateEntries hash state₁, stateEntries hash state₂ with
  | .ok entries₁, .ok entries₂ =>
    (state₁.accounts.keys ++ state₂.accounts.keys).findSome? fun address =>
      if state₁.accounts[address]? ≠ state₂.accounts[address]? then
        findSecuredCollision hash entries₁ entries₂ ⟨address.toArray⟩
      else if address ∈ state₁.accounts then
        match storageRoot hash (state₁.storage.getD address ∅),
            storageRoot hash (state₂.storage.getD address ∅) with
        | .ok root₁, .ok root₂ =>
          if root₁ ≠ root₂ then
            findSecuredCollision hash entries₁ entries₂ ⟨address.toArray⟩
          else
            findStorageCollision hash (state₁.storage.getD address ∅)
              (state₂.storage.getD address ∅)
        | _, _ => none
      else none
  | _, _ => none

/-- Every pair that the state search returns is a collision. -/
theorem findStateCollision_valid (hash : ByteArray → Hash32) {state₁ state₂ : State}
    {pair : ByteArray × ByteArray} (h : findStateCollision hash state₁ state₂ = some pair) :
    IsCollision hash pair := by
  unfold findStateCollision at h
  split at h
  · obtain ⟨-, address, -, -, hfound, -⟩ := List.findSome?_eq_some_iff.mp h
    split at hfound
    · exact findSecuredCollision_valid hash hfound
    · split at hfound
      · split at hfound
        · split at hfound
          · exact findSecuredCollision_valid hash hfound
          · exact findStorageCollision_valid hash hfound
        · cases hfound
      · cases hfound
  · cases h

/-- A state compared with itself has no collision. -/
theorem findStateCollision_self (hash : ByteArray → Hash32) (state : State) :
    findStateCollision hash state state = none := by
  unfold findStateCollision
  split
  · refine List.findSome?_eq_none_iff.mpr fun address _ => ?_
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    split
    · split
      · rename_i root₁ root₂ hsr₁ hsr₂
        rw [hsr₁] at hsr₂
        cases hsr₂
        simp [findStorageCollision_self]
      · rfl
    · rfl
  · rfl

/-- Binding of the state root: two states with one state root give every address the same account.

At every address that has an account, the two states also give every key the same word.

An unset key has the word `0`.

Otherwise `findStateCollision` returns a collision of `hash`. -/
theorem stateRoot_binding (hash : ByteArray → Hash32) {state₁ state₂ : State} {root' : Hash32}
    (hroot₁ : stateRoot hash state₁ = .ok root')
    (hroot₂ : stateRoot hash state₂ = .ok root') :
    (∀ address : Address,
        state₁.accounts[address]? = state₂.accounts[address]? ∧
        (address ∈ state₁.accounts → ∀ key : Bytes32,
          (state₁.storage.getD address ∅).getD key 0 =
            (state₂.storage.getD address ∅).getD key 0)) ∨
      ∃ pair, findStateCollision hash state₁ state₂ = some pair ∧ IsCollision hash pair := by
  cases hsearch : findStateCollision hash state₁ state₂ with
  | some pair => exact .inr ⟨pair, rfl, findStateCollision_valid hash hsearch⟩
  | none =>
  obtain ⟨entries₁, hentries₁, htrie₁⟩ := stateRoot_eq_ok_iff.mp hroot₁
  obtain ⟨entries₂, hentries₂, htrie₂⟩ := stateRoot_eq_ok_iff.mp hroot₂
  refine .inl fun address => ?_
  by_cases hmem_keys : address ∈ state₁.accounts.keys ++ state₂.accounts.keys
  · unfold findStateCollision at hsearch
    rw [hentries₁, hentries₂] at hsearch
    have hnone := List.findSome?_eq_none_iff.mp hsearch address hmem_keys
    by_cases hacc : state₁.accounts[address]? = state₂.accounts[address]?
    · refine ⟨hacc, fun hmem => ?_⟩
      simp only [ne_eq, hacc, not_true_eq_false, ↓reduceIte, hmem] at hnone
      obtain ⟨acc, hget₁⟩ := Option.isSome_iff_exists.mp
        (Std.ExtTreeMap.isSome_getElem?_iff_mem.mpr hmem)
      obtain ⟨_, _, hstep₁⟩ := exists_mem_of_mapM_ok hentries₁
        (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hget₁)
      obtain ⟨_, _, hstep₂⟩ := exists_mem_of_mapM_ok hentries₂
        (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr (hacc.symm.trans hget₁))
      cases hsr₁ : storageRoot hash (state₁.storage.getD address ∅) with
      | error e => simp [hsr₁, bind, Except.bind] at hstep₁
      | ok sr₁ =>
        cases hsr₂ : storageRoot hash (state₂.storage.getD address ∅) with
        | error e => simp [hsr₂, bind, Except.bind] at hstep₂
        | ok sr₂ =>
          rw [hsr₁, hsr₂] at hnone
          by_cases hsr_eq : sr₁ = sr₂
          · subst hsr_eq
            simp only [not_true_eq_false, ↓reduceIte] at hnone
            rcases storageRoot_binding hash hsr₁ hsr₂ with hwords | ⟨pair, hf, -⟩
            · exact hwords
            · simp [hnone] at hf
          · simp only [hsr_eq, not_false_eq_true, ↓reduceIte] at hnone
            have ⟨_, hsr⟩ := account_and_storageRoot_of_find_eq hentries₁ hentries₂
              (find_eq_of_findSecuredCollision_none hash (stateEntries_nodup hentries₁)
                (stateEntries_nodup hentries₂) htrie₁ htrie₂ hnone)
            obtain ⟨sr, h₁, h₂⟩ := hsr hmem
            rw [hsr₁] at h₁
            rw [hsr₂] at h₂
            cases h₁
            exact absurd (Except.ok.inj h₂).symm hsr_eq
    · simp only [ne_eq, hacc, not_false_eq_true, ↓reduceIte] at hnone
      have ⟨hacc', _⟩ := account_and_storageRoot_of_find_eq hentries₁ hentries₂
        (find_eq_of_findSecuredCollision_none hash (stateEntries_nodup hentries₁)
          (stateEntries_nodup hentries₂) htrie₁ htrie₂ hnone)
      exact absurd hacc' hacc
  · rw [List.mem_append, Std.ExtTreeMap.mem_keys, Std.ExtTreeMap.mem_keys] at hmem_keys
    have hn₁ : address ∉ state₁.accounts := fun h => hmem_keys (.inl h)
    have hn₂ : address ∉ state₂.accounts := fun h => hmem_keys (.inr h)
    rw [Std.ExtTreeMap.getElem?_eq_none hn₁, Std.ExtTreeMap.getElem?_eq_none hn₂]
    exact ⟨rfl, fun h => absurd h hn₁⟩

end EthLib.Execution.State

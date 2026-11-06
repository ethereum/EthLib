module

public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Proofs.Blocks.Receipt
public import EthLib.Execution.Proofs.Blocks.Withdrawal
public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Execution.Proofs.Trie.Root
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the roots of a block body

An empty list has the root of the empty trie, the Keccak-256 hash of `0x80`.

So a block with no transactions, receipts or withdrawals has that root for each list.

The key of each item is the RLP encoding of its index, so the keys of a list's trie are distinct.

Two lists with one root then give every key one value, or the search finds a Keccak-256 collision.

So two lists with one root are equal, or a search over their indices finds such a collision.

The same holds for transactions, withdrawals, and receipts whose types the fork has.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Transactions
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The root of the empty list is the root of the empty trie. -/
theorem indexedRoot_nil : indexedRoot [] = .ok (keccak256 ⟨#[0x80]⟩) :=
  root_empty keccak256 false

/-- A block with no transaction has the root of the empty trie. -/
theorem transactionsRoot_nil : transactionsRoot [] = .ok (keccak256 ⟨#[0x80]⟩) :=
  indexedRoot_nil

/-- A block with no receipt has the root of the empty trie. -/
theorem receiptsRoot_nil {fork : Fork} :
    receiptsRoot (fork := fork) [] = .ok (keccak256 ⟨#[0x80]⟩) :=
  indexedRoot_nil

/-- A block with no withdrawal has the root of the empty trie. -/
theorem withdrawalsRoot_nil : withdrawalsRoot [] = .ok (keccak256 ⟨#[0x80]⟩) :=
  indexedRoot_nil

/-! ## The keys of a list -/

/-- The entries of a list are as many as its items. -/
theorem length_of_indexedEntries {values : List ByteArray}
    {entries : List (ByteArray × ByteArray)} (h : indexedEntries values = .ok entries) :
    entries.length = values.length := by
  rw [mapM_ok_length h, List.length_zip, List.length_range, Nat.min_self]

/-- The entry at an index holds the encoding of the index, and the item at the index. -/
theorem getElem_of_indexedEntries {values : List ByteArray}
    {entries : List (ByteArray × ByteArray)} (h : indexedEntries values = .ok entries)
    (i : Fin entries.length) :
    Codec.encode i.val = .ok entries[i].1 ∧
      entries[i].2 = values[i.val]'(length_of_indexedEntries h ▸ i.isLt) := by
  have hi : i.val < ((List.range values.length).zip values).length := by
    rw [List.length_zip, List.length_range, Nat.min_self, ← length_of_indexedEntries h]
    exact i.isLt
  have hentry := mapM_ok_getElem h i.val hi
  simp only [List.getElem_zip, List.getElem_range] at hentry
  -- The entry is the pair of the index's encoding and the item, once the encoding succeeds.
  cases hkey : Codec.encode i.val with
  | error e => simp [hkey, bind, Except.bind] at hentry
  | ok key =>
    simp only [hkey, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hentry
    simp [← hentry]

/-- The keys of a list's entries are distinct.

Two indices with one encoding are one index, because the decoder reads each index back. -/
theorem indexedEntries_nodup {values : List ByteArray}
    {entries : List (ByteArray × ByteArray)} (h : indexedEntries values = .ok entries) :
    (entries.map Prod.fst).Nodup := by
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij heq => Nat.ne_of_lt hij ?_
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at heq
  have hi' := (getElem_of_indexedEntries h ⟨i, hi⟩).1
  have hj' := (getElem_of_indexedEntries h ⟨j, hj⟩).1
  simp only [Fin.getElem_fin] at hi' hj'
  rw [heq] at hi'
  -- Both indices decode from the one key.
  exact Codec.encode_injective hi' hj'

/-- A list has a root exactly when its entries have that root, as a plain trie. -/
theorem indexedRoot_eq_ok_iff {values : List ByteArray} {root' : Hash32} :
    indexedRoot values = .ok root' ↔
      ∃ entries, indexedEntries values = .ok entries ∧
        root keccak256 ⟨false, entries⟩ = .ok root' := by
  unfold indexedRoot
  cases hentries : indexedEntries values <;>
    simp [Except.mapError, bind, Except.bind]

/-- Binding of a list's root: two lists with one root give every key one value.

Otherwise the search finds a Keccak-256 collision in the proofs of that key. -/
theorem indexedRoot_binding_key {values₁ values₂ : List ByteArray}
    {entries₁ entries₂ : List (ByteArray × ByteArray)} {root' : Hash32}
    (hentries₁ : indexedEntries values₁ = .ok entries₁)
    (hentries₂ : indexedEntries values₂ = .ok entries₂)
    (hroot₁ : root keccak256 ⟨false, entries₁⟩ = .ok root')
    (hroot₂ : root keccak256 ⟨false, entries₂⟩ = .ok root') (key : ByteArray) :
    valueAt keccak256 ⟨false, entries₁⟩ key = valueAt keccak256 ⟨false, entries₂⟩ key ∨
      ∃ pair,
        findCollision keccak256 ⟨false, entries₁⟩ ⟨false, entries₂⟩ key = some pair ∧
          IsCollision keccak256 pair := by
  have hkeys₁ := indexedEntries_nodup hentries₁
  have hkeys₂ := indexedEntries_nodup hentries₂
  rcases root_binding keccak256 (trie₁ := ⟨false, entries₁⟩) (trie₂ := ⟨false, entries₂⟩) rfl
      hroot₁ hroot₂ hkeys₁ hkeys₂ key with hvalue | hfound | ⟨_, hpath, _⟩ | ⟨_, hpath, _⟩
  · exact .inl hvalue
  · exact .inr hfound
  -- A plain trie has no two keys with one path, so the path searches return nothing.
  · simp [findPathCollision] at hpath
  · simp [findPathCollision] at hpath

/-! ## Two lists with one root -/

/-- The value of an index's key in a list's trie is the item at that index.

Past the end of the list, the key has no value. -/
theorem valueAt_of_indexedEntries {values : List ByteArray}
    {entries : List (ByteArray × ByteArray)} (h : indexedEntries values = .ok entries)
    {i : Nat} {key : ByteArray} (hkey : Codec.encode i = .ok key) :
    valueAt keccak256 ⟨false, entries⟩ key = values[i]? := by
  rw [valueAt_plain keccak256 entries key]
  -- Each entry with the key is the entry at the index, since its own index has the same key.
  have hunique : ∀ entry ∈ entries, entry.1 = key →
      ∃ hi : i < entries.length, entry = entries[i] := by
    intro entry hmem heq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
    have hj' := (getElem_of_indexedEntries h ⟨j, hj⟩).1
    simp only [Fin.getElem_fin] at hj'
    rw [heq] at hj'
    cases Codec.encode_injective hj' hkey
    exact ⟨hj, rfl⟩
  by_cases hi : i < entries.length
  · have hentry := getElem_of_indexedEntries h ⟨i, hi⟩
    simp only [Fin.getElem_fin] at hentry
    have hkey' : entries[i].1 = key := (Except.ok.inj (hkey.symm.trans hentry.1)).symm
    -- The search finds an entry with the key, and that entry is the one at the index.
    cases hfind : entries.find? (fun entry => sameBytes entry.1 key) with
    | none =>
      have := List.find?_eq_none.mp hfind entries[i] (List.getElem_mem hi)
      simp [(sameBytes_iff _ _).mpr hkey'] at this
    | some entry =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hsame := (sameBytes_iff _ _).mp (List.find?_some
        (p := fun entry : ByteArray × ByteArray => sameBytes entry.1 key) hfind)
      obtain ⟨_, rfl⟩ := hunique entry hmem hsame
      rw [List.getElem?_eq_getElem (length_of_indexedEntries h ▸ hi)]
      simp [hentry.2]
  · -- No entry has the key, and the list ends before the index.
    rw [List.getElem?_eq_none (by rw [← length_of_indexedEntries h]; omega)]
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro entry hmem hsame
      exact hi (hunique entry hmem ((sameBytes_iff _ _).mp hsame)).1

/-- The collision in the proofs of the first index, below the longer length, of two lists. -/
def findIndexedCollision (values₁ values₂ : List ByteArray) : Option (ByteArray × ByteArray) :=
  match indexedEntries values₁, indexedEntries values₂ with
  | .ok entries₁, .ok entries₂ =>
    (List.range (max values₁.length values₂.length)).findSome? fun i =>
      match Codec.encode i with
      | .ok key => findCollision keccak256 ⟨false, entries₁⟩ ⟨false, entries₂⟩ key
      | .error _ => none
  | _, _ => none

/-- Every pair that the search returns is a collision. -/
theorem findIndexedCollision_valid {values₁ values₂ : List ByteArray}
    {pair : ByteArray × ByteArray} (h : findIndexedCollision values₁ values₂ = some pair) :
    IsCollision keccak256 pair := by
  unfold findIndexedCollision at h
  split at h
  · obtain ⟨-, i, -, -, hfound, -⟩ := List.findSome?_eq_some_iff.mp h
    split at hfound
    · exact findCollision_valid keccak256 hfound
    · cases hfound
  · cases h

/-- A list compared with itself has no collision. -/
theorem findIndexedCollision_self (values : List ByteArray) :
    findIndexedCollision values values = none := by
  unfold findIndexedCollision
  split
  · rename_i entries₁ entries₂ h₁ h₂
    rw [h₁] at h₂
    cases h₂
    refine List.findSome?_eq_none_iff.mpr fun i _ => ?_
    split
    · exact findCollision_self keccak256 _ _
    · rfl
  · rfl

/-- Binding of a list's root: two lists with one root are equal.

Otherwise the search over their indices finds a Keccak-256 collision in the proofs of one index. -/
theorem indexedRoot_binding {values₁ values₂ : List ByteArray} {root' : Hash32}
    (hroot₁ : indexedRoot values₁ = .ok root') (hroot₂ : indexedRoot values₂ = .ok root') :
    values₁ = values₂ ∨
      ∃ pair, findIndexedCollision values₁ values₂ = some pair ∧ IsCollision keccak256 pair := by
  cases hsearch : findIndexedCollision values₁ values₂ with
  | some pair => exact .inr ⟨pair, rfl, findIndexedCollision_valid hsearch⟩
  | none =>
  refine .inl (List.ext_getElem? fun i => ?_)
  obtain ⟨entries₁, hentries₁, htrie₁⟩ := indexedRoot_eq_ok_iff.mp hroot₁
  obtain ⟨entries₂, hentries₂, htrie₂⟩ := indexedRoot_eq_ok_iff.mp hroot₂
  by_cases hi : i < max values₁.length values₂.length
  · -- The index has a key, since one of the lists encodes it.
    obtain ⟨key, hkey⟩ : ∃ key, Codec.encode i = .ok key := by
      by_cases hi₁ : i < values₁.length
      · exact ⟨_, (getElem_of_indexedEntries hentries₁
          ⟨i, (length_of_indexedEntries hentries₁).symm ▸ hi₁⟩).1⟩
      · exact ⟨_, (getElem_of_indexedEntries hentries₂
          ⟨i, (length_of_indexedEntries hentries₂).symm ▸ (by omega)⟩).1⟩
    rw [← valueAt_of_indexedEntries hentries₁ hkey, ← valueAt_of_indexedEntries hentries₂ hkey]
    rcases indexedRoot_binding_key hentries₁ hentries₂ htrie₁ htrie₂ key with hvalue |
      ⟨pair, hfound, -⟩
    · exact hvalue
    · -- The search over the indices reaches this one and returns its collision.
      unfold findIndexedCollision at hsearch
      rw [hentries₁, hentries₂] at hsearch
      have := List.findSome?_eq_none_iff.mp hsearch i (List.mem_range.mpr hi)
      simp [hkey, hfound] at this
  · -- Both lists end before the index.
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ## The roots of typed lists -/

/-- Two lists that map to one output are equal, when two inputs with one output are equal. -/
theorem eq_of_mapM_eq_ok {α β : Type} {f : α → Except RlpError β} {xs ys : List α} {zs : List β}
    (hinjective : ∀ x ∈ xs, ∀ y ∈ ys, ∀ z, f x = .ok z → f y = .ok z → x = y)
    (hx : xs.mapM f = .ok zs) (hy : ys.mapM f = .ok zs) : xs = ys := by
  induction xs generalizing ys zs with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hx
    subst hx
    cases ys with
    | nil => rfl
    | cons y ys =>
      obtain ⟨_, _, _, _, h⟩ := mapM_cons_ok.mp hy
      cases h
  | cons x xs ih =>
    obtain ⟨z, rest, hz, hrest, rfl⟩ := mapM_cons_ok.mp hx
    cases ys with
    | nil => cases hy
    | cons y ys =>
      obtain ⟨z', rest', hz', hrest', h⟩ := mapM_cons_ok.mp hy
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      -- The heads have one output, and the tails map to one list.
      rw [hinjective x (by simp) y (by simp) z hz hz',
        ih (fun x hx y hy => hinjective x (by simp [hx]) y (by simp [hy])) hrest hrest']

/-- A typed list has a root when its items have bytes, and the list of those bytes has the root. -/
theorem indexedRoot_of_mapM {γ : Type} {encodeItem : γ → Except RlpError ByteArray}
    {items : List γ} {root' : Hash32}
    (h : (do indexedRoot (← (items.mapM encodeItem).mapError TrieError.rlp)) = .ok root') :
    ∃ values, items.mapM encodeItem = .ok values ∧ indexedRoot values = .ok root' := by
  cases hvalues : items.mapM encodeItem with
  | error e => simp [hvalues, Except.mapError, bind, Except.bind] at h
  | ok values =>
    simp only [hvalues, Except.mapError, bind, Except.bind] at h
    exact ⟨values, rfl, h⟩

/-- Binding of the transactions root: two lists of transactions with one root are equal.

Otherwise the search over their bytes finds a Keccak-256 collision in the proofs of one index. -/
theorem transactionsRoot_binding {transactions₁ transactions₂ : List Transaction}
    {root' : Hash32} (hroot₁ : transactionsRoot transactions₁ = .ok root')
    (hroot₂ : transactionsRoot transactions₂ = .ok root') :
    transactions₁ = transactions₂ ∨
      ∃ values₁ values₂ pair, transactions₁.mapM encodeTransaction = .ok values₁ ∧
        transactions₂.mapM encodeTransaction = .ok values₂ ∧
        findIndexedCollision values₁ values₂ = some pair ∧ IsCollision keccak256 pair := by
  obtain ⟨values₁, hvalues₁, hindexed₁⟩ := indexedRoot_of_mapM hroot₁
  obtain ⟨values₂, hvalues₂, hindexed₂⟩ := indexedRoot_of_mapM hroot₂
  rcases indexedRoot_binding hindexed₁ hindexed₂ with rfl | ⟨pair, hfound, hvalid⟩
  · -- Two transactions with the same bytes are equal.
    exact .inl (eq_of_mapM_eq_ok (fun _ _ _ _ _ hx hy => encodeTransaction_injective hx hy)
      hvalues₁ hvalues₂)
  · exact .inr ⟨values₁, values₂, pair, hvalues₁, hvalues₂, hfound, hvalid⟩

/-- Binding of the withdrawals root: two lists of withdrawals with one root are equal.

Otherwise the search over their bytes finds a Keccak-256 collision in the proofs of one index. -/
theorem withdrawalsRoot_binding {withdrawals₁ withdrawals₂ : List Withdrawal} {root' : Hash32}
    (hroot₁ : withdrawalsRoot withdrawals₁ = .ok root')
    (hroot₂ : withdrawalsRoot withdrawals₂ = .ok root') :
    withdrawals₁ = withdrawals₂ ∨
      ∃ values₁ values₂ pair, withdrawals₁.mapM Codec.encode = .ok values₁ ∧
        withdrawals₂.mapM Codec.encode = .ok values₂ ∧
        findIndexedCollision values₁ values₂ = some pair ∧ IsCollision keccak256 pair := by
  obtain ⟨values₁, hvalues₁, hindexed₁⟩ := indexedRoot_of_mapM hroot₁
  obtain ⟨values₂, hvalues₂, hindexed₂⟩ := indexedRoot_of_mapM hroot₂
  rcases indexedRoot_binding hindexed₁ hindexed₂ with rfl | ⟨pair, hfound, hvalid⟩
  · -- Two withdrawals with the same bytes are equal.
    exact .inl (eq_of_mapM_eq_ok (fun _ _ _ _ _ hx hy => Codec.encode_injective hx hy)
      hvalues₁ hvalues₂)
  · exact .inr ⟨values₁, values₂, pair, hvalues₁, hvalues₂, hfound, hvalid⟩

/-- Binding of the receipts root: two lists of receipts with one root are equal.

Each type must be 0, or a type that the fork has, as the decoder of a receipt requires.

Otherwise the search over their bytes finds a Keccak-256 collision in the proofs of one index. -/
theorem receiptsRoot_binding {fork : Fork} {receipts₁ receipts₂ : List (UInt8 × Receipt fork)}
    {root' : Hash32}
    (htypes₁ : ∀ entry ∈ receipts₁,
      entry.1 = 0 ∨ ∃ since, typeFork entry.1 = some since ∧ since ≤ fork)
    (htypes₂ : ∀ entry ∈ receipts₂,
      entry.1 = 0 ∨ ∃ since, typeFork entry.1 = some since ∧ since ≤ fork)
    (hroot₁ : receiptsRoot receipts₁ = .ok root') (hroot₂ : receiptsRoot receipts₂ = .ok root') :
    receipts₁ = receipts₂ ∨
      ∃ values₁ values₂ pair,
        receipts₁.mapM (fun (type, r) => encodeReceipt (fork := fork) type r) = .ok values₁ ∧
        receipts₂.mapM (fun (type, r) => encodeReceipt (fork := fork) type r) = .ok values₂ ∧
        findIndexedCollision values₁ values₂ = some pair ∧ IsCollision keccak256 pair := by
  obtain ⟨values₁, hvalues₁, hindexed₁⟩ := indexedRoot_of_mapM hroot₁
  obtain ⟨values₂, hvalues₂, hindexed₂⟩ := indexedRoot_of_mapM hroot₂
  rcases indexedRoot_binding hindexed₁ hindexed₂ with rfl | ⟨pair, hfound, hvalid⟩
  · -- The decoder reads the type and the receipt back from the bytes of each.
    refine .inl (eq_of_mapM_eq_ok (fun ⟨tx, rx⟩ hx ⟨ty, ry⟩ hy bytes hxb hyb => ?_)
      hvalues₁ hvalues₂)
    exact Except.ok.inj ((decodeReceipt_encodeReceipt hxb (htypes₁ _ hx)).symm.trans
      (decodeReceipt_encodeReceipt hyb (htypes₂ _ hy)))
  · exact .inr ⟨values₁, values₂, pair, hvalues₁, hvalues₂, hfound, hvalid⟩

end EthLib.Execution.Blocks

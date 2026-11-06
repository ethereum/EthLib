module

public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Proofs.Trie.Binding
public import EthLib.Execution.Proofs.Trie.Root
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the roots of a block body

An empty list has the root of the empty trie, the Keccak-256 hash of `0x80`.

So a block with no transactions, receipts or withdrawals has that root for each list.

The key of each item is the RLP encoding of its index, so the keys of a list's trie are distinct.

Two lists with one root then give every key one value, or the search finds a Keccak-256 collision.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
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

end EthLib.Execution.Blocks

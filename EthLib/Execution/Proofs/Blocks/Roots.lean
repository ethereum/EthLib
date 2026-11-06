module

public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Proofs.Trie.Root
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the roots of a block body

An empty list has the root of the empty trie, the Keccak-256 hash of `0x80`.

So a block with no transactions, receipts or withdrawals has that root for each list.

The trie of a list has one entry for each item, in order.

Entry `i` holds the RLP encoding of `i` and item `i`.

The RLP encoding of a number determines the number, so the keys are distinct.
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

/-! ## The entries of the trie of a list -/

/-- The trie of a list has one entry for each item. -/
theorem length_indexedEntries {values : List ByteArray} {entries : List (ByteArray × ByteArray)}
    (h : indexedEntries values = .ok entries) : entries.length = values.length := by
  rw [mapM_ok_length h, List.length_zip, List.length_range, Nat.min_self]

/-- Entry `i` of the trie of a list holds the RLP encoding of `i` and item `i`. -/
theorem indexedEntries_getElem {values : List ByteArray} {entries : List (ByteArray × ByteArray)}
    (h : indexedEntries values = .ok entries) (i : Fin entries.length) :
    Codec.encode i.val = .ok entries[i].1 ∧
      entries[i].2 = values[i.val]'(length_indexedEntries h ▸ i.isLt) := by
  have hi : i.val < ((List.range values.length).zip values).length := by
    rw [← mapM_ok_length h]
    exact i.isLt
  have hentry := mapM_ok_getElem h i.val hi
  simp only [List.getElem_zip, List.getElem_range] at hentry
  -- The entry is the encoding of the index, paired with the item.
  cases hencode : (Codec.encode i.val : Except RlpError ByteArray) with
  | error e => simp [hencode, bind, Except.bind] at hentry
  | ok key =>
    simp only [hencode, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hentry
    simp [← hentry]

/-- The trie of a list has distinct keys. -/
theorem indexedEntries_nodup {values : List ByteArray} {entries : List (ByteArray × ByteArray)}
    (h : indexedEntries values = .ok entries) : (entries.map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij heq
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map] at heq
  -- Two keys that agree encode the same index.
  have hi' := (indexedEntries_getElem h ⟨i, hi⟩).1
  have hj' := (indexedEntries_getElem h ⟨j, hj⟩).1
  simp only [Fin.getElem_fin] at hi' hj'
  rw [heq] at hi'
  exact Nat.ne_of_lt hij (Codec.encode_injective hi' hj')

end EthLib.Execution.Blocks

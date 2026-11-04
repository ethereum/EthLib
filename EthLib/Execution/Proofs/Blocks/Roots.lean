module

public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Proofs.Trie.Root

/-!
# Proofs: the roots of a block body

An empty list has the root of the empty trie, the Keccak-256 hash of `0x80`.

So a block with no transactions, receipts or withdrawals has that root for each list.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Trie
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

end EthLib.Execution.Blocks

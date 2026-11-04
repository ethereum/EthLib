module

public import EthLib.Execution.Blocks.Receipt
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Trie.Root

/-!
# `Blocks.Roots`

The roots of the lists of a block body: its transactions, its receipts and its withdrawals.

Each root commits to a list in a plain trie.

The key of the item at index `i`, from 0, is the RLP encoding of `i`.

Its value is the bytes of the item.

Section 4.4 of the Yellow Paper, Shanghai version, defines the first two: [`Paper.tex`][yp].

[EIP-2718][eip-2718] makes the value of a typed transaction or receipt its typed bytes.

[EIP-4895][eip-4895] adds the withdrawals root at Shapella.

Ethereum hashes with Keccak-256.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-2718]: https://eips.ethereum.org/EIPS/eip-2718#transactions
[eip-4895]: https://eips.ethereum.org/EIPS/eip-4895#specification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Execution.Transactions
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The entries of the trie of a list: the RLP encoding of each index, and the item there. -/
def indexedEntries (values : List ByteArray) : Except RlpError (List (ByteArray × ByteArray)) :=
  (List.range values.length).zip values |>.mapM fun (index, value) => do
    return (← Codec.encode index, value)

/-- The root of a list: the root of the plain trie of its indexed entries. -/
def indexedRoot (values : List ByteArray) : Except TrieError Hash32 := do
  root keccak256 ⟨false, ← (indexedEntries values).mapError .rlp⟩

/-- The transactions root: the root of the list of the bytes of each transaction. -/
def transactionsRoot (transactions : List Transaction) : Except TrieError Hash32 := do
  indexedRoot (← (transactions.mapM encodeTransaction).mapError .rlp)

/-- The receipts root: the root of the list of the bytes of each receipt.

Each receipt comes with the type of its transaction. -/
def receiptsRoot {fork : Fork} (receipts : List (UInt8 × Receipt fork)) :
    Except TrieError Hash32 := do
  indexedRoot (← (receipts.mapM fun (type, r) => encodeReceipt (fork := fork) type r).mapError .rlp)

/-- The withdrawals root: the root of the list of the RLP encoding of each withdrawal. -/
def withdrawalsRoot (withdrawals : List Withdrawal) : Except TrieError Hash32 := do
  indexedRoot (← (withdrawals.mapM Codec.encode).mapError .rlp)

end EthLib.Execution.Blocks

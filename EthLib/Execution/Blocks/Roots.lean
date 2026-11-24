module

public import EthLib.Execution.Blocks.Receipt
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Execution.Trie.Root

/-!
# `Blocks.Roots`

The roots of the lists of a block body: its transactions, its receipts and its withdrawals.

Section 4.4.2 of the Yellow Paper, Shanghai version, defines all three: [`Paper.tex`][yp].

[EIP-2718][eip-2718] makes the value of a typed transaction or receipt its typed bytes.

[EIP-4895][eip-4895] adds the withdrawals root at Shapella.

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

/-- The entries of the trie of a list: the RLP encoding of each index, and the item there.

The key of the item at index `i`, from 0, is the RLP encoding of `i`.

Its value is the bytes of the item. -/
def indexedEntries (values : List ByteArray) : Except RlpError (List (ByteArray × ByteArray)) :=
  -- Yellow Paper §4.4.2: the pair `(RLP(k), v)` for each index `k < ||values||`.
  (List.range values.length).zip values |>.mapM fun (index, value) => do
    return (← Codec.encode index, value)

/-- The root of a list: the root of the plain trie of its indexed entries. -/
def indexedRoot (values : List ByteArray) : Except TrieError Hash32 := do
  -- `TRIE` of Appendix D over those pairs, whose keys are not hashed first.
  --
  -- Ethereum hashes with Keccak-256.
  root keccak256 ⟨false, ← (indexedEntries values).mapError .rlp⟩

/-- The transactions root: the root of the list of the bytes of each transaction. -/
def transactionsRoot (transactions : List Transaction) : Except TrieError Hash32 := do
  -- Yellow Paper §4.4.2: `H_t = TRIE({p_T(i, B_T[i])})`.
  --
  -- The value of `p_T` is `RLP(L_T(T))` for `T_x = 0`, and `(T_x) · RLP(L_T(T))` otherwise.
  indexedRoot (← (transactions.mapM encodeTransaction).mapError .rlp)

/-- The receipts root: the root of the list of the bytes of each receipt.

Each receipt comes with the type of its transaction. -/
def receiptsRoot {fork : Fork} (receipts : List (UInt8 × Receipt fork)) :
    Except TrieError Hash32 := do
  -- Yellow Paper §4.4.2: `H_e = TRIE({p_R(i, B_R[i])})`.
  --
  -- The value of `p_R` is `RLP(L_R(R))` for `R_x = 0`, and `(R_x) · RLP(L_R(R))` otherwise.
  indexedRoot (← (receipts.mapM fun (type, r) => encodeReceipt (fork := fork) type r).mapError .rlp)

/-- The withdrawals root: the root of the list of the RLP encoding of each withdrawal. -/
def withdrawalsRoot (withdrawals : List Withdrawal) : Except TrieError Hash32 := do
  -- Yellow Paper §4.4.2: `H_w = TRIE({p_W(i, B_W[i])})`.
  --
  -- The value of `p_W` is `RLP(L_W(W))`, the second part of `p_W(k, W) = (RLP(k), RLP(L_W(W)))`.
  indexedRoot (← (withdrawals.mapM Codec.encode).mapError .rlp)

end EthLib.Execution.Blocks

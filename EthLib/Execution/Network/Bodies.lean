module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Network.Blocks

/-!
# `Execution.Network.Bodies`

The check of a block body that the eth capability sends, from "Block Encoding and Validity" in
[`caps/eth.md`][eth].

A node syncs by fetching headers first, then the bodies of those blocks with GetBlockBodies (0x05).
BlockBodies (0x06) answers with one body for each hash.

A body crosses the wire as the RLP item `[transactions, ommers]`, followed by `withdrawals` from Shapella.

Each transaction is an item: a legacy transaction is its RLP list, and a typed one is the byte string `type || payload`.

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#block-encoding-and-validity
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- Why a body does not belong to a header. -/
inductive BodyError where
  /-- The item is not `[transactions, ommers]`, with the withdrawals from Shapella. -/
  | decoding (error : RlpError)
  /-- A root cannot be computed, because a trie value is empty or too long to encode. -/
  | trie (error : TrieError)
  /-- The trie root of the transactions is not the transactions root of the header. -/
  | wrongTransactionsRoot
  /-- From Shapella, the body has no withdrawals. -/
  | missingWithdrawals
  /-- Before Shapella, the body has withdrawals. -/
  | unexpectedWithdrawals
  /-- The trie root of the withdrawals is not the withdrawals root of the header. -/
  | wrongWithdrawalsRoot
  /-- The ommers list holds more than `MAX_OMMERS` headers. -/
  | tooManyOmmers (count : Nat)
  /-- The Keccak-256 hash of the ommers list is not the ommers hash of the header. -/
  | wrongOmmersHash
  /-- The ommer at `index` has a block number above that of the block that holds it. -/
  | ommerAfterBlock (index number : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 601, above every code of the other eth errors.

A new constructor takes a new code, so that each code keeps its meaning. -/
def BodyError.code : BodyError → UInt32
  | .decoding _ => 601
  | .trie _ => 602
  | .wrongTransactionsRoot => 603
  | .missingWithdrawals => 604
  | .unexpectedWithdrawals => 605
  | .wrongWithdrawalsRoot => 606
  | .tooManyOmmers _ => 607
  | .wrongOmmersHash => 608
  | .ommerAfterBlock .. => 609

/-- The bytes that a transaction item stands for in the trie of the transactions root.

A list is the RLP encoding of a legacy transaction, and a byte string is a typed transaction as it is. -/
def transactionBytes : Item → Except RlpError ByteArray
  | .bytes b => .ok b
  | item@(.list _) => encode item

/-- The bytes of each transaction of a body, in order. -/
def transactionValues (transactions : Item) : Except RlpError (List ByteArray) := do
  (← transactions.toItems).mapM transactionBytes

/-- The transactions of a body match the transactions root of the header. -/
def checkTransactions {fork : Fork} (header : Header fork) (transactions : Item) :
    Except BodyError Unit := do
  let values ← (transactionValues transactions).mapError .decoding
  let root ← (indexedRoot values).mapError .trie
  ensure (root == header.transactionsRoot) .wrongTransactionsRoot

/-- The withdrawals of a body, from Shapella, match the withdrawals root of the header. -/
def checkWithdrawals {fork : Fork} (header : Header fork) (h : .shapella ≤ fork)
    (withdrawals : Item) : Except BodyError Unit := do
  let ws : List Withdrawal ← (Codec.ofItem withdrawals).mapError .decoding
  let root ← (withdrawalsRoot ws).mapError .trie
  ensure (root == header.withdrawalsRoot h) .wrongWithdrawalsRoot

/-- The ommers of a body match the ommers hash of the header, and stay within its limits.

The hash is that of the ommers item as received. -/
def checkOmmers {fork : Fork} (header : Header fork) (ommers : Item) : Except BodyError Unit := do
  let items ← ommers.toItems.mapError .decoding
  ensure (items.length ≤ MAX_OMMERS) (.tooManyOmmers items.length)
  let encoded ← (encode ommers).mapError .decoding
  ensure (keccak256 encoded == header.ommersHash) .wrongOmmersHash
  (List.range items.length).zip items |>.forM fun (i, ommer) => do
    let n ← (headerNumber ommer).mapError .decoding
    ensure (n ≤ header.number) (.ommerAfterBlock i n)

/--
Check a body against the header that it was requested for.

The body is the RLP item `[transactions, ommers]`, followed by `withdrawals` from Shapella.

The check succeeds exactly when all of the following hold, and it fails with the first that does not.

1. The body is a list of 2 items before Shapella and of 3 items from Shapella.
2. The trie root of the transactions is `header.transactionsRoot`.
3. From Shapella, the trie root of the withdrawals is `header.withdrawalsRoot`.
4. The ommers list holds at most `MAX_OMMERS` items.
5. The Keccak-256 hash of the ommers list is `header.ommersHash`.
6. Each ommer has a block number at most `header.number`.

"Block Encoding and Validity" lists these among the rules of data validity.

The check reads only the message and the header.

It leaves out three rules of that section, each for a reason.

- The transactions "must be valid for inclusion into the chain at the block's number".
  That needs more than the header: the state before the block.
- The ommer headers must be valid and must refer to recent ancestors.
  That needs the chain.
- "The sum of the `gas-limit`s of all transactions must not exceed the `gas-limit` of the block."
  Block validity is weaker: it asks only that the gas limit of each transaction is at most the gas that the block still has after the transactions before it (`gasAllowanceExceeded`).
  A block of two transactions with gas limit 20,000,000 each, in a block of gas limit 30,000,000, is valid.
  So EthLib does not ask for the stricter rule.

The caller pairs each body with the header of the hash that it requested.
-/
def checkBody {fork : Fork} (header : Header fork) (body : Item) : Except BodyError Unit := do
  let items ← body.toItems.mapError .decoding
  if h : .shapella ≤ fork then
    match items with
    | [transactions, ommers, withdrawals] =>
      checkTransactions header transactions
      checkWithdrawals header h withdrawals
      checkOmmers header ommers
    | [_, _] => throw .missingWithdrawals
    | _ => throw (.decoding (.wrongFieldCount 3 items.length))
  else
    match items with
    | [transactions, ommers] =>
      checkTransactions header transactions
      checkOmmers header ommers
    | [_, _, _] => throw .unexpectedWithdrawals
    | _ => throw (.decoding (.wrongFieldCount 2 items.length))

end EthLib.Execution.Network

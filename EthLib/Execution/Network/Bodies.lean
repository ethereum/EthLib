module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Network.Blocks

/-!
# `Execution.Network.Bodies`

The check of a block body against the header that it was requested for.

It follows "Block Encoding and Validity" in [`caps/eth.md`][eth].

A node fetches headers first, then asks for their bodies with GetBlockBodies (0x05).

BlockBodies (0x06) answers with one body for each hash.

A body is the RLP list of its transactions and its ommers, then its withdrawals from Shapella.

A legacy transaction is an RLP list, and a typed one is the byte string of its type and payload.

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#block-encoding-and-validity
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks
open EthLib.Execution.Trie
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- Why a body does not belong to a header. -/
inductive BodyError where
  /-- The body, or one of its parts, does not have the RLP form that the check reads. -/
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
  /-- The ommers list holds more than two headers. -/
  | tooManyOmmers (count : Nat)
  /-- The Keccak-256 hash of the ommers list is not the ommers hash of the header. -/
  | wrongOmmersHash
  /-- An ommer has a block number above that of the block that holds it. -/
  | ommerAfterBlock (index number : Nat)
  /-- A transaction is a byte string that is empty or whose first byte is not a type. -/
  | untypedTransaction
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
  | .untypedTransaction => 610

/-- The bytes that a transaction item stands for in the trie of the transactions root.

A list is a legacy transaction, and it stands for its RLP encoding.

A byte string is a typed transaction, and it stands for itself.

Its first byte is the type, which [EIP-2718][eip-2718] keeps at most `0x7f`.

An RLP list starts with a byte of at least `0xc0`, so the two forms never stand for the same bytes.

[eip-2718]: https://eips.ethereum.org/EIPS/eip-2718#transactiontype-only-goes-up-to-0x7f -/
def transactionBytes : Item → Except BodyError ByteArray
  | .bytes b =>
    if h : 0 < b.size then
      if b[0] < 0x80 then .ok b else .error .untypedTransaction
    else .error .untypedTransaction
  | item@(.list _) => (encode item).mapError .decoding

/-- The bytes of each transaction of a body, in order. -/
def transactionValues (transactions : Item) : Except BodyError (List ByteArray) := do
  (← transactions.toItems.mapError .decoding).mapM transactionBytes

/-- The transactions of a body match the transactions root of the header. -/
def checkTransactions {fork : Fork} (header : Header fork) (transactions : Item) :
    Except BodyError Unit := do
  let values ← transactionValues transactions
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

The body is the RLP list of the transactions and the ommers, then the withdrawals from Shapella.

The check fails with the first of the following that does not hold.

1. The body is a list of 2 items before Shapella and of 3 items from Shapella.
2. Each transaction sent as a byte string starts with a type below `0x80`.
3. The trie root of the transactions is the transactions root of the header.
4. From Shapella, the trie root of the withdrawals is the withdrawals root of the header.
5. The ommers list holds at most two items.
6. The Keccak-256 hash of the ommers list is the ommers hash of the header.
7. Each ommer is a list whose ninth field, the block number, is at most that of the block.

The check does not decode the ommers further, since their validity is left to the chain.

"Block Encoding and Validity" lists these among the rules of data validity.

The check reads only the body and the header.

It leaves out four rules of that section, each for a reason.

- "The block `header` must be valid."
  The header checks of the eth protocol decide it before the body is asked for.
- The transactions "must be valid for inclusion into the chain at the block's number".
  That needs the state before the block.
- The ommer headers must be valid, and must be recent ancestors not included before.
  That needs the chain.
- "The sum of the `gas-limit`s of all transactions must not exceed the `gas-limit` of the block."
  Block validity is weaker, and a stricter rule would reject valid blocks.

Block validity asks only that each transaction fits in the gas that the block still has.

Take a block of gas limit 30,000,000 and two transactions of gas limit 20,000,000 each.

If the first uses 21,000 gas, the second sees 29,979,000 gas left, so the block can be valid.

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

/-- The body of a block as it crosses the wire.

It lists the transactions and the ommers, then the withdrawals from Shapella. -/
def bodyOf {fork : Fork} (block : Block fork Transaction) : Except RlpError Item := do
  let transactions ← block.transactions.mapM bodyItem
  return .list ([.list transactions, ommersItem block.ommers] ++ Item.ofSince block.withdrawals)

end EthLib.Execution.Network

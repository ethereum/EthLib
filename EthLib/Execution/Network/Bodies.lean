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

[eth]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/caps/eth.md#block-encoding-and-validity
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
  /-- The transactions root `expected` of the header is not `actual`, that of the transactions. -/
  | wrongTransactionsRoot (expected actual : Hash32)
  /-- From Shapella, the body has no withdrawals. -/
  | missingWithdrawals
  /-- Before Shapella, the body has withdrawals. -/
  | unexpectedWithdrawals
  /-- The withdrawals root `expected` of the header is not `actual`, that of the withdrawals. -/
  | wrongWithdrawalsRoot (expected actual : Hash32)
  /-- The ommers list holds more than two headers. -/
  | tooManyOmmers (count : Nat)
  /-- The ommers hash `expected` of the header is not `actual`, the hash of the ommers list. -/
  | wrongOmmersHash (expected actual : Hash32)
  /-- An ommer has a block number above that of the block that holds it. -/
  | ommerAfterBlock (index number : Nat)
  /-- A transaction is a byte string whose first byte `first` is not a type.

  The first byte is none when the string is empty. -/
  | untypedTransaction (first : Option UInt8)
  /-- The transaction at `index`, counted from 0, holds no transaction of the fork. -/
  | invalidTransaction (index : Nat) (error : TransactionError)
  /-- The transaction at `index` has the gas limit `gas`, above the block's gas limit `limit`. -/
  | gasLimitAboveBlock (index gas limit : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 601, above every code of the other eth errors.

A new constructor takes a new code, so that each code keeps its meaning. -/
def BodyError.code : BodyError → UInt32
  | .decoding _ => 601
  | .trie _ => 602
  | .wrongTransactionsRoot .. => 603
  | .missingWithdrawals => 604
  | .unexpectedWithdrawals => 605
  | .wrongWithdrawalsRoot .. => 606
  | .tooManyOmmers _ => 607
  | .wrongOmmersHash .. => 608
  | .ommerAfterBlock .. => 609
  | .untypedTransaction _ => 610
  | .invalidTransaction .. => 611
  | .gasLimitAboveBlock .. => 612

/-- The bytes that a transaction stands for in the trie of the transactions root.

A list is a legacy transaction, and it stands for the bytes it was read from.

The decoder keeps those bytes as its RLP encoding.

A byte string is a typed transaction, and it stands for itself.

Its first byte is the type, which [EIP-2718][eip-2718] keeps at most `0x7f`.

An RLP list starts with a byte of at least `0xc0`, so the two forms never stand for the same bytes.

[eip-2718]: https://eips.ethereum.org/EIPS/eip-2718#transactiontype-only-goes-up-to-0x7f -/
def transactionBytes (tx : Encoded) : Except BodyError ByteArray :=
  match tx.item with
  | .bytes b =>
    if h : 0 < b.size then
      if b[0] < 0x80 then .ok b else .error (.untypedTransaction (some b[0]))
    else .error (.untypedTransaction none)
  | .list _ => .ok tx.bytes

/-- The bytes of each transaction of a body, in order. -/
def transactionValues (transactions : Encoded) : Except BodyError (List ByteArray) := do
  (← transactions.parts.mapError .decoding).mapM transactionBytes

/-- Each transaction of a body is one of the fork, with a gas limit at most that of the header.

A transaction only has to fit in the gas that the block has left, so the sum may exceed the limit.
-/
def checkGasLimits {fork : Fork} (header : Header fork) (transactions : Item) :
    Except BodyError Unit := do
  let items ← transactions.toItems.mapError .decoding
  (List.range items.length).zip items |>.forM fun (i, item) => do
    let tx ← (decodeBodyTransaction fork item).mapError (.invalidTransaction i)
    ensure (tx.gas.toNat ≤ header.gasLimit) (.gasLimitAboveBlock i tx.gas.toNat header.gasLimit)

/-- The transactions of a body match the transactions root of the header.

Each of them is then one of the fork, with a gas limit at most that of the header. -/
def checkTransactions {fork : Fork} (header : Header fork) (transactions : Encoded) :
    Except BodyError Unit := do
  let values ← transactionValues transactions
  let root ← (indexedRoot values).mapError .trie
  ensure (root == header.transactionsRoot) (.wrongTransactionsRoot header.transactionsRoot root)
  checkGasLimits header transactions.item

/-- The withdrawals of a body, from Shapella, match the withdrawals root of the header. -/
def checkWithdrawals {fork : Fork} (header : Header fork) (h : .shapella ≤ fork)
    (withdrawals : Item) : Except BodyError Unit := do
  let ws : List Withdrawal ← (Codec.ofItem withdrawals).mapError .decoding
  let root ← (withdrawalsRoot ws).mapError .trie
  ensure (root == header.withdrawalsRoot h) (.wrongWithdrawalsRoot (header.withdrawalsRoot h) root)

/-- The ommers of a body match the ommers hash of the header, and stay within its limits.

The hash reads the bytes that the ommers list was read from.

The decoder keeps those bytes as its RLP encoding. -/
def checkOmmers {fork : Fork} (header : Header fork) (ommers : Encoded) :
    Except BodyError Unit := do
  let items ← ommers.item.toItems.mapError .decoding
  ensure (items.length ≤ MAX_OMMERS) (.tooManyOmmers items.length)
  ensure (keccak256 ommers.bytes == header.ommersHash)
    (.wrongOmmersHash header.ommersHash (keccak256 ommers.bytes))
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
4. Each transaction decodes at the fork, with a gas limit at most the gas limit of the header.
5. From Shapella, the trie root of the withdrawals is the withdrawals root of the header.
6. The ommers list holds at most two items.
7. The Keccak-256 hash of the ommers list is the ommers hash of the header.
8. Each ommer is a list whose ninth field, the block number, is at most that of the block.

The check does not decode the ommers further, since their validity is left to the chain.

"Block Encoding and Validity" lists these among the rules of data validity.

The check reads only the body and the header.

It leaves out three rules of that section, each for a reason.

- "The block `header` must be valid."
  The header checks of the eth protocol decide it before the body is asked for.
- The transactions "must be valid for inclusion into the chain at the block's number".
  Step 4 checks only that each decodes at the fork, so a type that the fork lacks is rejected.
  The rest needs the state before the block.
- The ommer headers must be valid, and must be recent ancestors not included before.
  That needs the chain.

Step 4 follows "The `gas-limit` of each transaction must not exceed the `gas-limit` of the block."

The sum of the gas limits may exceed that of the block.

Take a block of gas limit 30,000,000 and two transactions of gas limit 20,000,000 each.

If the first uses 21,000 gas, the second sees 29,979,000 gas left, so the block can be valid.

The caller pairs each body with the header of the hash that it requested.

The body keeps the bytes it was read from.

Each legacy transaction and the ommers list are hashed from their slices of those bytes.

So the check never encodes an item that a peer chose.
-/
def checkBody {fork : Fork} (header : Header fork) (body : Encoded) : Except BodyError Unit := do
  let items ← body.parts.mapError .decoding
  if h : .shapella ≤ fork then
    match items with
    | [transactions, ommers, withdrawals] =>
      checkTransactions header transactions
      checkWithdrawals header h withdrawals.item
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

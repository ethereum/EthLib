module

public import EthLib.Execution.Blocks.Block
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Network.Blocks

/-!
# `Execution.Network.Bodies`

The check of a block body against the header that it was requested for.

It follows the section Block Encoding and Validity of [`caps/eth.md`][eth].

A node fetches headers first, then asks for their bodies with GetBlockBodies (0x05).

BlockBodies (0x06) answers with one body for each hash.

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

A legacy transaction is an RLP list, and a typed one is the byte string of its type and payload. -/
def transactionBytes (tx : Encoded) : Except BodyError ByteArray :=
  match tx.item with
  -- A byte string is a typed transaction, and it stands for itself.
  --
  -- `typed-tx = tx-type || tx-data`, with `tx-type` at most `0x7f` by EIP-2718; empty is refused.
  -- https://eips.ethereum.org/EIPS/eip-2718#transactiontype-only-goes-up-to-0x7f
  --
  -- An RLP list starts with a byte of at least `0xc0`.
  --
  -- So the two forms never stand for the same bytes.
  | .bytes b =>
    if h : 0 < b.size then
      if b[0] < 0x80 then .ok b else .error (.untypedTransaction (some b[0]))
    else .error (.untypedTransaction none)
  -- A list is a `legacy-tx`, which stands for the bytes it was read from.
  --
  -- The decoder keeps those bytes as its RLP encoding.
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
    -- Each transaction decodes at the fork, so a type that the fork lacks fails.
    let tx ← (decodeBodyTransaction fork item).mapError (.invalidTransaction i)
    -- The gas limit of each transaction does not exceed the gas limit of the block.
    --
    -- Block Encoding and Validity bounds the gas limit of each transaction by that of the block.
    --
    -- It does not bound their sum.
    --
    -- Take a block of gas limit 30,000,000 and two transactions of gas limit 20,000,000 each.
    --
    -- If the first uses 21,000 gas, the second sees 29,979,000 gas left, so the block can be valid.
    ensure (tx.gas.toNat ≤ header.gasLimit) (.gasLimitAboveBlock i tx.gas.toNat header.gasLimit)

/-- The transactions of a body match the transactions root of the header.

Each of them is then one of the fork, with a gas limit at most that of the header. -/
def checkTransactions {fork : Fork} (header : Header fork) (transactions : Encoded) :
    Except BodyError Unit := do
  let values ← transactionValues transactions
  -- The `txs-root` of the header is the trie root of the transactions, by index.
  let root ← (indexedRoot values).mapError .trie
  ensure (root == header.transactionsRoot) (.wrongTransactionsRoot header.transactionsRoot root)
  checkGasLimits header transactions.item

/-- The withdrawals of a body, from Shapella, match the withdrawals root of the header. -/
def checkWithdrawals {fork : Fork} (header : Header fork) (h : .shapella ≤ fork)
    (withdrawals : Item) : Except BodyError Unit := do
  let ws : List Withdrawal ← (Codec.ofItem withdrawals).mapError .decoding
  -- The `withdrawals-root` of the header is the trie root of the withdrawals, by EIP-4895.
  let root ← (withdrawalsRoot ws).mapError .trie
  ensure (root == header.withdrawalsRoot h) (.wrongWithdrawalsRoot (header.withdrawalsRoot h) root)

/-- The ommers of a body match the ommers hash of the header, and stay within its limits.

The hash reads the bytes that the ommers list was read from.

The decoder keeps those bytes as its RLP encoding. -/
def checkOmmers {fork : Fork} (header : Header fork) (ommers : Encoded) :
    Except BodyError Unit := do
  let items ← ommers.item.toItems.mapError .decoding
  -- At most two ommers.
  ensure (items.length ≤ MAX_OMMERS) (.tooManyOmmers items.length)
  -- `keccak256(ommers)` is the `ommers-hash` of the header, over the bytes the list was read from.
  ensure (keccak256 ommers.bytes == header.ommersHash)
    (.wrongOmmersHash header.ommersHash (keccak256 ommers.bytes))
  -- Each ommer is a header list whose number, its ninth field, is at most that of the block.
  (List.range items.length).zip items |>.forM fun (i, ommer) => do
    let n ← (headerNumber ommer).mapError .decoding
    ensure (n ≤ header.number) (.ommerAfterBlock i n)

/--
Check a body against the header that it was requested for.

The caller pairs each body with the header of the hash that it requested.

The check fails with the first rule that does not hold, in the order of the lines below.

The rules that the check marks come from the data validity rules of Block Encoding and Validity.

The check reads only the body and the header.

The check does not decode the ommers further, since their validity is left to the chain.

It leaves out three rules of that section, each for a reason.

- The block header must be valid.
  The header checks of the eth protocol decide it before the body is asked for.
- The transactions must be valid for inclusion into the chain at the number of the block.
  The check reads only that each decodes at the fork, so a type that the fork lacks is rejected.
  The rest needs the state before the block.
- The ommer headers must be valid, and must be recent ancestors not included before.
  That needs the chain.
-/
def checkBody {fork : Fork} (header : Header fork) (body : Encoded) : Except BodyError Unit := do
  -- The body keeps the bytes it was read from.
  --
  -- Each legacy transaction and the ommers list are hashed from their slices of those bytes.
  --
  -- So the check never encodes an item that a peer chose.
  let items ← body.parts.mapError .decoding
  -- A body is the RLP list of the transactions and the ommers, then the withdrawals from Shapella.
  --
  -- From Shapella, `[transactions, ommers, withdrawals]`, by EIP-4895.
  if h : .shapella ≤ fork then
    match items with
    | [transactions, ommers, withdrawals] =>
      -- The transactions: types, the transactions root, then decoding and gas limits.
      checkTransactions header transactions
      -- The withdrawals root.
      checkWithdrawals header h withdrawals.item
      -- The ommers: their count, the ommers hash and their numbers.
      checkOmmers header ommers
    | [_, _] => throw .missingWithdrawals
    | _ => throw (.decoding (.wrongFieldCount 3 items.length))
  -- Before Shapella, `[transactions, ommers]`.
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
  -- `block-body = [transactions, ommers, withdrawals]`, the withdrawals from Shapella.
  let transactions ← block.transactions.mapM bodyItem
  return .list ([.list transactions, ommersItem block.ommers] ++ Item.ofSince block.withdrawals)

end EthLib.Execution.Network

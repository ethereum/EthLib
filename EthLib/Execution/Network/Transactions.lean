module

public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Network.Protocol
public import EthLib.Serialization.Rlp.Decode
public import EthLib.Serialization.Rlp.Codec

/-!
# `Execution.Network.Transactions`

The transaction exchange of the eth capability, from "Protocol Messages" of [`caps/eth.md`][eth].

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#protocol-messages

- Transactions (0x02) sends whole transactions.
- NewPooledTransactionHashes (0x08) announces transactions by type, size and hash.
- GetPooledTransactions (0x09) asks for transactions by hash, and PooledTransactions (0x0a)
  answers.

A transaction crosses the wire as an RLP list when it is legacy, and as the byte string
`tx-type || tx-data` when it is typed, as
[EIP-2976](https://eips.ethereum.org/EIPS/eip-2976#specification) says.

The messages carry each transaction as its RLP item.

From eth/68 on, an announcement has three lists of equal length, as
[EIP-5793](https://eips.ethereum.org/EIPS/eip-5793#specification) says.

From eth/72 on, it also has a 16-byte bitmap of the cells that the peer holds, empty when no blob
transaction is announced, as [EIP-8070](https://eips.ethereum.org/EIPS/eip-8070#specification)
says.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The message ID of Transactions. -/
def TRANSACTIONS_ID : Nat := 0x02

/-- The message ID of NewPooledTransactionHashes. -/
def NEW_POOLED_TRANSACTION_HASHES_ID : Nat := 0x08

/-- The message ID of GetPooledTransactions. -/
def GET_POOLED_TRANSACTIONS_ID : Nat := 0x09

/-- The message ID of PooledTransactions. -/
def POOLED_TRANSACTIONS_ID : Nat := 0x0a

/-- An announcement of transactions: one type, one size and one hash for each transaction. -/
inductive Announcement where
  /-- eth/68 to eth/71: `[txtypes, [txsize, ...], [txhash, ...]]`. -/
  | eth68 (types : ByteArray) (sizes : List Nat) (hashes : List Hash32)
  /-- eth/72: `[txtypes, [txsize, ...], [txhash, ...], cells]`.

  The cells are 16 bytes, or none when no blob transaction is announced.

  The reader accepts either form whatever the types, so it does not check that rule of EIP-8070.
  -/
  | eth72 (types : ByteArray) (sizes : List Nat) (hashes : List Hash32)
      (cells : Option (Vector UInt8 16))
  deriving DecidableEq

namespace Announcement

/-- The announcement as an RLP list, in the field order of its version. -/
def toItem : Announcement → Item
  | eth68 t s h => .list [Codec.toItem t, Codec.toItem s, Codec.toItem h]
  | eth72 t s h c => .list [Codec.toItem t, Codec.toItem s, Codec.toItem h, Codec.toItem c]

/-- The types, the sizes and the hashes of an announcement. -/
def lists : Announcement → ByteArray × List Nat × List Hash32
  | eth68 t s h | eth72 t s h _ => (t, s, h)

/-- Whether an announcement has as many types and sizes as hashes. -/
def lengthsAgree (a : Announcement) : Bool :=
  let (t, s, h) := a.lists
  t.size == h.length && s.length == h.length

/-- The announcement of a version in an RLP list.

eth/68 to eth/71 read three fields, and eth/72 reads four.

The reader of messages also checks that the three lists have equal lengths. -/
def ofItem (version : EthVersion) (item : Item) : Except RlpError Announcement := do
  if version < .eth72 then
    match ← item.fields 3 with
    | [t, s, h] => return eth68 (← t.field 0) (← s.field 1) (← h.field 2)
    | items => throw (.wrongFieldCount 3 items.length)
  else
    match ← item.fields 4 with
    | [t, s, h, c] => return eth72 (← t.field 0) (← s.field 1) (← h.field 2) (← c.field 3)
    | items => throw (.wrongFieldCount 4 items.length)

end Announcement

/-- The transaction type of a blob transaction, from EIP-4844. -/
def BLOB_TX_TYPE : UInt8 := 0x03

/--
The hash of a transaction as it crosses the wire.

A legacy transaction hashes its RLP list, and a typed one its bytes `tx-type || tx-data`.

A blob transaction in PooledTransactions can come in its network form, the type 3 followed by
`rlp([tx_payload_body, ...])`, as
[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#networking) says.

Its hash is the hash of `0x03 || rlp(tx_payload_body)`, the transaction without its blobs.

The payload of a canonical blob transaction starts with the chain ID, a scalar, and the network
form with the body, a list, so the first item tells the two apart.
-/
def wireHash (tx : Item) : Except RlpError Hash32 := do
  match tx with
  | .list _ => return Cryptography.Hash.Keccak.keccak256 (← Serialization.Rlp.encode tx)
  | .bytes b =>
    let canonical := Cryptography.Hash.Keccak.keccak256 b
    match b.data.toList with
    | type :: rest =>
      if type = BLOB_TX_TYPE then
        match Serialization.Rlp.decode ⟨rest.toArray⟩ with
        | .ok (.list (body@(.list _) :: _)) =>
          return Cryptography.Hash.Keccak.keccak256
            (⟨#[BLOB_TX_TYPE]⟩ ++ (← Serialization.Rlp.encode body))
        | _ => return canonical
      else return canonical
    | [] => return canonical

/-- Why the transactions of a PooledTransactions do not answer a GetPooledTransactions. -/
inductive PoolError where
  /-- A transaction has no hash, since its item does not encode. -/
  | rlp (error : RlpError)
  /-- The hashes of the transactions are not the requested hashes, in their order, with some
  left out. -/
  | notRequested
  /-- The response is not PooledTransactions with the request ID of the request. -/
  | notAnswer
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 301, above every code of the other eth errors.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PoolError.code : PoolError → UInt32
  | .rlp _ => 301
  | .notRequested => 302
  | .notAnswer => 303

/--
Whether the transactions `txs` answer a request of the hashes `requested`.

The transactions must be in the order of the request, but the peer may leave some out, as
"PooledTransactions (0x0a)" says.

So their hashes form a sublist of the requested hashes.
-/
def checkPooled (requested : List Hash32) (txs : List Item) : Except PoolError Unit := do
  let hashes ← (txs.mapM wireHash).mapError .rlp
  if hashes.isSublist requested then pure () else throw .notRequested

end EthLib.Execution.Network

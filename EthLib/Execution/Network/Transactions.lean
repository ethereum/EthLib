module

public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Network.Protocol
public import EthLib.Serialization.Rlp.Decode
public import EthLib.Serialization.Rlp.Codec

/-!
# `Execution.Network.Transactions`

The transaction exchange of the eth capability, from Protocol Messages in [`caps/eth.md`][eth].

[eth]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/caps/eth.md#protocol-messages
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The message ID of Transactions, which sends whole transactions. -/
def TRANSACTIONS_ID : Nat := 0x02

/-- The message ID of NewPooledTransactionHashes, which announces transactions. -/
def NEW_POOLED_TRANSACTION_HASHES_ID : Nat := 0x08

/-- The message ID of GetPooledTransactions, which asks for transactions by hash. -/
def GET_POOLED_TRANSACTIONS_ID : Nat := 0x09

/-- The message ID of PooledTransactions, which answers GetPooledTransactions. -/
def POOLED_TRANSACTIONS_ID : Nat := 0x0a

/-- An announcement of transactions: one type, one size and one hash for each transaction. -/
inductive Announcement where
  /-- eth/68 to eth/71: `[txtypes, [txsize, ...], [txhash, ...]]`, three lists of equal length.

  [EIP-5793](https://eips.ethereum.org/EIPS/eip-5793#specification) sets the three lists. -/
  | eth68 (types : ByteArray) (sizes : List Nat) (hashes : List Hash32)
  /-- eth/72: the three lists, then a 16-byte bitmap of the cells that the peer holds.

  The bitmap is 16 bytes even when no blob transaction is announced, by [EIP-8070][eip-8070].

  The recipient may then ignore it.

  [eip-8070]: https://eips.ethereum.org/EIPS/eip-8070#specification -/
  | eth72 (types : ByteArray) (sizes : List Nat) (hashes : List Hash32)
      (cells : Vector UInt8 16)
  deriving DecidableEq

namespace Announcement

/-- The announcement as an RLP list, in the field order of its version. -/
def toItem : Announcement → Item
  -- EIP-5793: `[types: B, [size_0: P, size_1: P, ...], [hash_0: B_32, hash_1: B_32, ...]]`.
  | eth68 t s h => .list [Codec.toItem t, Codec.toItem s, Codec.toItem h]
  -- EIP-8070: then `cell_mask: B_16`.
  | eth72 t s h c => .list [Codec.toItem t, Codec.toItem s, Codec.toItem h, Codec.toItem c]

/-- The types, the sizes and the hashes of an announcement. -/
def lists : Announcement → ByteArray × List Nat × List Hash32
  | eth68 t s h | eth72 t s h _ => (t, s, h)

/-- Whether an announcement has as many types and sizes as hashes. -/
def lengthsAgree (a : Announcement) : Bool :=
  -- NewPooledTransactionHashes of eth.md: the three lists have an equal number of items.
  let (t, s, h) := a.lists
  t.size == h.length && s.length == h.length

/-- The announcement of a version in an RLP list, without the check of the list lengths.

The reader of messages checks that the three lists have equal lengths. -/
def ofItem (version : EthVersion) (item : Item) : Except RlpError Announcement := do
  -- Before eth/72, the three lists of EIP-5793.
  if version < .eth72 then
    match ← item.fields 3 with
    | [t, s, h] => return eth68 (← t.field 0) (← s.field 1) (← h.field 2)
    | items => throw (.wrongFieldCount 3 items.length)
  -- From eth/72, `cell_mask: B_16` comes fourth, by EIP-8070.
  else
    match ← item.fields 4 with
    | [t, s, h, c] => return eth72 (← t.field 0) (← s.field 1) (← h.field 2) (← c.field 3)
    | items => throw (.wrongFieldCount 4 items.length)

end Announcement

/-- The transaction type of a blob transaction, from EIP-4844. -/
def BLOB_TX_TYPE : UInt8 := 0x03

/--
The hash of a transaction as it crosses the wire, from its item and the bytes it was read from.

A legacy transaction hashes its RLP list, and a typed one its bytes `tx-type || tx-data`.

A blob transaction in PooledTransactions can come in its network form, as [EIP-4844][eip-4844] says.

That form is the type 3 followed by `rlp([tx_payload_body, ...])`.

Its hash is the hash of `0x03 || rlp(tx_payload_body)`, the transaction without its blobs.

The payload of a canonical blob transaction starts with the chain ID, a scalar.

The network form starts with the body, a list.

So the first item tells the two apart.

Each encoding hashed is a slice of the bytes read, so nothing is encoded again.

[eip-4844]: https://eips.ethereum.org/EIPS/eip-4844#networking
-/
def wireHash (tx : Encoded) : Hash32 :=
  -- Each encoding hashed is a slice of the bytes read, so nothing is encoded again.
  match tx.item with
  -- EIP-2976: a legacy transaction crosses as an RLP list.
  --
  -- It hashes as `keccak256(rlp(LegacyTransaction))`.
  | .list _ => Cryptography.Hash.Keccak.keccak256 tx.bytes
  | .bytes b =>
    -- EIP-2976: a typed transaction crosses as the byte string `tx-type || tx-data`.
    --
    -- It hashes as `keccak256(TypedTransaction)`.
    --
    -- That is the bytes `TransactionType || TransactionPayload`.
    let canonical := Cryptography.Hash.Keccak.keccak256 b
    match b.data.toList with
    | type :: rest =>
      -- EIP-4844: in PooledTransactions, a blob transaction can come in its network form.
      --
      -- That form is the type 3, then an RLP list: payload body, blobs, commitments, proofs.
      --
      -- So the hash is over the type `0x03` and the RLP of the payload body, without the blobs.
      if type = BLOB_TX_TYPE then
        let form : ByteArray := ⟨rest.toArray⟩
        -- The body is the first item of the network form, and its bytes are the first encoding.
        --
        -- A canonical payload starts with the chain ID, a scalar.
        --
        -- The network form starts with the body, a list, so the first item tells the two apart.
        match Serialization.Rlp.decode form, listEncodings form with
        | .ok (.list (.list _ :: _)), .ok (body :: _) =>
          Cryptography.Hash.Keccak.keccak256 (⟨#[BLOB_TX_TYPE]⟩ ++ body)
        | _, _ => canonical
      else canonical
    | [] => canonical

/-- Why the transactions of a PooledTransactions do not answer a GetPooledTransactions. -/
inductive PoolError where
  /-- The hashes of the transactions are not a sublist of the requested hashes.

  A sublist keeps the order of the request, and may leave some hashes out. -/
  | notRequested
  /-- The response is not PooledTransactions with the request ID of the request. -/
  | notAnswer
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 302, after the header errors at 201.

Code 301 stays unused, so that no code takes another meaning.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PoolError.code : PoolError → UInt32
  | .notRequested => 302
  | .notAnswer => 303

/--
Whether the transactions `txs` answer a request of the hashes `requested`.

The transactions must be in the order of the request.

The peer may leave some out, as the section PooledTransactions (0x0a) says.

So their hashes form a sublist of the requested hashes.
-/
def checkPooled (requested : List Hash32) (txs : List Encoded) : Except PoolError Unit :=
  -- PooledTransactions: the order of the request, with some transactions left out.
  if (txs.map wireHash).isSublist requested then pure () else throw .notRequested

end EthLib.Execution.Network

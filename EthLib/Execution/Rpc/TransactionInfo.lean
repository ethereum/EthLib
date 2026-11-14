module

public import EthLib.Execution.Rpc.Transaction
public import EthLib.Execution.Rpc.View
public import EthLib.Execution.Transactions.Envelope
public import EthLib.Execution.Transactions.Signature

/-!
# `Execution.Rpc.TransactionInfo`

A transaction of a block that the node holds, as the methods that look one up return it.

It is the object `TransactionInfo` of [`transaction.yaml`][tx].

It has the signed fields of the transaction and the context of its block.

That context is the hash, number and timestamp of the block, and the index of the transaction.

It also has the sender that the signature names and the hash of the transaction.

Its gas price is the effective gas price: what the sender pays per gas at the base fee of the block.

A block before London has no base fee, and its transactions pay their own gas price.

A lookup by hash reads the canonical blocks first, then the other blocks that the node holds.

The schema of the methods does not say which block to read when a transaction is in several.

It does not read the transactions that wait in the pool: the result schema requires a block hash.

A lookup by block and index finds no transaction when the block is unknown or too short.

[tx]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/transaction.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Transactions

/-- A transaction of a block, with its sender, its hash, and what it pays per gas. -/
structure TransactionInfo where
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The number of the block. -/
  blockNumber : Nat
  /-- The timestamp of the block. -/
  blockTimestamp : Nat
  /-- The index of the transaction in the block, from 0. -/
  index : Nat
  /-- The sender that the signature names. -/
  sender : Address
  /-- The hash of the transaction. -/
  hash : Hash32
  /-- The effective gas price: what the sender pays per gas in the block. -/
  gasPrice : Nat
  /-- The transaction. -/
  tx : Transaction

/-- The object of a transaction of a block as JSON. -/
def transactionInfoJson (info : TransactionInfo) : Json :=
  Json.mkObj ([("blockHash", dataJson info.blockHash.toList),
    ("blockNumber", quantityJson info.blockNumber),
    ("blockTimestamp", quantityJson info.blockTimestamp),
    ("from", dataJson info.sender.toList), ("hash", dataJson info.hash.toList),
    ("transactionIndex", quantityJson info.index)] ++ transactionFields info.gasPrice info.tx)

/-- The base fee per gas of a block, or 0 before London, which has no base fee. -/
def BlockRecord.baseFee (r : BlockRecord) : Nat :=
  if h : .london ≤ r.fork then r.block.header.baseFeePerGas h else 0

/-- The object of the transaction at an index of a block.

It fails when the signature names no sender or the transaction has no hash. -/
def BlockRecord.transactionInfo (r : BlockRecord) (index : Nat) (tx : Transaction) :
    Except RpcError TransactionInfo := do
  let sender ← (recoverSender r.fork tx).mapError fun _ =>
    internalError.toRpcError (some (.str "transaction sender: the sender is not recovered"))
  let hash ← (transactionHash tx).mapError fun _ =>
    internalError.toRpcError (some (.str "transaction hash: the transaction has no RLP encoding"))
  return { blockHash := r.hash, blockNumber := r.block.header.number
           blockTimestamp := r.block.header.timestamp.toNat, index, sender, hash
           gasPrice := effectiveGasPrice r.baseFee tx, tx }

/-- Whether a transaction has a hash, and that hash is the given one. -/
def hasHash (hash : Hash32) (tx : Transaction) : Bool :=
  match transactionHash tx with
  | .ok h => h == hash
  | .error _ => false

/-- The first transaction of a block whose hash is the given one, with its index. -/
def BlockRecord.findTransaction (r : BlockRecord) (hash : Hash32) : Option (Transaction × Nat) :=
  r.block.transactions.zipIdx.find? fun (tx, _) => hasHash hash tx

namespace ChainView

/-- The first transaction of a given hash in the blocks of the node, canonical blocks first.

It comes with its block and its index. -/
def findTransaction (v : ChainView) (hash : Hash32) : Option (BlockRecord × Transaction × Nat) :=
  (v.canonical ++ v.side).findSome? fun r => (r.findTransaction hash).map fun p => (r, p)

/-- The object of the transaction with a hash, or none when no block of the node holds one. -/
def transactionByHash (v : ChainView) (hash : Hash32) :
    Except RpcError (Option TransactionInfo) :=
  match v.findTransaction hash with
  | none => .ok none
  | some (r, tx, index) => some <$> r.transactionInfo index tx

/-- The object of the transaction at an index of the block that a parameter names, if any. -/
def transactionByBlockAndIndex (v : ChainView) (p : BlockParam) (index : Nat) :
    Except RpcError (Option TransactionInfo) := do
  match ← v.resolve p with
  | none => return none
  | some r =>
    match r.block.transactions[index]? with
    | none => return none
    | some tx => some <$> r.transactionInfo index tx

end ChainView

end EthLib.Execution.Rpc

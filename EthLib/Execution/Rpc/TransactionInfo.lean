module

public import EthLib.Execution.Rpc.Transaction
public import EthLib.Execution.Rpc.View
public import EthLib.Execution.Transactions.Envelope
public import EthLib.Execution.Transactions.Signature

/-!
# `Execution.Rpc.TransactionInfo`

A transaction of a block that the node holds, as the methods that look one up return it.

Sources:

- [`transaction.yaml`][tx], at commit `1ca0818` of execution-apis: the fields of `TransactionInfo`
- the upstream report [execution-apis#1008][canonical]: the canonical blocks for a lookup by hash

[tx]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/transaction.yaml
[canonical]: https://github.com/ethereum/execution-apis/pull/1008
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Transactions

/-- A transaction of a block, with its sender, its hash, and what it pays per gas.

It has the signed fields of the transaction and the context of its block.

That context is the hash, number and timestamp of the block, and the index of the transaction.

It also has the sender that the signature names and the hash of the transaction. -/
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
  /-- The effective gas price: what the sender pays per gas at the base fee of the block.

  A block before London has no base fee, and its transactions pay their own gas price. -/
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

/-- The first transaction of a given hash in the canonical blocks, with its block and its index.

A block off the canonical chain is not read. -/
def findTransaction (v : ChainView) (hash : Hash32) : Option (BlockRecord × Transaction × Nat) :=
  v.canonical.findSome? fun r => (r.findTransaction hash).map fun p => (r, p)

/-- The object of the transaction with a hash, or none when no canonical block holds one.

So a transaction that only a block off the canonical chain holds, as after a reorg, is not found.

The method text does not say which blocks to read.

The upstream report execution-apis#1008 proposes to state this rule there.

The lookup does not read the transactions that wait in the pool.

The result schema requires a block hash, which such a transaction lacks. -/
def transactionByHash (v : ChainView) (hash : Hash32) :
    Except RpcError (Option TransactionInfo) :=
  match v.findTransaction hash with
  | none => .ok none
  | some (r, tx, index) => some <$> r.transactionInfo index tx

/-- The object of the transaction at an index of the block that a parameter names, if any.

The lookup finds no transaction when the block is unknown or too short. -/
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

module

public import EthLib.Execution.Rpc.Header
public import EthLib.Execution.Rpc.Json
public import EthLib.Execution.Rpc.Raw

/-!
# `Execution.Rpc.Block`

A block that the node holds as JSON: the object `Block` of [`block.yaml`][schema].

The object holds the fields of the header object and the fields of the block.

Only the header methods say that a field from a fork MUST be omitted before it.

The block object follows the same rule, as the fixtures of the block methods do.

[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

/-- The fields of a block object after those of its header.

They are its size, the hashes of its ommers, its transactions, and its withdrawals from Shapella. -/
def blockFields {fork : Fork} (size : Nat) (uncles : List Hash32) (transactions : Json)
    (withdrawals : Since .shapella fork (List Withdrawal)) : List (String × Json) :=
  -- The size, the hashes of the ommers, the transactions, then the withdrawals from Shapella.
  [("size", quantityJson size), ("uncles", listJson hash32Json uncles),
    ("transactions", transactions)] ++
    sinceField "withdrawals" (listJson withdrawalJson) withdrawals

/-- The names of the fields of a block object after those of its header, at a fork. -/
def blockNames (fork : Fork) : List String :=
  ["size", "uncles", "transactions"] ++ sinceName .shapella fork "withdrawals"

namespace BlockRecord

/-- The hashes of the transactions of a block, in order. -/
def transactionHashes (r : BlockRecord) : Except RpcError (List Hash32) :=
  r.block.transactions.mapM fun tx =>
    (transactionHash tx).mapError fun _ => encodingError "transaction hash"

/-- The objects of the transactions of a block, in order. -/
def transactionInfos (r : BlockRecord) : Except RpcError (List TransactionInfo) :=
  r.block.transactions.zipIdx.mapM fun (tx, index) => r.transactionInfo index tx

/-- The length of the RLP form of a block, in bytes. -/
def size (r : BlockRecord) : Except RpcError Nat :=
  -- The schema gives the size only a title, and the fixtures pin this length.
  (·.size) <$> r.rawBlock

/-- The block object of a block, with the objects of its transactions when they are hydrated.

It fails when the node cannot compute the RLP form of the block, a hash or a sender in it. -/
def blockJson (r : BlockRecord) (full : Bool) : Except RpcError Json := do
  let size ← r.size
  -- The hash of the header of each ommer.
  let uncles ← r.block.ommers.mapM fun o => o.2.hash.mapError fun _ => encodingError "ommer hash"
  -- The objects of the transactions when asked for, else their hashes.
  let transactions ← if full then listJson transactionInfoJson <$> r.transactionInfos
    else listJson hash32Json <$> r.transactionHashes
  -- The header object, with the hash that the node keeps for the block.
  --
  -- It always writes the difficulty, as the fixtures do, though the schema does not require it.
  return Json.mkObj (headerFields r.hash r.block.header ++
    blockFields size uncles transactions r.block.withdrawals)

end BlockRecord

end EthLib.Execution.Rpc

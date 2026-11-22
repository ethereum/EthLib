module

public import EthLib.Execution.Rpc.Header
public import EthLib.Execution.Rpc.Raw
public import EthLib.Execution.Evm.Call.ContractAddress

/-!
# `Execution.Rpc.Receipt`

The receipt of a transaction of a block, as the receipt methods return it.

It is the object `ReceiptInfo` of [`receipt.yaml`][receipt], with its logs as objects `Log`.

It adds to the receipt of the block the values that the node computes from the block.

From Glamsterdam, [EIP-7778][eip-7778] counts the gas of a block before the refunds.

The receipts count apart the gas that the senders paid, by [EIP-8037][eip-8037].

So the gas of a transaction is then the gas that its sender paid.

The schema still describes both gas fields as the gas used.

The position of a log in its block is defined only by the notes of [`eth_simulateV1`][simulate].

Their section on the log index adds that receipts use the same numbering.

[receipt]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/receipt.yaml
[eip-7778]: https://eips.ethereum.org/EIPS/eip-7778#specification
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#receipt-semantics
[simulate]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/docs-api/docs/ethsimulatev1-notes.mdx
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

/-- A log of a block that the node holds, with its place in the block. -/
structure LogInfo where
  /-- The log. -/
  log : Log
  /-- The position of the log among all the logs of its block, from 0. -/
  logIndex : Nat
  /-- The index of the transaction that wrote it. -/
  transactionIndex : Nat
  /-- The hash of that transaction. -/
  transactionHash : Hash32
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The number of the block. -/
  blockNumber : Nat
  /-- The timestamp of the block. -/
  blockTimestamp : Nat

/-- The object of a log as JSON, which a node never reports as removed. -/
def logInfoJson (l : LogInfo) : Json :=
  -- Every field, as the fixtures write them, though the schema requires only the transaction hash.
  --
  -- Only the text of subscriptions explains removal, for reorgs.
  --
  -- A log of a block that the node holds is not removed, so false, as the fixtures show.
  Json.mkObj [("address", dataJson l.log.address.toList),
    ("topics", listJson hash32Json l.log.topics), ("data", dataJson l.log.data.toList),
    ("blockNumber", quantityJson l.blockNumber), ("transactionHash", hash32Json l.transactionHash),
    ("transactionIndex", quantityJson l.transactionIndex), ("blockHash", hash32Json l.blockHash),
    ("blockTimestamp", quantityJson l.blockTimestamp), ("logIndex", quantityJson l.logIndex),
    ("removed", .bool false)]

/-- The outcome of a transaction: the state root after it, or whether it succeeded. -/
def outcomeOf {fork : Fork} : Outcome fork → Hash32 ⊕ Bool
  | .postState _ root => .inl root
  | .status _ succeeded => .inr succeeded

/-- The field of an outcome: `root` for a state root, `status` `0x1` or `0x0` for a status. -/
def outcomeFields : Hash32 ⊕ Bool → List (String × Json)
  -- The schema, before Byzantium: the state root after the transaction.
  | .inl root => [("root", hash32Json root)]
  -- The schema, from Byzantium: the status, 1 for a success and 0 for a failure.
  | .inr succeeded => [("status", quantityJson (if succeeded then 1 else 0))]

/-- A receipt of a transaction of a block, with the values that the node computes for it. -/
structure ReceiptInfo where
  /-- The type of the transaction. -/
  type : UInt8
  /-- The hash of the transaction. -/
  transactionHash : Hash32
  /-- The index of the transaction in the block, from 0. -/
  transactionIndex : Nat
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The number of the block. -/
  blockNumber : Nat
  /-- The sender that the signature names. -/
  sender : Address
  /-- The recipient, or none for a creation. -/
  to : Option Address
  /-- The cumulative gas of the receipt. -/
  cumulativeGasUsed : Nat
  /-- The gas of the transaction alone. -/
  gasUsed : Nat
  /-- The address that a creation makes, or none. -/
  contractAddress : Option Address
  /-- The logs of the transaction, with their places. -/
  logs : List LogInfo
  /-- The Bloom filter of the receipt. -/
  logsBloom : Bytes256
  /-- The outcome of the transaction: a state root before Byzantium, a status from it. -/
  outcome : Hash32 ⊕ Bool
  /-- What the sender pays per gas. -/
  effectiveGasPrice : Nat
  /-- The blob gas of a blob transaction and its price per blob gas, or none for other types. -/
  blob : Option (Nat × Nat)

/-- The object of a receipt as JSON. -/
def receiptInfoJson (r : ReceiptInfo) : Json :=
  -- Every field of the fork and the type, as the fixtures write them.
  --
  -- The schema requires ten, and leaves the type, the recipient and the created address optional.
  --
  -- It also leaves the root, the status and the blob fields optional.
  Json.mkObj ([("type", byteJson r.type), ("transactionHash", hash32Json r.transactionHash),
    ("transactionIndex", quantityJson r.transactionIndex), ("blockHash", hash32Json r.blockHash),
    ("blockNumber", quantityJson r.blockNumber), ("from", dataJson r.sender.toList),
    ("to", optionJson (fun (a : Address) => dataJson a.toList) r.to),
    ("cumulativeGasUsed", quantityJson r.cumulativeGasUsed), ("gasUsed", quantityJson r.gasUsed),
    ("contractAddress", optionJson (fun (a : Address) => dataJson a.toList) r.contractAddress),
    ("logs", listJson logInfoJson r.logs), ("logsBloom", dataJson r.logsBloom.toList),
    ("effectiveGasPrice", quantityJson r.effectiveGasPrice)] ++ outcomeFields r.outcome ++
    match r.blob with
    -- The blob gas and its price, for a blob transaction only.
    | some (used, price) =>
      [("blobGasUsed", quantityJson used), ("blobGasPrice", quantityJson price)]
    | none => [])

namespace BlockRecord

/-- The price per blob gas of a block, on a chain, or 0 before Dencun. -/
def blobGasPrice (r : BlockRecord) (config : ChainConfig) : Nat :=
  -- EIP-4844: the blob base fee, the fake exponential of the excess blob gas of the block.
  blobGasPriceOf (blockEnvironment config [] r.block.header)

/-- The log objects of the transaction at `index` of a block, with the hash `hash`.

The logs before them in the block number `firstLog`. -/
def logInfos (r : BlockRecord) (index firstLog : Nat) (hash : Hash32) (logs : List Log) :
    List LogInfo :=
  -- Log i of the transaction follows the logs before it in the block, numbered from 0.
  logs.zipIdx.map fun (log, i) =>
    { log, logIndex := firstLog + i, transactionIndex := index, transactionHash := hash
      blockHash := r.hash, blockNumber := r.block.header.number
      blockTimestamp := r.block.header.timestamp.toNat }

/-- The receipt object of the transaction at an index of a block.

The receipts before it used `before` gas, and wrote `firstLog` logs. -/
def receiptInfo (r : BlockRecord) (config : ChainConfig) (index before firstLog : Nat)
    (tx : Transaction) (receipt : Receipt r.fork) : Except RpcError ReceiptInfo := do
  -- The hash, the sender and the price per gas of the transaction.
  let info ← r.transactionInfo index tx
  -- Yellow Paper §7: a creation makes `B_{96..255}(KEC(RLP((s, n))))`, of sender `s` and nonce `n`.
  let contractAddress ← match tx.to with
    | some _ => pure none
    | none => some <$> (Evm.createAddress info.sender tx.nonce.toNat).mapError fun _ =>
        encodingError "contract address"
  let logs := r.logInfos index firstLog info.hash receipt.logs
  -- EIP-4844: a blob transaction uses `2^17` blob gas per blob, at the price of the block.
  let blob := match tx with
    | .blob _ =>
      some (Fees.BlobBaseFee.GAS_PER_BLOB * tx.blobHashes.length, r.blobGasPrice config)
    | _ => none
  -- The schema: the cumulative gas sums the gas of this and the earlier transactions.
  --
  -- So the gas of the transaction is its cumulative gas minus that of the receipt before.
  --
  -- The effective gas price is what the sender pays per gas, at the base fee of the block.
  return { type := tx.type, transactionHash := info.hash, transactionIndex := index
           blockHash := r.hash, blockNumber := r.block.header.number, sender := info.sender
           to := tx.to, cumulativeGasUsed := receipt.cumulativeGasUsed
           gasUsed := receipt.cumulativeGasUsed - before, contractAddress, logs
           logsBloom := receipt.bloom, outcome := outcomeOf receipt.outcome
           effectiveGasPrice := info.gasPrice, blob }

/-- The cumulative gas of the first `k` receipts of a block: that of the last of them, or 0. -/
def gasBefore (r : BlockRecord) (k : Nat) : Nat :=
  ((r.receipts.take k).map (·.2.cumulativeGasUsed)).getLast?.getD 0

/-- The number of logs of the first `k` receipts of a block. -/
def logsBefore (r : BlockRecord) (k : Nat) : Nat :=
  ((r.receipts.take k).map (·.2.logs.length)).sum

/-- The receipt objects of some transactions of a block, each with its receipt, from an index.

The receipts before them used `before` gas, and wrote `firstLog` logs. -/
def receiptInfosFrom (r : BlockRecord) (config : ChainConfig) :
    Nat → Nat → Nat → List (Transaction × Receipt r.fork) → Except RpcError (List ReceiptInfo)
  | _, _, _, [] => .ok []
  | index, before, firstLog, (tx, receipt) :: rest => do
    -- Each receipt, then the next with the cumulative gas and the logs counted so far.
    let info ← r.receiptInfo config index before firstLog tx receipt
    let infos ← r.receiptInfosFrom config (index + 1) receipt.cumulativeGasUsed
      (firstLog + receipt.logs.length) rest
    return info :: infos

/-- The receipt objects of the transactions of a block, in order.

It fails when the block does not have one receipt for each transaction. -/
def receiptInfos (r : BlockRecord) (config : ChainConfig) : Except RpcError (List ReceiptInfo) :=
  -- One receipt per transaction, else EthLib's choice of code -32603.
  if r.block.transactions.length = r.receipts.length then
    r.receiptInfosFrom config 0 0 0 (r.block.transactions.zip (r.receipts.map (·.2)))
  else .error (internalError.toRpcError (some (.str "receipts: not one per transaction")))

end BlockRecord

namespace ChainView

/-- The receipt objects of the block that a parameter names, or none when there is none. -/
def blockReceipts (v : ChainView) (p : BlockParam) :
    Except RpcError (Option (List ReceiptInfo)) := do
  match ← v.resolve p with
  -- The method: null for an unknown block.
  --
  -- The view holds every block it finds, so it never answers 4444, which the method allows.
  | none => return none
  | some r => some <$> r.receiptInfos v.config

/-- The receipt object of the transaction of a hash, or none when no canonical block has one.

It is the object at the index of the transaction among those of its block. -/
def transactionReceipt (v : ChainView) (hash : Hash32) : Except RpcError (Option ReceiptInfo) :=
  match v.findTransaction hash with
  -- The method gives null for an unknown transaction; EthLib also gives null for a side block only.
  --
  -- The view holds every block it finds, so it never answers 4444, which the method allows.
  | none => .ok none
  | some (r, _, index) => do
    let infos ← r.receiptInfos v.config
    return infos[index]?

end ChainView

end EthLib.Execution.Rpc

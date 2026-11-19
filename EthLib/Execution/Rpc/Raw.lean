module

public import EthLib.Execution.Rpc.TransactionInfo

/-!
# `Execution.Rpc.Raw`

The consensus encodings of the objects of a chain, which the raw getters return.

The getters are those of [`getters.yaml`][getters].

- The header of a block is its RLP form.
- A block is its RLP form, with each typed transaction as the byte string of its bytes.
- A transaction is its bytes of [EIP-2718][eip2718]: a legacy one is its RLP form.
- The receipts of a block are the bytes of each receipt, in order.

The summary of the transaction getter says that it returns an array of transactions.

Its result schema is one byte string, and the definition follows the schema.

No result schema of the getters allows `null`.

No text says which error an unknown block or transaction gets.

Here an unknown block or transaction gets `-32001`, "Resource not found".

The getter of a block access list in the same file says that an unknown block MUST get `-32001`.

The tag `pending` names the pending block of the view, and gets that error when there is none.

A block below the lowest block that the node holds is unknown, so it gets that error too.

Every getter also lists `4444` for pruned history, which the view never answers.

An encoding fails only when a byte string or a list has a payload of `2^64` bytes or more.

The getter then fails with `-32603`.

[getters]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/debug/getters.yaml
[eip2718]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-2718.md
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc (RpcError)
open EthLib.Serialization.Rlp (Codec)
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

namespace BlockRecord

/-- The error of a value of a block that the node cannot compute. -/
def encodingError (what : String) : RpcError :=
  internalError.toRpcError (some (.str s!"{what}: cannot be encoded"))

/-- The RLP form of the header of a block. -/
def rawHeader (r : BlockRecord) : Except RpcError ByteArray :=
  (Codec.encode r.block.header).mapError fun _ => encodingError "header"

/-- The RLP form of a block, with each typed transaction as the byte string of its bytes. -/
def rawBlock (r : BlockRecord) : Except RpcError ByteArray := do
  let block ← (bodyItems r.block).mapError fun _ => encodingError "block"
  block.encode.mapError fun _ => encodingError "block"

/-- The bytes of the receipts of a block, in order, each at the type of its transaction. -/
def rawReceipts (r : BlockRecord) : Except RpcError (List ByteArray) :=
  r.receipts.mapM fun (type, receipt) =>
    (encodeReceipt type receipt).mapError fun _ => encodingError "receipt"

end BlockRecord

namespace ChainView

/-- The error of a block or a transaction that the node does not hold. -/
def unknown (what : String) : RpcError :=
  resourceNotFound.toRpcError (some (.str s!"unknown {what}"))

/-- A value of the block that a parameter names, or the error of an unknown block. -/
def ofBlock {α : Type} (v : ChainView) (p : BlockParam) (f : BlockRecord → Except RpcError α) :
    Except RpcError α := do
  match ← v.resolve p with
  | none => throw (unknown "block")
  | some r => f r

/-- The RLP form of the header of the block that a parameter names. -/
def rawHeader (v : ChainView) (p : BlockParam) : Except RpcError ByteArray :=
  v.ofBlock p BlockRecord.rawHeader

/-- The RLP form of the block that a parameter names. -/
def rawBlock (v : ChainView) (p : BlockParam) : Except RpcError ByteArray :=
  v.ofBlock p BlockRecord.rawBlock

/-- The bytes of the receipts of the block that a parameter names, in order. -/
def rawReceipts (v : ChainView) (p : BlockParam) : Except RpcError (List ByteArray) :=
  v.ofBlock p BlockRecord.rawReceipts

/-- The bytes of the transaction of a hash, from the first block of the node that holds one.

The canonical blocks come first, then the blocks off the canonical chain. -/
def rawTransaction (v : ChainView) (hash : Hash32) : Except RpcError ByteArray :=
  match v.findTransaction hash with
  | none => .error (unknown "transaction")
  | some (_, tx, _) =>
    (encodeTransaction tx).mapError fun _ => BlockRecord.encodingError "transaction"

end ChainView

end EthLib.Execution.Rpc

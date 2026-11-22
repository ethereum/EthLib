module

public import EthLib.Execution.Rpc.TransactionInfo

/-!
# `Execution.Rpc.Raw`

The consensus encodings of the objects of a chain, which the raw getters return.

The getters are those of [`getters.yaml`][getters].

A transaction is its bytes of [EIP-2718][eip2718]: a legacy one is its RLP form.

No result schema of the getters allows null.

Only the getter of a block access list names the error of an unknown block: -32001.

Every getter also lists 4444 for pruned history, which the view never answers.

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
  -- EthLib's choice: code -32603, for RLP fails only on a payload of `2^64` bytes or more.
  internalError.toRpcError (some (.str s!"{what}: cannot be encoded"))

/-- The RLP form of the header of a block. -/
def rawHeader (r : BlockRecord) : Except RpcError ByteArray :=
  (Codec.encode r.block.header).mapError fun _ => encodingError "header"

/-- The RLP form of a block, with each typed transaction as the byte string of its bytes. -/
def rawBlock (r : BlockRecord) : Except RpcError ByteArray := do
  -- EIP-2718: each typed transaction is the byte string of its bytes in the RLP form of the block.
  let block ← (bodyItems r.block).mapError fun _ => encodingError "block"
  block.encode.mapError fun _ => encodingError "block"

/-- The bytes of the receipts of a block, in order, each at the type of its transaction. -/
def rawReceipts (r : BlockRecord) : Except RpcError (List ByteArray) :=
  -- EIP-2718: a typed receipt is its type byte, then its payload; a legacy one is its RLP.
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
  -- An unknown block, a block below the lowest one, or no pending block: code -32001.
  --
  -- The source requires that code of the getter of a block access list.
  --
  -- EIP-1898 recommends it for a block not found, and EthLib gives it for every getter.
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

/-- The bytes of the transaction of a hash, from the first canonical block that holds one. -/
def rawTransaction (v : ChainView) (hash : Hash32) : Except RpcError ByteArray :=
  match v.findTransaction hash with
  -- An unknown transaction: code -32001, EthLib's choice.
  | none => .error (unknown "transaction")
  -- One byte string, as the result schema says, though the summary names an array.
  | some (_, tx, _) =>
    (encodeTransaction tx).mapError fun _ => BlockRecord.encodingError "transaction"

end ChainView

end EthLib.Execution.Rpc

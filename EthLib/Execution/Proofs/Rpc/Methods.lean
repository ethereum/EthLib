module

public import EthLib.Execution.Rpc.Methods

/-!
# Proofs: the methods of the chain view

A notification gets no response, as section 4.1 of JSON-RPC 2.0 requires.

A request of a method that the view does not serve gets the error of a method not found.

The header of the tag `pending` is `null`, and any other block parameter gives its block's header.

In a valid view, the header object of a block is what the writer of headers writes for it.

So the reader of headers reads it back, and its names are those of the fork of the block.
-/

public section

namespace EthLib.Execution.Rpc.ChainView

open Lean (Json)
open EthLib.Serialization.JsonRpc (optionJson RpcError)

/-- A notification gets no response. -/
theorem answerJson_notification (v : ChainView) {j : Json} (h : isNotification j = true) :
    v.answerJson j = none := by
  simp [answerJson, h]

/-- A request of a method that the view does not serve fails with the code of a method not found. -/
theorem call_unknown (v : ChainView) {method : String} (params : List Json)
    (h : method ∉ ["eth_blockNumber", "eth_chainId", "eth_config", "net_version",
      "eth_getTransactionByHash",
      "eth_getTransactionByBlockHashAndIndex", "eth_getTransactionByBlockNumberAndIndex",
      "eth_getHeaderByHash", "eth_getHeaderByNumber", "eth_getBlockByHash", "eth_getBlockByNumber",
      "eth_getBlockTransactionCountByHash", "eth_getBlockTransactionCountByNumber",
      "eth_getTransactionReceipt", "eth_getBlockReceipts", "eth_getLogs", "eth_getBalance",
      "eth_getTransactionCount", "eth_getCode", "eth_getStorageAt", "eth_getStorageValues",
      "eth_getProof", "eth_call", "eth_estimateGas", "eth_createAccessList",
      "eth_feeHistory", "eth_baseFee", "eth_sendRawTransaction", "debug_getRawHeader",
      "debug_getRawBlock", "debug_getRawTransaction", "debug_getRawReceipts",
      "eth_getBlockAccessList", "debug_getRawBlockAccessList", "eth_simulateV1"]) :
    v.call method params = .error (methodNotFound.toRpcError (some (.str method))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold call
  split <;> simp_all

/-- The header of the tag `pending` is `null`. -/
theorem headerByNumber_pending (v : ChainView) : v.headerByNumber (.tag .pending) = .ok .null :=
  rfl

/-- Any other block parameter gives the header object of the block that it resolves to.

It gives `null` for no block, and the error of the resolution when there is one. -/
theorem headerByNumber_of_ne {v : ChainView} {p : BlockParam} (hp : p ≠ .tag .pending) :
    v.headerByNumber p = optionJson headerObject <$> v.resolve p := by
  unfold headerByNumber
  split
  · exact absurd rfl hp
  · rfl

/-- The writer gives the header object of a block whose kept hash is that of its header. -/
theorem headerJson_eq_headerObject {r : BlockRecord} (h : r.block.header.hash = .ok r.hash) :
    headerJson r.block.header = .ok (headerObject r) := by
  simp only [headerJson, headerObject, h]
  rfl

/-- In a valid view, the header object of each block that the node holds is what the writer gives.

That holds for the canonical blocks, the other blocks and the pending block. -/
theorem Valid.headerJson_eq {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {r : BlockRecord} (hr : r ∈ v.canonical ++ v.side ∨ v.pending = some r) :
    headerJson r.block.header = .ok (headerObject r) := by
  rcases hr with hr | hr
  · exact headerJson_eq_headerObject (hv.hash r hr)
  · exact headerJson_eq_headerObject (hv.pending r hr).1

/-- A request that its reader rejects gets the code of invalid parameters, `-32602`. -/
theorem call_simulate_rejected (v : ChainView) {s : Json} {rest : List Json} {reason : String}
    (h : simulatePayload s = .error reason) :
    v.call "eth_simulateV1" (s :: rest) = .error (RpcError.invalidParams reason) := by
  simp [call, readParam, h, Except.mapError, bind, Except.bind]

end EthLib.Execution.Rpc.ChainView

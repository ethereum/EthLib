module

public import EthLib.Execution.Rpc.Methods

/-!
# Proofs: the methods of the chain view

A notification gets no response, as section 4.1 of JSON-RPC 2.0 requires.

A request of a method that the view does not serve gets the error of a method not found.
-/

public section

namespace EthLib.Execution.Rpc.ChainView

open Lean (Json)

/-- A notification gets no response. -/
theorem answerJson_notification (v : ChainView) {j : Json} (h : isNotification j = true) :
    v.answerJson j = none := by
  simp [answerJson, h]

/-- A request of a method that the view does not serve fails with the code of a method not found. -/
theorem call_unknown (v : ChainView) {method : String} (params : List Json)
    (h : method ∉ ["eth_blockNumber", "eth_chainId", "net_version"]) :
    v.call method params = .error (methodNotFound.toRpcError (some (.str method))) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold call
  split <;> simp_all

end EthLib.Execution.Rpc.ChainView

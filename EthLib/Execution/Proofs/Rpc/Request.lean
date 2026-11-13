module

public import EthLib.Execution.Rpc.Request
public import EthLib.Serialization.Proofs.JsonRpc
-- The members of an encoded object unfold the JSON object builder of Lean.
import all Lean.Data.Json.Basic

/-!
# Proofs: requests and responses

The readers of requests and responses read back what their writers write.

A request reads back with its parameters, whether it has any or not.

A response reads back with its result, even `null`, or with its error object.
-/

public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Serialization.JsonRpc

/-- The reader of identifiers reads back any identifier. -/
theorem requestId_requestIdJson (i : RequestId) : requestId (requestIdJson i) = .ok i := by
  cases i <;> rfl

/-- The reader of requests reads back any request. -/
theorem request_requestJson (r : Request) : request (requestJson r) = .ok r := by
  obtain ⟨id, method, params⟩ := r
  by_cases hp : params.isEmpty = true
  · obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (pairs :=
      [("jsonrpc", .str "2.0"), ("id", requestIdJson id), ("method", .str method)]) (by simp)
    have h : requestJson ⟨id, method, params⟩ = .obj kvs := by
      rw [requestJson]; simp only [hp, ite_true, List.append_nil]; exact hobj
    rw [h, request]
    have hall : (kvs.toList.all fun (k, _) =>
        k == "jsonrpc" || k == "id" || k == "method" || k == "params") = true := by
      simp only [List.all_eq_true]
      rintro ⟨k, v⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have h1 := lookup_of_mem hd ((hmem ("jsonrpc", Json.str "2.0")).mpr (by simp))
    have h2 := lookup_of_mem hd ((hmem ("id", requestIdJson id)).mpr (by simp))
    have h3 := lookup_of_mem hd ((hmem ("method", Json.str method)).mpr (by simp))
    have h4 : kvs.toList.lookup "params" = none := by
      rw [List.lookup_eq_none_iff]
      rintro ⟨k, v⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have hv : jsonrpcVersion kvs.toList = true := by simp [jsonrpcVersion, h1]
    have hpe : params = [] := List.isEmpty_iff.mp hp
    subst hpe
    simp [hall, hv, h2, h3, h4, field, string, requestId_requestIdJson, bind, Except.bind, pure,
      Except.pure]
  · obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (pairs :=
      [("jsonrpc", .str "2.0"), ("id", requestIdJson id), ("method", .str method),
        ("params", .arr params.toArray)]) (by simp)
    have h : requestJson ⟨id, method, params⟩ = .obj kvs := by
      rw [requestJson]; simp only [hp, Bool.false_eq_true, ite_false, List.cons_append,
        List.nil_append]
      exact hobj
    rw [h, request]
    have hall : (kvs.toList.all fun (k, _) =>
        k == "jsonrpc" || k == "id" || k == "method" || k == "params") = true := by
      simp only [List.all_eq_true]
      rintro ⟨k, v⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    have h1 := lookup_of_mem hd ((hmem ("jsonrpc", Json.str "2.0")).mpr (by simp))
    have h2 := lookup_of_mem hd ((hmem ("id", requestIdJson id)).mpr (by simp))
    have h3 := lookup_of_mem hd ((hmem ("method", Json.str method)).mpr (by simp))
    have h4 := lookup_of_mem hd ((hmem ("params", Json.arr params.toArray)).mpr (by simp))
    have hv : jsonrpcVersion kvs.toList = true := by simp [jsonrpcVersion, h1]
    simp [hall, hv, h2, h3, h4, field, string, requestId_requestIdJson, bind, Except.bind, pure,
      Except.pure]

/-- The reader of responses reads back any response. -/
theorem response_responseJson (r : Response) : response (responseJson r) = .ok r := by
  obtain ⟨id, outcome⟩ := r
  -- The two outcomes differ only in the name and value of the third member.
  have key : ∀ (name : String) (v : Json), (name = "result" ∨ name = "error") →
      response (Json.mkObj [("jsonrpc", .str "2.0"), ("id", requestIdJson id), (name, v)]) =
        match (if name = "result" then some v else none),
            (if name = "error" then some v else none) with
        | some result, none => .ok { id, outcome := .ok result }
        | none, some e => (rpcErrorOfJson e).bind fun e => .ok { id, outcome := .error e }
        | _, _ => .error "response: not exactly one of result and error" := by
    intro name v hname
    obtain ⟨kvs, hobj, hlen, hmem, hd⟩ := toList_mkObj (pairs :=
      [("jsonrpc", .str "2.0"), ("id", requestIdJson id), (name, v)])
      (by rcases hname with rfl | rfl <;> simp)
    rw [hobj, response]
    have h1 := lookup_of_mem hd ((hmem ("jsonrpc", Json.str "2.0")).mpr (by simp))
    have h2 := lookup_of_mem hd ((hmem ("id", requestIdJson id)).mpr (by simp))
    have h3 := lookup_of_mem hd ((hmem (name, v)).mpr (by simp))
    have hv : jsonrpcVersion kvs.toList = true := by simp [jsonrpcVersion, h1]
    have hnone : ∀ other : String, other ≠ "jsonrpc" → other ≠ "id" → other ≠ name →
        kvs.toList.lookup other = none := by
      intro other o1 o2 o3
      rw [List.lookup_eq_none_iff]
      rintro ⟨k, w⟩ hkv
      have := (hmem _).mp hkv
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at this
      rcases this with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp_all
    rcases hname with rfl | rfl
    · have hr := h3
      have he := hnone "error" (by decide) (by decide) (by decide)
      simp [hlen, hv, hr, he, h2, field, requestId_requestIdJson, bind, Except.bind, pure,
        Except.pure]
    · have hr := hnone "result" (by decide) (by decide) (by decide)
      have he := h3
      simp [hlen, hv, hr, he, h2, field, requestId_requestIdJson, bind, Except.bind, pure,
        Except.pure]
  cases outcome with
  | ok result =>
    rw [responseJson]
    exact (key "result" result (Or.inl rfl)).trans (by simp)
  | error e =>
    rw [responseJson]
    refine (key "error" (rpcErrorJson e) (Or.inr rfl)).trans ?_
    simp [rpcErrorOfJson_json]
    rfl

end EthLib.Execution.Rpc

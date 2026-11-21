module

public import EthLib.Engine.Json

/-!
# `Engine.GetInclusionList`

The method `engine_getInclusionListV1`, from Bogota.

A member of the inclusion list committee asks its execution layer for transactions.

The answer must keep two rules.

Each transaction has at least one byte.

The lengths of the transactions add up to at most 8192 bytes.

The source leaves the choice of the transactions to each node, from its view of the pool.

So the candidates, in the order that the node prefers, are an input here.

The method keeps each candidate in turn when the list still keeps both rules.

It drops an empty candidate, and one that would take the list past the bound.

Each candidate is taken to be a transaction of EIP-2718, which this method does not check.

The source also asks that the list should hold no blob transaction, which this method leaves out.

The method takes no parameter, and its answer is an array of byte strings.

[`bogota.md`][bogota] states the method and the bound, at commit `68d76a5` of execution-apis.

[bogota]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/engine/bogota.md#engine_getinclusionlistv1
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc

/-- The most bytes that the transactions of an inclusion list hold together: `2^13`. -/
def MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST : Nat := 2 ^ 13

/-- The transactions of an inclusion list, from candidates in the order that the node prefers.

Each candidate joins the list in turn when it is not empty and the list stays within the bound.

The bytes already taken start at `taken`. -/
def selectInclusionList (taken : Nat) : List ByteArray → List ByteArray
  | [] => []
  | tx :: rest =>
    if tx.size ≠ 0 ∧ taken + tx.size ≤ MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST then
      tx :: selectInclusionList (taken + tx.size) rest
    else selectInclusionList taken rest

/-- The parameters of the method: none, so an empty array. -/
def getInclusionListParams (params : Json) : Decode Unit := do
  match ← paramsArray params with
  | [] => pure ()
  | params => invalid s!"params: got {params.length}, expected 0"

/-- The answer of the method, from candidates in the order that the node prefers. -/
def getInclusionList (candidates : List ByteArray) (params : Json) :
    Decode (List ByteArray) := do
  getInclusionListParams params
  return selectInclusionList 0 candidates

end EthLib.Engine

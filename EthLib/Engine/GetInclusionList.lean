module

public import EthLib.Engine.Json

/-!
# `Engine.GetInclusionList`

The method `engine_getInclusionListV1`, from Bogota.

A member of the inclusion list committee asks its execution layer for transactions.

A step comment names a step of the specification of the method.

[`bogota.md`][bogota] states the method and the bound, at commit `68d76a5` of execution-apis.

[EIP-7805][eip-7805] sets the same bound of 8 KiB for an inclusion list, in IL Building.

[bogota]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/engine/bogota.md#engine_getinclusionlistv1
[eip-7805]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7805.md#il-building
-/

@[expose] public section

namespace EthLib.Engine

open Lean (Json)
open EthLib.Engine.Json
open EthLib.Serialization.JsonRpc

/-- The most bytes that the transactions of an inclusion list hold together: `2^13`. -/
def MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST : Nat :=
  -- The constant of `bogota.md`, `2^13 = 8192`, the bound that EIP-7805 states as 8 KiB.
  2 ^ 13

/-- The transactions of an inclusion list, from candidates in the order that the node prefers.

The bytes already taken start at `taken`. -/
def selectInclusionList (taken : Nat) : List ByteArray → List ByteArray
  | [] => []
  | tx :: rest =>
    -- Step 1.1: every transaction has non-zero length, at least 1 byte.
    --
    -- Step 1.3: the total byte length of the list does not exceed 8192 bytes.
    if tx.size ≠ 0 ∧ taken + tx.size ≤ MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST then
      tx :: selectInclusionList (taken + tx.size) rest
    -- EthLib drops an empty candidate, and one that would take the list past the bound.
    --
    -- It then tries the next candidate, so a shorter one later in the order may still join.
    else selectInclusionList taken rest

/-- The parameters of the method: none, so an empty array. -/
def getInclusionListParams (params : Json) : Decode Unit := do
  match ← paramsArray params with
  -- Request: the parameters are the empty array.
  | [] => pure ()
  -- The source names no error for a parameter, and EthLib gives `-32602`, invalid params.
  | params => invalid s!"params: got {params.length}, expected 0"

/-- The answer of the method, from candidates in the order that the node prefers. -/
def getInclusionList (candidates : List ByteArray) (params : Json) :
    Decode (List ByteArray) := do
  getInclusionListParams params
  -- Step 1: a list of transactions from the local view of the mempool of the node.
  --
  -- Step 2 leaves the strategy of selection to the node, so the candidates are an input here.
  --
  -- Response: an `Array of DATA`, each a transaction of EIP-2718.
  --
  -- EthLib takes each candidate to be one, and does not check it.
  --
  -- Step 1.2: the list should include no blob transaction, which EthLib leaves to the candidates.
  return selectInclusionList 0 candidates

end EthLib.Engine

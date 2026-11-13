module

public import EthLib.Serialization.JsonRpc
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Execution.Rpc.Json`

The JSON form of a withdrawal, as the JSON-RPC APIs exchange it.

A withdrawal is an object with exactly four fields.

They are its index, its validator index, its address and its amount.

The Engine API types the amount as a 64-bit number, in [WithdrawalV1][wv1].

The JSON-RPC schema [`Withdrawal`][wrpc] types it as a 256-bit number.

EthLib holds the amount in 64 bits, so one writer serves both APIs.

The reader keeps the 64-bit bound of the Engine API.

[wv1]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/shanghai.md#withdrawalv1
[wrpc]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/withdrawal.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (Withdrawal)

/-- A withdrawal, with exactly its four fields. -/
def withdrawal (j : Json) : Read Withdrawal := do
  let fs ← fields "withdrawal" j
  unless hasExactly fs ["index", "validatorIndex", "address", "amount"] do
    reject "withdrawal: wrong fields"
  return {
    index := ← uint64 "index" (← field "withdrawal" fs "index")
    validatorIndex := ← uint64 "validatorIndex" (← field "withdrawal" fs "validatorIndex")
    address := ← address "address" (← field "withdrawal" fs "address")
    amount := ← uint64 "amount" (← field "withdrawal" fs "amount") }

/-- A withdrawal as the JSON-RPC APIs write it. -/
def withdrawalJson (w : Withdrawal) : Json :=
  Json.mkObj [("index", quantityJson w.index.toNat),
    ("validatorIndex", quantityJson w.validatorIndex.toNat),
    ("address", dataJson w.address.toList), ("amount", quantityJson w.amount.toNat)]

end EthLib.Execution.Rpc

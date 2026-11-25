module

public import EthLib.Serialization.JsonRpc
public import EthLib.Execution.Blocks.Withdrawal
public import EthLib.Cryptography.Kzg.Types

/-!
# `Execution.Rpc.Json`

The JSON form of a withdrawal and of a versioned hash, as the JSON-RPC APIs exchange them.

Sources, at commit `1ca0818` of execution-apis:

- [WithdrawalV1][wv1] of the Engine API: the four fields, with a 64-bit amount
- the JSON-RPC schema [`Withdrawal`][wrpc]: the same fields, with a 256-bit amount
- the pattern of [`hash32`][types], which a versioned hash has in the [transaction][tx] schema
- the same pattern in the [Engine schema][payload] of the parameters of `engine_newPayload`

[wv1]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/shanghai.md#withdrawalv1
[wrpc]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/withdrawal.yaml
[types]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/base-types.yaml
[tx]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/transaction.yaml
[payload]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/engine/openrpc/methods/payload.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (Withdrawal)
open EthLib.Cryptography.Kzg (VersionedHash)

/-- A withdrawal, with exactly its four fields.

The reader keeps the 64-bit bound of the amount of the Engine API. -/
def withdrawal (j : Json) : Read Withdrawal := do
  let fs ← fields "withdrawal" j
  -- An object with exactly four fields: the index, the validator index, the address, the amount.
  unless hasExactly fs ["index", "validatorIndex", "address", "amount"] do
    reject "withdrawal: wrong fields"
  return {
    index := ← uint64 "index" (← field "withdrawal" fs "index")
    validatorIndex := ← uint64 "validatorIndex" (← field "withdrawal" fs "validatorIndex")
    address := ← address "address" (← field "withdrawal" fs "address")
    amount := ← uint64 "amount" (← field "withdrawal" fs "amount") }

/-- A withdrawal as the JSON-RPC APIs write it.

Every 64-bit number is below `2^256`, and both APIs write numbers alike, so one writer serves both.
-/
def withdrawalJson (w : Withdrawal) : Json :=
  Json.mkObj [("index", quantityJson w.index.toNat),
    ("validatorIndex", quantityJson w.validatorIndex.toNat),
    ("address", dataJson w.address.toList), ("amount", quantityJson w.amount.toNat)]

/-- A versioned hash of EIP-4844: exactly 32 bytes, in lowercase hex.

The version byte is not checked here. -/
def versionedHash (what : String) (j : Json) : Read VersionedHash :=
  -- `hash32`: `0x`, then 64 lowercase hex digits, as `^0x[0-9a-f]{64}$` asks.
  VersionedHash.mk <$> fixed what 32 j

/-- A versioned hash as JSON: `0x`, then its 32 bytes in lowercase hex. -/
def versionedHashJson (h : VersionedHash) : Json := dataJson h.bytes.toList

end EthLib.Execution.Rpc

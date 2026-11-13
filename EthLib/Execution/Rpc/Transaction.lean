module

public import EthLib.Execution.Rpc.Base
public import EthLib.Execution.Transactions.Settlement

/-!
# `Execution.Rpc.Transaction`

The JSON form of a signed transaction, as the schemas of [`transaction.yaml`][tx] give it.

Every kind has its type, its nonce, its gas, its value, its input and the two integers `r` and `s`.

A legacy transaction also has its recipient, its gas price and `v`.

Its chain is written when `v` carries one, as [EIP-155][eip155] puts it in `v`.

A typed transaction also has its recipient, its chain, its access list and the parity `yParity`.

It repeats the parity as `v`, a field that the schemas keep as optional and deprecated.

Outside a block, a transaction of type 2, 3 or 4 also has a gas price: its maximum fee per gas.

The schemas ask for that value outside a block, and keep the field as deprecated.

A creation has the recipient `null`.

The reader reads the fields of the kind that the type names, and ignores any other field.

So it also reads the object of a transaction of a block, which has more fields.

It takes the chain of a legacy transaction from `v`, and the parity of a typed one from `yParity`.

A transaction of type 2, 3 or 4 stores no gas price, so the reader drops that field.

Only type 2 still needs the field, which its schema requires.

An entry of an access list has exactly its address and its storage keys, as its schema says.

[tx]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/transaction.yaml
[eip155]: https://eips.ethereum.org/EIPS/eip-155#specification
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Transactions

/-- An entry of an access list as JSON: its address and its storage keys. -/
def accessJson (a : Access) : Json :=
  Json.mkObj [("address", dataJson a.account.toList),
    ("storageKeys", listJson (fun (k : Bytes32) => dataJson k.toList) a.slots)]

/-- An entry of an access list, with exactly its address and its storage keys. -/
def access (j : Json) : Read Access := do
  let fs ← fields "access list entry" j
  unless hasExactly fs ["address", "storageKeys"] do reject "access list entry: wrong fields"
  return {
    account := ← address "address" (← field "access list entry" fs "address")
    slots := ← array "storageKeys" (bytes32 "storage key")
      (← field "access list entry" fs "storageKeys") }

/-- An authorization as JSON: its chain, its nonce, its address and its signature. -/
def authorizationJson (a : Authorization) : Json :=
  Json.mkObj [("chainId", quantityJson a.chainId.toNat), ("nonce", quantityJson a.nonce.toNat),
    ("address", dataJson a.address.toList), ("yParity", byteJson a.yParity),
    ("r", quantityJson a.r.toNat), ("s", quantityJson a.s.toNat)]

/-- An authorization: its chain, its nonce, its address and its signature. -/
def authorization (j : Json) : Read Authorization := do
  let fs ← fields "authorization" j
  return {
    chainId := ← uint256 "chainId" (← field "authorization" fs "chainId")
    nonce := ← uint64 "nonce" (← field "authorization" fs "nonce")
    address := ← address "address" (← field "authorization" fs "address")
    yParity := ← byte "yParity" (← field "authorization" fs "yParity")
    r := ← uint256 "r" (← field "authorization" fs "r")
    s := ← uint256 "s" (← field "authorization" fs "s") }

/-- An access list as JSON. -/
def accessListJson (l : List Access) : Json := listJson accessJson l

/-- A number below `2^256` as JSON. -/
def u256Json (x : U256) : Json := quantityJson x.toNat

/-- The fields of a typed transaction that every type has, before its type-specific fields. -/
def typedFields (type : UInt8) (chainId : UInt64) (nonce gas value : U256) (data : ByteArray)
    (accessList : List Access) (yParity r s : U256) : List (String × Json) :=
  [("type", byteJson type), ("chainId", quantityJson chainId.toNat), ("nonce", u256Json nonce),
    ("gas", u256Json gas), ("value", u256Json value), ("input", dataJson data.data.toList),
    ("accessList", accessListJson accessList), ("yParity", u256Json yParity),
    ("v", u256Json yParity), ("r", u256Json r), ("s", u256Json s)]

/-- The fields of a signed transaction, with the price per gas that it pays as its gas price. -/
def transactionFields (gasPrice : Nat) : Transaction → List (String × Json)
  | .legacy tx =>
    [("type", byteJson 0), ("nonce", u256Json tx.nonce), ("gas", u256Json tx.gas),
      ("value", u256Json tx.value), ("input", dataJson tx.data.data.toList),
      ("to", optionJson (fun (a : Address) => dataJson a.toList) tx.to),
      ("gasPrice", quantityJson gasPrice), ("v", u256Json tx.v), ("r", u256Json tx.r),
      ("s", u256Json tx.s)] ++
    if 35 ≤ tx.v.toNat then [("chainId", quantityJson ((tx.v.toNat - 35) / 2))] else []
  | .accessList tx =>
    typedFields 1 tx.chainId tx.nonce tx.gas tx.value tx.data tx.accessList tx.yParity tx.r tx.s ++
      [("to", optionJson (fun (a : Address) => dataJson a.toList) tx.to),
        ("gasPrice", quantityJson gasPrice)]
  | .feeMarket tx =>
    typedFields 2 tx.chainId tx.nonce tx.gas tx.value tx.data tx.accessList tx.yParity tx.r tx.s ++
      [("to", optionJson (fun (a : Address) => dataJson a.toList) tx.to),
        ("gasPrice", quantityJson gasPrice),
        ("maxPriorityFeePerGas", u256Json tx.maxPriorityFeePerGas),
        ("maxFeePerGas", u256Json tx.maxFeePerGas)]
  | .blob tx =>
    typedFields 3 tx.chainId tx.nonce tx.gas tx.value tx.data tx.accessList tx.yParity tx.r tx.s ++
      [("to", dataJson tx.to.toList), ("gasPrice", quantityJson gasPrice),
        ("maxPriorityFeePerGas", u256Json tx.maxPriorityFeePerGas),
        ("maxFeePerGas", u256Json tx.maxFeePerGas),
        ("maxFeePerBlobGas", u256Json tx.maxFeePerBlobGas),
        ("blobVersionedHashes",
          listJson (fun (h : Bytes32) => dataJson h.toList) tx.blobVersionedHashes)]
  | .setCode tx =>
    typedFields 4 tx.chainId tx.nonce tx.gas tx.value tx.data tx.accessList tx.yParity tx.r tx.s ++
      [("to", dataJson tx.to.toList), ("gasPrice", quantityJson gasPrice),
        ("maxPriorityFeePerGas", u256Json tx.maxPriorityFeePerGas),
        ("maxFeePerGas", u256Json tx.maxFeePerGas),
        ("authorizationList", listJson authorizationJson tx.authorizations)]

/-- A signed transaction as JSON, outside a block.

Its gas price is its maximum fee per gas. -/
def transactionJson (tx : Transaction) : Json :=
  Json.mkObj (transactionFields tx.maxFeePerGas tx)

/-- The recipient of a transaction: an address, or none when the field is absent or `null`. -/
def recipient (fs : List (String × Json)) : Read (Option Address) :=
  match fs.lookup "to" with
  | none => pure none
  | some j => some <$> address "to" j

/-- A signed transaction, read by the kind that its type names.

Any other field is ignored, but type 2 still needs a gas price, which its schema requires. -/
def transactionOfJson (j : Json) : Read Transaction := do
  let fs ← fields "transaction" j
  let get := field "transaction" fs
  let type ← uint "type" (← get "type")
  if 4 < type then reject "type: not a transaction type"
  let nonce ← uint256 "nonce" (← get "nonce")
  let gas ← uint256 "gas" (← get "gas")
  let value ← uint256 "value" (← get "value")
  let data ← bytes "input" (← get "input")
  let r ← uint256 "r" (← get "r")
  let s ← uint256 "s" (← get "s")
  if type = 0 then
    return .legacy { nonce, gas, value, data, r, s
                     gasPrice := ← uint256 "gasPrice" (← get "gasPrice")
                     to := ← recipient fs
                     v := ← uint256 "v" (← get "v") }
  let chainId ← uint64 "chainId" (← get "chainId")
  let accessList ← array "accessList" access (← get "accessList")
  let yParity := BitVec.ofNat 256 (← byte "yParity" (← get "yParity")).toNat
  if type = 1 then
    return .accessList { chainId, nonce, gas, value, data, accessList, yParity, r, s
                         gasPrice := ← uint256 "gasPrice" (← get "gasPrice")
                         to := ← recipient fs }
  let maxPriorityFeePerGas ← uint256 "maxPriorityFeePerGas" (← get "maxPriorityFeePerGas")
  let maxFeePerGas ← uint256 "maxFeePerGas" (← get "maxFeePerGas")
  if type = 2 then
    let _ ← uint "gasPrice" (← get "gasPrice")
    return .feeMarket { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, value, data,
                        accessList, yParity, r, s
                        to := ← recipient fs }
  let to ← address "to" (← get "to")
  if type = 3 then
    return .blob { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data,
                   accessList, yParity, r, s
                   maxFeePerBlobGas := ← uint256 "maxFeePerBlobGas" (← get "maxFeePerBlobGas")
                   blobVersionedHashes := ← array "blobVersionedHashes" (bytes32 "blob hash")
                     (← get "blobVersionedHashes") }
  if type = 4 then
    return .setCode { chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data,
                      accessList, yParity, r, s
                      authorizations := ← array "authorizationList" authorization
                        (← get "authorizationList") }
  reject "type: not a transaction type"

end EthLib.Execution.Rpc

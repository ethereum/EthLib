module

public import EthLib.Execution.Rpc.Raw

/-!
# `Execution.Rpc.Account`

The account queries of the execution JSON-RPC API, in [`state.yaml`][state].

Each query reads the state after the block that its block parameter names.

The parameter is optional, and `latest` by default.

- `eth_getBalance` gives the balance of an address.
- `eth_getTransactionCount` gives its nonce.
- `eth_getCode` gives its code.
- `eth_getStorageAt` gives the word at one key of its storage.
- `eth_getStorageValues` gives the words at some keys of the storage of some addresses.

For an address with no account, the fixtures fix answers that no text states.

The balance is `0x0`, as `get-balance-unknown-account.io` expects.

The nonce is `0x0`, as `get-nonce-unknown-account.io` expects.

The code is `0x`, as `get-code-unknown-account.io` expects.

Each storage word is zero, as `get-storage-unknown-account.io` expects.

So an address with no account reads as the empty account.

Its storage words are those of the state, which the transition leaves empty for such an address.

The code of an account delegated by [EIP-7702][eip7702] is its delegation designator.

That is the code that the state holds for it.

The fixture `get-code-eip7702-delegation.io` expects that.

A storage key is a `bytesMax32`, at most 32 bytes in hex, read as a number on 32 bytes.

A word is 32 bytes.

The fixtures give each word on 32 bytes, with leading zeros, though the schema types it `bytes`.

The schema of `eth_getStorageValues` does not say how to treat an empty object.

Here it is an invalid parameter, `-32602`, as `get-storage-values-empty-request.io` expects.

Two members of the object can name one address, in two cases of hex.

Here they are an invalid parameter too, since the answer has one member for each address.

A member name written twice in the same case is one member, the last, as the JSON text is read.

A member whose keys are `null` is an invalid parameter, since the schema asks for an array.

The answer writes each address in lower case, as the fixtures do.

The example of the source echoes the case of the request, which no text requires.

The block parameter, when present, is a block: `null` is an invalid parameter.

An unknown block gets `-32001`, "Resource not found", as for the raw getters.

The tag `pending` gets the same error when the view has no pending block.

A code hash with no code in the state gets `-32603`.

[state]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/state.yaml
[eip7702]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7702.md
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.State (Account State EMPTY_ACCOUNT)

namespace BlockRecord

/-- The account of an address in the state after the block, or the empty account for none. -/
def account (r : BlockRecord) (a : Address) : Account :=
  (r.state.getAccountOptional a).getD EMPTY_ACCOUNT

/-- The code of an address in the state after the block, empty for no account.

A code hash with no code in the state is an internal error. -/
def code (r : BlockRecord) (a : Address) : Except RpcError ByteArray :=
  (r.state.getCode (r.account a).codeHash).mapError fun _ =>
    internalError.toRpcError (some (.str "code: missing from the state"))

/-- The word at a key of the storage of an address in the state after the block. -/
def storage (r : BlockRecord) (a : Address) (key : Bytes32) : U256 :=
  r.state.getStorage a key

end BlockRecord

/-- The requests of `eth_getStorageValues`: each address with its keys.

The object must have a member, and no two members may name one address. -/
def storageRequests (j : Json) : Read (List (Address × List Bytes32)) := do
  let .obj members := j | reject "requests: not an object"
  let fs := members.toList
  if fs.isEmpty then reject "requests: empty request"
  let requests ← fs.mapM fun (name, keys) => do
    return (← address "address" (.str name), ← array "keys" (bytesMax32 "key") keys)
  unless (requests.map (·.1)).Nodup do reject "requests: an address twice"
  return requests

/-- The JSON of a word on 32 bytes. -/
def wordJson (w : U256) : Json :=
  dataJson w.toBeBytes.toList

/-- The answer of `eth_getStorageValues`: an object from each address to its words. -/
def storageValuesJson (values : List (Address × List U256)) : Json :=
  Json.mkObj (values.map fun (a, words) => (hexString a.toList, listJson wordJson words))

namespace ChainView

/-- The balance of an address after a block, as `eth_getBalance` returns it. -/
def balance (v : ChainView) (a : Address) (p : BlockParam) : Except RpcError U256 :=
  v.ofBlock p fun r => .ok (r.account a).balance

/-- The nonce of an address after a block, as `eth_getTransactionCount` returns it. -/
def nonce (v : ChainView) (a : Address) (p : BlockParam) : Except RpcError Nat :=
  v.ofBlock p fun r => .ok (r.account a).nonce

/-- The code of an address after a block, as `eth_getCode` returns it. -/
def code (v : ChainView) (a : Address) (p : BlockParam) : Except RpcError ByteArray :=
  v.ofBlock p (·.code a)

/-- The word at a key of the storage of an address after a block, as `eth_getStorageAt` gives it. -/
def storageAt (v : ChainView) (a : Address) (key : Bytes32) (p : BlockParam) :
    Except RpcError U256 :=
  v.ofBlock p fun r => .ok (r.storage a key)

/-- The words at the keys of each address after a block, as `eth_getStorageValues` gives them. -/
def storageValues (v : ChainView) (requests : List (Address × List Bytes32)) (p : BlockParam) :
    Except RpcError (List (Address × List U256)) :=
  v.ofBlock p fun r => .ok (requests.map fun (a, keys) => (a, keys.map (r.storage a)))

end ChainView

end EthLib.Execution.Rpc

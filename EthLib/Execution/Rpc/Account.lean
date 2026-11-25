module

public import EthLib.Base.List
public import EthLib.Execution.Rpc.Raw

/-!
# `Execution.Rpc.Account`

The account queries of the execution JSON-RPC API.

Each query reads the state after the block that its block parameter names, the latest by default.

The parameter, when present, must not be null: null is an invalid parameter, -32602.

Source: [`state.yaml`][state], at commit `1ca0818` of execution-apis: the methods and their schemas.

[state]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/eth/state.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.State (Account State EMPTY_ACCOUNT)

namespace BlockRecord

/-- The account of an address in the state after the block, or the empty account for none.

For an address with no account, the fixtures fix answers that no text states, and EthLib follows. -/
def account (r : BlockRecord) (a : Address) : Account :=
  -- No account reads as the empty account: balance 0, nonce 0, no code, as the fixtures expect.
  (r.state.getAccountOptional a).getD EMPTY_ACCOUNT

/-- The code of an address in the state after the block, empty for no account.

The code of an account delegated by [EIP-7702][eip7702] is its delegation designator.

A code hash with no code in the state is an internal error.

[eip7702]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7702.md
-/
def code (r : BlockRecord) (a : Address) : Except RpcError ByteArray :=
  -- The code of the code hash, which is the delegation designator for an account of EIP-7702.
  --
  -- A fixture expects that designator.
  --
  -- EthLib's choice: a code hash with no code in the state gets code -32603.
  (r.state.getCode (r.account a).codeHash).mapError fun _ =>
    internalError.toRpcError (some (.str "code: missing from the state"))

/-- The word at a key of the storage of an address in the state after the block. -/
def storage (r : BlockRecord) (a : Address) (key : Bytes32) : U256 :=
  -- An address with no account has empty storage, so each word is 0, as the fixtures expect.
  r.state.getStorage a key

end BlockRecord

/-- The requests of `eth_getStorageValues`: each address with its keys.

The object must have a member, and no two members may name one address. -/
def storageRequests (j : Json) : Read (List (Address × List Bytes32)) := do
  let .obj members := j | reject "requests: not an object"
  -- EthLib's choice: a name written twice in the same case is one member, the last.
  --
  -- RFC 8259 §4 leaves an object with a repeated name open.
  let fs := members.toList
  -- An empty object is invalid, code -32602, as a fixture expects.
  --
  -- The schema does not say how to treat it.
  if fs.isEmpty then reject "requests: empty request"
  -- EthLib reads each member name as an address, since the method asks for accounts.
  --
  -- The schema: the keys of a member are an array, so null keys are invalid.
  --
  -- A key has at most 32 bytes in hex, read as a number on 32 bytes.
  let requests ← fs.mapM fun (name, keys) => do
    return (← address "address" (.str name), ← array "keys" (bytesMax32 "key") keys)
  -- EthLib's choice: one address in two cases of hex is invalid, code -32602.
  --
  -- The answer has one member for each address.
  unless (Base.firstRepeated (requests.map (·.1))).isNone do reject "requests: an address twice"
  return requests

/-- The JSON of a word on 32 bytes. -/
def wordJson (w : U256) : Json :=
  -- 32 bytes with leading zeros, as the fixtures write a word, though the schema types it bytes.
  dataJson w.toBeBytes.toList

/-- The answer of `eth_getStorageValues`: an object from each address to its words. -/
def storageValuesJson (values : List (Address × List U256)) : Json :=
  -- Each address in lower case, as the fixtures write it.
  --
  -- The example of the source echoes the case of the request, which no text requires.
  Json.mkObj (values.map fun (a, words) => (hexString a.toList, listJson wordJson words))

namespace ChainView

/-- The balance of an address after a block, as `eth_getBalance` returns it. -/
def balance (v : ChainView) (a : Address) (p : BlockParam) : Except RpcError U256 :=
  -- Each query: an unknown block, or no pending block for that tag, gets code -32001.
  --
  -- EIP-1898 recommends that code for a block not found, and EthLib uses it for every form.
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

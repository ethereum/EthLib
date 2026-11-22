module

public import EthLib.Execution.Rpc.Account
public import EthLib.Execution.Rpc.Raw
public import EthLib.Execution.Rpc.Base

/-!
# `Execution.Rpc.AccessList`

The block access list of [EIP-7928][eip7928], in the JSON and RLP forms of the execution API.

The JSON schema is [`block-access-list.yaml`][schema].

The methods follow `eth_getBlockAccessList` in [`block.yaml`][eth] and the [raw getter][debug].

The source leaves the pending block open for the raw getter, and EthLib reads it from the view.

[eip7928]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7928.md#rlp-encoding
[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block-access-list.yaml
[eth]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/block.yaml
[debug]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/debug/getters.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Serialization.Rlp (Codec)
open EthLib.Execution.Blocks

/-- The required fields of an access-list object, with no other field.

A `null` field counts as a field, since the schema allows no `null` value. -/
def blockAccessFields (names : List String) : Json → Read (List (String × Json))
  -- The schema: each required field, and no other.
  | .obj kvs =>
    if hasExactly kvs.toList names then .ok kvs.toList
    else reject "block access list: wrong fields"
  | _ => reject "block access list: not an object"

/-- A storage word read from exactly 32 bytes. -/
def storageWordOfJson (j : Json) : Read U256 :=
  -- The schema: a storage key or value is 32 bytes of data, read big-endian.
  U256.fromBeBytes <$> hash32 "storage word" j

/-- The JSON object of a `StorageChange`, with the fields of the access-list schema. -/
def storageChangeJson (c : StorageChange) : Json :=
  -- The index as a quantity, and the value as 32 bytes of data.
  Json.mkObj [
    ("index", quantityJson c.index.toNat),
    ("value", wordJson c.value)]

/-- Read a `StorageChange` from the fields of its JSON schema. -/
def storageChangeOfJson (j : Json) : Read StorageChange := do
  let fs ← blockAccessFields ["index", "value"] j
  -- The index fits 32 bits, and the value is 32 bytes.
  return {
    index := ← uint32 "index" (← field "block access list" fs "index")
    value := ← storageWordOfJson (← field "block access list" fs "value") }

/-- The JSON object of a `BalanceChange`, with the fields of the access-list schema. -/
def balanceChangeJson (c : BalanceChange) : Json :=
  -- The index and the balance, both quantities.
  Json.mkObj [
    ("index", quantityJson c.index.toNat),
    ("value", quantityJson c.balance.toNat)]

/-- Read a `BalanceChange` from the fields of its JSON schema. -/
def balanceChangeOfJson (j : Json) : Read BalanceChange := do
  let fs ← blockAccessFields ["index", "value"] j
  -- The index fits 32 bits, and the balance 256 bits.
  return {
    index := ← uint32 "index" (← field "block access list" fs "index")
    balance := ← uint256 "value" (← field "block access list" fs "value") }

/-- The JSON object of a `NonceChange`, with the fields of the access-list schema. -/
def nonceChangeJson (c : NonceChange) : Json :=
  -- The index and the nonce, both quantities.
  Json.mkObj [
    ("index", quantityJson c.index.toNat),
    ("value", quantityJson c.nonce.toNat)]

/-- Read a `NonceChange` from the fields of its JSON schema. -/
def nonceChangeOfJson (j : Json) : Read NonceChange := do
  let fs ← blockAccessFields ["index", "value"] j
  -- The index fits 32 bits, and the nonce 64 bits.
  return {
    index := ← uint32 "index" (← field "block access list" fs "index")
    nonce := ← uint64 "value" (← field "block access list" fs "value") }

/-- The JSON object of a `CodeChange`, with the fields of the access-list schema. -/
def codeChangeJson (c : CodeChange) : Json :=
  -- The index as a quantity, and the code as data.
  Json.mkObj [
    ("index", quantityJson c.index.toNat),
    ("code", dataJson c.code.data.toList)]

/-- Read a `CodeChange` from the fields of its JSON schema. -/
def codeChangeOfJson (j : Json) : Read CodeChange := do
  let fs ← blockAccessFields ["index", "code"] j
  -- The index fits 32 bits, and the code is any bytes.
  return {
    index := ← uint32 "index" (← field "block access list" fs "index")
    code := ← bytes "code" (← field "block access list" fs "code") }

/-- The JSON object of a `SlotChanges`, with the fields of the access-list schema. -/
def slotChangesJson (c : SlotChanges) : Json :=
  -- The key as 32 bytes of data, then its changes in order.
  Json.mkObj [
    ("key", wordJson c.slot),
    ("changes", listJson storageChangeJson c.changes)]

/-- Read a `SlotChanges` from the fields of its JSON schema. -/
def slotChangesOfJson (j : Json) : Read SlotChanges := do
  let fs ← blockAccessFields ["key", "changes"] j
  -- The key is 32 bytes, and the changes a list.
  return {
    slot := ← storageWordOfJson (← field "block access list" fs "key")
    changes := ← array "changes" storageChangeOfJson (← field "block access list" fs "changes") }

/-- The JSON object of `AccountChanges`, with the fields of the access-list schema. -/
def accountChangesJson (c : AccountChanges) : Json :=
  -- The method: all six fields, with an empty change list as an empty array.
  Json.mkObj [
    ("address", dataJson c.address.toList),
    ("storageChanges", listJson slotChangesJson c.storageChanges),
    ("storageReads", listJson wordJson c.storageReads),
    ("balanceChanges", listJson balanceChangeJson c.balanceChanges),
    ("nonceChanges", listJson nonceChangeJson c.nonceChanges),
    ("codeChanges", listJson codeChangeJson c.codeChanges)]

/-- Read `AccountChanges` from the fields of its JSON schema. -/
def accountChangesOfJson (j : Json) : Read AccountChanges := do
  let fs ← blockAccessFields
    ["address", "storageChanges", "storageReads", "balanceChanges", "nonceChanges", "codeChanges"] j
  -- The address, then the five lists of the schema.
  return {
    address := ← address "address" (← field "block access list" fs "address")
    storageChanges := ← array "storageChanges" slotChangesOfJson
      (← field "block access list" fs "storageChanges")
    storageReads := ← array "storageReads" storageWordOfJson
      (← field "block access list" fs "storageReads")
    balanceChanges := ← array "balanceChanges" balanceChangeOfJson
      (← field "block access list" fs "balanceChanges")
    nonceChanges := ← array "nonceChanges" nonceChangeOfJson
      (← field "block access list" fs "nonceChanges")
    codeChanges := ← array "codeChanges" codeChangeOfJson
      (← field "block access list" fs "codeChanges") }

/-- The block access list as JSON, in its retained account and change order.

The method asks for the order of the canonical RLP encoding, which the retained list keeps. -/
def blockAccessListJson (bal : BlockAccessList) : Json := listJson accountChangesJson bal

/-- Read the JSON form of a block access list, without checking its canonical order. -/
def blockAccessListOfJson (j : Json) : Read BlockAccessList :=
  array "block access list" accountChangesOfJson j

namespace BlockRecord

/-- The retained list, or the error fixed by the method for the fork or pruning. -/
def retainedAccessList (r : BlockRecord) : Except RpcError BlockAccessList :=
  -- Both methods: a block before Amsterdam, here Glamsterdam, gets code -32001.
  if r.fork < .glamsterdam then
    .error (resourceNotFound.toRpcError (some (.str "block predates Amsterdam")))
  -- Both methods: a list that the node pruned gets code 4444.
  else match r.accessList with
    | none => .error (prunedHistoryUnavailable.toRpcError none)
    | some bal => .ok bal

/-- The JSON form of the retained block access list. -/
def blockAccessList (r : BlockRecord) : Except RpcError Json :=
  blockAccessListJson <$> r.retainedAccessList

/-- The RLP form of the retained block access list. -/
def rawBlockAccessList (r : BlockRecord) : Except RpcError ByteArray := do
  let bal ← r.retainedAccessList
  -- EIP-7928: the RLP of the list, so 0xc0 for a block with no access, as the raw getter says.
  (Codec.encode bal).mapError fun _ => encodingError "block access list"

end BlockRecord

namespace ChainView

/-- The JSON list of the requested block, or `null` for an unknown block or `pending`. -/
def blockAccessList (v : ChainView) : BlockParam → Except RpcError Json
  -- The method: null for the pending block.
  | .tag .pending => .ok .null
  | p => do
    match ← v.resolve p with
    -- The method: null for an unknown block.
    | none => return .null
    | some r => r.blockAccessList

/-- The RLP list of the requested block, with an error for an unknown block. -/
def rawBlockAccessList (v : ChainView) (p : BlockParam) : Except RpcError ByteArray :=
  -- The method: an unknown block gets code -32001.
  v.ofBlock p BlockRecord.rawBlockAccessList

/-- Forget retained access lists at the named block numbers, while keeping their blocks. -/
def pruneAccessLists (v : ChainView) (numbers : List Nat) : ChainView :=
  let prune := fun (r : BlockRecord) =>
    if r.block.header.number ∈ numbers then { r with accessList := none } else r
  { v with
    canonical := v.canonical.map prune
    nonempty := by simpa using v.nonempty
    side := v.side.map prune
    pending := v.pending.map prune }

end ChainView

end EthLib.Execution.Rpc

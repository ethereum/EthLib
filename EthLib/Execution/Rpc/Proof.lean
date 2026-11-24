module

public import EthLib.Execution.Rpc.Account
public import EthLib.Execution.State.AccountProof

/-!
# `Execution.Rpc.Proof`

The answer of `eth_getProof`, and its JSON form.

Sources, at commit `1ca0818` of execution-apis:

- the [method text][method] of [`state.yaml`][state]: the slot order and the form of each key
- the [`AccountProof` schema][schema]: the fields of the answer

[state]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/eth/state.yaml
[method]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/eth/state.yaml#L161-L200
[schema]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/state.yaml#L1-L63
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.State (AccountProof StorageKey StorageProof)

/-- A storage key of a request: at most 64 hex digits, read as a slot.

A key of 63 or 64 digits comes back in the answer as 32 bytes, and any other key as a number. -/
def storageKey (what : String) (j : Json) : Read StorageKey := do
  -- The type of the schema: at most 64 hex digits, read as a number on 32 bytes, so 0x is 0.
  let slot ← bytesMax32 what j
  -- The method: a key of 63 or 64 digits comes back as 32 bytes, and any other as a number.
  let digits ← hexDigits what j
  return ⟨slot, 63 ≤ digits.size⟩

/-- The key of a slot of an answer: 32 bytes, or a quantity, as the schema of the answer allows.

A key of 64 hex digits is 32 bytes, and any other key must be a quantity without leading zeros. -/
def answerKey (what : String) (j : Json) : Read StorageKey := do
  let slot ← bytesMax32 what j
  let digits ← hexDigits what j
  -- The schema: 32 bytes for 64 digits, else a quantity without leading zeros.
  if digits.size = 64 then return ⟨slot, true⟩
  let _ ← quantity what 256 j
  return ⟨slot, false⟩

/-- The JSON of a storage key, in the form in which the request gave it. -/
def storageKeyJson (key : StorageKey) : Json :=
  if key.asBytes then dataJson key.slot.toList else quantityJson (ByteOrder.ofBE key.slot.toList)

/-- The nodes of a proof, each a byte string. -/
def proofNodes (what : String) (j : Json) : Read (List ByteArray) :=
  array what (bytes what) j

/-- One slot of an answer: its key, its word and the nodes of its proof. -/
def storageProofOfJson (j : Json) : Read StorageProof := do
  let fs ← fields "slot" j
  return ⟨← answerKey "key" (← field "slot" fs "key"),
    BitVec.ofNat 256 (← quantity "value" 256 (← field "slot" fs "value")),
    ← proofNodes "proof" (← field "slot" fs "proof")⟩

/-- An answer of `eth_getProof`, from the value of its JSON.

Its fields are those of the `AccountProof` schema. -/
def accountProofOfJson (j : Json) : Read AccountProof := do
  let fs ← fields "answer" j
  let field := field "answer" fs
  -- The schema: an address of 20 bytes, a nonce below `2^64`, and a balance below `2^256`.
  --
  -- A code hash and a storage root of 32 bytes, and each node of a proof a byte string.
  --
  -- The writer does not bound the nonce, so the reader takes back only a nonce below `2^64`.
  return {
    address := ← address "address" (← field "address")
    nonce := ← quantity "nonce" 64 (← field "nonce")
    balance := BitVec.ofNat 256 (← quantity "balance" 256 (← field "balance"))
    codeHash := ← fixed "codeHash" 32 (← field "codeHash")
    storageHash := ← fixed "storageHash" 32 (← field "storageHash")
    accountProof := ← proofNodes "accountProof" (← field "accountProof")
    storageProof := ← array "storageProof" storageProofOfJson (← field "storageProof") }

/-- The JSON of the nodes of a proof. -/
def proofNodesJson (nodes : List ByteArray) : Json :=
  listJson (dataJson ·.toList) nodes

/-- The JSON of one slot: the key in the form of the request, the word and the proof. -/
def storageProofJson (s : StorageProof) : Json :=
  Json.mkObj [("key", storageKeyJson s.key),
    ("value", quantityJson s.value.toNat), ("proof", proofNodesJson s.proof)]

/-- The JSON of an answer of `eth_getProof`. -/
def accountProofJson (p : AccountProof) : Json :=
  -- The address in lower case, as the fixtures write it.
  Json.mkObj [("address", dataJson p.address.toList),
    ("accountProof", proofNodesJson p.accountProof),
    ("balance", quantityJson p.balance.toNat),
    ("codeHash", dataJson p.codeHash.toList),
    ("nonce", quantityJson p.nonce),
    ("storageHash", dataJson p.storageHash.toList),
    ("storageProof", listJson storageProofJson p.storageProof)]

namespace ChainView

/-- The proof of an address and some of its slots after a block, as `eth_getProof` gives it.

The source requires a node to take at least 1024 keys, and here a request may hold any number.

The source does not bound how far back a node serves proofs.

Here the node serves them at every block that it holds, so it never gives the error 4444.

That error is for a node that drops old state. -/
def accountProof (v : ChainView) (a : Address) (keys : List StorageKey) (p : BlockParam) :
    Except RpcError AccountProof :=
  -- The method: one slot for each key, in the order of the request, even for a key given twice.
  --
  -- EthLib's choice: a trie of the state that the node cannot encode gets code -32603.
  v.ofBlock p fun r =>
    (AccountProof.ofState Cryptography.Hash.Keccak.keccak256 r.state a keys).mapError fun _ =>
      internalError.toRpcError (some (.str "proof: the state has no proof"))

end ChainView

end EthLib.Execution.Rpc

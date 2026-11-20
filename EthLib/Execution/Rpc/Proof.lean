module

public import EthLib.Execution.Rpc.Account
public import EthLib.Execution.State.AccountProof

/-!
# `Execution.Rpc.Proof`

The answer of `eth_getProof`, in [`state.yaml`][state], and its JSON form.

The node answers with the proof of an account, and of some of its slots, in the state after a block.

The block parameter is optional, and `latest` by default.

The fields of the answer are those of the [`AccountProof` schema][schema].

An address is 20 bytes of hex, a nonce a 64-bit number, and a balance or a word a quantity.

The writer does not bound the nonce, so the reader takes back only a nonce below `2^64`.

A code hash or a storage root is 32 bytes, and each node of a proof a byte string.

A storage key of a request has at most 64 hex digits, as the `bytesMax32` type allows.

The reader takes it as a number on 32 bytes, and an empty key `0x` as `0`.

The reader of an answer takes a key only as 32 bytes, or as a quantity without leading zeros.

The answer has one slot for each key, in the order of the request, even for a key given twice.

Each slot gives back its key in the form of the [method text][method].

A key of 63 or 64 hex digits comes back as 32 bytes, and any other key as a number.

The source asks a node to take at least 1024 keys; here a request may hold any number of keys.

The answer writes the address in lower case, as the fixtures do.

A trie of the state that the node cannot encode gets `-32603`.

The source does not bound how far back a node serves proofs.

Here it serves them at every block that it holds, so it never gives the error `4444`.

That error is for a node that drops old state.

[state]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/eth/state.yaml
[method]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/eth/state.yaml#L161-L200
[schema]: https://github.com/ethereum/execution-apis/blob/68d76a5b1c09dff023782d97eec6ce87a6f6505e/src/schemas/state.yaml#L1-L62
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
  let slot ← bytesMax32 what j
  let digits ← hexDigits what j
  return ⟨slot, 63 ≤ digits.size⟩

/-- The key of a slot of an answer: 32 bytes, or a quantity, as the schema of the answer allows.

A key of 64 hex digits is 32 bytes, and any other key must be a quantity without leading zeros. -/
def answerKey (what : String) (j : Json) : Read StorageKey := do
  let slot ← bytesMax32 what j
  let digits ← hexDigits what j
  if digits.size = 64 then return ⟨slot, true⟩
  let _ ← quantity what 256 j
  return ⟨slot, false⟩

/-- The JSON of a storage key, in the form in which the request gave it. -/
def storageKeyJson (key : StorageKey) : Json :=
  if key.asBytes then dataJson key.slot.toList else quantityJson (bytesToNat key.slot.toList)

/-- The nodes of a proof, each a byte string. -/
def proofNodes (what : String) (j : Json) : Read (List ByteArray) :=
  array what (bytes what) j

/-- One slot of an answer: its key, its word and the nodes of its proof. -/
def storageProofOfJson (j : Json) : Read StorageProof := do
  let fs ← fields "slot" j
  return ⟨← answerKey "key" (← field "slot" fs "key"),
    BitVec.ofNat 256 (← quantity "value" 256 (← field "slot" fs "value")),
    ← proofNodes "proof" (← field "slot" fs "proof")⟩

/-- An answer of `eth_getProof`, from the value of its JSON. -/
def accountProofOfJson (j : Json) : Read AccountProof := do
  let fs ← fields "answer" j
  let field := field "answer" fs
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

/-- The JSON of one slot of an answer: the key in the form of the request, the word and the proof.
-/
def storageProofJson (s : StorageProof) : Json :=
  Json.mkObj [("key", storageKeyJson s.key),
    ("value", quantityJson s.value.toNat), ("proof", proofNodesJson s.proof)]

/-- The JSON of an answer of `eth_getProof`. -/
def accountProofJson (p : AccountProof) : Json :=
  Json.mkObj [("address", dataJson p.address.toList),
    ("accountProof", proofNodesJson p.accountProof),
    ("balance", quantityJson p.balance.toNat),
    ("codeHash", dataJson p.codeHash.toList),
    ("nonce", quantityJson p.nonce),
    ("storageHash", dataJson p.storageHash.toList),
    ("storageProof", listJson storageProofJson p.storageProof)]

namespace ChainView

/-- The proof of an address and some of its slots after a block, as `eth_getProof` gives it. -/
def accountProof (v : ChainView) (a : Address) (keys : List StorageKey) (p : BlockParam) :
    Except RpcError AccountProof :=
  v.ofBlock p fun r =>
    (AccountProof.ofState Cryptography.Hash.Keccak.keccak256 r.state a keys).mapError fun _ =>
      internalError.toRpcError (some (.str "proof: the state has no proof"))

end ChainView

end EthLib.Execution.Rpc

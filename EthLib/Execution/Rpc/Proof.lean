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

A storage key has at most 64 hex digits, as the `bytesMax32` type of the schema allows.

The reader takes a key as a number on 32 bytes.

The answer writes each key as a quantity, without leading zeros.

The fixture `get-account-proof-with-storage.io` asks for the key `0x00` and expects `0x0`.

The schema allows both forms, and no text fixes the form of the echo.

The answer writes the address in lower case, as the fixtures do.

A trie of the state that the node cannot encode gets `-32603`.

The source does not bound how far back a node serves proofs.

Here it serves them at every block that it holds.

[state]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/state.yaml
[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/state.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.State (AccountProof StorageProof)

/-- The nodes of a proof, each a byte string. -/
def proofNodes (what : String) (j : Json) : Read (List ByteArray) :=
  array what (bytes what) j

/-- One slot of an answer: its key, its word and the nodes of its proof. -/
def storageProofOfJson (j : Json) : Read StorageProof := do
  let fs ← fields "slot" j
  return ⟨← bytesMax32 "key" (← field "slot" fs "key"),
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

/-- The JSON of one slot of an answer: the key as a quantity, the word and the proof. -/
def storageProofJson (s : StorageProof) : Json :=
  Json.mkObj [("key", quantityJson (bytesToNat s.key.toList)),
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
def accountProof (v : ChainView) (a : Address) (keys : List Bytes32) (p : BlockParam) :
    Except RpcError AccountProof :=
  v.ofBlock p fun r =>
    (AccountProof.ofState Cryptography.Hash.Keccak.keccak256 r.state a keys).mapError fun _ =>
      internalError.toRpcError (some (.str "proof: the state has no proof"))

end ChainView

end EthLib.Execution.Rpc

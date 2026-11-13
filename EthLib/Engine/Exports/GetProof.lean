module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Engine.Json
public import EthLib.Execution.State.AccountProof

/-!
# `Exports.GetProof`

The C export that checks an answer of `eth_getProof` against a state root.

The answer crosses as the typed value of its JSON: the `result` object of the response.

Its fields are those of `AccountProof` in the execution API, each in the pattern of its base type.

So an address is 20 bytes of hex, a nonce a 64-bit number and a balance or a slot value a word.

A code hash or a storage root is 32 bytes, and each node of a proof a byte string.

A storage key has at most 64 hex digits, as its type `bytesMax32` allows.

It is read as a number on 32 bytes.

A field that is missing or out of its pattern, or a root that is not 32 bytes, has code 0.

The export sits in the Engine layer, beside the readers of the patterns of the execution API.

The base types are those of [`base-types.yaml`][types].

[types]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/base-types.yaml
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Serialization.JsonRpc (Read address array bytes field fields fixed hexDigits
  hexValue quantity reject)

/-- A storage key: at most 64 lowercase hex digits, read as a number on 32 big-endian bytes. -/
def storageKey (j : Json) : Read Bytes32 := do
  let digits ← hexDigits "key" j
  if digits.size > 64 then reject "key: more than 64 hex digits" else
  let mut value := 0
  for c in digits do
    match hexValue false c with
    | some d => value := 16 * value + d.toNat
    | none => reject "key: not a hex digit"
  return Vector.ofFn fun i : Fin 32 => (value / 256 ^ (31 - i.val) % 256).toUInt8

/-- The nodes of a proof, each a byte string. -/
def proofNodes (what : String) (j : Json) : Read (List ByteArray) :=
  array what (bytes what) j

/-- One slot of an answer: its key, its value and the nodes of its proof. -/
def storageProofOfJson (j : Json) : Read Execution.State.StorageProof := do
  let fs ← fields "slot" j
  return ⟨← storageKey (← field "slot" fs "key"),
    BitVec.ofNat 256 (← quantity "value" 256 (← field "slot" fs "value")),
    ← proofNodes "proof" (← field "slot" fs "proof")⟩

/-- An answer of `eth_getProof`, from the value of its JSON. -/
def accountProofOfJson (j : Json) : Read Execution.State.AccountProof := do
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

/-- Check an answer of `eth_getProof` against a 32-byte state root, with Keccak-256.

`None` means that the proof shows no account at the address, with the nonce, balance and slots 0.

Otherwise each slot is true when it is set and holds its value, and false when it is not set. -/
def verifyAccountProofOf (args : ByteArray × PyValue) : Result (Option (List Bool)) := do
  let (root, answer) := args
  if h : root.size = 32 then
    let p ← (accountProofOfJson answer.toJson).mapError fun reason => (0, reason)
    match p.verify Cryptography.Hash.Keccak.keccak256 ⟨root.data, h⟩ with
    | .ok .absent => return none
    | .ok (.present slots) => return some (slots.map fun
        | .set => true
        | .absent => false)
    | .error e => throw (e.code, s!"answer does not hold: {repr e}")
  else
    throw (0, s!"bad root size: {root.size}, expected 32")

/-- Check an answer of `eth_getProof` against a 32-byte state root, with Keccak-256.

The arguments are the state root and the `result` object of the response.

`None` means that the proof shows no account at the address, with the nonce, balance and slots 0.

Otherwise each slot is true when it is set and holds its value, and false when it is not set.

A field that is missing or out of its pattern, or a root that is not 32 bytes, has code 0.

An answer that does not hold has the code of its fault. -/
@[export eth_trie_verify_account_proof]
def verifyAccountProofExport (args : PyValue) : Result PyValue :=
  pyExport verifyAccountProofOf args

end EthLib.Engine.Exports

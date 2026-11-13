module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Rpc.Proof

/-!
# `Exports.GetProof`

The C export that checks an answer of `eth_getProof` against a state root.

The answer crosses as the typed value of its JSON: the `result` object of the response.

It is read as the answer of the JSON-RPC method, each field in the pattern of its type.

A field that is missing or out of its pattern, or a root that is not 32 bytes, has code 0.
-/

public section

namespace EthLib.Engine.Exports

open Lean (Json)
open EthLib.Exports (Result PyValue pyExport)
open EthLib.Base
open EthLib.Execution.Rpc (accountProofOfJson)

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

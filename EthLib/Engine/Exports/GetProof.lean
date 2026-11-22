module

public import EthLib.Base.Exports.PyValue
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
open EthLib.Exports (ExportError Result PyValue UnreadArgument oneLine pyExport toResult)
open EthLib.Base
open EthLib.Execution.Rpc (accountProofOfJson)

/-- An answer that does not hold reaches Python with its code, and its message is on one line. -/
instance : ExportError Execution.State.AccountProofError where
  code := Execution.State.AccountProofError.code
  message := oneLine

/-- Check an answer of `eth_getProof` against a 32-byte state root, with Keccak-256.

`None` means that the proof shows no account at the address.

The answer then has nonce and balance 0, zero hashes, and each slot the word 0 with no proof node.

Otherwise each slot is true when it is set and holds its value, and false when it is not set. -/
def verifyAccountProofOf (args : ByteArray × PyValue) : Result (Option (List Bool)) := do
  let (root, answer) := args
  let root ← toResult none (Base.exactBytes 32 root fun size =>
    UnreadArgument.mk s!"bad root size: {size}, expected 32")
  let p ← toResult none ((accountProofOfJson answer.toJson).mapError UnreadArgument.mk)
  match ← toResult "answer does not hold" (p.verify Cryptography.Hash.Keccak.keccak256 root) with
  | .absent => return none
  | .present slots => return some (slots.map fun
      | .set => true
      | .absent => false)

/-- Check an answer of `eth_getProof` against a 32-byte state root, with Keccak-256.

The arguments are the state root and the `result` object of the response.

`None` means that the proof shows no account at the address.

The answer then has nonce and balance 0, zero hashes, and each slot the word 0 with no proof node.

Otherwise each slot is true when it is set and holds its value, and false when it is not set.

A field that is missing or out of its pattern, or a root that is not 32 bytes, has code 0.

An answer that does not hold has the code of its fault. -/
@[export eth_trie_verify_account_proof]
def verifyAccountProofExport (args : PyValue) : Result PyValue :=
  pyExport verifyAccountProofOf args

end EthLib.Engine.Exports

module

public import EthLib.Execution.Rpc.Transaction

/-!
# `Execution.Rpc.GenericTransaction`

The transaction of a call request.

Source: [`transaction.yaml`][tx], at commit `1ca0818` of execution-apis: the fields and their types.

[tx]: https://github.com/ethereum/execution-apis/blob/1ca0818569467cff85b7f41372f22e728d5daa14/src/schemas/transaction.yaml
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Transactions (Access Authorization)

/-- The transaction of a call request, each field none when the request leaves it out.

The methods of `execute.yaml` take it, as do the methods that sign, fill or send a transaction. -/
structure GenericTransaction where
  /-- The type of the transaction. -/
  type : Option UInt8 := none
  /-- The nonce of the sender, which a call does not read. -/
  nonce : Option Nat := none
  /-- The recipient: none, from an absent or `null` field, for a creation. -/
  to : Option Address := none
  /-- The sender, the field `from`, which a request need not sign. -/
  sender : Option Address := none
  /-- The gas limit. -/
  gas : Option Nat := none
  /-- The wei that the transaction sends. -/
  value : Option Nat := none
  /-- The call data, or the init code of a creation. -/
  input : Option ByteArray := none
  /-- The price per gas of a legacy or type 1 transaction. -/
  gasPrice : Option Nat := none
  /-- The most wei per gas that the sender pays above the base fee. -/
  maxPriorityFeePerGas : Option Nat := none
  /-- The most wei per gas that the sender pays in all. -/
  maxFeePerGas : Option Nat := none
  /-- The most wei per blob gas that the sender pays. -/
  maxFeePerBlobGas : Option Nat := none
  /-- The access list of EIP-2930. -/
  accessList : Option (List Access) := none
  /-- The versioned hashes of the blobs of EIP-4844. -/
  blobVersionedHashes : Option (List Cryptography.Kzg.VersionedHash) := none
  /-- The blobs, which a call does not read. -/
  blobs : Option (List ByteArray) := none
  /-- The commitments of the blobs, which a call does not read. -/
  commitments : Option (List ByteArray) := none
  /-- The proofs of the blobs, which a call does not read. -/
  proofs : Option (List ByteArray) := none
  /-- The chain that the transaction is valid on. -/
  chainId : Option Nat := none
  /-- The authorization list of EIP-7702. -/
  authorizationList : Option (List Authorization) := none

/-- The names of the fields of the schema. -/
def genericTransactionFields : List String :=
  ["type", "nonce", "to", "from", "gas", "value", "input", "gasPrice", "maxPriorityFeePerGas",
    "maxFeePerGas", "maxFeePerBlobGas", "accessList", "blobVersionedHashes", "blobs",
    "commitments", "proofs", "chainId", "authorizationList"]

/-- The transaction of a call request, from an object with only the fields of the schema.

A field outside the schema is rejected even when its value is `null`. -/
def genericTransaction (j : Json) : Read GenericTransaction := do
  -- The schema allows no field that it does not name.
  if let .obj kvs := j then
    unless hasOnly kvs.toList genericTransactionFields do
      reject "transaction: a field outside the schema"
  -- Every field is optional, and only `to` may be `null` in the schema.
  --
  -- Here any field of the schema whose value is `null` counts as absent, as for the other readers.
  --
  -- That is a leniency beyond the schema.
  let fs ← fields "transaction" j
  let opt {α : Type} (name : String) (f : String → Json → Read α) : Read (Option α) :=
    (fs.lookup name).mapM (f name)
  -- The type is a byte, and every other number a `uint` with no bound.
  --
  -- A call that runs the request checks the bounds.
  --
  -- The numbers of an authorization are read with the bounds of a signed authorization.
  return {
    type := ← opt "type" byte
    nonce := ← opt "nonce" uint
    to := ← opt "to" address
    sender := ← opt "from" address
    gas := ← opt "gas" uint
    value := ← opt "value" uint
    input := ← opt "input" bytes
    gasPrice := ← opt "gasPrice" uint
    maxPriorityFeePerGas := ← opt "maxPriorityFeePerGas" uint
    maxFeePerGas := ← opt "maxFeePerGas" uint
    maxFeePerBlobGas := ← opt "maxFeePerBlobGas" uint
    accessList := ← opt "accessList" fun what => array what access
    blobVersionedHashes := ← opt "blobVersionedHashes" fun what =>
      array what fun j => Cryptography.Kzg.VersionedHash.mk <$> hash32 "blob hash" j
    blobs := ← opt "blobs" fun what => array what (bytes "blob")
    commitments := ← opt "commitments" fun what => array what (bytes "commitment")
    proofs := ← opt "proofs" fun what => array what (bytes "proof")
    chainId := ← opt "chainId" uint
    authorizationList := ← opt "authorizationList" fun what => array what authorization }

namespace GenericTransaction

/-- Whether the request names a fee per gas: a gas price, a fee cap or a priority fee.

A blob fee cap alone names no fee. -/
def namesFee (tx : GenericTransaction) : Bool :=
  -- A gas price, a fee cap or a priority fee, and not the blob fee cap.
  tx.gasPrice.isSome || tx.maxFeePerGas.isSome || tx.maxPriorityFeePerGas.isSome

/-- The kind of the transaction: its type, else the latest kind whose own fields it has.

A simulation fixes type 2 by default instead, and reads a blob fee cap alone as no kind. -/
def kind (tx : GenericTransaction) : UInt8 :=
  match tx.type with
  -- The type of the request, when it names one.
  | some t => t
  -- Else EthLib's inference, since the source fixes no kind: the latest kind whose fields it has.
  | none =>
    -- An authorization list: type 4, EIP-7702.
    if tx.authorizationList.isSome then 4
    -- Blob hashes or a blob fee cap: type 3, EIP-4844.
    else if tx.blobVersionedHashes.isSome || tx.maxFeePerBlobGas.isSome then 3
    -- A fee cap or a priority fee: type 2, EIP-1559.
    else if tx.maxFeePerGas.isSome || tx.maxPriorityFeePerGas.isSome then 2
    -- An access list: type 1, EIP-2930.
    else if tx.accessList.isSome then 1
    -- Else a legacy transaction.
    else 0

end GenericTransaction

end EthLib.Execution.Rpc

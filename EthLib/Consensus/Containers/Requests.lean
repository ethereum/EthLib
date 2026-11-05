module

public import EthLib.Consensus.Constants
public import EthLib.Consensus.Containers.Builder
public import EthLib.Consensus.Containers.Execution

/-!
# `Consensus.Containers.Requests`

From Electra: the requests that an execution block passes to the beacon chain, and their queues.

[EIP-7685] lets the execution layer pass typed requests to the consensus layer.

[EIP-6110] passes deposits that way, and [EIP-7002] withdrawals and exits.

[EIP-7251] adds consolidations, and queues deposits and partial withdrawals by their balance.

From Gloas the request lists have no limit in their type, as [EIP-7688] specifies.

Gloas also adds the deposit and exit requests of builders, as [EIP-8282] specifies.

The beacon chain asks the execution layer to check a payload with a new payload request.

[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#consensus-layer
[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
[EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002#consensus-layer
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-7688]: https://eips.ethereum.org/EIPS/eip-7688#converted-types
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- A deposit that waits in the queue of the state until the churn lets it in. -/
structure PendingDeposit where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The commitment to the key or address that may withdraw the balance. -/
  withdrawalCredentials : Bytes32
  /-- The amount deposited. -/
  amount : Gwei
  /-- The signature of the deposit message, by the key of the validator. -/
  signature : BLSSignature
  /-- The slot at which the deposit entered the queue. -/
  slot : Slot
  deriving DecidableEq, Repr

instance : SszType PendingDeposit :=
  .container ["pubkey", "withdrawal_credentials", "amount", "signature", "slot"]
    (fun d => (d.pubkey, d.withdrawalCredentials, d.amount, d.signature, d.slot))
    (fun (pubkey, withdrawalCredentials, amount, signature, slot) =>
      ⟨pubkey, withdrawalCredentials, amount, signature, slot⟩)

/-- A withdrawal of part of a balance, waiting until it can be paid. -/
structure PendingPartialWithdrawal where
  /-- The validator. -/
  validatorIndex : ValidatorIndex
  /-- The amount to withdraw. -/
  amount : Gwei
  /-- The epoch from which the amount can be withdrawn. -/
  withdrawableEpoch : Epoch
  deriving DecidableEq, Repr

instance : SszType PendingPartialWithdrawal :=
  .container ["validator_index", "amount", "withdrawable_epoch"]
    (fun w => (w.validatorIndex, w.amount, w.withdrawableEpoch))
    (fun (validatorIndex, amount, withdrawableEpoch) =>
      ⟨validatorIndex, amount, withdrawableEpoch⟩)

/-- A consolidation of one validator into another, waiting until the source can be withdrawn. -/
structure PendingConsolidation where
  /-- The validator whose balance moves. -/
  sourceIndex : ValidatorIndex
  /-- The validator that receives the balance. -/
  targetIndex : ValidatorIndex
  deriving DecidableEq, Repr

instance : SszType PendingConsolidation :=
  .container ["source_index", "target_index"] (fun c => (c.sourceIndex, c.targetIndex))
    (fun (sourceIndex, targetIndex) => ⟨sourceIndex, targetIndex⟩)

/-- A deposit as the execution layer reports it from the logs of the deposit contract. -/
structure DepositRequest where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The commitment to the key or address that may withdraw the balance. -/
  withdrawalCredentials : Bytes32
  /-- The amount deposited. -/
  amount : Gwei
  /-- The signature of the deposit message, by the key of the validator. -/
  signature : BLSSignature
  /-- The index of the deposit in the deposit contract. -/
  index : UInt64
  deriving DecidableEq, Repr

instance : SszType DepositRequest :=
  .container ["pubkey", "withdrawal_credentials", "amount", "signature", "index"]
    (fun d => (d.pubkey, d.withdrawalCredentials, d.amount, d.signature, d.index))
    (fun (pubkey, withdrawalCredentials, amount, signature, index) =>
      ⟨pubkey, withdrawalCredentials, amount, signature, index⟩)

/-- A request, sent from the withdrawal address, to withdraw from a validator or to exit it.

An amount of zero asks for a full exit. -/
structure WithdrawalRequest where
  /-- The address that sent the request. -/
  sourceAddress : ExecutionAddress
  /-- The key of the validator. -/
  validatorPubkey : BLSPubkey
  /-- The amount to withdraw. -/
  amount : Gwei
  deriving DecidableEq, Repr

instance : SszType WithdrawalRequest :=
  .container ["source_address", "validator_pubkey", "amount"]
    (fun r => (r.sourceAddress, r.validatorPubkey, r.amount))
    (fun (sourceAddress, validatorPubkey, amount) => ⟨sourceAddress, validatorPubkey, amount⟩)

/-- A request, sent from the withdrawal address of the source, to move its balance to a target. -/
structure ConsolidationRequest where
  /-- The address that sent the request. -/
  sourceAddress : ExecutionAddress
  /-- The key of the validator whose balance moves. -/
  sourcePubkey : BLSPubkey
  /-- The key of the validator that receives the balance. -/
  targetPubkey : BLSPubkey
  deriving DecidableEq, Repr

instance : SszType ConsolidationRequest :=
  .container ["source_address", "source_pubkey", "target_pubkey"]
    (fun r => (r.sourceAddress, r.sourcePubkey, r.targetPubkey))
    (fun (sourceAddress, sourcePubkey, targetPubkey) => ⟨sourceAddress, sourcePubkey, targetPubkey⟩)

/-- The deposit requests of one execution block. -/
abbrev DepositRequests (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork DepositRequest preset.MAX_DEPOSIT_REQUESTS_PER_PAYLOAD.toNat

/-- The withdrawal requests of one execution block. -/
abbrev WithdrawalRequests (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork WithdrawalRequest preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD.toNat

/-- The consolidation requests of one execution block. -/
abbrev ConsolidationRequests (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork ConsolidationRequest
    preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat

/-- The requests of one execution block, one list for each type. -/
structure ExecutionRequests (preset : Preset) (fork : Fork) where
  /-- The deposit requests. -/
  deposits : DepositRequests preset fork
  /-- The withdrawal requests. -/
  withdrawals : WithdrawalRequests preset fork
  /-- The consolidation requests. -/
  consolidations : ConsolidationRequests preset fork
  /-- From Gloas: the deposit requests of builders. -/
  builderDeposits : Since .glamsterdam fork BuilderDepositRequests
  /-- From Gloas: the exit requests of builders. -/
  builderExits : Since .glamsterdam fork BuilderExitRequests

namespace ExecutionRequests

/-- The names of the fields of the requests at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["deposits", "withdrawals", "consolidations"] ++
  sinceNames .glamsterdam fork ["builder_deposits", "builder_exits"]

/-- From Gloas: the layout of the requests, their five fields in their order. -/
def activeFields : List Bool := [true, true, true, true, true]

instance {preset : Preset} {fork : Fork} : SszType (ExecutionRequests preset fork) :=
  .forkContainer .glamsterdam fork activeFields (names fork)
    (fun r => (r.deposits, r.withdrawals, r.consolidations, r.builderDeposits, r.builderExits))
    (fun (deposits, withdrawals, consolidations, builderDeposits, builderExits) =>
      ⟨deposits, withdrawals, consolidations, builderDeposits, builderExits⟩)

/-- One list of requests: its type, the number of its requests, and its SSZ bytes. -/
structure TypedList where
  /-- The type of the requests. -/
  type : Vector UInt8 1
  /-- The number of requests. -/
  count : Nat
  /-- The SSZ bytes of the list. -/
  bytes : Except Err ByteArray

/-- Each list of the requests with its type, in the order of the types. -/
def typedLists {preset : Preset} {fork : Fork} (requests : ExecutionRequests preset fork) :
    List TypedList :=
  [⟨DEPOSIT_REQUEST_TYPE, requests.deposits.data.size, SszType.serialize requests.deposits⟩,
    ⟨WITHDRAWAL_REQUEST_TYPE, requests.withdrawals.data.size,
      SszType.serialize requests.withdrawals⟩,
    ⟨CONSOLIDATION_REQUEST_TYPE, requests.consolidations.data.size,
      SszType.serialize requests.consolidations⟩] ++
  if gloas : .glamsterdam ≤ fork then
    [⟨BUILDER_DEPOSIT_REQUEST_TYPE, (requests.builderDeposits gloas).data.size,
        SszType.serialize (requests.builderDeposits gloas)⟩,
      ⟨BUILDER_EXIT_REQUEST_TYPE, (requests.builderExits gloas).data.size,
        SszType.serialize (requests.builderExits gloas)⟩]
  else []

end ExecutionRequests

/-- From Electra: the requests as the execution layer receives them, by [EIP-7685].

Each nonempty list gives its type byte followed by its SSZ bytes, in the order of the types.

An empty list gives nothing.

[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#execution-layer -/
def getExecutionRequestsList {preset : Preset} {fork : Fork}
    (requests : ExecutionRequests preset fork) : Except Err (List ByteArray) :=
  (requests.typedLists.filter (·.count != 0)).mapM fun list => do
    return ⟨list.type.toArray⟩ ++ (← list.bytes)

/-- From Deneb: the versioned hashes of the blobs of an execution payload. -/
abbrev VersionedHashes (preset : Preset) :=
  SszList VersionedHash preset.MAX_BLOB_COMMITMENTS_PER_BLOCK.toNat

/-- From Bellatrix: what the beacon chain gives the execution layer to check a payload.

Deneb adds the versioned hashes of the blobs and the root of the parent beacon block.

Electra adds the requests of the payload. -/
structure NewPayloadRequest (preset : Preset) (fork : Fork) where
  /-- The payload. -/
  executionPayload : ExecutionPayload preset fork
  /-- From Deneb: the versioned hashes of the blobs that the payload commits to. -/
  versionedHashes : Since .dencun fork (VersionedHashes preset)
  /-- From Deneb: the root of the parent beacon block. -/
  parentBeaconBlockRoot : Since .dencun fork Root
  /-- From Electra: the requests of the payload. -/
  executionRequests : Since .pectra fork (ExecutionRequests preset fork)

namespace NewPayloadRequest

/-- The names of the fields of a new payload request at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["execution_payload"] ++
  sinceNames .dencun fork ["versioned_hashes", "parent_beacon_block_root"] ++
  sinceNames .pectra fork ["execution_requests"]

/-- From Gloas: the layout of a new payload request, its four fields in their order. -/
def activeFields : List Bool := [true, true, true, true]

instance {preset : Preset} {fork : Fork} : SszType (NewPayloadRequest preset fork) :=
  .forkContainer .glamsterdam fork activeFields (names fork)
    (fun r => (r.executionPayload, r.versionedHashes, r.parentBeaconBlockRoot,
      r.executionRequests))
    (fun (executionPayload, versionedHashes, parentBeaconBlockRoot, executionRequests) =>
      ⟨executionPayload, versionedHashes, parentBeaconBlockRoot, executionRequests⟩)

end NewPayloadRequest

end EthLib.Consensus

module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Containers.Requests`

From Electra: the requests that an execution block passes to the beacon chain, and their queues.

[EIP-7685] lets the execution layer pass typed requests to the consensus layer.

[EIP-6110] passes deposits that way, and [EIP-7002] withdrawals and exits.

[EIP-7251] adds consolidations, and queues deposits and partial withdrawals by their balance.

[EIP-7685]: https://eips.ethereum.org/EIPS/eip-7685#consensus-layer
[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
[EIP-7002]: https://eips.ethereum.org/EIPS/eip-7002#consensus-layer
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer
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

/-- The requests of one execution block, one list for each type. -/
structure ExecutionRequests (preset : Preset) where
  /-- The deposit requests. -/
  deposits : SszList DepositRequest preset.MAX_DEPOSIT_REQUESTS_PER_PAYLOAD.toNat
  /-- The withdrawal requests. -/
  withdrawals : SszList WithdrawalRequest preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD.toNat
  /-- The consolidation requests. -/
  consolidations : SszList ConsolidationRequest preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD.toNat
  deriving DecidableEq

instance {preset : Preset} : SszType (ExecutionRequests preset) :=
  .container ["deposits", "withdrawals", "consolidations"]
    (fun r => (r.deposits, r.withdrawals, r.consolidations))
    (fun (deposits, withdrawals, consolidations) => ⟨deposits, withdrawals, consolidations⟩)

end EthLib.Consensus

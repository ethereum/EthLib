module

public import EthLib.Consensus.Containers.Misc

/-!
# `Consensus.Containers.Builder`

From Gloas: the registry of builders, their payments and withdrawals, and their requests.

A builder stakes ether to sell execution payloads to proposers, apart from the validators.

A bid offers the proposer a value, paid from the balance of the builder.

[EIP-7732] adds the builders, and [EIP-8282] their deposit and exit requests.

On 2026-11-03 both EIPs were in Last Call.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#new-containers
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- A builder in the registry of builders. -/
structure Builder where
  /-- The public key of the builder. -/
  pubkey : BLSPubkey
  /-- The version of the builder. -/
  version : UInt8
  /-- The address that receives the withdrawals of the builder. -/
  executionAddress : ExecutionAddress
  /-- The balance of the builder. -/
  balance : Gwei
  /-- The epoch of the first deposit of the builder. -/
  depositEpoch : Epoch
  /-- The epoch from which the builder can withdraw its balance. -/
  withdrawableEpoch : Epoch
  deriving DecidableEq, Repr

instance : SszType Builder :=
  .container ["pubkey", "version", "execution_address", "balance", "deposit_epoch",
      "withdrawable_epoch"]
    (fun b => (b.pubkey, b.version, b.executionAddress, b.balance, b.depositEpoch,
      b.withdrawableEpoch))
    (fun (pubkey, version, executionAddress, balance, depositEpoch, withdrawableEpoch) =>
      ⟨pubkey, version, executionAddress, balance, depositEpoch, withdrawableEpoch⟩)

/-- An amount that a builder owes, waiting in the queue until it is paid. -/
structure BuilderPendingWithdrawal where
  /-- The address that receives the amount. -/
  feeRecipient : ExecutionAddress
  /-- The amount. -/
  amount : Gwei
  /-- The builder that pays it. -/
  builderIndex : BuilderIndex
  deriving DecidableEq, Repr

instance : SszType BuilderPendingWithdrawal :=
  .container ["fee_recipient", "amount", "builder_index"]
    (fun w => (w.feeRecipient, w.amount, w.builderIndex))
    (fun (feeRecipient, amount, builderIndex) => ⟨feeRecipient, amount, builderIndex⟩)

/-- The payment of a bid, with the attesting balance that supports its block so far.

The payment enters the queue of withdrawals once enough balance supports the block. -/
structure BuilderPendingPayment where
  /-- The effective balance of the attesters that support the block. -/
  weight : Gwei
  /-- The withdrawal that pays the bid. -/
  withdrawal : BuilderPendingWithdrawal
  /-- The proposer of the block. -/
  proposerIndex : ValidatorIndex
  deriving DecidableEq, Repr

instance : SszType BuilderPendingPayment :=
  .container ["weight", "withdrawal", "proposer_index"]
    (fun p => (p.weight, p.withdrawal, p.proposerIndex))
    (fun (weight, withdrawal, proposerIndex) => ⟨weight, withdrawal, proposerIndex⟩)

/-- The payment of no bid: every field is zero. -/
def BuilderPendingPayment.empty : BuilderPendingPayment :=
  ⟨0, ⟨Vector.replicate 20 0, 0, 0⟩, 0⟩

/-- A deposit to a builder, as the execution layer reports it.

It has the fields of a deposit request of a validator, without the index. -/
structure BuilderDepositRequest where
  /-- The public key of the builder. -/
  pubkey : BLSPubkey
  /-- The withdrawal credentials, which name the address of the builder. -/
  withdrawalCredentials : Bytes32
  /-- The amount deposited. -/
  amount : Gwei
  /-- The signature of the deposit message, by the key of the builder. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType BuilderDepositRequest :=
  .container ["pubkey", "withdrawal_credentials", "amount", "signature"]
    (fun d => (d.pubkey, d.withdrawalCredentials, d.amount, d.signature))
    (fun (pubkey, withdrawalCredentials, amount, signature) =>
      ⟨pubkey, withdrawalCredentials, amount, signature⟩)

/-- A request, sent from the address of a builder, to exit that builder. -/
structure BuilderExitRequest where
  /-- The address that sent the request. -/
  sourceAddress : ExecutionAddress
  /-- The key of the builder. -/
  pubkey : BLSPubkey
  deriving DecidableEq, Repr

instance : SszType BuilderExitRequest :=
  .container ["source_address", "pubkey"] (fun r => (r.sourceAddress, r.pubkey))
    (fun (sourceAddress, pubkey) => ⟨sourceAddress, pubkey⟩)

/-- The registry of builders, with no limit on its length. -/
abbrev Builders := ProgressiveList Builder

/-- The queue of builder withdrawals, with no limit on its length. -/
abbrev BuilderPendingWithdrawals := ProgressiveList BuilderPendingWithdrawal

/-- The builder deposit requests of one execution payload, in a list type with no limit. -/
abbrev BuilderDepositRequests := ProgressiveList BuilderDepositRequest

/-- The builder exit requests of one execution payload, in a list type with no limit. -/
abbrev BuilderExitRequests := ProgressiveList BuilderExitRequest

/-- The payments of the bids of the previous epoch, then of the current epoch, one per slot. -/
abbrev BuilderPendingPayments (preset : Preset) :=
  Vector BuilderPendingPayment (2 * preset.SLOTS_PER_EPOCH.toNat)

end EthLib.Consensus

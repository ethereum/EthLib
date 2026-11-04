module

public import EthLib.Base.Hash32
public import EthLib.Consensus.Constants
public import EthLib.Consensus.Preset
public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Ssz.Typed.Collections
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# `Consensus.Containers.Misc`

The small containers of the beacon chain, from Phase 0 on.

They name forks, checkpoints, validators, deposits and block headers.

Each one encodes as an SSZ container of its fields, in declaration order.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The current and previous versions of the fork of a state, and when the current one began. -/
structure ForkVersions where
  /-- The version before the current fork. -/
  previousVersion : Version
  /-- The version of the current fork. -/
  currentVersion : Version
  /-- The epoch at which the current fork began. -/
  epoch : Epoch
  deriving DecidableEq, Repr

instance : SszType ForkVersions :=
  .container ["previous_version", "current_version", "epoch"]
    (fun f => (f.previousVersion, f.currentVersion, f.epoch))
    (fun (previousVersion, currentVersion, epoch) => ⟨previousVersion, currentVersion, epoch⟩)

/-- A checkpoint: a block root at the start of an epoch, as Casper FFG votes for it. -/
structure Checkpoint where
  /-- The epoch of the checkpoint. -/
  epoch : Epoch
  /-- The root of the block at the checkpoint. -/
  root : Root
  deriving DecidableEq, Repr

instance : SszType Checkpoint :=
  .container ["epoch", "root"] (fun c => (c.epoch, c.root))
    (fun (epoch, root) => ⟨epoch, root⟩)

/-- A validator in the registry, with its key, its balance and the epochs of its life. -/
structure Validator where
  /-- The public key that signs for the validator. -/
  pubkey : BLSPubkey
  /-- The commitment to the key or address that may withdraw the balance. -/
  withdrawalCredentials : Bytes32
  /-- The balance that counts for rewards and votes, a whole number of increments. -/
  effectiveBalance : Gwei
  /-- Whether the validator has been slashed. -/
  slashed : Bool
  /-- The epoch at which the validator joined the queue for activation. -/
  activationEligibilityEpoch : Epoch
  /-- The epoch at which the validator became active. -/
  activationEpoch : Epoch
  /-- The epoch at which the validator stops being active. -/
  exitEpoch : Epoch
  /-- The epoch from which the balance can be withdrawn. -/
  withdrawableEpoch : Epoch
  deriving DecidableEq, Repr

instance : SszType Validator :=
  .container ["pubkey", "withdrawal_credentials", "effective_balance", "slashed",
      "activation_eligibility_epoch", "activation_epoch", "exit_epoch", "withdrawable_epoch"]
    (fun v => (v.pubkey, v.withdrawalCredentials, v.effectiveBalance, v.slashed,
      v.activationEligibilityEpoch, v.activationEpoch, v.exitEpoch, v.withdrawableEpoch))
    (fun (pubkey, withdrawalCredentials, effectiveBalance, slashed, activationEligibilityEpoch,
        activationEpoch, exitEpoch, withdrawableEpoch) =>
      ⟨pubkey, withdrawalCredentials, effectiveBalance, slashed, activationEligibilityEpoch,
        activationEpoch, exitEpoch, withdrawableEpoch⟩)

/-- What an attestation votes for: a head block, and a source and target checkpoint. -/
structure AttestationData where
  /-- The slot of the attestation. -/
  slot : Slot
  /-- The committee of the slot that attests.

  From Electra the field is zero, as [EIP-7549] specifies.

  [EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer -/
  index : CommitteeIndex
  /-- The root of the head block, the vote of the fork choice. -/
  beaconBlockRoot : Root
  /-- The source checkpoint of the Casper FFG vote. -/
  source : Checkpoint
  /-- The target checkpoint of the Casper FFG vote. -/
  target : Checkpoint
  deriving DecidableEq, Repr

instance : SszType AttestationData :=
  .container ["slot", "index", "beacon_block_root", "source", "target"]
    (fun a => (a.slot, a.index, a.beaconBlockRoot, a.source, a.target))
    (fun (slot, index, beaconBlockRoot, source, target) =>
      ⟨slot, index, beaconBlockRoot, source, target⟩)

/-- Before Altair: an attestation that a block included, kept until the epoch ends. -/
structure PendingAttestation (preset : Preset) where
  /-- One bit for each member of the committee, set when the member attested. -/
  aggregationBits : Bitlist preset.MAX_VALIDATORS_PER_COMMITTEE.toNat
  /-- What the committee attested to. -/
  data : AttestationData
  /-- The number of slots between the attestation and the block that included it. -/
  inclusionDelay : Slot
  /-- The proposer of the block that included it. -/
  proposerIndex : ValidatorIndex
  deriving DecidableEq

instance {preset : Preset} : SszType (PendingAttestation preset) :=
  .container ["aggregation_bits", "data", "inclusion_delay", "proposer_index"]
    (fun a => (a.aggregationBits, a.data, a.inclusionDelay, a.proposerIndex))
    (fun (aggregationBits, data, inclusionDelay, proposerIndex) =>
      ⟨aggregationBits, data, inclusionDelay, proposerIndex⟩)

/-- A vote on the state of the deposit contract of the execution layer. -/
structure Eth1Data where
  /-- The root of the deposit tree. -/
  depositRoot : Root
  /-- The number of deposits in the tree. -/
  depositCount : UInt64
  /-- The hash of the execution block that the vote reads. -/
  blockHash : Hash32
  deriving DecidableEq, Repr

instance : SszType Eth1Data :=
  .container ["deposit_root", "deposit_count", "block_hash"]
    (fun d => (d.depositRoot, d.depositCount, d.blockHash))
    (fun (depositRoot, depositCount, blockHash) => ⟨depositRoot, depositCount, blockHash⟩)

/-- The block roots and state roots of one span of slots, as the history keeps them. -/
structure HistoricalBatch (preset : Preset) where
  /-- The roots of the blocks, one for each slot of the span. -/
  blockRoots : Vector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  /-- The roots of the states, one for each slot of the span. -/
  stateRoots : Vector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  deriving DecidableEq, Repr

instance {preset : Preset} : SszType (HistoricalBatch preset) :=
  .container ["block_roots", "state_roots"] (fun b => (b.blockRoots, b.stateRoots))
    (fun (blockRoots, stateRoots) => ⟨blockRoots, stateRoots⟩)

/-- The part of a deposit that the depositor signs. -/
structure DepositMessage where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The commitment to the key or address that may withdraw the balance. -/
  withdrawalCredentials : Bytes32
  /-- The amount deposited. -/
  amount : Gwei
  deriving DecidableEq, Repr

instance : SszType DepositMessage :=
  .container ["pubkey", "withdrawal_credentials", "amount"]
    (fun d => (d.pubkey, d.withdrawalCredentials, d.amount))
    (fun (pubkey, withdrawalCredentials, amount) => ⟨pubkey, withdrawalCredentials, amount⟩)

/-- A deposit as the deposit contract records it: the message and its signature. -/
structure DepositData where
  /-- The public key of the validator. -/
  pubkey : BLSPubkey
  /-- The commitment to the key or address that may withdraw the balance. -/
  withdrawalCredentials : Bytes32
  /-- The amount deposited. -/
  amount : Gwei
  /-- The signature of the deposit message, by the key of the validator. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType DepositData :=
  .container ["pubkey", "withdrawal_credentials", "amount", "signature"]
    (fun d => (d.pubkey, d.withdrawalCredentials, d.amount, d.signature))
    (fun (pubkey, withdrawalCredentials, amount, signature) =>
      ⟨pubkey, withdrawalCredentials, amount, signature⟩)

/-- A beacon block with its body replaced by the root of the body. -/
structure BeaconBlockHeader where
  /-- The slot of the block. -/
  slot : Slot
  /-- The validator that proposed the block. -/
  proposerIndex : ValidatorIndex
  /-- The root of the parent block. -/
  parentRoot : Root
  /-- The root of the state after the block. -/
  stateRoot : Root
  /-- The root of the body of the block. -/
  bodyRoot : Root
  deriving DecidableEq, Repr

instance : SszType BeaconBlockHeader :=
  .container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
    (fun h => (h.slot, h.proposerIndex, h.parentRoot, h.stateRoot, h.bodyRoot))
    (fun (slot, proposerIndex, parentRoot, stateRoot, bodyRoot) =>
      ⟨slot, proposerIndex, parentRoot, stateRoot, bodyRoot⟩)

/-- A block header with the signature of its proposer. -/
structure SignedBeaconBlockHeader where
  /-- The header. -/
  message : BeaconBlockHeader
  /-- The signature of the header by its proposer. -/
  signature : BLSSignature
  deriving DecidableEq, Repr

instance : SszType SignedBeaconBlockHeader :=
  .container ["message", "signature"] (fun s => (s.message, s.signature))
    (fun (message, signature) => ⟨message, signature⟩)

/-- The fields of an execution block that a proposer reads to vote on the deposit contract.

A client keeps the other fields of the block too, but they take no part in the vote. -/
structure Eth1Block where
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : UInt64
  /-- The root of the deposit tree after the block. -/
  depositRoot : Root
  /-- The number of deposits after the block. -/
  depositCount : UInt64
  deriving DecidableEq, Repr

instance : SszType Eth1Block :=
  .container ["timestamp", "deposit_root", "deposit_count"]
    (fun b => (b.timestamp, b.depositRoot, b.depositCount))
    (fun (timestamp, depositRoot, depositCount) => ⟨timestamp, depositRoot, depositCount⟩)

/-- From Capella: the roots of the block roots and the state roots of one span of slots. -/
structure HistoricalSummary where
  /-- The root of the block roots of the span. -/
  blockSummaryRoot : Root
  /-- The root of the state roots of the span. -/
  stateSummaryRoot : Root
  deriving DecidableEq, Repr

instance : SszType HistoricalSummary :=
  .container ["block_summary_root", "state_summary_root"]
    (fun s => (s.blockSummaryRoot, s.stateSummaryRoot))
    (fun (blockSummaryRoot, stateSummaryRoot) => ⟨blockSummaryRoot, stateSummaryRoot⟩)

end EthLib.Consensus

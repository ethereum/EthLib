module

public import EthLib.Base.Hash32
public import EthLib.Base.U256
public import EthLib.Consensus.Constants
public import EthLib.Networking.Gossip.Parameters

/-!
# `Consensus.Config`

A configuration fixes the values of one network, such as its genesis and the epochs of its forks.

It holds each value under the name of its source, from Phase 0 to Heze.

The values of Gloas come from EIP-7732, EIP-8061 and EIP-8261, in Last Call on 2026-11-03.

They can change until the EIPs are final.

The values of Heze come from EIP-7805, a Draft on 2026-11-03.

The parameters of the attestation subnets come from the networking layer, which reads them too.

The payload cap is the same on every network, so only the networking layer defines it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- From Fulu: one entry of the blob schedule. -/
structure BlobScheduleEntry where
  /-- The first epoch of the entry. -/
  EPOCH : Epoch
  /-- The most blobs in one block from that epoch on. -/
  MAX_BLOBS_PER_BLOCK : UInt64
  deriving DecidableEq, Repr

/-- From Gloas: one entry of the gas limit schedule. -/
structure GasLimitScheduleEntry where
  /-- The first epoch of the entry. -/
  EPOCH : Epoch
  /-- The gas limit that the schedule recommends from that epoch on. -/
  GAS_LIMIT : UInt64
  deriving DecidableEq, Repr

/-- The values of a configuration, from Phase 0 to Heze. -/
structure Config extends Networking.Gossip.SubnetParameters where
  /-- The name of the preset that the configuration uses. -/
  PRESET_BASE : String
  /-- The name of the configuration. -/
  CONFIG_NAME : String
  /-- From Bellatrix: the total difficulty at which the execution chain stops proof of work. -/
  TERMINAL_TOTAL_DIFFICULTY : U256
  /-- From Bellatrix: the hash of a block that overrides the terminal total difficulty. -/
  TERMINAL_BLOCK_HASH : Hash32
  /-- From Bellatrix: the epoch from which the terminal block hash applies. -/
  TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH : Epoch
  /-- The fewest active validators at genesis. -/
  MIN_GENESIS_ACTIVE_VALIDATOR_COUNT : UInt64
  /-- The earliest time of genesis, in seconds since the Unix epoch. -/
  MIN_GENESIS_TIME : UInt64
  /-- The version of Phase 0. -/
  GENESIS_FORK_VERSION : Version
  /-- The seconds from the block that triggers genesis to genesis. -/
  GENESIS_DELAY : UInt64
  /-- The version of Altair. -/
  ALTAIR_FORK_VERSION : Version
  /-- The first epoch of Altair. -/
  ALTAIR_FORK_EPOCH : Epoch
  /-- The version of Bellatrix. -/
  BELLATRIX_FORK_VERSION : Version
  /-- The first epoch of Bellatrix. -/
  BELLATRIX_FORK_EPOCH : Epoch
  /-- The version of Capella. -/
  CAPELLA_FORK_VERSION : Version
  /-- The first epoch of Capella. -/
  CAPELLA_FORK_EPOCH : Epoch
  /-- The version of Deneb. -/
  DENEB_FORK_VERSION : Version
  /-- The first epoch of Deneb. -/
  DENEB_FORK_EPOCH : Epoch
  /-- The version of Electra. -/
  ELECTRA_FORK_VERSION : Version
  /-- The first epoch of Electra. -/
  ELECTRA_FORK_EPOCH : Epoch
  /-- The version of Fulu. -/
  FULU_FORK_VERSION : Version
  /-- The first epoch of Fulu. -/
  FULU_FORK_EPOCH : Epoch
  /-- The version of Gloas. -/
  GLOAS_FORK_VERSION : Version
  /-- The first epoch of Gloas. -/
  GLOAS_FORK_EPOCH : Epoch
  /-- The version of Heze. -/
  HEZE_FORK_VERSION : Version
  /-- The first epoch of Heze. -/
  HEZE_FORK_EPOCH : Epoch
  /-- The length of a slot, in milliseconds. -/
  SLOT_DURATION_MS : UInt64
  /-- The expected time between two blocks of the deposit chain, in seconds. -/
  SECONDS_PER_ETH1_BLOCK : UInt64
  /-- The fewest epochs from the exit of a validator to its withdrawal. -/
  MIN_VALIDATOR_WITHDRAWABILITY_DELAY : Epoch
  /-- From Gloas: the fewest epochs from the exit of a builder to its withdrawal.

  [EIP-7732](https://eips.ethereum.org/EIPS/eip-7732#time-parameters) defines it. -/
  MIN_BUILDER_WITHDRAWABILITY_DELAY : Epoch
  /-- The fewest epochs from the activation of a validator to its voluntary exit. -/
  SHARD_COMMITTEE_PERIOD : Epoch
  /-- The number of blocks of the deposit chain that a vote on its state stays behind. -/
  ETH1_FOLLOW_DISTANCE : UInt64
  /-- The part of a slot, in basis points, after which a proposer does not reorganize its head. -/
  PROPOSER_REORG_CUTOFF_BPS : UInt64
  /-- The part of a slot, in basis points, at which an attestation is due. -/
  ATTESTATION_DUE_BPS : UInt64
  /-- The part of a slot, in basis points, at which an aggregate is due. -/
  AGGREGATE_DUE_BPS : UInt64
  /-- From Altair: the part of a slot, in basis points, at which a sync committee message is due. -/
  SYNC_MESSAGE_DUE_BPS : UInt64
  /-- From Altair: the part of a slot, in basis points, at which a contribution is due. -/
  CONTRIBUTION_DUE_BPS : UInt64
  /-- From Gloas: the part of a slot, in basis points, at which an attestation is due.

  [EIP-7732](https://eips.ethereum.org/EIPS/eip-7732#fork-choice-changes) gives it. -/
  ATTESTATION_DUE_BPS_GLOAS : UInt64
  /-- From Gloas: the part of a slot, in basis points, at which an aggregate is due. -/
  AGGREGATE_DUE_BPS_GLOAS : UInt64
  /-- From Gloas: the part of a slot, in basis points, at which a sync committee message is due. -/
  SYNC_MESSAGE_DUE_BPS_GLOAS : UInt64
  /-- From Gloas: the part of a slot, in basis points, at which a contribution is due. -/
  CONTRIBUTION_DUE_BPS_GLOAS : UInt64
  /-- From Gloas: the part of a slot, in basis points, by which the payload must be seen. -/
  PAYLOAD_DUE_BPS : UInt64
  /-- From Gloas: the part of a slot, in basis points, at which a payload attestation is due. -/
  PAYLOAD_ATTESTATION_DUE_BPS : UInt64
  /-- From Heze: the part of a slot, in basis points, after which no new inclusion list is stored.

  [EIP-7805](https://eips.ethereum.org/EIPS/eip-7805#validators) puts this deadline at 9 s.

  That is 7500 of a 12-second slot, but both configurations below give 6667, that is 8 s. -/
  INCLUSION_LIST_DUE_BPS : UInt64
  /-- From Altair: the inactivity score that a validator gains in each epoch that it misses. -/
  INACTIVITY_SCORE_BIAS : UInt64
  /-- From Altair: the most inactivity score that a validator loses in an epoch without a leak. -/
  INACTIVITY_SCORE_RECOVERY_RATE : UInt64
  /-- An active validator whose effective balance is at most this amount is ejected. -/
  EJECTION_BALANCE : Gwei
  /-- Before Electra: the smallest churn limit, as a count of validators. -/
  MIN_PER_EPOCH_CHURN_LIMIT : UInt64
  /-- The active validators divided by this give the churn limit, and from Electra their balance. -/
  CHURN_LIMIT_QUOTIENT : UInt64
  /-- In Deneb: the largest churn limit for activations, as a count of validators. -/
  MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT : UInt64
  /-- From Electra: the smallest churn limit, as a balance. -/
  MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA : Gwei
  /-- From Electra: the largest churn limit for activations and exits, as a balance. -/
  MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT : Gwei
  /-- From Gloas: the active balance divided by this gives the churn of activations and exits.

  [EIP-8061](https://eips.ethereum.org/EIPS/eip-8061#configuration) defines it. -/
  CHURN_LIMIT_QUOTIENT_GLOAS : UInt64
  /-- From Gloas: the active balance divided by this gives the churn of consolidations. -/
  CONSOLIDATION_CHURN_LIMIT_QUOTIENT : UInt64
  /-- From Gloas: the largest churn for activations, as a balance.

  The EIP drops the suffix and gives the value as 256 ether, here in Gwei. -/
  MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS : Gwei
  /-- The boost of the weight of a timely proposal, in percent of a committee's weight. -/
  PROPOSER_SCORE_BOOST : UInt64
  /-- A late head is reorganized only below this weight, in percent of a committee's weight. -/
  REORG_HEAD_WEIGHT_THRESHOLD : UInt64
  /-- A late head is reorganized only when its parent weighs more, in percent of a committee. -/
  REORG_PARENT_WEIGHT_THRESHOLD : UInt64
  /-- A late head is reorganized only when finality is at most this many epochs behind. -/
  REORG_MAX_EPOCHS_SINCE_FINALIZATION : Epoch
  /-- The chain ID of the deposit chain. -/
  DEPOSIT_CHAIN_ID : UInt64
  /-- The network ID of the deposit chain. -/
  DEPOSIT_NETWORK_ID : UInt64
  /-- The address of the deposit contract. -/
  DEPOSIT_CONTRACT_ADDRESS : ExecutionAddress
  /-- Before Deneb: the most blocks in one request. -/
  MAX_REQUEST_BLOCKS : UInt64
  /-- The most slots during which an attestation can propagate. -/
  ATTESTATION_PROPAGATION_SLOT_RANGE : Slot
  /-- The largest clock disparity between honest nodes, in milliseconds. -/
  MAXIMUM_GOSSIP_CLOCK_DISPARITY : UInt64
  /-- From Deneb: the most blocks in one request. -/
  MAX_REQUEST_BLOCKS_DENEB : UInt64
  /-- From Deneb: the fewest recent epochs whose blob sidecars a node serves. -/
  MIN_EPOCHS_FOR_BLOB_SIDECARS_REQUESTS : Epoch
  /-- In Deneb: the number of subnets of blob sidecars. -/
  BLOB_SIDECAR_SUBNET_COUNT : UInt64
  /-- In Deneb: the most blobs in one block. -/
  MAX_BLOBS_PER_BLOCK : UInt64
  /-- From Electra: the number of subnets of blob sidecars. -/
  BLOB_SIDECAR_SUBNET_COUNT_ELECTRA : UInt64
  /-- From Electra: the most blobs in one block, until the blob schedule sets another limit. -/
  MAX_BLOBS_PER_BLOCK_ELECTRA : UInt64
  /-- From Fulu: the number of custody groups. -/
  NUMBER_OF_CUSTODY_GROUPS : UInt64
  /-- From Fulu: the number of subnets of data column sidecars. -/
  DATA_COLUMN_SIDECAR_SUBNET_COUNT : UInt64
  /-- From Fulu: the fewest samples that an honest node takes in one slot. -/
  SAMPLES_PER_SLOT : UInt64
  /-- From Fulu: the fewest custody groups of an honest node. -/
  CUSTODY_REQUIREMENT : UInt64
  /-- From Fulu: the fewest custody groups of an honest node with validators attached. -/
  VALIDATOR_CUSTODY_REQUIREMENT : UInt64
  /-- From Fulu: the balance of attached validators that adds one custody group. -/
  BALANCE_PER_ADDITIONAL_CUSTODY_GROUP : Gwei
  /-- From Fulu: the fewest recent epochs whose data column sidecars a node serves. -/
  MIN_EPOCHS_FOR_DATA_COLUMN_SIDECARS_REQUESTS : Epoch
  /-- From Gloas: the most execution payload envelopes in one request. -/
  MAX_REQUEST_PAYLOADS : UInt64
  /-- From Heze: the most inclusion lists in one request. -/
  MAX_REQUEST_INCLUSION_LIST : UInt64
  /-- From Heze: the fewest recent slots whose inclusion lists a node serves. -/
  MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS : Slot
  /-- From Heze: the most bytes of the transactions of one inclusion list.

  [EIP-7805] names it `MAX_BYTES_PER_INCLUSION_LIST`.

  [EIP-7805]: https://eips.ethereum.org/EIPS/eip-7805#il-building -/
  MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST : UInt64
  /-- From Fulu: the limits of blobs from given epochs, as EIP-7892 allows. -/
  BLOB_SCHEDULE : List BlobScheduleEntry
  /-- From Gloas: the gas limits that the schedule recommends from given epochs.

  It adds no validity rule.

  [EIP-8261](https://eips.ethereum.org/EIPS/eip-8261#gas-limit-schedule) defines it. -/
  GAS_LIMIT_SCHEDULE : List GasLimitScheduleEntry
  /-- The largest share of Byzantine validators, in percent, that fast confirmation assumes. -/
  CONFIRMATION_BYZANTINE_THRESHOLD : UInt64
  deriving DecidableEq, Repr

namespace Config

/-- The configuration of mainnet. -/
def mainnet : Config where
  PRESET_BASE := "mainnet"
  CONFIG_NAME := "mainnet"
  TERMINAL_TOTAL_DIFFICULTY := 58750000000000000000000
  TERMINAL_BLOCK_HASH := Vector.replicate 32 0
  TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH := FAR_FUTURE_EPOCH
  MIN_GENESIS_ACTIVE_VALIDATOR_COUNT := 2 ^ 14
  MIN_GENESIS_TIME := 1606824000
  GENESIS_FORK_VERSION := #v[0x00, 0x00, 0x00, 0x00]
  GENESIS_DELAY := 604800
  ALTAIR_FORK_VERSION := #v[0x01, 0x00, 0x00, 0x00]
  ALTAIR_FORK_EPOCH := 74240
  BELLATRIX_FORK_VERSION := #v[0x02, 0x00, 0x00, 0x00]
  BELLATRIX_FORK_EPOCH := 144896
  CAPELLA_FORK_VERSION := #v[0x03, 0x00, 0x00, 0x00]
  CAPELLA_FORK_EPOCH := 194048
  DENEB_FORK_VERSION := #v[0x04, 0x00, 0x00, 0x00]
  DENEB_FORK_EPOCH := 269568
  ELECTRA_FORK_VERSION := #v[0x05, 0x00, 0x00, 0x00]
  ELECTRA_FORK_EPOCH := 364032
  FULU_FORK_VERSION := #v[0x06, 0x00, 0x00, 0x00]
  FULU_FORK_EPOCH := 411392
  GLOAS_FORK_VERSION := #v[0x07, 0x00, 0x00, 0x00]
  GLOAS_FORK_EPOCH := FAR_FUTURE_EPOCH
  HEZE_FORK_VERSION := #v[0x08, 0x00, 0x00, 0x00]
  HEZE_FORK_EPOCH := FAR_FUTURE_EPOCH
  SLOT_DURATION_MS := 12000
  SECONDS_PER_ETH1_BLOCK := 14
  MIN_VALIDATOR_WITHDRAWABILITY_DELAY := 2 ^ 8
  MIN_BUILDER_WITHDRAWABILITY_DELAY := 2 ^ 6
  SHARD_COMMITTEE_PERIOD := 2 ^ 8
  ETH1_FOLLOW_DISTANCE := 2 ^ 11
  PROPOSER_REORG_CUTOFF_BPS := 1667
  ATTESTATION_DUE_BPS := 3333
  AGGREGATE_DUE_BPS := 6667
  SYNC_MESSAGE_DUE_BPS := 3333
  CONTRIBUTION_DUE_BPS := 6667
  ATTESTATION_DUE_BPS_GLOAS := 2500
  AGGREGATE_DUE_BPS_GLOAS := 5000
  SYNC_MESSAGE_DUE_BPS_GLOAS := 2500
  CONTRIBUTION_DUE_BPS_GLOAS := 5000
  PAYLOAD_DUE_BPS := 5000
  PAYLOAD_ATTESTATION_DUE_BPS := 7500
  INCLUSION_LIST_DUE_BPS := 6667
  INACTIVITY_SCORE_BIAS := 2 ^ 2
  INACTIVITY_SCORE_RECOVERY_RATE := 2 ^ 4
  EJECTION_BALANCE := 2 ^ 4 * 10 ^ 9
  MIN_PER_EPOCH_CHURN_LIMIT := 2 ^ 2
  CHURN_LIMIT_QUOTIENT := 2 ^ 16
  MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT := 2 ^ 3
  MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA := 2 ^ 7 * 10 ^ 9
  MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := 2 ^ 8 * 10 ^ 9
  CHURN_LIMIT_QUOTIENT_GLOAS := 2 ^ 15
  CONSOLIDATION_CHURN_LIMIT_QUOTIENT := 2 ^ 16
  MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS := 2 ^ 8 * 10 ^ 9
  PROPOSER_SCORE_BOOST := 40
  REORG_HEAD_WEIGHT_THRESHOLD := 20
  REORG_PARENT_WEIGHT_THRESHOLD := 160
  REORG_MAX_EPOCHS_SINCE_FINALIZATION := 2
  DEPOSIT_CHAIN_ID := 1
  DEPOSIT_NETWORK_ID := 1
  DEPOSIT_CONTRACT_ADDRESS := #v[0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40, 0x35, 0x6c,
    0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30, 0x3d, 0x77, 0x05, 0xfa]
  MAX_REQUEST_BLOCKS := 2 ^ 10
  EPOCHS_PER_SUBNET_SUBSCRIPTION := 2 ^ 8
  ATTESTATION_PROPAGATION_SLOT_RANGE := 32
  MAXIMUM_GOSSIP_CLOCK_DISPARITY := 500
  SUBNETS_PER_NODE := 2
  ATTESTATION_SUBNET_COUNT := 2 ^ 6
  ATTESTATION_SUBNET_EXTRA_BITS := 0
  MAX_REQUEST_BLOCKS_DENEB := 2 ^ 7
  MIN_EPOCHS_FOR_BLOB_SIDECARS_REQUESTS := 2 ^ 12
  BLOB_SIDECAR_SUBNET_COUNT := 6
  MAX_BLOBS_PER_BLOCK := 6
  BLOB_SIDECAR_SUBNET_COUNT_ELECTRA := 9
  MAX_BLOBS_PER_BLOCK_ELECTRA := 9
  NUMBER_OF_CUSTODY_GROUPS := 128
  DATA_COLUMN_SIDECAR_SUBNET_COUNT := 2 ^ 7
  SAMPLES_PER_SLOT := 8
  CUSTODY_REQUIREMENT := 4
  VALIDATOR_CUSTODY_REQUIREMENT := 8
  BALANCE_PER_ADDITIONAL_CUSTODY_GROUP := 32 * 10 ^ 9
  MIN_EPOCHS_FOR_DATA_COLUMN_SIDECARS_REQUESTS := 2 ^ 12
  MAX_REQUEST_PAYLOADS := 2 ^ 7
  MAX_REQUEST_INCLUSION_LIST := 2 ^ 4
  MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS := 1
  MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST := 2 ^ 13
  BLOB_SCHEDULE := [⟨412672, 15⟩, ⟨419072, 21⟩]
  GAS_LIMIT_SCHEDULE := []
  CONFIRMATION_BYZANTINE_THRESHOLD := 25

/-- The minimal configuration, which the minimal preset uses for tests. -/
def minimal : Config :=
  { mainnet with
    PRESET_BASE := "minimal"
    CONFIG_NAME := "minimal"
    TERMINAL_TOTAL_DIFFICULTY :=
      115792089237316195423570985008687907853269984665640564039457584007913129638912
    MIN_GENESIS_ACTIVE_VALIDATOR_COUNT := 64
    MIN_GENESIS_TIME := 1578009600
    GENESIS_FORK_VERSION := #v[0x00, 0x00, 0x00, 0x01]
    GENESIS_DELAY := 300
    ALTAIR_FORK_VERSION := #v[0x01, 0x00, 0x00, 0x01]
    ALTAIR_FORK_EPOCH := FAR_FUTURE_EPOCH
    BELLATRIX_FORK_VERSION := #v[0x02, 0x00, 0x00, 0x01]
    BELLATRIX_FORK_EPOCH := FAR_FUTURE_EPOCH
    CAPELLA_FORK_VERSION := #v[0x03, 0x00, 0x00, 0x01]
    CAPELLA_FORK_EPOCH := FAR_FUTURE_EPOCH
    DENEB_FORK_VERSION := #v[0x04, 0x00, 0x00, 0x01]
    DENEB_FORK_EPOCH := FAR_FUTURE_EPOCH
    ELECTRA_FORK_VERSION := #v[0x05, 0x00, 0x00, 0x01]
    ELECTRA_FORK_EPOCH := FAR_FUTURE_EPOCH
    FULU_FORK_VERSION := #v[0x06, 0x00, 0x00, 0x01]
    FULU_FORK_EPOCH := FAR_FUTURE_EPOCH
    GLOAS_FORK_VERSION := #v[0x07, 0x00, 0x00, 0x01]
    HEZE_FORK_VERSION := #v[0x08, 0x00, 0x00, 0x01]
    SLOT_DURATION_MS := 6000
    MIN_BUILDER_WITHDRAWABILITY_DELAY := 2
    SHARD_COMMITTEE_PERIOD := 64
    ETH1_FOLLOW_DISTANCE := 16
    MIN_PER_EPOCH_CHURN_LIMIT := 2
    CHURN_LIMIT_QUOTIENT := 32
    MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT := 4
    MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA := 64000000000
    MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := 128000000000
    CHURN_LIMIT_QUOTIENT_GLOAS := 16
    CONSOLIDATION_CHURN_LIMIT_QUOTIENT := 32
    MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS := 128000000000
    DEPOSIT_CHAIN_ID := 5
    DEPOSIT_NETWORK_ID := 5
    DEPOSIT_CONTRACT_ADDRESS := #v[0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, 0x78, 0x90,
      0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, 0x78, 0x90]
    BLOB_SCHEDULE := [] }

end Config

end EthLib.Consensus

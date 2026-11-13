module

public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.ForkSchedule
public import EthLib.Consensus.Preset
public import EthLib.Networking.ReqResp.Encoding

/-!
# `Consensus.BeaconApi.Config`

The answers of the Beacon API that describe the chain.

They are the spec map, the fork schedule, the deposit contract and the genesis.

The [spec endpoint] maps the names of the constants, the presets and the configuration to values.

EthLib gives the presets and the configuration only.

It writes a value that starts with `0x` as hex, and a number as a quoted integer.

It writes a list as an array.

Its example writes an entry of the blob schedule as an object of quoted integers.

The [fork schedule endpoint] returns every fork that the node knows, as `Fork` containers.

The [deposit contract endpoint] returns the chain ID and the address of the deposit contract.

The [genesis endpoint] returns the genesis time, the root of the genesis validators and a version.

EthLib gives the genesis version of the configuration.

SOUNDNESS.md records the points that the source leaves open.

[spec endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/config/spec.yaml
[fork schedule endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/config/fork_schedule.yaml
[deposit contract endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/config/deposit_contract.yaml
[genesis endpoint]: https://github.com/ethereum/beacon-APIs/blob/7911555e6a30c51f9b69bb168111a59f1ff8ee49/apis/beacon/genesis.yaml
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Base Serialization.Ssz

/-! ## The spec map -/

/-- A value of the configuration or of a preset, as the spec map writes it. -/
inductive SpecValue where
  /-- An integer, of any size. -/
  | int (value : Nat)
  /-- A byte string. -/
  | bytes (value : List UInt8)
  /-- A text, such as the name of a preset. -/
  | text (value : String)
  /-- A list of values. -/
  | list (items : List SpecValue)
  /-- An entry of a schedule: an integer under each of its names. -/
  | entry (fields : List (String × Nat))
  deriving Inhabited

/-- How a type of the configuration or of a preset gives its value in the spec map. -/
class ToSpecValue (α : Type) where
  /-- The value in the spec map. -/
  spec : α → SpecValue

export ToSpecValue (spec)

instance : ToSpecValue UInt64 := ⟨fun n => .int n.toNat⟩
instance : ToSpecValue U256 := ⟨fun n => .int n.toNat⟩
instance {n : Nat} : ToSpecValue (Vector UInt8 n) := ⟨fun bytes => .bytes bytes.toList⟩
instance : ToSpecValue String := ⟨.text⟩
instance {α : Type} [ToSpecValue α] : ToSpecValue (List α) := ⟨fun items => .list (items.map spec)⟩

instance : ToSpecValue BlobScheduleEntry :=
  ⟨fun entry => .entry [("EPOCH", entry.EPOCH.toNat),
    ("MAX_BLOBS_PER_BLOCK", entry.MAX_BLOBS_PER_BLOCK.toNat)]⟩

instance : ToSpecValue GasLimitScheduleEntry :=
  ⟨fun entry => .entry [("EPOCH", entry.EPOCH.toNat), ("GAS_LIMIT", entry.GAS_LIMIT.toNat)]⟩

/-- The JSON of a value in the spec map.

An integer is a quoted decimal integer, and a byte string is lowercase hex after `0x`.

A list is an array, and an entry of a schedule is an object. -/
def specValueJson : SpecValue → Json
  | .int value => .str (toString value)
  | .bytes value => .str (hexString value)
  | .text value => .str value
  | .list items => .arr (items.map specValueJson).toArray
  | .entry fields => Json.mkObj (fields.map fun (name, value) => (name, .str (toString value)))

/-- Each value of a preset under its name, with the four values that it derives from the others. -/
def presetEntries (preset : Preset) : List (String × SpecValue) := [
  ("MAX_COMMITTEES_PER_SLOT", spec preset.MAX_COMMITTEES_PER_SLOT),
  ("TARGET_COMMITTEE_SIZE", spec preset.TARGET_COMMITTEE_SIZE),
  ("MAX_VALIDATORS_PER_COMMITTEE", spec preset.MAX_VALIDATORS_PER_COMMITTEE),
  ("SHUFFLE_ROUND_COUNT", spec preset.SHUFFLE_ROUND_COUNT),
  ("HYSTERESIS_QUOTIENT", spec preset.HYSTERESIS_QUOTIENT),
  ("HYSTERESIS_DOWNWARD_MULTIPLIER", spec preset.HYSTERESIS_DOWNWARD_MULTIPLIER),
  ("HYSTERESIS_UPWARD_MULTIPLIER", spec preset.HYSTERESIS_UPWARD_MULTIPLIER),
  ("MIN_DEPOSIT_AMOUNT", spec preset.MIN_DEPOSIT_AMOUNT),
  ("MAX_EFFECTIVE_BALANCE", spec preset.MAX_EFFECTIVE_BALANCE),
  ("EFFECTIVE_BALANCE_INCREMENT", spec preset.EFFECTIVE_BALANCE_INCREMENT),
  ("MIN_ATTESTATION_INCLUSION_DELAY", spec preset.MIN_ATTESTATION_INCLUSION_DELAY),
  ("SLOTS_PER_EPOCH", spec preset.SLOTS_PER_EPOCH),
  ("MIN_SEED_LOOKAHEAD", spec preset.MIN_SEED_LOOKAHEAD),
  ("MAX_SEED_LOOKAHEAD", spec preset.MAX_SEED_LOOKAHEAD),
  ("EPOCHS_PER_ETH1_VOTING_PERIOD", spec preset.EPOCHS_PER_ETH1_VOTING_PERIOD),
  ("SLOTS_PER_HISTORICAL_ROOT", spec preset.SLOTS_PER_HISTORICAL_ROOT),
  ("MIN_EPOCHS_TO_INACTIVITY_PENALTY", spec preset.MIN_EPOCHS_TO_INACTIVITY_PENALTY),
  ("EPOCHS_PER_HISTORICAL_VECTOR", spec preset.EPOCHS_PER_HISTORICAL_VECTOR),
  ("EPOCHS_PER_SLASHINGS_VECTOR", spec preset.EPOCHS_PER_SLASHINGS_VECTOR),
  ("HISTORICAL_ROOTS_LIMIT", spec preset.HISTORICAL_ROOTS_LIMIT),
  ("VALIDATOR_REGISTRY_LIMIT", spec preset.VALIDATOR_REGISTRY_LIMIT),
  ("BASE_REWARD_FACTOR", spec preset.BASE_REWARD_FACTOR),
  ("WHISTLEBLOWER_REWARD_QUOTIENT", spec preset.WHISTLEBLOWER_REWARD_QUOTIENT),
  ("PROPOSER_REWARD_QUOTIENT", spec preset.PROPOSER_REWARD_QUOTIENT),
  ("INACTIVITY_PENALTY_QUOTIENT", spec preset.INACTIVITY_PENALTY_QUOTIENT),
  ("MIN_SLASHING_PENALTY_QUOTIENT", spec preset.MIN_SLASHING_PENALTY_QUOTIENT),
  ("PROPORTIONAL_SLASHING_MULTIPLIER", spec preset.PROPORTIONAL_SLASHING_MULTIPLIER),
  ("MAX_PROPOSER_SLASHINGS", spec preset.MAX_PROPOSER_SLASHINGS),
  ("MAX_ATTESTER_SLASHINGS", spec preset.MAX_ATTESTER_SLASHINGS),
  ("MAX_ATTESTATIONS", spec preset.MAX_ATTESTATIONS),
  ("MAX_DEPOSITS", spec preset.MAX_DEPOSITS),
  ("MAX_VOLUNTARY_EXITS", spec preset.MAX_VOLUNTARY_EXITS),
  ("INACTIVITY_PENALTY_QUOTIENT_ALTAIR", spec preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR),
  ("MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR", spec preset.MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR),
  ("PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR", spec preset.PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR),
  ("SYNC_COMMITTEE_SIZE", spec preset.SYNC_COMMITTEE_SIZE),
  ("EPOCHS_PER_SYNC_COMMITTEE_PERIOD", spec preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD),
  ("MIN_SYNC_COMMITTEE_PARTICIPANTS", spec preset.MIN_SYNC_COMMITTEE_PARTICIPANTS),
  ("INACTIVITY_PENALTY_QUOTIENT_BELLATRIX", spec preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX),
  ("MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX", spec preset.MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX),
  ("PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX",
    spec preset.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX),
  ("MAX_BYTES_PER_TRANSACTION", spec preset.MAX_BYTES_PER_TRANSACTION),
  ("MAX_TRANSACTIONS_PER_PAYLOAD", spec preset.MAX_TRANSACTIONS_PER_PAYLOAD),
  ("BYTES_PER_LOGS_BLOOM", spec preset.BYTES_PER_LOGS_BLOOM),
  ("MAX_EXTRA_DATA_BYTES", spec preset.MAX_EXTRA_DATA_BYTES),
  ("MAX_BLS_TO_EXECUTION_CHANGES", spec preset.MAX_BLS_TO_EXECUTION_CHANGES),
  ("MAX_WITHDRAWALS_PER_PAYLOAD", spec preset.MAX_WITHDRAWALS_PER_PAYLOAD),
  ("MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP", spec preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP),
  ("MAX_BLOB_COMMITMENTS_PER_BLOCK", spec preset.MAX_BLOB_COMMITMENTS_PER_BLOCK),
  ("KZG_COMMITMENT_INCLUSION_PROOF_DEPTH", spec preset.KZG_COMMITMENT_INCLUSION_PROOF_DEPTH),
  ("FIELD_ELEMENTS_PER_BLOB", spec preset.FIELD_ELEMENTS_PER_BLOB),
  ("MIN_ACTIVATION_BALANCE", spec preset.MIN_ACTIVATION_BALANCE),
  ("MAX_EFFECTIVE_BALANCE_ELECTRA", spec preset.MAX_EFFECTIVE_BALANCE_ELECTRA),
  ("MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA", spec preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA),
  ("WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA", spec preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA),
  ("PENDING_DEPOSITS_LIMIT", spec preset.PENDING_DEPOSITS_LIMIT),
  ("PENDING_PARTIAL_WITHDRAWALS_LIMIT", spec preset.PENDING_PARTIAL_WITHDRAWALS_LIMIT),
  ("PENDING_CONSOLIDATIONS_LIMIT", spec preset.PENDING_CONSOLIDATIONS_LIMIT),
  ("MAX_ATTESTER_SLASHINGS_ELECTRA", spec preset.MAX_ATTESTER_SLASHINGS_ELECTRA),
  ("MAX_ATTESTATIONS_ELECTRA", spec preset.MAX_ATTESTATIONS_ELECTRA),
  ("MAX_DEPOSIT_REQUESTS_PER_PAYLOAD", spec preset.MAX_DEPOSIT_REQUESTS_PER_PAYLOAD),
  ("MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD", spec preset.MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD),
  ("MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD", spec preset.MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD),
  ("MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP",
    spec preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP),
  ("MAX_PENDING_DEPOSITS_PER_EPOCH", spec preset.MAX_PENDING_DEPOSITS_PER_EPOCH),
  ("KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH", spec preset.KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH),
  ("FIELD_ELEMENTS_PER_CELL", spec preset.FIELD_ELEMENTS_PER_CELL),
  ("PTC_SIZE", spec preset.PTC_SIZE),
  ("MAX_PAYLOAD_ATTESTATIONS", spec preset.MAX_PAYLOAD_ATTESTATIONS),
  ("MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD",
    spec preset.MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD),
  ("MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD", spec preset.MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD),
  ("MAX_BUILDERS_PER_WITHDRAWALS_SWEEP", spec preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP),
  ("MAX_SIGNED_AGGREGATE_AND_PROOF_SIZE", spec preset.MAX_SIGNED_AGGREGATE_AND_PROOF_SIZE),
  ("MAX_ATTESTER_SLASHING_SIZE", spec preset.MAX_ATTESTER_SLASHING_SIZE),
  ("MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE", spec preset.MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE),
  ("INCLUSION_LIST_COMMITTEE_SIZE", spec preset.INCLUSION_LIST_COMMITTEE_SIZE),
  ("MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE_HEZE",
    spec preset.MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE_HEZE),
  ("MAX_SIGNED_INCLUSION_LIST_SIZE", spec preset.MAX_SIGNED_INCLUSION_LIST_SIZE),
  ("UPDATE_TIMEOUT", spec preset.UPDATE_TIMEOUT),
  ("FIELD_ELEMENTS_PER_EXT_BLOB", spec preset.FIELD_ELEMENTS_PER_EXT_BLOB),
  ("CELLS_PER_EXT_BLOB", spec preset.CELLS_PER_EXT_BLOB),
  ("NUMBER_OF_COLUMNS", spec preset.NUMBER_OF_COLUMNS)]

/-- Each value of a configuration under its name, with the payload cap that every network shares. -/
def configEntries (config : Config) : List (String × SpecValue) := [
  ("EPOCHS_PER_SUBNET_SUBSCRIPTION", spec config.EPOCHS_PER_SUBNET_SUBSCRIPTION),
  ("SUBNETS_PER_NODE", spec config.SUBNETS_PER_NODE),
  ("ATTESTATION_SUBNET_COUNT", spec config.ATTESTATION_SUBNET_COUNT),
  ("ATTESTATION_SUBNET_EXTRA_BITS", spec config.ATTESTATION_SUBNET_EXTRA_BITS),
  ("PRESET_BASE", spec config.PRESET_BASE),
  ("CONFIG_NAME", spec config.CONFIG_NAME),
  ("TERMINAL_TOTAL_DIFFICULTY", spec config.TERMINAL_TOTAL_DIFFICULTY),
  ("TERMINAL_BLOCK_HASH", spec config.TERMINAL_BLOCK_HASH),
  ("TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH", spec config.TERMINAL_BLOCK_HASH_ACTIVATION_EPOCH),
  ("MIN_GENESIS_ACTIVE_VALIDATOR_COUNT", spec config.MIN_GENESIS_ACTIVE_VALIDATOR_COUNT),
  ("MIN_GENESIS_TIME", spec config.MIN_GENESIS_TIME),
  ("GENESIS_FORK_VERSION", spec config.GENESIS_FORK_VERSION),
  ("GENESIS_DELAY", spec config.GENESIS_DELAY),
  ("ALTAIR_FORK_VERSION", spec config.ALTAIR_FORK_VERSION),
  ("ALTAIR_FORK_EPOCH", spec config.ALTAIR_FORK_EPOCH),
  ("BELLATRIX_FORK_VERSION", spec config.BELLATRIX_FORK_VERSION),
  ("BELLATRIX_FORK_EPOCH", spec config.BELLATRIX_FORK_EPOCH),
  ("CAPELLA_FORK_VERSION", spec config.CAPELLA_FORK_VERSION),
  ("CAPELLA_FORK_EPOCH", spec config.CAPELLA_FORK_EPOCH),
  ("DENEB_FORK_VERSION", spec config.DENEB_FORK_VERSION),
  ("DENEB_FORK_EPOCH", spec config.DENEB_FORK_EPOCH),
  ("ELECTRA_FORK_VERSION", spec config.ELECTRA_FORK_VERSION),
  ("ELECTRA_FORK_EPOCH", spec config.ELECTRA_FORK_EPOCH),
  ("FULU_FORK_VERSION", spec config.FULU_FORK_VERSION),
  ("FULU_FORK_EPOCH", spec config.FULU_FORK_EPOCH),
  ("GLOAS_FORK_VERSION", spec config.GLOAS_FORK_VERSION),
  ("GLOAS_FORK_EPOCH", spec config.GLOAS_FORK_EPOCH),
  ("HEZE_FORK_VERSION", spec config.HEZE_FORK_VERSION),
  ("HEZE_FORK_EPOCH", spec config.HEZE_FORK_EPOCH),
  ("SLOT_DURATION_MS", spec config.SLOT_DURATION_MS),
  ("SECONDS_PER_ETH1_BLOCK", spec config.SECONDS_PER_ETH1_BLOCK),
  ("MIN_VALIDATOR_WITHDRAWABILITY_DELAY", spec config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY),
  ("MIN_BUILDER_WITHDRAWABILITY_DELAY", spec config.MIN_BUILDER_WITHDRAWABILITY_DELAY),
  ("SHARD_COMMITTEE_PERIOD", spec config.SHARD_COMMITTEE_PERIOD),
  ("ETH1_FOLLOW_DISTANCE", spec config.ETH1_FOLLOW_DISTANCE),
  ("PROPOSER_REORG_CUTOFF_BPS", spec config.PROPOSER_REORG_CUTOFF_BPS),
  ("ATTESTATION_DUE_BPS", spec config.ATTESTATION_DUE_BPS),
  ("AGGREGATE_DUE_BPS", spec config.AGGREGATE_DUE_BPS),
  ("SYNC_MESSAGE_DUE_BPS", spec config.SYNC_MESSAGE_DUE_BPS),
  ("CONTRIBUTION_DUE_BPS", spec config.CONTRIBUTION_DUE_BPS),
  ("ATTESTATION_DUE_BPS_GLOAS", spec config.ATTESTATION_DUE_BPS_GLOAS),
  ("AGGREGATE_DUE_BPS_GLOAS", spec config.AGGREGATE_DUE_BPS_GLOAS),
  ("SYNC_MESSAGE_DUE_BPS_GLOAS", spec config.SYNC_MESSAGE_DUE_BPS_GLOAS),
  ("CONTRIBUTION_DUE_BPS_GLOAS", spec config.CONTRIBUTION_DUE_BPS_GLOAS),
  ("PAYLOAD_DUE_BPS", spec config.PAYLOAD_DUE_BPS),
  ("PAYLOAD_ATTESTATION_DUE_BPS", spec config.PAYLOAD_ATTESTATION_DUE_BPS),
  ("INCLUSION_LIST_DUE_BPS", spec config.INCLUSION_LIST_DUE_BPS),
  ("INACTIVITY_SCORE_BIAS", spec config.INACTIVITY_SCORE_BIAS),
  ("INACTIVITY_SCORE_RECOVERY_RATE", spec config.INACTIVITY_SCORE_RECOVERY_RATE),
  ("EJECTION_BALANCE", spec config.EJECTION_BALANCE),
  ("MIN_PER_EPOCH_CHURN_LIMIT", spec config.MIN_PER_EPOCH_CHURN_LIMIT),
  ("CHURN_LIMIT_QUOTIENT", spec config.CHURN_LIMIT_QUOTIENT),
  ("MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT", spec config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT),
  ("MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA", spec config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA),
  ("MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT",
    spec config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT),
  ("CHURN_LIMIT_QUOTIENT_GLOAS", spec config.CHURN_LIMIT_QUOTIENT_GLOAS),
  ("CONSOLIDATION_CHURN_LIMIT_QUOTIENT", spec config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT),
  ("MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS",
    spec config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS),
  ("PROPOSER_SCORE_BOOST", spec config.PROPOSER_SCORE_BOOST),
  ("REORG_HEAD_WEIGHT_THRESHOLD", spec config.REORG_HEAD_WEIGHT_THRESHOLD),
  ("REORG_PARENT_WEIGHT_THRESHOLD", spec config.REORG_PARENT_WEIGHT_THRESHOLD),
  ("REORG_MAX_EPOCHS_SINCE_FINALIZATION", spec config.REORG_MAX_EPOCHS_SINCE_FINALIZATION),
  ("DEPOSIT_CHAIN_ID", spec config.DEPOSIT_CHAIN_ID),
  ("DEPOSIT_NETWORK_ID", spec config.DEPOSIT_NETWORK_ID),
  ("DEPOSIT_CONTRACT_ADDRESS", spec config.DEPOSIT_CONTRACT_ADDRESS),
  ("MAX_REQUEST_BLOCKS", spec config.MAX_REQUEST_BLOCKS),
  ("ATTESTATION_PROPAGATION_SLOT_RANGE", spec config.ATTESTATION_PROPAGATION_SLOT_RANGE),
  ("MAXIMUM_GOSSIP_CLOCK_DISPARITY", spec config.MAXIMUM_GOSSIP_CLOCK_DISPARITY),
  ("MAX_REQUEST_BLOCKS_DENEB", spec config.MAX_REQUEST_BLOCKS_DENEB),
  ("MIN_EPOCHS_FOR_BLOB_SIDECARS_REQUESTS", spec config.MIN_EPOCHS_FOR_BLOB_SIDECARS_REQUESTS),
  ("BLOB_SIDECAR_SUBNET_COUNT", spec config.BLOB_SIDECAR_SUBNET_COUNT),
  ("MAX_BLOBS_PER_BLOCK", spec config.MAX_BLOBS_PER_BLOCK),
  ("BLOB_SIDECAR_SUBNET_COUNT_ELECTRA", spec config.BLOB_SIDECAR_SUBNET_COUNT_ELECTRA),
  ("MAX_BLOBS_PER_BLOCK_ELECTRA", spec config.MAX_BLOBS_PER_BLOCK_ELECTRA),
  ("NUMBER_OF_CUSTODY_GROUPS", spec config.NUMBER_OF_CUSTODY_GROUPS),
  ("DATA_COLUMN_SIDECAR_SUBNET_COUNT", spec config.DATA_COLUMN_SIDECAR_SUBNET_COUNT),
  ("SAMPLES_PER_SLOT", spec config.SAMPLES_PER_SLOT),
  ("CUSTODY_REQUIREMENT", spec config.CUSTODY_REQUIREMENT),
  ("VALIDATOR_CUSTODY_REQUIREMENT", spec config.VALIDATOR_CUSTODY_REQUIREMENT),
  ("BALANCE_PER_ADDITIONAL_CUSTODY_GROUP", spec config.BALANCE_PER_ADDITIONAL_CUSTODY_GROUP),
  ("MIN_EPOCHS_FOR_DATA_COLUMN_SIDECARS_REQUESTS",
    spec config.MIN_EPOCHS_FOR_DATA_COLUMN_SIDECARS_REQUESTS),
  ("MAX_REQUEST_PAYLOADS", spec config.MAX_REQUEST_PAYLOADS),
  ("MAX_REQUEST_INCLUSION_LIST", spec config.MAX_REQUEST_INCLUSION_LIST),
  ("MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS", spec config.MIN_SLOTS_FOR_INCLUSION_LISTS_REQUESTS),
  ("MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST",
    spec config.MAX_TRANSACTIONS_BYTES_PER_INCLUSION_LIST),
  ("BLOB_SCHEDULE", spec config.BLOB_SCHEDULE),
  ("GAS_LIMIT_SCHEDULE", spec config.GAS_LIMIT_SCHEDULE),
  ("CONFIRMATION_BYZANTINE_THRESHOLD", spec config.CONFIRMATION_BYZANTINE_THRESHOLD),
  ("MAX_PAYLOAD_SIZE", spec Networking.ReqResp.MAX_PAYLOAD_SIZE)]

/-- The spec map of a configuration and a preset: each value under the name of the source. -/
def specMap (config : Config) (preset : Preset) : List (String × Json) :=
  (configEntries config ++ presetEntries preset).map fun (name, value) =>
    (name, specValueJson value)

/-! ## The fork schedule -/

/-- The entry of the fork schedule for the consensus fork after a fork, if there is one.

It holds the version of the fork, the version of the next fork, and the epoch of the next fork. -/
def nextForkEntry (config : Config) (fork : Fork) : Option ForkVersions :=
  (config.nextFork fork).map fun (next, epoch) =>
    { previousVersion := config.forkVersion fork
      currentVersion := config.forkVersion next
      epoch }

/-- The consensus forks before Heze, in order: those that have a next fork. -/
def forksBeforeHeze : List Fork :=
  [.phase0, .altair, .bellatrix, .shapella, .dencun, .pectra, .fusaka, .glamsterdam]

/-- The fork schedule of a configuration, Phase 0 first.

The entry of Phase 0 has the genesis version as both versions, and epoch 0.

Each later consensus fork up to Heze follows, with the version before it and its fork epoch.

A fork at the farthest epoch is listed too. -/
def forkSchedule (config : Config) : List ForkVersions :=
  { previousVersion := config.GENESIS_FORK_VERSION
    currentVersion := config.GENESIS_FORK_VERSION
    epoch := 0 } :: forksBeforeHeze.filterMap (nextForkEntry config)

/-! ## The deposit contract and the genesis -/

/-- The chain of the deposit contract, and its address. -/
structure DepositContract where
  /-- The ID of the chain that holds the contract. -/
  chainId : UInt64
  /-- The address of the contract. -/
  address : ExecutionAddress
  deriving DecidableEq, Repr

instance : SszType DepositContract :=
  .container ["chain_id", "address"] (fun d => (d.chainId, d.address))
    (fun (chainId, address) => ⟨chainId, address⟩)

instance : ApiSpelling DepositContract := .unmarked

/-- The deposit contract of a configuration. -/
def depositContract (config : Config) : DepositContract :=
  { chainId := config.DEPOSIT_CHAIN_ID, address := config.DEPOSIT_CONTRACT_ADDRESS }

/-- The genesis of the chain: its time, the root of its validators and its fork version. -/
structure GenesisInfo where
  /-- The time of the genesis, in seconds. -/
  genesisTime : UInt64
  /-- The root of the validators at the genesis. -/
  genesisValidatorsRoot : Root
  /-- The version of the fork at the genesis. -/
  genesisForkVersion : Version
  deriving DecidableEq, Repr

instance : SszType GenesisInfo :=
  .container ["genesis_time", "genesis_validators_root", "genesis_fork_version"]
    (fun g => (g.genesisTime, g.genesisValidatorsRoot, g.genesisForkVersion))
    (fun (genesisTime, genesisValidatorsRoot, genesisForkVersion) =>
      ⟨genesisTime, genesisValidatorsRoot, genesisForkVersion⟩)

instance : ApiSpelling GenesisInfo := .unmarked

/-- The genesis of the chain: the time and the root of its genesis state, and the genesis version.

The version is the one of the configuration, which the domain of a deposit also uses. -/
def genesisInfo {preset : Preset} {fork : Fork} (config : Config)
    (state : BeaconState preset fork) : GenesisInfo :=
  { genesisTime := state.genesisTime
    genesisValidatorsRoot := state.genesisValidatorsRoot
    genesisForkVersion := config.GENESIS_FORK_VERSION }

end EthLib.Consensus.BeaconApi

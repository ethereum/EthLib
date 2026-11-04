module

public import EthLib.Base.Fork
public import EthLib.Consensus.Types

/-!
# `Consensus.Preset`

A preset fixes the values that differ between modes of operation, such as mainnet and testing.

It holds each value under the name of its source, so a value that a fork replaces has two fields.

The parameters at a fork take, for each such value, the field in force at that fork.

The values of Gloas come from EIP-7732 and EIP-8282, in Last Call on 2026-11-03, and EIP-7688.

EIP-7688 was in Review then, and it asks for the three message size bounds without fixing them.

The values of Heze come from EIP-7805, a Draft then, and the same request of EIP-7688.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- The values of a preset, from Phase 0 to Heze. -/
structure Preset where
  /-- The most committees in one slot. -/
  MAX_COMMITTEES_PER_SLOT : UInt64
  /-- The committee size that the assignment of committees aims for. -/
  TARGET_COMMITTEE_SIZE : UInt64
  /-- The most validators in one committee. -/
  MAX_VALIDATORS_PER_COMMITTEE : UInt64
  /-- The number of rounds of the shuffle. -/
  SHUFFLE_ROUND_COUNT : UInt64
  /-- The balance increment divided by this is one step of hysteresis. -/
  HYSTERESIS_QUOTIENT : UInt64
  /-- A balance more than this many steps below the effective balance lowers it. -/
  HYSTERESIS_DOWNWARD_MULTIPLIER : UInt64
  /-- A balance more than this many steps above the effective balance raises it. -/
  HYSTERESIS_UPWARD_MULTIPLIER : UInt64
  /-- The smallest amount of a deposit. -/
  MIN_DEPOSIT_AMOUNT : Gwei
  /-- The largest effective balance of a validator before Electra. -/
  MAX_EFFECTIVE_BALANCE : Gwei
  /-- Each effective balance is a multiple of this amount. -/
  EFFECTIVE_BALANCE_INCREMENT : Gwei
  /-- The fewest slots from the slot of an attestation to the block that includes it. -/
  MIN_ATTESTATION_INCLUSION_DELAY : Slot
  /-- The number of slots in one epoch. -/
  SLOTS_PER_EPOCH : Slot
  /-- The committees of an epoch are fixed at least this many epochs before it starts. -/
  MIN_SEED_LOOKAHEAD : Epoch
  /-- An activation or an exit takes effect one more than this many epochs after the current one. -/
  MAX_SEED_LOOKAHEAD : Epoch
  /-- The number of epochs in one period of votes on the state of the deposit contract. -/
  EPOCHS_PER_ETH1_VOTING_PERIOD : Epoch
  /-- The number of recent block roots and state roots that the state keeps. -/
  SLOTS_PER_HISTORICAL_ROOT : Slot
  /-- The inactivity leak starts when finality lags the previous epoch by more than this. -/
  MIN_EPOCHS_TO_INACTIVITY_PENALTY : Epoch
  /-- The number of recent epochs whose RANDAO mix the state keeps. -/
  EPOCHS_PER_HISTORICAL_VECTOR : Epoch
  /-- The number of recent epochs whose slashed balance the state keeps. -/
  EPOCHS_PER_SLASHINGS_VECTOR : Epoch
  /-- The most historical roots that the state can hold. -/
  HISTORICAL_ROOTS_LIMIT : UInt64
  /-- The most validators that the registry can hold. -/
  VALIDATOR_REGISTRY_LIMIT : UInt64
  /-- The factor that scales the base reward. -/
  BASE_REWARD_FACTOR : UInt64
  /-- Before Electra: the slashed effective balance divided by this is the whistleblower reward. -/
  WHISTLEBLOWER_REWARD_QUOTIENT : UInt64
  /-- In Phase 0: a reward divided by this is the share of the block proposer. -/
  PROPOSER_REWARD_QUOTIENT : UInt64
  /-- In Phase 0: the divisor of the inactivity penalty.

  [EIP-2982](https://eips.ethereum.org/EIPS/eip-2982#initial-punitive-parameters) sets it low. -/
  INACTIVITY_PENALTY_QUOTIENT : UInt64
  /-- In Phase 0: the effective balance divided by this is the first penalty of a slashing. -/
  MIN_SLASHING_PENALTY_QUOTIENT : UInt64
  /-- In Phase 0: the factor of the total slashed balance in the penalty of a slashing. -/
  PROPORTIONAL_SLASHING_MULTIPLIER : UInt64
  /-- The most proposer slashings in one block. -/
  MAX_PROPOSER_SLASHINGS : UInt64
  /-- Before Electra: the most attester slashings in one block. -/
  MAX_ATTESTER_SLASHINGS : UInt64
  /-- Before Electra: the most attestations in one block. -/
  MAX_ATTESTATIONS : UInt64
  /-- The most deposits in one block. -/
  MAX_DEPOSITS : UInt64
  /-- The most voluntary exits in one block. -/
  MAX_VOLUNTARY_EXITS : UInt64
  /-- In Altair: the divisor of the inactivity penalty. -/
  INACTIVITY_PENALTY_QUOTIENT_ALTAIR : UInt64
  /-- In Altair: the effective balance divided by this is the first penalty of a slashing. -/
  MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR : UInt64
  /-- In Altair: the factor of the total slashed balance in the penalty of a slashing. -/
  PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR : UInt64
  /-- From Altair: the number of members of a sync committee. -/
  SYNC_COMMITTEE_SIZE : UInt64
  /-- From Altair: the number of epochs that one sync committee serves. -/
  EPOCHS_PER_SYNC_COMMITTEE_PERIOD : Epoch
  /-- From Altair: a light client accepts an update only with at least this many signers. -/
  MIN_SYNC_COMMITTEE_PARTICIPANTS : UInt64
  /-- From Bellatrix: the divisor of the inactivity penalty. -/
  INACTIVITY_PENALTY_QUOTIENT_BELLATRIX : UInt64
  /-- From Bellatrix to Deneb: the effective balance divided by this is the first penalty. -/
  MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX : UInt64
  /-- From Bellatrix: the factor of the total slashed balance in the penalty of a slashing. -/
  PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX : UInt64
  /-- From Bellatrix: the most bytes in one transaction of an execution payload. -/
  MAX_BYTES_PER_TRANSACTION : UInt64
  /-- From Bellatrix: the most transactions in one execution payload. -/
  MAX_TRANSACTIONS_PER_PAYLOAD : UInt64
  /-- From Bellatrix: the number of bytes of the logs bloom of an execution payload. -/
  BYTES_PER_LOGS_BLOOM : UInt64
  /-- From Bellatrix: the most bytes of extra data in an execution payload. -/
  MAX_EXTRA_DATA_BYTES : UInt64
  /-- From Capella: the most changes of withdrawal credentials in one block. -/
  MAX_BLS_TO_EXECUTION_CHANGES : UInt64
  /-- From Capella: the most withdrawals in one execution payload. -/
  MAX_WITHDRAWALS_PER_PAYLOAD : UInt64
  /-- From Capella: the most validators that one sweep for withdrawals reads. -/
  MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP : UInt64
  /-- From Deneb: the most blob commitments in one block. -/
  MAX_BLOB_COMMITMENTS_PER_BLOCK : UInt64
  /-- From Deneb: the depth of the proof that one blob commitment is in a block body. -/
  KZG_COMMITMENT_INCLUSION_PROOF_DEPTH : UInt64
  /-- From Deneb: the number of field elements in a blob. -/
  FIELD_ELEMENTS_PER_BLOB : UInt64
  /-- From Electra: the balance that activates a validator.

  It is also the largest effective balance without compounding.

  [EIP-7251](https://eips.ethereum.org/EIPS/eip-7251#consensus-layer) defines it. -/
  MIN_ACTIVATION_BALANCE : Gwei
  /-- From Electra: the largest effective balance of a compounding validator.

  [EIP-7251](https://eips.ethereum.org/EIPS/eip-7251#consensus-layer) defines it. -/
  MAX_EFFECTIVE_BALANCE_ELECTRA : Gwei
  /-- From Electra: the effective balance divided by this is the first penalty of a slashing. -/
  MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA : UInt64
  /-- From Electra: the slashed effective balance divided by this is the whistleblower reward. -/
  WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA : UInt64
  /-- From Electra: the most pending deposits that the state can hold. -/
  PENDING_DEPOSITS_LIMIT : UInt64
  /-- From Electra: the most pending partial withdrawals that the state can hold. -/
  PENDING_PARTIAL_WITHDRAWALS_LIMIT : UInt64
  /-- From Electra: the most pending consolidations that the state can hold. -/
  PENDING_CONSOLIDATIONS_LIMIT : UInt64
  /-- From Electra: the most attester slashings in one block.

  [EIP-7549](https://eips.ethereum.org/EIPS/eip-7549#max_attester_slashings-value) lowers it. -/
  MAX_ATTESTER_SLASHINGS_ELECTRA : UInt64
  /-- From Electra: the most attestations in one block.

  [EIP-7549](https://eips.ethereum.org/EIPS/eip-7549#max_attestations-value) lowers it. -/
  MAX_ATTESTATIONS_ELECTRA : UInt64
  /-- From Electra: the most deposit requests in one execution payload. -/
  MAX_DEPOSIT_REQUESTS_PER_PAYLOAD : UInt64
  /-- From Electra: the most withdrawal requests in one execution payload. -/
  MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD : UInt64
  /-- From Electra: the most consolidation requests in one execution payload. -/
  MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD : UInt64
  /-- From Electra: the most pending partial withdrawals that one sweep processes. -/
  MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP : UInt64
  /-- From Electra: the most pending deposits that one epoch processes. -/
  MAX_PENDING_DEPOSITS_PER_EPOCH : UInt64
  /-- From Fulu: the depth of the proof that the list of blob commitments is in a block body. -/
  KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH : UInt64
  /-- From Fulu: the number of field elements in a cell. -/
  FIELD_ELEMENTS_PER_CELL : UInt64
  /-- From Gloas: the number of members of the payload timeliness committee of a slot.

  [EIP-7732](https://eips.ethereum.org/EIPS/eip-7732#misc-1) defines it. -/
  PTC_SIZE : UInt64
  /-- From Gloas: the most payload attestations in one block. -/
  MAX_PAYLOAD_ATTESTATIONS : UInt64
  /-- From Gloas: the most builder deposit requests in one execution payload. -/
  MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD : UInt64
  /-- From Gloas: the most builder exit requests in one execution payload. -/
  MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD : UInt64
  /-- From Gloas: the most builders that one sweep for withdrawals reads. -/
  MAX_BUILDERS_PER_WITHDRAWALS_SWEEP : UInt64
  /-- From Gloas: the most bytes of a signed aggregate with its proof, before compression.

  A list without a limit does not bound the size of the message, so a constant does.

  [EIP-7688](https://eips.ethereum.org/EIPS/eip-7688#network-message-size-bounds) asks for it. -/
  MAX_SIGNED_AGGREGATE_AND_PROOF_SIZE : UInt64
  /-- From Gloas: the most bytes of an attester slashing, before compression. -/
  MAX_ATTESTER_SLASHING_SIZE : UInt64
  /-- From Gloas: the most bytes of a signed execution payload bid, before compression. -/
  MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE : UInt64
  /-- From Heze: the number of members of the inclusion list committee of a slot.

  [EIP-7805](https://eips.ethereum.org/EIPS/eip-7805#preset) names it `IL_COMMITTEE_SIZE`. -/
  INCLUSION_LIST_COMMITTEE_SIZE : UInt64
  /-- From Heze: the most bytes of a signed execution payload bid, which carries inclusion bits. -/
  MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE_HEZE : UInt64
  /-- From Heze: the most bytes of a signed inclusion list, before compression. -/
  MAX_SIGNED_INCLUSION_LIST_SIZE : UInt64
  deriving DecidableEq, Repr

namespace Preset

variable (preset : Preset)

/-- From Altair: one period of sync committees, in slots.

A light client forces its best update when its finalized header is older than this. -/
def UPDATE_TIMEOUT : Slot := preset.SLOTS_PER_EPOCH * preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD

/-- From Fulu: the number of field elements in an extended blob, twice those of a blob. -/
def FIELD_ELEMENTS_PER_EXT_BLOB : UInt64 := 2 * preset.FIELD_ELEMENTS_PER_BLOB

/-- From Fulu: the number of cells in an extended blob. -/
def CELLS_PER_EXT_BLOB : UInt64 :=
  preset.FIELD_ELEMENTS_PER_EXT_BLOB / preset.FIELD_ELEMENTS_PER_CELL

/-- From Fulu: the number of columns of the matrix of extended blobs, one for each cell. -/
def NUMBER_OF_COLUMNS : UInt64 := preset.CELLS_PER_EXT_BLOB

/-- The mainnet preset. -/
def mainnet : Preset where
  MAX_COMMITTEES_PER_SLOT := 2 ^ 6
  TARGET_COMMITTEE_SIZE := 2 ^ 7
  MAX_VALIDATORS_PER_COMMITTEE := 2 ^ 11
  SHUFFLE_ROUND_COUNT := 90
  HYSTERESIS_QUOTIENT := 4
  HYSTERESIS_DOWNWARD_MULTIPLIER := 1
  HYSTERESIS_UPWARD_MULTIPLIER := 5
  MIN_DEPOSIT_AMOUNT := 2 ^ 0 * 10 ^ 9
  MAX_EFFECTIVE_BALANCE := 2 ^ 5 * 10 ^ 9
  EFFECTIVE_BALANCE_INCREMENT := 2 ^ 0 * 10 ^ 9
  MIN_ATTESTATION_INCLUSION_DELAY := 2 ^ 0
  SLOTS_PER_EPOCH := 2 ^ 5
  MIN_SEED_LOOKAHEAD := 2 ^ 0
  MAX_SEED_LOOKAHEAD := 2 ^ 2
  EPOCHS_PER_ETH1_VOTING_PERIOD := 2 ^ 6
  SLOTS_PER_HISTORICAL_ROOT := 2 ^ 13
  MIN_EPOCHS_TO_INACTIVITY_PENALTY := 2 ^ 2
  EPOCHS_PER_HISTORICAL_VECTOR := 2 ^ 16
  EPOCHS_PER_SLASHINGS_VECTOR := 2 ^ 13
  HISTORICAL_ROOTS_LIMIT := 2 ^ 24
  VALIDATOR_REGISTRY_LIMIT := 2 ^ 40
  BASE_REWARD_FACTOR := 2 ^ 6
  WHISTLEBLOWER_REWARD_QUOTIENT := 2 ^ 9
  PROPOSER_REWARD_QUOTIENT := 2 ^ 3
  INACTIVITY_PENALTY_QUOTIENT := 2 ^ 26
  MIN_SLASHING_PENALTY_QUOTIENT := 2 ^ 7
  PROPORTIONAL_SLASHING_MULTIPLIER := 1
  MAX_PROPOSER_SLASHINGS := 2 ^ 4
  MAX_ATTESTER_SLASHINGS := 2 ^ 1
  MAX_ATTESTATIONS := 2 ^ 7
  MAX_DEPOSITS := 2 ^ 4
  MAX_VOLUNTARY_EXITS := 2 ^ 4
  INACTIVITY_PENALTY_QUOTIENT_ALTAIR := 3 * 2 ^ 24
  MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR := 2 ^ 6
  PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR := 2
  SYNC_COMMITTEE_SIZE := 2 ^ 9
  EPOCHS_PER_SYNC_COMMITTEE_PERIOD := 2 ^ 8
  MIN_SYNC_COMMITTEE_PARTICIPANTS := 1
  INACTIVITY_PENALTY_QUOTIENT_BELLATRIX := 2 ^ 24
  MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX := 2 ^ 5
  PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX := 3
  MAX_BYTES_PER_TRANSACTION := 2 ^ 30
  MAX_TRANSACTIONS_PER_PAYLOAD := 2 ^ 20
  BYTES_PER_LOGS_BLOOM := 2 ^ 8
  MAX_EXTRA_DATA_BYTES := 2 ^ 5
  MAX_BLS_TO_EXECUTION_CHANGES := 2 ^ 4
  MAX_WITHDRAWALS_PER_PAYLOAD := 2 ^ 4
  MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP := 2 ^ 14
  MAX_BLOB_COMMITMENTS_PER_BLOCK := 2 ^ 12
  KZG_COMMITMENT_INCLUSION_PROOF_DEPTH := 17
  FIELD_ELEMENTS_PER_BLOB := 4096
  MIN_ACTIVATION_BALANCE := 2 ^ 5 * 10 ^ 9
  MAX_EFFECTIVE_BALANCE_ELECTRA := 2 ^ 11 * 10 ^ 9
  MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA := 2 ^ 12
  WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA := 2 ^ 12
  PENDING_DEPOSITS_LIMIT := 2 ^ 27
  PENDING_PARTIAL_WITHDRAWALS_LIMIT := 2 ^ 27
  PENDING_CONSOLIDATIONS_LIMIT := 2 ^ 18
  MAX_ATTESTER_SLASHINGS_ELECTRA := 2 ^ 0
  MAX_ATTESTATIONS_ELECTRA := 2 ^ 3
  MAX_DEPOSIT_REQUESTS_PER_PAYLOAD := 2 ^ 13
  MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD := 2 ^ 4
  MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD := 2 ^ 1
  MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP := 2 ^ 3
  MAX_PENDING_DEPOSITS_PER_EPOCH := 2 ^ 4
  KZG_COMMITMENTS_INCLUSION_PROOF_DEPTH := 4
  FIELD_ELEMENTS_PER_CELL := 64
  PTC_SIZE := 2 ^ 9
  MAX_PAYLOAD_ATTESTATIONS := 2 ^ 2
  MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD := 2 ^ 6
  MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD := 2 ^ 4
  MAX_BUILDERS_PER_WITHDRAWALS_SWEEP := 2 ^ 14
  MAX_SIGNED_AGGREGATE_AND_PROOF_SIZE := 16829
  MAX_ATTESTER_SLASHING_SIZE := 2097616
  MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE := 196932
  INCLUSION_LIST_COMMITTEE_SIZE := 2 ^ 4
  MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE_HEZE := 196934
  MAX_SIGNED_INCLUSION_LIST_SIZE := 41112

/-- The minimal preset, which shrinks the mainnet preset for tests. -/
def minimal : Preset :=
  { mainnet with
    MAX_COMMITTEES_PER_SLOT := 2 ^ 2
    TARGET_COMMITTEE_SIZE := 2 ^ 2
    SHUFFLE_ROUND_COUNT := 10
    SLOTS_PER_EPOCH := 2 ^ 3
    EPOCHS_PER_ETH1_VOTING_PERIOD := 2 ^ 2
    SLOTS_PER_HISTORICAL_ROOT := 2 ^ 6
    EPOCHS_PER_HISTORICAL_VECTOR := 2 ^ 6
    EPOCHS_PER_SLASHINGS_VECTOR := 2 ^ 6
    INACTIVITY_PENALTY_QUOTIENT := 2 ^ 25
    MIN_SLASHING_PENALTY_QUOTIENT := 2 ^ 6
    PROPORTIONAL_SLASHING_MULTIPLIER := 2
    SYNC_COMMITTEE_SIZE := 2 ^ 5
    EPOCHS_PER_SYNC_COMMITTEE_PERIOD := 2 ^ 3
    MAX_WITHDRAWALS_PER_PAYLOAD := 2 ^ 2
    MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP := 2 ^ 4
    PENDING_PARTIAL_WITHDRAWALS_LIMIT := 2 ^ 6
    PENDING_CONSOLIDATIONS_LIMIT := 2 ^ 6
    MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP := 2 ^ 1
    PTC_SIZE := 2 ^ 4
    MAX_BUILDERS_PER_WITHDRAWALS_SWEEP := 2 ^ 4
    MAX_SIGNED_AGGREGATE_AND_PROOF_SIZE := 1462
    MAX_ATTESTER_SLASHING_SIZE := 131536 }

end Preset

/-- The values of a preset that a fork replaces, as they stand at one fork. -/
structure Parameters where
  /-- The divisor of the inactivity penalty. -/
  INACTIVITY_PENALTY_QUOTIENT : UInt64
  /-- The effective balance divided by this is the first penalty of a slashing. -/
  MIN_SLASHING_PENALTY_QUOTIENT : UInt64
  /-- The factor of the total slashed balance in the penalty of a slashing. -/
  PROPORTIONAL_SLASHING_MULTIPLIER : UInt64
  /-- The slashed effective balance divided by this is the whistleblower reward. -/
  WHISTLEBLOWER_REWARD_QUOTIENT : UInt64
  /-- The most attester slashings in one block. -/
  MAX_ATTESTER_SLASHINGS : UInt64
  /-- The most attestations in one block. -/
  MAX_ATTESTATIONS : UInt64
  /-- From Gloas: the most bytes of a signed execution payload bid, before compression.

  Before Gloas no block has a bid, and the value is that of Gloas. -/
  MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE : UInt64
  deriving DecidableEq, Repr

/-- The parameters of a preset at a fork.

Altair and Bellatrix raise the penalties of inactivity and slashing in two steps.

Electra lowers the first penalty of a slashing and the whistleblower reward.

Electra also lowers the most attestations and attester slashings in one block.

An attestation can then cover every committee of a slot, so it grows.

[EIP-7549](https://eips.ethereum.org/EIPS/eip-7549#rationale) gives these limits.

Heze adds the inclusion bits of EIP-7805 to the bid, so its signed form grows by two bytes. -/
def parameters (preset : Preset) (fork : Fork) : Parameters where
  INACTIVITY_PENALTY_QUOTIENT :=
    if fork ≥ .bellatrix then preset.INACTIVITY_PENALTY_QUOTIENT_BELLATRIX
    else if fork ≥ .altair then preset.INACTIVITY_PENALTY_QUOTIENT_ALTAIR
    else preset.INACTIVITY_PENALTY_QUOTIENT
  MIN_SLASHING_PENALTY_QUOTIENT :=
    if fork ≥ .pectra then preset.MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA
    else if fork ≥ .bellatrix then preset.MIN_SLASHING_PENALTY_QUOTIENT_BELLATRIX
    else if fork ≥ .altair then preset.MIN_SLASHING_PENALTY_QUOTIENT_ALTAIR
    else preset.MIN_SLASHING_PENALTY_QUOTIENT
  PROPORTIONAL_SLASHING_MULTIPLIER :=
    if fork ≥ .bellatrix then preset.PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX
    else if fork ≥ .altair then preset.PROPORTIONAL_SLASHING_MULTIPLIER_ALTAIR
    else preset.PROPORTIONAL_SLASHING_MULTIPLIER
  WHISTLEBLOWER_REWARD_QUOTIENT :=
    if fork ≥ .pectra then preset.WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA
    else preset.WHISTLEBLOWER_REWARD_QUOTIENT
  MAX_ATTESTER_SLASHINGS :=
    if fork ≥ .pectra then preset.MAX_ATTESTER_SLASHINGS_ELECTRA
    else preset.MAX_ATTESTER_SLASHINGS
  MAX_ATTESTATIONS :=
    if fork ≥ .pectra then preset.MAX_ATTESTATIONS_ELECTRA else preset.MAX_ATTESTATIONS
  MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE :=
    if fork ≥ .hegota then preset.MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE_HEZE
    else preset.MAX_SIGNED_EXECUTION_PAYLOAD_BID_SIZE

end EthLib.Consensus

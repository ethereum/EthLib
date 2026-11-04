module

public import EthLib.Base.Hash32
public import EthLib.Base.U256
public import EthLib.Consensus.Types

/-!
# `Consensus.Constants`

The constants of the beacon chain: values that no preset, configuration or fork changes.

Each constant keeps the name and the type of its source.

A constant that a fork adds names that fork.
-/

@[expose] public section

namespace EthLib.Consensus

/-- The largest 64-bit unsigned integer, `2^64 - 1`. -/
def UINT64_MAX : UInt64 := UInt64.ofNat (2 ^ 64 - 1)

/-- The integer square root of the largest 64-bit unsigned integer, `2^32 - 1`. -/
def UINT64_MAX_SQRT : UInt64 := 4294967295

/-- The number of Gwei in one ether. -/
def ETH_TO_GWEI : UInt64 := 10 ^ 9

/-- The weak subjectivity period tolerates this loss, in percent, of the safety margin of finality.

An attack on the period then has a margin of at least `1/3 - SAFETY_DECAY/100`. -/
def SAFETY_DECAY : UInt64 := 10

/-- The number of basis points in a whole, which fork choice measures parts of a slot in. -/
def BASIS_POINTS : UInt64 := 10000

/-- The number of aggregators that each committee aims to select. -/
def TARGET_AGGREGATORS_PER_COMMITTEE : UInt64 := 16

/-- The most requests that a node sends at once under one request and response protocol. -/
def MAX_CONCURRENT_REQUESTS : UInt64 := 2

/-- The slot of genesis. -/
def GENESIS_SLOT : Slot := 0

/-- The epoch of genesis. -/
def GENESIS_EPOCH : Epoch := 0

/-- The epoch that stands for "never", `2^64 - 1`. -/
def FAR_FUTURE_EPOCH : Epoch := UInt64.ofNat (2 ^ 64 - 1)

/-- The number of parts of the base reward of a validator in Phase 0. -/
def BASE_REWARDS_PER_EPOCH : UInt64 := 4

/-- The number of recent epochs whose justification the state records. -/
def JUSTIFICATION_BITS_LENGTH : UInt64 := 4

/-- The depth of the Merkle tree of deposits in the deposit contract. -/
def DEPOSIT_CONTRACT_TREE_DEPTH : UInt64 := 32

/-- The first byte of withdrawal credentials that hash a BLS public key. -/
def BLS_WITHDRAWAL_PREFIX : Vector UInt8 1 := #v[0x00]

/-- The first byte of withdrawal credentials that name an execution address. -/
def ETH1_ADDRESS_WITHDRAWAL_PREFIX : Vector UInt8 1 := #v[0x01]

/-- The domain type of a block proposal. -/
def DOMAIN_BEACON_PROPOSER : DomainType := #v[0x00, 0x00, 0x00, 0x00]

/-- The domain type of an attestation. -/
def DOMAIN_BEACON_ATTESTER : DomainType := #v[0x01, 0x00, 0x00, 0x00]

/-- The domain type of a RANDAO reveal. -/
def DOMAIN_RANDAO : DomainType := #v[0x02, 0x00, 0x00, 0x00]

/-- The domain type of a deposit. -/
def DOMAIN_DEPOSIT : DomainType := #v[0x03, 0x00, 0x00, 0x00]

/-- The domain type of a voluntary exit. -/
def DOMAIN_VOLUNTARY_EXIT : DomainType := #v[0x04, 0x00, 0x00, 0x00]

/-- The domain type of the proof that selects an aggregator. -/
def DOMAIN_SELECTION_PROOF : DomainType := #v[0x05, 0x00, 0x00, 0x00]

/-- The domain type of an aggregate with its selection proof. -/
def DOMAIN_AGGREGATE_AND_PROOF : DomainType := #v[0x06, 0x00, 0x00, 0x00]

/-- The bits of a domain type that applications reserve.

A domain type of an application has one of these bits set, and every other domain type has none. -/
def DOMAIN_APPLICATION_MASK : DomainType := #v[0x00, 0x00, 0x00, 0x01]

/-- From Altair: the index of the flag of a timely source vote. -/
def TIMELY_SOURCE_FLAG_INDEX : UInt64 := 0

/-- From Altair: the index of the flag of a timely target vote. -/
def TIMELY_TARGET_FLAG_INDEX : UInt64 := 1

/-- From Altair: the index of the flag of a timely head vote. -/
def TIMELY_HEAD_FLAG_INDEX : UInt64 := 2

/-- From Altair: the weight of the reward for a timely source vote. -/
def TIMELY_SOURCE_WEIGHT : UInt64 := 14

/-- From Altair: the weight of the reward for a timely target vote. -/
def TIMELY_TARGET_WEIGHT : UInt64 := 26

/-- From Altair: the weight of the reward for a timely head vote. -/
def TIMELY_HEAD_WEIGHT : UInt64 := 14

/-- From Altair: the weight of the reward for sync committee signatures. -/
def SYNC_REWARD_WEIGHT : UInt64 := 2

/-- From Altair: the weight of the reward of the block proposer. -/
def PROPOSER_WEIGHT : UInt64 := 8

/-- From Altair: the sum of all reward weights. -/
def WEIGHT_DENOMINATOR : UInt64 := 64

/-- From Altair: the reward weight of each participation flag, in the order of the flag indices. -/
def PARTICIPATION_FLAG_WEIGHTS : List UInt64 :=
  [TIMELY_SOURCE_WEIGHT, TIMELY_TARGET_WEIGHT, TIMELY_HEAD_WEIGHT]

/-- From Altair: the domain type of a sync committee signature. -/
def DOMAIN_SYNC_COMMITTEE : DomainType := #v[0x07, 0x00, 0x00, 0x00]

/-- From Altair: the domain type of the proof that selects a sync committee aggregator. -/
def DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF : DomainType := #v[0x08, 0x00, 0x00, 0x00]

/-- From Altair: the domain type of a sync committee contribution with its selection proof. -/
def DOMAIN_CONTRIBUTION_AND_PROOF : DomainType := #v[0x09, 0x00, 0x00, 0x00]

/-- From Bellatrix: the block hash of no execution payload, 32 zero bytes. -/
def EMPTY_BLOCK_HASH : Base.Hash32 := Vector.replicate 32 0

/-- From Altair: the number of aggregators that each sync subcommittee aims to select. -/
def TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE : UInt64 := 16

/-- From Altair: the most light client updates in one response. -/
def MAX_REQUEST_LIGHT_CLIENT_UPDATES : UInt64 := 128

/-- From Bellatrix: the execution payload of the block is valid. -/
def PAYLOAD_STATUS_VALID : PayloadValidationStatus := 0

/-- From Bellatrix: the execution engine found the execution payload of the block invalid. -/
def PAYLOAD_STATUS_INVALIDATED : PayloadValidationStatus := 1

/-- From Bellatrix: the execution engine has not yet validated the execution payload. -/
def PAYLOAD_STATUS_NOT_VALIDATED : PayloadValidationStatus := 2

/-- From Bellatrix: a block whose parent has no execution payload waits this many slots.

After them, a node may import it optimistically, before the execution layer validates it.

A node must let its user set another value. -/
def SAFE_SLOTS_TO_IMPORT_OPTIMISTICALLY : UInt64 := 128

/-- From Capella: the domain type of a change of withdrawal credentials to an execution address. -/
def DOMAIN_BLS_TO_EXECUTION_CHANGE : DomainType := #v[0x0A, 0x00, 0x00, 0x00]

/-- From Deneb: the first byte of the versioned hash of a KZG commitment.

[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#parameters) defines it. -/
def VERSIONED_HASH_VERSION_KZG : Vector UInt8 1 := #v[0x01]

/-- From Electra: the start index of deposit requests while none is known, `2^64 - 1`. -/
def UNSET_DEPOSIT_REQUESTS_START_INDEX : UInt64 := UInt64.ofNat (2 ^ 64 - 1)

/-- From Electra: the amount of a withdrawal request that asks for a full exit. -/
def FULL_EXIT_REQUEST_AMOUNT : Gwei := 0

/-- From Electra: the first byte of withdrawal credentials of a compounding validator.

[EIP-7251](https://eips.ethereum.org/EIPS/eip-7251#consensus-layer) defines it. -/
def COMPOUNDING_WITHDRAWAL_PREFIX : Vector UInt8 1 := #v[0x02]

/-- From Electra: the type of a deposit request. -/
def DEPOSIT_REQUEST_TYPE : Vector UInt8 1 := #v[0x00]

/-- From Electra: the type of a withdrawal request.

[EIP-7002](https://eips.ethereum.org/EIPS/eip-7002#configuration) defines it. -/
def WITHDRAWAL_REQUEST_TYPE : Vector UInt8 1 := #v[0x01]

/-- From Electra: the type of a consolidation request.

[EIP-7251](https://eips.ethereum.org/EIPS/eip-7251#execution-layer) defines it. -/
def CONSOLIDATION_REQUEST_TYPE : Vector UInt8 1 := #v[0x02]

/-- From Fulu: the largest 256-bit unsigned integer, `2^256 - 1`. -/
def UINT256_MAX : Base.U256 := BitVec.allOnes 256

end EthLib.Consensus

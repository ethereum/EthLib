module

public import EthLib.Consensus.Containers.Block
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.Containers.State`

The beacon state, one type for every fork from Phase 0 to Fulu.

Each fork adds its fields after those of the forks before.

Altair replaces the pending attestations of Phase 0 by participation flags, at the same places.

A field that a fork adds or removes holds nothing where it is absent, and its codec skips it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The state of the beacon chain after a slot.

Altair adds inactivity scores and sync committees, and Bellatrix the latest payload header.

Capella adds the withdrawal sweep and the historical summaries.

Electra adds the balance churn and the pending queues of [EIP-7251].

Electra also adds the index of the first deposit request of [EIP-6110].

Fulu adds the proposer lookahead of [EIP-7917].

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer
[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
-/
structure BeaconState (preset : Preset) (fork : Fork) where
  /-- The time of the genesis, in seconds since the Unix epoch. -/
  genesisTime : UInt64
  /-- The root of the validators at genesis, which tells chains apart. -/
  genesisValidatorsRoot : Root
  /-- The slot of the state. -/
  slot : Slot
  /-- The current and previous fork versions, and the epoch of the current fork. -/
  forkVersions : ForkVersions
  /-- The header of the latest block, with an empty state root until the next slot. -/
  latestBlockHeader : BeaconBlockHeader
  /-- The roots of the recent blocks, one for each slot, in a circular buffer. -/
  blockRoots : Vector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  /-- The roots of the recent states, one for each slot, in a circular buffer. -/
  stateRoots : Vector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  /-- The roots of the historical batches, frozen from Capella. -/
  historicalRoots : SszList Root preset.HISTORICAL_ROOTS_LIMIT.toNat
  /-- The deposit contract data that the chain has agreed on. -/
  eth1Data : Eth1Data
  /-- The votes of the current voting period on the deposit contract data. -/
  eth1DataVotes :
    SszList Eth1Data (preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat)
  /-- The number of deposits that the state has processed. -/
  eth1DepositIndex : UInt64
  /-- The registry of validators. -/
  validators : SszList Validator preset.VALIDATOR_REGISTRY_LIMIT.toNat
  /-- The balance of each validator, in the order of the registry. -/
  balances : SszList Gwei preset.VALIDATOR_REGISTRY_LIMIT.toNat
  /-- The RANDAO mixes of the recent epochs, in a circular buffer. -/
  randaoMixes : Vector Bytes32 preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
  /-- The slashed balances of the recent epochs, in a circular buffer. -/
  slashings : Vector Gwei preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat
  /-- Before Altair: the attestations that the previous epoch's blocks included. -/
  previousEpochAttestations :
    Until .altair fork
      (SszList (PendingAttestation preset)
        (preset.MAX_ATTESTATIONS.toNat * preset.SLOTS_PER_EPOCH.toNat))
  /-- Before Altair: the attestations that the current epoch's blocks included. -/
  currentEpochAttestations :
    Until .altair fork
      (SszList (PendingAttestation preset)
        (preset.MAX_ATTESTATIONS.toNat * preset.SLOTS_PER_EPOCH.toNat))
  /-- From Altair: the flags of each validator for the previous epoch. -/
  previousEpochParticipation :
    Since .altair fork (SszList ParticipationFlags preset.VALIDATOR_REGISTRY_LIMIT.toNat)
  /-- From Altair: the flags of each validator for the current epoch. -/
  currentEpochParticipation :
    Since .altair fork (SszList ParticipationFlags preset.VALIDATOR_REGISTRY_LIMIT.toNat)
  /-- Whether each of the recent epochs is justified, the latest first. -/
  justificationBits : Bitvector JUSTIFICATION_BITS_LENGTH.toNat
  /-- The justified checkpoint of the previous epoch. -/
  previousJustifiedCheckpoint : Checkpoint
  /-- The justified checkpoint of the current epoch. -/
  currentJustifiedCheckpoint : Checkpoint
  /-- The finalized checkpoint. -/
  finalizedCheckpoint : Checkpoint
  /-- From Altair: the inactivity score of each validator. -/
  inactivityScores : Since .altair fork (SszList UInt64 preset.VALIDATOR_REGISTRY_LIMIT.toNat)
  /-- From Altair: the sync committee of the current period. -/
  currentSyncCommittee : Since .altair fork (SyncCommittee preset)
  /-- From Altair: the sync committee of the next period. -/
  nextSyncCommittee : Since .altair fork (SyncCommittee preset)
  /-- From Bellatrix: the header of the latest execution payload. -/
  latestExecutionPayloadHeader : Since .bellatrix fork (ExecutionPayloadHeader preset fork)
  /-- From Capella: the index of the next withdrawal. -/
  nextWithdrawalIndex : Since .shapella fork WithdrawalIndex
  /-- From Capella: the validator at which the next withdrawal sweep starts. -/
  nextWithdrawalValidatorIndex : Since .shapella fork ValidatorIndex
  /-- From Capella: the summaries of the historical batches. -/
  historicalSummaries :
    Since .shapella fork (SszList HistoricalSummary preset.HISTORICAL_ROOTS_LIMIT.toNat)
  /-- From Electra: the index of the first deposit that came as a request. -/
  depositRequestsStartIndex : Since .pectra fork UInt64
  /-- From Electra: the balance that deposits may still use from the churn. -/
  depositBalanceToConsume : Since .pectra fork Gwei
  /-- From Electra: the balance that exits may still use from the churn. -/
  exitBalanceToConsume : Since .pectra fork Gwei
  /-- From Electra: the earliest epoch at which a new exit may take effect. -/
  earliestExitEpoch : Since .pectra fork Epoch
  /-- From Electra: the balance that consolidations may still use from the churn. -/
  consolidationBalanceToConsume : Since .pectra fork Gwei
  /-- From Electra: the earliest epoch at which a new consolidation may take effect. -/
  earliestConsolidationEpoch : Since .pectra fork Epoch
  /-- From Electra: the deposits waiting for the churn. -/
  pendingDeposits : Since .pectra fork (SszList PendingDeposit preset.PENDING_DEPOSITS_LIMIT.toNat)
  /-- From Electra: the partial withdrawals waiting to be paid. -/
  pendingPartialWithdrawals :
    Since .pectra fork
      (SszList PendingPartialWithdrawal preset.PENDING_PARTIAL_WITHDRAWALS_LIMIT.toNat)
  /-- From Electra: the consolidations waiting for their source to be withdrawable. -/
  pendingConsolidations :
    Since .pectra fork (SszList PendingConsolidation preset.PENDING_CONSOLIDATIONS_LIMIT.toNat)
  /-- From Fulu: the proposer of each slot of the current epoch and the next ones. -/
  proposerLookahead :
    Since .fusaka fork
      (Vector ValidatorIndex ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat))

namespace BeaconState

/-- The names of the fields of a state at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
    "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
    "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings"] ++
  untilNames .altair fork ["previous_epoch_attestations", "current_epoch_attestations"] ++
  sinceNames .altair fork ["previous_epoch_participation", "current_epoch_participation"] ++
  ["justification_bits", "previous_justified_checkpoint", "current_justified_checkpoint",
    "finalized_checkpoint"] ++
  sinceNames .altair fork ["inactivity_scores", "current_sync_committee", "next_sync_committee"] ++
  sinceNames .bellatrix fork ["latest_execution_payload_header"] ++
  sinceNames .shapella fork
    ["next_withdrawal_index", "next_withdrawal_validator_index", "historical_summaries"] ++
  sinceNames .pectra fork
    ["deposit_requests_start_index", "deposit_balance_to_consume", "exit_balance_to_consume",
      "earliest_exit_epoch", "consolidation_balance_to_consume", "earliest_consolidation_epoch",
      "pending_deposits", "pending_partial_withdrawals", "pending_consolidations"] ++
  sinceNames .fusaka fork ["proposer_lookahead"]

instance {preset : Preset} {fork : Fork} : SszType (BeaconState preset fork) :=
  .container (names fork)
    (fun s => (s.genesisTime, s.genesisValidatorsRoot, s.slot, s.forkVersions, s.latestBlockHeader,
      s.blockRoots, s.stateRoots, s.historicalRoots, s.eth1Data, s.eth1DataVotes,
      s.eth1DepositIndex, s.validators, s.balances, s.randaoMixes, s.slashings,
      s.previousEpochAttestations, s.currentEpochAttestations, s.previousEpochParticipation,
      s.currentEpochParticipation, s.justificationBits, s.previousJustifiedCheckpoint,
      s.currentJustifiedCheckpoint, s.finalizedCheckpoint, s.inactivityScores,
      s.currentSyncCommittee, s.nextSyncCommittee, s.latestExecutionPayloadHeader,
      s.nextWithdrawalIndex, s.nextWithdrawalValidatorIndex, s.historicalSummaries,
      s.depositRequestsStartIndex, s.depositBalanceToConsume, s.exitBalanceToConsume,
      s.earliestExitEpoch, s.consolidationBalanceToConsume, s.earliestConsolidationEpoch,
      s.pendingDeposits, s.pendingPartialWithdrawals, s.pendingConsolidations,
      s.proposerLookahead))
    (fun (genesisTime, genesisValidatorsRoot, slot, forkVersions, latestBlockHeader, blockRoots,
        stateRoots, historicalRoots, eth1Data, eth1DataVotes, eth1DepositIndex, validators,
        balances, randaoMixes, slashings, previousEpochAttestations, currentEpochAttestations,
        previousEpochParticipation, currentEpochParticipation, justificationBits,
        previousJustifiedCheckpoint, currentJustifiedCheckpoint, finalizedCheckpoint,
        inactivityScores, currentSyncCommittee, nextSyncCommittee, latestExecutionPayloadHeader,
        nextWithdrawalIndex, nextWithdrawalValidatorIndex, historicalSummaries,
        depositRequestsStartIndex, depositBalanceToConsume, exitBalanceToConsume,
        earliestExitEpoch, consolidationBalanceToConsume, earliestConsolidationEpoch,
        pendingDeposits, pendingPartialWithdrawals, pendingConsolidations, proposerLookahead) =>
      ⟨genesisTime, genesisValidatorsRoot, slot, forkVersions, latestBlockHeader, blockRoots,
        stateRoots, historicalRoots, eth1Data, eth1DataVotes, eth1DepositIndex, validators,
        balances, randaoMixes, slashings, previousEpochAttestations, currentEpochAttestations,
        previousEpochParticipation, currentEpochParticipation, justificationBits,
        previousJustifiedCheckpoint, currentJustifiedCheckpoint, finalizedCheckpoint,
        inactivityScores, currentSyncCommittee, nextSyncCommittee, latestExecutionPayloadHeader,
        nextWithdrawalIndex, nextWithdrawalValidatorIndex, historicalSummaries,
        depositRequestsStartIndex, depositBalanceToConsume, exitBalanceToConsume,
        earliestExitEpoch, consolidationBalanceToConsume, earliestConsolidationEpoch,
        pendingDeposits, pendingPartialWithdrawals, pendingConsolidations, proposerLookahead⟩)

end BeaconState

end EthLib.Consensus

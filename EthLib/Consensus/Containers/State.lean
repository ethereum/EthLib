module

public import EthLib.Consensus.Containers.Block
public import EthLib.Consensus.Containers.Builder
public import EthLib.Serialization.Ssz.Typed.RootedList
public import EthLib.Serialization.Ssz.Typed.Since

/-!
# `Consensus.Containers.State`

The beacon state, one type for every fork from Phase 0 to Heze.

Each fork adds its fields after those of the forks before.

Altair replaces the pending attestations of Phase 0 by participation flags, at the same places.

Gloas replaces the latest payload header by the latest block hash, at the same place.

A field that a fork adds or removes holds nothing where it is absent, and its codec skips it.

From Gloas the state is a progressive container, as [EIP-7688] specifies.

Its registry, its balances, its flags and its queues then have no limit in their type.

From Heze the places of the removed fields stay empty, so the other fields keep theirs.

[EIP-7688]: https://eips.ethereum.org/EIPS/eip-7688#converted-types
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

/-- The registry of validators, with its Merkle tree before Gloas. -/
abbrev Validators (preset : Preset) (fork : Fork) :=
  RootedForkList .glamsterdam fork Validator preset.VALIDATOR_REGISTRY_LIMIT.toNat

/-- The balance of each validator, in the order of the registry. -/
abbrev Balances (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork Gwei preset.VALIDATOR_REGISTRY_LIMIT.toNat

/-- From Altair: the participation flags of each validator for one epoch. -/
abbrev EpochParticipation (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork ParticipationFlags preset.VALIDATOR_REGISTRY_LIMIT.toNat

/-- From Altair: the inactivity score of each validator. -/
abbrev InactivityScores (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork UInt64 preset.VALIDATOR_REGISTRY_LIMIT.toNat

/-- From Electra: the deposits waiting for the churn. -/
abbrev PendingDeposits (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork PendingDeposit preset.PENDING_DEPOSITS_LIMIT.toNat

/-- From Electra: the partial withdrawals waiting to be paid. -/
abbrev PendingPartialWithdrawals (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork PendingPartialWithdrawal
    preset.PENDING_PARTIAL_WITHDRAWALS_LIMIT.toNat

/-- From Electra: the consolidations waiting for their source to be withdrawable. -/
abbrev PendingConsolidations (preset : Preset) (fork : Fork) :=
  ForkList .glamsterdam fork PendingConsolidation preset.PENDING_CONSOLIDATIONS_LIMIT.toNat

/-- The state of the beacon chain after a slot.

Altair adds inactivity scores and sync committees, and Bellatrix the latest payload header.

Capella adds the withdrawal sweep and the historical summaries.

Electra adds the balance churn and the pending queues of [EIP-7251].

Electra also adds the index of the first deposit request of [EIP-6110].

Fulu adds the proposer lookahead of [EIP-7917].

Gloas adds the builders, their payments and withdrawals, and the latest bid of [EIP-7732].

It also adds the availability of recent payloads and the window of payload committees.

Heze removes the deposit contract data, its votes and the two deposit indices of [EIP-8015].

On 2026-11-03 EIP-8015 was a Draft that EIP-8081 only considers for Hegotá.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#modified-containers
[EIP-8015]: https://eips.ethereum.org/EIPS/eip-8015#beaconstate-modifications
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
  blockRoots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  /-- The roots of the recent states, one for each slot, in a circular buffer. -/
  stateRoots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  /-- The roots of the historical batches, frozen from Capella. -/
  historicalRoots : SszList Root preset.HISTORICAL_ROOTS_LIMIT.toNat
  /-- Before Heze: the deposit contract data that the chain has agreed on. -/
  eth1Data : Until .hegota fork Eth1Data
  /-- Before Heze: the votes of the current voting period on the deposit contract data. -/
  eth1DataVotes :
    Until .hegota fork
      (SszList Eth1Data
        (preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat))
  /-- Before Heze: the number of deposits that the state has processed. -/
  eth1DepositIndex : Until .hegota fork UInt64
  /-- The registry of validators. -/
  validators : Validators preset fork
  /-- The balance of each validator, in the order of the registry. -/
  balances : Balances preset fork
  /-- The RANDAO mixes of the recent epochs, in a circular buffer. -/
  randaoMixes : RootedVector Bytes32 preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat
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
  previousEpochParticipation : Since .altair fork (EpochParticipation preset fork)
  /-- From Altair: the flags of each validator for the current epoch. -/
  currentEpochParticipation : Since .altair fork (EpochParticipation preset fork)
  /-- Whether each of the recent epochs is justified, the latest first. -/
  justificationBits : Bitvector JUSTIFICATION_BITS_LENGTH.toNat
  /-- The justified checkpoint of the previous epoch. -/
  previousJustifiedCheckpoint : Checkpoint
  /-- The justified checkpoint of the current epoch. -/
  currentJustifiedCheckpoint : Checkpoint
  /-- The finalized checkpoint. -/
  finalizedCheckpoint : Checkpoint
  /-- From Altair: the inactivity score of each validator. -/
  inactivityScores : Since .altair fork (InactivityScores preset fork)
  /-- From Altair: the sync committee of the current period. -/
  currentSyncCommittee : Since .altair fork (SyncCommittee preset)
  /-- From Altair: the sync committee of the next period. -/
  nextSyncCommittee : Since .altair fork (SyncCommittee preset)
  /-- From Bellatrix to Fulu: the header of the latest execution payload. -/
  latestExecutionPayloadHeader :
    During .bellatrix .glamsterdam fork (ExecutionPayloadHeader preset fork)
  /-- From Gloas: the hash of the latest execution block that the chain holds. -/
  latestBlockHash : Since .glamsterdam fork Hash32
  /-- From Capella: the index of the next withdrawal. -/
  nextWithdrawalIndex : Since .shapella fork WithdrawalIndex
  /-- From Capella: the validator at which the next withdrawal sweep starts. -/
  nextWithdrawalValidatorIndex : Since .shapella fork ValidatorIndex
  /-- From Capella: the summaries of the historical batches. -/
  historicalSummaries :
    Since .shapella fork (SszList HistoricalSummary preset.HISTORICAL_ROOTS_LIMIT.toNat)
  /-- From Electra to Gloas: the index of the first deposit that came as a request. -/
  depositRequestsStartIndex : During .pectra .hegota fork UInt64
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
  pendingDeposits : Since .pectra fork (PendingDeposits preset fork)
  /-- From Electra: the partial withdrawals waiting to be paid. -/
  pendingPartialWithdrawals : Since .pectra fork (PendingPartialWithdrawals preset fork)
  /-- From Electra: the consolidations waiting for their source to be withdrawable. -/
  pendingConsolidations : Since .pectra fork (PendingConsolidations preset fork)
  /-- From Fulu: the proposer of each slot of the current epoch and the next ones. -/
  proposerLookahead :
    Since .fusaka fork
      (Vector ValidatorIndex ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat))
  /-- From Gloas: the registry of builders. -/
  builders : Since .glamsterdam fork Builders
  /-- From Gloas: the builder at which the next withdrawal sweep of builders starts. -/
  nextWithdrawalBuilderIndex : Since .glamsterdam fork BuilderIndex
  /-- From Gloas: whether the block of each recent slot has a payload. -/
  executionPayloadAvailability : Since .glamsterdam fork (ExecutionPayloadAvailability preset)
  /-- From Gloas: the payments of the bids of the previous and current epochs. -/
  builderPendingPayments : Since .glamsterdam fork (BuilderPendingPayments preset)
  /-- From Gloas: the payments to builders and proposers waiting to be withdrawn. -/
  builderPendingWithdrawals : Since .glamsterdam fork BuilderPendingWithdrawals
  /-- From Gloas: the bid of the latest block. -/
  latestExecutionPayloadBid : Since .glamsterdam fork (ExecutionPayloadBid preset fork)
  /-- From Gloas: the withdrawals that the payload of the latest block must apply. -/
  payloadExpectedWithdrawals : Since .glamsterdam fork (Withdrawals preset fork)
  /-- From Gloas: the payload committees of the previous, current and lookahead epochs. -/
  ptcWindow : Since .glamsterdam fork (PayloadTimelinessCommitteeWindow preset)

namespace BeaconState

/-- The names of the fields of a state at a fork, in their order. -/
def names (fork : Fork) : List String :=
  ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
    "block_roots", "state_roots", "historical_roots"] ++
  untilNames .hegota fork ["eth1_data", "eth1_data_votes", "eth1_deposit_index"] ++
  ["validators", "balances", "randao_mixes", "slashings"] ++
  untilNames .altair fork ["previous_epoch_attestations", "current_epoch_attestations"] ++
  sinceNames .altair fork ["previous_epoch_participation", "current_epoch_participation"] ++
  ["justification_bits", "previous_justified_checkpoint", "current_justified_checkpoint",
    "finalized_checkpoint"] ++
  sinceNames .altair fork ["inactivity_scores", "current_sync_committee", "next_sync_committee"] ++
  duringNames .bellatrix .glamsterdam fork ["latest_execution_payload_header"] ++
  sinceNames .glamsterdam fork ["latest_block_hash"] ++
  sinceNames .shapella fork
    ["next_withdrawal_index", "next_withdrawal_validator_index", "historical_summaries"] ++
  duringNames .pectra .hegota fork ["deposit_requests_start_index"] ++
  sinceNames .pectra fork
    ["deposit_balance_to_consume", "exit_balance_to_consume", "earliest_exit_epoch",
      "consolidation_balance_to_consume", "earliest_consolidation_epoch", "pending_deposits",
      "pending_partial_withdrawals", "pending_consolidations"] ++
  sinceNames .fusaka fork ["proposer_lookahead"] ++
  sinceNames .glamsterdam fork
    ["builders", "next_withdrawal_builder_index", "execution_payload_availability",
      "builder_pending_payments", "builder_pending_withdrawals", "latest_execution_payload_bid",
      "payload_expected_withdrawals", "ptc_window"]

/-- From Gloas: the layout of a state, forty-six places in their order.

From Heze the places of the four removed fields stay empty. -/
def activeFields (fork : Fork) : List Bool :=
  if .hegota ≤ fork then
    List.replicate 8 true ++ List.replicate 3 false ++ List.replicate 17 true ++ [false] ++
      List.replicate 17 true
  else List.replicate 46 true

instance {preset : Preset} {fork : Fork} : SszType (BeaconState preset fork) :=
  .forkContainer .glamsterdam fork (activeFields fork) (names fork)
    (fun s => (s.genesisTime, s.genesisValidatorsRoot, s.slot, s.forkVersions, s.latestBlockHeader,
      s.blockRoots, s.stateRoots, s.historicalRoots, s.eth1Data, s.eth1DataVotes,
      s.eth1DepositIndex, s.validators, s.balances, s.randaoMixes, s.slashings,
      s.previousEpochAttestations, s.currentEpochAttestations, s.previousEpochParticipation,
      s.currentEpochParticipation, s.justificationBits, s.previousJustifiedCheckpoint,
      s.currentJustifiedCheckpoint, s.finalizedCheckpoint, s.inactivityScores,
      s.currentSyncCommittee, s.nextSyncCommittee, s.latestExecutionPayloadHeader,
      s.latestBlockHash,
      s.nextWithdrawalIndex, s.nextWithdrawalValidatorIndex, s.historicalSummaries,
      s.depositRequestsStartIndex, s.depositBalanceToConsume, s.exitBalanceToConsume,
      s.earliestExitEpoch, s.consolidationBalanceToConsume, s.earliestConsolidationEpoch,
      s.pendingDeposits, s.pendingPartialWithdrawals, s.pendingConsolidations,
      s.proposerLookahead, s.builders, s.nextWithdrawalBuilderIndex,
      s.executionPayloadAvailability, s.builderPendingPayments, s.builderPendingWithdrawals,
      s.latestExecutionPayloadBid, s.payloadExpectedWithdrawals, s.ptcWindow))
    (fun (genesisTime, genesisValidatorsRoot, slot, forkVersions, latestBlockHeader, blockRoots,
        stateRoots, historicalRoots, eth1Data, eth1DataVotes, eth1DepositIndex, validators,
        balances, randaoMixes, slashings, previousEpochAttestations, currentEpochAttestations,
        previousEpochParticipation, currentEpochParticipation, justificationBits,
        previousJustifiedCheckpoint, currentJustifiedCheckpoint, finalizedCheckpoint,
        inactivityScores, currentSyncCommittee, nextSyncCommittee, latestExecutionPayloadHeader,
        latestBlockHash, nextWithdrawalIndex, nextWithdrawalValidatorIndex, historicalSummaries,
        depositRequestsStartIndex, depositBalanceToConsume, exitBalanceToConsume,
        earliestExitEpoch, consolidationBalanceToConsume, earliestConsolidationEpoch,
        pendingDeposits, pendingPartialWithdrawals, pendingConsolidations, proposerLookahead,
        builders, nextWithdrawalBuilderIndex, executionPayloadAvailability, builderPendingPayments,
        builderPendingWithdrawals, latestExecutionPayloadBid, payloadExpectedWithdrawals,
        ptcWindow) =>
      ⟨genesisTime, genesisValidatorsRoot, slot, forkVersions, latestBlockHeader, blockRoots,
        stateRoots, historicalRoots, eth1Data, eth1DataVotes, eth1DepositIndex, validators,
        balances, randaoMixes, slashings, previousEpochAttestations, currentEpochAttestations,
        previousEpochParticipation, currentEpochParticipation, justificationBits,
        previousJustifiedCheckpoint, currentJustifiedCheckpoint, finalizedCheckpoint,
        inactivityScores, currentSyncCommittee, nextSyncCommittee, latestExecutionPayloadHeader,
        latestBlockHash, nextWithdrawalIndex, nextWithdrawalValidatorIndex, historicalSummaries,
        depositRequestsStartIndex, depositBalanceToConsume, exitBalanceToConsume,
        earliestExitEpoch, consolidationBalanceToConsume, earliestConsolidationEpoch,
        pendingDeposits, pendingPartialWithdrawals, pendingConsolidations, proposerLookahead,
        builders, nextWithdrawalBuilderIndex, executionPayloadAvailability, builderPendingPayments,
        builderPendingWithdrawals, latestExecutionPayloadBid, payloadExpectedWithdrawals,
        ptcWindow⟩)

/-- The registry holds at most the number of validators that the preset allows.

Before Gloas the type of the registry says so.

From Gloas the registry is a progressive list, so a theorem that needs the bound takes it. -/
def RegistryWithinLimit {preset : Preset} {fork : Fork} (state : BeaconState preset fork) : Prop :=
  state.validators.data.size ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat

end BeaconState

end EthLib.Consensus

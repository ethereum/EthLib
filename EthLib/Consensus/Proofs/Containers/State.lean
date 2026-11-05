module

public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Proofs.Containers.Block

/-!
# Proofs: the beacon state is lawful at every fork

The state has distinct field names at every fork, and converts to and from its fields.

So its bytes decode back to it, at every fork.

At Altair the participation flags take the places of the pending attestations.

At Gloas the latest block hash takes the place of the latest payload header.

The field names at Fulu and at Gloas are those of the specification, in their order.

The vectors whose length comes from the preset need that length to be positive.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The field names of a state are distinct at every fork. -/
theorem BeaconState.names_nodup : (BeaconState.names fork).Nodup := by
  have all : (["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
      "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
      "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
      "previous_epoch_attestations", "current_epoch_attestations",
      "previous_epoch_participation", "current_epoch_participation", "justification_bits",
      "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint",
      "inactivity_scores", "current_sync_committee", "next_sync_committee",
      "latest_execution_payload_header", "latest_block_hash", "next_withdrawal_index",
      "next_withdrawal_validator_index", "historical_summaries", "deposit_requests_start_index",
      "deposit_balance_to_consume", "exit_balance_to_consume", "earliest_exit_epoch",
      "consolidation_balance_to_consume", "earliest_consolidation_epoch", "pending_deposits",
      "pending_partial_withdrawals", "pending_consolidations", "proposer_lookahead",
      "builders", "next_withdrawal_builder_index", "execution_payload_availability",
      "builder_pending_payments", "builder_pending_withdrawals", "latest_execution_payload_bid",
      "payload_expected_withdrawals", "ptc_window"] :
      List String).Nodup := by decide
  refine all.sublist ?_
  unfold BeaconState.names
  exact (((((((((((List.Sublist.refl _).append (untilNames_sublist _)).append
    (sinceNames_sublist _)).append (List.Sublist.refl _)).append (sinceNames_sublist _)).append
    (duringNames_sublist _)).append (sinceNames_sublist _)).append (sinceNames_sublist _)).append
    (sinceNames_sublist _)).append (sinceNames_sublist _)).append (sinceNames_sublist _))

/-- At Fulu, the fields of a state are those of Electra and the proposer lookahead. -/
theorem BeaconState.names_fusaka :
    BeaconState.names .fusaka =
      ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
        "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
        "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
        "previous_epoch_participation", "current_epoch_participation", "justification_bits",
        "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint",
        "inactivity_scores", "current_sync_committee", "next_sync_committee",
        "latest_execution_payload_header", "next_withdrawal_index",
        "next_withdrawal_validator_index", "historical_summaries", "deposit_requests_start_index",
        "deposit_balance_to_consume", "exit_balance_to_consume", "earliest_exit_epoch",
        "consolidation_balance_to_consume", "earliest_consolidation_epoch", "pending_deposits",
        "pending_partial_withdrawals", "pending_consolidations", "proposer_lookahead"] := by
  decide

/-- At Gloas, the state has forty-six fields, the latest block hash in place of the header. -/
theorem BeaconState.names_glamsterdam :
    BeaconState.names .glamsterdam =
      ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
        "block_roots", "state_roots", "historical_roots", "eth1_data", "eth1_data_votes",
        "eth1_deposit_index", "validators", "balances", "randao_mixes", "slashings",
        "previous_epoch_participation", "current_epoch_participation", "justification_bits",
        "previous_justified_checkpoint", "current_justified_checkpoint", "finalized_checkpoint",
        "inactivity_scores", "current_sync_committee", "next_sync_committee",
        "latest_block_hash", "next_withdrawal_index", "next_withdrawal_validator_index",
        "historical_summaries", "deposit_requests_start_index", "deposit_balance_to_consume",
        "exit_balance_to_consume", "earliest_exit_epoch", "consolidation_balance_to_consume",
        "earliest_consolidation_epoch", "pending_deposits", "pending_partial_withdrawals",
        "pending_consolidations", "proposer_lookahead", "builders",
        "next_withdrawal_builder_index", "execution_payload_availability",
        "builder_pending_payments", "builder_pending_withdrawals", "latest_execution_payload_bid",
        "payload_expected_withdrawals", "ptc_window"] := by
  decide

/-- Before Gloas, the registry holds at most the number of validators that the preset allows. -/
theorem BeaconState.registryWithinLimit_of_lt (before : fork < .glamsterdam)
    (state : BeaconState preset fork) : state.RegistryWithinLimit :=
  state.validators.bound before

instance : NeZero JUSTIFICATION_BITS_LENGTH.toNat := ⟨by decide⟩

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
  [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
  [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
  [NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)]
  [NeZero preset.PTC_SIZE.toNat] [NeZero (2 * preset.SLOTS_PER_EPOCH.toNat)]
  [NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat)]

-- The fields of every fork make a tuple of forty-nine, beyond the default size of the search.
set_option synthInstance.maxSize 512 in
instance : LawfulSszType (BeaconState preset fork) :=
  .forkContainer
    (fun gloas => by
      have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
      have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
      have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) gloas
      have fulu : Fork.fusaka ≤ fork := Nat.le_trans (by decide) gloas
      exact ⟨rfl, by decide, by
        simp [BeaconState.activeFields, SszFields.descs, altair, capella, electra, fulu, gloas,
          not_lt_of_switch gloas, not_lt_of_switch altair]⟩)
    ⟨by
      by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
        by_cases capella : Fork.shapella ≤ fork <;> by_cases electra : Fork.pectra ≤ fork <;>
        by_cases fulu : Fork.fusaka ≤ fork <;> by_cases gloas : Fork.glamsterdam ≤ fork <;>
        simp [BeaconState.names, sinceNames, untilNames, duringNames, SszFields.descs, altair,
          bellatrix, capella, electra, fulu, gloas, not_lt_of_switch, lt_of_not_switch],
     by simp [BeaconState.names],
     firstDuplicate_of_nodup _ BeaconState.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

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

At Heze four fields leave the state, and each field that stays keeps its place in the tree.

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
  exact ((((((((((((((List.Sublist.refl _).append (untilNames_sublist _)).append
    (List.Sublist.refl _)).append (untilNames_sublist _)).append (sinceNames_sublist _)).append
    (List.Sublist.refl _)).append (sinceNames_sublist _)).append (duringNames_sublist _)).append
    (sinceNames_sublist _)).append (sinceNames_sublist _)).append (duringNames_sublist _)).append
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

/-- At Heze, the deposit contract data, its votes and the two deposit indices leave the state. -/
theorem BeaconState.names_hegota :
    BeaconState.names .hegota =
      ["genesis_time", "genesis_validators_root", "slot", "fork", "latest_block_header",
        "block_roots", "state_roots", "historical_roots", "validators", "balances",
        "randao_mixes", "slashings", "previous_epoch_participation",
        "current_epoch_participation", "justification_bits", "previous_justified_checkpoint",
        "current_justified_checkpoint", "finalized_checkpoint", "inactivity_scores",
        "current_sync_committee", "next_sync_committee", "latest_block_hash",
        "next_withdrawal_index", "next_withdrawal_validator_index", "historical_summaries",
        "deposit_balance_to_consume", "exit_balance_to_consume", "earliest_exit_epoch",
        "consolidation_balance_to_consume", "earliest_consolidation_epoch", "pending_deposits",
        "pending_partial_withdrawals", "pending_consolidations", "proposer_lookahead", "builders",
        "next_withdrawal_builder_index", "execution_payload_availability",
        "builder_pending_payments", "builder_pending_withdrawals", "latest_execution_payload_bid",
        "payload_expected_withdrawals", "ptc_window"] := by
  decide

/-- Every field of a state at Heze sits at the place it has at Gloas.

So a proof of one of these fields against a Gloas state root keeps its path at Heze. -/
theorem BeaconState.fieldPlace_hegota :
    ∀ name ∈ BeaconState.names .hegota,
      fieldPlace (BeaconState.activeFields .hegota) (BeaconState.names .hegota) name =
        fieldPlace (BeaconState.activeFields .glamsterdam) (BeaconState.names .glamsterdam)
          name := by
  decide

/-- Every field of a state at Heze has the generalized index it has at Gloas, at every preset. -/
theorem BeaconState.getGeneralizedIndex_hegota {name : String}
    (kept : name ∈ BeaconState.names .hegota) :
    SszType.getGeneralizedIndex (BeaconState preset .hegota)
        [.position ((BeaconState.names .hegota).idxOf name)] =
      SszType.getGeneralizedIndex (BeaconState preset .glamsterdam)
        [.position ((BeaconState.names .glamsterdam).idxOf name)] := by
  have placed : ∀ name ∈ BeaconState.names .hegota,
      (fieldPlace (BeaconState.activeFields .hegota) (BeaconState.names .hegota)
        name).isSome := by
    decide
  obtain ⟨place, found⟩ := Option.isSome_iff_exists.mp (placed name kept)
  unfold SszType.getGeneralizedIndex
  refine getGeneralizedIndex_eq_of_fieldPlace (leftActive := BeaconState.activeFields .hegota)
    (rightActive := BeaconState.activeFields .glamsterdam) ?_ ?_ found
    ((BeaconState.fieldPlace_hegota name kept) ▸ found) <;> rfl

/-- At Gloas, the four fields that Heze removes sit at places 8, 9, 10 and 28.

Those places are the gaps of the Heze layout. -/
theorem BeaconState.fieldPlace_removed_hegota :
    ["eth1_data", "eth1_data_votes", "eth1_deposit_index", "deposit_requests_start_index"].map
        (fieldPlace (BeaconState.activeFields .glamsterdam) (BeaconState.names .glamsterdam)) =
      [some 8, some 9, some 10, some 28] ∧
      [8, 9, 10, 28].map ((BeaconState.activeFields .hegota)[·]?) =
        [some false, some false, some false, some false] := by
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
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

-- The fields of every fork make a tuple of forty-nine, beyond the default size of the search.
set_option synthInstance.maxSize 512 in
instance : LawfulSszType (BeaconState preset fork) :=
  .forkContainer
    (fun gloas => by
      have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) gloas
      have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) gloas
      have electra : Fork.pectra ≤ fork := Nat.le_trans (by decide) gloas
      have fulu : Fork.fusaka ≤ fork := Nat.le_trans (by decide) gloas
      by_cases heze : Fork.hegota ≤ fork
      · exact ⟨by simp [BeaconState.activeFields, heze],
          by simp [BeaconState.activeFields, heze, maxActiveFields], by
          simp [BeaconState.activeFields, SszFields.descs, altair, capella, electra, fulu, gloas,
            heze, not_lt_of_switch gloas, not_lt_of_switch altair, not_lt_of_switch heze]⟩
      · exact ⟨by simp [BeaconState.activeFields, heze],
          by simp [BeaconState.activeFields, heze, maxActiveFields], by
          simp [BeaconState.activeFields, SszFields.descs, altair, capella, electra, fulu, gloas,
            heze, not_lt_of_switch gloas, not_lt_of_switch altair, lt_of_not_switch heze]⟩)
    ⟨by
      by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
        by_cases capella : Fork.shapella ≤ fork <;> by_cases electra : Fork.pectra ≤ fork <;>
        by_cases fulu : Fork.fusaka ≤ fork <;> by_cases gloas : Fork.glamsterdam ≤ fork <;>
        by_cases heze : Fork.hegota ≤ fork <;>
        simp [BeaconState.names, sinceNames, untilNames, duringNames, SszFields.descs, altair,
          bellatrix, capella, electra, fulu, gloas, heze, not_lt_of_switch, lt_of_not_switch],
     by simp [BeaconState.names],
     firstDuplicate_of_nodup _ BeaconState.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

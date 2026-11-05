module

public import EthLib.Consensus.Containers.State
public import EthLib.Consensus.Proofs.Containers.Block

/-!
# Proofs: the beacon state is lawful at every fork

The state has distinct field names at every fork, and converts to and from its fields.

So its bytes decode back to it, at every fork.

At Altair the participation flags take the places of the pending attestations.

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
      "latest_execution_payload_header", "next_withdrawal_index",
      "next_withdrawal_validator_index", "historical_summaries", "deposit_requests_start_index",
      "deposit_balance_to_consume", "exit_balance_to_consume", "earliest_exit_epoch",
      "consolidation_balance_to_consume", "earliest_consolidation_epoch", "pending_deposits",
      "pending_partial_withdrawals", "pending_consolidations", "proposer_lookahead"] :
      List String).Nodup := by decide
  refine all.sublist ?_
  unfold BeaconState.names
  exact (((((((((List.Sublist.refl _).append (untilNames_sublist _)).append
    (sinceNames_sublist _)).append (List.Sublist.refl _)).append (sinceNames_sublist _)).append
    (sinceNames_sublist _)).append (sinceNames_sublist _)).append (sinceNames_sublist _)).append
    (sinceNames_sublist _))

instance : NeZero JUSTIFICATION_BITS_LENGTH.toNat := ⟨by decide⟩

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat]
  [NeZero preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat]
  [NeZero preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat]
  [NeZero ((preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat)]

instance : LawfulSszType (BeaconState preset fork) :=
  .container
    ⟨by
      have before : fork < Fork.altair ↔ ¬Fork.altair ≤ fork := Nat.not_le.symm
      by_cases altair : Fork.altair ≤ fork <;> by_cases bellatrix : Fork.bellatrix ≤ fork <;>
        by_cases capella : Fork.shapella ≤ fork <;> by_cases electra : Fork.pectra ≤ fork <;>
        by_cases fulu : Fork.fusaka ≤ fork <;>
        simp [BeaconState.names, sinceNames, untilNames, SszFields.descs, before, altair,
          bellatrix, capella, electra, fulu],
     by simp [BeaconState.names],
     firstDuplicate_of_nodup _ BeaconState.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

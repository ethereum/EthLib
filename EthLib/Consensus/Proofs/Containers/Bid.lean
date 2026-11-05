module

public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Proofs.Containers.InclusionList
public import EthLib.Consensus.Proofs.Containers.Requests

/-!
# Proofs: the bid and envelope containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it, at every fork.

The bid and the envelope are progressive containers that hold all their fields.

From Heze the bid has a thirteenth field, its inclusion list bits.

The bitvector of those bits needs a committee of positive size.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The field names of a bid are distinct at every fork. -/
theorem ExecutionPayloadBid.names_nodup : (ExecutionPayloadBid.names fork).Nodup := by
  unfold ExecutionPayloadBid.names sinceNames
  split <;> decide

/-- At Gloas, a bid has the twelve fields of EIP-7732. -/
theorem ExecutionPayloadBid.names_glamsterdam :
    ExecutionPayloadBid.names .glamsterdam =
      ["parent_block_hash", "parent_block_root", "block_hash", "prev_randao", "fee_recipient",
        "gas_limit", "builder_index", "slot", "value", "execution_payment",
        "blob_kzg_commitments", "execution_requests_root"] := by
  decide

/-- At Heze, a bid has one more field, its inclusion list bits, after the twelve of Gloas. -/
theorem ExecutionPayloadBid.names_hegota :
    ExecutionPayloadBid.names .hegota =
      ExecutionPayloadBid.names .glamsterdam ++ ["inclusion_list_bits"] := by
  decide

instance [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] :
    LawfulSszType (ExecutionPayloadBid preset fork) :=
  .progressiveContainer
    ⟨by by_cases heze : Fork.hegota ≤ fork <;> simp [ExecutionPayloadBid.activeFields, heze],
     by by_cases heze : Fork.hegota ≤ fork <;>
       simp [ExecutionPayloadBid.activeFields, heze, maxActiveFields],
     by by_cases heze : Fork.hegota ≤ fork <;>
       simp [ExecutionPayloadBid.activeFields, SszFields.descs, heze]⟩
    ⟨by by_cases heze : Fork.hegota ≤ fork <;>
       simp [ExecutionPayloadBid.names, sinceNames, SszFields.descs, heze],
     by simp [ExecutionPayloadBid.names],
     firstDuplicate_of_nodup _ ExecutionPayloadBid.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] :
    LawfulSszType (SignedExecutionPayloadBid preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (ExecutionPayloadEnvelope preset fork) :=
  .progressiveContainer ⟨rfl, by decide, rfl⟩
    ⟨rfl, by simp [ExecutionPayloadEnvelope.names], by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (SignedExecutionPayloadEnvelope preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

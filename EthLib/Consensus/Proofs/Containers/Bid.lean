module

public import EthLib.Consensus.Containers.Bid
public import EthLib.Consensus.Proofs.Containers.Requests

/-!
# Proofs: the bid and envelope containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it, at every fork.

The bid and the envelope are progressive containers that hold all their fields.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

instance : LawfulSszType (ExecutionPayloadBid preset fork) :=
  .progressiveContainer ⟨rfl, by decide, rfl⟩ ⟨rfl, by simp [ExecutionPayloadBid.names], by decide⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (SignedExecutionPayloadBid preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (ExecutionPayloadEnvelope preset fork) :=
  .progressiveContainer ⟨rfl, by decide, rfl⟩
    ⟨rfl, by simp [ExecutionPayloadEnvelope.names], by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] :
    LawfulSszType (SignedExecutionPayloadEnvelope preset fork) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

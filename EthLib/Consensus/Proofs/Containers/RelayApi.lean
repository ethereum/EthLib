module

public import EthLib.Consensus.Containers.RelayApi
public import EthLib.Consensus.Proofs.Containers.BuilderApi

/-!
# Proofs: the containers of the Relay API are lawful at every fork

A bid trace and a submission have distinct field names, so their bytes decode back to them.

For a submission this holds when the logs bloom has a byte.

A bid trace has a fixed size: every bid trace serializes to 236 bytes.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType

variable {preset : Preset} {fork : Fork}

instance : LawfulSszType BidTrace := .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- A bid trace serializes to 236 bytes: `8 + 32 + 32 + 48 + 48 + 20 + 8 + 8 + 32`. -/
theorem BidTrace.serialize_size {t : BidTrace} {data : ByteArray}
    (wrote : serialize t = .ok data) : data.size = 236 :=
  Serialization.Ssz.SszType.serialize_size (by decide) wrote

/-- The field names of a submission are distinct at every fork. -/
theorem SubmitBlockRequest.names_nodup : (SubmitBlockRequest.names fork).Nodup := by
  have all : (["message", "execution_payload", "blobs_bundle", "execution_requests",
      "signature"] : List String).Nodup := by decide
  refine all.sublist ?_
  unfold SubmitBlockRequest.names
  exact (((List.Sublist.refl _).append (duringNames_sublist _)).append
    (duringNames_sublist _)).append (List.Sublist.refl _)

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]

instance : LawfulSszType (SubmitBlockRequest preset fork) :=
  .container
    ⟨by
      by_cases deneb : Fork.dencun ≤ fork <;> by_cases electra : Fork.pectra ≤ fork <;>
        by_cases gloas : Fork.glamsterdam ≤ fork <;>
        simp [SubmitBlockRequest.names, duringNames, SszFields.descs, deneb, electra, gloas,
          not_lt_of_switch, lt_of_not_switch],
     by simp [SubmitBlockRequest.names],
     firstDuplicate_of_nodup _ SubmitBlockRequest.names_nodup⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType (BuilderSubmitNewBlockRequest preset fork) :=
  .container ⟨rfl, by simp [BuilderSubmitNewBlockRequest.names], rfl⟩
    (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

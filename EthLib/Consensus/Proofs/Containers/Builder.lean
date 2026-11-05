module

public import EthLib.Consensus.Containers.Builder
public import EthLib.Consensus.Containers.PayloadAttestation
public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections

/-!
# Proofs: the builder and payload attestation containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it.

An aggregated vote and its indexed form are progressive containers that hold their three fields.

A builder deposit request has the layout of a deposit request without its last field, the index.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType Builder := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderPendingWithdrawal :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderPendingPayment :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderDepositRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BuilderExitRequest := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PayloadAttestationData :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PayloadAttestationMessage :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} [NeZero preset.PTC_SIZE.toNat] :
    LawfulSszType (PayloadAttestation preset) :=
  .progressiveContainer ⟨rfl, by decide, rfl⟩ ⟨rfl, by simp, by decide⟩ (fun _ => rfl)
    (fun _ => rfl)

instance {preset : Preset} : LawfulSszType (IndexedPayloadAttestation preset) :=
  .progressiveContainer ⟨rfl, by decide, rfl⟩ ⟨rfl, by simp, by decide⟩ (fun _ => rfl)
    (fun _ => rfl)

/-- A deposit request has the fields of a builder deposit request, then the index, a uint64. -/
theorem desc_depositRequest {names : List String} {fields : List Desc}
    (builder : SszType.desc BuilderDepositRequest = .container names fields) :
    SszType.desc DepositRequest =
      .container (names ++ ["index"]) (fields ++ [SszType.desc UInt64]) := by
  injection builder with namesEq fieldsEq
  subst namesEq fieldsEq
  rfl

end EthLib.Consensus

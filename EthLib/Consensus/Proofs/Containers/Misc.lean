module

public import EthLib.Consensus.Containers.Operations
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: the shared containers of the beacon chain are lawful

Each container has distinct field names, and converts to and from the tuple of its fields.

So its bytes decode back to it, and two values with one encoding are equal.

A vector whose length comes from the preset needs that length to be positive.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType ForkVersions := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType Checkpoint := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType Validator := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType AttestationData := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} : LawfulSszType (PendingAttestation preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType Eth1Data := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} [NeZero preset.SLOTS_PER_HISTORICAL_ROOT.toNat] :
    LawfulSszType (HistoricalBatch preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType DepositMessage := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType DepositData := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BeaconBlockHeader :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedBeaconBlockHeader :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType Eth1Block := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType ProposerSlashing := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType Deposit := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType VoluntaryExit := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedVoluntaryExit :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType HistoricalSummary :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BLSToExecutionChange :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedBLSToExecutionChange :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus

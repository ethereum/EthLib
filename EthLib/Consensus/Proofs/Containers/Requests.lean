module

public import EthLib.Consensus.Containers.Requests
public import EthLib.Consensus.Proofs.Containers.Misc

/-!
# Proofs: the request and queue containers are lawful

Each container has distinct field names, and converts to and from its fields.

So its bytes decode back to it.

The three request types are distinct bytes, so a request list names its type without doubt.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType PendingDeposit := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PendingPartialWithdrawal :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PendingConsolidation :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType DepositRequest := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType WithdrawalRequest := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType ConsolidationRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} : LawfulSszType (ExecutionRequests preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

/-- The deposit, withdrawal and consolidation request types are three distinct bytes. -/
theorem requestTypes_nodup :
    [DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE].Nodup := by
  decide

end EthLib.Consensus

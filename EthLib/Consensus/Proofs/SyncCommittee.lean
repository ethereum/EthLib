module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Proofs.PayloadTimeliness
public import EthLib.Consensus.SyncCommittee

/-!
# Proofs: the sync committee

Each member of the next sync committee is active in the epoch after the epoch of the state.

The committee has the size of the preset by its type, and may hold a validator more than once.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- Each member of the next sync committee is active in the next epoch. -/
theorem mem_getNextSyncCommitteeIndices {state : BeaconState preset fork}
    {result : Vector ValidatorIndex preset.SYNC_COMMITTEE_SIZE.toNat}
    (computed : getNextSyncCommitteeIndices state = .ok result) :
    ∀ index ∈ result.toList,
      index ∈ getActiveValidatorIndices state (getCurrentEpoch state + 1) := by
  simp only [getNextSyncCommitteeIndices, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨epoch, next, _, _, selected⟩ := computed
  have epochEq : epoch = getCurrentEpoch state + 1 := by
    obtain ⟨fits, value⟩ := addChecked_ok_iff.mp next
    apply UInt64.toNat_inj.mp
    rw [value, UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using fits)]
  subst epochEq
  intro index member
  simpa using mem_of_computeBalanceWeightedSelection selected index member

end EthLib.Consensus

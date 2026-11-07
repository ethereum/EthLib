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

The committee holds the keys of the drawn validators, in the order of the draw, and their aggregate.
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
    rw [value, toNat_add_of_lt (by simpa using fits)]
  subst epochEq
  intro index member
  simpa using mem_of_computeBalanceWeightedSelection selected index member

/-- The next sync committee holds the keys of the drawn validators, in order, and their aggregate.

Member `i` of the committee has the key of the validator at position `i` of the draw. -/
theorem getNextSyncCommittee_ok {state : BeaconState preset fork}
    {committee : SyncCommittee preset} (computed : getNextSyncCommittee state = .ok committee) :
    ∃ indices, getNextSyncCommitteeIndices state = .ok indices ∧
      (∀ i : Fin preset.SYNC_COMMITTEE_SIZE.toNat, ∃ validator,
        getValidator state indices[i] = .ok validator ∧ committee.pubkeys[i] = validator.pubkey) ∧
      aggregatePubkeys committee.pubkeys.toArray = .ok committee.aggregatePubkey := by
  unfold getNextSyncCommittee at computed
  obtain ⟨indices, indicesOk, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨pubkeys, pubkeysOk, rest⟩ := bind_ok_iff.mp rest
  obtain ⟨aggregate, aggregateOk, rest⟩ := bind_ok_iff.mp rest
  cases rest
  refine ⟨indices, indicesOk, fun i => ?_, aggregateOk⟩
  -- Each key comes from the read of the validator at the same position.
  have read := vector_mapM_ok_getElem pubkeysOk i.val i.isLt
  obtain ⟨validator, found, key⟩ := bind_ok_iff.mp read
  exact ⟨validator, found, (Except.ok.inj key).symm⟩

end EthLib.Consensus

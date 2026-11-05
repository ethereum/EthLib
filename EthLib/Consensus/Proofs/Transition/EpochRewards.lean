module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochRewards

/-!
# Proofs: rewards and penalties

Adding a delta changes the entry at its index only.

A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead.

So a validator absent from the unslashed signers earns no reward for that kind of vote.

The first epoch has no rewards, and the step keeps one balance for each validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- Adding a delta keeps the entries at the other indices. -/
theorem addDelta_getD_of_ne {deltas result : Array Gwei} {index : ValidatorIndex}
    {amount : Gwei} (computed : addDelta deltas index amount = .ok result) {j : Nat}
    (other : j ≠ index.toNat) : result.getD j 0 = deltas.getD j 0 := by
  unfold addDelta at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    simp [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Ne.symm other]
  · cases computed

/-- Adding nothing keeps the deltas. -/
theorem addDelta_zero {deltas result : Array Gwei} {index : ValidatorIndex}
    (computed : addDelta deltas index 0 = .ok result) : result = deltas := by
  unfold addDelta at computed
  split at computed
  · rename_i old read
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff,
      pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨sum, ⟨_, value⟩, rfl⟩ := computed
    have same : sum = old := UInt64.toNat_inj.mp (by simpa using value)
    subst same
    obtain ⟨inside, rfl⟩ := Array.getElem?_eq_some_iff.mp read
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, inside]
  · cases computed

/-- A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead. -/
theorem componentDelta_unmatched (state : BeaconState preset fork)
    (base attestingBalance totalActiveBalance : Gwei) :
    componentDelta state false base attestingBalance totalActiveBalance = .ok (0, base) := rfl

/-- A validator absent from the unslashed signers of some attestations earns nothing for them.

This holds in a leak and outside one. -/
theorem getAttestationComponentDeltas_absent {attestations : Array (PendingAttestation preset)}
    {rewards penalties : Array Gwei}
    (computed : getAttestationComponentDeltas state attestations = .ok (rewards, penalties))
    {attesters : List ValidatorIndex}
    (signers : getUnslashedAttestingIndices state attestations = .ok attesters) {index : Nat}
    (absent : ∀ attester ∈ attesters, attester.toNat ≠ index) : rewards.getD index 0 = 0 := by
  simp only [getAttestationComponentDeltas, bind_ok_iff, liftAccessor_ok, signers] at computed
  obtain ⟨_, _, _, found, _, _, eligible, _, folded⟩ := computed
  cases found
  have unmarked : (markIndices state.validators.data.size attesters).getD index false = false := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    split
    · simp only [Option.getD_some, List.any_eq_false, beq_iff_eq]
      exact fun attester member => absent attester member
    · rfl
  let P : Array Gwei × Array Gwei → Prop := fun deltas =>
    ∀ j, (markIndices state.validators.data.size attesters).getD j false = false →
      deltas.1.getD j 0 = 0
  have start : P (Array.replicate state.validators.data.size 0,
      Array.replicate state.validators.data.size 0) := by
    intro j _
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have holds := foldlM_ok_invariant P (fun deltas index next before step => by
    obtain ⟨rewards, penalties⟩ := deltas
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨_, _, ⟨reward, penalty⟩, delta, newRewards, rewardsOk, _, _, rfl⟩ := step
    intro j unmarkedJ
    by_cases same : j = index.toNat
    · subst same
      rw [unmarkedJ] at delta
      rw [componentDelta_unmatched] at delta
      cases delta
      rw [addDelta_zero rewardsOk]
      exact before _ unmarkedJ
    · rw [addDelta_getD_of_ne rewardsOk same]
      exact before j unmarkedJ) start folded
  exact holds index unmarked

/-- In the first epoch, rewards and penalties change nothing before Altair. -/
theorem processRewardsAndPenalties_genesis (before : fork < .altair)
    (genesis : getCurrentEpoch state = GENESIS_EPOCH) :
    processRewardsAndPenalties state = .ok state := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp [processRewardsAndPenalties, notAltair, genesis, pure, Except.pure]

/-- Applying the deltas of one validator keeps the sizes. -/
theorem sameSizes_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : SameSizes state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨raised, raisedOk, lowered⟩ := computed
  exact (sameSizes_increaseBalance raisedOk).trans (sameSizes_decreaseBalance lowered)

/-- Rewards and penalties succeed only before Altair, and keep the sizes. -/
theorem processRewardsAndPenalties_ok
    (computed : processRewardsAndPenalties state = .ok after) :
    fork < .altair ∧ SameSizes state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · cases computed
  rename_i altair
  refine ⟨Nat.lt_of_not_le altair, ?_⟩
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _
  · simp only [bind_ok_iff] at computed
    obtain ⟨⟨rewards, penalties⟩, _, applied⟩ := computed
    exact foldlM_ok_invariant (SameSizes state) (fun _ _ _ sizes step =>
      sizes.trans (sameSizes_applyDeltas step)) (SameSizes.refl state) applied

end EthLib.Consensus

module

public import EthLib.Consensus.Proofs.Transition.MixesKept

/-!
# Proofs: a run of slots and blocks within one fork keeps the committees of nearby epochs

A slot or a block writes at most the RANDAO mix of an epoch between the current epochs of the run.

So a run keeps each mix at a position that none of those epochs takes.

The seed of an epoch reads the mix `MIN_SEED_LOOKAHEAD + 1` epochs before it.

That mix is final at the start when the epoch is at most `MIN_SEED_LOOKAHEAD` after its epoch.

A run keeps it while it stays within the ring of mixes.

A run also keeps activity up to its start plus `MAX_SEED_LOOKAHEAD`, below 2^64 validators.

So it keeps the committees of each epoch up to its start plus `MIN_SEED_LOOKAHEAD`.

The epoch must also be within that activity, and the run must end within the ring.

The run stays within one fork, as the states of a store do.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- Two states of one fork, of which the second can follow the first by slots and blocks.

The current epoch never moves back, and the registry never shrinks.

Each RANDAO mix is kept at a position that no epoch between the two current epochs takes.

It keeps activity up to the current epoch of the first plus `MAX_SEED_LOOKAHEAD`, capped. -/
structure RunKept (state after : BeaconState preset fork) : Prop where
  later : getCurrentEpoch state ≤ getCurrentEpoch after
  grows : state.validators.data.size ≤ after.validators.data.size
  mixes : ∀ epoch : Epoch, (∀ written : Epoch, getCurrentEpoch state ≤ written →
      written ≤ getCurrentEpoch after →
        written % preset.EPOCHS_PER_HISTORICAL_VECTOR ≠
          epoch % preset.EPOCHS_PER_HISTORICAL_VECTOR) →
    readCircular after.randaoMixes.elements epoch = readCircular state.randaoMixes.elements epoch
  active : ActiveKept (activityFixedEpoch state) state after

theorem RunKept.refl (state : BeaconState preset fork) : RunKept state state :=
  ⟨UInt64.le_refl _, Nat.le_refl _, fun _ _ => rfl, ActiveKept.refl _ _⟩

theorem RunKept.trans {first second third : BeaconState preset fork}
    (one : RunKept first second) (two : RunKept second third) : RunKept first third where
  later := UInt64.le_trans one.later two.later
  grows := Nat.le_trans one.grows two.grows
  mixes epoch apart := by
    rw [two.mixes epoch fun written low high =>
        apart written (UInt64.le_trans one.later low) high,
      one.mixes epoch fun written low high =>
        apart written low (UInt64.le_trans high two.later)]
  active := one.active.trans (two.active.mono (activityFixedEpoch_mono one.later))

/-- One slot is a run step. -/
theorem runKept_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    RunKept state after := by
  have later : getCurrentEpoch state ≤ getCurrentEpoch after := by
    rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat,
      advanceSlot_slot computed]
    exact Nat.div_le_div_right (Nat.le_succ _)
  exact ⟨later, advanceSlot_registryGrows computed,
    fun epoch apart => mixesKeptBut_advanceSlot computed epoch fun same =>
      apart _ later (UInt64.le_refl _) same.symm,
    activeKept_advanceSlot computed⟩

/-- A block is a run step. -/
theorem runKept_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    RunKept state after := by
  have frame := frame_processBlock computed
  have same : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  exact ⟨same ▸ UInt64.le_refl _, frame.registryGrows,
    fun epoch apart => mixesKeptBut_processBlock computed epoch fun eq =>
      apart _ (UInt64.le_refl _) (same ▸ UInt64.le_refl _) eq.symm,
    activeKept_processBlock computed⟩

/-- Some count of slots is a run step. -/
private theorem runKept_advanceSlots :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after → RunKept state after
  | 0, state, after, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ RunKept.refl state
  | count + 1, state, after, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact (runKept_advanceSlot nextOk).trans (runKept_advanceSlots rest)

/-- Advancing to a later slot is a run step. -/
theorem runKept_processSlots {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) : RunKept state after := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨-, -, advanced⟩ := computed
  exact runKept_advanceSlots advanced

/-- The state transition of a block is a run step. -/
theorem runKept_stateTransition {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    RunKept state after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  exact (runKept_processSlots slotsOk).trans (runKept_processBlock blockOk)

/-- A run keeps the committees of each epoch up to its start plus `MIN_SEED_LOOKAHEAD`.

The epoch must also be at most the fixed epoch of activity of the start.

The first bound implies it when `MIN_SEED_LOOKAHEAD` is at most `MAX_SEED_LOOKAHEAD`.

The run must end before the mix that the seed of the epoch reads is written again. -/
theorem RunKept.committeesKept (run : RunKept state after)
    {epoch : Epoch}
    (final : epoch.toNat ≤ (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat)
    (fixed : epoch ≤ activityFixedEpoch state)
    (inRing : (getCurrentEpoch after).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    CommitteesKept epoch state after := by
  refine CommitteesKept.of_seed (run.active.getActiveValidatorIndices_eq fixed)
    (run.active.getActiveValidatorIndicesChecked_eq fixed)
    (getSeed_eq_of_mix _ fun shifted reads => run.mixes shifted fun written low high same => ?_)
  have lowLe := UInt64.le_iff_toNat_le.mp low
  have highLe := UInt64.le_iff_toNat_le.mp high
  have same := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
  exact Nat.mod_ne_of_sub_lt (low := written.toNat) (high := shifted.toNat)
    (length := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (by omega) (by omega) same.symm

end EthLib.Consensus

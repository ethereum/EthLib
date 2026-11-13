module

public import EthLib.Consensus.Proofs.Proposers
public import EthLib.Consensus.Proofs.Transition.Totality.SyncCommittee

/-!
# Proofs: the proposer lookahead of an epoch succeeds under bounds

From Fulu the epoch step draws the proposers of the epoch after the seed lookahead.

From Gloas the proposer of a slot is a weighted selection of one, as the sync committee draws.

Before Gloas the proposer search picks the same validator whenever that selection succeeds.

The proof assumes one candidate at the cap of the draw, active in that epoch: it is always accepted.

From Gloas a slashed validator is no candidate, so that one must not be slashed.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- The candidates to propose are no more than the active validators. -/
private theorem size_proposerCandidates_le (state : BeaconState preset fork)
    (active : Array ValidatorIndex) : (proposerCandidates state active).size ≤ active.size := by
  unfold proposerCandidates
  split
  · exact Array.size_filter_le
  · exact Nat.le_refl _

/-- Each candidate to propose is an active validator. -/
private theorem mem_of_mem_proposerCandidates {state : BeaconState preset fork}
    {active : Array ValidatorIndex} {index : ValidatorIndex}
    (member : index ∈ proposerCandidates state active) : index ∈ active := by
  unfold proposerCandidates at member
  split at member
  · exact (Array.mem_filter.mp member).1
  · exact member

/-- The proposer of a slot is drawn when a candidate is at the cap of the draw.

Each candidate must name a validator whose effective balance is at most that cap.

The products of the draw must fit in 64 bits.

At most `2^40` candidates keep the shuffle in range. -/
theorem computeSlotProposer_ok {state : BeaconState preset fork}
    {indices : Array ValidatorIndex} {seed : Bytes32}
    (fits : DrawFits preset fork)
    (known : ∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
      validator.effectiveBalance.toNat ≤ drawCap preset fork)
    (full : ∃ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
      validator.effectiveBalance.toNat = drawCap preset fork)
    (few : indices.size ≤ 2 ^ 40) :
    ∃ proposer, computeSlotProposer state indices seed = .ok proposer := by
  unfold computeSlotProposer
  have room : (1 : UInt64).toNat * indices.size < 2 ^ 64 := by
    change 1 * _ < _
    omega
  obtain ⟨selected, drawn⟩ := computeBalanceWeightedSelection_ok (seed := seed) (size := 1)
    (shuffleIndices := true) fits known full few room
  split
  · simp only [drawn, bind, Except.bind]
    exact ⟨_, rfl⟩
  · exact ⟨_, computeProposerIndex_of_computeBalanceWeightedSelection drawn⟩

/-- The assumptions under which the proposers of an epoch can be drawn from a state.

No effective balance is above the cap of the draw.

One validator active in the epoch is at that cap: an assumption on the registry, not a bound.

From Gloas that validator is not slashed, since a slashed one is no candidate.

The registry holds at most `2^40` validators. -/
structure ProposersDrawable (state : BeaconState preset fork) (epoch : Epoch) : Prop where
  /-- No effective balance is above the cap of the draw. -/
  capped : ∀ validator ∈ state.validators.data,
    validator.effectiveBalance.toNat ≤ drawCap preset fork
  /-- One validator active in the epoch, and unslashed from Gloas, is at the cap of the draw. -/
  full : ∃ validator ∈ state.validators.data, isActiveValidator validator epoch ∧
    (.glamsterdam ≤ fork → validator.slashed = false) ∧
    validator.effectiveBalance.toNat = drawCap preset fork
  /-- The registry holds at most `2^40` validators. -/
  few : state.validators.data.size ≤ 2 ^ 40

/-- The proposers of an epoch are drawn under bounds, with a validator at the cap of the draw.

The epoch plus the length of the history of mixes stays below `2^64`.

The seed lookahead is shorter than that history.

The first slot of the next epoch is at most `2^64`, so every slot of the epoch fits in 64 bits. -/
theorem getBeaconProposerIndices_ok {state : BeaconState preset fork} {epoch : Epoch}
    (fits : DrawFits preset fork)
    (seedRoom : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (drawable : ProposersDrawable state epoch) :
    ∃ proposers, getBeaconProposerIndices state epoch = .ok proposers := by
  obtain ⟨seed, seedOk⟩ := getSeed_ok (state := state) (epoch := epoch) DOMAIN_BEACON_PROPOSER
    seedRoom lookahead
  have checked := getActiveValidatorIndicesChecked_of_size_le (state := state)
    (by have := drawable.few; omega) epoch
  have lengthLe := length_getActiveValidatorIndices_le state epoch
  -- Each candidate names a validator of the registry, at most at the cap of the draw.
  have known : ∀ index ∈ proposerCandidates state
      (getActiveValidatorIndices state epoch).toArray, ∃ validator,
      getValidator state index = .ok validator ∧
        validator.effectiveBalance.toNat ≤ drawCap preset fork := by
    intro index member
    obtain ⟨validator, read, _⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp
      (List.mem_toArray.mp (mem_of_mem_proposerCandidates member))
    exact ⟨validator, by unfold getValidator; rw [read],
      drawable.capped validator (Array.mem_of_getElem? read)⟩
  have full : ∃ index ∈ proposerCandidates state
      (getActiveValidatorIndices state epoch).toArray, ∃ validator,
      getValidator state index = .ok validator ∧
        validator.effectiveBalance.toNat = drawCap preset fork := by
    obtain ⟨validator, member, active, unslashed, atCap⟩ := drawable.full
    obtain ⟨position, inside, rfl⟩ := Array.getElem_of_mem member
    have positionNat : (UInt64.ofNat position).toNat = position :=
      UInt64.toNat_ofNat_of_lt' (by
        have := drawable.few
        have : UInt64.size = 2 ^ 64 := rfl
        omega)
    have read : state.validators.data[(UInt64.ofNat position).toNat]? =
        some state.validators.data[position] := by
      rw [positionNat, Array.getElem?_eq_getElem inside]
    have listed : UInt64.ofNat position ∈ (getActiveValidatorIndices state epoch).toArray :=
      List.mem_toArray.mpr
        ((mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mpr ⟨_, read, active⟩)
    refine ⟨UInt64.ofNat position, ?_, _, by unfold getValidator; rw [read], atCap⟩
    unfold proposerCandidates
    split
    · next gloas =>
      refine Array.mem_filter.mpr ⟨listed, ?_⟩
      rw [read]
      simp [unslashed gloas]
    · exact listed
  have few : (proposerCandidates state (getActiveValidatorIndices state epoch).toArray).size ≤
      2 ^ 40 := by
    refine Nat.le_trans (size_proposerCandidates_le _ _) ?_
    simp only [List.size_toArray]
    have := drawable.few
    omega
  have startOk : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | pos
    · rw [zero]; simp
    · rw [Nat.add_mul] at slotRoom
      omega
  obtain ⟨start, startEq⟩ : ∃ start, computeStartSlotAtEpoch preset epoch = .ok start :=
    ⟨_, Uint64.mulChecked_of_lt startOk⟩
  obtain ⟨-, startNat⟩ := computeStartSlotAtEpoch_ok_iff.mp startEq
  have drawn : ∃ proposers, computeProposerIndices state epoch seed
      (proposerCandidates state (getActiveValidatorIndices state epoch).toArray) =
        .ok proposers := by
    unfold computeProposerIndices
    simp only [liftArith, startEq, bind, Except.bind, Except.mapError]
    have : ∃ proposers, (Vector.range preset.SLOTS_PER_EPOCH.toNat).mapM
        (fun offset => (do
          let slot ← liftArith (Uint64.addChecked start offset.toUInt64)
          computeSlotProposer state
            (proposerCandidates state (getActiveValidatorIndices state epoch).toArray)
            (proposerSlotSeed seed slot) :
          Except AccessorError ValidatorIndex)) = .ok proposers := by
      have each : ∀ offset ∈ (Vector.range preset.SLOTS_PER_EPOCH.toNat).toList, ∃ y,
          (do
            let slot ← liftArith (Uint64.addChecked start offset.toUInt64)
            computeSlotProposer state
              (proposerCandidates state (getActiveValidatorIndices state epoch).toArray)
              (proposerSlotSeed seed slot) : Except AccessorError ValidatorIndex) = .ok y := by
        intro offset member
        have lt : offset < preset.SLOTS_PER_EPOCH.toNat := by simpa using member
        have small := preset.SLOTS_PER_EPOCH.toNat_lt
        have fitsSlot : start.toNat + offset.toUInt64.toNat < 2 ^ 64 := by
          rw [startNat, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by
            have : UInt64.size = 2 ^ 64 := rfl
            omega)]
          rw [Nat.add_mul] at slotRoom
          omega
        obtain ⟨proposer, ok⟩ := computeSlotProposer_ok (state := state)
          (indices := proposerCandidates state (getActiveValidatorIndices state epoch).toArray)
          (seed := proposerSlotSeed seed (start + offset.toUInt64)) fits known full few
        exact ⟨proposer, by
          simp only [liftArith, Uint64.addChecked_of_lt fitsSlot, bind, Except.bind,
            Except.mapError]
          exact ok⟩
      choose! out outOk using each
      refine ⟨Vector.ofFn fun i => out i.val, vector_mapM_eq_ok_iff.mpr fun i hi => ?_⟩
      simpa using outOk i (by simpa using hi)
    exact this
  obtain ⟨proposers, drawn⟩ := drawn
  exact ⟨proposers, by
    simp only [getBeaconProposerIndices, checked, seedOk, drawn, bind, Except.bind]⟩

/-- From Fulu, the move of the proposer lookahead succeeds under bounds on the state.

A validator at the cap of the draw must be active in the epoch it draws.

The epoch it draws is the one after the seed lookahead.

That epoch plus the length of the history of mixes stays below `2^64`.

The seed lookahead is shorter than that history.

The first slot of the epoch after it is at most `2^64`, so every slot of it fits in 64 bits.

The step changes only the lookahead. -/
theorem processProposerLookahead_ok (fulu : .fusaka ≤ fork) {state : BeaconState preset fork}
    (fits : DrawFits preset fork)
    (seedRoom : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (drawable :
      ProposersDrawable state (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1)) :
    ∃ after, processProposerLookahead state fulu = .ok after ∧
      after = { state with proposerLookahead := fun _ => after.proposerLookahead fulu } := by
  have one : (1 : UInt64).toNat = 1 := rfl
  have firstFits : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < 2 ^ 64 := by
    omega
  have first := Uint64.toNat_add_of_lt firstFits
  have secondFits : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD).toNat +
      (1 : UInt64).toNat < 2 ^ 64 := by omega
  have second := Uint64.toNat_add_of_lt secondFits
  have epochNat : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1).toNat + 1 =
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2 := by omega
  obtain ⟨proposers, drawn⟩ := getBeaconProposerIndices_ok (state := state)
    (epoch := getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1) fits
    (by omega) lookahead (by rw [epochNat]; exact slotRoom) drawable
  unfold processProposerLookahead
  simp only [liftArith, Uint64.addChecked_of_lt firstFits, Uint64.addChecked_of_lt secondFits,
    bind, Except.bind, Except.mapError, drawn]
  exact ⟨_, rfl, rfl⟩

/-- The first lookahead of proposers succeeds under bounds; the upgrade to Fulu computes it.

It covers the current epoch and each epoch of the seed lookahead after it.

Each of these epochs has an active validator at the cap of the draw, unslashed from Gloas.

No effective balance is above that cap, and the registry holds at most `2^40` validators.

The products of the draw fit in 64 bits.

The last epoch drawn plus the length of the history of mixes stays below `2^64`.

The seed lookahead is shorter than that history.

The first slot of the epoch after the last one drawn is at most `2^64`.

So every slot drawn fits in 64 bits. -/
theorem initializeProposerLookahead_ok {state : BeaconState preset fork}
    (fits : DrawFits preset fork)
    (seedRoom : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (drawable : ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
      ProposersDrawable state (getCurrentEpoch state + offset.toUInt64)) :
    ∃ proposers, initializeProposerLookahead state = .ok proposers := by
  have each : ∀ offset ∈ (Vector.range (preset.MIN_SEED_LOOKAHEAD.toNat + 1)).toList, ∃ y,
      (do
        let epoch ← liftArith (Uint64.addChecked (getCurrentEpoch state) offset.toUInt64)
        getBeaconProposerIndices state epoch :
        Except AccessorError (Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat)) = .ok y := by
    intro offset member
    have lt : offset < preset.MIN_SEED_LOOKAHEAD.toNat + 1 := by simpa using member
    have offsetNat : offset.toUInt64.toNat = offset := by
      have small := preset.MIN_SEED_LOOKAHEAD.toNat_lt
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by
        have : UInt64.size = 2 ^ 64 := rfl
        omega)]
    have fitsEpoch : (getCurrentEpoch state).toNat + offset.toUInt64.toNat < 2 ^ 64 := by
      omega
    have epochNat := Uint64.toNat_add_of_lt fitsEpoch
    obtain ⟨proposers, drawn⟩ := getBeaconProposerIndices_ok (state := state)
      (epoch := getCurrentEpoch state + offset.toUInt64) fits (by omega) lookahead
      (by
        rw [epochNat, offsetNat]
        exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) slotRoom)
      (drawable offset (by omega))
    exact ⟨proposers, by
      simp only [liftArith, Uint64.addChecked_of_lt fitsEpoch, bind, Except.bind,
        Except.mapError]
      exact drawn⟩
  choose! out outOk using each
  have mapped := vector_mapM_eq_ok_iff (f := fun offset => (do
      let epoch ← liftArith (Uint64.addChecked (getCurrentEpoch state) offset.toUInt64)
      getBeaconProposerIndices state epoch :
      Except AccessorError (Vector ValidatorIndex preset.SLOTS_PER_EPOCH.toNat)))
    (xs := Vector.range (preset.MIN_SEED_LOOKAHEAD.toNat + 1))
    (ys := Vector.ofFn fun i => out i.val) |>.mpr fun i hi => by
      simpa using outOk i (by simpa using hi)
  unfold initializeProposerLookahead
  simp only [bind, Except.bind, pure, Except.pure] at mapped ⊢
  rw [mapped]
  exact ⟨_, rfl⟩

end EthLib.Consensus

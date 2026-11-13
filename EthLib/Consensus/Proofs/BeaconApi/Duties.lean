module

public import EthLib.Consensus.BeaconApi.Duties
public import EthLib.Consensus.Proofs.HonestValidator
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: the duty answers of the Beacon API

Each attester duty names a committee of its slot, and the validator's place in it.

A requested validator in a committee of the epoch has exactly one duty.

A request for an epoch after the next one is refused.

In the current epoch, each proposer duty names the proposer of its slot.

Each seat of a sync duty holds the key of the validator.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-- An attester duty comes from the committee assignment of its validator. -/
private theorem attesterDuty_some {state : BeaconState preset fork} {epoch : Epoch}
    {index : ValidatorIndex} {duty : AttesterDuty}
    (computed : attesterDuty state epoch index = .ok (some duty)) :
    ∃ committee, getCommitteeAssignment state epoch index =
        .ok (some (committee, duty.committeeIndex, duty.slot)) ∧
      duty.validatorIndex = index ∧ duty.committeeLength = committee.size.toUInt64 ∧
      duty.validatorCommitteeIndex = (committee.idxOf index).toUInt64 := by
  unfold attesterDuty at computed
  obtain ⟨validator, -, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨assignment, assigned, computed⟩ := bind_ok_iff.mp computed
  rw [mapError_ok_iff] at assigned
  match assignment, computed with
  | some (committee, committeeIndex, slot), computed =>
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at computed
    subst computed
    exact ⟨committee, assigned, rfl, rfl, rfl⟩

/-- Each attester duty comes from a requested validator. -/
private theorem attesterDuties_mem {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) {duty : AttesterDuty}
    (mem : duty ∈ duties) :
    ∃ index ∈ indices, attesterDuty state epoch index = .ok (some duty) := by
  unfold attesterDuties at computed
  obtain ⟨found, mapped, computed⟩ := bind_ok_iff.mp computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  obtain ⟨_, member, rfl⟩ := List.mem_filterMap.mp mem
  exact mapM_ok_mem mapped _ member

/-- Each attester duty names a committee of its slot that holds the validator.

The committee has the length of the duty, and the validator at the position of the duty. -/
theorem attesterDuties_committee {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) {duty : AttesterDuty}
    (mem : duty ∈ duties) :
    ∃ (committee : Array ValidatorIndex) (position : Nat),
      getBeaconCommittee state duty.slot duty.committeeIndex = .ok committee ∧
      duty.committeeLength = committee.size.toUInt64 ∧
      duty.validatorCommitteeIndex = position.toUInt64 ∧
      committee[position]? = some duty.validatorIndex := by
  obtain ⟨index, -, made⟩ := attesterDuties_mem computed mem
  obtain ⟨committee, assigned, named, length, position⟩ := attesterDuty_some made
  obtain ⟨-, -, read, member⟩ := getCommitteeAssignment_sound assigned
  refine ⟨committee, committee.idxOf index, read, length, position, ?_⟩
  rw [named]
  rcases committee with ⟨members⟩
  simp only [List.idxOf_toArray, List.getElem?_toArray]
  exact List.getElem?_idxOf (List.mem_toArray.mp member)

/-- A requested validator in a committee of the epoch has exactly one duty.

The request must not repeat an index. -/
theorem attesterDuties_complete {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} {duties : List AttesterDuty}
    (computed : attesterDuties state epoch indices = .ok duties) (distinct : indices.Nodup)
    {index : ValidatorIndex} (requested : index ∈ indices) {committee : Array ValidatorIndex}
    {committeeIndex : CommitteeIndex} {slot : Slot}
    (assigned :
      getCommitteeAssignment state epoch index = .ok (some (committee, committeeIndex, slot))) :
    (duties.filter (·.validatorIndex = index)).length = 1 := by
  unfold attesterDuties at computed
  obtain ⟨found, mapped, computed⟩ := bind_ok_iff.mp computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  clear computed
  induction indices generalizing found with
  | nil => simp at requested
  | cons first rest ih =>
    obtain ⟨head, tail, headOk, tailOk, rfl⟩ := mapM_cons_ok.mp mapped
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    by_cases same : first = index
    · subst same
      -- The requested validator has a duty, and no later index names it.
      obtain ⟨validator, validatorOk, headOk⟩ := bind_ok_iff.mp headOk
      rw [assigned] at headOk
      simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at headOk
      subst headOk
      have none : (tail.filterMap id).filter (·.validatorIndex = first) = [] := by
        refine List.filter_eq_nil_iff.mpr fun duty member named => ?_
        obtain ⟨_, member, rfl⟩ := List.mem_filterMap.mp member
        obtain ⟨other, otherMem, made⟩ := mapM_ok_mem tailOk _ member
        obtain ⟨_, -, otherNamed, -⟩ := attesterDuty_some made
        have named := of_decide_eq_true named
        exact absent (by rw [← named, otherNamed]; exact otherMem)
      rw [List.filterMap_cons_some (f := id) rfl, List.filter_cons_of_pos (by simp), none]
      rfl
    · have later : index ∈ rest := (List.mem_cons.mp requested).resolve_left (Ne.symm same)
      rw [← ih distinct later tail tailOk]
      cases head with
      | none => simp
      | some duty =>
        obtain ⟨_, -, named, -⟩ := attesterDuty_some headOk
        simp [named, same]

/-- A request for an epoch after the next one gets the error with code 400.

The request must name at least one validator. -/
theorem attesterDuties_epoch_bound {state : BeaconState preset fork} {epoch : Epoch}
    {indices : List ValidatorIndex} (nonempty : indices ≠ [])
    (far : (getCurrentEpoch state).toNat + 1 < epoch.toNat) :
    ∃ error, attesterDuties state epoch indices = .error error ∧ error.code = 400 := by
  obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  -- The next epoch fits in 64 bits, since the requested epoch is past it.
  have fits : (getCurrentEpoch state).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have := epoch.toNat_lt
    simp only [UInt64.toNat_one]
    omega
  have nextOk : Uint64.addChecked (getCurrentEpoch state) 1 = .ok (getCurrentEpoch state + 1) :=
    Uint64.addChecked_ok_iff.mpr ⟨fits, by rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]⟩
  have nextNat := (Uint64.addChecked_ok_iff.mp nextOk).2
  have beyond : ¬epoch ≤ getCurrentEpoch state + 1 := by
    rw [UInt64.le_iff_toNat_le, nextNat]
    simp only [UInt64.toNat_one]
    omega
  have tooFar : getCommitteeAssignment state epoch first =
      .error (.epochTooFar epoch (getCurrentEpoch state + 1)) := by
    unfold getCommitteeAssignment
    simp [nextOk, beyond, Except.mapError, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  cases validatorOk : requestedValidator state first with
  | error fault =>
    refine ⟨fault, ?_, ?_⟩
    · simp [attesterDuties, attesterDuty, validatorOk, List.mapM_cons, bind, Except.bind]
    · unfold requestedValidator at validatorOk
      cases found : getValidator state first with
      | error _ =>
        simp only [found, Except.mapError, Except.error.injEq] at validatorOk
        rw [← validatorOk]
        rfl
      | ok _ => simp [found, Except.mapError] at validatorOk
  | ok validator =>
    refine ⟨invalidEpoch epoch, ?_, rfl⟩
    simp [attesterDuties, attesterDuty, validatorOk, tooFar, List.mapM_cons, bind, Except.bind,
      Except.mapError, dutyError]

/-- Each proposer duty names the proposer at its offset, at that offset from the first slot. -/
private theorem proposerDuties_mem {state : BeaconState preset fork} {epoch : Epoch}
    {duties : List ProposerDuty} (computed : proposerDuties state epoch = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties) :
    ∃ (proposers : List ValidatorIndex) (start : Slot) (offset : Nat),
      epochProposers state epoch = .ok proposers ∧
      computeStartSlotAtEpoch preset epoch = .ok start ∧
      proposers[offset]? = some duty.validatorIndex ∧
      Uint64.addChecked start offset.toUInt64 = .ok duty.slot := by
  unfold proposerDuties at computed
  obtain ⟨proposers, proposersOk, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨start, startOk, computed⟩ := bind_ok_iff.mp computed
  rw [mapError_ok_iff] at startOk
  obtain ⟨⟨proposer, offset⟩, member, made⟩ := mapM_ok_mem computed _ mem
  obtain ⟨inside, entry⟩ := List.mem_zipIdx' member
  obtain ⟨slot, slotOk, made⟩ := bind_ok_iff.mp made
  rw [mapError_ok_iff] at slotOk
  obtain ⟨validator, -, made⟩ := bind_ok_iff.mp made
  simp only [pure, Except.pure, Except.ok.injEq] at made
  subst made
  refine ⟨proposers, start, offset, proposersOk, startOk, ?_, slotOk⟩
  rw [List.getElem?_eq_getElem inside, ← entry]

/-- Slot steps that reach no epoch start keep the registry, the RANDAO mixes and the lookahead. -/
private theorem advanceSlots_kept {config : Config} {checks : SignatureChecks} :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      (∀ step, 1 ≤ step → step ≤ count →
        (state.slot.toNat + step) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) →
      after.validators = state.validators ∧ after.randaoMixes = state.randaoMixes ∧
        after.proposerLookahead = state.proposerLookahead
  | 0, _, _, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, rfl⟩
  | count + 1, state, _, computed, inside => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, middleEq⟩ := advanceSlot_ok first
    -- The next slot starts no epoch, so the step only caches the slot.
    have noEpoch : ¬next % preset.SLOTS_PER_EPOCH = 0 := by
      intro zero
      have natural := congrArg UInt64.toNat zero
      rw [UInt64.toNat_mod, sum] at natural
      exact inside 1 le_rfl (by omega) natural
    simp only [epochIfLast, noEpoch, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have middleSlot : middle.slot.toNat = state.slot.toNat + 1 := by
      rw [middleEq]
      exact sum
    have kept := advanceSlots_kept (state := middle) count rest fun step low high => by
      have shifted := inside (step + 1) (by omega) (by omega)
      rwa [middleSlot, show state.slot.toNat + 1 + step = state.slot.toNat + (step + 1) by omega]
    refine ⟨kept.1.trans ?_, kept.2.1.trans ?_, kept.2.2.trans ?_⟩ <;> rw [middleEq, cachedEq]

/-- A current proposer duty is in the epoch, and a state at its slot with that data names it. -/
private theorem proposerDuties_current {state : BeaconState preset fork}
    {duties : List ProposerDuty}
    (computed : proposerDuties state (getCurrentEpoch state) = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties) :
    duty.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = (getCurrentEpoch state).toNat ∧
      ∀ other : BeaconState preset fork, other.slot = duty.slot →
        other.validators = state.validators → other.randaoMixes = state.randaoMixes →
        other.proposerLookahead = state.proposerLookahead →
        getBeaconProposerIndex other = .ok duty.validatorIndex := by
  obtain ⟨proposers, start, offset, proposersOk, startOk, entry, slotOk⟩ :=
    proposerDuties_mem computed mem
  obtain ⟨-, startNat⟩ := computeStartSlotAtEpoch_ok_iff.mp startOk
  unfold epochProposers at proposersOk
  -- The proposers of the current epoch are one per slot of the epoch, at most.
  have lt : offset < preset.SLOTS_PER_EPOCH.toNat := by
    by_cases fulu : .fusaka ≤ fork
    · simp [fulu, pure, Except.pure] at proposersOk
      subst proposersOk
      rw [List.getElem?_take] at entry
      split at entry
      · assumption
      · simp at entry
    · simp only [fulu, ↓reduceDIte, ↓reduceIte, bind_ok_iff, mapError_ok_iff, pure,
        Except.pure, Except.ok.injEq] at proposersOk
      obtain ⟨drawn, -, rfl⟩ := proposersOk
      simpa using (List.getElem?_eq_some_iff.mp entry).1
  have slotNat : duty.slot.toNat = start.toNat + offset := by
    obtain ⟨-, sum⟩ := Uint64.addChecked_ok_iff.mp slotOk
    have := preset.SLOTS_PER_EPOCH.toNat_lt
    rw [sum, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by omega
  have slotDiv :
      duty.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = (getCurrentEpoch state).toNat := by
    rw [slotNat, startNat, Nat.mul_comm, Nat.mul_add_div positive, Nat.div_eq_of_lt lt]
    rfl
  have slotMod : duty.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = offset := by
    rw [slotNat, startNat, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt lt]
  refine ⟨slotDiv, fun other otherSlot validators mixes lookahead => ?_⟩
  by_cases fulu : .fusaka ≤ fork
  · simp [fulu, pure, Except.pure] at proposersOk
    subst proposersOk
    have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := fun zero => by simp [zero] at positive
    have index : (other.slot % preset.SLOTS_PER_EPOCH).toNat = offset := by
      rw [UInt64.toNat_mod, otherSlot, slotMod]
    rw [List.getElem?_take_of_lt lt, Vector.getElem?_toList] at entry
    unfold getBeaconProposerIndex
    simp only [fulu, nonzero, ↓reduceDIte]
    simp only [lookahead, index, pure, Except.pure, Except.ok.injEq]
    exact (Vector.getElem?_eq_some_iff.mp entry).2
  · simp only [fulu, ↓reduceDIte, ↓reduceIte, bind_ok_iff, mapError_ok_iff, pure,
      Except.pure, Except.ok.injEq] at proposersOk
    obtain ⟨drawn, drawnOk, rfl⟩ := proposersOk
    have named : drawn[offset] = duty.validatorIndex := by
      simpa using (List.getElem?_eq_some_iff.mp entry).2
    have notGloas : ¬.glamsterdam ≤ fork := fun gloas =>
      fulu (Nat.le_trans (show Fork.fusaka.ctorIdx ≤ Fork.glamsterdam.ctorIdx by decide) gloas)
    -- The proposer at the offset is drawn from the active validators, with the seed of the slot.
    unfold getBeaconProposerIndices at drawnOk
    obtain ⟨active, activeOk, drawnOk⟩ := bind_ok_iff.mp drawnOk
    obtain ⟨seed, seedOk, drawnOk⟩ := bind_ok_iff.mp drawnOk
    unfold computeProposerIndices at drawnOk
    obtain ⟨start', startOk', drawnOk⟩ := bind_ok_iff.mp drawnOk
    rw [liftArith, mapError_ok_iff, startOk, Except.ok.injEq] at startOk'
    subst startOk'
    have drawnAt := vector_mapM_ok_getElem drawnOk offset lt
    simp only [Vector.getElem_range, liftArith, slotOk, Except.mapError, bind, Except.bind,
      computeSlotProposer, notGloas, ↓reduceIte, proposerCandidates, named] at drawnAt
    -- The other state reads the same epoch, seed, active validators and balances.
    have epoch : getCurrentEpoch other = getCurrentEpoch state := by
      rw [← UInt64.toNat_inj, getCurrentEpoch_toNat, otherSlot]
      exact slotDiv
    have seedOther : getSeed other (getCurrentEpoch state) DOMAIN_BEACON_PROPOSER =
        .ok seed := by
      rw [← seedOk]
      simp only [getSeed, getRandaoMix, mixes]
    have activeOther : getActiveValidatorIndicesChecked other (getCurrentEpoch state) =
        .ok active := by
      rw [← activeOk]
      simp only [getActiveValidatorIndicesChecked, validators]
    have drawOther : computeProposerIndex other active.toArray (proposerSlotSeed seed duty.slot) =
        .ok duty.validatorIndex := by
      rw [← drawnAt]
      simp only [computeProposerIndex, validators]
    unfold getBeaconProposerIndex
    simp only [fulu, ↓reduceDIte]
    simp only [epoch, seedOther, activeOther, bind, Except.bind]
    rw [← drawOther, otherSlot]
    rfl

/-- In the current epoch, each proposer duty after the slot of the state names its proposer.

The proposer is that of the state advanced to the slot of the duty. -/
theorem proposerDuties_beaconProposer {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {duties : List ProposerDuty}
    (computed : proposerDuties state (getCurrentEpoch state) = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties)
    (advanced : processSlots config checks state duty.slot = .ok after) :
    getBeaconProposerIndex after = .ok duty.validatorIndex := by
  obtain ⟨sameEpoch, named⟩ := proposerDuties_current computed mem
  obtain ⟨later, reached⟩ := processSlots_slot advanced
  have later := UInt64.lt_iff_toNat_lt.mp later
  have current := getCurrentEpoch_toNat state
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
  obtain ⟨_, _, advanced⟩ := advanced
  -- Every slot passed lies strictly inside the epoch of the duty, so no epoch step runs.
  obtain ⟨validators, mixes, lookahead⟩ := advanceSlots_kept _ advanced fun step low high => by
    intro zero
    have split := Nat.div_add_mod (state.slot.toNat + step) preset.SLOTS_PER_EPOCH.toNat
    have below := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have quotient : (state.slot.toNat + step) / preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch state).toNat := by
      refine Nat.le_antisymm ?_ ?_
      · rw [← sameEpoch]
        exact Nat.div_le_div_right (by omega)
      · rw [current]
        exact Nat.div_le_div_right (by omega)
    rw [quotient, zero] at split
    rw [← current] at below
    omega
  exact named after reached validators mixes lookahead

/-- The proposer duty at the slot of the state names the proposer of the state. -/
theorem proposerDuties_current_slot {state : BeaconState preset fork}
    {duties : List ProposerDuty}
    (computed : proposerDuties state (getCurrentEpoch state) = .ok duties)
    {duty : ProposerDuty} (mem : duty ∈ duties) (now : duty.slot = state.slot) :
    getBeaconProposerIndex state = .ok duty.validatorIndex :=
  (proposerDuties_current computed mem).2 state now.symm rfl rfl rfl

/-- Each seat of a sync duty holds the key of the validator, in the committee of the period.

A sync duty has at least one seat. -/
theorem syncDuties_seats {state : BeaconState preset fork} {altair : .altair ≤ fork}
    {epoch : Epoch} {indices : List ValidatorIndex} {duties : List SyncDuty}
    (computed : syncDuties state altair epoch indices = .ok duties) {duty : SyncDuty}
    (mem : duty ∈ duties) :
    ∃ committee validator, syncCommitteeOf state altair epoch = .ok committee ∧
      getValidator state duty.validatorIndex = .ok validator ∧
      duty.pubkey = validator.pubkey ∧ duty.validatorSyncCommitteeIndices ≠ [] ∧
      ∀ seat ∈ duty.validatorSyncCommitteeIndices,
        committee.pubkeys.toList[seat.toNat]? = some validator.pubkey := by
  unfold syncDuties at computed
  obtain ⟨committee, committeeOk, computed⟩ := bind_ok_iff.mp computed
  obtain ⟨found, mapped, computed⟩ := bind_ok_iff.mp computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  obtain ⟨_, member, rfl⟩ := List.mem_filterMap.mp mem
  obtain ⟨index, -, made⟩ := mapM_ok_mem mapped _ member
  unfold syncDuty at made
  obtain ⟨validator, validatorOk, made⟩ := bind_ok_iff.mp made
  unfold requestedValidator at validatorOk
  rw [mapError_ok_iff] at validatorOk
  refine ⟨committee, validator, committeeOk, ?_⟩
  -- The seats are those of the key in the committee, and there is at least one.
  have seated : duty.pubkey = validator.pubkey ∧ duty.validatorIndex = index ∧
      duty.validatorSyncCommitteeIndices = syncSeats committee validator.pubkey ∧
      syncSeats committee validator.pubkey ≠ [] := by
    split at made
    · simp [pure, Except.pure] at made
    · rename_i seats nonempty
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at made
      subst made
      exact ⟨rfl, rfl, rfl, nonempty⟩
  obtain ⟨key, named, seats, nonempty⟩ := seated
  refine ⟨named ▸ validatorOk, key, seats ▸ nonempty, fun seat inside => ?_⟩
  rw [seats] at inside
  simp only [syncSeats, List.mem_map, List.mem_filter, beq_iff_eq] at inside
  obtain ⟨⟨pubkey, position⟩, ⟨within, same⟩, rfl⟩ := inside
  obtain ⟨inside, entry⟩ := List.mem_zipIdx' within
  have small : position < 2 ^ 64 := by
    have := preset.SYNC_COMMITTEE_SIZE.toNat_lt
    simp only [Vector.length_toList] at inside
    omega
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  rw [List.getElem?_eq_getElem inside, ← entry]
  exact congrArg some same

/-- Before the second epoch, the dependent root of a lag of one is the genesis root. -/
theorem dependentRoot_genesis {state : BeaconState preset fork} {epoch : Epoch}
    {genesisRoot : Root} (early : epoch.toNat < 1) :
    dependentRoot state 1 epoch genesisRoot = .ok genesisRoot := by
  simp [dependentRoot, early, pure, Except.pure]

end EthLib.Consensus.BeaconApi

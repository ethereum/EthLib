module

public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: the beacon committees of an epoch do not change during it

A beacon committee of an epoch depends only on activity in that epoch and on one RANDAO mix.

That mix is the one `MIN_SEED_LOOKAHEAD + 1` epochs before.

A step keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`, capped at 2^64 - 1.

Before Altair, the steps of a block and of an epoch keep activity and write at most one mix.

Before Altair, the epoch step also moves the pending attestations of the current epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- Before Gloas, the registry holds fewer than 2^64 validators. -/
theorem BeaconState.validators_size_lt_of_lt_glamsterdam (before : fork < .glamsterdam)
    (state : BeaconState preset fork) : state.validators.data.size < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (state.validators.bound before) (UInt64.toNat_lt _)

/-- Two states agree on which positions of the registry are active, in each epoch up to a bound.

A position outside the registry counts as not active. -/
def ActiveKept {post : Base.Fork} (bound : Epoch) (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ epoch ≤ bound, ∀ position, isActiveAt after epoch position = isActiveAt state epoch position

theorem ActiveKept.refl (bound : Epoch) (state : BeaconState preset fork) :
    ActiveKept bound state state :=
  fun _ _ _ => rfl

theorem ActiveKept.trans {middle last : Base.Fork} {bound : Epoch}
    {first : BeaconState preset fork} {second : BeaconState preset middle}
    {third : BeaconState preset last} (one : ActiveKept bound first second)
    (two : ActiveKept bound second third) : ActiveKept bound first third :=
  fun epoch le position => (two epoch le position).trans (one epoch le position)

theorem ActiveKept.mono {post : Base.Fork} {bound lower : Epoch}
    {other : BeaconState preset post} (kept : ActiveKept bound state other)
    (le : lower ≤ bound) : ActiveKept lower state other :=
  fun epoch below position => kept epoch (UInt64.le_trans below le) position

/-- The fixed epoch of a state: the steps below keep the active validators of each epoch up to it.

They assume the registry after the step holds fewer than 2^64 validators.

It is the current epoch plus `MAX_SEED_LOOKAHEAD`, capped at the largest epoch.

Every activation or exit that a step sets lands after it, and an activation lands just after it.

The committees of an epoch are fixed only up to the current epoch plus `MIN_SEED_LOOKAHEAD`.

That bound comes from the RANDAO mix that their seed reads. -/
def activityFixedEpoch (state : BeaconState preset fork) : Epoch :=
  UInt64.ofNat (min ((getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat) (2 ^ 64 - 1))

/-- The fixed epoch of a state, as a natural number. -/
theorem activityFixedEpoch_toNat {post : Base.Fork} (state : BeaconState preset post) :
    (activityFixedEpoch state).toNat =
      min ((getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat) (2 ^ 64 - 1) := by
  rw [activityFixedEpoch, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- The current epoch is at most the fixed epoch. -/
theorem getCurrentEpoch_le_activityFixedEpoch (state : BeaconState preset fork) :
    getCurrentEpoch state ≤ activityFixedEpoch state := by
  rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
  have := (getCurrentEpoch state).toNat_lt
  omega

/-- A current epoch at least as late gives a fixed epoch at least as late. -/
theorem activityFixedEpoch_mono {post : Base.Fork} {other : BeaconState preset post}
    (le : getCurrentEpoch state ≤ getCurrentEpoch other) :
    activityFixedEpoch state ≤ activityFixedEpoch other := by
  rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat, activityFixedEpoch_toNat]
  have := UInt64.le_iff_toNat_le.mp le
  omega

/-- An epoch after the current epoch plus `MAX_SEED_LOOKAHEAD` is after the fixed epoch. -/
theorem activityFixedEpoch_lt_of_toNat_lt {epoch : Epoch}
    (later : (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < epoch.toNat) :
    activityFixedEpoch state < epoch := by
  rw [UInt64.lt_iff_toNat_lt, activityFixedEpoch_toNat]
  omega

/-- Two states with the same slot have the same fixed epoch. -/
theorem activityFixedEpoch_eq_of_slot {post : Base.Fork} {other : BeaconState preset post}
    (slot : other.slot = state.slot) : activityFixedEpoch other = activityFixedEpoch state := by
  simp only [activityFixedEpoch, getCurrentEpoch, slot]

/-- A step that keeps the slot, and activity in each epoch up to the fixed epoch of its state. -/
def ActiveStep (state after : BeaconState preset fork) : Prop :=
  after.slot = state.slot ∧ ActiveKept (activityFixedEpoch state) state after

/-- Every state is a step to itself. -/
theorem ActiveStep.refl (state : BeaconState preset fork) : ActiveStep state state :=
  ⟨rfl, ActiveKept.refl _ _⟩

/-- Two steps in a row keep the slot and activity up to the fixed epoch of the first state. -/
theorem ActiveStep.trans {first second third : BeaconState preset fork}
    (one : ActiveStep first second) (two : ActiveStep second third) : ActiveStep first third := by
  have epoch := activityFixedEpoch_eq_of_slot one.1
  exact ⟨two.1.trans one.1, one.2.trans (epoch ▸ two.2)⟩

/-- Two functions that agree on the elements of a list keep the same of them. -/
private theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {list : List α}, (∀ value ∈ list, f value = g value) →
      list.filterMap f = list.filterMap g
  | [], _ => rfl
  | first :: rest, same => by
    simp only [List.filterMap_cons, same first List.mem_cons_self,
      filterMap_congr_mem fun value member => same value (List.mem_cons_of_mem first member)]

/-- The positions of a list that pass a test, read over the positions of the list. -/
private theorem filterMap_zipIdx_eq_range_length {α : Type} (test : α → Bool)
    (list : List α) :
    (list.zipIdx.filterMap fun (value, index) =>
        if test value then some index.toUInt64 else none) =
      (List.range list.length).filterMap fun index =>
        if (list[index]?.map test).getD false then some index.toUInt64 else none := by
  generalize size : list.length = n
  induction n generalizing list with
  | zero =>
    rw [List.eq_nil_of_length_eq_zero size]
    rfl
  | succ n more =>
    have nonempty : list ≠ [] := by
      intro empty
      simp [empty] at size
    rw [← List.dropLast_concat_getLast nonempty] at size ⊢
    generalize list.dropLast = init at size ⊢
    generalize list.getLast nonempty = last
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at size
    rw [List.zipIdx_append, List.filterMap_append, List.range_succ, List.filterMap_append,
      more init size]
    congr 1
    · refine filterMap_congr_mem fun index member => ?_
      simp [List.getElem?_append_left (size ▸ List.mem_range.mp member)]
    · subst size
      rw [Nat.zero_add, List.zipIdx_singleton, List.filterMap_cons, List.filterMap_cons,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simp

/-- The positions of a list that pass a test, read over the first `n` positions. -/
private theorem filterMap_zipIdx_eq_range {α : Type} (test : α → Bool) (list : List α) :
    ∀ {n : Nat}, list.length ≤ n →
      (list.zipIdx.filterMap fun (value, index) =>
          if test value then some index.toUInt64 else none) =
        (List.range n).filterMap fun index =>
          if (list[index]?.map test).getD false then some index.toUInt64 else none
  | n, le => by
    induction n with
    | zero =>
      rw [filterMap_zipIdx_eq_range_length, Nat.le_zero.mp le]
    | succ n more =>
      rcases Nat.lt_or_ge n list.length with lt | ge
      · rw [filterMap_zipIdx_eq_range_length, Nat.le_antisymm le lt]
      · rw [more ge, List.range_succ, List.filterMap_append]
        simp [List.getElem?_eq_none ge]

/-- The active indices of an epoch, read over the first `n` positions of the registry. -/
private theorem getActiveValidatorIndices_eq_range {post : Base.Fork}
    (other : BeaconState preset post) (epoch : Epoch) {n : Nat}
    (le : other.validators.data.size ≤ n) :
    getActiveValidatorIndices other epoch = (List.range n).filterMap fun index =>
      if isActiveAt other epoch index then some index.toUInt64 else none := by
  unfold getActiveValidatorIndices
  rw [filterMap_zipIdx_eq_range (isActiveValidator · epoch) _ (by simpa using le)]
  simp [isActiveAt]

/-- Two states with the same activity in an epoch have the same active indices in it. -/
theorem ActiveKept.getActiveValidatorIndices_eq {post : Base.Fork} {bound epoch : Epoch}
    {other : BeaconState preset post} (kept : ActiveKept bound state other) (le : epoch ≤ bound) :
    getActiveValidatorIndices other epoch = getActiveValidatorIndices state epoch := by
  rw [getActiveValidatorIndices_eq_range other epoch (Nat.le_max_left _ state.validators.data.size),
    getActiveValidatorIndices_eq_range state epoch (Nat.le_max_right other.validators.data.size _)]
  exact filterMap_congr_mem fun index _ => by rw [kept epoch le index]

/-- The RANDAO mixes of two states agree, except perhaps at the position of one epoch. -/
def MixesKeptBut {post : Base.Fork} (written : Epoch) (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ epoch : Epoch,
    epoch % preset.EPOCHS_PER_HISTORICAL_VECTOR ≠ written % preset.EPOCHS_PER_HISTORICAL_VECTOR →
      readCircular after.randaoMixes.elements epoch = readCircular state.randaoMixes.elements epoch

/-- The beacon committees of the slots of an epoch are the same in two states. -/
def CommitteesKept {post : Base.Fork} (epoch : Epoch) (state : BeaconState preset fork)
    (after : BeaconState preset post) : Prop :=
  ∀ slot index, computeEpochAtSlot preset slot = epoch →
    getBeaconCommittee after slot index = getBeaconCommittee state slot index

theorem CommitteesKept.refl (epoch : Epoch) (state : BeaconState preset fork) :
    CommitteesKept epoch state state :=
  fun _ _ _ => rfl

theorem CommitteesKept.trans {middle last : Base.Fork} {epoch : Epoch}
    {first : BeaconState preset fork} {second : BeaconState preset middle}
    {third : BeaconState preset last} (one : CommitteesKept epoch first second)
    (two : CommitteesKept epoch second third) : CommitteesKept epoch first third :=
  fun slot index inside => (two slot index inside).trans (one slot index inside)

/-- Two states with the same active indices and attester seed of an epoch agree on its committees.
-/
theorem CommitteesKept.of_seed {post : Base.Fork} {other : BeaconState preset post}
    {epoch : Epoch}
    (active : getActiveValidatorIndices other epoch = getActiveValidatorIndices state epoch)
    (seed :
      getSeed other epoch DOMAIN_BEACON_ATTESTER = getSeed state epoch DOMAIN_BEACON_ATTESTER) :
    CommitteesKept epoch state other := by
  intro slot index inside
  unfold getBeaconCommittee attesterShuffle getCommitteeCountPerSlot
  subst inside
  simp only [active, seed]

/-- Two states with the same registry and the same RANDAO mixes have the same committees. -/
theorem CommitteesKept.of_eq {post : Base.Fork} {other : BeaconState preset post}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements) (epoch : Epoch) :
    CommitteesKept epoch state other :=
  CommitteesKept.of_seed (by unfold getActiveValidatorIndices; rw [validators])
    (by unfold getSeed getRandaoMix; rw [mixes])

/-- The seed of an epoch is the same in two states with the same mix at the position it reads.

That position is the epoch plus the length of the ring, less `MIN_SEED_LOOKAHEAD + 1`. -/
theorem getSeed_eq_of_mix {post : Base.Fork} {other : BeaconState preset post} {epoch : Epoch}
    (domainType : DomainType)
    (same : ∀ shifted : Epoch, shifted.toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 =
        epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
      readCircular other.randaoMixes.elements shifted =
        readCircular state.randaoMixes.elements shifted) :
    getSeed other epoch domainType = getSeed state epoch domainType := by
  unfold getSeed getRandaoMix
  -- Both seeds read the same position, and the mix there is the same.
  have reads : ∀ {γ : Type} (result : Except AccessorError Epoch)
      (finish : Bytes32 → Except AccessorError γ),
      (∀ shifted, result = .ok shifted → readCircular other.randaoMixes.elements shifted =
        readCircular state.randaoMixes.elements shifted) →
      (result >>= fun shifted => readCircular other.randaoMixes.elements shifted >>= finish) =
        (result >>= fun shifted => readCircular state.randaoMixes.elements shifted >>= finish) := by
    intro _ result finish same
    cases result with
    | error => rfl
    | ok shifted =>
      show readCircular other.randaoMixes.elements shifted >>= finish =
        readCircular state.randaoMixes.elements shifted >>= finish
      rw [same shifted rfl]
  refine reads _ _ fun shifted computed => same shifted ?_
  simp only [liftArith, mapError_ok_iff, bind_ok_iff] at computed
  obtain ⟨sum, sumOk, lower, lowerOk, shiftedOk⟩ := computed
  obtain ⟨-, sumEq⟩ := addChecked_ok_iff.mp sumOk
  obtain ⟨-, lowerEq⟩ := subChecked_ok_iff.mp lowerOk
  obtain ⟨above, shiftedEq⟩ := subChecked_ok_iff.mp shiftedOk
  simp only [UInt64.reduceToNat] at above shiftedEq
  omega

/-- The seed of an epoch reads only the mix of one position, which a nearby write misses.

The write is at the position of that epoch or of the next one.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
private theorem getSeed_eq_of_mixesKeptBut {post : Base.Fork} {other : BeaconState preset post}
    {epoch written : Epoch}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (mixes : MixesKeptBut written state other) (low : epoch ≤ written)
    (high : written.toNat ≤ epoch.toNat + 1) (domainType : DomainType) :
    getSeed other epoch domainType = getSeed state epoch domainType := by
  refine getSeed_eq_of_mix domainType fun shifted shiftedEq => mixes shifted fun same => ?_
  have lowLe := UInt64.le_iff_toNat_le.mp low
  -- The seed reads the mix `MIN_SEED_LOOKAHEAD + 1` epochs back, never that of the write.
  have same := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
  exact Nat.mod_ne_of_sub_lt (low := written.toNat) (high := shifted.toNat)
    (length := preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) (by omega) (by omega) same

/-- Two states agree on the committees of an epoch, when two facts hold.

They agree on activity in each epoch up to that one.

Their RANDAO mixes differ at most at one position, of that epoch or of the next one.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem CommitteesKept.of_activeKept {post : Base.Fork} {other : BeaconState preset post}
    {epoch written : Epoch}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (active : ActiveKept epoch state other) (mixes : MixesKeptBut written state other)
    (low : epoch ≤ written) (high : written.toNat ≤ epoch.toNat + 1) :
    CommitteesKept epoch state other :=
  CommitteesKept.of_seed (active.getActiveValidatorIndices_eq (UInt64.le_refl _))
    (getSeed_eq_of_mixesKeptBut apart mixes low high _)

/-- Two states agree on the attesters of an attestation, given the same active indices and seed.

Both are those of the epoch of its slot. -/
private theorem getAttestingIndices_eq_of_seed {other : BeaconState preset fork}
    {attestation : Attestation preset fork}
    (active : getActiveValidatorIndices other (computeEpochAtSlot preset attestation.data.slot) =
      getActiveValidatorIndices state (computeEpochAtSlot preset attestation.data.slot))
    (seed : getSeed other (computeEpochAtSlot preset attestation.data.slot)
        DOMAIN_BEACON_ATTESTER =
      getSeed state (computeEpochAtSlot preset attestation.data.slot) DOMAIN_BEACON_ATTESTER) :
    getAttestingIndices other attestation = getAttestingIndices state attestation := by
  unfold getAttestingIndices attesterShuffle getCommitteeCountPerSlot
  simp only [active, seed]

/-- Two states with the same registry and RANDAO mixes agree on the attesters of an attestation.
-/
theorem getAttestingIndices_eq_of_eq {other : BeaconState preset fork}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements)
    (attestation : Attestation preset fork) :
    getAttestingIndices other attestation = getAttestingIndices state attestation :=
  getAttestingIndices_eq_of_seed (by unfold getActiveValidatorIndices; rw [validators])
    (by unfold getSeed getRandaoMix; rw [mixes])

/-- Two states agree on the attesters of an attestation, when two facts hold.

They agree on activity in each epoch up to the epoch of its slot.

Their RANDAO mixes differ at most at one position, of that epoch or of the next one.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem getAttestingIndices_eq_of_activeKept {other : BeaconState preset fork}
    {attestation : Attestation preset fork} {written : Epoch}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (active : ActiveKept (computeEpochAtSlot preset attestation.data.slot) state other)
    (mixes : MixesKeptBut written state other)
    (low : computeEpochAtSlot preset attestation.data.slot ≤ written)
    (high : written.toNat ≤ (computeEpochAtSlot preset attestation.data.slot).toNat + 1) :
    getAttestingIndices other attestation = getAttestingIndices state attestation :=
  getAttestingIndices_eq_of_seed (active.getActiveValidatorIndices_eq (UInt64.le_refl _))
    (getSeed_eq_of_mixesKeptBut apart mixes low high _)

/-! ## Exits and slashings -/

/-- Two states with the same registry agree on activity at every epoch. -/
theorem ActiveKept.of_validators {post : Base.Fork} {other : BeaconState preset post}
    (validators : other.validators.data = state.validators.data) (bound : Epoch) :
    ActiveKept bound state other := by
  intro epoch _ position
  simp only [isActiveAt, validators]

/-- A step that keeps the registry and the slot keeps activity. -/
theorem ActiveStep.of_validators (validators : after.validators.data = state.validators.data)
    (slot : after.slot = state.slot) : ActiveStep state after :=
  ⟨slot, ActiveKept.of_validators validators _⟩

/-- A write of one validator changes activity only at its position. -/
private theorem isActiveAt_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) (epoch : Epoch) (position : Nat) :
    isActiveAt after epoch position =
      if position = index.toNat then isActiveValidator validator epoch
      else isActiveAt state epoch position := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  unfold isActiveAt
  split
  · rename_i same
    subst same
    simp [BeaconState.putValidator, inside]
  · rename_i other
    simp [BeaconState.putValidator, Ne.symm other]

/-- A write of a validator with the activity of the old one, up to a bound, keeps activity. -/
private theorem activeKept_setValidator {bound : Epoch} {index : ValidatorIndex}
    {validator old : Validator} (found : getValidator state index = .ok old)
    (same : ∀ epoch ≤ bound, isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : ActiveKept bound state after := by
  intro epoch le position
  rw [isActiveAt_setValidator set]
  split
  · rename_i here
    subst here
    rw [same epoch le]
    simp [isActiveAt, getValidator_eq_ok_iff.mp found]
  · rfl

/-- A write of a validator with the activity of the old one keeps the slot and activity. -/
theorem activeStep_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : ActiveStep state after := by
  have active := activeKept_setValidator found same set
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨rfl, active⟩

/-- A new exit epoch after a bound, from the far future, keeps activity up to the bound.

The activation epoch must stay the same. -/
theorem isActiveValidator_eq_of_exit {validator old : Validator} {bound epoch : Epoch}
    (activation : validator.activationEpoch = old.activationEpoch)
    (far : old.exitEpoch = FAR_FUTURE_EPOCH) (later : bound < validator.exitEpoch)
    (le : epoch ≤ bound) : isActiveValidator validator epoch = isActiveValidator old epoch := by
  have le := UInt64.le_iff_toNat_le.mp le
  have later := UInt64.lt_iff_toNat_lt.mp later
  have bounded := validator.exitEpoch.toNat_lt
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  simp only [isActiveValidator, activation, far]
  congr 1
  simp only [decide_eq_decide, UInt64.lt_iff_toNat_lt, farNat]
  omega

/-- A new activation epoch after a bound keeps activity up to the bound.

The old activation epoch must be the far future or after the bound. -/
theorem isActiveValidator_eq_of_activation {validator old : Validator} {bound epoch : Epoch}
    (pending : old.activationEpoch = FAR_FUTURE_EPOCH ∨ bound < old.activationEpoch)
    (later : bound < validator.activationEpoch) (le : epoch ≤ bound) :
    isActiveValidator validator epoch = isActiveValidator old epoch := by
  have le := UInt64.le_iff_toNat_le.mp le
  have later := UInt64.lt_iff_toNat_lt.mp later
  have bounded := validator.activationEpoch.toNat_lt
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have pending : old.activationEpoch.toNat = 2 ^ 64 - 1 ∨ bound.toNat < old.activationEpoch.toNat :=
    pending.imp (fun far => by rw [far, farNat]) UInt64.lt_iff_toNat_lt.mp
  simp only [isActiveValidator, UInt64.le_iff_toNat_le]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The exit queue gives an exit epoch after the current epoch plus `MAX_SEED_LOOKAHEAD`.

That holds before Electra and from it. -/
theorem exitQueue_lt {exitBalance : Gwei} {queued : BeaconState preset fork} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (queued, exitEpoch)) :
    (getCurrentEpoch state).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < exitEpoch.toNat := by
  unfold exitQueue at computed
  split at computed
  · rename_i electra
    cases first : computeActivationExitEpoch preset (getCurrentEpoch state) with
    | error =>
      simp [computeExitEpochAndUpdateChurn, first, liftArith, Except.mapError, bind,
        Except.bind] at computed
    | ok firstEpoch =>
      have early :=
        UInt64.le_iff_toNat_le.mp (computeExitEpochAndUpdateChurn_first first computed).1
      have firstEq := (computeActivationExitEpoch_ok_iff.mp first).2
      omega
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨epoch, epochOk, -, rfl⟩ := computed
    simp only [exitQueueEpoch, bind_ok_iff, liftArith, mapError_ok_iff] at epochOk
    obtain ⟨earliest, earliestOk, rest⟩ := epochOk
    have earliestEq := (computeActivationExitEpoch_ok_iff.mp earliestOk).2
    have latest := UInt64.le_iff_toNat_le.mp (le_foldl_maxExitEpoch
      (state.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)) earliest).1
    split at rest
    · have := (addChecked_ok_iff.mp (mapError_ok_iff.mp rest)).2
      simp only [UInt64.reduceToNat] at this
      omega
    · simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      omega

/-! ## Steps that keep activity, the mixes and the pending attestations -/

/-- Two states with the same RANDAO mixes and the same pending attestations. -/
private def Untouched (state after : BeaconState preset fork) : Prop :=
  after.randaoMixes = state.randaoMixes ∧
    after.previousEpochAttestations = state.previousEpochAttestations ∧
    after.currentEpochAttestations = state.currentEpochAttestations

/-- A step that keeps activity up to the fixed epoch, the mixes, the attestations and the slot. -/
private def Keeps (state after : BeaconState preset fork) : Prop :=
  Untouched state after ∧ ActiveKept (activityFixedEpoch state) state after ∧
    after.slot = state.slot

private theorem Keeps.refl (state : BeaconState preset fork) : Keeps state state :=
  ⟨⟨rfl, rfl, rfl⟩, ActiveKept.refl _ _, rfl⟩

private theorem Keeps.trans {first second third : BeaconState preset fork}
    (one : Keeps first second) (two : Keeps second third) : Keeps first third := by
  have epoch := activityFixedEpoch_eq_of_slot one.2.2
  exact ⟨⟨two.1.1.trans one.1.1, two.1.2.1.trans one.1.2.1, two.1.2.2.trans one.1.2.2⟩,
    one.2.1.trans (epoch ▸ two.2.1), two.2.2.trans one.2.2⟩

private theorem Keeps.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (keeps : ∀ s x s', step s x = .ok s' → Keeps s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Keeps state after :=
  foldlM_ok_invariant (Keeps state) (fun _ _ _ before ok => before.trans (keeps _ _ _ ok))
    (Keeps.refl state) computed

/-- A step that keeps the registry, the mixes, the attestations and the slot keeps them all. -/
private theorem Keeps.of_eq (validators : after.validators = state.validators)
    (randaoMixes : after.randaoMixes = state.randaoMixes)
    (previous : after.previousEpochAttestations = state.previousEpochAttestations)
    (current : after.currentEpochAttestations = state.currentEpochAttestations)
    (slot : after.slot = state.slot) : Keeps state after :=
  ⟨⟨randaoMixes, previous, current⟩,
    ActiveKept.of_validators (congrArg (·.data) validators) _, slot⟩

private theorem Keeps.activeStep (keeps : Keeps state after) : ActiveStep state after :=
  ⟨keeps.2.2, keeps.2.1⟩

private theorem keeps_setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : Keeps state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact Keeps.of_eq rfl rfl rfl rfl rfl

private theorem keeps_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Keeps state after :=
  keeps_setBalance (increaseBalance_ok computed).choose_spec

private theorem keeps_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Keeps state after :=
  keeps_setBalance (decreaseBalance_ok computed).choose_spec

private theorem keeps_setValidator {index : ValidatorIndex} {validator old : Validator}
    (found : getValidator state index = .ok old)
    (same : ∀ epoch ≤ activityFixedEpoch state,
      isActiveValidator validator epoch = isActiveValidator old epoch)
    (set : state.setValidator index validator = .ok after) : Keeps state after := by
  have step := activeStep_setValidator found same set
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨⟨rfl, rfl, rfl⟩, step.2, rfl⟩

/-- Starting an exit keeps activity up to the fixed epoch, at every fork.

The exit epoch it sets is after that epoch. -/
private theorem keeps_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Keeps state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, exitEpoch, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Keeps.refl _
  have later := exitQueue_lt queue
  obtain ⟨left, earliest, queuedEq⟩ := exitQueue_eq queue
  have kept : Keeps state queued := by
    rw [queuedEq]
    exact Keeps.of_eq rfl rfl rfl rfl rfl
  have found' : getValidator queued index = .ok validator := by
    rw [queuedEq]
    exact found
  have epoch : getCurrentEpoch queued = getCurrentEpoch state := by
    simp only [getCurrentEpoch, kept.2.2]
  -- The validator had not started to exit, and its new exit epoch is after the bound.
  refine kept.trans (keeps_setValidator found' (fun _ le => ?_) set)
  exact isActiveValidator_eq_of_exit rfl far
    (activityFixedEpoch_lt_of_toNat_lt (by rw [epoch]; exact later)) le

private theorem keeps_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Keeps state after := by
  obtain ⟨exited, validator, _, marked, _, _, slashings, lowered, _, _, raised, last, exitedOk,
    found, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok computed
  -- Marking the validator slashed keeps its activation and exit epochs.
  refine (keeps_initiateValidatorExit exitedOk).trans <|
    (keeps_setValidator
      (validator := { validator with slashed := true, withdrawableEpoch := _ })
      found (fun _ _ => rfl) markedOk).trans <|
    (Keeps.of_eq rfl rfl rfl rfl rfl : Keeps marked { marked with slashings }).trans <|
    (keeps_decreaseBalance loweredOk).trans <| (keeps_increaseBalance raisedOk).trans <|
    (keeps_increaseBalance lastOk).trans ?_
  subst done
  split <;> exact Keeps.refl _

/-! ## Blocks and epochs before Altair -/

/-- Before Altair: a step of a block other than an attestation.

It is a block frame, and keeps activity up to the current epoch.

It writes at most the RANDAO mix of the current epoch.

It keeps the pending attestations of both epochs. -/
structure PendingFrame (state after : BeaconState preset fork) : Prop
    extends BlockFrame state after where
  active : ActiveKept (getCurrentEpoch state) state after
  mixes : MixesKeptBut (getCurrentEpoch state) state after
  previousPending : ∀ before : fork < .altair,
    after.previousEpochAttestations before = state.previousEpochAttestations before
  currentPending : ∀ before : fork < .altair,
    after.currentEpochAttestations before = state.currentEpochAttestations before

theorem PendingFrame.refl (state : BeaconState preset fork) : PendingFrame state state :=
  ⟨BlockFrame.refl state, ActiveKept.refl _ state, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem PendingFrame.trans {first second third : BeaconState preset fork}
    (one : PendingFrame first second) (two : PendingFrame second third) :
    PendingFrame first third := by
  have epoch : getCurrentEpoch second = getCurrentEpoch first := by
    simp only [getCurrentEpoch, one.slot]
  refine ⟨one.toBlockFrame.trans two.toBlockFrame, one.active.trans (epoch ▸ two.active),
    fun other apart => (two.mixes other (epoch ▸ apart)).trans (one.mixes other apart),
    fun before => (two.previousPending before).trans (one.previousPending before),
    fun before => (two.currentPending before).trans (one.currentPending before)⟩

/-- A block frame that keeps activity, the mixes and the pending attestations is a pending frame.
-/
private theorem PendingFrame.of_keeps (frame : BlockFrame state after)
    (keeps : Keeps state after) : PendingFrame state after :=
  ⟨frame, keeps.2.1.mono (getCurrentEpoch_le_activityFixedEpoch _), fun _ _ => by rw [keeps.1.1],
    fun before => by rw [keeps.1.2.1], fun before => by rw [keeps.1.2.2]⟩

/-! ## The steps of a block before Altair -/

private theorem pendingFrame_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : PendingFrame state after := by
  have frame := frame_processBlockHeader computed
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact PendingFrame.of_keeps frame (Keeps.of_eq rfl rfl rfl rfl rfl)

private theorem pendingFrame_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : PendingFrame state after := by
  have frame := frame_processEth1Data computed
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact PendingFrame.of_keeps frame (Keeps.of_eq (by rw [← rest]) (by rw [← rest])
    (by rw [← rest]) (by rw [← rest]) (by rw [← rest]))

/-- The RANDAO step writes only the mix of the current epoch. -/
theorem mixesKeptBut_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    MixesKeptBut (getCurrentEpoch state) state after := by
  obtain ⟨_, _, _, _, mix, randaoMixes, _, _, _, _, _, _, written, rfl⟩ :=
    processRandao_eq computed
  intro other apart
  have plain := writeCircularRooted_elements state.randaoMixes (getCurrentEpoch state)
    (Vector.zipWith (· ^^^ ·) mix
      (Cryptography.Hash.Sha256.hash32 (Base.packBytes body.randaoReveal)))
  rw [written] at plain
  exact readCircular_writeCircular_of_ne plain.symm (Ne.symm apart)

private theorem pendingFrame_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : PendingFrame state after := by
  have frame := frame_processRandao computed
  have mixes := mixesKeptBut_processRandao computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact ⟨frame, ActiveKept.of_validators rfl _, mixes, fun _ => rfl, fun _ => rfl⟩

private theorem pendingFrame_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    PendingFrame state after := by
  have frame := frame_processProposerSlashing computed
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact PendingFrame.of_keeps frame (keeps_slashValidator slashed)

private theorem pendingFrame_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    PendingFrame step.1 next.1 := by
  have frame := frame_slashIfSlashable computed
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact PendingFrame.of_keeps frame (keeps_slashValidator slashed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact PendingFrame.refl _

private theorem pendingFrame_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    PendingFrame state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => PendingFrame state step.1)
    (fun _ _ _ before ok => before.trans (pendingFrame_slashIfSlashable ok))
    (show PendingFrame state (state, false).1 from PendingFrame.refl state) folded

/-- A validator from a deposit is active in no epoch. -/
theorem isActiveValidator_getValidatorFromDeposit {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} (epoch : Epoch) :
    isActiveValidator (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount)
      epoch = false := by
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have bounded := epoch.toNat_lt
  simp only [getValidatorFromDeposit, isActiveValidator, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt, farNat, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- A new validator keeps the slot and activity, at every fork.

Its index is the size of the registry, so it replaces no validator. -/
theorem activeStep_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    ActiveStep state after := by
  have pushed := addValidatorToRegistry_validators_eq_push computed
  refine ⟨(frame_addValidatorToRegistry computed).slot, fun epoch _ position => ?_⟩
  unfold isActiveAt
  rw [pushed, Array.getElem?_push]
  split
  · rename_i last
    subst last
    simp [isActiveValidator_getValidatorFromDeposit]
  · rfl

/-- Before Altair, a new validator is never active, so adding it keeps activity. -/
private theorem keeps_addValidatorToRegistry (before : fork < .altair)
    {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Keeps state after := by
  have step := activeStep_addValidatorToRegistry computed
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  unfold addValidatorToRegistry at computed
  simp only [notAltair, ↓reduceDIte] at computed
  split at computed
  · cases computed
    exact ⟨⟨rfl, rfl, rfl⟩, step.2, step.1⟩
  · cases computed

/-- Before Altair, a deposit is a block frame that keeps the activity and the pending attestations.

It keeps every RANDAO mix but the one of the current epoch. -/
theorem pendingFrame_processDeposit (before : fork < .altair) {deposit : Deposit}
    {hegota : fork < .hegota}
    (computed : processDeposit config checks hegota state deposit = .ok after) :
    PendingFrame state after := by
  have frame := frame_processDeposit computed
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  have notElectra : ¬Fork.pectra ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide : Fork.altair < Fork.pectra))
  unfold applyDeposit at applied
  simp only [notElectra, ↓reduceDIte] at applied
  -- Recording the deposit index changes neither activity nor the mixes nor the attestations.
  generalize recorded : { state with eth1DepositIndex := fun _ => next } = middle at applied
  have kept : Keeps state middle := by
    subst recorded
    exact Keeps.of_eq rfl rfl rfl rfl rfl
  have parts : Keeps middle after := by
    unfold applyPendingDeposit at applied
    split at applied
    · split at applied
      · cases applied
        exact Keeps.refl _
      simp only [bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      split at applied
      · exact keeps_addValidatorToRegistry before applied
      · simp only [pure, Except.pure, Except.ok.injEq] at applied
        subst applied
        exact Keeps.refl _
    · simp only [liftAccessor_ok, bind_ok_iff] at applied
      obtain ⟨_, _, applied⟩ := applied
      exact keeps_increaseBalance applied
  exact PendingFrame.of_keeps frame (kept.trans parts)

private theorem pendingFrame_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    PendingFrame state after := by
  have frame := frame_processVoluntaryExit computed
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact PendingFrame.of_keeps frame (keeps_initiateValidatorExit exited)

/-- Before Altair, a block is a pending frame, its attestations in order, then a pending frame.

The attestations read the parent slot from the latest block header before the block. -/
theorem processBlock_pendingSplit (before : fork < .altair) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ first last, PendingFrame state first ∧
      block.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) first = .ok last ∧
      PendingFrame last after := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  have notCapella : ¬Fork.shapella ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide : Fork.altair < Fork.shapella))
  have notElectra : ¬Fork.pectra ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide : Fork.altair < Fork.pectra))
  have notGloas : ¬Fork.glamsterdam ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide : Fork.altair < Fork.glamsterdam))
  unfold processBlock at computed
  simp only [notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨headed, headerOk, revealed, randaoOk, voted, eth1Ok, operationsOk⟩ := computed
  unfold processOperations at operationsOk
  simp only [notGloas, notElectra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at operationsOk
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, attested, attestedOk, _, depositedOk, _,
    exitsOk, changed, changesOk, requestsOk⟩ := operationsOk
  simp only [processBlsToExecutionChanges, notCapella, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at changesOk requestsOk
  subst changesOk requestsOk
  have proposers := foldlM_ok_invariant (PendingFrame voted)
    (fun _ _ _ holds ok => holds.trans (pendingFrame_processProposerSlashing ok))
    (PendingFrame.refl voted) proposersOk
  have attesters := foldlM_ok_invariant (PendingFrame voted)
    (fun _ _ _ holds ok => holds.trans (pendingFrame_processAttesterSlashing ok)) proposers
    attestersOk
  have deposits := foldlM_ok_invariant (PendingFrame attested)
    (fun _ _ _ holds ok => holds.trans (pendingFrame_processDeposit before ok))
    (PendingFrame.refl attested) depositedOk
  have exits := foldlM_ok_invariant (PendingFrame attested)
    (fun _ _ _ holds ok => holds.trans (pendingFrame_processVoluntaryExit ok)) deposits exitsOk
  exact ⟨_, attested, (pendingFrame_processBlockHeader headerOk).trans <|
    (pendingFrame_processRandao randaoOk).trans <| (pendingFrame_processEth1Data eth1Ok).trans
      attesters, attestedOk, exits⟩

/-- An attestation keeps the registry and the RANDAO mixes, at every fork. -/
theorem processAttestation_registry {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    after.validators = state.validators ∧ after.randaoMixes = state.randaoMixes := by
  by_cases altair : Fork.altair ≤ fork
  · unfold processAttestation at computed
    simp only [altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    -- The flags and the proposer reward leave the registry alone, and so does a payment.
    have last : after.validators = raised.validators ∧ after.randaoMixes = raised.randaoMixes := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact ⟨rfl, rfl⟩
      · cases final
        exact ⟨rfl, rfl⟩
    obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
    obtain ⟨_, rfl⟩ := setBalance_ok set
    rw [last.1, last.2]
    unfold setEpochParticipation
    split <;> exact ⟨rfl, rfl⟩
  · obtain ⟨_, -, -, -, -, recorded, -⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) computed
    have kept := recordPendingAttestation_ok recorded
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      rw [← rest]
      exact ⟨rfl, rfl⟩

/-- An attestation that the step accepts has its slot in the previous or the current epoch.

That holds at every fork. -/
theorem processAttestation_slotEpoch {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    computeEpochAtSlot preset attestation.data.slot = getPreviousEpoch state ∨
      computeEpochAtSlot preset attestation.data.slot = getCurrentEpoch state := by
  by_cases altair : Fork.altair ≤ fork
  · unfold processAttestation at computed
    simp only [altair, ↓reduceDIte] at computed
    unfold processAttestationAltair at computed
    simp only [bind_ok_iff, ensure_ok_iff] at computed
    obtain ⟨_, recent, _, slotEpoch, -⟩ := computed
    exact slotEpoch ▸ recent
  · obtain ⟨recent, slotEpoch, -⟩ := processAttestation_checks (Nat.lt_of_not_le altair) computed
    exact slotEpoch ▸ recent

/-! ## The steps of an epoch before Altair -/

private theorem keeps_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : Keeps state after := by
  have deltas : ∀ {state after : BeaconState preset fork} {all : Array Gwei × Array Gwei},
      applyAllDeltas state all = .ok after → Keeps state after := fun computed =>
    Keeps.foldlM (fun _ _ _ ok => by
      simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, raised, lowered⟩ := ok
      exact (keeps_increaseBalance raised).trans (keeps_decreaseBalance lowered)) computed
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Keeps.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact Keeps.foldlM (fun _ _ _ ok => deltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact deltas applied

private theorem keeps_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : Keeps state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  -- Joining the queue changes only the eligibility epoch.
  have same : queued.activationEpoch = validator.activationEpoch ∧
      queued.exitEpoch = validator.exitEpoch := by
    unfold queueForActivation at queuedOk
    split at queuedOk
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
      obtain ⟨_, _, rfl⟩ := queuedOk
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at queuedOk
      exact queuedOk ▸ ⟨rfl, rfl⟩
  have set : Keeps state marked := keeps_setValidator found
    (fun _ _ => by simp only [isActiveValidator, same.1, same.2]) markedOk
  split at computed
  · rw [liftAccessor_ok] at computed
    exact set.trans (keeps_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- Activating validators that are not yet active keeps activity up to the fixed epoch.

Each must have the far-future activation epoch, or one after the fixed epoch. -/
private theorem keeps_foldlM_activateValidator :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      (∀ index ∈ indices, ∀ validator, getValidator state index = .ok validator →
        validator.activationEpoch = FAR_FUTURE_EPOCH ∨
          activityFixedEpoch state < validator.activationEpoch) →
      indices.foldlM activateValidator state = .ok after → Keeps state after
  | [], state, after, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Keeps.refl _
  | index :: rest, state, after, pending, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith,
      mapError_ok_iff] at step
    obtain ⟨validator, found, activation, activationOk, set⟩ := step
    have activationEq := (computeActivationExitEpoch_ok_iff.mp activationOk).2
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    -- Neither the old nor the new activation epoch is at or before the fixed epoch.
    have first : Keeps state middle := keeps_setValidator found (fun _ le =>
      isActiveValidator_eq_of_activation (pending index List.mem_cons_self validator found)
        (activityFixedEpoch_lt_of_toNat_lt (by simp only [activationEq]; omega)) le) set
    refine first.trans (keeps_foldlM_activateValidator (fun other member written ok => ?_)
      computed)
    rw [activityFixedEpoch_eq_of_slot first.2.2]
    by_cases same : other = index
    · subst same
      rw [getValidator_setValidator_self set] at ok
      cases ok
      refine .inr (activityFixedEpoch_lt_of_toNat_lt ?_)
      simp only [activationEq]
      omega
    · rw [getValidator_setValidator_of_ne set same] at ok
      exact pending other (List.mem_cons_of_mem index member) written ok

private theorem keeps_processRegistryUpdates (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) : Keeps state after := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  unfold processRegistryUpdates at computed
  simp only [notElectra, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have first := Keeps.foldlM (fun _ _ _ ok => keeps_updateRegistryEntry ok) updatedOk
  refine first.trans (keeps_foldlM_activateValidator (fun index member validator found => ?_)
    activated)
  -- The queue holds only validators whose activation epoch is still the far future.
  have queued := activationEpochAt_of_mem_activationQueue
    (updated.validators.bound (Nat.lt_trans before (by decide))) (List.mem_of_mem_take member)
  simp only [activationEpochAt, found, Except.map] at queued
  exact .inl (Except.ok.inj queued)

private theorem keeps_processSlashings (computed : processSlashings state = .ok after) :
    Keeps state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine Keeps.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, lowered⟩ := ok
        exact keeps_decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ Keeps.refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Keeps.refl _
  · refine Keeps.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact keeps_decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ Keeps.refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Keeps.refl _

private theorem keeps_processEth1DataReset {hegota : fork < .hegota}
    (computed : processEth1DataReset hegota state = .ok after) : Keeps state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Keeps.of_eq rfl rfl rfl rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Keeps.refl _

private theorem keeps_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : Keeps state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine Keeps.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, effectiveBalance, _, set⟩ := ok
  exact keeps_setValidator (validator := { validator with effectiveBalance }) found
    (fun _ _ => rfl) set

private theorem keeps_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    Keeps state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact Keeps.of_eq rfl rfl rfl rfl rfl

private theorem keeps_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Keeps state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact Keeps.of_eq rfl rfl rfl rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Keeps.refl _

private theorem keeps_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) : Keeps state after := by
  obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · exact Keeps.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact Keeps.of_eq (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])
      (by rw [← rest])

/-! ## Steps that keep the RANDAO mixes and the slot, at every fork -/

/-- Justification and finalization keep the RANDAO mixes and the slot. -/
theorem randaoMixes_slot_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot :=
  have keeps := keeps_processJustificationAndFinalization computed
  ⟨keeps.1.1, keeps.2.2⟩

/-- The rewards and penalties of an epoch keep the RANDAO mixes and the slot. -/
theorem randaoMixes_slot_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot :=
  have keeps := keeps_processRewardsAndPenalties computed
  ⟨keeps.1.1, keeps.2.2⟩

/-- The slashing penalties of an epoch keep the RANDAO mixes and the slot. -/
theorem randaoMixes_slot_processSlashings (computed : processSlashings state = .ok after) :
    after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot :=
  have keeps := keeps_processSlashings computed
  ⟨keeps.1.1, keeps.2.2⟩

/-- The reset of the deposit votes keeps the RANDAO mixes and the slot. -/
theorem randaoMixes_slot_processEth1DataReset {hegota : fork < .hegota}
    (computed : processEth1DataReset hegota state = .ok after) :
    after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot :=
  have keeps := keeps_processEth1DataReset computed
  ⟨keeps.1.1, keeps.2.2⟩

/-- The updates of the effective balances keep the RANDAO mixes and the slot. -/
theorem randaoMixes_slot_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot :=
  have keeps := keeps_processEffectiveBalanceUpdates computed
  ⟨keeps.1.1, keeps.2.2⟩

/-- The update of the historical roots keeps the RANDAO mixes and the slot. -/
theorem randaoMixes_slot_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    after.randaoMixes = state.randaoMixes ∧ after.slot = state.slot :=
  have keeps := keeps_processHistoricalRootsUpdate computed
  ⟨keeps.1.1, keeps.2.2⟩

/-! ## Steps that keep the slot and activity, at every fork -/

/-- A balance increase keeps the slot and activity. -/
theorem activeStep_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : ActiveStep state after :=
  (keeps_increaseBalance computed).activeStep

/-- A balance decrease keeps the slot and activity. -/
theorem activeStep_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : ActiveStep state after :=
  (keeps_decreaseBalance computed).activeStep

/-- Starting an exit keeps the slot and activity up to the fixed epoch, at every fork. -/
theorem activeStep_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : ActiveStep state after :=
  (keeps_initiateValidatorExit computed).activeStep

/-- Slashing a validator keeps the slot and activity up to the fixed epoch, at every fork. -/
theorem activeStep_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ActiveStep state after :=
  (keeps_slashValidator computed).activeStep

/-- Justification and finalization keep the slot and activity. -/
theorem activeStep_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) : ActiveStep state after :=
  (keeps_processJustificationAndFinalization computed).activeStep

/-- The rewards and penalties of an epoch keep the slot and activity. -/
theorem activeStep_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : ActiveStep state after :=
  (keeps_processRewardsAndPenalties computed).activeStep

/-- Before Electra, the registry updates keep the slot and activity up to the fixed epoch. -/
theorem activeStep_processRegistryUpdates (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) : ActiveStep state after :=
  (keeps_processRegistryUpdates before computed).activeStep

/-- The slashing penalties of an epoch keep the slot and activity. -/
theorem activeStep_processSlashings (computed : processSlashings state = .ok after) :
    ActiveStep state after :=
  (keeps_processSlashings computed).activeStep

/-- The reset of the eth1 data votes keeps the slot and activity. -/
theorem activeStep_processEth1DataReset {hegota : fork < .hegota}
    (computed : processEth1DataReset hegota state = .ok after) : ActiveStep state after :=
  (keeps_processEth1DataReset computed).activeStep

/-- The effective balance updates keep the slot and activity. -/
theorem activeStep_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : ActiveStep state after :=
  (keeps_processEffectiveBalanceUpdates computed).activeStep

/-- The reset of the slashings of the next epoch keeps the slot and activity. -/
theorem activeStep_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    ActiveStep state after :=
  (keeps_processSlashingsReset computed).activeStep

/-- The historical roots update keeps the slot and activity. -/
theorem activeStep_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : ActiveStep state after :=
  (keeps_processHistoricalRootsUpdate computed).activeStep

/-- Before Altair, what the epoch step keeps, writes and rotates. -/
private theorem processEpoch_kept (before : fork < .altair)
    (computed : processEpoch config checks state = .ok after) :
    ActiveKept (activityFixedEpoch state) state after ∧
      (∃ next : Epoch, next.toNat = (getCurrentEpoch state).toNat + 1 ∧
        MixesKeptBut next state after) ∧
      after.previousEpochAttestations before = state.currentEpochAttestations before ∧
      (after.currentEpochAttestations before).data = #[] := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  unfold processEpoch at computed
  simp only [notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨_, justifiedOk, _, rewardedOk, _, registeredOk, _, slashedOk, _, resetOk, _,
    balancedOk, cleared, clearedOk, _, mixedOk, rooted, rootedOk, rotated⟩ := computed
  have head : Keeps state cleared :=
    (keeps_processJustificationAndFinalization justifiedOk).trans <|
    (keeps_processRewardsAndPenalties rewardedOk).trans <|
    (keeps_processRegistryUpdates (Nat.lt_trans before (by decide)) registeredOk).trans <|
    (keeps_processSlashings slashedOk).trans <|
    (keeps_processEth1DataReset resetOk).trans <|
    (keeps_processEffectiveBalanceUpdates balancedOk).trans <|
    keeps_processSlashingsReset clearedOk
  have epoch : getCurrentEpoch cleared = getCurrentEpoch state := by
    simp only [getCurrentEpoch, head.2.2]
  obtain ⟨next, mix, randaoMixes, nextEq, -, written, rfl⟩ := processRandaoMixesReset_eq mixedOk
  have tail := keeps_processHistoricalRootsUpdate rootedOk
  have tailActive : ActiveKept (activityFixedEpoch state) { cleared with randaoMixes } rooted := by
    have active := tail.2.1
    rwa [activityFixedEpoch_eq_of_slot (other := { cleared with randaoMixes }) head.2.2] at active
  obtain ⟨rotated', rotatedOk, previous, current, rest⟩ :=
    processParticipationRecordUpdates_eq (state := rooted) before
  obtain rfl := Except.ok.inj (rotated.symm.trans rotatedOk)
  refine ⟨head.2.1.trans <| (ActiveKept.of_validators rfl _).trans <| tailActive.trans <|
      ActiveKept.of_validators (by rw [← rest]) _, ⟨next, by rw [nextEq, epoch], ?_⟩, ?_,
      current⟩
  · intro other apart
    have plain := writeCircularRooted_elements cleared.randaoMixes next mix
    rw [written] at plain
    have mixesEq : after.randaoMixes = rooted.randaoMixes := by rw [← rest]
    rw [mixesEq, tail.1.1]
    exact (readCircular_writeCircular_of_ne plain.symm (Ne.symm apart)).trans
      (by rw [head.1.1])
  · rw [previous, tail.1.2.2]
    exact congrFun head.1.2.2 before

/-- Before Altair, the epoch step keeps activity up to the current epoch plus `MAX_SEED_LOOKAHEAD`.

Each activation and exit epoch that it writes is after that epoch. -/
theorem activeKept_processEpoch_of_lt_altair (before : fork < .altair)
    (computed : processEpoch config checks state = .ok after) :
    ActiveKept (activityFixedEpoch state) state after :=
  (processEpoch_kept before computed).1

/-- Before Altair, the epoch step writes at most the RANDAO mix of the next epoch. -/
theorem mixesKeptBut_processEpoch_of_lt_altair (before : fork < .altair)
    (computed : processEpoch config checks state = .ok after) :
    ∃ next : Epoch, next.toNat = (getCurrentEpoch state).toNat + 1 ∧
      MixesKeptBut next state after :=
  (processEpoch_kept before computed).2.1

/-- Before Altair, the epoch step moves the pending attestations of the current epoch.

They become those of the previous epoch, and the current epoch then has none. -/
theorem processEpoch_pendingRotation (before : fork < .altair)
    (computed : processEpoch config checks state = .ok after) :
    after.previousEpochAttestations before = state.currentEpochAttestations before ∧
      (after.currentEpochAttestations before).data = #[] :=
  (processEpoch_kept before computed).2.2

end EthLib.Consensus

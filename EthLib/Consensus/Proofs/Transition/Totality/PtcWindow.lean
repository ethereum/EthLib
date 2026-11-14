module

public import EthLib.Consensus.Proofs.PayloadTimeliness
public import EthLib.Consensus.Proofs.Transition.Totality.SyncCommittee

/-!
# Proofs: the window of payload timeliness committees succeeds under bounds

From Gloas, the epoch step draws the payload timeliness committees of the epoch after the lookahead.

It is a weighted selection, without a shuffle, over the members of the beacon committees of a slot.

The argument needs, in each slot, one member of those committees at the cap of the draw.

The shuffle of the epoch decides the members, so this is an assumption, not a bound.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork}

/-- The draws of the payload timeliness committees of an epoch end, at the seed of that epoch.

Each slot draws among the members of its beacon committees, with a seed of its own.

A member at the cap of the draw in each slot makes them end.

In the random oracle model, with at least one candidate, the search ends with high probability.

That is a bound on a probability, not a fact about the hash, so a run assumes the end. -/
def PtcDrawsEnd (state : BeaconState preset fork) (epoch : Epoch) : Prop :=
  ∀ seed, getSeed state epoch DOMAIN_PTC_ATTESTER = .ok seed →
    ∀ slot, computeEpochAtSlot preset slot = epoch → ∀ members,
      slotCommitteeMembers state slot = .ok members →
        ∃ committee, computeBalanceWeightedSelection state members
          (Cryptography.Hash.Sha256.hash32 ⟨seed.toArray ++ (uintToBytes 8 slot.toNat).toArray⟩)
          preset.PTC_SIZE false = .ok committee

/-- The assumptions under which the payload timeliness committees of an epoch can be drawn.

The draws of the epoch end: an assumption, not a bound. -/
structure PtcDrawable (state : BeaconState preset fork) (epoch : Epoch) : Prop where
  /-- The draws of the epoch end. -/
  ends : PtcDrawsEnd state epoch
  /-- The registry holds at most `2^40` validators. -/
  few : state.validators.data.size ≤ 2 ^ 40
  /-- The number of validators times a bound on the committees of an epoch is below `2^64`.

  The bound is one more than the most committees of a slot, times the slots of an epoch. -/
  committeeRoom : state.validators.data.size * (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
    preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64

/-- Two states with the same registry and mixes have the same beacon committee members in a slot. -/
theorem slotCommitteeMembers_eq_of_eq {fork' : Fork}
    {state : BeaconState preset fork} {other : BeaconState preset fork'}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements) (slot : Slot) :
    slotCommitteeMembers other slot = slotCommitteeMembers state slot := by
  unfold slotCommitteeMembers attesterShuffle getCommitteeCountPerSlot getActiveValidatorIndices
    getActiveValidatorIndicesChecked getSeed getRandaoMix
  simp only [validators, mixes]

/-- The draws of the committees of an epoch still end on a state with the same registry and mixes.

The two forks must be on the same side of Electra. -/
theorem PtcDrawsEnd.of_eq {fork' : Fork}
    {state : BeaconState preset fork} {other : BeaconState preset fork'} {epoch : Epoch}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements)
    (electra : .pectra ≤ fork' ↔ .pectra ≤ fork)
    (ends : PtcDrawsEnd state epoch) : PtcDrawsEnd other epoch := by
  intro seed seedOk slot inEpoch members found
  rw [getSeed_eq_of_eq mixes] at seedOk
  rw [slotCommitteeMembers_eq_of_eq validators mixes] at found
  rw [computeBalanceWeightedSelection_eq_of_eq validators electra]
  exact ends seed seedOk slot inEpoch members found

/-- The committees of an epoch stay drawable on a state with the same registry and mixes.

The two forks must be on the same side of Electra. -/
theorem PtcDrawable.of_eq {fork' : Fork}
    {state : BeaconState preset fork} {other : BeaconState preset fork'} {epoch : Epoch}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes.elements = state.randaoMixes.elements)
    (electra : .pectra ≤ fork' ↔ .pectra ≤ fork)
    (drawable : PtcDrawable state epoch) : PtcDrawable other epoch :=
  ⟨drawable.ends.of_eq validators mixes electra, validators ▸ drawable.few,
    validators ▸ drawable.committeeRoom⟩

/-- A committee that is cut has a nonzero count and the size of its range of positions. -/
private theorem size_of_shuffledCommittee {indices : Array ValidatorIndex}
    {shuffled : Array UInt64} {index count : UInt64} {committee : Array ValidatorIndex}
    (cut : shuffledCommittee indices shuffled index count = .ok committee) :
    count ≠ 0 ∧ committee.size = indices.size * (index.toNat + 1) / count.toNat -
      indices.size * index.toNat / count.toNat := by
  unfold shuffledCommittee at cut
  by_cases zero : count = 0
  · simp [zero, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at cut
  by_cases fits : index.toNat + 1 < 18446744073709551616 ∧
      indices.size * (index.toNat + 1) < 18446744073709551616
  · by_cases past : indices.size * index.toNat / count.toNat <
        indices.size * (index.toNat + 1) / count.toNat ∧
        indices.size < indices.size * (index.toNat + 1) / count.toNat
    · simp [zero, fits, past, bind, Except.bind, throw, throwThe, MonadExcept.throw,
        MonadExceptOf.throw] at cut
    · simp [zero, fits, past, pure, Except.pure] at cut
      subst cut
      simp [zero]
  · simp [zero, fits, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw] at cut

/-- A committee with a nonzero count and a position below it is cut when its bounds fit. -/
private theorem shuffledCommittee_ok {indices : Array ValidatorIndex} {shuffled : Array UInt64}
    {index count : UInt64} (inside : index < count)
    (fits : indices.size * (index.toNat + 1) < 2 ^ 64) :
    ∃ committee, shuffledCommittee indices shuffled index count = .ok committee := by
  have natLt : index.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp inside
  have positive : count ≠ 0 := by
    intro zero
    simp [zero] at natLt
  have bound : indices.size * (index.toNat + 1) ≤ indices.size * count.toNat :=
    Nat.mul_le_mul_left _ natLt
  have stopLe : indices.size * (index.toNat + 1) / count.toNat ≤ indices.size :=
    Nat.div_le_of_le_mul (Nat.le_trans bound (Nat.le_of_eq (Nat.mul_comm _ _)))
  have below : index.toNat + 1 < 2 ^ 64 := Nat.lt_of_le_of_lt natLt count.toNat_lt
  simp only [shuffledCommittee, positive, below, fits, and_self, Nat.not_lt.mpr stopLe, and_false,
    ↓reduceIte]
  exact ⟨_, rfl⟩

/-- A beacon committee that is cut has the size of its range of positions in the epoch. -/
private theorem size_beaconCommitteeOf {slot : Slot} {index : CommitteeIndex} {perSlot : UInt64}
    {active : Array ValidatorIndex} {shuffled : Array UInt64} {committee : Array ValidatorIndex}
    (cut : beaconCommitteeOf preset slot index perSlot active shuffled = .ok committee) :
    committee.size = active.size * ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat +
        index.toNat + 1) / (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) -
      active.size * ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + index.toNat) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
  simp only [beaconCommitteeOf, bind_ok_iff, liftArith, mapError_ok_iff,
    Base.Uint64.mulChecked_ok_iff, Base.Uint64.addChecked_ok_iff] at cut
  obtain ⟨position, ⟨product, ⟨_, productEq⟩, _, positionEq⟩,
    count, ⟨_, countEq⟩, committeeOk⟩ := cut
  rw [(size_of_shuffledCommittee committeeOk).2, positionEq, productEq, countEq]

/-- The committees of a slot, one after the other, cut the range of their positions. -/
private theorem size_foldlM_committees {slot : Slot} {perSlot : UInt64}
    {active : Array ValidatorIndex} {shuffled : Array UInt64} (m : Nat)
    (le : m ≤ perSlot.toNat) {members : Array ValidatorIndex}
    (folded : (List.range m).foldlM (fun members index => do
      return members ++ (← beaconCommitteeOf preset slot index.toUInt64 perSlot active shuffled))
      #[] = .ok members) :
    members.size = active.size * ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + m) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) -
      active.size * ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
  induction m generalizing members with
  | zero =>
    rw [List.range_zero, List.foldlM_nil] at folded
    obtain rfl := Except.ok.inj folded
    simp
  | succ m ih =>
    rw [List.range_succ, List.foldlM_append] at folded
    simp only [List.foldlM_cons, List.foldlM_nil, bind_ok_iff, pure, Except.pure] at folded
    obtain ⟨before, beforeOk, committee, ⟨cut, cutOk, joined⟩, same⟩ := folded
    obtain rfl := Except.ok.inj joined
    obtain rfl := Except.ok.inj same
    have lt : m < 2 ^ 64 := Nat.lt_trans (Nat.lt_of_succ_le le) perSlot.toNat_lt
    have mNat : (m.toUInt64).toNat = m := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' lt]
    have firstSize := ih (Nat.le_of_succ_le le) beforeOk
    have cutSize := size_beaconCommitteeOf cutOk
    rw [mNat] at cutSize
    rw [Array.size_append, firstSize, cutSize, ← Nat.add_assoc]
    have mono1 : active.size * ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) ≤ active.size *
        ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + m) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
    have mono2 : active.size * ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + m) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) ≤ active.size *
        ((slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + m + 1) /
        (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
    omega

/-- The beacon committees of a slot hold no more members than the registry holds validators. -/
theorem size_slotCommitteeMembers_le {state : BeaconState preset fork} {slot : Slot}
    {members : Array ValidatorIndex} (found : slotCommitteeMembers state slot = .ok members) :
    members.size ≤ state.validators.data.size := by
  unfold slotCommitteeMembers at found
  simp only [bind_ok_iff] at found
  obtain ⟨⟨active, shuffled⟩, shuffleOk, folded⟩ := found
  obtain ⟨_, _, _, rfl⟩ := attesterShuffle_ok shuffleOk
  have activeLe := length_getActiveValidatorIndices_le state (computeEpochAtSlot preset slot)
  unfold slotCommitteeMembersOf at folded
  have total := size_foldlM_committees _ (Nat.le_refl _) folded
  simp only [List.size_toArray] at total ⊢
  rw [total, UInt64.toNat_mod]
  refine Nat.le_trans (Nat.le_trans (Nat.sub_le _ _) ?_) activeLe
  rcases Nat.eq_zero_or_pos
    ((getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
      preset.SLOTS_PER_EPOCH.toNat) with zero | positive
  · rw [zero, Nat.div_zero]
    exact Nat.zero_le _
  · have perEpoch : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.pos_of_mul_pos_left positive
    have below := Nat.mod_lt slot.toNat perEpoch
    generalize (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat = p at *
    generalize (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length = n at *
    generalize UInt64.toNat slot % UInt64.toNat preset.SLOTS_PER_EPOCH = k at *
    generalize UInt64.toNat preset.SLOTS_PER_EPOCH = e at *
    refine Nat.div_le_of_le_mul ?_
    have step : k * p + p ≤ p * e :=
      calc k * p + p = (k + 1) * p := (Nat.succ_mul k p).symm
        _ ≤ e * p := Nat.mul_le_mul_right _ below
        _ = p * e := Nat.mul_comm _ _
    calc n * (k * p + p) ≤ n * (p * e) := Nat.mul_le_mul_left _ step
      _ = p * e * n := Nat.mul_comm _ _

/-- The draws of the payload timeliness committees end when each slot has a member at the cap.

No effective balance is above the cap, and the registry holds at most `2^40` validators.

The size of a committee times the number of validators is below `2^64`.

The products of the draw fit in 64 bits. -/
theorem PtcDrawsEnd.of_atCap {state : BeaconState preset fork} {epoch : Epoch}
    (fits : DrawFits preset fork)
    (capped : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance.toNat ≤ drawCap preset fork)
    (full : ∀ slot, computeEpochAtSlot preset slot = epoch → ∀ members,
      slotCommitteeMembers state slot = .ok members →
      ∃ index ∈ members, ∃ validator, getValidator state index = .ok validator ∧
        validator.effectiveBalance.toNat = drawCap preset fork)
    (few : state.validators.data.size ≤ 2 ^ 40)
    (room : preset.PTC_SIZE.toNat * state.validators.data.size < 2 ^ 64) :
    PtcDrawsEnd state epoch := by
  intro seed _ slot inEpoch members found
  have checked := getActiveValidatorIndicesChecked_of_size_le (state := state) (by omega)
    (computeEpochAtSlot preset slot)
  have membersLe := size_slotCommitteeMembers_le found
  exact computeBalanceWeightedSelection_ok fits
    (fun index member => by
      obtain ⟨_, _, committee, got, mem⟩ := (mem_slotCommitteeMembers found).mp member
      obtain ⟨validator, read, _⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp
        (mem_getActiveValidatorIndices_of_getBeaconCommittee got mem)
      exact ⟨validator, by unfold getValidator; rw [read],
        capped validator (Array.mem_of_getElem? read)⟩)
    (full slot inEpoch members found) (by omega)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ membersLe) room)

/-- The shuffle of an epoch succeeds when the registry holds at most `2^40` validators. -/
private theorem attesterShuffle_ok_of_le {state : BeaconState preset fork} {epoch : Epoch}
    (seedRoom : epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (few : state.validators.data.size ≤ 2 ^ 40) :
    ∃ shuffled, attesterShuffle state epoch =
      .ok ((getActiveValidatorIndices state epoch).toArray, shuffled) := by
  obtain ⟨seed, seedOk⟩ := getSeed_ok (state := state) (epoch := epoch) DOMAIN_BEACON_ATTESTER
    seedRoom lookahead
  have checked := getActiveValidatorIndicesChecked_of_size_le (state := state) (by omega) epoch
  have lengthLe := length_getActiveValidatorIndices_le state epoch
  have lt : (getActiveValidatorIndices state epoch).toArray.size < 2 ^ 64 := by
    simp only [List.size_toArray]
    omega
  have countNat := UInt64.toNat_ofNat_of_lt' lt
  have permuted := computeShuffledPermutation_eq (preset := preset) (seed := seed)
    (count := UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size)
    (by rw [countNat]; simp only [List.size_toArray]; omega)
  refine ⟨Shuffle.shuffledPositions preset.SHUFFLE_ROUND_COUNT.toNat seed
    (UInt64.ofNat (getActiveValidatorIndices state epoch).toArray.size).toNat, ?_⟩
  simp only [attesterShuffle, seedOk, checked, liftArith, bind, Except.bind, Except.mapError,
    Base.Uint64.ofNatChecked_of_lt lt, Nat.toUInt64_eq, permuted, pure, Except.pure]

/-- A beacon committee is cut when its position is below the count of the epoch. -/
private theorem beaconCommitteeOf_ok {slot : Slot} {index : CommitteeIndex} {perSlot : UInt64}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (count : perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (inside : (slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + index.toNat <
      perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (fits : active.size * (perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64) :
    ∃ committee, beaconCommitteeOf preset slot index perSlot active shuffled = .ok committee := by
  have productFits : (slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat < 2 ^ 64 := by omega
  have sumFits : ((slot % preset.SLOTS_PER_EPOCH) * perSlot).toNat + index.toNat < 2 ^ 64 := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt productFits]
    omega
  have positionNat : ((slot % preset.SLOTS_PER_EPOCH) * perSlot + index).toNat =
      (slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat + index.toNat := by
    rw [Base.Uint64.toNat_add_of_lt sumFits, UInt64.toNat_mul, Nat.mod_eq_of_lt productFits]
  have countFits : perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := count
  have countNat : (perSlot * preset.SLOTS_PER_EPOCH).toNat =
      perSlot.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt countFits]
  obtain ⟨committee, cut⟩ := shuffledCommittee_ok (indices := active) (shuffled := shuffled)
    (index := (slot % preset.SLOTS_PER_EPOCH) * perSlot + index)
    (count := perSlot * preset.SLOTS_PER_EPOCH) (by
      rw [UInt64.lt_iff_toNat_lt, positionNat, countNat]
      exact inside) (by
      rw [positionNat]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) fits)
  refine ⟨committee, ?_⟩
  simp only [beaconCommitteeOf, liftArith, Base.Uint64.mulChecked_of_lt
    (by simpa only using productFits : (slot % preset.SLOTS_PER_EPOCH).toNat * perSlot.toNat <
      2 ^ 64), Base.Uint64.addChecked_of_lt sumFits,
    Base.Uint64.mulChecked_of_lt countFits, bind, Except.bind, Except.mapError, cut]

/-- The committees of a slot are all cut when each one is. -/
private theorem foldlM_committees_ok {slot : Slot} {perSlot : UInt64}
    {active : Array ValidatorIndex} {shuffled : Array UInt64} (m : Nat)
    (each : ∀ i < m, ∃ committee,
      beaconCommitteeOf preset slot i.toUInt64 perSlot active shuffled = .ok committee) :
    ∃ members, (List.range m).foldlM (fun members index => do
      return members ++ (← beaconCommitteeOf preset slot index.toUInt64 perSlot active shuffled))
      #[] = .ok members := by
  induction m with
  | zero => exact ⟨#[], rfl⟩
  | succ m ih =>
    obtain ⟨before, beforeOk⟩ := ih fun i lt => each i (Nat.lt_succ_of_lt lt)
    obtain ⟨committee, cutOk⟩ := each m (Nat.lt_succ_self m)
    refine ⟨before ++ committee, ?_⟩
    rw [List.range_succ, List.foldlM_append, beforeOk]
    simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind, cutOk, pure, Except.pure]

/-- The payload timeliness committee of a slot is drawn under bounds on the state.

The epoch of the slot plus the length of the history of mixes stays below `2^64`.

The seed lookahead is shorter than that history.

An epoch has at least one slot.

The draws of the epoch of the slot end.

The registry holds at most `2^40` validators.

Their number times a bound on the committees of an epoch is below `2^64`.

The bound is one more than the most committees of a slot, times the slots of an epoch. -/
theorem computePtc_ok {state : BeaconState preset fork} {slot : Slot}
    (seedRoom : (computeEpochAtSlot preset slot).toNat +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (perEpoch : preset.SLOTS_PER_EPOCH ≠ 0)
    (ends : PtcDrawsEnd state (computeEpochAtSlot preset slot))
    (few : state.validators.data.size ≤ 2 ^ 40)
    (committeeRoom : state.validators.data.size * (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ committee, computePtc state slot = .ok committee := by
  have perSlotPos := UInt64.le_iff_toNat_le.mp
    (one_le_getCommitteeCountPerSlot state (computeEpochAtSlot preset slot))
  have perSlotMax := UInt64.le_iff_toNat_le.mp
    (getCommitteeCountPerSlot_le state (computeEpochAtSlot preset slot))
  have lengthLe := length_getActiveValidatorIndices_le state (computeEpochAtSlot preset slot)
  have epochPos : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    refine Nat.pos_of_ne_zero fun zero => perEpoch ?_
    exact UInt64.toNat_inj.mp zero
  simp only [Base.Uint64.toNat_max] at perSlotMax
  have one : (1 : UInt64).toNat = 1 := rfl
  have empty : state.validators.data.size = 0 →
      getCommitteeCountPerSlot state (computeEpochAtSlot preset slot) = 1 := by
    intro zero
    have hlen : (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length = 0 := by
      omega
    simp [getCommitteeCountPerSlot, committeeCountOf, hlen]
    apply UInt64.toNat_inj.mp
    simp [Base.Uint64.toNat_max, Base.Uint64.toNat_min]
  have perSlotLe : (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat ≤
      preset.MAX_COMMITTEES_PER_SLOT.toNat + 1 := by omega
  have slotsSmall := preset.SLOTS_PER_EPOCH.toNat_lt
  have countFits : (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
      preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos state.validators.data.size with zero | pos
    · rw [empty zero, one]
      omega
    · calc _ ≤ (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat :=
            Nat.mul_le_mul_right _ perSlotLe
        _ ≤ state.validators.data.size * (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
            preset.SLOTS_PER_EPOCH.toNat :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ pos)
        _ < 2 ^ 64 := committeeRoom
  have activeFits : (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length *
      ((getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64 :=
    calc _ ≤ state.validators.data.size * ((preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
            preset.SLOTS_PER_EPOCH.toNat) :=
          Nat.mul_le_mul lengthLe (Nat.mul_le_mul_right _ perSlotLe)
      _ = state.validators.data.size * (preset.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
            preset.SLOTS_PER_EPOCH.toNat := (Nat.mul_assoc _ _ _).symm
      _ < 2 ^ 64 := committeeRoom
  obtain ⟨seed, seedOk⟩ := getSeed_ok (state := state) (epoch := computeEpochAtSlot preset slot)
    DOMAIN_PTC_ATTESTER seedRoom lookahead
  obtain ⟨shuffled, shuffleOk⟩ := attesterShuffle_ok_of_le (state := state)
    (epoch := computeEpochAtSlot preset slot) seedRoom lookahead few
  obtain ⟨members, membersOk⟩ : ∃ members, slotCommitteeMembersOf preset slot
      (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot))
      (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).toArray shuffled =
      .ok members := by
    unfold slotCommitteeMembersOf
    refine foldlM_committees_ok _ fun i lt => beaconCommitteeOf_ok countFits ?_ (by
      simpa only [List.size_toArray] using activeFits)
    have iNat : (i.toUInt64).toNat = i := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans lt
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat_lt)]
    rw [iNat, UInt64.toNat_mod]
    have below := Nat.mod_lt slot.toNat epochPos
    generalize (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat = p at *
    generalize UInt64.toNat slot % UInt64.toNat preset.SLOTS_PER_EPOCH = k at *
    generalize UInt64.toNat preset.SLOTS_PER_EPOCH = e at *
    calc k * p + i < k * p + p := Nat.add_lt_add_left lt _
      _ = (k + 1) * p := (Nat.succ_mul k p).symm
      _ ≤ e * p := Nat.mul_le_mul_right _ below
      _ = p * e := Nat.mul_comm _ _
  have found : slotCommitteeMembers state slot = .ok members := by
    unfold slotCommitteeMembers
    simp only [shuffleOk, bind, Except.bind]
    exact membersOk
  simp only [computePtc, computePtcOf, seedOk, shuffleOk, membersOk, bind, Except.bind]
  exact ends seed seedOk slot rfl members found

/-- From Gloas, the move of the window of payload timeliness committees succeeds under bounds.

The epoch it draws is the one after the seed lookahead.

That epoch plus the length of the history of mixes stays below `2^64`.

The seed lookahead is shorter than that history.

The first slot of the epoch after it is at most `2^64`, so every slot of it fits in 64 bits.

An epoch has at least one slot.

That epoch meets the assumptions of the draw.

The step changes only the window. -/
theorem processPtcWindow_ok (gloas : .glamsterdam ≤ fork) {state : BeaconState preset fork}
    (seedRoom : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (perEpoch : preset.SLOTS_PER_EPOCH ≠ 0)
    (drawable : PtcDrawable state (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1)) :
    ∃ after, processPtcWindow state gloas = .ok after ∧
      after = { state with ptcWindow := fun _ => after.ptcWindow gloas } := by
  have one : (1 : UInt64).toNat = 1 := rfl
  have slotsSmall := preset.SLOTS_PER_EPOCH.toNat_lt
  have epochPos : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    refine Nat.pos_of_ne_zero fun zero => perEpoch ?_
    exact UInt64.toNat_inj.mp zero
  have firstFits : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat < 2 ^ 64 := by
    omega
  have first := Base.Uint64.toNat_add_of_lt firstFits
  have secondFits : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD).toNat +
      (1 : UInt64).toNat < 2 ^ 64 := by omega
  have second := Base.Uint64.toNat_add_of_lt secondFits
  have epochNat : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1).toNat =
      (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 := by omega
  have startFits : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1).toNat *
      preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 := by
    rw [epochNat, ← Nat.succ_mul]
    exact slotRoom
  -- Each offset of the new epoch of the window names a slot of the epoch after the lookahead.
  have slotOk : ∀ offset < preset.SLOTS_PER_EPOCH.toNat, ∃ slot,
      ptcWindowSlot preset (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1) offset =
        .ok slot := by
    intro offset lt
    have zeroDiv : (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat = 0 := by
      rw [Nat.div_eq_of_lt lt]
      rfl
    have addZero := Base.Uint64.addChecked_of_lt (a := getCurrentEpoch state +
      preset.MIN_SEED_LOOKAHEAD + 1) (b := (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64)
      (by rw [zeroDiv]; omega)
    have restNat : (offset % preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat = offset := by
      rw [Nat.mod_eq_of_lt lt, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by
        have : UInt64.size = 2 ^ 64 := rfl
        omega)]
    have sumNat : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1 +
        (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64).toNat =
        (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1).toNat := by
      rw [Base.Uint64.toNat_add_of_lt (by rw [zeroDiv]; omega), zeroDiv, Nat.add_zero]
    have productFits : (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1 +
        (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64).toNat *
        preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
      rw [sumNat]
      omega
    have productNat := UInt64.toNat_mul (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1 +
      (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64) preset.SLOTS_PER_EPOCH
    rw [Nat.mod_eq_of_lt productFits, sumNat] at productNat
    have sumFits : ((getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1 +
        (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64) * preset.SLOTS_PER_EPOCH).toNat +
        (offset % preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat < 2 ^ 64 := by
      rw [productNat, restNat]
      omega
    refine ⟨(getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1 +
      (offset / preset.SLOTS_PER_EPOCH.toNat).toUInt64) * preset.SLOTS_PER_EPOCH +
      (offset % preset.SLOTS_PER_EPOCH.toNat).toUInt64, ?_⟩
    simp only [ptcWindowSlot, liftArith, addZero, computeStartSlotAtEpoch,
      Base.Uint64.mulChecked_of_lt productFits, bind, Except.bind, Except.mapError,
      Base.Uint64.addChecked_of_lt sumFits]
  rw [processPtcWindow_eq]
  simp only [liftArith, Base.Uint64.addChecked_of_lt firstFits,
    Base.Uint64.addChecked_of_lt secondFits, bind, Except.bind, Except.mapError]
  obtain ⟨fresh, freshOk⟩ : ∃ fresh, (Vector.range preset.SLOTS_PER_EPOCH.toNat).mapM
      (fun offset => (do
        computePtc state
          (← ptcWindowSlot preset (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1) offset) :
        Except AccessorError (PayloadTimelinessCommittee preset))) = .ok fresh := by
    have each : ∀ offset ∈ (Vector.range preset.SLOTS_PER_EPOCH.toNat).toList, ∃ y,
        (do
          computePtc state
            (← ptcWindowSlot preset (getCurrentEpoch state + preset.MIN_SEED_LOOKAHEAD + 1)
              offset) : Except AccessorError (PayloadTimelinessCommittee preset)) = .ok y := by
      intro offset member
      have lt : offset < preset.SLOTS_PER_EPOCH.toNat := by simpa using member
      obtain ⟨slot, slotEq⟩ := slotOk offset lt
      have epochEq := computeEpochAtSlot_ptcWindowSlot lt slotEq
      obtain ⟨committee, ok⟩ := computePtc_ok (state := state) (slot := slot)
        (by rw [epochEq, epochNat]; omega) lookahead perEpoch
        (by rw [epochEq]; exact drawable.ends) drawable.few drawable.committeeRoom
      exact ⟨committee, by simp only [slotEq, bind, Except.bind, ok]⟩
    choose! out outOk using each
    refine ⟨Vector.ofFn fun i => out i.val, vector_mapM_eq_ok_iff.mpr fun i hi => ?_⟩
    simpa using outOk i (by simpa using hi)
  simp only [bind, Except.bind] at freshOk
  rw [freshOk]
  exact ⟨_, rfl, rfl⟩

/-- Each slot of an epoch has a member at the cap when every active validator is at the cap.

The epoch needs at least as many active validators as slots, so that each slot has a member.

This shows that the assumption on the slots of an epoch can hold. -/
theorem PtcDrawable.full_of_active_atCap {state : BeaconState preset fork} {epoch : Epoch}
    (perEpoch : preset.SLOTS_PER_EPOCH ≠ 0)
    (enough : preset.SLOTS_PER_EPOCH.toNat ≤ (getActiveValidatorIndices state epoch).length)
    (atCap : ∀ validator ∈ state.validators.data, isActiveValidator validator epoch = true →
      validator.effectiveBalance.toNat = drawCap preset fork) :
    ∀ slot, computeEpochAtSlot preset slot = epoch → ∀ members,
      slotCommitteeMembers state slot = .ok members →
      ∃ index ∈ members, ∃ validator, getValidator state index = .ok validator ∧
        validator.effectiveBalance.toNat = drawCap preset fork := by
  intro slot epochEq members found
  subst epochEq
  have perSlotPos := UInt64.le_iff_toNat_le.mp
    (one_le_getCommitteeCountPerSlot state (computeEpochAtSlot preset slot))
  have epochPos : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    refine Nat.pos_of_ne_zero fun zero => perEpoch ?_
    exact UInt64.toNat_inj.mp zero
  have one : (1 : UInt64).toNat = 1 := rfl
  have foundCopy := found
  unfold slotCommitteeMembers at foundCopy
  simp only [bind_ok_iff] at foundCopy
  obtain ⟨⟨active, shuffled⟩, shuffleOk, folded⟩ := foundCopy
  have shuffleCopy := shuffleOk
  obtain ⟨_, _, _, rfl⟩ := attesterShuffle_ok shuffleOk
  have checked : getActiveValidatorIndicesChecked state (computeEpochAtSlot preset slot) =
      .ok (getActiveValidatorIndices state (computeEpochAtSlot preset slot)) := by
    simp only [attesterShuffle, bind_ok_iff] at shuffleCopy
    obtain ⟨_, _, indices, indicesOk, _⟩ := shuffleCopy
    rw [← getActiveValidatorIndicesChecked_ok indicesOk]
    exact indicesOk
  unfold slotCommitteeMembersOf at folded
  have total := size_foldlM_committees _ (Nat.le_refl _) folded
  simp only [List.size_toArray] at total
  rw [UInt64.toNat_mod] at total
  have positive : 0 < members.size := by
    generalize (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat = p at *
    generalize (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).length = n at *
    generalize UInt64.toNat slot % UInt64.toNat preset.SLOTS_PER_EPOCH = k at *
    generalize UInt64.toNat preset.SLOTS_PER_EPOCH = e at *
    have pPos : 0 < p := by omega
    have first : n * (k * p + p) = p * (n * (k + 1)) := by grind
    have second : n * (k * p) = p * (n * k) := by grind
    rw [first, second, Nat.mul_div_mul_left _ _ pPos, Nat.mul_div_mul_left _ _ pPos] at total
    have split : n * k / e + n / e ≤ n * (k + 1) / e := by
      refine (Nat.le_div_iff_mul_le epochPos).mpr ?_
      have h1 := Nat.div_mul_le_self (n * k) e
      have h2 := Nat.div_mul_le_self n e
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one]
      omega
    have atLeast : 0 < n / e := Nat.div_pos enough epochPos
    omega
  have memberMem : members[0] ∈ members := Array.getElem_mem positive
  obtain ⟨_, _, committee, got, mem⟩ := (mem_slotCommitteeMembers found).mp memberMem
  obtain ⟨validator, read, active⟩ := (mem_iff_of_getActiveValidatorIndicesChecked_ok checked).mp
    (mem_getActiveValidatorIndices_of_getBeaconCommittee got mem)
  exact ⟨members[0], memberMem, validator, by unfold getValidator; rw [read],
    atCap validator (Array.mem_of_getElem? read) active⟩

/-- The bounds on the registry size beside the `2^40` bound follow from it on mainnet and minimal.
-/
theorem ptcRoom_presets {size : Nat} (few : size ≤ 2 ^ 40) :
    (Preset.mainnet.PTC_SIZE.toNat * size < 2 ^ 64 ∧
      size * (Preset.mainnet.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
        Preset.mainnet.SLOTS_PER_EPOCH.toNat < 2 ^ 64) ∧
    (Preset.minimal.PTC_SIZE.toNat * size < 2 ^ 64 ∧
      size * (Preset.minimal.MAX_COMMITTEES_PER_SLOT.toNat + 1) *
        Preset.minimal.SLOTS_PER_EPOCH.toNat < 2 ^ 64) := by
  have mainPtc : Preset.mainnet.PTC_SIZE.toNat = 512 := rfl
  have mainCommittees : Preset.mainnet.MAX_COMMITTEES_PER_SLOT.toNat = 64 := rfl
  have mainSlots : Preset.mainnet.SLOTS_PER_EPOCH.toNat = 32 := rfl
  have miniPtc : Preset.minimal.PTC_SIZE.toNat = 16 := rfl
  have miniCommittees : Preset.minimal.MAX_COMMITTEES_PER_SLOT.toNat = 4 := rfl
  have miniSlots : Preset.minimal.SLOTS_PER_EPOCH.toNat = 8 := rfl
  rw [mainPtc, mainCommittees, mainSlots, miniPtc, miniCommittees, miniSlots]
  omega

/-- The first window of payload timeliness committees succeeds under bounds.

The upgrade to Gloas computes it.

The committees of the previous epoch hold only index zero, and need no bound.

The window then covers the current epoch and each epoch of the seed lookahead after it.

Each of these epochs meets the assumptions of the draw.

The last epoch drawn plus the length of the history of mixes stays below `2^64`.

The seed lookahead is shorter than that history.

The first slot of the epoch after the last one drawn is at most `2^64`.

So every slot drawn fits in 64 bits.

An epoch has at least one slot. -/
theorem initializePtcWindow_ok {state : BeaconState preset fork}
    (seedRoom : (getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : ((getCurrentEpoch state).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (perEpoch : preset.SLOTS_PER_EPOCH ≠ 0)
    (drawable : ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
      PtcDrawable state (getCurrentEpoch state + offset.toUInt64)) :
    ∃ window, initializePtcWindow state = .ok window := by
  have slotsSmall := preset.SLOTS_PER_EPOCH.toNat_lt
  have epochPos : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    refine Nat.pos_of_ne_zero fun zero => perEpoch ?_
    exact UInt64.toNat_inj.mp zero
  have size : UInt64.size = 2 ^ 64 := rfl
  -- Each position after the previous epoch names a slot of the current epoch or of the lookahead.
  have slotOk : ∀ rest < (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat,
      ∃ slot, ptcWindowSlot preset (getCurrentEpoch state) rest = .ok slot := by
    intro rest lt
    have quotLe : rest / preset.SLOTS_PER_EPOCH.toNat ≤ preset.MIN_SEED_LOOKAHEAD.toNat :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul epochPos).mpr lt)
    have quotNat : (rest / preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat =
        rest / preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by
        have := preset.MIN_SEED_LOOKAHEAD.toNat_lt
        omega)]
    have epochFits : (getCurrentEpoch state).toNat +
        (rest / preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat < 2 ^ 64 := by
      rw [quotNat]
      omega
    have sumNat := Base.Uint64.toNat_add_of_lt epochFits
    rw [quotNat] at sumNat
    have below : ((getCurrentEpoch state).toNat + rest / preset.SLOTS_PER_EPOCH.toNat) *
        preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64 := by
      rw [← Nat.succ_mul]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) slotRoom
    have productFits : (getCurrentEpoch state +
        (rest / preset.SLOTS_PER_EPOCH.toNat).toUInt64).toNat *
        preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
      rw [sumNat]
      omega
    have productNat := UInt64.toNat_mul (getCurrentEpoch state +
      (rest / preset.SLOTS_PER_EPOCH.toNat).toUInt64) preset.SLOTS_PER_EPOCH
    rw [Nat.mod_eq_of_lt productFits, sumNat] at productNat
    have restLt := Nat.mod_lt rest epochPos
    have restNat : (rest % preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat =
        rest % preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by omega)]
    have sumFits : ((getCurrentEpoch state + (rest / preset.SLOTS_PER_EPOCH.toNat).toUInt64) *
        preset.SLOTS_PER_EPOCH).toNat +
        (rest % preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat < 2 ^ 64 := by
      rw [productNat, restNat]
      omega
    refine ⟨(getCurrentEpoch state + (rest / preset.SLOTS_PER_EPOCH.toNat).toUInt64) *
      preset.SLOTS_PER_EPOCH + (rest % preset.SLOTS_PER_EPOCH.toNat).toUInt64, ?_⟩
    simp only [ptcWindowSlot, liftArith, Base.Uint64.addChecked_of_lt epochFits,
      computeStartSlotAtEpoch, Base.Uint64.mulChecked_of_lt productFits, bind, Except.bind,
      Except.mapError, Base.Uint64.addChecked_of_lt sumFits]
  rw [initializePtcWindow_eq]
  have each : ∀ position ∈ (Vector.range ((preset.MIN_SEED_LOOKAHEAD.toNat + 2) *
      preset.SLOTS_PER_EPOCH.toNat)).toList, ∃ y,
      (do
        if position < preset.SLOTS_PER_EPOCH.toNat then return Vector.replicate _ 0
        computePtc state (← ptcWindowSlot preset (getCurrentEpoch state)
          (position - preset.SLOTS_PER_EPOCH.toNat)) :
        Except AccessorError (PayloadTimelinessCommittee preset)) = .ok y := by
    intro position member
    have lt : position < (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat :=
      by simpa using member
    by_cases before : position < preset.SLOTS_PER_EPOCH.toNat
    · exact ⟨_, by simp only [before, ↓reduceIte]; rfl⟩
    have sizes : (preset.MIN_SEED_LOOKAHEAD.toNat + 2) * preset.SLOTS_PER_EPOCH.toNat =
        (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat +
          preset.SLOTS_PER_EPOCH.toNat := Nat.succ_mul _ _
    have restLt : position - preset.SLOTS_PER_EPOCH.toNat <
        (preset.MIN_SEED_LOOKAHEAD.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by omega
    obtain ⟨slot, slotEq⟩ := slotOk _ restLt
    have epochEq := computeEpochAtSlot_ptcWindowSlot_eq_add epochPos slotEq
    have quotLe : (position - preset.SLOTS_PER_EPOCH.toNat) / preset.SLOTS_PER_EPOCH.toNat ≤
        preset.MIN_SEED_LOOKAHEAD.toNat :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul epochPos).mpr restLt)
    have quotNat : ((position - preset.SLOTS_PER_EPOCH.toNat) /
        preset.SLOTS_PER_EPOCH.toNat).toUInt64.toNat =
        (position - preset.SLOTS_PER_EPOCH.toNat) / preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by
        have := preset.MIN_SEED_LOOKAHEAD.toNat_lt
        omega)]
    have drawn := drawable _ quotLe
    rw [← epochEq] at drawn
    obtain ⟨committee, ok⟩ := computePtc_ok (state := state) (slot := slot)
      (by rw [epochEq, Base.Uint64.toNat_add_of_lt (by rw [quotNat]; omega), quotNat]; omega)
      lookahead perEpoch drawn.ends drawn.few drawn.committeeRoom
    exact ⟨committee, by simp only [before, ↓reduceIte, slotEq, bind, Except.bind, ok]⟩
  choose! out outOk using each
  refine ⟨_, congrArg (Serialization.Ssz.RootedVector.ofVector <$> ·) (vector_mapM_eq_ok_iff
    (ys := Vector.ofFn fun i => out i.val) |>.mpr fun i hi => ?_)⟩
  simpa using outOk i (by simpa using hi)

end EthLib.Consensus

module

public import EthLib.Consensus.InclusionListCommittee
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Time
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the inclusion list committee and its signature

Seat `i` of the committee holds member `i` of its slot, counted modulo the number of members.

The committee fails exactly when the beacon committees of the slot hold no validator.

A list signed with the key of its member passes the signature check.

An assignment names the first slot of the epoch whose committee seats the validator.

No assignment means that no slot of the epoch seats it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork} {state : BeaconState preset fork} {slot : Slot}

/-- Seat `i` of a committee holds member `i` of the slot, counted modulo the number of members.

The slot then has at least one member. -/
theorem getInclusionListCommittee_seat {members : Array ValidatorIndex}
    {committee : InclusionListCommittee preset}
    (found : slotCommitteeMembers state slot = .ok members)
    (made : getInclusionListCommittee state slot = .ok committee) :
    ∃ nonempty : 0 < members.size, ∀ i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat,
      committee[i] = members[i.val % members.size]'(Nat.mod_lt _ nonempty) := by
  simp only [getInclusionListCommittee, found, bind, Except.bind] at made
  split at made
  · rename_i nonempty
    simp only [pure, Except.pure, Except.ok.injEq] at made
    subst made
    exact ⟨nonempty, fun i => by simp⟩
  · cases made

/-- The committee fails exactly when the beacon committees of the slot hold no validator. -/
theorem getInclusionListCommittee_eq_error_iff {members : Array ValidatorIndex}
    (found : slotCommitteeMembers state slot = .ok members) :
    getInclusionListCommittee state slot = .error .noCandidates ↔ members.size = 0 := by
  simp only [getInclusionListCommittee, found, bind, Except.bind]
  split
  · rename_i nonempty
    simp only [pure, Except.pure, reduceCtorEq, false_iff]
    omega
  · rename_i empty
    simp only [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, true_iff]
    omega

/-- Every seat of a committee holds a validator of a beacon committee of the slot. -/
theorem getInclusionListCommittee_mem {committee : InclusionListCommittee preset}
    (made : getInclusionListCommittee state slot = .ok committee)
    (i : Fin preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat) :
    ∃ j < (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat,
      ∃ beacon, getBeaconCommittee state slot j.toUInt64 = .ok beacon ∧ committee[i] ∈ beacon := by
  cases found : slotCommitteeMembers state slot with
  | error e =>
    simp [getInclusionListCommittee, found, bind, Except.bind] at made
  | ok members =>
    obtain ⟨nonempty, seat⟩ := getInclusionListCommittee_seat found made
    rw [seat i]
    exact (mem_slotCommitteeMembers found).mp (Array.getElem_mem _)

/-- A list signed with the secret key of its member passes the signature check.

The member must be in the registry with the public key of that secret key. -/
theorem isValidInclusionListSignature_of_sign {config : Config}
    {signed : SignedInclusionList} {key : Signatures.SecretKey} {validator : Validator}
    (registered : getValidator state signed.message.validatorIndex = .ok validator)
    (owned : validator.pubkey = Signatures.skToPk key)
    (signedBy : getInclusionListSignature config state signed.message key =
      .ok signed.signature) :
    isValidInclusionListSignature config state signed = .ok true := by
  simp only [getInclusionListSignature, bind, Except.bind] at signedBy
  split at signedBy
  · cases signedBy
  rename_i root rooted
  have rootOk : inclusionListSigningRoot config state signed.message = .ok root := by
    cases h : inclusionListSigningRoot config state signed.message <;>
      simp_all [Except.mapError]
  obtain ⟨signature, signs, verifies⟩ := Signatures.verify_sign key (packBytes root)
  have same : signature = signed.signature := by
    rw [signs] at signedBy
    simpa [Except.mapError] using signedBy
  subst same
  simp only [isValidInclusionListSignature, registered, rootOk, bind, Except.bind,
    Except.mapError, pure, Except.pure, owned]
  exact congrArg Except.ok verifies

variable {validator : ValidatorIndex}

open Uint64

/-- Whether the inclusion list committee of a slot, once computed, seats a validator. -/
def SeatedAt (state : BeaconState preset fork) (validator : ValidatorIndex) (slot : Slot) :
    Prop :=
  ∃ committee, getInclusionListCommittee state slot = .ok committee ∧
    validator ∈ committee.toList

/-- A search that finds a slot finds one that seats the validator, after none that does. -/
theorem firstInclusionListSlot_some {slots : List Slot} {slot : Slot}
    (ascending : slots.Pairwise (· < ·))
    (found : firstInclusionListSlot state validator slots = .ok (some slot)) :
    slot ∈ slots ∧ SeatedAt state validator slot ∧
      ∀ earlier ∈ slots, earlier < slot → ¬SeatedAt state validator earlier := by
  induction slots with
  | nil => simp [firstInclusionListSlot, pure, Except.pure] at found
  | cons head rest ih =>
    simp only [firstInclusionListSlot, bind, Except.bind] at found
    split at found
    · cases found
    rename_i committee made
    obtain ⟨headFirst, restAscending⟩ := List.pairwise_cons.mp ascending
    split at found
    · rename_i seated
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at found
      subst found
      refine ⟨List.mem_cons_self, ⟨committee, made, seated⟩, fun earlier member below => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact absurd below (UInt64.lt_irrefl _)
      · have after := headFirst earlier later
        rw [UInt64.lt_iff_toNat_lt] at after below
        omega
    · rename_i unseated
      obtain ⟨member, seated, none⟩ := ih restAscending found
      refine ⟨List.mem_cons_of_mem _ member, seated, fun earlier member' below => ?_⟩
      rcases List.mem_cons.mp member' with rfl | later
      · rintro ⟨other, made', seated'⟩
        rw [made] at made'
        cases made'
        exact unseated seated'
      · exact none earlier later below

/-- A search that finds no slot meets no slot that seats the validator. -/
theorem firstInclusionListSlot_none {slots : List Slot}
    (found : firstInclusionListSlot state validator slots = .ok none) :
    ∀ slot ∈ slots, ¬SeatedAt state validator slot := by
  induction slots with
  | nil => simp
  | cons head rest ih =>
    simp only [firstInclusionListSlot, bind, Except.bind] at found
    split at found
    · cases found
    rename_i committee made
    split at found
    · cases found
    rename_i unseated
    intro slot member
    rcases List.mem_cons.mp member with rfl | later
    · rintro ⟨other, made', seated'⟩
      rw [made] at made'
      cases made'
      exact unseated seated'
    · exact ih found slot later

/-- The slots of an epoch, from its first slot, when the last one has no overflow, ascend. -/
private theorem epochSlots_spec {start : Slot} {count : UInt64}
    (fits : start.toNat + count.toNat < 2 ^ 64) :
    ((List.range count.toNat).map fun k => start + k.toUInt64).Pairwise (· < ·) ∧
      ∀ slot, slot ∈ (List.range count.toNat).map (fun k => start + k.toUInt64) ↔
        start.toNat ≤ slot.toNat ∧ slot.toNat < start.toNat + count.toNat := by
  have value : ∀ k < count.toNat, (start + k.toUInt64).toNat = start.toNat + k := by
    intro k below
    rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  constructor
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range)
    intro a b aIn bIn less
    rw [List.mem_range] at aIn bIn
    rw [UInt64.lt_iff_toNat_lt, value a aIn, value b bIn]
    omega
  · intro slot
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨k, below, rfl⟩
      rw [value k below]
      omega
    · rintro ⟨low, high⟩
      refine ⟨slot.toNat - start.toNat, by omega, ?_⟩
      apply UInt64.toNat_inj.mp
      rw [value _ (by omega)]
      omega

/-- An assignment names the first slot of the epoch whose committee seats the validator.

The slots of the epoch are those from its first slot, for one epoch's worth of slots. -/
theorem getInclusionListCommitteeAssignment_some {epoch : Epoch} {slot start : Slot}
    (first : computeStartSlotAtEpoch preset epoch = .ok start)
    (found : getInclusionListCommitteeAssignment state epoch validator = .ok (some slot)) :
    start.toNat ≤ slot.toNat ∧ slot.toNat < start.toNat + preset.SLOTS_PER_EPOCH.toNat ∧
      SeatedAt state validator slot ∧
      ∀ earlier : Slot, start.toNat ≤ earlier.toNat → earlier < slot →
        ¬SeatedAt state validator earlier := by
  simp only [getInclusionListCommitteeAssignment, liftArith, bind, Except.bind,
    Except.mapError] at found
  split at found
  · cases found
  split at found
  · cases found
  split at found
  · cases found
  rename_i slots slotsOk
  have listed : epochSlots preset epoch = .ok slots := by
    revert slotsOk
    cases epochSlots preset epoch <;> simp
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_of_start first listed
  obtain ⟨ascending, range⟩ := epochSlots_spec fits
  obtain ⟨member, seated, none⟩ := firstInclusionListSlot_some ascending found
  obtain ⟨low, high⟩ := (range slot).mp member
  refine ⟨low, high, seated, fun earlier above below => ?_⟩
  have high' : earlier.toNat < start.toNat + preset.SLOTS_PER_EPOCH.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp below
    omega
  exact none earlier ((range earlier).mpr ⟨above, high'⟩) below

/-- No assignment means that no slot of the epoch has a committee that seats the validator. -/
theorem getInclusionListCommitteeAssignment_none {epoch : Epoch} {start : Slot}
    (first : computeStartSlotAtEpoch preset epoch = .ok start)
    (found : getInclusionListCommitteeAssignment state epoch validator = .ok none) :
    ∀ slot : Slot, start.toNat ≤ slot.toNat →
      slot.toNat < start.toNat + preset.SLOTS_PER_EPOCH.toNat →
        ¬SeatedAt state validator slot := by
  simp only [getInclusionListCommitteeAssignment, liftArith, bind, Except.bind,
    Except.mapError] at found
  split at found
  · cases found
  split at found
  · cases found
  split at found
  · cases found
  rename_i slots slotsOk
  have listed : epochSlots preset epoch = .ok slots := by
    revert slotsOk
    cases epochSlots preset epoch <;> simp
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_of_start first listed
  intro slot low high
  exact firstInclusionListSlot_none found slot ((epochSlots_spec fits).2 slot |>.mpr ⟨low, high⟩)

/-- An epoch past the next epoch of the state has no assignment. -/
theorem getInclusionListCommitteeAssignment_epochTooFar {epoch nextEpoch : Epoch}
    (next : addChecked (getCurrentEpoch state) 1 = .ok nextEpoch) (far : nextEpoch < epoch) :
    getInclusionListCommitteeAssignment state epoch validator =
      .error (.epochTooFar epoch nextEpoch) := by
  simp [getInclusionListCommitteeAssignment, liftArith, next, far, bind, Except.bind,
    Except.mapError, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

end EthLib.Consensus

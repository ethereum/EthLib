module

public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.InclusionListCommittee
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the inclusion list committee and its signature

A validator is a member of the beacon committees of a slot exactly when one of them holds it.

Each seat of the inclusion list committee holds such a member, in the order of the committees.

The committee fails exactly when the beacon committees of the slot hold no validator.

A list signed with the key of its member passes the signature check, under the pairing laws.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork} {state : BeaconState preset fork} {slot : Slot}

/-- A validator is among the members of a slot exactly when a beacon committee of it holds it. -/
theorem mem_getSlotCommitteeMembers {members : Array ValidatorIndex}
    (found : getSlotCommitteeMembers state slot = .ok members) {validator : ValidatorIndex} :
    validator ∈ members ↔
      ∃ i < (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat,
        ∃ committee, getBeaconCommittee state slot i.toUInt64 = .ok committee ∧
          validator ∈ committee := by
  simp only [getSlotCommitteeMembers, bind, Except.bind] at found
  split at found
  · cases found
  rename_i committees mapped
  simp only [pure, Except.pure, Except.ok.injEq] at found
  subst found
  simp only [Array.mem_flatten, List.mem_toArray]
  constructor
  · rintro ⟨committee, member, holds⟩
    obtain ⟨i, inRange, made⟩ := mapM_ok_mem mapped committee member
    exact ⟨i, List.mem_range.mp inRange, committee, made, holds⟩
  · rintro ⟨i, inRange, committee, made, holds⟩
    have bound : i < (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).length := by
      simpa using inRange
    have atIndex := mapM_ok_getElem mapped i bound
    rw [List.getElem_range, made] at atIndex
    cases atIndex
    exact ⟨_, List.getElem_mem _, holds⟩

/-- Seat `i` of a committee holds member `i` of the slot, counted modulo the number of members.

The slot then has at least one member. -/
theorem getInclusionListCommittee_seat {members : Array ValidatorIndex}
    {committee : InclusionListCommittee preset}
    (found : getSlotCommitteeMembers state slot = .ok members)
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
    (found : getSlotCommitteeMembers state slot = .ok members) :
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
  cases found : getSlotCommitteeMembers state slot with
  | error e =>
    simp [getInclusionListCommittee, found, bind, Except.bind] at made
  | ok members =>
    obtain ⟨nonempty, seat⟩ := getInclusionListCommittee_seat found made
    rw [seat i]
    exact (mem_getSlotCommitteeMembers found).mp (Array.getElem_mem _)

/-- A list signed with the secret key of its member passes the signature check.

The member must be in the registry with the public key of that secret key.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidInclusionListSignature_of_sign (laws : PairingLaws) {config : Config}
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
  obtain ⟨signature, signs, verifies⟩ := Signatures.verify_sign laws key (packBytes root)
  have same : signature = signed.signature := by
    rw [signs] at signedBy
    simpa [Except.mapError] using signedBy
  subst same
  simp only [isValidInclusionListSignature, registered, rootOk, bind, Except.bind,
    Except.mapError, pure, Except.pure, owned]
  exact congrArg Except.ok verifies

end EthLib.Consensus

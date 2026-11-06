module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Gossip.Seen
public import EthLib.Consensus.HonestValidator
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the duties of an honest validator

Under the pairing laws, each signature of an honest validator passes the check of its receivers.

They check it under the same domain type and epoch, against the public key of the secret key.

A committee assignment is a committee of the epoch that holds the validator.

It is the only one: two committees of one epoch never share a validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- Two errors with one code come from one constructor. -/
theorem ValidatorDutyError.code_injective (e₁ e₂ : ValidatorDutyError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code is one more than the index of its constructor.
  have back : ∀ e : ValidatorDutyError, e.code.toNat - 1 = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

/-! ## Signatures -/

/-- A signature at an epoch passes the check of a signature at that epoch, under its public key.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidSignatureAtEpoch_of_signAtEpoch (laws : PairingLaws) {α : Type} [SszType α]
    {config : Config} {state : BeaconState preset fork} {domainType : DomainType}
    {epoch : Epoch} {object : α} {key : Signatures.SecretKey} {signature : BLSSignature}
    (signed : signAtEpoch config state domainType epoch object key = .ok signature) :
    isValidSignatureAtEpoch config .bls state domainType epoch object (Signatures.skToPk key)
      signature = .ok true := by
  unfold signAtEpoch at signed
  -- Split the binds with lemmas, so the kernel never evaluates the signature.
  obtain ⟨domain, domained, signed⟩ := bind_ok_iff.mp signed
  obtain ⟨root, rooted, signs⟩ := bind_ok_iff.mp signed
  rw [mapError_ok_iff] at domained rooted signs
  obtain ⟨signature', signs', verifies⟩ := Signatures.verify_sign laws key (packBytes root)
  rw [signs', Except.ok.injEq] at signs
  subst signs
  unfold isValidSignatureAtEpoch
  simp only [domained, rooted, bind, Except.bind, Except.mapError, pure, Except.pure]
  exact congrArg Except.ok verifies

/-- A selection proof for the slot of an aggregate passes the gossip check of a selection proof.

The check reads the target epoch of the aggregate, which must be the epoch of its slot.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidSignatureAtEpoch_getSlotSignature (laws : PairingLaws) {config : Config}
    {state : BeaconState preset fork} {data : AttestationData} {key : Signatures.SecretKey}
    {proof : BLSSignature} (sameEpoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    (signed : getSlotSignature config state data.slot key = .ok proof) :
    isValidSignatureAtEpoch config .bls state DOMAIN_SELECTION_PROOF data.target.epoch data.slot
      (Signatures.skToPk key) proof = .ok true := by
  rw [sameEpoch]
  exact isValidSignatureAtEpoch_of_signAtEpoch laws signed

/-- An aggregate and proof signed by its aggregator passes the gossip check of its signature.

The check reads the target epoch of the aggregate, which must be the epoch of its slot.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidSignatureAtEpoch_getAggregateAndProofSignature (laws : PairingLaws)
    {config : Config} {state : BeaconState preset fork} {proof : AggregateAndProof preset fork}
    {key : Signatures.SecretKey} {signature : BLSSignature}
    (sameEpoch : proof.aggregate.data.target.epoch =
      computeEpochAtSlot preset proof.aggregate.data.slot)
    (signed : getAggregateAndProofSignature config state proof key = .ok signature) :
    isValidSignatureAtEpoch config .bls state DOMAIN_AGGREGATE_AND_PROOF
      proof.aggregate.data.target.epoch proof (Signatures.skToPk key) signature = .ok true := by
  rw [sameEpoch]
  exact isValidSignatureAtEpoch_of_signAtEpoch laws signed

/-- A sync committee message passes the check of a signature at the epoch of its slot.

The state must be at a slot of the current epoch, as the message takes its slot from it.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidSignatureAtSlot_getSyncCommitteeMessage (laws : PairingLaws) {config : Config}
    {state : BeaconState preset fork} {blockRoot : Root} {validatorIndex : ValidatorIndex}
    {key : Signatures.SecretKey} {message : SyncCommitteeMessage}
    (signed : getSyncCommitteeMessage config state blockRoot validatorIndex key = .ok message) :
    isValidSignatureAtSlot config .bls state DOMAIN_SYNC_COMMITTEE message.slot
      message.beaconBlockRoot (Signatures.skToPk key) message.signature = .ok true := by
  unfold getSyncCommitteeMessage at signed
  obtain ⟨signature, signs, made⟩ := bind_ok_iff.mp signed
  simp only [pure, Except.pure, Except.ok.injEq] at made
  subst made
  exact isValidSignatureAtEpoch_of_signAtEpoch laws signs

/-- A contribution and proof signed by its aggregator passes the check at the epoch of its slot.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidSignatureAtSlot_getContributionAndProofSignature (laws : PairingLaws)
    {config : Config} {state : BeaconState preset fork} {proof : ContributionAndProof preset}
    {key : Signatures.SecretKey} {signature : BLSSignature}
    (signed : getContributionAndProofSignature config state proof key = .ok signature) :
    isValidSignatureAtSlot config .bls state DOMAIN_CONTRIBUTION_AND_PROOF
      proof.contribution.slot proof (Signatures.skToPk key) signature = .ok true :=
  isValidSignatureAtEpoch_of_signAtEpoch laws signed

/-! ## Committee assignments -/

/-- A committee that the search returns is the committee of one of its positions.

It holds the validator. -/
theorem findCommittee_sound {state : BeaconState preset fork} {validatorIndex : ValidatorIndex} :
    ∀ {positions : List (Slot × CommitteeIndex)} {committee : Array ValidatorIndex}
      {index : CommitteeIndex} {slot : Slot},
      findCommittee state validatorIndex positions = .ok (some (committee, index, slot)) →
      (slot, index) ∈ positions ∧ getBeaconCommittee state slot index = .ok committee ∧
        validatorIndex ∈ committee
  | [], _, _, _, h => by simp [findCommittee, pure, Except.pure] at h
  | (slot', index') :: rest, committee, index, slot, h => by
    unfold findCommittee at h
    obtain ⟨committee', computed, h⟩ := bind_ok_iff.mp h
    rw [mapError_ok_iff] at computed
    split at h
    · rename_i mem
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, computed, mem⟩
    · obtain ⟨mem, computed', member⟩ := findCommittee_sound h
      exact ⟨List.mem_cons_of_mem _ mem, computed', member⟩

/-- Each position of an epoch is a slot of the epoch and an index below the committees of a slot. -/
theorem mem_committeePositions {state : BeaconState preset fork} {epoch : Epoch}
    {positions : List (Slot × CommitteeIndex)}
    (h : committeePositions state epoch = .ok positions) {slot : Slot} {index : CommitteeIndex}
    (mem : (slot, index) ∈ positions) :
    computeEpochAtSlot preset slot = epoch ∧ index < getCommitteeCountPerSlot state epoch := by
  unfold committeePositions at h
  obtain ⟨startSlot, started, h⟩ := bind_ok_iff.mp h
  rw [mapError_ok_iff] at started
  have start := (mulChecked_ok_iff.mp started)
  split at h
  · rename_i fits
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at mem
    obtain ⟨offset, offsetLt, index', indexLt, rfl, rfl⟩ := mem
    have perSmall := (getCommitteeCountPerSlot state epoch).toNat_lt
    refine ⟨?_, UInt64.lt_iff_toNat_lt.mpr (by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans indexLt perSmall)]
      exact indexLt)⟩
    -- The slot is the first slot of the epoch plus an offset below the length of an epoch.
    have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) offsetLt
    have offsetSmall : offset < 2 ^ 64 :=
      Nat.lt_of_lt_of_le offsetLt (Nat.le_of_lt preset.SLOTS_PER_EPOCH.toNat_lt)
    have sum : (startSlot + offset.toUInt64).toNat = startSlot.toNat + offset := by
      rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt offsetSmall]
      exact Nat.mod_eq_of_lt (by omega)
    apply UInt64.toNat_inj.mp
    simp only [computeEpochAtSlot, UInt64.toNat_div, sum, start.2]
    rw [Nat.mul_comm, Nat.mul_add_div lengthPos, Nat.div_eq_of_lt offsetLt, Nat.add_zero]
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A committee assignment is a committee of the epoch that holds the validator.

Its slot is in the epoch, and its index is below the committees of a slot. -/
theorem getCommitteeAssignment_sound {state : BeaconState preset fork} {epoch : Epoch}
    {validatorIndex : ValidatorIndex} {committee : Array ValidatorIndex} {index : CommitteeIndex}
    {slot : Slot}
    (h : getCommitteeAssignment state epoch validatorIndex = .ok (some (committee, index, slot))) :
    computeEpochAtSlot preset slot = epoch ∧ index < getCommitteeCountPerSlot state epoch ∧
      getBeaconCommittee state slot index = .ok committee ∧ validatorIndex ∈ committee := by
  unfold getCommitteeAssignment at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  split at h
  · obtain ⟨positions, positioned, found⟩ := bind_ok_iff.mp h
    obtain ⟨mem, computed, member⟩ := findCommittee_sound found
    exact ⟨(mem_committeePositions positioned mem).1, (mem_committeePositions positioned mem).2,
      computed, member⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A committee assignment is the only committee of the epoch that holds the validator.

Take a committee of a slot of the epoch, with an index below the committees of a slot.

If it holds the validator, it has the slot and the index of the assignment.

The registry must stay within its limit.

The number of active validators times the number of committees of the epoch must fit in 64 bits. -/
theorem getCommitteeAssignment_unique {state : BeaconState preset fork} {epoch : Epoch}
    (within : state.RegistryWithinLimit)
    (fits : (getActiveValidatorIndices state epoch).length *
      ((getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {validatorIndex : ValidatorIndex} {committee : Array ValidatorIndex} {index : CommitteeIndex}
    {slot : Slot}
    (assigned :
      getCommitteeAssignment state epoch validatorIndex = .ok (some (committee, index, slot)))
    {otherSlot : Slot} {otherIndex : CommitteeIndex} {otherCommittee : Array ValidatorIndex}
    (otherEpoch : computeEpochAtSlot preset otherSlot = epoch)
    (otherLt : otherIndex < getCommitteeCountPerSlot state epoch)
    (otherComputed : getBeaconCommittee state otherSlot otherIndex = .ok otherCommittee)
    (otherMem : validatorIndex ∈ otherCommittee) :
    otherSlot = slot ∧ otherIndex = index := by
  obtain ⟨slotEpoch, indexLt, computed, member⟩ := getCommitteeAssignment_sound assigned
  subst otherEpoch
  exact eq_of_mem_getBeaconCommittee within (slotEpoch.symm) otherLt (slotEpoch ▸ indexLt) fits
    otherComputed computed otherMem member

end EthLib.Consensus

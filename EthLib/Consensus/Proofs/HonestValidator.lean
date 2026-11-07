module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.List
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.Gossip.Seen
public import EthLib.Consensus.HonestValidator
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Gossip.SyncCommittee
public import EthLib.Consensus.Transition.Block
public import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the duties of an honest validator

Under the pairing laws, each signature of an honest validator passes the check of its receivers.

They check it under the same domain type and epoch, against the public key of the secret key.

A committee assignment is a committee of the epoch that holds the validator.

It is the only one under two bounds.

The registry stays within its limit, and its active validators times the committees fit in 64 bits.

The proposer check and the sync committee seat check have their outcomes characterized.

The sync committee subnets of a validator come once each, in increasing order.
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

/-- A signature at an epoch is a signature of the signing root of the object at that epoch.

Under the laws of the pairing, it verifies under the public key of the secret key. -/
theorem signAtEpoch_verifies (laws : PairingLaws) {α : Type} [SszType α] {config : Config}
    {state : BeaconState preset fork} {domainType : DomainType} {epoch : Epoch} {object : α}
    {key : Signatures.SecretKey} {signature : BLSSignature}
    (signed : signAtEpoch config state domainType epoch object key = .ok signature) :
    ∃ domain root, getDomain config state domainType (some epoch) = .ok domain ∧
      computeSigningRoot object domain = .ok root ∧
      Signatures.verify (packBytes (Signatures.skToPk key)) (packBytes root)
        (packBytes signature) = true := by
  unfold signAtEpoch at signed
  -- Split the binds with lemmas, so the kernel never evaluates the signature.
  obtain ⟨domain, domained, signed⟩ := bind_ok_iff.mp signed
  obtain ⟨root, rooted, signs⟩ := bind_ok_iff.mp signed
  rw [mapError_ok_iff] at domained rooted signs
  obtain ⟨signature', signs', verifies⟩ := Signatures.verify_sign laws key (packBytes root)
  rw [signs', Except.ok.injEq] at signs
  subst signs
  exact ⟨domain, root, domained, rooted, verifies⟩

/-- A signature at an epoch passes the check of a signature at that epoch, under its public key.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem isValidSignatureAtEpoch_of_signAtEpoch (laws : PairingLaws) {α : Type} [SszType α]
    {config : Config} {state : BeaconState preset fork} {domainType : DomainType}
    {epoch : Epoch} {object : α} {key : Signatures.SecretKey} {signature : BLSSignature}
    (signed : signAtEpoch config state domainType epoch object key = .ok signature) :
    isValidSignatureAtEpoch config .bls state domainType epoch object (Signatures.skToPk key)
      signature = .ok true := by
  obtain ⟨domain, root, domained, rooted, verifies⟩ := signAtEpoch_verifies laws signed
  unfold isValidSignatureAtEpoch
  simp only [domained, rooted, bind, Except.bind, Except.mapError, pure, Except.pure]
  exact congrArg Except.ok verifies

/-- A block signed by its proposer passes the check of the block's signature.

The block must be for a slot of the current epoch, and the proposer must have the public key.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem verifyBlockSignature_of_getBlockSignature (laws : PairingLaws) {config : Config}
    {state : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {key : Signatures.SecretKey} {proposer : Validator}
    (registered : getValidator state signed.message.proposerIndex = .ok proposer)
    (owned : proposer.pubkey = Signatures.skToPk key)
    (current : computeEpochAtSlot preset signed.message.slot = getCurrentEpoch state)
    (signedBy : getBlockSignature config state signed.message key = .ok signed.signature) :
    verifyBlockSignature config .bls state signed = .ok true := by
  unfold getBlockSignature at signedBy
  rw [current] at signedBy
  obtain ⟨domain, root, domained, rooted, verifies⟩ := signAtEpoch_verifies laws signedBy
  unfold verifyBlockSignature
  -- The domain of the current epoch is the default domain of the state.
  have domainDefault : getDomain config state DOMAIN_BEACON_PROPOSER = .ok domain := domained
  simp only [liftAccessor, liftSsz, registered, domainDefault, rooted, Except.mapError, bind,
    Except.bind, pure, Except.pure, owned, SignatureChecks.bls, verifies]

/-- The RANDAO reveal of the proposer passes the RANDAO check of its block.

The block must be for a slot of the current epoch, and the proposer must have the public key.

The processing of the reveal may still fail for another reason, never for an invalid reveal.

The statement holds under the laws of the pairing, as BLS correctness does. -/
theorem processRandao_ne_invalidRandaoReveal (laws : PairingLaws) {config : Config}
    {state : BeaconState preset fork} {block : BeaconBlock preset fork}
    {key : Signatures.SecretKey} {proposerIndex : ValidatorIndex} {proposer : Validator}
    (proposes : getBeaconProposerIndex state = .ok proposerIndex)
    (registered : getValidator state proposerIndex = .ok proposer)
    (owned : proposer.pubkey = Signatures.skToPk key)
    (current : computeEpochAtSlot preset block.slot = getCurrentEpoch state)
    (signedBy : getEpochSignature config state block key = .ok block.body.randaoReveal) :
    processRandao config .bls state block.body ≠ .error .invalidRandaoReveal := by
  unfold getEpochSignature at signedBy
  simp only [current] at signedBy
  obtain ⟨domain, root, domained, rooted, verifies⟩ := signAtEpoch_verifies laws signedBy
  have domainDefault : getDomain config state DOMAIN_RANDAO = .ok domain := domained
  unfold processRandao
  simp only [liftAccessor, liftSsz, proposes, registered, domainDefault, rooted, Except.mapError,
    bind, Except.bind, pure, Except.pure, owned, SignatureChecks.bls, verifies, ensure,
    ↓reduceIte]
  -- What is left reads and writes the mix of the epoch, whose errors are accessor errors.
  cases getRandaoMix state (getCurrentEpoch state) with
  | error => simp
  | ok mix =>
    simp only
    cases writeCircularRooted state.randaoMixes (getCurrentEpoch state) _ <;> simp

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

The message takes its slot from the state, so that epoch is the current epoch that it signs in.

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

/-- The slots of an epoch are its first slot plus each offset below the length of an epoch.

The sum of the first slot and that length is below `2^64`. -/
theorem epochSlots_eq_ok_iff {epoch : Epoch} {slots : List Slot} :
    epochSlots preset epoch = .ok slots ↔
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 ∧
        slots = (List.range preset.SLOTS_PER_EPOCH.toNat).map fun offset =>
          epoch * preset.SLOTS_PER_EPOCH + offset.toUInt64 := by
  unfold epochSlots computeStartSlotAtEpoch mulChecked addChecked
  by_cases mul : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64
  · have product : (epoch * preset.SLOTS_PER_EPOCH).toNat =
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt mul]
    by_cases add : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat <
        2 ^ 64
    · simp only [mul, product, add, ite_true, Except.mapError, bind, Except.bind, pure,
        Except.pure, Except.ok.injEq, true_and, eq_comm]
    · simp only [mul, product, add, ite_true, ite_false, Except.mapError, bind, Except.bind,
        false_and, reduceCtorEq]
  · have add : ¬epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat <
        2 ^ 64 := by omega
    simp only [mul, add, ite_false, Except.mapError, bind, Except.bind, false_and, reduceCtorEq]

/-- An epoch whose first slot plus the length of an epoch reaches `2^64` has no slots.

The guide computes that sum as a 64-bit integer, which overflows there. -/
theorem epochSlots_eq_error {epoch : Epoch}
    (big : 2 ^ 64 ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat) :
    epochSlots preset epoch = .error (.arith .overflow) := by
  unfold epochSlots computeStartSlotAtEpoch mulChecked addChecked
  by_cases mul : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64
  · have product : (epoch * preset.SLOTS_PER_EPOCH).toNat =
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_mul, Nat.mod_eq_of_lt mul]
    have add : ¬epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat <
        2 ^ 64 := Nat.not_lt.mpr big
    simp only [mul, product, add, ite_true, ite_false, Except.mapError, bind, Except.bind]
  · simp only [mul, ite_false, Except.mapError, bind, Except.bind]

/-- No committee assignment exists for an epoch whose slots do not fit in 64 bits.

The search fails there, before it reads any committee. -/
theorem getCommitteeAssignment_eq_error_of_overflow {state : BeaconState preset fork}
    {epoch : Epoch} {validatorIndex : ValidatorIndex}
    (big : 2 ^ 64 ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat)
    (near : epoch.toNat ≤ (getCurrentEpoch state).toNat + 1) :
    getCommitteeAssignment state epoch validatorIndex = .error (.arith .overflow) := by
  unfold getCommitteeAssignment committeePositions
  cases next : addChecked (getCurrentEpoch state) 1 with
  | error e =>
    -- The next epoch overflows too, with the same error.
    have : e = .overflow := by
      unfold addChecked at next
      split at next <;> simp_all
    subst this
    simp [Except.mapError, bind, Except.bind]
  | ok nextEpoch =>
    have nextNat := (addChecked_ok_iff.mp next).2
    have within : epoch ≤ nextEpoch := UInt64.le_iff_toNat_le.mpr (by simp at nextNat; omega)
    simp [Except.mapError, bind, Except.bind, within, epochSlots_eq_error big]

/-- The slot at an offset below the length of an epoch, as a number. -/
theorem toNat_epochSlot {epoch : Epoch}
    (fits : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    {offset : Nat} (offsetLt : offset < preset.SLOTS_PER_EPOCH.toNat) :
    (epoch * preset.SLOTS_PER_EPOCH + offset.toUInt64).toNat =
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + offset := by
  have offsetSmall : offset < 2 ^ 64 :=
    Nat.lt_of_lt_of_le offsetLt (Nat.le_of_lt preset.SLOTS_PER_EPOCH.toNat_lt)
  have productSmall : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt productSmall]
  exact Nat.mod_eq_of_lt (by omega)

/-- Each slot of an epoch has that epoch. -/
theorem mem_epochSlots {epoch : Epoch} {slots : List Slot} (h : epochSlots preset epoch = .ok slots)
    {slot : Slot} (mem : slot ∈ slots) : computeEpochAtSlot preset slot = epoch := by
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_iff.mp h
  simp only [List.mem_map, List.mem_range] at mem
  obtain ⟨offset, offsetLt, rfl⟩ := mem
  -- The slot is the first slot of the epoch plus an offset below the length of an epoch.
  have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) offsetLt
  apply UInt64.toNat_inj.mp
  simp only [computeEpochAtSlot, UInt64.toNat_div, toNat_epochSlot fits offsetLt]
  rw [Nat.mul_comm, Nat.mul_add_div lengthPos, Nat.div_eq_of_lt offsetLt, Nat.add_zero]

/-- Each slot of an epoch is among its slots, when an epoch has at least one slot. -/
theorem mem_epochSlots_of_epoch {epoch : Epoch} {slots : List Slot}
    (positive : preset.SLOTS_PER_EPOCH ≠ 0) (h : epochSlots preset epoch = .ok slots)
    {slot : Slot} (slotEpoch : computeEpochAtSlot preset slot = epoch) : slot ∈ slots := by
  obtain ⟨fits, rfl⟩ := epochSlots_eq_ok_iff.mp h
  have lengthPos : 0 < preset.SLOTS_PER_EPOCH.toNat :=
    Nat.pos_of_ne_zero fun zero => positive (UInt64.toNat_inj.mp (by simpa using zero))
  have epochNat := congrArg UInt64.toNat slotEpoch
  simp only [computeEpochAtSlot, UInt64.toNat_div] at epochNat
  -- The slot is the first slot of the epoch plus its place in the epoch.
  have split := Nat.div_add_mod slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [epochNat] at split
  have offsetLt := Nat.mod_lt slot.toNat lengthPos
  simp only [List.mem_map, List.mem_range]
  refine ⟨slot.toNat % preset.SLOTS_PER_EPOCH.toNat, offsetLt, ?_⟩
  apply UInt64.toNat_inj.mp
  rw [toNat_epochSlot fits offsetLt, Nat.mul_comm, split]

/-- Each position of an epoch is a slot of the epoch and an index below the committees of a slot. -/
theorem mem_committeePositions {state : BeaconState preset fork} {epoch : Epoch}
    {positions : List (Slot × CommitteeIndex)}
    (h : committeePositions state epoch = .ok positions) {slot : Slot} {index : CommitteeIndex}
    (mem : (slot, index) ∈ positions) :
    computeEpochAtSlot preset slot = epoch ∧ index < getCommitteeCountPerSlot state epoch := by
  unfold committeePositions at h
  obtain ⟨slots, sloted, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at mem
  obtain ⟨slot', mem', index', indexLt, rfl, rfl⟩ := mem
  have perSmall := (getCommitteeCountPerSlot state epoch).toNat_lt
  refine ⟨mem_epochSlots sloted mem', UInt64.lt_iff_toNat_lt.mpr ?_⟩
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans indexLt perSmall)]
  exact indexLt

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

/-- A search that finds nothing found no position whose committee holds the validator. -/
theorem not_mem_of_findCommittee_none {state : BeaconState preset fork}
    {validatorIndex : ValidatorIndex} :
    ∀ {positions : List (Slot × CommitteeIndex)},
      findCommittee state validatorIndex positions = .ok none →
      ∀ position ∈ positions, ∀ committee,
        getBeaconCommittee state position.1 position.2 = .ok committee →
        validatorIndex ∉ committee
  | [], _, _, mem, _, _ => absurd mem List.not_mem_nil
  | (slot, index) :: rest, h, position, mem, committee, computed => by
    unfold findCommittee at h
    obtain ⟨committee', computed', h⟩ := bind_ok_iff.mp h
    rw [mapError_ok_iff] at computed'
    split at h
    · cases h
    rename_i notMem
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [computed, Except.ok.injEq] at computed'
      exact computed' ▸ notMem
    · exact not_mem_of_findCommittee_none h position mem committee computed

/-- Each slot of an epoch, with an index below the committees of a slot, is a position of it.

An epoch must have at least one slot. -/
theorem mem_committeePositions_of_epoch {state : BeaconState preset fork} {epoch : Epoch}
    {positions : List (Slot × CommitteeIndex)} (positive : preset.SLOTS_PER_EPOCH ≠ 0)
    (h : committeePositions state epoch = .ok positions) {slot : Slot} {index : CommitteeIndex}
    (slotEpoch : computeEpochAtSlot preset slot = epoch)
    (indexLt : index < getCommitteeCountPerSlot state epoch) :
    (slot, index) ∈ positions := by
  unfold committeePositions at h
  obtain ⟨slots, sloted, h⟩ := bind_ok_iff.mp h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨slot, mem_epochSlots_of_epoch positive sloted slotEpoch, index.toNat,
    UInt64.lt_iff_toNat_lt.mp indexLt, rfl, by simp⟩

/-- An active validator never gets the answer that it has no committee in its epoch.

The search may still fail, for an epoch too far ahead or a committee without a value.

It also fails for the epoch whose first slot plus the length of an epoch is `2^64`.

The seed of the epoch must have a value, and an epoch must have at least one slot.

The slots of the epoch must fit in 64 bits.

There must be at most `2^40` active validators.

Their number times the number of committees of the epoch must fit in 64 bits. -/
theorem getCommitteeAssignment_ne_none {state : BeaconState preset fork} {epoch : Epoch}
    {seed : Bytes32} (seedOk : getSeed state epoch DOMAIN_BEACON_ATTESTER = .ok seed)
    (positive : preset.SLOTS_PER_EPOCH ≠ 0)
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (small : (getActiveValidatorIndices state epoch).length ≤ 2 ^ 40)
    (fits : (getActiveValidatorIndices state epoch).length *
      ((getCommitteeCountPerSlot state epoch).toNat * preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    {validatorIndex : ValidatorIndex}
    (active : validatorIndex ∈ getActiveValidatorIndices state epoch) :
    getCommitteeAssignment state epoch validatorIndex ≠ .ok none := by
  intro h
  unfold getCommitteeAssignment at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  split at h
  · obtain ⟨positions, positioned, found⟩ := bind_ok_iff.mp h
    obtain ⟨slot, index, committee, slotEpoch, indexLt, computed, mem⟩ :=
      exists_mem_getBeaconCommittee seedOk positive slotsFit small fits active
    exact not_mem_of_findCommittee_none found (slot, index)
      (mem_committeePositions_of_epoch positive positioned slotEpoch indexLt) committee computed mem
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Proposer and sync committee duties -/

/-- The check of a proposer succeeds exactly when the proposer index of the state exists.

It then returns whether that index is the validator. -/
theorem isProposer_ok_iff {state : BeaconState preset fork} {validatorIndex : ValidatorIndex}
    {b : Bool} :
    isProposer state validatorIndex = .ok b ↔
      ∃ proposer, getBeaconProposerIndex state = .ok proposer ∧
        (proposer == validatorIndex) = b := by
  unfold isProposer
  rw [bind_ok_iff]
  simp only [mapError_ok_iff, pure, Except.pure, Except.ok.injEq]

/-- A validator is the proposer exactly when it is the proposer index of the state. -/
theorem isProposer_eq_ok_true_iff {state : BeaconState preset fork}
    {validatorIndex : ValidatorIndex} :
    isProposer state validatorIndex = .ok true ↔
      getBeaconProposerIndex state = .ok validatorIndex := by
  rw [isProposer_ok_iff]
  constructor
  · rintro ⟨proposer, found, eq⟩
    rw [beq_iff_eq] at eq
    exact eq ▸ found
  · intro found
    exact ⟨validatorIndex, found, beq_self_eq_true _⟩

/-- A validator other than the proposer index of the state gets the answer that it does not propose.

The proposer index must exist. -/
theorem isProposer_eq_ok_false_of_ne {state : BeaconState preset fork}
    {validatorIndex proposer : ValidatorIndex}
    (found : getBeaconProposerIndex state = .ok proposer) (ne : proposer ≠ validatorIndex) :
    isProposer state validatorIndex = .ok false :=
  isProposer_ok_iff.mpr ⟨proposer, found, by simpa using ne⟩

/-- The check of a proposer fails exactly when the proposer index of the state fails.

It fails with the same error, as an accessor error. -/
theorem isProposer_eq_error_iff {state : BeaconState preset fork}
    {validatorIndex : ValidatorIndex} {e : ValidatorDutyError} :
    isProposer state validatorIndex = .error e ↔
      ∃ accessorError, getBeaconProposerIndex state = .error accessorError ∧
        e = .accessor accessorError := by
  unfold isProposer
  cases found : getBeaconProposerIndex state with
  | ok proposer => simp [bind, Except.bind, Except.mapError, pure, Except.pure]
  | error accessorError =>
    simp [bind, Except.bind, Except.mapError, eq_comm]

/-- The seat check succeeds exactly when the period is the current one or the next.

The next period must not overflow, and the validator must exist.

The answer says whether its key is in the current committee, or in the next one. -/
theorem isAssignedToSyncCommittee_ok_iff {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {epoch : Epoch} {validatorIndex : ValidatorIndex} {b : Bool} :
    isAssignedToSyncCommittee state altair epoch validatorIndex = .ok b ↔
      (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1 < 2 ^ 64 ∧
      ∃ validator, getValidator state validatorIndex = .ok validator ∧
        ((computeSyncCommitteePeriod preset epoch =
            computeSyncCommitteePeriod preset (getCurrentEpoch state) ∧
          (state.currentSyncCommittee altair).pubkeys.contains validator.pubkey = b) ∨
        (computeSyncCommitteePeriod preset epoch =
            computeSyncCommitteePeriod preset (getCurrentEpoch state) + 1 ∧
          (state.nextSyncCommittee altair).pubkeys.contains validator.pubkey = b)) := by
  unfold isAssignedToSyncCommittee
  simp only [bind_ok_iff, mapError_ok_iff]
  generalize computeSyncCommitteePeriod preset epoch = p
  generalize computeSyncCommitteePeriod preset (getCurrentEpoch state) = c
  -- The next period of `c`, when it exists, is `c + 1`.
  have next : ∀ a : UInt64, addChecked c 1 = .ok a ↔ c.toNat + 1 < 2 ^ 64 ∧ a = c + 1 := by
    intro a
    rw [addChecked_ok_iff]
    constructor
    · rintro ⟨fits, sum⟩
      refine ⟨by simpa using fits, UInt64.toNat_inj.mp ?_⟩
      rw [toNat_add_of_lt (by simpa using fits), sum]
    · rintro ⟨fits, rfl⟩
      exact ⟨by simpa using fits, toNat_add_of_lt (by simpa using fits)⟩
  have ne : c + 1 ≠ c := by
    intro eq
    have := congrArg UInt64.toNat eq
    rw [UInt64.toNat_add] at this
    have := c.toNat_lt
    simp at *
  constructor
  · rintro ⟨a, added, h⟩
    obtain ⟨fits, rfl⟩ := (next a).mp added
    refine ⟨fits, ?_⟩
    by_cases hp : p = c ∨ p = c + 1
    · simp only [hp, ↓reduceIte] at h
      obtain ⟨validator, found, h⟩ := bind_ok_iff.mp h
      rw [mapError_ok_iff] at found
      refine ⟨validator, found, ?_⟩
      rcases hp with rfl | rfl
      · simp [pure, Except.pure] at h
        exact Or.inl ⟨rfl, h⟩
      · simp [ne, pure, Except.pure] at h
        exact Or.inr ⟨rfl, h⟩
    · simp only [hp, ↓reduceIte] at h
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rintro ⟨fits, validator, found, h⟩
    refine ⟨c + 1, (next _).mpr ⟨fits, rfl⟩, ?_⟩
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · simp only [true_or, ↓reduceIte]
      refine bind_ok_iff.mpr ⟨validator, (mapError_ok_iff).mpr found, ?_⟩
      simpa [pure, Except.pure] using h
    · simp only [or_true, ↓reduceIte]
      refine bind_ok_iff.mpr ⟨validator, (mapError_ok_iff).mpr found, ?_⟩
      simpa [ne, pure, Except.pure] using h

/-- A period other than the current one and the next is out of range.

The next period must not overflow. -/
theorem isAssignedToSyncCommittee_eq_error_of_ne {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {epoch : Epoch} {validatorIndex : ValidatorIndex}
    (fits : (computeSyncCommitteePeriod preset (getCurrentEpoch state)).toNat + 1 < 2 ^ 64)
    (notCurrent : computeSyncCommitteePeriod preset epoch ≠
      computeSyncCommitteePeriod preset (getCurrentEpoch state))
    (notNext : computeSyncCommitteePeriod preset epoch ≠
      computeSyncCommitteePeriod preset (getCurrentEpoch state) + 1) :
    isAssignedToSyncCommittee state altair epoch validatorIndex =
      .error (.periodOutOfRange (computeSyncCommitteePeriod preset epoch)
        (computeSyncCommitteePeriod preset (getCurrentEpoch state))) := by
  unfold isAssignedToSyncCommittee
  have : ¬(computeSyncCommitteePeriod preset epoch =
      computeSyncCommitteePeriod preset (getCurrentEpoch state) ∨
    computeSyncCommitteePeriod preset epoch =
      computeSyncCommitteePeriod preset (getCurrentEpoch state) + 1) := by
    rintro (h | h)
    exacts [notCurrent h, notNext h]
  have added := addChecked_of_lt (a := computeSyncCommitteePeriod preset (getCurrentEpoch state))
    (b := 1) (by simpa using fits)
  simp [this, added, Except.mapError, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-! ## Sync committee subnets -/

/-- The subnets of a key come once each. -/
theorem syncSubnetsOfPubkey_nodup (committee : SyncCommittee preset) (pubkey : BLSPubkey) :
    (syncSubnetsOfPubkey committee pubkey).Nodup :=
  Base.nodup_eraseDups _

/-- The subnets of a validator come from the committee of the next slot and the validator's key.

They come once each, in strictly increasing order.

A subnet is among them exactly when a seat of the key falls in its subcommittee. -/
theorem computeSubnetsForSyncCommittee_ok {state : BeaconState preset fork}
    {altair : .altair ≤ fork} {validatorIndex : ValidatorIndex} {subnets : List UInt64}
    (h : computeSubnetsForSyncCommittee state altair validatorIndex = .ok subnets) :
    ∃ committee validator, syncCommitteeAtNextSlot state altair = .ok committee ∧
      getValidator state validatorIndex = .ok validator ∧
      subnets.Pairwise (· < ·) ∧
      ∀ subnet, subnet ∈ subnets ↔
        ∃ position, committee.pubkeys.toList[position]? = some validator.pubkey ∧
          (position / syncSubcommitteeSize preset).toUInt64 = subnet := by
  unfold computeSubnetsForSyncCommittee at h
  obtain ⟨committee, committed, h⟩ := bind_ok_iff.mp h
  obtain ⟨validator, validated, h⟩ := bind_ok_iff.mp h
  rw [mapError_ok_iff] at committed validated
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨committee, validator, committed, validated, ?_, fun subnet => ?_⟩
  · -- Sorted and without repeats, so strictly increasing.
    have nodup : (List.mergeSort (syncSubnetsOfPubkey committee validator.pubkey)
        (· ≤ ·)).Nodup :=
      (List.mergeSort_perm _ _).nodup_iff.mpr (syncSubnetsOfPubkey_nodup _ _)
    have sorted := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
      (by intro a b c; simpa using UInt64.le_trans) (by intro a b; simpa using UInt64.le_total a b)
      (syncSubnetsOfPubkey committee validator.pubkey)
    exact (sorted.and nodup).imp fun ⟨hle, hne⟩ => UInt64.lt_of_le_of_ne (by simpa using hle) hne
  · rw [(List.mergeSort_perm _ _).mem_iff, mem_syncSubnetsOfPubkey]

end EthLib.Consensus

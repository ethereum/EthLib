module

public import EthLib.Consensus.Gossip.Attestation
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Gossip.SyncCommittee

/-!
# Proofs: the outcomes of the attestation and aggregate topics

Each topic checks a vote in a fixed order, so its outcome is a chain of checks.

The chain needs the head state, the subnet, the committee and the signatures.

It also needs the checks of the clock and of the ancestors of the block voted for.

Once these are computed, the outcome is that chain.

From the chain follows which votes each topic accepts and which it ignores.

A valid vote records its keys, and the same vote is then ignored.

From Gloas a vote whose payload checks pass also passes those of the fork choice.

The checks of an aggregate cut its committee and its participants from one shuffle.

Reading each of them from the state alone gives the same outcome, errors included.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {statuses : PayloadStatuses}
  {currentTimeMs subnetId : UInt64}

/-! ## Helpers -/

/-- Earlier bits of another length never cover new bits. -/
theorem isNonStrictSuperset_of_length_ne {prior bits : List Bool}
    (other : prior.length ≠ bits.length) : isNonStrictSuperset [prior] bits = false := by
  simp [isNonStrictSuperset, other]

/-- Earlier bits cover new bits of the same length that set fewer bits.

For example `[true, true]` covers `[true, false]`. -/
theorem isNonStrictSuperset_witness : isNonStrictSuperset [[true, true]] [true, false] = true := by
  decide

/-- The block voted for passes exactly when the node knows it and holds its state. -/
theorem votedBlockOutcome_eq_accept {root : Root} :
    votedBlockOutcome store root = accept ↔ root ∈ store.blocks ∧ root ∈ store.blockStates := by
  unfold votedBlockOutcome
  by_cases known : root ∈ store.blocks <;> simp [known]

/-- The block voted for makes the vote ignored exactly when the node does not know it. -/
theorem votedBlockOutcome_eq_ignore {root : Root} {reason : String} :
    votedBlockOutcome store root = .ignore reason ↔
      root ∉ store.blocks ∧ reason = "block being voted for has not been seen" := by
  unfold votedBlockOutcome
  by_cases known : root ∈ store.blocks <;>
    simp [known, rejectUnless, ignoreUnless, ValidationResult.andThen] <;> grind

/-- Before Deneb the clock must be in the propagation range of slots from the slot of the vote. -/
theorem voteTimeOutcome_of_lt_deneb {slot : Slot} {futureReason epochReason : String}
    {within : Bool} (early : ¬ .dencun ≤ fork)
    (range : store.isWithinSlotRange config slot config.ATTESTATION_PROPAGATION_SLOT_RANGE
      currentTimeMs = .ok within) :
    voteTimeOutcome config store slot currentTimeMs futureReason epochReason =
      .ok (ignoreUnless within "attestation slot not within propagation range") := by
  simp [voteTimeOutcome, early, range, bind, Except.bind, pure, Except.pure]

/-- From Deneb the slot of the vote must not be in the future, and its epoch must be recent. -/
theorem voteTimeOutcome_of_deneb {slot : Slot} {futureReason epochReason : String}
    {future recent : Bool} (deneb : .dencun ≤ fork)
    (clock : store.isFutureSlot config slot currentTimeMs = .ok future)
    (epoch : store.isCurrentOrPreviousEpoch config (computeEpochAtSlot preset slot)
      currentTimeMs = .ok recent) :
    voteTimeOutcome config store slot currentTimeMs futureReason epochReason =
      .ok ((ignoreUnless (!future) futureReason).andThen fun _ =>
        ignoreUnless recent epochReason) := by
  cases future <;> simp [voteTimeOutcome, deneb, clock, epoch, bind, Except.bind, pure,
    Except.pure]

/-- The checks of the clock never reject. -/
theorem voteTimeOutcome_ne_reject {slot : Slot} {futureReason epochReason reason : String} :
    voteTimeOutcome config store slot currentTimeMs futureReason epochReason ≠
      .ok (.reject reason) := by
  unfold voteTimeOutcome
  split
  · cases store.isFutureSlot config slot currentTimeMs with
    | error => simp [bind, Except.bind]
    | ok future =>
      cases future <;>
        cases store.isCurrentOrPreviousEpoch config (computeEpochAtSlot preset slot)
          currentTimeMs <;>
        simp [bind, Except.bind, pure, Except.pure, ignoreUnless, ValidationResult.andThenM] <;>
        split <;> simp
  · cases store.isWithinSlotRange config slot config.ATTESTATION_PROPAGATION_SLOT_RANGE
      currentTimeMs <;> simp [bind, Except.bind, pure, Except.pure, ignoreUnless] <;>
      split <;> simp

/-- The last checks of a vote: a wrong target rejects, and a block off the finalized chain ignores.

This holds once the two checkpoint blocks are computed. -/
theorem voteAncestryOutcome_eq {root targetBlock finalizedBlock : Root} {target : Checkpoint}
    (targetOf : store.getCheckpointBlock root target.epoch = .ok targetBlock)
    (finalizedOf : store.getCheckpointBlock root store.finalizedCheckpoint.epoch =
      .ok finalizedBlock) :
    voteAncestryOutcome store root target =
      .ok ((rejectUnless (targetBlock == target.root)
          "target block is not an ancestor of LMD vote block").andThen fun _ =>
        ignoreUnless (finalizedBlock == store.finalizedCheckpoint.root)
          "finalized checkpoint is not an ancestor of block") := by
  unfold voteAncestryOutcome
  simp only [targetOf, finalizedOf, bind, Except.bind, pure, Except.pure, rejectUnless_andThenM,
    rejectUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The first attester of a committee of one, whose bit is set, is its member. -/
theorem firstAttester_witness {member : ValidatorIndex} :
    firstAttester #[member] #[true] = some member := by
  simp [firstAttester]

/-- A committee with fewer than twice the target of aggregators has a modulus of 1.

So every selection proof selects its signer. -/
theorem isAggregator_of_small {size : Nat} {proof : BLSSignature} (small : size < 32) :
    isAggregator size proof = true := by
  have le : size.toUInt64 / TARGET_AGGREGATORS_PER_COMMITTEE ≤ 1 := by
    rw [UInt64.le_iff_toNat_le]
    simp [TARGET_AGGREGATORS_PER_COMMITTEE]
    omega
  have one : max 1 (size.toUInt64 / TARGET_AGGREGATORS_PER_COMMITTEE) = 1 := by
    simp only [Max.max]
    split
    · exact UInt64.le_antisymm le ‹_›
    · rfl
  simp [isAggregator, one]

/-- The check of the index in the data accepts exactly when the index is allowed at the fork. -/
@[simp] theorem dataIndexOutcome_eq_accept {index : CommitteeIndex}
    {zeroReason binaryReason : String} :
    dataIndexOutcome fork index zeroReason binaryReason = accept ↔
      isValidDataIndex fork index = true := by
  simp [dataIndexOutcome]

/-- The check of the index in the data never ignores. -/
@[simp] theorem dataIndexOutcome_ne_ignore {index : CommitteeIndex}
    {zeroReason binaryReason reason : String} :
    dataIndexOutcome fork index zeroReason binaryReason ≠ .ignore reason := by
  simp [dataIndexOutcome]

/-- From Gloas the index in the data of a vote is allowed exactly when it is 0 or 1. -/
theorem isValidDataIndex_of_gloas {index : CommitteeIndex} (gloas : .glamsterdam ≤ fork) :
    isValidDataIndex fork index = true ↔ index ≤ 1 := by
  simp [isValidDataIndex, gloas]

/-- Before Gloas the index in the data of a vote is allowed exactly when it is zero. -/
theorem isValidDataIndex_of_lt_gloas {index : CommitteeIndex} (early : ¬ .glamsterdam ≤ fork) :
    isValidDataIndex fork index = true ↔ index = 0 := by
  simp [isValidDataIndex, early]

/-- Before Gloas a vote sees no payload, so its payload checks accept. -/
theorem attestationPayloadOutcome_of_lt_gloas {data : AttestationData}
    (early : ¬ .glamsterdam ≤ fork) :
    attestationPayloadOutcome store statuses data = .ok accept := by
  simp [attestationPayloadOutcome, early, pure, Except.pure]

/-- Before Gloas the last checks of a vote are those of its ancestors. -/
theorem voteOutcome_of_lt_gloas {data : AttestationData} (early : ¬ .glamsterdam ≤ fork) :
    voteOutcome store statuses data =
      voteAncestryOutcome store data.beaconBlockRoot data.target := by
  unfold voteOutcome
  rw [attestationPayloadOutcome_of_lt_gloas early]
  cases voteAncestryOutcome store data.beaconBlockRoot data.target with
  | error e => rfl
  | ok outcome => cases outcome <;> rfl

/-- From Gloas the payload checks of a vote on a known block accept exactly in these cases.

A vote in the slot of its block says 0.

A vote that says 1 has its payload verified, with a status neither unvalidated nor invalid. -/
theorem attestationPayloadOutcome_eq_accept {data : AttestationData}
    {voted : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (known : store.block data.beaconBlockRoot = .ok voted) :
    attestationPayloadOutcome store statuses data = .ok accept ↔
      (voted.slot = data.slot → data.index = 0) ∧
        (data.index = 1 → store.isPayloadVerified gloas data.beaconBlockRoot = true ∧
          statuses.get data.beaconBlockRoot ≠ PAYLOAD_STATUS_NOT_VALIDATED ∧
          statuses.get data.beaconBlockRoot ≠ PAYLOAD_STATUS_INVALIDATED) := by
  unfold attestationPayloadOutcome
  simp only [gloas, dite_true, known, bind, Except.bind, rejectUnless_andThenM,
    ignoreUnless_andThenM, pure, Except.pure]
  by_cases same : voted.slot = data.slot <;> by_cases one : data.index = 1 <;>
    by_cases zero : data.index = 0 <;>
    by_cases verifiedRoot : store.isPayloadVerified gloas data.beaconBlockRoot = true <;>
    by_cases optimistic : statuses.get data.beaconBlockRoot = PAYLOAD_STATUS_NOT_VALIDATED <;>
    by_cases invalid : statuses.get data.beaconBlockRoot = PAYLOAD_STATUS_INVALIDATED <;>
    simp_all [ignoreUnless, rejectUnless, ValidationResult.andThen]

/-- From Gloas a vote whose payload checks pass, with an allowed index, passes the fork choice.

The fork choice checks the payload that the vote sees, on the same block. -/
theorem validatePayloadVote_of_attestationPayloadOutcome {attestation : Attestation preset fork}
    {voted : BeaconBlock preset fork} (gloas : .glamsterdam ≤ fork)
    (known : store.block attestation.data.beaconBlockRoot = .ok voted)
    (index : isValidDataIndex fork attestation.data.index = true)
    (accepted : attestationPayloadOutcome store statuses attestation.data = .ok accept) :
    store.validatePayloadVote gloas attestation voted = .ok () := by
  rw [isValidDataIndex_of_gloas gloas] at index
  obtain ⟨sameSlot, verified⟩ := (attestationPayloadOutcome_eq_accept gloas known).mp accepted
  unfold Store.validatePayloadVote
  have binary : ¬ (attestation.data.index ≠ 0 ∧ attestation.data.index ≠ 1) := by
    rintro ⟨zero, one⟩
    rw [UInt64.le_iff_toNat_le] at index
    have : attestation.data.index.toNat ≠ 0 := fun h => zero (UInt64.toNat_inj.mp h)
    have : attestation.data.index.toNat ≠ 1 := fun h => one (UInt64.toNat_inj.mp h)
    simp at index
    omega
  have notSame : ¬ (voted.slot = attestation.data.slot ∧ attestation.data.index ≠ 0) :=
    fun ⟨same, nonzero⟩ => nonzero (sameSlot same)
  simp only [binary, notSame, ite_false]
  by_cases one : attestation.data.index = 1
  · simp [one, (verified one).1, pure, Except.pure]
  · simp [one, pure, Except.pure]

/-! ## Single attestations, from Electra -/

/-- A single attestation whose attester has a valid one for its target epoch is ignored. -/
theorem validateSingleAttestation_of_seen {electra : .pectra ≤ fork}
    {attestation : SingleAttestation}
    (known : (attestation.data.target.epoch, attestation.attesterIndex) ∈
      seen.attestationValidatorEpochs) :
    validateSingleAttestation config checks seen store statuses electra attestation currentTimeMs
        subnetId =
      .ok (.ignore "already seen attestation for this epoch and validator") := by
  simp [validateSingleAttestation, dataIndexOutcome, known, pure, Except.pure]

/-- A valid single attestation records its key, so the same attestation is then ignored. -/
theorem validateSingleAttestation_recordAttestation {electra : .pectra ≤ fork}
    {attestation : SingleAttestation} :
    validateSingleAttestation config checks
        (seen.recordAttestation attestation.data.target.epoch attestation.attesterIndex) store
        statuses electra attestation currentTimeMs subnetId =
      .ok (.ignore "already seen attestation for this epoch and validator") :=
  validateSingleAttestation_of_seen (by simp [Seen.recordAttestation])

/-- From Gloas a single attestation whose data index is above 1 is rejected.

That check comes right after the check of the seen keys. -/
theorem validateSingleAttestation_of_gloas_index {electra : .pectra ≤ fork}
    {attestation : SingleAttestation} (gloas : .glamsterdam ≤ fork)
    (fresh : (attestation.data.target.epoch, attestation.attesterIndex) ∉
      seen.attestationValidatorEpochs)
    (large : 1 < attestation.data.index) :
    validateSingleAttestation config checks seen store statuses electra attestation currentTimeMs
        subnetId =
      .ok (.reject "attestation data index must be 0 or 1") := by
  have notSmall : ¬ attestation.data.index ≤ 1 := UInt64.not_le.mpr large
  simp [validateSingleAttestation, dataIndexOutcome, isValidDataIndex, gloas, fresh, notSmall,
    pure, Except.pure]

section Single

variable {electra : .pectra ≤ fork} {attestation : SingleAttestation}
  {state : BeaconState preset fork} {subnet : SubnetID} {time ancestry : ValidationResult}
  {committee : Array ValidatorIndex} {attester : Validator} {valid : Bool}

/-- The outcome of a single attestation is its chain of checks, in order.

This holds once the head state, the subnet, the committee and the signature are computed.

The checks of the clock and of the ancestors are computed too, and have their own lemmas. -/
theorem validateSingleAttestation_eq (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.committeeIndex = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.committeeIndex =
      .ok committee)
    (found : state.validators.data[attestation.attesterIndex.toNat]? = some attester)
    (signature : isValidSignatureAtEpoch config checks state DOMAIN_BEACON_ATTESTER
      attestation.data.target.epoch attestation.data attester.pubkey attestation.signature =
      .ok valid)
    (ancestryOf : voteOutcome store statuses attestation.data = .ok ancestry) :
    validateSingleAttestation config checks seen store statuses electra attestation currentTimeMs
        subnetId =
      .ok ((ignoreUnless (!seen.attestationValidatorEpochs.contains
          (attestation.data.target.epoch, attestation.attesterIndex))
          "already seen attestation for this epoch and validator").andThen fun _ =>
        (dataIndexOutcome fork attestation.data.index "attestation data index is non-zero"
          "attestation data index must be 0 or 1").andThen fun _ =>
        (votedBlockOutcome store attestation.data.beaconBlockRoot).andThen fun _ =>
        (rejectUnless (decide (attestation.committeeIndex <
          getCommitteeCountPerSlot state attestation.data.target.epoch))
          "committee index out of range").andThen fun _ =>
        (rejectUnless (subnet == subnetId) "attestation is for wrong subnet").andThen fun _ =>
        time.andThen fun _ =>
        (rejectUnless (attestation.data.target.epoch ==
          computeEpochAtSlot preset attestation.data.slot)
          "attestation epoch does not match target epoch").andThen fun _ =>
        (rejectUnless (committee.contains attestation.attesterIndex)
          "attester is not a member of the committee").andThen fun _ =>
        (rejectUnless valid "invalid attestation signature").andThen fun _ =>
        ancestry) := by
  unfold validateSingleAttestation
  simp only [dataIndexOutcome, head, subnetOf, clock, committeeOf, found, signature, ancestryOf,
    bind, Except.bind, pure, Except.pure, Except.mapError, ignoreUnless_andThenM,
    ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]
  cases votedBlockOutcome store attestation.data.beaconBlockRoot <;> cases time <;>
    simp only [ValidationResult.andThenM, ValidationResult.andThen, pure, Except.pure,
      apply_ite (Except.ok (ε := ForkChoiceError))]

/-- A single attestation is valid exactly when every check passes.

This holds once its inputs are computed. -/
theorem validateSingleAttestation_eq_accept (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.committeeIndex = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.committeeIndex =
      .ok committee)
    (found : state.validators.data[attestation.attesterIndex.toNat]? = some attester)
    (signature : isValidSignatureAtEpoch config checks state DOMAIN_BEACON_ATTESTER
      attestation.data.target.epoch attestation.data attester.pubkey attestation.signature =
      .ok valid)
    (ancestryOf : voteOutcome store statuses attestation.data = .ok ancestry) :
    validateSingleAttestation config checks seen store statuses electra attestation currentTimeMs
        subnetId =
        .ok accept ↔
      (attestation.data.target.epoch, attestation.attesterIndex) ∉
        seen.attestationValidatorEpochs ∧ isValidDataIndex fork attestation.data.index = true ∧
        attestation.data.beaconBlockRoot ∈ store.blocks ∧
        attestation.data.beaconBlockRoot ∈ store.blockStates ∧
        attestation.committeeIndex <
          getCommitteeCountPerSlot state attestation.data.target.epoch ∧
        subnet = subnetId ∧ time = accept ∧
        attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot ∧
        attestation.attesterIndex ∈ committee ∧ valid = true ∧ ancestry = accept := by
  rw [validateSingleAttestation_eq head subnetOf clock committeeOf found signature
    ancestryOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept,
    votedBlockOutcome_eq_accept]
  simp
  grind

/-- Once its inputs are computed, a single attestation is ignored in four cases.

Its attester has a valid one for its target epoch, or the block it votes for is unknown.

Or the clock ignores it, or the finalized checkpoint is not an ancestor of its block.

Each case after the first needs the checks before it to pass. -/
theorem validateSingleAttestation_ignored (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.committeeIndex = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.committeeIndex =
      .ok committee)
    (found : state.validators.data[attestation.attesterIndex.toNat]? = some attester)
    (signature : isValidSignatureAtEpoch config checks state DOMAIN_BEACON_ATTESTER
      attestation.data.target.epoch attestation.data attester.pubkey attestation.signature =
      .ok valid)
    (ancestryOf : voteOutcome store statuses attestation.data = .ok ancestry) :
    (∃ reason, validateSingleAttestation config checks seen store statuses electra attestation
        currentTimeMs subnetId = .ok (.ignore reason)) ↔
      (attestation.data.target.epoch, attestation.attesterIndex) ∈
          seen.attestationValidatorEpochs ∨
        isValidDataIndex fork attestation.data.index = true ∧
          (attestation.data.beaconBlockRoot ∉ store.blocks ∨
          attestation.data.beaconBlockRoot ∈ store.blocks ∧
          attestation.data.beaconBlockRoot ∈ store.blockStates ∧
          attestation.committeeIndex <
            getCommitteeCountPerSlot state attestation.data.target.epoch ∧
          subnet = subnetId ∧ ((∃ reason, time = .ignore reason) ∨ time = accept ∧
            attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot ∧
            attestation.attesterIndex ∈ committee ∧ valid = true ∧
            ∃ reason, ancestry = .ignore reason)) := by
  rw [validateSingleAttestation_eq head subnetOf clock committeeOf found signature
    ancestryOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept, votedBlockOutcome_eq_accept,
    votedBlockOutcome_eq_ignore]
  simp
  grind

end Single

/-! ## Attestations, before Electra -/

section Attestations

variable {early : fork < .pectra} {attestation : Attestation preset fork}
  {state : BeaconState preset fork} {subnet : SubnetID} {time ancestry : ValidationResult}
  {committee : Array ValidatorIndex} {attester : ValidatorIndex}
  {indexed : IndexedAttestation preset fork} {valid : Bool}

/-- The attester that a valid attestation records is the one that its checks read.

This holds once the head state and the committee are computed. -/
theorem beaconAttestationAttester_eq (head : store.headState config = .ok state)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.data.index =
      .ok committee) :
    beaconAttestationAttester config store attestation =
      .ok (firstAttester committee attestation.aggregationBits.bits) := by
  simp [beaconAttestationAttester, head, committeeOf, bind, Except.bind, pure, Except.pure,
    Except.mapError]

/-- The outcome of an attestation is its chain of checks, in order.

This holds once the head state, the subnet and the committee are computed.

The attester and the signature must be computed too.

The checks of the clock and of the ancestors are computed too, and have their own lemmas. -/
theorem validateBeaconAttestation_eq (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.data.index = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.data.index =
      .ok committee)
    (attesterOf : firstAttester committee attestation.aggregationBits.bits = some attester)
    (indexedOf : getIndexedAttestation state attestation = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteAncestryOutcome store attestation.data.beaconBlockRoot
      attestation.data.target = .ok ancestry) :
    validateBeaconAttestation config checks seen store early attestation currentTimeMs subnetId =
      .ok ((votedBlockOutcome store attestation.data.beaconBlockRoot).andThen fun _ =>
        (rejectUnless (decide (attestation.data.index <
          getCommitteeCountPerSlot state attestation.data.target.epoch))
          "committee index out of range").andThen fun _ =>
        (rejectUnless (subnet == subnetId) "attestation is for wrong subnet").andThen fun _ =>
        time.andThen fun _ =>
        (rejectUnless (attestation.data.target.epoch ==
          computeEpochAtSlot preset attestation.data.slot)
          "attestation epoch does not match target epoch").andThen fun _ =>
        (rejectUnless (attestation.aggregationBits.bits.count true == 1)
          "attestation is not unaggregated").andThen fun _ =>
        (rejectUnless (attestation.aggregationBits.bits.size == committee.size)
          "aggregation bits length does not match committee size").andThen fun _ =>
        (ignoreUnless (!seen.attestationValidatorEpochs.contains
          (attestation.data.target.epoch, attester))
          "already seen attestation for this epoch and validator").andThen fun _ =>
        (rejectUnless valid "invalid attestation signature").andThen fun _ =>
        ancestry) := by
  unfold validateBeaconAttestation
  simp only [head, subnetOf, clock, committeeOf, attesterOf, indexedOf, signature, ancestryOf,
    bind, Except.bind, pure, Except.pure, Except.mapError, ignoreUnless_andThenM,
    ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen]
  cases votedBlockOutcome store attestation.data.beaconBlockRoot <;> cases time <;>
    simp only [ValidationResult.andThenM, ValidationResult.andThen, pure, Except.pure,
      apply_ite (Except.ok (ε := ForkChoiceError))]

/-- An attestation is valid exactly when every check passes.

It must set one bit, and have one bit for each member of the committee.

This holds once its inputs are computed. -/
theorem validateBeaconAttestation_eq_accept (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.data.index = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.data.index =
      .ok committee)
    (attesterOf : firstAttester committee attestation.aggregationBits.bits = some attester)
    (indexedOf : getIndexedAttestation state attestation = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteAncestryOutcome store attestation.data.beaconBlockRoot
      attestation.data.target = .ok ancestry) :
    validateBeaconAttestation config checks seen store early attestation currentTimeMs subnetId =
        .ok accept ↔
      attestation.data.beaconBlockRoot ∈ store.blocks ∧
        attestation.data.beaconBlockRoot ∈ store.blockStates ∧
        attestation.data.index < getCommitteeCountPerSlot state attestation.data.target.epoch ∧
        subnet = subnetId ∧ time = accept ∧
        attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot ∧
        attestation.aggregationBits.bits.count true = 1 ∧
        attestation.aggregationBits.bits.size = committee.size ∧
        (attestation.data.target.epoch, attester) ∉ seen.attestationValidatorEpochs ∧
        valid = true ∧ ancestry = accept := by
  rw [validateBeaconAttestation_eq head subnetOf clock committeeOf attesterOf indexedOf signature
    ancestryOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept,
    votedBlockOutcome_eq_accept]
  simp
  grind

/-- Once its inputs are computed, an attestation is ignored in four cases.

The block it votes for is unknown, or the clock ignores it.

Or its attester has a valid one for its target epoch.

Or the finalized checkpoint is not an ancestor of its block.

Each case needs the checks before it to pass. -/
theorem validateBeaconAttestation_ignored (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.data.index = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.data.index =
      .ok committee)
    (attesterOf : firstAttester committee attestation.aggregationBits.bits = some attester)
    (indexedOf : getIndexedAttestation state attestation = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteAncestryOutcome store attestation.data.beaconBlockRoot
      attestation.data.target = .ok ancestry) :
    (∃ reason, validateBeaconAttestation config checks seen store early attestation
        currentTimeMs subnetId = .ok (.ignore reason)) ↔
      attestation.data.beaconBlockRoot ∉ store.blocks ∨
        attestation.data.beaconBlockRoot ∈ store.blocks ∧
        attestation.data.beaconBlockRoot ∈ store.blockStates ∧
        attestation.data.index < getCommitteeCountPerSlot state attestation.data.target.epoch ∧
        subnet = subnetId ∧ ((∃ reason, time = .ignore reason) ∨ time = accept ∧
          attestation.data.target.epoch = computeEpochAtSlot preset attestation.data.slot ∧
          attestation.aggregationBits.bits.count true = 1 ∧
          attestation.aggregationBits.bits.size = committee.size ∧
          ((attestation.data.target.epoch, attester) ∈ seen.attestationValidatorEpochs ∨
            valid = true ∧ ∃ reason, ancestry = .ignore reason)) := by
  rw [validateBeaconAttestation_eq head subnetOf clock committeeOf attesterOf indexedOf signature
    ancestryOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept, votedBlockOutcome_eq_accept,
    votedBlockOutcome_eq_ignore]
  simp
  grind

/-- A valid attestation records its key, so the same attestation is then ignored.

This holds once its inputs are computed, which do not read the keys. -/
theorem validateBeaconAttestation_recordAttestation (head : store.headState config = .ok state)
    (subnetOf : computeSubnetForAttestation preset config
      (getCommitteeCountPerSlot state attestation.data.target.epoch) attestation.data.slot
      attestation.data.index = .ok subnet)
    (clock : voteTimeOutcome config store attestation.data.slot currentTimeMs
      "attestation slot is from a future slot"
      "attestation epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state attestation.data.slot attestation.data.index =
      .ok committee)
    (attesterOf : firstAttester committee attestation.aggregationBits.bits = some attester)
    (indexedOf : getIndexedAttestation state attestation = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteAncestryOutcome store attestation.data.beaconBlockRoot
      attestation.data.target = .ok ancestry)
    (accepted : validateBeaconAttestation config checks seen store early attestation
      currentTimeMs subnetId = .ok accept) :
    validateBeaconAttestation config checks
        (seen.recordAttestation attestation.data.target.epoch attester) store early attestation
        currentTimeMs subnetId =
      .ok (.ignore "already seen attestation for this epoch and validator") := by
  rw [validateBeaconAttestation_eq_accept head subnetOf clock committeeOf attesterOf indexedOf
    signature ancestryOf] at accepted
  rw [validateBeaconAttestation_eq head subnetOf clock committeeOf attesterOf indexedOf signature
    ancestryOf]
  obtain ⟨known, hasState, inRange, onSubnet, onTime, inEpoch, one, size, -, -, -⟩ := accepted
  have epochMatches : (attestation.data.target.epoch ==
      computeEpochAtSlot preset attestation.data.slot) = true := beq_iff_eq.mpr inEpoch
  simp [votedBlockOutcome, known, hasState, inRange, onSubnet, onTime, epochMatches, one, size,
    Seen.recordAttestation]

end Attestations

/-! ## Aggregates -/

section Aggregates

variable {signed : SignedAggregateAndProof preset fork} {index : CommitteeIndex} {root : Root}
  {state : BeaconState preset fork} {time ancestry : ValidationResult}
  {committee : Array ValidatorIndex} {participants : List ValidatorIndex}
  {aggregator : Validator} {selected byAggregator valid : Bool}
  {indexed : IndexedAttestation preset fork}

/-- Before Electra the committee of an aggregate is the index in its data. -/
theorem validateAggregateAndProof_of_lt_electra (early : ¬ .pectra ≤ fork) :
    validateAggregateAndProof config checks seen store statuses signed currentTimeMs =
      validateAggregateInCommittee config checks seen store statuses signed
        signed.message.aggregate.data.index currentTimeMs := by
  simp [validateAggregateAndProof, early]

/-- From Electra an aggregate whose data has a nonzero index is rejected first. -/
theorem validateAggregateAndProof_of_index_ne_zero (gloas : ¬ .glamsterdam ≤ fork)
    (electra : .pectra ≤ fork) (nonzero : signed.message.aggregate.data.index ≠ 0) :
    validateAggregateAndProof config checks seen store statuses signed currentTimeMs =
      .ok (.reject "aggregate data index is non-zero") := by
  simp [validateAggregateAndProof, dataIndexOutcome, isValidDataIndex, gloas, electra, nonzero,
    pure, Except.pure]

/-- From Gloas an aggregate whose data index is above 1 is rejected first. -/
theorem validateAggregateAndProof_of_gloas_index (gloas : .glamsterdam ≤ fork)
    (large : 1 < signed.message.aggregate.data.index) :
    validateAggregateAndProof config checks seen store statuses signed currentTimeMs =
      .ok (.reject "aggregate data index must be 0 or 1") := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) gloas
  have notSmall : ¬ signed.message.aggregate.data.index ≤ 1 := UInt64.not_le.mpr large
  simp [validateAggregateAndProof, dataIndexOutcome, isValidDataIndex, gloas, electra, notSmall,
    pure, Except.pure]

/-- From Electra an aggregate whose committee bits do not name exactly one committee is rejected.

That check comes right after the check of the index in its data. -/
theorem validateAggregateAndProof_of_not_one_committee (electra : .pectra ≤ fork)
    (validIndex : isValidDataIndex fork signed.message.aggregate.data.index = true)
    (notOne : ∀ index,
      getCommitteeIndices (signed.message.aggregate.committeeBits electra) ≠ [index]) :
    validateAggregateAndProof config checks seen store statuses signed currentTimeMs =
      .ok (.reject "aggregate committee bits must specify exactly one committee") := by
  simp only [validateAggregateAndProof, dataIndexOutcome, electra, validIndex, dite_true,
    rejectUnless_andThenM, ite_true]
  first
    | rfl
    | split <;> first | exact absurd ‹_› (notOne _) | rfl

/-- From Electra the committee of an aggregate is the one that its committee bits name.

This holds when the index in its data is zero. -/
theorem validateAggregateAndProof_of_electra (electra : .pectra ≤ fork)
    (validIndex : isValidDataIndex fork signed.message.aggregate.data.index = true)
    (one : getCommitteeIndices (signed.message.aggregate.committeeBits electra) = [index]) :
    validateAggregateAndProof config checks seen store statuses signed currentTimeMs =
      validateAggregateInCommittee config checks seen store statuses signed index
        currentTimeMs := by
  simp [validateAggregateAndProof, dataIndexOutcome, electra, validIndex, one]

/-- The checks of an aggregate in its committee equal those that call the accessors.

There the committee, the participants and the indexed form are each read from the state.

The two sides fail with the same error too. -/
theorem validateAggregateInCommittee_eq_accessors :
    validateAggregateInCommittee config checks seen store statuses signed index currentTimeMs =
      (do
        let proof := signed.message
        let aggregate := proof.aggregate
        let data := aggregate.data
        let bits := aggregate.aggregationBits.bits
        let root ← (Serialization.Ssz.SszType.hashTreeRoot data).mapError .ssz
        let seenBits := seen.aggregateBitsFor (aggregateKey fork root index)
        (ignoreUnless (!isNonStrictSuperset seenBits bits.toList)
          "already seen aggregate for this data").andThenM fun _ =>
        (ignoreUnless (!seen.aggregatorEpochs.contains (data.target.epoch, proof.aggregatorIndex))
          "already seen aggregate for this epoch and aggregator").andThenM fun _ =>
        (votedBlockOutcome store data.beaconBlockRoot).andThenM fun _ => do
        let state ← store.headState config
        (rejectUnless (index < getCommitteeCountPerSlot state data.target.epoch)
          "committee index out of range").andThenM fun _ => do
        (← voteTimeOutcome config store data.slot currentTimeMs
          "aggregate slot is from a future slot"
          "aggregate epoch is not current or previous epoch").andThenM fun _ =>
        (rejectUnless (data.target.epoch == computeEpochAtSlot preset data.slot)
          "attestation epoch does not match target epoch").andThenM fun _ => do
        let committee ← (getBeaconCommittee state data.slot index).mapError .accessor
        (rejectUnless (bits.size == committee.size)
          "aggregation bits length does not match committee size").andThenM fun _ => do
        let participants ← (getAttestingIndices state aggregate).mapError .accessor
        (rejectUnless (!participants.isEmpty) "aggregate has no participants").andThenM fun _ =>
        (rejectUnless (isAggregator committee.size proof.selectionProof)
          "validator is not selected as aggregator").andThenM fun _ =>
        (rejectUnless (committee.contains proof.aggregatorIndex)
          "aggregator is not a member of the committee").andThenM fun _ => do
        let some aggregator := state.validators.data[proof.aggregatorIndex.toNat]?
          | throw (.accessor (.indexOutOfRange proof.aggregatorIndex))
        let selected ← isValidSignatureAtEpoch config checks state DOMAIN_SELECTION_PROOF
          data.target.epoch data.slot aggregator.pubkey proof.selectionProof
        (rejectUnless selected "invalid selection proof signature").andThenM fun _ => do
        let signedByAggregator ← isValidSignatureAtEpoch config checks state
          DOMAIN_AGGREGATE_AND_PROOF data.target.epoch proof aggregator.pubkey signed.signature
        (rejectUnless signedByAggregator "invalid aggregator signature").andThenM fun _ => do
        let indexed ← (getIndexedAttestation state aggregate).mapError .accessor
        let valid ← (isValidIndexedAttestation config checks state indexed).mapError .transition
        (rejectUnless valid "invalid aggregate signature").andThenM fun _ =>
        voteOutcome store statuses data) := by
  simp only [validateAggregateInCommittee, getBeaconCommittee, getIndexedAttestation]
  cases store.headState config with
  | error e => simp only [bind, Except.bind]
  | ok state =>
    simp only [bind, Except.bind]
    cases shuffleOk : attesterShuffle state
        (computeEpochAtSlot preset signed.message.aggregate.data.slot) with
    -- Both sides read the shuffle at the committee, so its failure is the same error on both.
    | error e => simp only [Except.mapError]
    | ok pair =>
      obtain ⟨active, shuffled⟩ := pair
      -- With this shuffle, each read of the participants on the right equals the one on the left.
      simp only [Except.mapError, getAttestingIndices_of_attesterShuffle shuffleOk]
      cases attestingIndicesOf signed.message.aggregate
          (getCommitteeCountPerSlot state
            (computeEpochAtSlot preset signed.message.aggregate.data.slot)) active shuffled <;>
        rfl

/-- An aggregate whose bits a valid aggregate for its data and committee covers is ignored.

This needs only the root of its data. -/
theorem validateAggregateInCommittee_of_covered
    (rootOf : Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (covered : isNonStrictSuperset (seen.aggregateBitsFor (aggregateKey fork root index))
      signed.message.aggregate.aggregationBits.bits.toList = true) :
    validateAggregateInCommittee config checks seen store statuses signed index currentTimeMs =
      .ok (.ignore "already seen aggregate for this data") := by
  simp [validateAggregateInCommittee, rootOf, covered, bind, Except.bind, Except.mapError, pure,
    Except.pure]

/-- Before Electra the key of an aggregate holds the committee 0. -/
theorem aggregateKeyCommittee_of_lt_electra {aggregate : Attestation preset fork}
    (early : ¬ .pectra ≤ fork) : aggregateKeyCommittee aggregate = 0 := by
  simp [aggregateKeyCommittee, early]

/-- From Electra the key of an aggregate that names one committee holds that committee. -/
theorem aggregateKeyCommittee_of_electra {aggregate : Attestation preset fork}
    (electra : .pectra ≤ fork)
    (one : getCommitteeIndices (aggregate.committeeBits electra) = [index]) :
    aggregateKeyCommittee aggregate = index := by
  simp [aggregateKeyCommittee, electra, one]

/-- A valid aggregate records its bits, so the same aggregate in its committee is then ignored.

The key that it records holds the committee of the check, as the two lemmas before show. -/
theorem validateAggregateInCommittee_recordAggregateAndProof
    (rootOf : Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (keyOf : aggregateKeyCommittee signed.message.aggregate =
      if .pectra ≤ fork then index else 0) :
    validateAggregateInCommittee config checks (seen.recordAggregateAndProof signed root) store
        statuses signed index currentTimeMs =
      .ok (.ignore "already seen aggregate for this data") := by
  apply validateAggregateInCommittee_of_covered rootOf
  apply isNonStrictSuperset_of_mem
  simp [Seen.aggregateBitsFor, Seen.recordAggregateAndProof, aggregateKey, keyOf]

/-- The outcome of an aggregate in its committee is its chain of checks, in order.

This holds once the root of its data, the head state and the committee are computed.

The participants and the signatures must be computed too.

The checks of the clock and of the ancestors are computed too, and have their own lemmas. -/
theorem validateAggregateInCommittee_eq
    (rootOf : Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (head : store.headState config = .ok state)
    (clock : voteTimeOutcome config store signed.message.aggregate.data.slot currentTimeMs
      "aggregate slot is from a future slot"
      "aggregate epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state signed.message.aggregate.data.slot index =
      .ok committee)
    (participantsOf : getAttestingIndices state signed.message.aggregate = .ok participants)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (selectedOf : isValidSignatureAtEpoch config checks state DOMAIN_SELECTION_PROOF
      signed.message.aggregate.data.target.epoch signed.message.aggregate.data.slot
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (signedOf : isValidSignatureAtEpoch config checks state DOMAIN_AGGREGATE_AND_PROOF
      signed.message.aggregate.data.target.epoch signed.message aggregator.pubkey
      signed.signature = .ok byAggregator)
    (indexedOf : getIndexedAttestation state signed.message.aggregate = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteOutcome store statuses signed.message.aggregate.data = .ok ancestry) :
    validateAggregateInCommittee config checks seen store statuses signed index currentTimeMs =
      .ok ((ignoreUnless
          (!isNonStrictSuperset (seen.aggregateBitsFor (aggregateKey fork root index))
            signed.message.aggregate.aggregationBits.bits.toList)
          "already seen aggregate for this data").andThen fun _ =>
        (ignoreUnless (!seen.aggregatorEpochs.contains
          (signed.message.aggregate.data.target.epoch, signed.message.aggregatorIndex))
          "already seen aggregate for this epoch and aggregator").andThen fun _ =>
        (votedBlockOutcome store signed.message.aggregate.data.beaconBlockRoot).andThen fun _ =>
        (rejectUnless (decide (index <
          getCommitteeCountPerSlot state signed.message.aggregate.data.target.epoch))
          "committee index out of range").andThen fun _ =>
        time.andThen fun _ =>
        (rejectUnless (signed.message.aggregate.data.target.epoch ==
          computeEpochAtSlot preset signed.message.aggregate.data.slot)
          "attestation epoch does not match target epoch").andThen fun _ =>
        (rejectUnless (signed.message.aggregate.aggregationBits.bits.size == committee.size)
          "aggregation bits length does not match committee size").andThen fun _ =>
        (rejectUnless (!participants.isEmpty) "aggregate has no participants").andThen fun _ =>
        (rejectUnless (isAggregator committee.size signed.message.selectionProof)
          "validator is not selected as aggregator").andThen fun _ =>
        (rejectUnless (committee.contains signed.message.aggregatorIndex)
          "aggregator is not a member of the committee").andThen fun _ =>
        (rejectUnless selected "invalid selection proof signature").andThen fun _ =>
        (rejectUnless byAggregator "invalid aggregator signature").andThen fun _ =>
        (rejectUnless valid "invalid aggregate signature").andThen fun _ =>
        ancestry) := by
  rw [validateAggregateInCommittee_eq_accessors]
  simp only [rootOf, head, clock, committeeOf, participantsOf, found, selectedOf, signedOf,
    indexedOf, signature, ancestryOf, bind, Except.bind, pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]
  cases votedBlockOutcome store signed.message.aggregate.data.beaconBlockRoot <;> cases time <;>
    simp only [ValidationResult.andThenM, ValidationResult.andThen, pure, Except.pure,
      apply_ite (Except.ok (ε := ForkChoiceError))]

/-- An aggregate in its committee is valid exactly when every check passes.

This holds once its inputs are computed. -/
theorem validateAggregateInCommittee_eq_accept
    (rootOf : Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (head : store.headState config = .ok state)
    (clock : voteTimeOutcome config store signed.message.aggregate.data.slot currentTimeMs
      "aggregate slot is from a future slot"
      "aggregate epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state signed.message.aggregate.data.slot index =
      .ok committee)
    (participantsOf : getAttestingIndices state signed.message.aggregate = .ok participants)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (selectedOf : isValidSignatureAtEpoch config checks state DOMAIN_SELECTION_PROOF
      signed.message.aggregate.data.target.epoch signed.message.aggregate.data.slot
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (signedOf : isValidSignatureAtEpoch config checks state DOMAIN_AGGREGATE_AND_PROOF
      signed.message.aggregate.data.target.epoch signed.message aggregator.pubkey
      signed.signature = .ok byAggregator)
    (indexedOf : getIndexedAttestation state signed.message.aggregate = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteOutcome store statuses signed.message.aggregate.data = .ok ancestry) :
    validateAggregateInCommittee config checks seen store statuses signed index currentTimeMs =
        .ok accept ↔
      isNonStrictSuperset (seen.aggregateBitsFor (aggregateKey fork root index))
          signed.message.aggregate.aggregationBits.bits.toList = false ∧
        (signed.message.aggregate.data.target.epoch, signed.message.aggregatorIndex) ∉
          seen.aggregatorEpochs ∧
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blocks ∧
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blockStates ∧
        index < getCommitteeCountPerSlot state signed.message.aggregate.data.target.epoch ∧
        time = accept ∧
        signed.message.aggregate.data.target.epoch =
          computeEpochAtSlot preset signed.message.aggregate.data.slot ∧
        signed.message.aggregate.aggregationBits.bits.size = committee.size ∧
        participants ≠ [] ∧ isAggregator committee.size signed.message.selectionProof = true ∧
        signed.message.aggregatorIndex ∈ committee ∧ selected = true ∧ byAggregator = true ∧
        valid = true ∧ ancestry = accept := by
  rw [validateAggregateInCommittee_eq rootOf head clock committeeOf participantsOf found
    selectedOf signedOf indexedOf signature ancestryOf]
  simp only [Except.ok.injEq, andThen_eq_accept, ignoreUnless_eq_accept, rejectUnless_eq_accept,
    votedBlockOutcome_eq_accept]
  simp
  grind

/-- Once its inputs are computed, an aggregate in its committee is ignored in five cases.

A valid aggregate covers its bits, or its aggregator has a valid one for its target epoch.

Or the block it votes for is unknown, or the clock ignores it.

Or the finalized checkpoint is not an ancestor of its block.

Each case needs the checks before it to pass. -/
theorem validateAggregateInCommittee_ignored
    (rootOf : Serialization.Ssz.SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (head : store.headState config = .ok state)
    (clock : voteTimeOutcome config store signed.message.aggregate.data.slot currentTimeMs
      "aggregate slot is from a future slot"
      "aggregate epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state signed.message.aggregate.data.slot index =
      .ok committee)
    (participantsOf : getAttestingIndices state signed.message.aggregate = .ok participants)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (selectedOf : isValidSignatureAtEpoch config checks state DOMAIN_SELECTION_PROOF
      signed.message.aggregate.data.target.epoch signed.message.aggregate.data.slot
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (signedOf : isValidSignatureAtEpoch config checks state DOMAIN_AGGREGATE_AND_PROOF
      signed.message.aggregate.data.target.epoch signed.message aggregator.pubkey
      signed.signature = .ok byAggregator)
    (indexedOf : getIndexedAttestation state signed.message.aggregate = .ok indexed)
    (signature : isValidIndexedAttestation config checks state indexed = .ok valid)
    (ancestryOf : voteOutcome store statuses signed.message.aggregate.data = .ok ancestry) :
    (∃ reason, validateAggregateInCommittee config checks seen store statuses signed index
        currentTimeMs = .ok (.ignore reason)) ↔
      isNonStrictSuperset (seen.aggregateBitsFor (aggregateKey fork root index))
          signed.message.aggregate.aggregationBits.bits.toList = true ∨
        (signed.message.aggregate.data.target.epoch, signed.message.aggregatorIndex) ∈
          seen.aggregatorEpochs ∨
        signed.message.aggregate.data.beaconBlockRoot ∉ store.blocks ∨
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blockStates ∧
        index < getCommitteeCountPerSlot state signed.message.aggregate.data.target.epoch ∧
        ((∃ reason, time = .ignore reason) ∨ time = accept ∧
          signed.message.aggregate.data.target.epoch =
            computeEpochAtSlot preset signed.message.aggregate.data.slot ∧
          signed.message.aggregate.aggregationBits.bits.size = committee.size ∧
          participants ≠ [] ∧ isAggregator committee.size signed.message.selectionProof = true ∧
          signed.message.aggregatorIndex ∈ committee ∧ selected = true ∧ byAggregator = true ∧
          valid = true ∧ ∃ reason, ancestry = .ignore reason) := by
  rw [validateAggregateInCommittee_eq rootOf head clock committeeOf participantsOf found
    selectedOf signedOf indexedOf signature ancestryOf]
  simp only [Except.ok.injEq, andThen_eq_ignore, ignoreUnless_eq_ignore, rejectUnless_ne_ignore,
    ignoreUnless_eq_accept, rejectUnless_eq_accept, votedBlockOutcome_eq_accept,
    votedBlockOutcome_eq_ignore]
  cases time <;> cases ancestry <;> simp <;> grind

end Aggregates

end EthLib.Consensus

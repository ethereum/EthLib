module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Gossip.SyncCommittee
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: the outcomes of the sync committee topics

Each topic checks a message in a fixed order, so its outcome is a chain of checks.

Once the clock, the head state, the committee and the signatures are computed, the outcome is fixed.

It is then that chain, so it follows which messages each topic accepts and which it ignores.

A valid message records its keys, and the same message is then ignored.

A fresh node has seen no bits, and in the minimal preset every selection proof selects.

So the checks of the seen bits and of the selection can pass, as the iffs need for an accept.

The keys a topic checks come from the next committee of a state when the next slot starts a period.

Otherwise they come from its current committee.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Networking.Gossip Networking.Gossip.ValidationResult

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {seen : Seen} {store : Store preset fork} {currentTimeMs : UInt64}
  {state : BeaconState preset fork} {altair : .altair ≤ fork}

/-! ## Helpers -/

/-- No earlier bits cover new bits when there are none. -/
@[simp] theorem isNonStrictSuperset_nil {bits : List Bool} : isNonStrictSuperset [] bits = false :=
  rfl

/-- Earlier bits that hold the new bits cover them. -/
theorem isNonStrictSuperset_of_mem {seenBits : List (List Bool)} {bits : List Bool}
    (mem : bits ∈ seenBits) : isNonStrictSuperset seenBits bits = true := by
  simp only [isNonStrictSuperset, List.any_eq_true]
  refine ⟨bits, mem, ?_⟩
  simp [List.all_eq_true, List.mem_iff_getElem]

/-- A selection proof selects its signer when the modulus of the selection is 1.

That is the case when a subcommittee has fewer than twice the aggregator target in members. -/
theorem isSyncCommitteeAggregator_of_small {signature : BLSSignature}
    (small : preset.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT /
      TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE ≤ 1) :
    isSyncCommitteeAggregator preset signature = true := by
  have one : max 1 (preset.SYNC_COMMITTEE_SIZE / SYNC_COMMITTEE_SUBNET_COUNT /
      TARGET_AGGREGATORS_PER_SYNC_SUBCOMMITTEE) = 1 := by
    rw [UInt64.max_def]
    split
    · exact UInt64.le_antisymm small ‹_›
    · rfl
  simp [isSyncCommitteeAggregator, one, UInt64.mod_one]

/-- In the minimal preset, every selection proof selects its signer. -/
theorem isSyncCommitteeAggregator_minimal {signature : BLSSignature} :
    isSyncCommitteeAggregator Preset.minimal signature = true :=
  isSyncCommitteeAggregator_of_small (by decide)

/-- A key holds a subnet exactly when one of its seats falls in the subcommittee of that subnet. -/
theorem mem_syncSubnetsOfPubkey {committee : SyncCommittee preset} {pubkey : BLSPubkey}
    {subnet : UInt64} :
    subnet ∈ syncSubnetsOfPubkey committee pubkey ↔
      ∃ position, committee.pubkeys.toList[position]? = some pubkey ∧
        (position / syncSubcommitteeSize preset).toUInt64 = subnet := by
  simp only [syncSubnetsOfPubkey, List.mem_eraseDups, List.mem_filterMap,
    List.mem_zipIdx_iff_getElem?, Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨⟨key, position⟩, found, rfl, rfl⟩
    exact ⟨position, by simpa using found, rfl⟩
  · rintro ⟨position, found, rfl⟩
    exact ⟨(pubkey, position), by simpa using found, rfl, rfl⟩

/-! ## The committee of the next slot -/

/-- A slot and the slot after it share a period exactly when the slot after does not start one.

A period is the slots of a fixed number of epochs. -/
private theorem period_eq_iff {slot : Slot} (fits : slot.toNat + 1 < 2 ^ 64) :
    computeSyncCommitteePeriod preset (computeEpochAtSlot preset slot) =
        computeSyncCommitteePeriodAtSlot preset (slot + 1) ↔
      (slot.toNat + 1) %
        (preset.SLOTS_PER_EPOCH.toNat * preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) ≠ 0 := by
  simp only [computeSyncCommitteePeriodAtSlot, computeSyncCommitteePeriod, computeEpochAtSlot,
    ← UInt64.toNat_inj, UInt64.toNat_div, Uint64.toNat_add_of_lt (a := slot) (b := 1) fits,
    UInt64.toNat_one, Nat.div_div_eq_div_mul]
  generalize preset.SLOTS_PER_EPOCH.toNat * preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat = length
  rcases Nat.eq_zero_or_pos length with zero | pos
  · simp [zero]
  · rw [Nat.succ_div, Ne, ← Nat.dvd_iff_mod_eq_zero]
    split <;> simp_all

/-- The sync committee of the slot after a state.

When that slot starts a period, it is the next committee of the state.

Otherwise it is the current committee of the state.

A period is the slots of a fixed number of epochs.

It fails with an overflow when the slot of the state is the largest 64-bit integer. -/
theorem syncCommitteeAtNextSlot_eq :
    syncCommitteeAtNextSlot state altair =
      if state.slot.toNat + 1 < 2 ^ 64 then
        .ok (if (state.slot.toNat + 1) %
            (preset.SLOTS_PER_EPOCH.toNat * preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) = 0
          then (state.nextSyncCommittee altair).value
          else (state.currentSyncCommittee altair).value)
      else .error .overflow := by
  unfold syncCommitteeAtNextSlot
  split
  · rename_i fits
    rw [addChecked_of_lt fits]
    simp only [getCurrentEpoch, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      beq_iff_eq, period_eq_iff fits]
    split <;> simp_all
  · rename_i over
    simp [addChecked, over, bind, Except.bind]

/-- The keys of a subcommittee whose index is below the number of subnets.

They are its slice of the sync committee of the slot after the state.

They fail exactly when that committee does. -/
theorem getSyncSubcommitteePubkeys_eq {subcommitteeIndex : UInt64}
    (inRange : subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT) :
    getSyncSubcommitteePubkeys state altair subcommitteeIndex =
      (syncCommitteeAtNextSlot state altair).map
        (syncSubcommitteePubkeys · subcommitteeIndex.toNat) := by
  have below : subcommitteeIndex.toNat < 4 := by
    simpa [SYNC_COMMITTEE_SUBNET_COUNT, Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT,
      UInt64.lt_iff_toNat_lt] using inRange
  have size : syncSubcommitteeSize preset < 2 ^ 62 := by
    have := preset.SYNC_COMMITTEE_SIZE.toNat_lt
    simp only [syncSubcommitteeSize, Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT]
    omega
  have small : (syncSubcommitteeSize preset).toUInt64.toNat < 2 ^ 62 := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    exact size
  have product :
      subcommitteeIndex.toNat * (syncSubcommitteeSize preset).toUInt64.toNat < 2 ^ 64 := by
    have := Nat.mul_le_mul_right (syncSubcommitteeSize preset).toUInt64.toNat
      (show subcommitteeIndex.toNat ≤ 3 by omega)
    omega
  unfold getSyncSubcommitteePubkeys
  cases syncCommitteeAtNextSlot state altair <;>
    simp [mulChecked_of_lt product, bind, Except.bind, pure, Except.pure, Except.map]

/-! ## Sync committee messages -/

section Message

variable {message : SyncCommitteeMessage} {subnetId : UInt64} {current valid : Bool}
  {validator : Validator} {committee : SyncCommittee preset}

/-- A message whose slot, validator and subnet a valid message had already is ignored. -/
theorem validateSyncCommitteeMessage_of_seen
    (known : (message.slot, message.validatorIndex, subnetId) ∈ seen.syncMessageKeys) :
    validateSyncCommitteeMessage config checks seen store altair message currentTimeMs subnetId =
      .ok (.ignore "already seen message from this validator for this slot and subnet") := by
  simp [validateSyncCommitteeMessage, known, pure, Except.pure]

/-- A valid message records its keys, so the same message on the same subnet is then ignored. -/
theorem validateSyncCommitteeMessage_recordSyncCommitteeMessage :
    validateSyncCommitteeMessage config checks (seen.recordSyncCommitteeMessage message subnetId)
        store altair message currentTimeMs subnetId =
      .ok (.ignore "already seen message from this validator for this slot and subnet") :=
  validateSyncCommitteeMessage_of_seen (by simp [Seen.recordSyncCommitteeMessage])

/-- A message whose index names no validator of the head state is rejected.

That check comes after the checks of the seen keys and of the slot. -/
theorem validateSyncCommitteeMessage_of_missing
    (clock : store.isCurrentSlot config message.slot currentTimeMs = .ok current)
    (head : store.headState config = .ok state)
    (missing : state.validators.data[message.validatorIndex.toNat]? = none) :
    validateSyncCommitteeMessage config checks seen store altair message currentTimeMs subnetId =
      .ok ((ignoreUnless
          (!seen.syncMessageKeys.contains (message.slot, message.validatorIndex, subnetId))
          "already seen message from this validator for this slot and subnet").andThen fun _ =>
        (ignoreUnless current "message is not for the current slot").andThen fun _ =>
        .reject "validator index out of range") := by
  unfold validateSyncCommitteeMessage
  simp only [clock, head, missing, bind, Except.bind, pure, Except.pure,
    ignoreUnless_andThenM, ignoreUnless_andThen, apply_ite (Except.ok (ε := ForkChoiceError))]

/-- The outcome of a sync committee message is its chain of checks, in order.

This holds once the slot check, the head state, the committee and the signature are computed. -/
theorem validateSyncCommitteeMessage_eq
    (clock : store.isCurrentSlot config message.slot currentTimeMs = .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[message.validatorIndex.toNat]? = some validator)
    (seats : syncCommitteeAtNextSlot state altair = .ok committee)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE message.slot
      message.beaconBlockRoot validator.pubkey message.signature = .ok valid) :
    validateSyncCommitteeMessage config checks seen store altair message currentTimeMs subnetId =
      .ok ((ignoreUnless
          (!seen.syncMessageKeys.contains (message.slot, message.validatorIndex, subnetId))
          "already seen message from this validator for this slot and subnet").andThen fun _ =>
        (ignoreUnless current "message is not for the current slot").andThen fun _ =>
        (rejectUnless ((syncSubnetsOfPubkey committee validator.pubkey).contains subnetId)
          "subnet_id is not valid for the validator").andThen fun _ =>
        rejectUnless valid "invalid sync committee message signature") := by
  unfold validateSyncCommitteeMessage
  simp only [clock, head, found, seats, signature, bind, Except.bind, pure, Except.pure,
    Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a message is ignored exactly in two cases.

A valid message had its slot, validator and subnet already, or its slot is not the current one. -/
theorem validateSyncCommitteeMessage_ignored
    (clock : store.isCurrentSlot config message.slot currentTimeMs = .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[message.validatorIndex.toNat]? = some validator)
    (seats : syncCommitteeAtNextSlot state altair = .ok committee)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE message.slot
      message.beaconBlockRoot validator.pubkey message.signature = .ok valid) :
    (∃ reason, validateSyncCommitteeMessage config checks seen store altair message currentTimeMs
        subnetId = .ok (.ignore reason)) ↔
      (message.slot, message.validatorIndex, subnetId) ∈ seen.syncMessageKeys ∨
        current = false := by
  rw [validateSyncCommitteeMessage_eq clock head found seats signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all

/-- Once its inputs are computed, a message is valid exactly when every check passes. -/
theorem validateSyncCommitteeMessage_eq_accept
    (clock : store.isCurrentSlot config message.slot currentTimeMs = .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[message.validatorIndex.toNat]? = some validator)
    (seats : syncCommitteeAtNextSlot state altair = .ok committee)
    (signature : isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE message.slot
      message.beaconBlockRoot validator.pubkey message.signature = .ok valid) :
    validateSyncCommitteeMessage config checks seen store altair message currentTimeMs subnetId =
        .ok accept ↔
      (message.slot, message.validatorIndex, subnetId) ∉ seen.syncMessageKeys ∧
        current = true ∧ subnetId ∈ syncSubnetsOfPubkey committee validator.pubkey ∧
        valid = true := by
  rw [validateSyncCommitteeMessage_eq clock head found seats signature]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all

end Message

/-! ## Contributions -/

section Contribution

variable {signed : SignedContributionAndProof preset} {current selected signedByAggregator
  aggregate : Bool} {aggregator : Validator} {pubkeys : List BLSPubkey}

/-- A contribution whose bits valid ones for its slot, root and subcommittee cover is ignored. -/
theorem validateContributionAndProof_of_covered
    (covered : isNonStrictSuperset (seen.contributionBits
      (signed.message.contribution.slot, signed.message.contribution.beaconBlockRoot,
        signed.message.contribution.subcommitteeIndex))
      signed.message.contribution.aggregationBits.bits.toList = true) :
    validateContributionAndProof config checks seen store altair signed currentTimeMs =
      .ok (.ignore "already seen contribution for this data") := by
  simp [validateContributionAndProof, covered, pure, Except.pure]

/-- A valid contribution records its bits, so the same contribution is then ignored. -/
theorem validateContributionAndProof_recordContributionAndProof :
    validateContributionAndProof config checks (seen.recordContributionAndProof signed) store
        altair signed currentTimeMs =
      .ok (.ignore "already seen contribution for this data") :=
  validateContributionAndProof_of_covered (isNonStrictSuperset_of_mem
    (by simp [Seen.recordContributionAndProof, Seen.contributionBits]))

/-- The outcome of a contribution is its chain of checks, in order.

This holds once the slot check, the head state, the subcommittee and the signatures are computed. -/
theorem validateContributionAndProof_eq
    (clock : store.isCurrentSlot config signed.message.contribution.slot currentTimeMs =
      .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (members : getSyncSubcommitteePubkeys state altair
      signed.message.contribution.subcommitteeIndex = .ok pubkeys)
    (selection : isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
      signed.message.contribution.slot
      (SyncAggregatorSelectionData.mk signed.message.contribution.slot
        signed.message.contribution.subcommitteeIndex)
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (bySigner : isValidSignatureAtSlot config checks state DOMAIN_CONTRIBUTION_AND_PROOF
      signed.message.contribution.slot signed.message aggregator.pubkey signed.signature =
        .ok signedByAggregator)
    (participants : isValidContributionSignature config checks state pubkeys
      signed.message.contribution = .ok aggregate) :
    validateContributionAndProof config checks seen store altair signed currentTimeMs =
      .ok ((ignoreUnless (!isNonStrictSuperset (seen.contributionBits
          (signed.message.contribution.slot, signed.message.contribution.beaconBlockRoot,
            signed.message.contribution.subcommitteeIndex))
          signed.message.contribution.aggregationBits.bits.toList)
          "already seen contribution for this data").andThen fun _ =>
        (ignoreUnless (!seen.syncContributionAggregatorKeys.contains
          (signed.message.contribution.slot, signed.message.aggregatorIndex,
            signed.message.contribution.subcommitteeIndex))
          "already seen contribution from this aggregator").andThen fun _ =>
        (ignoreUnless current "contribution is not for the current slot").andThen fun _ =>
        (rejectUnless (signed.message.contribution.subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT)
          "subcommittee index out of range").andThen fun _ =>
        (rejectUnless (signed.message.contribution.aggregationBits.bits.toList.any id)
          "contribution has no participants").andThen fun _ =>
        (rejectUnless (isSyncCommitteeAggregator preset signed.message.selectionProof)
          "validator is not selected as aggregator").andThen fun _ =>
        (rejectUnless (pubkeys.contains aggregator.pubkey)
          "aggregator is not a member of the committee").andThen fun _ =>
        (rejectUnless selected "invalid selection proof signature").andThen fun _ =>
        (rejectUnless signedByAggregator "invalid aggregator signature").andThen fun _ =>
        rejectUnless aggregate "invalid aggregate signature") := by
  unfold validateContributionAndProof
  simp only [clock, head, found, members, selection, bySigner, participants, bind, Except.bind,
    pure, Except.pure, Except.mapError,
    ignoreUnless_andThenM, ignoreUnless_andThen, rejectUnless_andThenM, rejectUnless_andThen,
    apply_ite (Except.ok (ε := ForkChoiceError))]

/-- Once its inputs are computed, a contribution is ignored exactly in three cases.

Valid contributions for its slot, root and subcommittee cover its bits.

Or its aggregator has a valid contribution for its slot and subcommittee already.

Or its slot is not the current one. -/
theorem validateContributionAndProof_ignored
    (clock : store.isCurrentSlot config signed.message.contribution.slot currentTimeMs =
      .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (members : getSyncSubcommitteePubkeys state altair
      signed.message.contribution.subcommitteeIndex = .ok pubkeys)
    (selection : isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
      signed.message.contribution.slot
      (SyncAggregatorSelectionData.mk signed.message.contribution.slot
        signed.message.contribution.subcommitteeIndex)
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (bySigner : isValidSignatureAtSlot config checks state DOMAIN_CONTRIBUTION_AND_PROOF
      signed.message.contribution.slot signed.message aggregator.pubkey signed.signature =
        .ok signedByAggregator)
    (participants : isValidContributionSignature config checks state pubkeys
      signed.message.contribution = .ok aggregate) :
    (∃ reason, validateContributionAndProof config checks seen store altair signed currentTimeMs =
        .ok (.ignore reason)) ↔
      isNonStrictSuperset (seen.contributionBits
          (signed.message.contribution.slot, signed.message.contribution.beaconBlockRoot,
            signed.message.contribution.subcommitteeIndex))
          signed.message.contribution.aggregationBits.bits.toList = true ∨
        (signed.message.contribution.slot, signed.message.aggregatorIndex,
          signed.message.contribution.subcommitteeIndex) ∈ seen.syncContributionAggregatorKeys ∨
        current = false := by
  rw [validateContributionAndProof_eq clock head found members selection bySigner participants]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all

/-- Once its inputs are computed, a contribution is valid exactly when every check passes. -/
theorem validateContributionAndProof_eq_accept
    (clock : store.isCurrentSlot config signed.message.contribution.slot currentTimeMs =
      .ok current)
    (head : store.headState config = .ok state)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (members : getSyncSubcommitteePubkeys state altair
      signed.message.contribution.subcommitteeIndex = .ok pubkeys)
    (selection : isValidSignatureAtSlot config checks state DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF
      signed.message.contribution.slot
      (SyncAggregatorSelectionData.mk signed.message.contribution.slot
        signed.message.contribution.subcommitteeIndex)
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (bySigner : isValidSignatureAtSlot config checks state DOMAIN_CONTRIBUTION_AND_PROOF
      signed.message.contribution.slot signed.message aggregator.pubkey signed.signature =
        .ok signedByAggregator)
    (participants : isValidContributionSignature config checks state pubkeys
      signed.message.contribution = .ok aggregate) :
    validateContributionAndProof config checks seen store altair signed currentTimeMs =
        .ok accept ↔
      isNonStrictSuperset (seen.contributionBits
          (signed.message.contribution.slot, signed.message.contribution.beaconBlockRoot,
            signed.message.contribution.subcommitteeIndex))
          signed.message.contribution.aggregationBits.bits.toList = false ∧
        (signed.message.contribution.slot, signed.message.aggregatorIndex,
          signed.message.contribution.subcommitteeIndex) ∉ seen.syncContributionAggregatorKeys ∧
        current = true ∧
        signed.message.contribution.subcommitteeIndex < SYNC_COMMITTEE_SUBNET_COUNT ∧
        signed.message.contribution.aggregationBits.bits.toList.any id = true ∧
        isSyncCommitteeAggregator preset signed.message.selectionProof = true ∧
        aggregator.pubkey ∈ pubkeys ∧ selected = true ∧ signedByAggregator = true ∧
        aggregate = true := by
  rw [validateContributionAndProof_eq clock head found members selection bySigner participants]
  simp only [Except.ok.injEq, ignoreUnless_andThen, rejectUnless_andThen]
  repeat' split
  all_goals simp_all [UInt64.lt_iff_toNat_lt]
  all_goals omega

end Contribution

end EthLib.Consensus

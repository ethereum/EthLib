module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.TargetPending
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades
public import EthLib.Consensus.Proofs.Transition.Totality.Pending

/-!
# Proofs: a block keeps the facts on the pending attestations

Before Altair, the totality of the epoch transition assumes facts on the pending attestations.

They are well formed and resolved, and each is a vote of its signers for its link.

A block keeps them, with the slots and upgrades before it.

It also keeps the two justified checkpoints equal in the first two epochs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## From Altair and across the upgrades -/

/-- From Altair, the votes of the pending attestations hold for any set, since none are kept. -/
theorem PendingVoted.of_altair {votes : Set (ValidatorIndex × AttestationData)}
    (altair : .altair ≤ fork) (state : BeaconState preset fork) : PendingVoted votes state :=
  fun before => absurd before (Nat.not_lt_of_le altair)

/-- The upgrades due at a slot keep the pending attestations well formed. -/
theorem PendingWellFormed.of_processUpgrades {forked upgraded : ForkedBeaconState preset}
    (holds : PendingWellFormed forked.state)
    (computed : processUpgrades config checks forked = .ok upgraded) :
    PendingWellFormed upgraded.state :=
  processUpgrades_induction (property := fun state => PendingWellFormed state.state)
    (fun _ stepOk => PendingWellFormed.of_altair (upgradeNext_altair stepOk).1 _) holds computed

/-- The upgrades due at a slot keep the pending attestations resolved. -/
theorem PendingResolved.of_processUpgrades {forked upgraded : ForkedBeaconState preset}
    (holds : PendingResolved forked.state)
    (computed : processUpgrades config checks forked = .ok upgraded) :
    PendingResolved upgraded.state :=
  processUpgrades_induction (property := fun state => PendingResolved state.state)
    (fun _ stepOk => PendingResolved.of_altair (upgradeNext_altair stepOk).1 _) holds computed

/-! ## A pending frame and one attestation -/

/-- The previous or the current epoch is at most the current epoch, and at least one before it. -/
private theorem recentEpoch_bounds (state : BeaconState preset fork) (current : Bool) :
    (if current then getCurrentEpoch state else getPreviousEpoch state) ≤
        getCurrentEpoch state ∧
      (getCurrentEpoch state).toNat ≤
        (if current then getCurrentEpoch state else getPreviousEpoch state).toNat + 1 := by
  have previous := getPreviousEpoch_toNat state
  cases current
  · exact ⟨getPreviousEpoch_le state, by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩
  · exact ⟨UInt64.le_refl _, by simp⟩

/-- A pending frame keeps the committees of the previous and the current epoch. -/
private theorem PendingFrame.committeesKept
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (frame : PendingFrame state after) (current : Bool) :
    CommitteesKept (if current then getCurrentEpoch state else getPreviousEpoch state)
      state after := by
  obtain ⟨low, high⟩ := recentEpoch_bounds state current
  exact CommitteesKept.of_activeKept apart (frame.active.mono low) frame.mixes low high

/-- A pending frame keeps the recent pending attestations well formed. -/
private theorem PendingWellFormed.of_pendingFrame (frame : PendingFrame state after)
    (wellFormed : PendingWellFormed state) : PendingWellFormed after := by
  intro before
  obtain ⟨previous, current⟩ := wellFormed before
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  have grows := frame.registryGrows
  refine ⟨fun attestation member => ?_, fun attestation member => ?_⟩
  · rw [frame.previousPending before] at member
    obtain ⟨epoch, delay, proposer⟩ := previous attestation member
    exact ⟨previousEq ▸ epoch, delay, by omega⟩
  · rw [frame.currentPending before] at member
    obtain ⟨epoch, delay, proposer⟩ := current attestation member
    exact ⟨currentEq ▸ epoch, delay, by omega⟩

/-- Before Altair, the slot of each recent pending attestation is in the epoch of its list. -/
private def PendingEpochs (state : BeaconState preset fork) : Prop :=
  ∀ before : fork < .altair,
    (∀ attestation ∈ (state.previousEpochAttestations before).data,
      computeEpochAtSlot preset attestation.data.slot = getPreviousEpoch state) ∧
    ∀ attestation ∈ (state.currentEpochAttestations before).data,
      computeEpochAtSlot preset attestation.data.slot = getCurrentEpoch state

/-- Well formed pending attestations have their slots in the epochs of their lists. -/
private theorem PendingEpochs.of_wellFormed (wellFormed : PendingWellFormed state) :
    PendingEpochs state := fun before =>
  ⟨fun attestation member => ((wellFormed before).1 attestation member).1,
    fun attestation member => ((wellFormed before).2 attestation member).1⟩

/-- A pending frame keeps the slots of the pending attestations in the epochs of their lists. -/
private theorem PendingEpochs.of_pendingFrame (frame : PendingFrame state after)
    (epochs : PendingEpochs state) : PendingEpochs after := by
  intro before
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  rw [frame.previousPending before, frame.currentPending before, currentEq, previousEq]
  exact epochs before

/-- A pending frame keeps the recent pending attestations resolved. -/
private theorem PendingResolved.of_pendingFrame
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (frame : PendingFrame state after) (epochs : PendingEpochs state)
    (resolved : PendingResolved state) : PendingResolved after := by
  intro before attestation member
  rw [frame.previousPending before, frame.currentPending before] at member
  obtain ⟨previous, current⟩ := epochs before
  have kept : ∀ inCurrent : Bool, computeEpochAtSlot preset attestation.data.slot =
      (if inCurrent then getCurrentEpoch state else getPreviousEpoch state) →
      getPendingAttestingIndices after attestation =
        getPendingAttestingIndices state attestation := by
    intro inCurrent atSlot
    unfold getPendingAttestingIndices
    rw [frame.committeesKept apart inCurrent _ _ atSlot]
  rcases member with inPrevious | inCurrent
  · rw [kept false (previous attestation inPrevious)]
    exact resolved before attestation (.inl inPrevious)
  · rw [kept true (current attestation inCurrent)]
    exact resolved before attestation (.inr inCurrent)

/-- Before Altair, an attestation adds one pending attestation to the list of its target epoch.

Each pending attestation after it was there before, or is the new one in the list of its target.
-/
private theorem processAttestation_lists {parentSlot : Slot} {attestation : Attestation preset fork}
    (before : fork < .altair)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ pending : PendingAttestation preset,
      pending.aggregationBits.bits = attestation.aggregationBits.bits ∧
      pending.data = attestation.data ∧
      pending.inclusionDelay = state.slot - attestation.data.slot ∧
      getBeaconProposerIndex state = .ok pending.proposerIndex ∧
      (∀ other ∈ (after.previousEpochAttestations before).data,
        other ∈ (state.previousEpochAttestations before).data ∨
          other = pending ∧ attestation.data.target.epoch = getPreviousEpoch state) ∧
      ∀ other ∈ (after.currentEpochAttestations before).data,
        other ∈ (state.currentEpochAttestations before).data ∨
          other = pending ∧ attestation.data.target.epoch = getCurrentEpoch state := by
  obtain ⟨recent, -⟩ := processAttestation_checks before computed
  obtain ⟨pending, bits, dataEq, delay, proposer, recorded, -⟩ :=
    processAttestation_records before computed
  refine ⟨pending, bits, dataEq, delay, proposer, ?_⟩
  have kept := recordPendingAttestation_ok recorded
  cases chosen : (attestation.data.target.epoch == getCurrentEpoch state)
  · simp only [chosen, Bool.false_eq_true, ↓reduceIte] at kept
    obtain ⟨pushed, rest⟩ := kept
    have differ : attestation.data.target.epoch ≠ getCurrentEpoch state := ne_of_beq_false chosen
    refine ⟨fun other member => ?_, fun other member => .inl ?_⟩
    · rw [pushed] at member
      rcases Array.mem_push.mp member with old | rfl
      · exact .inl old
      · exact .inr ⟨rfl, recent.resolve_right differ⟩
    · rw [← rest]
      exact member
  · simp only [chosen, ↓reduceIte] at kept
    obtain ⟨pushed, rest⟩ := kept
    refine ⟨fun other member => .inl ?_, fun other member => ?_⟩
    · rw [← rest]
      exact member
    · rw [pushed] at member
      rcases Array.mem_push.mp member with old | rfl
      · exact .inl old
      · exact .inr ⟨rfl, beq_iff_eq.mp chosen⟩

/-- Before Altair, an attestation keeps the pending attestations well formed, the new one too.

The least inclusion delay must be positive. -/
private theorem PendingWellFormed.of_processAttestation
    (delay : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat) {parentSlot : Slot}
    {attestation : Attestation preset fork} (wellFormed : PendingWellFormed state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PendingWellFormed after := by
  intro before
  obtain ⟨previous, current⟩ := wellFormed before
  have frame := frame_processAttestation computed
  have registry := processAttestation_registry computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  obtain ⟨-, slotEpoch, early, -⟩ := processAttestation_checks before computed
  obtain ⟨pending, -, dataEq, delayEq, proposerOk, inPrevious, inCurrent⟩ :=
    processAttestation_lists before computed
  -- The new pending attestation has a nonzero delay and a proposer of the registry.
  have newDelay : pending.inclusionDelay ≠ 0 := by
    rw [delayEq]
    intro zero
    have le : attestation.data.slot ≤ state.slot := UInt64.le_iff_toNat_le.mpr (by omega)
    have difference := UInt64.toNat_sub_of_le _ _ le
    rw [zero, UInt64.toNat_zero] at difference
    omega
  have newProposer : pending.proposerIndex.toNat < after.validators.data.size := by
    have beforeFulu : ¬.fusaka ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
    have active := mem_getActiveValidatorIndices_of_getBeaconProposerIndex beforeFulu proposerOk
    obtain ⟨validator, found, -⟩ := (mem_getActiveValidatorIndices
      (state.validators.bound (Nat.lt_trans before (by decide)))).mp active
    rw [registry.1]
    exact (Array.getElem?_eq_some_iff.mp found).1
  refine ⟨fun other member => ?_, fun other member => ?_⟩
  · rcases inPrevious other member with old | ⟨rfl, target⟩
    · obtain ⟨epoch, nonzero, proposer⟩ := previous other old
      exact ⟨previousEq ▸ epoch, nonzero, registry.1 ▸ proposer⟩
    · exact ⟨by rw [dataEq, previousEq, ← slotEpoch, target], newDelay, newProposer⟩
  · rcases inCurrent other member with old | ⟨rfl, target⟩
    · obtain ⟨epoch, nonzero, proposer⟩ := current other old
      exact ⟨currentEq ▸ epoch, nonzero, registry.1 ▸ proposer⟩
    · exact ⟨by rw [dataEq, currentEq, ← slotEpoch, target], newDelay, newProposer⟩

/-- Before Altair, an attestation keeps the pending attestations resolved, the new one too. -/
private theorem PendingResolved.of_processAttestation {parentSlot : Slot}
    {attestation : Attestation preset fork} (resolved : PendingResolved state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PendingResolved after := by
  intro before other member
  have registry := processAttestation_registry computed
  -- The registry and the mixes stay, so every committee does.
  have same : ∀ attestation, getPendingAttestingIndices after attestation =
      getPendingAttestingIndices state attestation := by
    intro attestation
    unfold getPendingAttestingIndices
    rw [CommitteesKept.of_eq (congrArg (·.data) registry.1) (congrArg (·.elements) registry.2)
      _ _ _ rfl]
  rw [same]
  obtain ⟨-, -, -, -, -, ⟨committee, committeeOk, sized⟩, -⟩ :=
    processAttestation_checks before computed
  obtain ⟨pending, bits, dataEq, -, -, inPrevious, inCurrent⟩ :=
    processAttestation_lists before computed
  -- The new one reads the committee that the attestation names, with one bit per member.
  have fresh : ∃ signers, getPendingAttestingIndices state pending = .ok signers := by
    unfold getPendingAttestingIndices
    rw [dataEq, committeeOk, bits]
    simp only [bind, Except.bind, committeeAttesters, sized, Nat.zero_add, Nat.lt_irrefl,
      and_false, ↓reduceIte, Except.ok.injEq, exists_eq']
  rcases member with inAfter | inAfter
  · rcases inPrevious other inAfter with old | ⟨rfl, -⟩
    · exact resolved before other (.inl old)
    · exact fresh
  · rcases inCurrent other inAfter with old | ⟨rfl, -⟩
    · exact resolved before other (.inr old)
    · exact fresh

/-- Before Altair, an attestation keeps the slots of the pending attestations in their epochs.
-/
private theorem PendingEpochs.of_processAttestation {parentSlot : Slot}
    {attestation : Attestation preset fork} (epochs : PendingEpochs state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PendingEpochs after := by
  intro before
  obtain ⟨previous, current⟩ := epochs before
  have frame := frame_processAttestation computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  obtain ⟨-, slotEpoch, -⟩ := processAttestation_checks before computed
  obtain ⟨pending, -, dataEq, -, -, inPrevious, inCurrent⟩ :=
    processAttestation_lists before computed
  refine ⟨fun other member => ?_, fun other member => ?_⟩
  · rcases inPrevious other member with old | ⟨rfl, target⟩
    · exact previousEq ▸ previous other old
    · rw [dataEq, previousEq, ← slotEpoch, target]
  · rcases inCurrent other member with old | ⟨rfl, target⟩
    · exact currentEq ▸ current other old
    · rw [dataEq, currentEq, ← slotEpoch, target]

/-! ## The theorems on a block -/

/-- A block keeps the recent pending attestations well formed.

The least inclusion delay must be positive, as on mainnet and minimal. -/
theorem PendingWellFormed.of_processBlock
    (delay : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat) {block : BeaconBlock preset fork}
    (wellFormed : PendingWellFormed state)
    (computed : processBlock config checks engine state block = .ok after) :
    PendingWellFormed after := by
  by_cases before : fork < .altair
  · obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
    exact PendingWellFormed.of_pendingFrame tail (foldlM_ok_invariant PendingWellFormed
      (fun _ _ _ holds ok => holds.of_processAttestation delay ok)
      (wellFormed.of_pendingFrame head) attested)
  · exact PendingWellFormed.of_altair (Nat.le_of_not_lt before) after

/-- After a block, the committee and the signers of each recent pending attestation succeed.

Each recent pending attestation must be as inclusion in a block stored it.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem PendingResolved.of_processBlock
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork} (wellFormed : PendingWellFormed state)
    (resolved : PendingResolved state)
    (computed : processBlock config checks engine state block = .ok after) :
    PendingResolved after := by
  by_cases before : fork < .altair
  · obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
    have epochs := PendingEpochs.of_wellFormed wellFormed
    have middle := foldlM_ok_invariant (fun state => PendingEpochs state ∧ PendingResolved state)
      (fun _ _ _ holds ok => ⟨holds.1.of_processAttestation ok, holds.2.of_processAttestation ok⟩)
      ⟨epochs.of_pendingFrame head, resolved.of_pendingFrame apart head epochs⟩ attested
    exact middle.2.of_pendingFrame apart tail middle.1
  · exact PendingResolved.of_altair (Nat.le_of_not_lt before) after

/-! ## A block after the slots and upgrades before it -/

/-- The three facts on the pending attestations, and the equal early justified checkpoints. -/
private def PendingFacts (state : BeaconState preset fork) : Prop :=
  PendingWellFormed state ∧ PendingResolved state ∧ PendingVoted Set.univ state ∧
    JustifiedEarly state

/-- One slot keeps the four facts. -/
private theorem PendingFacts.of_advanceSlot
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (facts : PendingFacts state) (computed : advanceSlot config checks state = .ok after) :
    PendingFacts after := by
  obtain ⟨wellFormed, resolved, voted, early⟩ := facts
  refine ⟨wellFormed.of_advanceSlot computed, resolved.of_advanceSlot apart wellFormed computed,
    ?_, early.of_advanceSlot computed⟩
  by_cases before : fork < .altair
  · exact voted.of_advanceSlot before apart early computed
  · exact PendingVoted.of_altair (Nat.le_of_not_lt before) after

/-- The upgrades due at a slot keep the four facts. -/
private theorem PendingFacts.of_processUpgrades {forked upgraded : ForkedBeaconState preset}
    (facts : PendingFacts forked.state)
    (computed : processUpgrades config checks forked = .ok upgraded) :
    PendingFacts upgraded.state :=
  ⟨facts.1.of_processUpgrades computed, facts.2.1.of_processUpgrades computed,
    facts.2.2.1.of_processUpgrades computed, facts.2.2.2.of_processUpgrades computed⟩

/-- A run of slots across the forks keeps the four facts, with the upgrades on the way. -/
private theorem PendingFacts.of_advanceSlotsAcross
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∀ {count : Nat} {forked reached : ForkedBeaconState preset},
      PendingFacts forked.state → advanceSlotsAcross config checks count forked = .ok reached →
        PendingFacts reached.state
  | 0, forked, reached, facts, computed => by
    simp only [advanceSlotsAcross, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ facts
  | count + 1, forked, reached, facts, computed => by
    simp only [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp nextOk
    exact PendingFacts.of_advanceSlotsAcross apart
      ((facts.of_advanceSlot apart advancedOk).of_processUpgrades upgraded) rest

/-- A block that the transition accepts keeps the facts on the pending attestations.

The state advances to the slot of the block, with the upgrades on the way.

Before Altair, the pending attestations stay well formed and resolved.

Each keeps its target in the epoch of its list and of its slot, and its source at the checkpoint.

At every fork, the early justified checkpoints stay equal.

The least inclusion delay must be positive.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem stateTransitionAcross_pending {forked : ForkedBeaconState preset}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (delay : 0 < preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (wellFormed : PendingWellFormed forked.state) (resolved : PendingResolved forked.state)
    (voted : PendingVoted Set.univ forked.state) (early : JustifiedEarly forked.state)
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    PendingWellFormed after ∧ PendingResolved after ∧ PendingVoted Set.univ after ∧
      JustifiedEarly after := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  simp only [processSlotsAcross, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  obtain ⟨wellFormed', resolved', voted', early'⟩ : PendingFacts advanced :=
    PendingFacts.of_advanceSlotsAcross apart ⟨wellFormed, resolved, voted, early⟩ advancedOk
  have blockOk := (applySignedBlock_ok applied).2.1
  refine ⟨wellFormed'.of_processBlock delay blockOk,
    resolved'.of_processBlock apart wellFormed' blockOk, ?_,
    early'.of_frame (frame_processBlock blockOk)⟩
  by_cases before : fork < .altair
  · exact (voted'.of_processBlock before apart blockOk).mono (Set.subset_univ _)
  · exact PendingVoted.of_altair (Nat.le_of_not_lt before) after

end EthLib.Consensus

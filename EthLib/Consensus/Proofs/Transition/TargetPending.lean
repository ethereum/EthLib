module

public import EthLib.Base.Proofs.FilterM
public import EthLib.Consensus.Proofs.Transition.MixesKept
public import EthLib.Consensus.Proofs.Transition.TargetSlots

/-!
# Proofs: before Altair, the attesters that justification counts cast votes for the right link

Before Altair, justification counts the stake of the attesters of pending attestations.

Each of them cast a vote of a set for the link of the epoch of its attestation.

A block adds the votes that its attestations cast, and each other step keeps the fact.

A block accepts an attestation only when the signature checks accept its aggregate signature.

Reading such a vote as signed by its validator assumes the BLS checks and unforgeable aggregates.

Gasper §4.4, Definition 4.5, justifies a checkpoint by the stake of the votes for one link.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- Before Altair: the pending attestations of the current epoch when asked, else of the previous.
-/
def recentPending (state : BeaconState preset fork) (before : fork < .altair) (current : Bool) :
    Array (PendingAttestation preset) :=
  if current then (state.currentEpochAttestations before).data
  else (state.previousEpochAttestations before).data

/-- Before Altair, each pending attestation of the two epochs is a vote of a set for its link.

Its target epoch is the epoch of its list, and the epoch of its slot.

Its source is the justified checkpoint that the state holds for that epoch.

Each member of its committee in the state whose bit is set cast a vote of the set with its data.
-/
def PendingVoted (votes : Set (ValidatorIndex × AttestationData))
    (state : BeaconState preset fork) : Prop :=
  ∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
    pending.data.target.epoch =
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
      pending.data.source =
        (if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint) ∧
      ∀ attesters, getPendingAttestingIndices state pending = .ok attesters →
        ∀ attester ∈ attesters, (attester, pending.data) ∈ votes

/-- With more votes, each pending attestation is still a vote of the set for its link. -/
theorem PendingVoted.mono {votes votes' : Set (ValidatorIndex × AttestationData)}
    (holds : PendingVoted votes state) (sub : votes ⊆ votes') : PendingVoted votes' state := by
  intro before current pending member
  obtain ⟨epoch, slot, source, voted⟩ := holds before current pending member
  exact ⟨epoch, slot, source, fun attesters computed attester inside =>
    sub (voted attesters computed attester inside)⟩

/-! ## Blocks -/

/-- The current or the previous epoch is at most the current one, and at most one before it. -/
private theorem recent_bounds (state : BeaconState preset fork) (current : Bool) :
    (if current then getCurrentEpoch state else getPreviousEpoch state) ≤
        getCurrentEpoch state ∧
      (getCurrentEpoch state).toNat ≤
        (if current then getCurrentEpoch state else getPreviousEpoch state).toNat + 1 := by
  have previous := getPreviousEpoch_toNat state
  cases current
  · exact ⟨getPreviousEpoch_le state, by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩
  · exact ⟨UInt64.le_refl _, by simp⟩

/-- The attesters of a pending attestation still cast votes of the set, with the same committees.
-/
private theorem votedAttesters_of {other : BeaconState preset fork}
    {votes : Set (ValidatorIndex × AttestationData)} {pending : PendingAttestation preset}
    (committees : CommitteesKept pending.data.target.epoch state other)
    (slot : computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch)
    (voted : ∀ attesters, getPendingAttestingIndices state pending = .ok attesters →
      ∀ attester ∈ attesters, (attester, pending.data) ∈ votes) :
    ∀ attesters, getPendingAttestingIndices other pending = .ok attesters →
      ∀ attester ∈ attesters, (attester, pending.data) ∈ votes := by
  intro attesters computed
  unfold getPendingAttestingIndices at computed
  rw [committees _ _ slot] at computed
  exact voted attesters computed

/-- Before Altair, recording a pending attestation appends it to the list of its epoch. -/
private theorem recordPendingAttestation_lists {before : fork < .altair} {current : Bool}
    {pending : PendingAttestation preset}
    (computed : recordPendingAttestation state before current pending = .ok after) :
    recentPending after before current = (recentPending state before current).push pending ∧
      recentPending after before (!current) = recentPending state before (!current) := by
  have kept := recordPendingAttestation_ok computed
  cases current
  · simp only [Bool.false_eq_true, ↓reduceIte] at kept
    obtain ⟨pushed, rest⟩ := kept
    refine ⟨pushed, ?_⟩
    simp only [recentPending, Bool.not_false, ↓reduceIte]
    rw [← rest]
  · simp only [↓reduceIte] at kept
    obtain ⟨pushed, rest⟩ := kept
    refine ⟨pushed, ?_⟩
    simp only [recentPending, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [← rest]

/-- Before Altair, a step of a block other than an attestation keeps the pending votes.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem PendingVoted.of_pendingFrame {votes : Set (ValidatorIndex × AttestationData)}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (frame : PendingFrame state after) (holds : PendingVoted votes state) :
    PendingVoted votes after := by
  intro before current pending member
  have lists : recentPending after before current = recentPending state before current := by
    cases current <;> simp [recentPending, frame.previousPending, frame.currentPending]
  rw [lists] at member
  obtain ⟨epoch, slot, source, voted⟩ := holds before current pending member
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  obtain ⟨low, high⟩ := recent_bounds state current
  have committees := CommitteesKept.of_activeKept apart (frame.active.mono low) frame.mixes low high
  rw [← epoch] at committees
  exact ⟨by rw [currentEq, previousEq]; exact epoch, slot,
    by rw [frame.currentJustified, frame.previousJustified]; exact source,
    votedAttesters_of committees slot voted⟩

/-- Before Altair, an attestation keeps the pending votes, and adds those that it casts.

It casts them in the committees of the state before it. -/
theorem PendingVoted.of_processAttestation {votes : Set (ValidatorIndex × AttestationData)}
    {parentSlot : Slot} {attestation : Attestation preset fork} (before : fork < .altair)
    (holds : PendingVoted votes state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PendingVoted (votes ∪ attestationVotes state attestation) after := by
  have frame := frame_processAttestation computed
  have registry := processAttestation_registry computed
  have beforeElectra : fork < .pectra := Nat.lt_trans before (by decide)
  have committees : ∀ epoch, CommitteesKept epoch state after := CommitteesKept.of_eq
    (congrArg (·.data) registry.1) (congrArg (·.elements) registry.2)
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  -- A pending vote that was there keeps its epoch, source and votes.
  have kept : ∀ (current : Bool), ∀ pending ∈ recentPending state before current,
      pending.data.target.epoch =
          (if current then getCurrentEpoch after else getPreviousEpoch after) ∧
        computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
        pending.data.source =
          (if current then after.currentJustifiedCheckpoint
          else after.previousJustifiedCheckpoint) ∧
        ∀ attesters, getPendingAttestingIndices after pending = .ok attesters →
          ∀ attester ∈ attesters,
            (attester, pending.data) ∈ votes ∪ attestationVotes state attestation := by
    intro current pending member
    obtain ⟨epoch, slot, source, voted⟩ := holds before current pending member
    exact ⟨by rw [currentEq, previousEq]; exact epoch, slot,
      by rw [frame.currentJustified, frame.previousJustified]; exact source,
      fun attesters computed attester inside =>
        .inl (votedAttesters_of (committees _) slot voted attesters computed attester inside)⟩
  obtain ⟨recent, slotEpoch, -, -, -, ⟨committee, committeeOk, -⟩, source⟩ :=
    processAttestation_checks before computed
  obtain ⟨pending, bits, dataEq, -, -, recorded, -⟩ := processAttestation_records before computed
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  intro before' current other member
  generalize chosen : (attestation.data.target.epoch == getCurrentEpoch state) = target
    at added same
  by_cases here : current = target
  · subst here
    rw [added] at member
    rcases Array.mem_push.mp member with old | rfl
    · exact kept _ other old
    -- The new pending vote: its epoch, its source, and the votes that the attestation casts.
    rw [dataEq]
    refine ⟨?_, slotEpoch.symm, ?_, fun attesters attestersOk attester inside => ?_⟩
    · cases current
      · have differ : attestation.data.target.epoch ≠ getCurrentEpoch state :=
          ne_of_beq_false chosen
        simpa [previousEq] using recent.resolve_right differ
      · simpa [currentEq] using beq_iff_eq.mp chosen
    · rw [frame.currentJustified, frame.previousJustified, source]
      cases current
      · simp [ne_of_beq_false chosen]
      · simp [beq_iff_eq.mp chosen]
    · have committeeAfter : getBeaconCommittee after attestation.data.slot
          attestation.data.index = .ok committee := by
        rw [committees _ _ _ rfl]
        exact committeeOk
      unfold getPendingAttestingIndices at attestersOk
      rw [dataEq, bits] at attestersOk
      simp only [committeeAfter, bind, Except.bind] at attestersOk
      have signers : getAttestingIndices state attestation = .ok (sortedSet attesters) := by
        simp only [getAttestingIndices_of_lt_electra beforeElectra, committeeOk, bind,
          Except.bind, attestersOk, pure, Except.pure]
      exact .inr ⟨rfl, _, signers, mem_sortedSet.mpr inside⟩
  · have flipped : current = !target := by cases current <;> cases target <;> simp_all
    subst flipped
    rw [same] at member
    exact kept _ other member

/-- Before Altair, a block keeps the pending votes, and adds those that its attestations cast.

It casts them in the committees of the state before the block.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem PendingVoted.of_processBlock {votes : Set (ValidatorIndex × AttestationData)}
    (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork}
    (holds : PendingVoted votes state)
    (computed : processBlock config checks engine state block = .ok after) :
    PendingVoted (votes ∪ blockVotes state block) after := by
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  have same := getAttestingIndices_eq_of_foldlM apart head.slot head.active head.mixes attested
  have middle := foldlM_processAttestation_votes PendingVoted (fun holds sub => holds.mono sub)
    (fun holds ok => holds.of_processAttestation before ok) (holds.of_pendingFrame apart head)
    attested
  rw [blockVotes_eq_of_attesters fun attestation member =>
    same attestation (Array.mem_toList_iff.mpr member)] at middle
  exact middle.of_pendingFrame apart tail

/-! ## Slots -/

/-- The caching of a slot keeps each pending attestation a vote of the set for its link. -/
theorem PendingVoted.of_processSlot {votes : Set (ValidatorIndex × AttestationData)}
    (holds : PendingVoted votes state) (computed : processSlot state = .ok after) :
    PendingVoted votes after := by
  have frame := frame_processSlot computed
  obtain ⟨_, _, _, _, afterEq⟩ := processSlot_ok computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  intro before current pending member
  have lists : recentPending after before current = recentPending state before current := by
    cases current <;> simp only [recentPending, afterEq]
  rw [lists] at member
  obtain ⟨epoch, slot, source, voted⟩ := holds before current pending member
  have committees : CommitteesKept pending.data.target.epoch state after :=
    CommitteesKept.of_eq (by rw [afterEq]) (by rw [afterEq]) _
  refine ⟨by rw [currentEq, previousEq]; exact epoch, slot, ?_,
    votedAttesters_of committees slot voted⟩
  rw [frame.currentJustified, frame.previousJustified]
  exact source

/-- Before Altair, one slot keeps each pending attestation a vote of the set for its link.

At the end of an epoch the votes of the current epoch become those of the previous one.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The two justified checkpoints must be equal in the first two epochs. -/
theorem PendingVoted.of_advanceSlot {votes : Set (ValidatorIndex × AttestationData)}
    (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (early : JustifiedEarly state) (holds : PendingVoted votes state)
    (computed : advanceSlot config checks state = .ok after) :
    PendingVoted votes after := by
  have committees := fun {epoch : Epoch} => committeesKept_advanceSlot (epoch := epoch) apart
    (BeaconState.validators_size_lt_of_lt_glamsterdam (Nat.lt_trans before (by decide)) after)
    computed
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have cachedFrame := frame_processSlot cachedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedLists : ∀ current, recentPending cached before current =
      recentPending state before current := by
    intro current
    cases current <;> simp [recentPending, cachedEq]
  have stateEpoch := getCurrentEpoch_toNat state
  have afterEpoch := getCurrentEpoch_toNat { epoched with slot := next }
  dsimp only at afterEpoch
  intro before' current pending member
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have epochs := nextSlot_epoch_of_boundary sum boundary
    have previousEq : getPreviousEpoch { epoched with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, afterEpoch, stateEpoch, epochs]
      rfl
    obtain ⟨rotated, emptied⟩ := processEpoch_pendingRotation before epochedOk
    obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
    have previousJustified := (early.of_frame cachedFrame).previousJustified_of_justification
      justifiedOk
    cases current
    · -- The votes of the old current epoch are now those of the previous epoch.
      have moved : recentPending { epoched with slot := next } before false =
          recentPending state before true := by
        rw [← cachedLists true]
        simp [recentPending, rotated]
      rw [moved] at member
      obtain ⟨epoch, slot, source, voted⟩ := holds before true pending member
      simp only [↓reduceIte] at epoch source
      refine ⟨by simp only [Bool.false_eq_true, ↓reduceIte, previousEq]; exact epoch, slot, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [source, frame.previousJustified, previousJustified, cachedFrame.currentJustified]
      · have kept : CommitteesKept pending.data.target.epoch state
            { epoched with slot := next } := by
          rw [epoch]
          exact committees (by rw [previousEq]; exact UInt64.le_refl _) (UInt64.le_refl _)
        exact votedAttesters_of kept slot voted
    · simp [recentPending, emptied] at member
  · rename_i inside
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have currentEq : getCurrentEpoch { cached with slot := next } = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [afterEpoch, stateEpoch]
      exact nextSlot_epoch_of_inside sum inside
    have previousEq : getPreviousEpoch { cached with slot := next } = getPreviousEpoch state := by
      unfold getPreviousEpoch
      rw [currentEq]
    have lists : recentPending { cached with slot := next } before current =
        recentPending state before current := cachedLists current
    rw [lists] at member
    obtain ⟨epoch, slot, source, voted⟩ := holds before current pending member
    obtain ⟨low, high⟩ := recent_bounds state current
    have kept : CommitteesKept pending.data.target.epoch state { cached with slot := next } := by
      rw [epoch]
      refine committees ?_ low
      rw [previousEq]
      cases current
      · exact UInt64.le_refl _
      · exact getPreviousEpoch_le state
    refine ⟨by rw [currentEq, previousEq]; exact epoch, slot, ?_,
      votedAttesters_of kept slot voted⟩
    show pending.data.source = if current then cached.currentJustifiedCheckpoint
      else cached.previousJustifiedCheckpoint
    rw [cachedFrame.currentJustified, cachedFrame.previousJustified]
    exact source

/-- Before Altair, slots keep each pending attestation a vote of the set for its link.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The two justified checkpoints must be equal in the first two epochs before the slots. -/
theorem PendingVoted.of_advanceSlots {votes : Set (ValidatorIndex × AttestationData)}
    (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∀ {count : Nat} {state after : BeaconState preset fork}, JustifiedEarly state →
      PendingVoted votes state → advanceSlots config checks count state = .ok after →
        PendingVoted votes after
  | 0, state, after, _, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | count + 1, state, after, early, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact PendingVoted.of_advanceSlots before apart (early.of_advanceSlot nextOk)
      (holds.of_advanceSlot before apart early nextOk) rest

/-! ## The attesters that justification counts -/

/-- Before Altair, each attester that justification counts for an epoch cast a vote of the set.

That vote is for the link of that epoch.

The epoch is the current one when asked, and the previous one otherwise.

The attestations are those of the epoch whose target is the first block of the epoch.

Each unslashed member of their committees whose bit is set cast such a vote.

The attester is active in that epoch.

The two justified checkpoints must be equal in the first two epochs. -/
theorem PendingVoted.attester {votes : Set (ValidatorIndex × AttestationData)}
    (before : fork < .altair) (holds : PendingVoted votes state)
    (early : JustifiedEarly state) (current : Bool)
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingTargetAttestations state before
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    {indices : List ValidatorIndex}
    (counted : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      ∃ data, LinkVote state current index.toNat (index, data) ∧ (index, data) ∈ votes := by
  -- The attester is a member of the committee of one of the matching attestations.
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at counted
  obtain ⟨signers, signersOk, unslashed⟩ := counted
  have flattened := mem_sortedSet.mp (mem_of_filterM_ok unslashed member)
  obtain ⟨signed, signedMember, inside⟩ := List.mem_flatten.mp flattened
  obtain ⟨length, each⟩ := mapM_eq_ok_iff.mp signersOk
  obtain ⟨position, bound, rfl⟩ := List.getElem_of_mem signedMember
  have attestersOk := each position (length ▸ bound)
  have listed : attestations.toList[position]'(length ▸ bound) ∈ attestations.toList :=
    List.getElem_mem _
  generalize attestations.toList[position]'(length ▸ bound) = pending at attestersOk listed
  -- The attestation matches the target, and it is a pending vote of the list of the epoch.
  simp only [getMatchingTargetAttestations, bind_ok_iff] at matching
  obtain ⟨recent, recentOk, matching⟩ := matching
  split at matching
  · simp only [pure, Except.pure, Except.ok.injEq] at matching
    subst matching
    simp at listed
  simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at matching
  obtain ⟨root, rootOk, rfl⟩ := matching
  obtain ⟨found, sameRoot⟩ := Array.mem_filter.mp (Array.mem_toList_iff.mp listed)
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at recentOk
  obtain ⟨_, _, rfl⟩ := recentOk
  have previous := getPreviousEpoch_toNat state
  have facts : pending.data.target.epoch =
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
      pending.data.source = (if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint) ∧
      ∀ attesters, getPendingAttestingIndices state pending = .ok attesters →
        ∀ attester ∈ attesters, (attester, pending.data) ∈ votes := by
    by_cases here : (if current then getCurrentEpoch state else getPreviousEpoch state) =
        getCurrentEpoch state
    · simp only [here, ↓reduceIte] at found
      obtain ⟨epoch, slot, source, voted⟩ := holds before true pending found
      simp only [↓reduceIte] at epoch source
      refine ⟨epoch.trans here.symm, slot, ?_, voted⟩
      cases current
      · -- The previous epoch is the current one only in the first epoch, where both agree.
        simp only [Bool.false_eq_true, ↓reduceIte] at here ⊢
        have first : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := by
          have := congrArg UInt64.toNat here
          rw [previous] at this
          exact UInt64.le_iff_toNat_le.mpr (by simp [GENESIS_EPOCH]; omega)
        rw [early first]
        exact source
      · exact source
    · simp only [here, ↓reduceIte] at found
      cases current
      · obtain ⟨epoch, slot, source, voted⟩ := holds before false pending found
        exact ⟨epoch, slot, source, voted⟩
      · simp at here
  obtain ⟨epoch, slot, source, voted⟩ := facts
  simp only [getPendingAttestingIndices, bind_ok_iff] at attestersOk
  obtain ⟨committee, committeeOk, attestersOk⟩ := attestersOk
  have active := mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
    (mem_of_committeeAttesters attestersOk inside)
  rw [slot, epoch] at active
  have pendingOk : getPendingAttestingIndices state pending = .ok signers[position] := by
    simp only [getPendingAttestingIndices, committeeOk, bind, Except.bind]
    exact attestersOk
  refine ⟨active, pending.data, ⟨rfl, epoch, source, ?_⟩, voted _ pendingOk index inside⟩
  show getBlockRoot state pending.data.target.epoch = .ok pending.data.target.root
  rw [epoch, rootOk, beq_iff_eq.mp sameRoot]

end EthLib.Consensus

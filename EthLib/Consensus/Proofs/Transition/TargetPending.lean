module

public import EthLib.Consensus.Proofs.Transition.Committees
public import EthLib.Consensus.Proofs.Transition.TargetSlots
import all Init.Data.List.Control

/-!
# Proofs: before Altair, the attesters that justification counts signed the right link

Before Altair the state keeps the pending attestations of the current and the previous epoch.

Justification counts the stake of the unslashed members of their committees whose bit is set.

Of those, it counts only the attestations whose target is the first block of their epoch.

It reads each committee again in the state at the epoch step.

The committees of an epoch do not change while the epoch is recent, so it reads the same ones.

Each member of a committee whose bit is set then signed the data of the attestation.

Its target epoch is the epoch of its list, and its source the justified checkpoint of that epoch.

The epoch step moves the list of the current epoch to the previous epoch, with the checkpoints.

So justification before Altair counts only signed votes for the link of each epoch.

Reading a valid aggregate as the validator's signature assumes that no one forges a BLS aggregate.

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

/-- Before Altair, each pending attestation of the two epochs is a signed vote for their link.

Its target epoch is the epoch of its list, and the epoch of its slot.

Its source is the justified checkpoint that the state holds for that epoch.

Each member of its committee in the state whose bit is set signed its data in the state. -/
def PendingSigned (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Prop :=
  ∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
    pending.data.target.epoch =
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
      pending.data.source =
        (if current then state.currentJustifiedCheckpoint
        else state.previousJustifiedCheckpoint) ∧
      ∀ attesters, getPendingAttestingIndices state pending = .ok attesters →
        ∀ attester ∈ attesters, SignedVote config checks state (attester, pending.data)

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

/-- The attesters of a pending attestation stay signed in a state with the same committees.

That state must keep the keys and the genesis validators root. -/
private theorem signedAttesters_of {other : BeaconState preset fork}
    {pending : PendingAttestation preset}
    (committees : CommitteesKept pending.data.target.epoch state other)
    (slot : computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch)
    (genesisValidatorsRoot : other.genesisValidatorsRoot = state.genesisValidatorsRoot)
    (keys : KeysKept state other)
    (signed : ∀ attesters, getPendingAttestingIndices state pending = .ok attesters →
      ∀ attester ∈ attesters, SignedVote config checks state (attester, pending.data)) :
    ∀ attesters, getPendingAttestingIndices other pending = .ok attesters →
      ∀ attester ∈ attesters, SignedVote config checks other (attester, pending.data) := by
  intro attesters computed attester member
  unfold getPendingAttestingIndices at computed
  rw [committees _ _ slot] at computed
  exact (signed attesters computed attester member).of_keys (Nat.le_refl _) genesisValidatorsRoot
    keys

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

/-- Before Altair, a step of a block other than an attestation keeps the pending votes signed.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The registry must stay below 2^64 validators after the step. -/
theorem PendingSigned.of_pendingFrame
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (small : after.validators.data.size < 2 ^ 64) (frame : PendingFrame state after)
    (holds : PendingSigned config checks state) : PendingSigned config checks after := by
  intro before current pending member
  have lists : recentPending after before current = recentPending state before current := by
    cases current <;> simp [recentPending, frame.previousPending, frame.currentPending]
  rw [lists] at member
  obtain ⟨epoch, slot, source, signed⟩ := holds before current pending member
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  obtain ⟨low, high⟩ := recent_bounds state current
  have committees := CommitteesKept.of_activeKept apart (frame.active.mono low) frame.mixes low high
  rw [← epoch] at committees
  refine ⟨by rw [currentEq, previousEq]; exact epoch, slot,
    by rw [frame.currentJustified, frame.previousJustified]; exact source, ?_⟩
  exact signedAttesters_of committees slot frame.genesisValidatorsRoot (frame.keysKept small) signed

/-- Before Altair, an attestation keeps the pending votes signed, and adds a signed one.

The fork versions of the state must be those of forks of the chain. -/
theorem PendingSigned.of_processAttestation {parentSlot : Slot}
    {attestation : Attestation preset fork} (before : fork < .altair)
    (known : ForkVersionsKnown config state) (holds : PendingSigned config checks state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PendingSigned config checks after := by
  have frame := frame_processAttestation computed
  have registry := processAttestation_registry before computed
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  have notElectra : ¬Fork.pectra ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide : Fork.altair < Fork.pectra))
  have committees : ∀ epoch, CommitteesKept epoch state after := CommitteesKept.of_eq
    (congrArg (·.data) registry.1) (congrArg (·.elements) registry.2)
  have keys : KeysKept state after := by
    intro index validator found
    exact ⟨validator, by rw [getValidator_of_validators_eq registry.1]; exact found, rfl⟩
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [currentEq]
  -- A pending vote that was there keeps its epoch, source and signers.
  have kept : ∀ (current : Bool), ∀ pending ∈ recentPending state before current,
      pending.data.target.epoch =
          (if current then getCurrentEpoch after else getPreviousEpoch after) ∧
        computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch ∧
        pending.data.source =
          (if current then after.currentJustifiedCheckpoint
          else after.previousJustifiedCheckpoint) ∧
        ∀ attesters, getPendingAttestingIndices after pending = .ok attesters →
          ∀ attester ∈ attesters, SignedVote config checks after (attester, pending.data) := by
    intro current pending member
    obtain ⟨epoch, slot, source, signed⟩ := holds before current pending member
    exact ⟨by rw [currentEq, previousEq]; exact epoch, slot,
      by rw [frame.currentJustified, frame.previousJustified]; exact source,
      signedAttesters_of (committees _) slot frame.genesisValidatorsRoot keys signed⟩
  unfold processAttestation at computed
  simp only [notAltair, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, _, _, committee, committeeOk, _, _,
    proposer, _, _, source, updated, recorded, indexed, indexedOk, valid, validOk, _, accepted,
    rfl⟩ := computed
  subst accepted
  rw [liftAccessor_ok] at committeeOk indexedOk
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  intro before' current pending member
  generalize chosen : (attestation.data.target.epoch == getCurrentEpoch state) = target
    at added same source
  by_cases here : current = target
  · subst here
    rw [added] at member
    rcases Array.mem_push.mp member with old | rfl
    · exact kept _ pending old
    -- The new pending vote: its epoch, its source, and the signers of its indexed attestation.
    refine ⟨?_, slotEpoch.symm,
      by rw [frame.currentJustified, frame.previousJustified]; exact source,
      fun attesters attestersOk attester inside => ?_⟩
    · cases current
      · have other : attestation.data.target.epoch ≠ getCurrentEpoch state := ne_of_beq_false chosen
        simpa [previousEq] using recent.resolve_right other
      · simpa [currentEq] using beq_iff_eq.mp chosen
    · have committeeAfter : getBeaconCommittee updated attestation.data.slot
          attestation.data.index = .ok committee := by
        rw [committees _ _ _ rfl]
        exact committeeOk
      unfold getPendingAttestingIndices at attestersOk
      simp only [committeeAfter, bind, Except.bind] at attestersOk
      have signers : getAttestingIndices updated attestation =
          .ok (sortedSet attesters) := by
        simp only [getAttestingIndices, notElectra, ↓reduceDIte, committeeAfter, bind,
          Except.bind, attestersOk, pure, Except.pure]
      obtain ⟨indexed', indexedOk', indices, data, -⟩ :=
        getIndexedAttestation_of_getAttestingIndices signers
      rw [indexedOk] at indexedOk'
      cases indexedOk'
      exact SignedVote.of_valid ((ForkVersionsKnown.congr frame.forkVersions).mpr known)
        validOk (by rw [indices]; exact List.mem_toArray.mpr (mem_sortedSet.mpr inside)) data
  · have flipped : current = !target := by cases current <;> cases target <;> simp_all
    subst flipped
    rw [same] at member
    exact kept _ pending member

/-- Before Altair, a block keeps each pending vote signed for its link.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The registry must stay below 2^64 validators after the block.

The fork versions after the block must be those of forks of the chain. -/
theorem PendingSigned.of_processBlock (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {block : BeaconBlock preset fork} (small : after.validators.data.size < 2 ^ 64)
    (known : ForkVersionsKnown config after) (holds : PendingSigned config checks state)
    (computed : processBlock config checks engine state block = .ok after) :
    PendingSigned config checks after := by
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  have attestedFrame := Frame.foldlM (fun _ _ _ ok => frame_processAttestation ok) attested
  have small' : first.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.le_trans attestedFrame.registryGrows tail.registryGrows) small
  have known' : ForkVersionsKnown config first :=
    (ForkVersionsKnown.congr (tail.forkVersions.trans attestedFrame.forkVersions)).mp known
  have middle := foldlM_ok_invariant
    (fun next => PendingSigned config checks next ∧ Frame first next)
    (fun _ _ _ holds ok => ⟨holds.1.of_processAttestation before
        ((ForkVersionsKnown.congr holds.2.forkVersions).mpr known') ok,
      holds.2.trans (frame_processAttestation ok)⟩)
    ⟨holds.of_pendingFrame apart small' head, Frame.refl first⟩ attested
  exact middle.1.of_pendingFrame apart small tail

/-! ## Slots -/

/-- Before Altair, one slot keeps each pending vote signed for its link.

At the end of an epoch the votes of the current epoch become those of the previous one.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The two justified checkpoints must be equal in the first two epochs.

The registry must stay below 2^64 validators after the slot. -/
theorem PendingSigned.of_advanceSlot (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (early : JustifiedEarly state) (small : after.validators.data.size < 2 ^ 64)
    (holds : PendingSigned config checks state)
    (computed : advanceSlot config checks state = .ok after) :
    PendingSigned config checks after := by
  obtain ⟨-, genesisRoot, -, keys⟩ := advanceSlot_keys computed
  have committees := fun {epoch : Epoch} => committeesKept_advanceSlot (epoch := epoch) before apart
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
      obtain ⟨epoch, slot, source, signed⟩ := holds before true pending member
      simp only [↓reduceIte] at epoch source
      refine ⟨by simp only [Bool.false_eq_true, ↓reduceIte, previousEq]; exact epoch, slot, ?_, ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [source, frame.previousJustified, previousJustified, cachedFrame.currentJustified]
      · have kept : CommitteesKept pending.data.target.epoch state
            { epoched with slot := next } := by
          rw [epoch]
          exact committees (by rw [previousEq]; exact UInt64.le_refl _) (UInt64.le_refl _)
        exact signedAttesters_of kept slot genesisRoot (keys small) signed
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
    obtain ⟨epoch, slot, source, signed⟩ := holds before current pending member
    obtain ⟨low, high⟩ := recent_bounds state current
    have kept : CommitteesKept pending.data.target.epoch state { cached with slot := next } := by
      rw [epoch]
      refine committees ?_ low
      rw [previousEq]
      cases current
      · exact UInt64.le_refl _
      · exact getPreviousEpoch_le state
    refine ⟨by rw [currentEq, previousEq]; exact epoch, slot, ?_,
      signedAttesters_of kept slot genesisRoot (keys small) signed⟩
    show pending.data.source = if current then cached.currentJustifiedCheckpoint
      else cached.previousJustifiedCheckpoint
    rw [cachedFrame.currentJustified, cachedFrame.previousJustified]
    exact source

/-- Before Altair, slots keep each pending vote signed for its link.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The two justified checkpoints must be equal in the first two epochs before the slots.

The registry must stay below 2^64 validators after the slots. -/
theorem PendingSigned.of_advanceSlots (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∀ {count : Nat} {state after : BeaconState preset fork}, JustifiedEarly state →
      after.validators.data.size < 2 ^ 64 → PendingSigned config checks state →
      advanceSlots config checks count state = .ok after → PendingSigned config checks after
  | 0, state, after, _, _, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ holds
  | count + 1, state, after, early, small, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact PendingSigned.of_advanceSlots before apart (early.of_advanceSlot nextOk) small
      (holds.of_advanceSlot before apart early
        (Nat.lt_of_le_of_lt (advanceSlots_registryGrows rest) small) nextOk) rest

/-- Before Altair, a block that the transition accepts keeps each pending vote signed.

The slots before the block keep that, and so does the block itself.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes.

The two justified checkpoints must be equal in the first two epochs before the block.

The registry must stay below 2^64 validators after the block.

The fork versions after the block must be those of forks of the chain. -/
theorem PendingSigned.of_stateTransition (before : fork < .altair)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (early : JustifiedEarly state) (small : after.validators.data.size < 2 ^ 64)
    (known : ForkVersionsKnown config after) (holds : PendingSigned config checks state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    PendingSigned config checks after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, -, slotsOk⟩ := slotsOk
  have slots := PendingSigned.of_advanceSlots before apart early
    (Nat.lt_of_le_of_lt (frame_processBlock blockOk).registryGrows small) holds slotsOk
  exact slots.of_processBlock before apart small known blockOk

/-! ## The attesters that justification counts -/

/-- A filter that a computation runs keeps only elements of its list, or of what it started with.
-/
private theorem mem_of_filterAuxM_ok {ε α : Type} {test : α → Except ε Bool} :
    ∀ {list kept out : List α}, List.filterAuxM test list kept = .ok out →
      ∀ value ∈ out, value ∈ list ∨ value ∈ kept
  | [], kept, out, computed => by
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact fun _ member => .inr member
  | first :: rest, kept, out, computed => by
    simp only [List.filterAuxM, bind_ok_iff] at computed
    obtain ⟨chosen, _, computed⟩ := computed
    intro value member
    rcases mem_of_filterAuxM_ok computed value member with inside | earlier
    · exact .inl (List.mem_cons_of_mem first inside)
    · cases chosen
      · exact .inr earlier
      · rcases List.mem_cons.mp earlier with rfl | earlier
        · exact .inl List.mem_cons_self
        · exact .inr earlier

/-- A filter that a computation runs keeps only elements of its list. -/
private theorem mem_of_filterM_ok {ε α : Type} {test : α → Except ε Bool} {list out : List α}
    (computed : list.filterM test = .ok out) {value : α} (member : value ∈ out) :
    value ∈ list := by
  simp only [List.filterM, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, filtered, rfl⟩ := computed
  rcases mem_of_filterAuxM_ok filtered value (List.mem_reverse.mp member) with inside | none
  · exact inside
  · cases none

/-- Before Altair, each attester that justification counts for an epoch signed a vote for its link.

The epoch is the current one when asked, and the previous one otherwise.

The attestations are those of the epoch whose target is the first block of the epoch.

Each unslashed member of their committees whose bit is set signed such data.

The vote is for the link of that epoch, at the position of the attester.

The attester is active in that epoch.

The two justified checkpoints must be equal in the first two epochs. -/
theorem PendingSigned.attester (before : fork < .altair) (holds : PendingSigned config checks state)
    (early : JustifiedEarly state) (current : Bool)
    {attestations : Array (PendingAttestation preset)}
    (matching : getMatchingTargetAttestations state before
      (if current then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    {indices : List ValidatorIndex}
    (counted : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state
        (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
      ∃ data, LinkVote state current index.toNat (index, data) ∧
        SignedVote config checks state (index, data) := by
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
        ∀ attester ∈ attesters, SignedVote config checks state (attester, pending.data) := by
    by_cases here : (if current then getCurrentEpoch state else getPreviousEpoch state) =
        getCurrentEpoch state
    · simp only [here, ↓reduceIte] at found
      obtain ⟨epoch, slot, source, signed⟩ := holds before true pending found
      simp only [↓reduceIte] at epoch source
      refine ⟨epoch.trans here.symm, slot, ?_, signed⟩
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
      · obtain ⟨epoch, slot, source, signed⟩ := holds before false pending found
        exact ⟨epoch, slot, source, signed⟩
      · simp at here
  obtain ⟨epoch, slot, source, signed⟩ := facts
  simp only [getPendingAttestingIndices, bind_ok_iff] at attestersOk
  obtain ⟨committee, committeeOk, attestersOk⟩ := attestersOk
  have active := mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
    (mem_of_committeeAttesters attestersOk inside)
  rw [slot, epoch] at active
  have pendingOk : getPendingAttestingIndices state pending = .ok signers[position] := by
    simp only [getPendingAttestingIndices, committeeOk, bind, Except.bind]
    exact attestersOk
  refine ⟨active, pending.data, ⟨rfl, epoch, source, ?_⟩, signed _ pendingOk index inside⟩
  show getBlockRoot state pending.data.target.epoch = .ok pending.data.target.root
  rw [epoch, rootOk, beq_iff_eq.mp sameRoot]

end EthLib.Consensus

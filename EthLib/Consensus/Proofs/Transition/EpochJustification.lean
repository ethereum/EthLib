module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.EpochJustification

/-!
# Proofs: justification and finalization

The step finalizes only a checkpoint that was justified before it, or keeps the finalized one.

The old current justified checkpoint becomes the previous one.

The new current justified checkpoint is the old one, or that of the previous or the current epoch.

It is that of an epoch only when the test of that epoch passes.

Its root is then the block root that the state records for the first slot of that epoch.

The checkpoints of a state are in order when finalized, previous and current justified epochs grow.

The step keeps them in order when the current justified epoch is at most the previous epoch.

The finalized epoch then never decreases.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The finalized, previous justified and current justified epochs are in increasing order. -/
def CheckpointsOrdered (state : BeaconState preset fork) : Prop :=
  state.finalizedCheckpoint.epoch ≤ state.previousJustifiedCheckpoint.epoch ∧
    state.previousJustifiedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch

/-- The epochs whose pending attestations match a source are the current and the previous one. -/
theorem getMatchingSourceAttestations_epoch {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)}
    (computed : getMatchingSourceAttestations state before epoch = .ok attestations) :
    epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state := by
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, recent, _⟩ := computed
  exact recent

/-- A justified checkpoint is that of its epoch.

Its root is the block root that the state records for the first slot of the epoch.

Otherwise the checkpoint stays. -/
theorem justifyCheckpoint_ok {justified : Bool} {epoch : Epoch} {checkpoint result : Checkpoint}
    (computed : justifyCheckpoint state justified epoch checkpoint = .ok result) :
    (justified = true ∧ result.epoch = epoch ∧ getBlockRoot state epoch = .ok result.root) ∨
      (justified = false ∧ result = checkpoint) := by
  cases justified
  · simp only [justifyCheckpoint, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at computed
    exact .inr ⟨rfl, computed.symm⟩
  · simp only [justifyCheckpoint, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, rootOk, rfl⟩ := computed
    exact .inl ⟨rfl, rfl, rootOk⟩

/-- Weighing the votes justifies a new checkpoint only for an epoch whose test passes.

The new current justified checkpoint stays when neither test passes.

Otherwise it is that of the previous or the current epoch, whose test passes.

A test passes when twice the total balance is at most three times the target balance.

The root of the checkpoint is the block root that the state records for the first slot of the epoch.
-/
theorem weighJustificationAndFinalization_currentJustified
    {total previousBalance currentBalance : Gwei}
    (computed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after) :
    (after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
        ∀ (current : Bool) (threshold weight : Gwei), mulChecked total 2 = .ok threshold →
          mulChecked (if current then currentBalance else previousBalance) 3 = .ok weight →
          weight < threshold) ∨
      ∃ (current : Bool) (threshold weight : Gwei), mulChecked total 2 = .ok threshold ∧
        mulChecked (if current then currentBalance else previousBalance) 3 = .ok weight ∧
        threshold ≤ weight ∧
        after.currentJustifiedCheckpoint.epoch =
          (if current then getCurrentEpoch state else getPreviousEpoch state) ∧
        getBlockRoot state after.currentJustifiedCheckpoint.epoch =
          .ok after.currentJustifiedCheckpoint.root := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨previousWeight, previousOk, threshold, thresholdOk, first, firstOk, currentWeight,
    currentOk, second, secondOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
  dsimp only
  rcases justifyCheckpoint_ok secondOk with ⟨passed, epoch, rootOk⟩ | ⟨failedCurrent, rfl⟩
  · rw [epoch]
    exact .inr ⟨true, threshold, currentWeight, thresholdOk, currentOk,
      of_decide_eq_true passed, rfl, rootOk⟩
  rcases justifyCheckpoint_ok firstOk with ⟨passed, epoch, rootOk⟩ | ⟨failedPrevious, rfl⟩
  · rw [epoch]
    exact .inr ⟨false, threshold, previousWeight, thresholdOk, previousOk,
      of_decide_eq_true passed, rfl, rootOk⟩
  refine .inl ⟨rfl, fun current threshold' weight thresholdOk' weightOk => ?_⟩
  rw [thresholdOk, Except.ok.injEq] at thresholdOk'
  subst thresholdOk'
  cases current
  · simp only [Bool.false_eq_true, ↓reduceIte] at weightOk
    rw [previousOk, Except.ok.injEq] at weightOk
    subst weightOk
    exact UInt64.not_le.mp (of_decide_eq_false failedPrevious)
  · simp only [↓reduceIte] at weightOk
    rw [currentOk, Except.ok.injEq] at weightOk
    subst weightOk
    exact UInt64.not_le.mp (of_decide_eq_false failedCurrent)

/-- The checkpoints that weighing the votes sets.

The old current justified checkpoint becomes the previous one.

The new current justified checkpoint is the old one, or that of the previous or the current epoch.

The new finalized checkpoint is the old one, or one of the two old justified checkpoints.

Nothing else changes but the bits of justification. -/
theorem weighJustificationAndFinalization_checkpoints {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    after.previousJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      (after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
        after.currentJustifiedCheckpoint.epoch = getPreviousEpoch state ∨
        after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state) ∧
      (after.finalizedCheckpoint = state.finalizedCheckpoint ∨
        after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∨
        after.finalizedCheckpoint = state.currentJustifiedCheckpoint) ∧
      { after with
        previousJustifiedCheckpoint := state.previousJustifiedCheckpoint,
        currentJustifiedCheckpoint := state.currentJustifiedCheckpoint,
        justificationBits := state.justificationBits,
        finalizedCheckpoint := state.finalizedCheckpoint } = state := by
  have justified := weighJustificationAndFinalization_currentJustified computed
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
  refine ⟨rfl, ?_, ?_, rfl⟩
  · rcases justified with ⟨same, -⟩ | ⟨current, -, -, -, -, -, epoch, -⟩
    · exact .inl same
    · cases current
      · exact .inr (.inl epoch)
      · exact .inr (.inr epoch)
  · dsimp only
    split
    · exact .inr (.inr rfl)
    · split
      · exact .inr (.inl rfl)
      · exact .inl rfl

/-- A rule of finalization applies only when its epochs are justified and its gap matches. -/
theorem finalizes_eq_true {justified : Bool} {source gap currentEpoch : Epoch}
    (computed : finalizes justified source gap currentEpoch = .ok true) :
    justified = true ∧ source.toNat + gap.toNat = currentEpoch.toNat := by
  cases justified
  · simp [finalizes, pure, Except.pure] at computed
  · simp only [finalizes, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      pure, Except.pure, Except.ok.injEq, beq_iff_eq] at computed
    obtain ⟨sum, sumOk, rfl⟩ := computed
    exact ⟨rfl, ((addChecked_ok_iff.mp sumOk).2).symm⟩

/-- What weighing the votes does to the three newest bits and to the finalized checkpoint.

A set bit 0 means that the test of the current epoch passed.

Its checkpoint is then the new current justified one, with the root recorded for the epoch.

A set bit 1 means that the test of the previous epoch passed, or that the old bit 0 was set.

In the first case the state records a root for the previous epoch.

Bit 2 is the old bit 1.

The new finalized checkpoint is the old one, or an old justified one by one of the four rules.

The old current justified checkpoint needs at least bit 0, and also bit 1 when two back.

The old previous justified checkpoint needs at least bit 1, and also bit 2 when three back. -/
theorem weighJustificationAndFinalization_bits {total previousBalance currentBalance : Gwei}
    (computed : weighJustificationAndFinalization state total previousBalance currentBalance =
      .ok after) :
    ∃ threshold previousWeight currentWeight : Gwei, mulChecked total 2 = .ok threshold ∧
      mulChecked previousBalance 3 = .ok previousWeight ∧
      mulChecked currentBalance 3 = .ok currentWeight ∧
      (after.justificationBits.bits[0] = true → threshold ≤ currentWeight ∧
        ∃ root, getBlockRoot state (getCurrentEpoch state) = .ok root ∧
          after.currentJustifiedCheckpoint = ⟨getCurrentEpoch state, root⟩) ∧
      (after.justificationBits.bits[1] = true →
        (threshold ≤ previousWeight ∧
            ∃ root, getBlockRoot state (getPreviousEpoch state) = .ok root) ∨
          state.justificationBits.bits[0] = true) ∧
      after.justificationBits.bits[2] = state.justificationBits.bits[1] ∧
      (after.finalizedCheckpoint = state.finalizedCheckpoint ∨
        (after.finalizedCheckpoint = state.currentJustifiedCheckpoint ∧
          after.justificationBits.bits[0] = true ∧
          (state.currentJustifiedCheckpoint.epoch.toNat + 1 = (getCurrentEpoch state).toNat ∨
            (after.justificationBits.bits[1] = true ∧
              state.currentJustifiedCheckpoint.epoch.toNat + 2 = (getCurrentEpoch state).toNat))) ∨
        (after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∧
          after.justificationBits.bits[1] = true ∧
          (state.previousJustifiedCheckpoint.epoch.toNat + 2 = (getCurrentEpoch state).toNat ∨
            (after.justificationBits.bits[2] = true ∧
              state.previousJustifiedCheckpoint.epoch.toNat + 3 =
                (getCurrentEpoch state).toNat)))) := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨previousWeight, previousOk, threshold, thresholdOk, first, firstOk, currentWeight,
    currentOk, second, secondOk, a, aOk, b, bOk, c, cOk, d, dOk, afterEq⟩ := computed
  obtain ⟨bits, bitsEq⟩ : ∃ bits, bits = ((shiftJustificationBits state.justificationBits).set 1
      (decide (threshold ≤ previousWeight) || (shiftJustificationBits state.justificationBits)[1])
      (by decide)).set 0 (decide (threshold ≤ currentWeight)) (by decide) := ⟨_, rfl⟩
  have bitsAfter : after.justificationBits.bits = bits := by rw [bitsEq, ← afterEq]
  rw [← bitsEq] at aOk bOk cOk dOk
  have bit0 : bits[0] = decide (threshold ≤ currentWeight) := by
    simp [bitsEq]
  have bit1 : bits[1] = (decide (threshold ≤ previousWeight) ||
      state.justificationBits.bits[0]) := by
    simp [bitsEq, shiftJustificationBits]
  have bit2 : bits[2] = state.justificationBits.bits[1] := by
    simp [bitsEq, shiftJustificationBits]
  refine ⟨threshold, previousWeight, currentWeight, thresholdOk, previousOk, currentOk, ?_, ?_,
    ?_, ?_⟩
  · rw [bitsAfter, bit0]
    intro passed
    refine ⟨of_decide_eq_true passed, ?_⟩
    rcases justifyCheckpoint_ok secondOk with ⟨-, epoch, rootOk⟩ | ⟨failed, -⟩
    · refine ⟨second.root, epoch ▸ rootOk, ?_⟩
      rw [← afterEq, ← epoch]
    · rw [passed] at failed
      cases failed
  · rw [bitsAfter, bit1]
    intro set
    rcases Bool.or_eq_true_iff.mp set with passed | old
    · refine .inl ⟨of_decide_eq_true passed, ?_⟩
      rcases justifyCheckpoint_ok firstOk with ⟨-, -, rootOk⟩ | ⟨failed, -⟩
      · exact ⟨first.root, rootOk⟩
      · rw [passed] at failed
        cases failed
    · exact .inr old
  · rw [bitsAfter, bit2]
  have finalizedEq : after.finalizedCheckpoint =
      if c || d then state.currentJustifiedCheckpoint
      else if a || b then state.previousJustifiedCheckpoint
      else state.finalizedCheckpoint := by
    rw [← afterEq]
  rw [bitsAfter]
  by_cases byCurrent : (c || d) = true
  · simp only [byCurrent, ↓reduceIte] at finalizedEq
    refine .inr (.inl ⟨finalizedEq, ?_⟩)
    rcases Bool.or_eq_true_iff.mp byCurrent with two | one
    · obtain ⟨set, sum⟩ := finalizes_eq_true (two ▸ cOk)
      simp only [Bool.and_eq_true] at set
      exact ⟨set.1.1, .inr ⟨set.1.2, by simpa using sum⟩⟩
    · obtain ⟨set, sum⟩ := finalizes_eq_true (one ▸ dOk)
      simp only [Bool.and_eq_true] at set
      exact ⟨set.1, .inl (by simpa using sum)⟩
  simp only [byCurrent, Bool.false_eq_true, ↓reduceIte] at finalizedEq
  by_cases byPrevious : (a || b) = true
  · simp only [byPrevious, ↓reduceIte] at finalizedEq
    refine .inr (.inr ⟨finalizedEq, ?_⟩)
    rcases Bool.or_eq_true_iff.mp byPrevious with three | two
    · obtain ⟨set, sum⟩ := finalizes_eq_true (three ▸ aOk)
      simp only [Bool.and_eq_true] at set
      exact ⟨set.1.1, .inr ⟨set.1.2, by simpa using sum⟩⟩
    · obtain ⟨set, sum⟩ := finalizes_eq_true (two ▸ bOk)
      simp only [Bool.and_eq_true] at set
      exact ⟨set.1, .inl (by simpa using sum)⟩
  simp only [byPrevious, Bool.false_eq_true, ↓reduceIte] at finalizedEq
  exact .inl finalizedEq

/-- Weighing the votes keeps the checkpoints in order.

The current justified epoch must be at most the previous epoch.

The finalized epoch then does not decrease. -/
theorem weighJustificationAndFinalization_ordered {total previous current : Gwei}
    (ordered : CheckpointsOrdered state)
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain ⟨previousJustified, currentJustified, finalized, _⟩ :=
    weighJustificationAndFinalization_checkpoints computed
  obtain ⟨finalizedLe, previousLe⟩ := ordered
  have epochs := getPreviousEpoch_le state
  simp only [CheckpointsOrdered, UInt64.le_iff_toNat_le] at *
  rw [previousJustified]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rcases finalized with same | same | same <;> rw [same] <;> omega
  · rcases currentJustified with same | same | same <;> rw [same] <;> omega
  · rcases finalized with same | same | same <;> rw [same] <;> omega

/-- In the first two epochs, justification and finalization change nothing before Altair. -/
theorem processJustificationAndFinalization_early (before : fork < .altair)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1) :
    processJustificationAndFinalization state = .ok state := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp [processJustificationAndFinalization, notAltair, early, pure, Except.pure]

/-- The indices that the justification test of an epoch counts for its target.

From Altair they are the unslashed validators with the timely target flag.

Before Altair they are the unslashed attesters of the matching target attestations. -/
def targetIndices (state : BeaconState preset fork) (epoch : Epoch) :
    Except TransitionError (List ValidatorIndex) := do
  if altair : .altair ≤ fork then
    liftAccessor (getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch)
  else
    let pending ← getMatchingTargetAttestations state (Nat.lt_of_not_le altair) epoch
    liftAccessor (getUnslashedAttestingIndices state pending)

/-- The target indices come from the target flags from Altair.

Before Altair they come from the unslashed attesters of the matching target attestations. -/
theorem targetIndices_ok {epoch : Epoch} {indices : List ValidatorIndex}
    (computed : targetIndices state epoch = .ok indices) :
    (∃ altair : .altair ≤ fork,
      getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch = .ok indices) ∨
      ∃ (before : fork < .altair) (pending : _),
        getMatchingTargetAttestations state before epoch = .ok pending ∧
        getUnslashedAttestingIndices state pending = .ok indices := by
  unfold targetIndices at computed
  split at computed
  · exact .inl ⟨‹_›, liftAccessor_ok.mp computed⟩
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨pending, matching, indicesOk⟩ := computed
    exact .inr ⟨_, pending, matching, indicesOk⟩

/-- What a successful justification and finalization read, and what it did.

In the first two epochs it changed nothing.

Later it read the target indices of the previous and the current epoch and their balances.

It also read the total active balance, then weighed the three balances. -/
theorem processJustificationAndFinalization_reads
    (computed : processJustificationAndFinalization state = .ok after) :
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 ∧ after = state) ∨
      GENESIS_EPOCH + 1 < getCurrentEpoch state ∧
      ∃ (previous current : List ValidatorIndex) (total previousBalance currentBalance : Gwei),
        targetIndices state (getPreviousEpoch state) = .ok previous ∧
        targetIndices state (getCurrentEpoch state) = .ok current ∧
        getTotalActiveBalance state = .ok total ∧
        getTotalBalance state previous = .ok previousBalance ∧
        getTotalBalance state current = .ok currentBalance ∧
        weighJustificationAndFinalization state total previousBalance currentBalance =
          .ok after := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · rename_i early
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl ⟨early, computed.symm⟩
    · rename_i late
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
        previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
      refine .inr ⟨UInt64.not_le.mp late, previous, current, total, previousBalance,
        currentBalance, ?_, ?_, totalOk, previousBalanceOk, currentBalanceOk, weighed⟩
      · simpa [targetIndices, altair, liftAccessor_ok] using previousOk
      · simpa [targetIndices, altair, liftAccessor_ok] using currentOk
  · rename_i notAltair
    split at computed
    · rename_i early
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl ⟨early, computed.symm⟩
    · rename_i late
      -- Before Altair the attesting balance reads the unslashed attesters, then their balance.
      simp only [bind_ok_iff, liftAccessor_ok, getAttestingBalance] at computed
      obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
        ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩, currentBalance,
        ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
      refine .inr ⟨UInt64.not_le.mp late, previousIndices, currentIndices, total,
        previousBalance, currentBalance, ?_, ?_, totalOk, previousBalanceOk, currentBalanceOk,
        weighed⟩
      · simp only [targetIndices, notAltair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok]
        exact ⟨_, previousOk, previousIndicesOk⟩
      · simp only [targetIndices, notAltair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok]
        exact ⟨_, currentOk, currentIndicesOk⟩

/-- What a successful justification and finalization did.

It changed nothing in the first two epochs, and else weighed some target balances. -/
theorem processJustificationAndFinalization_ok
    (computed : processJustificationAndFinalization state = .ok after) :
    after = state ∨ ∃ total previous current,
      weighJustificationAndFinalization state total previous current = .ok after := by
  rcases processJustificationAndFinalization_reads computed with ⟨-, same⟩ |
    ⟨-, -, -, total, previous, current, -, -, -, -, -, weighed⟩
  · exact .inl same
  · exact .inr ⟨total, previous, current, weighed⟩

/-- Justification and finalization keep the slot. -/
theorem processJustificationAndFinalization_slot
    (computed : processJustificationAndFinalization state = .ok after) :
    after.slot = state.slot := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · rfl
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

/-- Justification and finalization keep the current justified checkpoint, or justify a recent one.

A recent epoch is the previous or the current epoch of the state before.

The root of the new checkpoint is the block root that this state records for the epoch. -/
theorem processJustificationAndFinalization_currentJustified
    (computed : processJustificationAndFinalization state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      (after.currentJustifiedCheckpoint.epoch = getPreviousEpoch state ∨
          after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state) ∧
        getBlockRoot state after.currentJustifiedCheckpoint.epoch =
          .ok after.currentJustifiedCheckpoint.root := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact .inl rfl
  rcases weighJustificationAndFinalization_currentJustified weighed with ⟨same, -⟩ |
    ⟨current, -, -, -, -, -, epoch, rootOk⟩
  · exact .inl same
  refine .inr ⟨?_, rootOk⟩
  cases current
  · exact .inl epoch
  · exact .inr epoch

/-- From Altair, in the first two epochs, justification and finalization change nothing. -/
theorem processJustificationAndFinalization_early_altair (altair : .altair ≤ fork)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1) :
    processJustificationAndFinalization state = .ok state := by
  simp [processJustificationAndFinalization, processJustificationAndFinalizationAltair, altair,
    early, pure, Except.pure]

/-- In the first two epochs, justification and finalization change nothing, at every fork. -/
theorem processJustificationAndFinalization_early_eq
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (computed : processJustificationAndFinalization state = .ok after) : after = state := by
  by_cases altair : Fork.altair ≤ fork
  · rw [processJustificationAndFinalization_early_altair altair early] at computed
    exact (Except.ok.inj computed).symm
  · rw [processJustificationAndFinalization_early (Nat.lt_of_not_le altair) early] at computed
    exact (Except.ok.inj computed).symm

/-- Justification and finalization keep the checkpoints in order.

The current justified epoch must be at most the previous epoch.

The finalized epoch then does not decrease. -/
theorem processJustificationAndFinalization_ordered (ordered : CheckpointsOrdered state)
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact ⟨ordered, UInt64.le_refl _⟩
  · exact weighJustificationAndFinalization_ordered ordered settled weighed

theorem sameSizes_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    SameSizes state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact SameSizes.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]
    exact SameSizes.refl _

end EthLib.Consensus

module

public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.FfgStake
public import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
public import EthLib.Consensus.Proofs.Transition.ParticipationFlagsKept
public import EthLib.Consensus.Proofs.Transition.RunKept
public import EthLib.Consensus.Proofs.Transition.TargetPending
import EthLib.Base.Proofs.FilterM
import EthLib.Consensus.Proofs.Transition.BlockRoots
import EthLib.Consensus.Proofs.Transition.Slot
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.Transition.TargetVotes

/-!
# Proofs: counted target votes justify their epoch at its end

An epoch transition justifies an epoch when active, unslashed voters of its target hold two thirds.

The voters count through their target flags from Altair, or through pending attestations before.

Slots inside an epoch and blocks keep those flags and attestations, and the epoch's block root.

So votes that a state of the epoch holds still count at the epoch's last slot.

Each pending attestation for a later epoch than the anchor's targets the epoch of its list.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Counted target votes justify at an epoch boundary -/

/-- A validator is not slashed in a state, read through its slashed flag. -/
def UnslashedAt (state : BeaconState preset fork) (v : ValidatorIndex) : Prop :=
  (slashedFlagAt state v.toNat).getD false = false

private theorem previousEpoch_ne_current (state : BeaconState preset fork)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    getPreviousEpoch state ≠ getCurrentEpoch state := by
  have previous := getPreviousEpoch_toNat state
  have late : 1 < (getCurrentEpoch state).toNat := counted
  intro same
  have := congrArg UInt64.toNat same
  omega

/-- An active index that is not slashed reads an unslashed validator. -/
private theorem unslashed_validator_of_active {state : BeaconState preset fork} {epoch : Epoch}
    {v : ValidatorIndex} (active : v ∈ getActiveValidatorIndices state epoch)
    (clean : UnslashedAt state v) :
    ∃ validator, getValidator state v = .ok validator ∧ validator.slashed = false := by
  have found := Array.getElem?_eq_getElem (lt_size_of_mem_getActiveValidatorIndices active)
  exact ⟨_, getValidator_eq_ok_iff.mpr found,
    by simpa [UnslashedAt, slashedFlagAt, found] using clean⟩

private theorem mem_unslashedAttesting_of_pending {state : BeaconState preset fork}
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (before : fork < .altair) (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (matching : getMatchingTargetAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok attestations)
    (read : getUnslashedAttestingIndices state attestations = .ok indices)
    {v : ValidatorIndex}
    (active : v ∈ getActiveValidatorIndices state
      (if recent then getCurrentEpoch state else getPreviousEpoch state))
    (clean : UnslashedAt state v)
    {pending : PendingAttestation preset} (member : pending ∈ recentPending state before recent)
    (target : pending.data.target.root = root) {signers : List ValidatorIndex}
    (signersOk : getPendingAttestingIndices state pending = .ok signers)
    (signed : v ∈ signers) : v ∈ indices := by
  have ne := previousEpoch_ne_current state counted
  have sourceOk : getMatchingSourceAttestations state before
      (if recent then getCurrentEpoch state else getPreviousEpoch state) =
        .ok (recentPending state before recent) := by
    cases recent <;> simp [getMatchingSourceAttestations, recentPending, ne, ensure, Functor.map,
      Except.map]
  have listed : pending ∈ attestations := by
    simp only [getMatchingTargetAttestations, sourceOk, bind, Except.bind] at matching
    split at matching
    · rename_i empty
      have := Array.isEmpty_iff.mp empty
      rw [this] at member
      simp at member
    · simp only [rootOk, liftAccessor, Except.mapError,
        pure, Except.pure, Except.ok.injEq] at matching
      subst attestations
      exact Array.mem_filter.mpr ⟨member, by simpa using target⟩
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at read
  obtain ⟨lists, listsOk, filtered⟩ := read
  obtain ⟨result, resultMem, resultOk⟩ := exists_mem_of_mapM_ok listsOk
    (Array.mem_toList_iff.mpr listed)
  have same := Except.ok.inj (signersOk.symm.trans resultOk)
  subst result
  have inSet : v ∈ sortedSet lists.flatten :=
    mem_sortedSet.mpr (List.mem_flatten.mpr ⟨signers, resultMem, signed⟩)
  have pass : (do return !(← getValidator state v).slashed) =
      (Except.ok true : Except AccessorError Bool) := by
    obtain ⟨validator, validatorOk, unslashed⟩ := unslashed_validator_of_active active clean
    simp [validatorOk, unslashed, Functor.map, Except.map]
  exact mem_filterM_ok_of_test filtered inSet pass

/-- Included active, unslashed target voters with two thirds of the total justify their epoch. -/
theorem processJustificationAndFinalization_justifies
    {state after : BeaconState preset fork}
    (computed : processJustificationAndFinalization state = .ok after)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {voters : Finset ValidatorIndex} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (quorum : 2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters)
    (voted : ∀ v ∈ voters,
      v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      UnslashedAt state v ∧
      ((∃ altair : .altair ≤ fork,
          TargetFlagAt (recentParticipation state altair recent) v.toNat) ∨
        ∃ before : fork < .altair, ∃ pending ∈ recentPending state before recent,
          pending.data.target.root = root ∧
          ∃ indices, getPendingAttestingIndices state pending = .ok indices ∧ v ∈ indices)) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  have enough : ∀ (indices : List ValidatorIndex) (balance : Gwei),
      getTotalBalance state indices = .ok balance → voters ⊆ indices.toFinset →
      2 * total.toNat ≤ 3 * balance.toNat := by
    intro indices balance balanceOk subset
    have value := (getTotalBalance_ok_iff_stake.mp balanceOk).2.2
    have lower := stake_mono (w := fun v => balanceAt state v.toNat) subset
    omega
  have late : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1 := UInt64.not_le.mpr counted
  unfold processJustificationAndFinalization at computed
  split at computed
  · rename_i altair
    simp only [processJustificationAndFinalizationAltair, late, ↓reduceIte, bind_ok_iff,
      liftAccessor_ok, totalOk, Except.ok.injEq, exists_eq_left'] at computed
    obtain ⟨previous, previousOk, current, currentOk, previousBalance, previousBalanceOk,
      currentBalance, currentBalanceOk, weighed⟩ := computed
    apply weighJustificationAndFinalization_justifies weighed recent
    have read : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
        (if recent then getCurrentEpoch state else getPreviousEpoch state) =
          .ok (if recent then current else previous) := by cases recent <;> assumption
    apply enough (if recent then current else previous) _ (by cases recent <;> assumption)
    intro v member
    obtain ⟨active, clean, flags | ⟨before, -⟩⟩ := voted v member
    · obtain ⟨_, flags, found, set⟩ := flags
      obtain ⟨validator, validatorOk, unslashed⟩ := unslashed_validator_of_active active clean
      exact List.mem_toFinset.mpr (mem_getUnslashedParticipatingIndices_of_recent_flag recent read
        (previousEpoch_ne_current state counted) active validatorOk unslashed found set)
    · exact False.elim (Nat.not_lt_of_ge altair before)
  · rename_i notAltair
    simp only [bind_ok_iff, liftAccessor_ok, totalOk, Except.ok.injEq,
      exists_eq_left', getAttestingBalance] at computed
    obtain ⟨previous, previousOk, current, currentOk, previousBalance,
      ⟨previousIndices, previousIndicesOk, previousBalanceOk⟩, currentBalance,
      ⟨currentIndices, currentIndicesOk, currentBalanceOk⟩, weighed⟩ := computed
    apply weighJustificationAndFinalization_justifies weighed recent
    apply enough (if recent then currentIndices else previousIndices) _
      (by cases recent <;> assumption)
    intro v member
    obtain ⟨active, clean, voted⟩ := voted v member
    rcases voted with ⟨altair, -⟩ | ⟨before, pending, member, target, indices, read, signed⟩
    · exact absurd altair notAltair
    · exact List.mem_toFinset.mpr (mem_unslashedAttesting_of_pending counted before recent rootOk
        (attestations := if recent then current else previous)
        (by cases recent <;> assumption) (by cases recent <;> assumption)
        active clean member target read signed)

/-- At the last slot, caching preserves the quorum that the epoch transition weighs. -/
theorem advanceSlot_justifies {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state)
    (recent : Bool) {root : Root}
    (rootOk : getBlockRoot state
      (if recent then getCurrentEpoch state else getPreviousEpoch state) = .ok root)
    {voters : Finset ValidatorIndex} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (quorum : 2 * total.toNat ≤ 3 * stake (fun v => balanceAt state v.toNat) voters)
    (voted : ∀ v ∈ voters,
      v ∈ getActiveValidatorIndices state
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      UnslashedAt state v ∧
      ((∃ altair : .altair ≤ fork,
          TargetFlagAt (recentParticipation state altair recent) v.toNat) ∨
        ∃ before : fork < .altair, ∃ pending ∈ recentPending state before recent,
          pending.data.target.root = root ∧
          ∃ indices, getPendingAttestingIndices state pending = .ok indices ∧ v ∈ indices)) :
    (if recent then getCurrentEpoch state else getPreviousEpoch state) ≤
      after.currentJustifiedCheckpoint.epoch := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
  change _ ≤ epoched.currentJustifiedCheckpoint.epoch
  rw [frame.currentJustified]
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have current : getCurrentEpoch cached = getCurrentEpoch state := by rw [cachedEq]; rfl
  have previous : getPreviousEpoch cached = getPreviousEpoch state := by rw [cachedEq]; rfl
  have roots : getBlockRoot cached
      (if recent then getCurrentEpoch cached else getPreviousEpoch cached) = .ok root := by
    rw [current, previous, getBlockRoot_processSlot cachedOk
      (slot_lt_epoch_add_historical positive window (by cases recent <;> simp))]
    exact rootOk
  have totalEq : getTotalActiveBalance cached = getTotalActiveBalance state := by
    rw [cachedEq]; rfl
  have balanceEq : ∀ index, balanceAt cached index = balanceAt state index := by
    intro index; rw [cachedEq]; rfl
  have result := processJustificationAndFinalization_justifies (voters := voters)
    justifiedOk (current.symm ▸ counted) recent roots (totalEq.trans totalOk) ?_ ?_
  · simpa [current, previous] using result
  · simpa only [balanceEq] using quorum
  · have activeEq : ∀ epoch, getActiveValidatorIndices cached epoch =
        getActiveValidatorIndices state epoch := by
      intro epoch
      rw [cachedEq]
      rfl
    have pendingEq : ∀ pending, getPendingAttestingIndices cached pending =
        getPendingAttestingIndices state pending := by
      intro pending
      rw [cachedEq]
      rfl
    intro v member
    obtain ⟨active, clean, flags | pending⟩ := voted v member
    · refine ⟨?_, ?_, .inl ?_⟩
      · rwa [current, previous, activeEq]
      · simpa [cachedEq, UnslashedAt, slashedFlagAt] using clean
      · simpa [cachedEq, recentParticipation] using flags
    · refine ⟨?_, ?_, .inr ?_⟩
      · rwa [current, previous, activeEq]
      · simpa [cachedEq, UnslashedAt, slashedFlagAt] using clean
      · obtain ⟨before, attestation, member, target, indices, read, signed⟩ := pending
        refine ⟨before, attestation, ?_, target, indices, ?_, signed⟩
        · simpa only [cachedEq, recentPending] using member
        · rw [pendingEq]
          exact read

/-- The last slot of an epoch past the first two reads the total active balance. -/
theorem advanceSlot_total_of_last {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (advanced : advanceSlot config checks state = .ok after)
    (lastSlot : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (counted : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, -⟩ := advanceSlot_ok advanced
  have boundary : next % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    simpa [UInt64.toNat_mod, sum] using lastSlot
  simp only [epochIfLast, boundary, ↓reduceIte] at epochedOk
  obtain ⟨justified, justifiedOk, -⟩ := processEpoch_frame epochedOk
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have current : getCurrentEpoch cached = getCurrentEpoch state := by rw [cachedEq]; rfl
  obtain ⟨total, totalOk⟩ := processJustificationAndFinalization_totalActiveBalance justifiedOk
      (current.symm ▸ counted)
  refine ⟨total, ?_⟩
  rw [cachedEq] at totalOk
  exact totalOk

/-! ## Votes kept inside an epoch -/

/-- In a state of an epoch or the next, the recent list chosen by that epoch is of that epoch. -/
theorem recentEpoch_eq {state : BeaconState preset fork} {epoch : Epoch}
    (lower : epoch ≤ getCurrentEpoch state)
    (upper : (getCurrentEpoch state).toNat < epoch.toNat + 2) :
    (if decide (getCurrentEpoch state = epoch) then getCurrentEpoch state
      else getPreviousEpoch state) = epoch := by
  by_cases same : getCurrentEpoch state = epoch
  · simp [same]
  · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte]
    have lowerNat := UInt64.le_iff_toNat_le.mp lower
    have ne : (getCurrentEpoch state).toNat ≠ epoch.toNat :=
      fun eq => same (UInt64.toNat_inj.mp eq)
    apply UInt64.toNat_inj.mp
    rw [getPreviousEpoch_toNat]
    omega

/-- A slot strictly inside an epoch is not followed by a boundary. -/
private theorem succ_mod_ne_zero_of_inside {s e n : ℕ} (low : e * n ≤ s)
    (high : s + 1 < (e + 1) * n) :
    (s + 1) % n ≠ 0 := by
  intro zero
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero zero
  have h1 : n * e < n * k := by rw [← hk, Nat.mul_comm]; omega
  have h2 : n * k < n * (e + 1) := by rw [← hk, Nat.mul_comm]; exact high
  have := Nat.lt_of_mul_lt_mul_left h1
  have := Nat.lt_of_mul_lt_mul_left h2
  omega

/-- A slot that ends no epoch caches roots and moves on, with any signature checks. -/
private theorem advanceSlot_inside_keeps {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after)
    (inside : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat ≠ 0) :
    (∀ other : SignatureChecks, advanceSlot config other state = .ok after) ∧
      (∀ altair current, recentParticipation after altair current =
        recentParticipation state altair current) ∧
      (∀ before current, recentPending after before current =
        recentPending state before current) := by
  have computed' := computed
  obtain ⟨next, cached, epoched, sum, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have notBoundary : ¬next % preset.SLOTS_PER_EPOCH = 0 := fun boundary =>
    inside (by simpa [UInt64.toNat_mod, sum] using congrArg UInt64.toNat boundary)
  have epochedEq : cached = epoched := by
    simpa [epochIfLast, notBoundary, pure, Except.pure] using epochedOk
  subst epochedEq
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  refine ⟨fun other => ?_, fun _ _ => by rw [cachedEq]; rfl,
    fun _ _ => by rw [cachedEq]; rfl⟩
  have epochOther : epochIfLast config other next cached = .ok cached := by
    simp [epochIfLast, notBoundary, pure, Except.pure]
  simp only [advanceSlot, bind_ok_iff] at computed' ⊢
  obtain ⟨next', nextOk, cached', cachedOk', epoched', -, done⟩ := computed'
  have same : cached' = cached := Except.ok.inj (cachedOk'.symm.trans cachedOk)
  subst same
  have nextSame : next' = next := by
    simp only [pure, Except.pure, Except.ok.injEq] at done
    have := congrArg BeaconState.slot done
    simpa using this
  subst nextSame
  exact ⟨next', nextOk, cached', cachedOk', cached', epochOther, rfl⟩

/-- Slots inside an epoch keep its recent root, target flags and pending attestations.

They give the same state with any signature checks. -/
theorem advanceSlots_keepsVotes {config : Config} {checks : SignatureChecks}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {epoch : Epoch} {root : Root} :
    ∀ {count : ℕ} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      state.slot.toNat + count <
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      (∀ other : SignatureChecks, advanceSlots config other count state = .ok after) ∧
      (RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current))
  | 0, state, after, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨fun _ => rfl, RunKept.refl _, rfl, fun _ read => read, fun _ _ _ _ flagged => flagged,
      fun _ _ _ member => member⟩
  | count + 1, state, after, computed, inside => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    have nextSlot := advanceSlot_slot nextOk
    have stateEpoch := getCurrentEpoch_toNat state
    have nextEpochNat := getCurrentEpoch_toNat next
    have low := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [← stateEpoch] at low
    have same : getCurrentEpoch next = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [nextEpochNat, nextSlot]
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.add_mul, Nat.one_mul]
        rw [Nat.add_mul, Nat.one_mul] at inside
        omega
    have nextInside : next.slot.toNat + count <
        ((getCurrentEpoch next).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
      rw [same, nextSlot]
      omega
    obtain ⟨others, run, epochEq, roots, flags, pendings⟩ :=
      advanceSlots_keepsVotes positive window (epoch := epoch) (root := root) rest nextInside
    have notLast := succ_mod_ne_zero_of_inside low (by omega)
    obtain ⟨nextOther, flagsEq, pendingEq⟩ := advanceSlot_inside_keeps nextOk notLast
    have step := runKept_advanceSlot nextOk
    refine ⟨fun other => ?_, step.trans run, epochEq.trans same, fun near read => ?_, ?_, ?_⟩
    · simp only [advanceSlots, bind_ok_iff]
      exact ⟨next, nextOther other, others other⟩
    · apply roots (same ▸ near)
      apply getBlockRoot_advanceSlot nextOk read
      rw [Nat.add_mul, Nat.one_mul] at inside
      have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat near
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · intro altair current position within flagged
      exact flags altair current position (Nat.lt_of_lt_of_le within step.grows)
        (by rw [flagsEq]; exact flagged)
    · intro before current pending member
      exact pendings before current pending (by rw [pendingEq]; exact member)

/-- Before Altair, an attestation keeps each pending attestation of both epochs. -/
private theorem processAttestation_keepsPending {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (before : fork < .altair)
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (current : Bool) {pending : PendingAttestation preset}
    (member : pending ∈ recentPending state before current) :
    pending ∈ recentPending after before current := by
  obtain ⟨_, _, _, _, _, recorded, _⟩ := processAttestation_records before computed
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  generalize (attestation.data.target.epoch == getCurrentEpoch state) = target at added same
  by_cases here : current = target
  · subst here
    rw [added]
    exact Array.mem_push_of_mem _ member
  · have flipped : current = !target := by cases current <;> cases target <;> simp_all
    subst flipped
    rw [same]
    exact member

/-- Before Altair, a block keeps each pending attestation of both epochs. -/
private theorem processBlock_keepsPending {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    (before : fork < .altair) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (current : Bool) {pending : PendingAttestation preset}
    (member : pending ∈ recentPending state before current) :
    pending ∈ recentPending after before current := by
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  rw [recentPending_pendingFrame tail before current]
  refine foldlM_ok_invariant (fun s => pending ∈ recentPending s before current)
    (fun _ _ _ holds ok => processAttestation_keepsPending before ok current holds) ?_
    attested
  rw [recentPending_pendingFrame head before current]
  exact member

/-- A block keeps the run, the epoch, each root, each target flag and each pending attestation. -/
theorem processBlock_keepsVotes
    {config : Config} {checks : SignatureChecks}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {state after : BeaconState preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    {epoch : Epoch} {root : Root} :
    RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current) := by
  have slotEq := processBlock_slot computed
  refine ⟨runKept_processBlock computed, by simp only [getCurrentEpoch, slotEq], ?_,
    fun altair current _ inside flagged =>
      TargetFlagAt.of_processBlock computed altair current inside flagged,
    fun before current _ member =>
      processBlock_keepsPending before computed current member⟩
  intro _ read
  unfold getBlockRoot at read ⊢
  simpa only [getBlockRootAtSlot_congr slotEq (processBlock_blockRoots computed)] using read

/-- A state that keeps an earlier state's votes passes them on through a step that keeps them. -/
theorem keptVotes_trans {first state after : BeaconState preset fork}
    {epoch : Epoch} {root : Root} {recent : Bool}
    (near : (getCurrentEpoch first).toNat ≤ epoch.toNat + 1)
    (kept : RunKept first state ∧ getCurrentEpoch state = getCurrentEpoch first ∧
      getBlockRoot state epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < first.validators.data.size →
        TargetFlagAt (recentParticipation first altair recent) position →
        TargetFlagAt (recentParticipation state altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending first before recent,
        pending ∈ recentPending state before recent))
    (step : RunKept state after ∧ getCurrentEpoch after = getCurrentEpoch state ∧
      ((getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → getBlockRoot state epoch = .ok root →
        getBlockRoot after epoch = .ok root) ∧
      (∀ (altair : .altair ≤ fork) (current : Bool) (position : ℕ),
        position < state.validators.data.size →
        TargetFlagAt (recentParticipation state altair current) position →
        TargetFlagAt (recentParticipation after altair current) position) ∧
      (∀ (before : fork < .altair) (current : Bool), ∀ pending ∈ recentPending state before current,
        pending ∈ recentPending after before current)) :
    RunKept first after ∧ getCurrentEpoch after = getCurrentEpoch first ∧
      getBlockRoot after epoch = .ok root ∧
      (∀ (altair : .altair ≤ fork) (position : ℕ), position < first.validators.data.size →
        TargetFlagAt (recentParticipation first altair recent) position →
        TargetFlagAt (recentParticipation after altair recent) position) ∧
      (∀ (before : fork < .altair), ∀ pending ∈ recentPending first before recent,
        pending ∈ recentPending after before recent) := by
  obtain ⟨run, epochEq, read, flags, pendings⟩ := kept
  obtain ⟨run', epochEq', roots, flags', pendings'⟩ := step
  exact ⟨run.trans run', epochEq'.trans epochEq, roots (epochEq ▸ near) read,
    fun altair position inside flagged => flags' altair recent position
      (Nat.lt_of_lt_of_le inside run.grows) (flags altair position inside flagged),
    fun before pending member => pendings' before recent pending (pendings before pending member)⟩

/-! ## Pending attestations after an epoch read their own epoch -/

/-- Each pending attestation of a list after the anchor epoch has that target epoch and slot. -/
def PendingAtOwnEpoch (anchorEpoch : Epoch) (state : BeaconState preset fork) : Prop :=
  ∀ (before : fork < .altair) (recent : Bool),
    anchorEpoch < (if recent then getCurrentEpoch state else getPreviousEpoch state) →
    ∀ pending ∈ recentPending state before recent,
      pending.data.target.epoch =
        (if recent then getCurrentEpoch state else getPreviousEpoch state) ∧
      computeEpochAtSlot preset pending.data.slot = pending.data.target.epoch

private theorem pendingAtOwnEpoch_frame {anchorEpoch : Epoch} {state after : BeaconState preset
    fork}
    (holds : PendingAtOwnEpoch anchorEpoch state) (frame : PendingFrame state after) :
    PendingAtOwnEpoch anchorEpoch after := by
  have current : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previous : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, current]
  intro before recent later pending member
  rw [recentPending_pendingFrame frame] at member
  rw [current, previous] at later ⊢
  exact holds before recent later pending member

private theorem pendingAtOwnEpoch_attestation {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {parentSlot : Slot} {attestation : Attestation preset fork}
    (before : fork < .altair) (holds : PendingAtOwnEpoch anchorEpoch state)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    PendingAtOwnEpoch anchorEpoch after := by
  have frame := voteFrame_processAttestation computed
  have currentEq : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, frame.slot]
  have previousEq : getPreviousEpoch after = getPreviousEpoch state := by
    simp only [getPreviousEpoch, currentEq]
  obtain ⟨recent, slotEpoch, -⟩ := processAttestation_checks before computed
  obtain ⟨pending, -, dataEq, -, -, recorded, -⟩ := processAttestation_records before computed
  obtain ⟨added, same⟩ := recordPendingAttestation_lists recorded
  intro before' current later other member
  rw [currentEq, previousEq] at later ⊢
  by_cases chosen : current = (attestation.data.target.epoch == getCurrentEpoch state)
  · rw [chosen, added] at member
    rcases Array.mem_push.mp member with old | rfl
    · rw [← chosen] at old
      exact holds before current later other old
    rw [dataEq]
    refine ⟨?_, slotEpoch.symm⟩
    cases current
    · have differ : attestation.data.target.epoch ≠ getCurrentEpoch state := by
        intro eq
        simp [eq] at chosen
      simpa using recent.resolve_right differ
    · simpa using (beq_iff_eq.mp chosen.symm)
  · have flipped : current = !(attestation.data.target.epoch == getCurrentEpoch state) := by
      revert chosen
      cases current <;> cases (attestation.data.target.epoch == getCurrentEpoch state) <;> simp
    rw [flipped, same, ← flipped] at member
    exact holds before current later other member

private theorem pendingAtOwnEpoch_block {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {block : BeaconBlock preset fork}
    (holds : PendingAtOwnEpoch anchorEpoch state)
    (computed : processBlock config checks engine state block = .ok after) :
    PendingAtOwnEpoch anchorEpoch after := by
  intro before
  obtain ⟨first, last, head, attested, tail⟩ := processBlock_pendingSplit before computed
  refine pendingAtOwnEpoch_frame ?_ tail before
  exact foldlM_ok_invariant (fun s => PendingAtOwnEpoch anchorEpoch s)
    (fun _ _ _ held ok => pendingAtOwnEpoch_attestation before held ok)
    (pendingAtOwnEpoch_frame holds head) attested

private theorem pendingAtOwnEpoch_advanceSlot {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    (holds : PendingAtOwnEpoch anchorEpoch state)
    (computed : advanceSlot config checks state = .ok after) :
    PendingAtOwnEpoch anchorEpoch after := by
  intro before current later pending member
  rcases recentPending_advanceSlot before computed with
    ⟨previousEq, -, moved, emptied⟩ | ⟨currentEq, previousEq, -, -, lists⟩
  · cases current
    · rw [moved] at member
      have prior : anchorEpoch < getCurrentEpoch state := by
        simpa only [Bool.false_eq_true, ↓reduceIte, previousEq] using later
      obtain ⟨epoch, slot⟩ := holds before true (by simpa using prior) pending member
      refine ⟨?_, slot⟩
      simpa [previousEq] using epoch
    · simp [emptied] at member
  · rw [lists] at member
    rw [currentEq, previousEq] at later ⊢
    exact holds before current later pending member

/-- A block's transition keeps each pending attestation at its own epoch. -/
theorem pendingAtOwnEpoch_stateTransition {anchorEpoch : Epoch} {config : Config}
    {checks : SignatureChecks} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : PendingAtOwnEpoch anchorEpoch state) (sound : Invariant state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    PendingAtOwnEpoch anchorEpoch after := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancing⟩ := slotsOk
  exact pendingAtOwnEpoch_block ((advanceSlots_invariant_of
    (fun s t => PendingAtOwnEpoch anchorEpoch s → PendingAtOwnEpoch anchorEpoch t) (fun _ kept =>
        kept)
    (fun _ one two kept => two (one kept)) (fun _ ok kept => pendingAtOwnEpoch_advanceSlot kept ok)
    sound advancing).2.2 holds) blockOk

end EthLib.Consensus

module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints

/-!
# Proofs: unrealized checkpoints are those of the next epoch

The fork choice runs justification and finalization on the state after a block.

The checkpoints it gets are the unrealized checkpoints of the block.

If no other block comes before the next epoch, the slot advance runs the same step at its end.

It weighs the same participation, the same balances and the same block roots.

So its checkpoints are the unrealized ones, also when the block slashed validators.

The block roots of the history must cover two epochs, as both presets do.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state tip after : BeaconState preset fork} {next : Slot}

section Helpers

open Serialization.Ssz Cryptography.Bls

/-! ## Justification reads the same values after the slots of an epoch -/

/-- A state that differs from another only in its slot, roots, header and payload availability. -/
private def Moved (state moved : BeaconState preset fork) : Prop :=
  ∃ (slot : Slot) (stateRoots blockRoots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (header : BeaconBlockHeader)
    (availability : Since .glamsterdam fork (ExecutionPayloadAvailability preset)),
    moved = { state with
      slot := slot
      stateRoots := stateRoots
      blockRoots := blockRoots
      latestBlockHeader := header
      executionPayloadAvailability := availability }

/-- The same epoch gives the same previous epoch. -/
private theorem previous_eq {moved : BeaconState preset fork}
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) :
    getPreviousEpoch moved = getPreviousEpoch state := by
  unfold getPreviousEpoch
  rw [epoch]

/-- From Altair, the participating validators are the same in both states. -/
private theorem participating_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) {altair : .altair ≤ fork}
    {flag : UInt64} {target : Epoch} :
    getUnslashedParticipatingIndices moved altair flag target =
      getUnslashedParticipatingIndices state altair flag target := by
  have previous := previous_eq epoch
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  unfold getUnslashedParticipatingIndices
  rw [epoch, previous]
  rfl

/-- The total active balance is the same in both states. -/
private theorem totalActive_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) :
    getTotalActiveBalance moved = getTotalActiveBalance state := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  unfold getTotalActiveBalance
  rw [epoch]
  rfl

/-- Both states give the same root for the first block of the previous or the current epoch.

This holds whenever both of them read that root. -/
private def SameRoots (state moved : BeaconState preset fork) : Prop :=
  ∀ {target : Epoch} {root root' : Root},
    (target = getPreviousEpoch state ∨ target = getCurrentEpoch state) →
    getBlockRoot state target = .ok root → getBlockRoot moved target = .ok root' → root' = root

/-- Two states with the same three checkpoints and the same justification bits. -/
private def SameOutcome (tip tip' : BeaconState preset fork) : Prop :=
  tip'.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint ∧
    tip'.previousJustifiedCheckpoint = tip.previousJustifiedCheckpoint ∧
    tip'.finalizedCheckpoint = tip.finalizedCheckpoint ∧
    tip'.justificationBits = tip.justificationBits

/-- A justified epoch gets the same checkpoint in both states. -/
private theorem justify_eq {moved : BeaconState preset fork} (roots : SameRoots state moved)
    {justified : Bool} {target : Epoch} {checkpoint first second : Checkpoint}
    (recent : target = getPreviousEpoch state ∨ target = getCurrentEpoch state)
    (one : justifyCheckpoint state justified target checkpoint = .ok first)
    (two : justifyCheckpoint moved justified target checkpoint = .ok second) : second = first := by
  unfold justifyCheckpoint at one two
  cases justified
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at one two
    rw [← one, ← two]
  · simp only [↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at one two
    obtain ⟨root, rootOk, rfl⟩ := one
    obtain ⟨root', rootOk', rfl⟩ := two
    rw [roots recent rootOk rootOk']

/-- Weighing the same balances gives the same checkpoints and bits in both states. -/
private theorem weigh_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    {total previousBalance currentBalance : Gwei}
    (one : weighJustificationAndFinalization state total previousBalance currentBalance = .ok tip)
    (two : weighJustificationAndFinalization moved total previousBalance currentBalance =
      .ok after) : SameOutcome tip after := by
  have previous := previous_eq epoch
  unfold weighJustificationAndFinalization at one two
  rw [epoch, previous] at two
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at one two
  obtain ⟨w1, hw1, th, hth, j1, hj1, w2, hw2, j2, hj2, f1, hf1, f2, hf2, f3, hf3, f4, hf4,
    rfl⟩ := one
  obtain ⟨w1', hw1', th', hth', j1', hj1', w2', hw2', j2', hj2', f1', hf1', f2', hf2', f3', hf3',
    f4', hf4', rfl⟩ := two
  cases hw1.symm.trans hw1'
  cases hth.symm.trans hth'
  cases hw2.symm.trans hw2'
  cases justify_eq roots (.inl rfl) hj1 hj1'
  cases justify_eq roots (.inr rfl) hj2 hj2'
  cases hf1.symm.trans hf1'
  cases hf2.symm.trans hf2'
  cases hf3.symm.trans hf3'
  cases hf4.symm.trans hf4'
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Before Altair, the balance of the signers is the same in both states. -/
private theorem attestingBalance_eq {moved : BeaconState preset fork} (same : Moved state moved)
    {attestations : Array (PendingAttestation preset)} :
    getAttestingBalance moved attestations = getAttestingBalance state attestations := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  rfl

/-- Before Altair, the votes for the first block of an epoch are the same in both states. -/
private theorem matchingTarget_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    {before : fork < .altair} {target : Epoch} {first second : Array (PendingAttestation preset)}
    (recent : target = getPreviousEpoch state ∨ target = getCurrentEpoch state)
    (one : getMatchingTargetAttestations state before target = .ok first)
    (two : getMatchingTargetAttestations moved before target = .ok second) : second = first := by
  have previous := previous_eq epoch
  have source : getMatchingSourceAttestations moved before target =
      getMatchingSourceAttestations state before target := by
    obtain ⟨_, _, _, _, _, rfl⟩ := same
    unfold getMatchingSourceAttestations
    rw [epoch, previous]
  unfold getMatchingTargetAttestations at one two
  rw [source] at two
  simp only [bind_ok_iff] at one two
  obtain ⟨found, foundOk, one⟩ := one
  obtain ⟨found', foundOk', two⟩ := two
  cases foundOk.symm.trans foundOk'
  by_cases empty : found.isEmpty
  · simp only [empty, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at one two
    rw [← one, ← two]
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at one two
    obtain ⟨root, rootOk, rfl⟩ := one
    obtain ⟨root', rootOk', rfl⟩ := two
    rw [roots recent rootOk rootOk']

/-- Justification on a moved state with the same epoch and roots ends the same way. -/
private theorem justification_eq {moved : BeaconState preset fork} (same : Moved state moved)
    (epoch : getCurrentEpoch moved = getCurrentEpoch state) (roots : SameRoots state moved)
    (one : processJustificationAndFinalization state = .ok tip)
    (two : processJustificationAndFinalization moved = .ok after) : SameOutcome tip after := by
  have previous := previous_eq epoch
  unfold processJustificationAndFinalization at one two
  split at one
  · rename_i altair
    simp only [altair, ↓reduceDIte] at two
    unfold processJustificationAndFinalizationAltair at one two
    rw [epoch] at two
    split at one
    · rename_i early
      simp only [early, ↓reduceIte] at two
      simp only [pure, Except.pure, Except.ok.injEq] at one two
      subst one two
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact ⟨rfl, rfl, rfl, rfl⟩
    rename_i late
    simp only [late, ↓reduceIte, previous, participating_eq same epoch,
      totalActive_eq same epoch] at two
    simp only [bind_ok_iff, liftAccessor_ok] at one two
    obtain ⟨p, hp, c, hc, t, ht, pb, hpb, cb, hcb, one⟩ := one
    obtain ⟨p', hp', c', hc', t', ht', pb', hpb', cb', hcb', two⟩ := two
    cases hp.symm.trans hp'
    cases hc.symm.trans hc'
    cases ht.symm.trans ht'
    have hpb'' : getTotalBalance state p = .ok pb' := by
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact hpb'
    have hcb'' : getTotalBalance state c = .ok cb' := by
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact hcb'
    cases hpb.symm.trans hpb''
    cases hcb.symm.trans hcb''
    exact weigh_eq same epoch roots one two
  · rename_i altair
    simp only [altair, ↓reduceDIte, epoch] at two
    split at one
    · rename_i early
      simp only [early, ↓reduceIte] at two
      simp only [pure, Except.pure, Except.ok.injEq] at one two
      subst one two
      obtain ⟨_, _, _, _, _, rfl⟩ := same
      exact ⟨rfl, rfl, rfl, rfl⟩
    rename_i late
    simp only [late, ↓reduceIte, previous, totalActive_eq same epoch,
      attestingBalance_eq same] at two
    simp only [bind_ok_iff, liftAccessor_ok] at one two
    obtain ⟨p, hp, c, hc, t, ht, pb, hpb, cb, hcb, one⟩ := one
    obtain ⟨p', hp', c', hc', t', ht', pb', hpb', cb', hcb', two⟩ := two
    cases matchingTarget_eq same epoch roots (.inl rfl) hp hp'
    cases matchingTarget_eq same epoch roots (.inr rfl) hc hc'
    cases ht.symm.trans ht'
    cases hpb.symm.trans hpb'
    cases hcb.symm.trans hcb'
    exact weigh_eq same epoch roots one two

/-! ## The slots up to the end of the epoch -/

/-- The moved state reads the same block roots at the slots before the original one.

Only slots from the start of the previous epoch count. -/
private def KeepsRoots (state moved : BeaconState preset fork) : Prop :=
  ∀ slot : Slot, slot.toNat < state.slot.toNat →
    ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat →
    readCircular moved.blockRoots.elements slot = readCircular state.blockRoots.elements slot

/-- A read of a block root is before the slot of the state, and reads the buffer of roots. -/
private theorem getBlockRootAtSlot_read {slot : Slot} {root : Root}
    (computed : getBlockRootAtSlot state slot = .ok root) :
    slot < state.slot ∧ readCircular state.blockRoots.elements slot = .ok root := by
  unfold getBlockRootAtSlot at computed
  by_cases lt : slot < state.slot
  · simp only [lt, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact ⟨lt, computed⟩
    · cases computed
  · simp only [lt, ↓reduceIte, bind_ok_iff] at computed
    obtain ⟨_, thrown, _⟩ := computed
    cases thrown

/-- Roots kept from the start of the previous epoch are the same roots for justification. -/
private theorem sameRoots_of (keeps : KeepsRoots state moved) : SameRoots state moved := by
  intro target root root' recent one two
  unfold getBlockRoot at one two
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at one two
  obtain ⟨slot, start, one⟩ := one
  obtain ⟨slot', start', two⟩ := two
  cases start.symm.trans start'
  obtain ⟨lt, read⟩ := getBlockRootAtSlot_read one
  obtain ⟨-, read'⟩ := getBlockRootAtSlot_read two
  have low : ((getCurrentEpoch state).toNat - 1) * preset.SLOTS_PER_EPOCH.toNat ≤ slot.toNat := by
    rw [(mulChecked_ok_iff.mp start).2]
    apply Nat.mul_le_mul_right
    rcases recent with rfl | rfl
    · rw [getPreviousEpoch_toNat]
    · exact Nat.sub_le _ _
  rw [keeps slot (UInt64.lt_iff_toNat_lt.mp lt) low, read] at read'
  exact (Except.ok.inj read').symm

/-- The caching of a slot writes one block root, at the position of the slot. -/
private theorem processSlot_blockRoots {cached : BeaconState preset fork}
    (computed : processSlot moved = .ok cached) :
    ∃ root, writeCircular moved.blockRoots.elements moved.slot root =
      .ok cached.blockRoots.elements := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, root, _, blockRoots, written, computed⟩ := computed
  have elements := writeCircularRooted_elements moved.blockRoots moved.slot root
  rw [written] at elements
  refine ⟨root, ?_⟩
  split at computed
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    exact elements.symm
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact elements.symm

/-- The caching of a slot keeps a moved state moved. -/
private theorem Moved.processSlot {cached : BeaconState preset fork} (same : Moved state moved)
    (computed : processSlot moved = .ok cached) : Moved state cached := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  exact ⟨_, _, _, _, _, rfl⟩

/-- A new slot keeps a moved state moved. -/
private theorem Moved.slot (same : Moved state moved) (slot : Slot) :
    Moved state { moved with slot } := by
  obtain ⟨_, _, _, _, _, rfl⟩ := same
  exact ⟨_, _, _, _, _, rfl⟩

/-- Two numbers that differ by less than a length lie at different positions modulo it. -/
private theorem mod_ne {low high length : Nat} (lt : low < high) (close : high - low < length) :
    high % length ≠ low % length := by
  intro same
  have zero := Nat.sub_mod_eq_zero_of_mod_eq same
  rw [Nat.mod_eq_of_lt close] at zero
  omega

/-- The first slot of the epoch of a state is at most its slot. -/
private theorem epoch_bounds (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat := by
  rw [getCurrentEpoch_toNat]
  exact Nat.div_mul_le_self _ _

/-- The caching of a slot keeps the roots that the original state reads.

The slot must be in the epoch of the original state, from its slot on. -/
private theorem KeepsRoots.processSlot {cached : BeaconState preset fork}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (keeps : KeepsRoots state moved) (computed : processSlot moved = .ok cached)
    (low : state.slot.toNat ≤ moved.slot.toNat)
    (high : moved.slot.toNat < ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat) :
    KeepsRoots state cached := by
  intro slot lt lo
  obtain ⟨root, written⟩ := processSlot_blockRoots computed
  rw [readCircular_writeCircular_of_ne written, keeps slot lt lo]
  intro same
  have same' := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
  have start := epoch_bounds state
  rw [Nat.add_mul, Nat.one_mul] at high
  rw [Nat.sub_mul, Nat.one_mul] at lo
  exact mod_ne (by omega) (by omega) same'

/-- The slots up to the first slot of the next epoch end as justification on the original state.

The last of them runs the epoch transition, on a state that reads the same values. -/
private theorem advanceSlots_outcome
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip) :
    ∀ {count : Nat} {moved after : BeaconState preset fork}, Moved state moved →
      KeepsRoots state moved → state.slot.toNat ≤ moved.slot.toNat →
      moved.slot.toNat + count + 1 =
        ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat →
      advanceSlots config checks (count + 1) moved = .ok after → SameOutcome tip after
  | count, moved, after, same, keeps, low, total, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨stepped, steppedOk, rest⟩ := computed
    simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at steppedOk
    obtain ⟨nextSlot, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := steppedOk
    simp only [UInt64.toNat_one] at sum
    have cachedSlot := processSlot_slot cachedOk
    have cachedSame := same.processSlot cachedOk
    have cachedKeeps := keeps.processSlot window cachedOk low (by omega)
    have start := epoch_bounds state
    have stateEpoch := getCurrentEpoch_toNat state
    rw [Nat.add_mul, Nat.one_mul] at total
    have epoch : getCurrentEpoch cached = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [getCurrentEpoch_toNat cached, cachedSlot]
      exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    unfold epochIfLast at epochedOk
    cases count with
    | zero =>
      simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at rest
      subst rest
      have boundary : nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero, show moved.slot.toNat + 1 =
          ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat by
            rw [Nat.add_mul, Nat.one_mul]; omega]
        exact Nat.mul_mod_left _ _
      simp only [boundary, ↓reduceIte] at epochedOk
      obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
      obtain ⟨current, previous, finalized, justificationBits⟩ :=
        justification_eq cachedSame epoch (sameRoots_of cachedKeeps) pulled justifiedOk
      exact ⟨frame.currentJustified.trans current, frame.previousJustified.trans previous,
        frame.finalized.trans finalized, frame.justificationBits.trans justificationBits⟩
    | succ count =>
      have notBoundary : ¬ nextSlot % preset.SLOTS_PER_EPOCH = 0 := by
        intro boundary
        have zero := congrArg UInt64.toNat boundary
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero] at zero
        have split := Nat.div_add_mod (moved.slot.toNat + 1) preset.SLOTS_PER_EPOCH.toNat
        rw [zero, Nat.add_zero, Nat.div_eq_of_lt_le (k := (getCurrentEpoch state).toNat)
          (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega), Nat.mul_comm] at split
        omega
      simp only [notBoundary, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact advanceSlots_outcome window pulled (cachedSame.slot nextSlot) cachedKeeps
        (by simp only; omega) (by simp only; rw [Nat.add_mul, Nat.one_mul]; omega) rest

end Helpers

/-- Advance a state to the first slot of the next epoch, with no block on the way.

Its justified and finalized checkpoints are then those of the state after justification.

Its justification bits are also those of that state.

That step reads the same participation, balances and block roots as the epoch transition.

The theorem assumes that the block roots of the history cover two epochs, as both presets do.

The bound is on natural numbers, since twice the slots of an epoch could overflow 64 bits. -/
theorem processSlots_checkpoints_eq_of_justification
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : processJustificationAndFinalization state = .ok tip)
    (start : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok next)
    (advanced : processSlots config checks state next = .ok after) :
    after.currentJustifiedCheckpoint = tip.currentJustifiedCheckpoint ∧
      after.previousJustifiedCheckpoint = tip.previousJustifiedCheckpoint ∧
      after.finalizedCheckpoint = tip.finalizedCheckpoint ∧
      after.justificationBits = tip.justificationBits := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at advanced
  obtain ⟨_, lt, advanced⟩ := advanced
  have lt' := UInt64.lt_iff_toNat_lt.mp lt
  have nextValue : next.toNat =
      ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    rw [(mulChecked_ok_iff.mp start).2, UInt64.toNat_add, UInt64.toNat_one]
    have bounded := (getCurrentEpoch state).toNat_lt
    by_cases full : (getCurrentEpoch state).toNat + 1 < 2 ^ 64
    · rw [Nat.mod_eq_of_lt full]
    · have wrapped : ((getCurrentEpoch state).toNat + 1) % 2 ^ 64 = 0 := by omega
      rw [(mulChecked_ok_iff.mp start).2, UInt64.toNat_add, UInt64.toNat_one, wrapped,
        Nat.zero_mul] at lt'
      omega
  obtain ⟨count, counted⟩ : ∃ count, next.toNat - state.slot.toNat = count + 1 :=
    ⟨next.toNat - state.slot.toNat - 1, by omega⟩
  rw [counted] at advanced
  exact advanceSlots_outcome (moved := state) window pulled
    ⟨state.slot, state.stateRoots, state.blockRoots, state.latestBlockHeader,
      state.executionPayloadAvailability, rfl⟩
    (fun _ _ _ => rfl) (Nat.le_refl _) (by omega) advanced

/-- The pulled-up tip of a block records the justified checkpoint of the next epoch.

The state of the block must advance to the first slot of the next epoch.

The store records no finalized checkpoint for each block; the previous theorem covers that one.

The theorem assumes that the block roots of the history cover two epochs, as both presets do. -/
theorem Store.computePulledUpTip_unrealizedJustification {store pulledStore : Store preset fork}
    {root : Root}
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (pulled : store.computePulledUpTip config root = .ok pulledStore)
    (stateOk : store.blockState root = .ok state)
    (start : computeStartSlotAtEpoch preset (getCurrentEpoch state + 1) = .ok next)
    (advanced : processSlots config checks state next = .ok after) :
    pulledStore.unrealizedJustifications[root]? = some after.currentJustifiedCheckpoint := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨found, foundOk, tip, weighed, block, -, epoch, -, pulled⟩ := pulled
  rw [stateOk, Except.ok.injEq] at foundOk
  subst foundOk
  rw [(processSlots_checkpoints_eq_of_justification window (Base.mapError_ok_iff.mp weighed)
    start advanced).1]
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled <;>
    simp only [updateCheckpoints, updateUnrealizedCheckpoints] <;> split_ifs <;> simp

end EthLib.Consensus

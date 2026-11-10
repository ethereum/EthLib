module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.Totality.Bound
import EthLib.Base.Proofs.FilterM

/-!
# Proofs: justification and finalization of an epoch succeed

The step sums the active balance and the balances that vote for the previous and current targets.

It triples each target balance and doubles the active balance, with checked products.

It reads the root of the first block of a recent epoch, to match targets or to justify it.

It adds a gap to a checkpoint epoch.

Each of these can fail, so the step succeeds only under bounds.

The step runs at the last slot of an epoch.

The first slot of the current epoch is then before the slot of the state, given two slots an epoch.

The first slot of the previous epoch is within the buffer of block roots, if it is long enough.

The invariant keeps the justified epochs at most the previous epoch, so the sums of epochs fit.

From Altair the votes are flags, one per validator, so the lists of flags must match the registry.

Before Altair the votes are pending attestations, whose signers come from committees.

The theorem takes as a hypothesis that the committee and the signers of each one succeed.

Its signers are then members of a committee, so validators of the registry.

The invariant of the state transition does not carry it yet, nor the one on the lists of flags.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- Before Altair, the committee and the signers of each recent pending attestation succeed.

The recent ones are those of the previous and the current epoch.

Inclusion in a block checked both, against the committee of the attestation. -/
def PendingResolved (state : BeaconState preset fork) : Prop :=
  ∀ before : fork < .altair, ∀ attestation,
    attestation ∈ (state.previousEpochAttestations before).data ∨
      attestation ∈ (state.currentEpochAttestations before).data →
    ∃ signers, getPendingAttestingIndices state attestation = .ok signers

/-- A step followed by a continuation succeeds when the step does and every continuation does. -/
private theorem bind_exists_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β}
    (first : ∃ a, x = .ok a) (rest : ∀ a, ∃ b, g a = .ok b) : ∃ b, x >>= g = .ok b := by
  obtain ⟨a, rfl⟩ := first
  exact rest a

/-- At the last slot of an epoch, the slot is one less than a whole number of epochs after. -/
theorem slot_mod_eq_of_last (epochSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0) :
    state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat = preset.SLOTS_PER_EPOCH.toNat - 1 := by
  have below := Nat.mod_lt state.slot.toNat (by omega : 0 < preset.SLOTS_PER_EPOCH.toNat)
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < preset.SLOTS_PER_EPOCH.toNat)] at last
  by_cases short :
      state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat + 1 < preset.SLOTS_PER_EPOCH.toNat
  · rw [Nat.mod_eq_of_lt short] at last
    omega
  · omega

/-- At the last slot of an epoch, the block root at the first slot of a recent epoch succeeds.

A recent epoch is the previous or the current one.

An epoch must have two slots at least, and the buffer of block roots must reach the epoch before.

The slot plus the length of the buffer of block roots must be below 2^64. -/
theorem getBlockRoot_exists_ok (roots : preset.RootsReachPreviousEpoch)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64) {epoch : Epoch}
    (recent : epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state) :
    ∃ root, getBlockRoot state epoch = .ok root := by
  have twoSlots := roots.twoSlots
  have reach := roots.reach
  have decomposed := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  rw [slot_mod_eq_of_last twoSlots last] at decomposed
  have current := getCurrentEpoch_toNat state
  have previous := getPreviousEpoch_toNat state
  have value : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ∨
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat =
        (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat -
          preset.SLOTS_PER_EPOCH.toNat := by
    rcases recent with rfl | rfl
    · right
      rw [previous, Nat.sub_mul, Nat.one_mul]
    · exact .inl rfl
  rw [← current, Nat.mul_comm] at decomposed
  have small : epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by omega
  have nonempty : 0 < preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by omega
  have start : (epoch * preset.SLOTS_PER_EPOCH).toNat =
      epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt small]
  obtain ⟨root, read⟩ := getBlockRootAtSlot_exists (state := state)
    (slot := epoch * preset.SLOTS_PER_EPOCH) (by rw [start]; omega) (by rw [start]; omega)
    (by rw [start]; omega) nonempty
  refine ⟨root, ?_⟩
  unfold getBlockRoot computeStartSlotAtEpoch
  rw [mulChecked_of_lt small]
  exact read

/-- From Altair, the validators with a flag in a recent epoch succeed, and are in the registry.

A recent epoch is the previous or the current one.

The registry must stay within its limit.

The lists of flags must have one entry for each validator. -/
theorem getUnslashedParticipatingIndices_exists_ok (within : state.RegistryWithinLimit)
    (altair : .altair ≤ fork) (flagIndex : UInt64) {epoch : Epoch}
    (recent : epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state)
    (sized : ParticipationMatches state) :
    ∃ result, getUnslashedParticipatingIndices state altair flagIndex epoch = .ok result ∧
      ∀ index ∈ result, index.toNat < state.validators.data.size := by
  have active : ∀ index ∈ getActiveValidatorIndices state epoch,
      index.toNat < state.validators.data.size := by
    intro index member
    obtain ⟨_, found, -⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  suffices ∃ result, getUnslashedParticipatingIndices state altair flagIndex epoch = .ok result by
    obtain ⟨result, computed⟩ := this
    exact ⟨result, computed, fun index member =>
      active index (mem_getUnslashedParticipatingIndices computed index member).1⟩
  unfold getUnslashedParticipatingIndices
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true recent)]
  have sizedAt : (if epoch = getCurrentEpoch state then
      (state.currentEpochParticipation altair).data
      else (state.previousEpochParticipation altair).data).size =
        state.validators.data.size := by
    split
    · exact (sized altair).2
    · exact (sized altair).1
  generalize (if epoch = getCurrentEpoch state then (state.currentEpochParticipation altair).data
    else (state.previousEpochParticipation altair).data) = participation at sizedAt ⊢
  refine bind_exists_ok (mapM_exists_ok (xs := getActiveValidatorIndices state epoch) ?_)
    fun _ => ⟨_, rfl⟩
  intro index member
  have lt := active index member
  have found : getValidator state index = .ok state.validators.data[index.toNat] :=
    getValidator_eq_ok_iff.mpr (Array.getElem?_eq_getElem lt)
  rw [Array.getElem?_eq_getElem (by omega)]
  exact ⟨_, by simp only [found]; rfl⟩

/-- A checked product, lifted to an error of the transition, succeeds when it fits. -/
private theorem liftMul_exists_ok {a b : UInt64} (fits : a.toNat * b.toNat < 2 ^ 64) :
    ∃ c, liftAccessor (liftArith (mulChecked a b)) = .ok c :=
  ⟨a * b, by rw [mulChecked_of_lt fits]; rfl⟩

/-- A checkpoint is justified, or kept, when the root of the first block of its epoch succeeds. -/
private theorem justifyCheckpoint_exists_ok {epoch : Epoch}
    (rooted : ∃ root, getBlockRoot state epoch = .ok root) (justified : Bool)
    (checkpoint : Checkpoint) :
    ∃ result, justifyCheckpoint state justified epoch checkpoint = .ok result := by
  obtain ⟨root, read⟩ := rooted
  unfold justifyCheckpoint
  cases justified
  · exact ⟨checkpoint, rfl⟩
  · exact ⟨⟨epoch, root⟩, by simp [read, liftAccessor, Except.mapError, bind, Except.bind,
      pure, Except.pure]⟩

/-- A finalization rule succeeds when its source plus its gap is below 2^64. -/
private theorem finalizes_exists_ok {source gap : Epoch}
    (fits : source.toNat + gap.toNat < 2 ^ 64) (justified : Bool) (currentEpoch : Epoch) :
    ∃ result, finalizes justified source gap currentEpoch = .ok result := by
  unfold finalizes
  cases justified
  · exact ⟨false, rfl⟩
  · exact ⟨source + gap == currentEpoch, by simp [addChecked_of_lt fits, liftArith, liftAccessor,
      Except.mapError, bind, Except.bind, pure, Except.pure]⟩

/-- The votes are weighed when the products fit, the roots succeed and the sums of epochs fit.

The roots are those of the first blocks of the previous and the current epoch.

The products are the target balances times three and the active balance times two.

The sums are the previous justified epoch plus three and the current one plus two. -/
private theorem weighJustificationAndFinalization_exists_ok {total previous current : Gwei}
    (previousRoot : ∃ root, getBlockRoot state (getPreviousEpoch state) = .ok root)
    (currentRoot : ∃ root, getBlockRoot state (getCurrentEpoch state) = .ok root)
    (totalFits : total.toNat * 2 < 2 ^ 64) (previousFits : previous.toNat * 3 < 2 ^ 64)
    (currentFits : current.toNat * 3 < 2 ^ 64)
    (oldPrevious : state.previousJustifiedCheckpoint.epoch.toNat + 3 < 2 ^ 64)
    (oldCurrent : state.currentJustifiedCheckpoint.epoch.toNat + 2 < 2 ^ 64) :
    ∃ after, weighJustificationAndFinalization state total previous current = .ok after := by
  unfold weighJustificationAndFinalization
  dsimp only
  refine bind_exists_ok (liftMul_exists_ok previousFits) fun _ => ?_
  refine bind_exists_ok (liftMul_exists_ok totalFits) fun _ => ?_
  refine bind_exists_ok (justifyCheckpoint_exists_ok previousRoot _ _) fun _ => ?_
  refine bind_exists_ok (liftMul_exists_ok currentFits) fun _ => ?_
  refine bind_exists_ok (justifyCheckpoint_exists_ok currentRoot _ _) fun _ => ?_
  refine bind_exists_ok (finalizes_exists_ok oldPrevious _ _) fun _ => ?_
  refine bind_exists_ok (finalizes_exists_ok (by simp; omega) _ _) fun _ => ?_
  refine bind_exists_ok (finalizes_exists_ok oldCurrent _ _) fun _ => ?_
  refine bind_exists_ok (finalizes_exists_ok (by simp; omega) _ _) fun _ => ?_
  exact ⟨_, rfl⟩

/-- The signers of a pending attestation are validators of the registry.

They come from a committee, whose members are active, and the active indices are in range. -/
private theorem pendingSigners_lt (within : state.RegistryWithinLimit)
    {attestation : PendingAttestation preset} {signers : List ValidatorIndex}
    (computed : getPendingAttestingIndices state attestation = .ok signers) :
    ∀ index ∈ signers, index.toNat < state.validators.data.size := by
  intro index member
  simp only [getPendingAttestingIndices, bind_ok_iff] at computed
  obtain ⟨committee, committeeOk, signersOk⟩ := computed
  have active := mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
    (mem_of_committeeAttesters signersOk member)
  obtain ⟨_, found, -⟩ := (mem_getActiveValidatorIndices within).mp active
  exact (Array.getElem?_eq_some_iff.mp found).1

/-- The unslashed signers of some pending attestations succeed.

The signers of each attestation must succeed.

The registry must stay within its limit.

The unslashed signers are then validators of the registry. -/
theorem getUnslashedAttestingIndices_exists_ok (within : state.RegistryWithinLimit)
    {attestations : Array (PendingAttestation preset)}
    (resolved : ∀ attestation ∈ attestations,
      ∃ signers, getPendingAttestingIndices state attestation = .ok signers) :
    ∃ attesters, getUnslashedAttestingIndices state attestations = .ok attesters ∧
      ∀ index ∈ attesters, index.toNat < state.validators.data.size := by
  obtain ⟨lists, listsOk⟩ := mapM_exists_ok (xs := attestations.toList)
    (f := getPendingAttestingIndices state) fun attestation member =>
      resolved attestation (Array.mem_toList_iff.mp member)
  have inside : ∀ index ∈ lists.flatten, index.toNat < state.validators.data.size := by
    intro index member
    obtain ⟨list, listMember, indexMember⟩ := List.mem_flatten.mp member
    obtain ⟨attestation, attestationMember, computed⟩ := mapM_ok_mem listsOk list listMember
    exact pendingSigners_lt within computed index indexMember
  obtain ⟨unslashed, unslashedOk⟩ := filterM_exists_ok (list := sortedSet lists.flatten)
    (test := fun index => do return !(← getValidator state index).slashed)
    fun index member => by
      have found : getValidator state index =
          .ok (state.validators.data[index.toNat]'(inside index (mem_sortedSet.mp member))) :=
        getValidator_eq_ok_iff.mpr (Array.getElem?_eq_getElem _)
      exact ⟨_, by rw [found]; rfl⟩
  refine ⟨unslashed, ?_, fun index member =>
    inside index (mem_sortedSet.mp (mem_of_filterM_ok unslashedOk member))⟩
  unfold getUnslashedAttestingIndices unslashedAmong
  rw [listsOk]
  exact bind_ok_iff.mpr ⟨_, rfl, unslashedOk⟩

/-- Before Altair, the balance of the signers of some pending attestations succeeds.

The signers of each attestation must succeed.

The registry must stay within its limit.

The sum of the effective balances must be below 2^64.

The balance is then at most one increment or that sum, whichever is larger. -/
private theorem getAttestingBalance_exists_ok (summed : effectiveBalanceSum state < 2 ^ 64)
    (within : state.RegistryWithinLimit) {attestations : Array (PendingAttestation preset)}
    (resolved : ∀ attestation ∈ attestations,
      ∃ signers, getPendingAttestingIndices state attestation = .ok signers) :
    ∃ total, getAttestingBalance state attestations = .ok total ∧
      total.toNat ≤ max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (effectiveBalanceSum state) := by
  obtain ⟨attesters, attestersOk, inside⟩ := getUnslashedAttestingIndices_exists_ok within resolved
  obtain ⟨total, totalOk, bounded⟩ := getTotalBalance_exists_ok inside summed
  refine ⟨total, ?_, bounded⟩
  unfold getAttestingBalance
  rw [attestersOk]
  exact totalOk

/-- Before Altair, the pending attestations with a matching source in a recent epoch succeed.

A recent epoch is the previous or the current one.

They are the list of the current epoch if the epoch is current, else that of the previous one. -/
theorem getMatchingSourceAttestations_eq_ok (before : fork < .altair) {epoch : Epoch}
    (recent : epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state) :
    getMatchingSourceAttestations state before epoch =
      .ok (if epoch = getCurrentEpoch state then (state.currentEpochAttestations before).data
        else (state.previousEpochAttestations before).data) :=
  bind_ok_iff.mpr ⟨(), ensure_ok_iff.mpr recent, rfl⟩

/-- A member of the list that the source match picks is in a list of a recent epoch. -/
theorem mem_recent_of_mem_source {before : fork < .altair} {epoch : Epoch}
    {attestation : PendingAttestation preset}
    (member : attestation ∈ (if epoch = getCurrentEpoch state then
      (state.currentEpochAttestations before).data
      else (state.previousEpochAttestations before).data)) :
    attestation ∈ (state.previousEpochAttestations before).data ∨
      attestation ∈ (state.currentEpochAttestations before).data := by
  split at member
  · exact .inr member
  · exact .inl member

/-- Before Altair, the pending attestations with a matching target in a recent epoch succeed.

The block root at the first slot of the epoch must succeed.

Each such attestation is one with a matching source in that epoch. -/
theorem getMatchingTargetAttestations_exists_ok (before : fork < .altair) {epoch : Epoch}
    (recent : epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state)
    (rooted : ∃ root, getBlockRoot state epoch = .ok root) :
    ∃ result, getMatchingTargetAttestations state before epoch = .ok result ∧
      ∀ attestation ∈ result, attestation ∈ (if epoch = getCurrentEpoch state then
        (state.currentEpochAttestations before).data
        else (state.previousEpochAttestations before).data) := by
  obtain ⟨root, read⟩ := rooted
  unfold getMatchingTargetAttestations
  rw [getMatchingSourceAttestations_eq_ok before recent]
  generalize (if epoch = getCurrentEpoch state then (state.currentEpochAttestations before).data
    else (state.previousEpochAttestations before).data) = source
  by_cases empty : source.isEmpty
  · exact ⟨#[], by simp [empty, bind, Except.bind, pure, Except.pure], by simp⟩
  · refine ⟨source.filter (·.data.target.root == root), ?_,
      fun attestation member => Array.mem_of_mem_filter member⟩
    simp [empty, read, liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Justification and finalization succeed at the last slot of an epoch, under bounds.

An epoch of the preset must have two slots at least.

Its buffer of block roots must reach the epoch before.

The slot plus the length of that buffer must be below 2^64.

The registry must stay within its limit.

The checkpoints must be in order, and the current justified one at most the previous epoch.

Three times the sum of one increment and all effective balances must be below 2^64.

From Altair each list of participation flags must have one entry for each validator.

Before Altair the committee and the signers of each recent pending attestation must succeed. -/
theorem processJustificationAndFinalization_total (roots : preset.RootsReachPreviousEpoch)
    (last : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    (room : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (within : state.RegistryWithinLimit) (ordered : CheckpointsOrdered state)
    (settled : JustifiedSettled state)
    (summed : 3 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state) < 2 ^ 64)
    (sized : ParticipationMatches state) (resolved : PendingResolved state) :
    ∃ after, processJustificationAndFinalization state = .ok after := by
  by_cases early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1
  · by_cases altair : .altair ≤ fork
    · exact ⟨state, processJustificationAndFinalization_early_altair altair early⟩
    · exact ⟨state, processJustificationAndFinalization_early (Nat.lt_of_not_le altair) early⟩
  have previousRoot := getBlockRoot_exists_ok roots last room (.inl rfl)
  have currentRoot := getBlockRoot_exists_ok roots last room (.inr rfl)
  have fitsSum : effectiveBalanceSum state < 2 ^ 64 := by omega
  have capped : max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (effectiveBalanceSum state) ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state :=
    Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  obtain ⟨total, totalOk, -, totalHigh⟩ := getTotalActiveBalance_exists_ok within fitsSum
  have totalLe : total.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      effectiveBalanceSum state := by
    rcases totalHigh with rfl | le <;> omega
  have epochs : state.previousJustifiedCheckpoint.epoch.toNat + 3 < 2 ^ 64 ∧
      state.currentJustifiedCheckpoint.epoch.toNat + 2 < 2 ^ 64 := by
    have half := Nat.div_le_div_left (a := state.slot.toNat) roots.twoSlots (by decide)
    have slotLt := state.slot.toNat_lt_size
    have current := getCurrentEpoch_toNat state
    have previous := getPreviousEpoch_le state
    have orderedNat := ordered.2
    simp only [JustifiedSettled, UInt64.le_iff_toNat_le, UInt64.size] at *
    omega
  have weighed : ∀ previous current : Gwei,
      previous.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state →
      current.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat + effectiveBalanceSum state →
      ∃ after, weighJustificationAndFinalization state total previous current = .ok after :=
    fun previous current previousLe currentLe =>
      weighJustificationAndFinalization_exists_ok previousRoot currentRoot (by omega) (by omega)
        (by omega) epochs.1 epochs.2
  unfold processJustificationAndFinalization
  by_cases altair : .altair ≤ fork
  · simp only [altair, ↓reduceDIte]
    unfold processJustificationAndFinalizationAltair
    simp only [early, ↓reduceIte]
    obtain ⟨previous, previousOk, previousIn⟩ := getUnslashedParticipatingIndices_exists_ok
      within altair TIMELY_TARGET_FLAG_INDEX (.inl rfl) sized
    obtain ⟨current, currentOk, currentIn⟩ := getUnslashedParticipatingIndices_exists_ok
      within altair TIMELY_TARGET_FLAG_INDEX (.inr rfl) sized
    obtain ⟨previousBalance, previousBalanceOk, previousLe⟩ :=
      getTotalBalance_exists_ok previousIn fitsSum
    obtain ⟨currentBalance, currentBalanceOk, currentLe⟩ :=
      getTotalBalance_exists_ok currentIn fitsSum
    obtain ⟨after, weighOk⟩ := weighed previousBalance currentBalance (by omega) (by omega)
    exact ⟨after, bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr previousOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr currentOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr totalOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr previousBalanceOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr currentBalanceOk, weighOk⟩⟩⟩⟩⟩⟩
  · simp only [altair, early, ↓reduceDIte, ↓reduceIte]
    have before : fork < .altair := Nat.lt_of_not_le altair
    obtain ⟨previous, previousOk, previousIn⟩ :=
      getMatchingTargetAttestations_exists_ok before (.inl rfl) previousRoot
    obtain ⟨current, currentOk, currentIn⟩ :=
      getMatchingTargetAttestations_exists_ok before (.inr rfl) currentRoot
    obtain ⟨previousBalance, previousBalanceOk, previousLe⟩ := getAttestingBalance_exists_ok
      fitsSum within fun attestation member =>
        resolved before attestation (mem_recent_of_mem_source (previousIn _ member))
    obtain ⟨currentBalance, currentBalanceOk, currentLe⟩ := getAttestingBalance_exists_ok
      fitsSum within fun attestation member =>
        resolved before attestation (mem_recent_of_mem_source (currentIn _ member))
    obtain ⟨after, weighOk⟩ := weighed previousBalance currentBalance (by omega) (by omega)
    exact ⟨after, bind_ok_iff.mpr ⟨_, previousOk,
      bind_ok_iff.mpr ⟨_, currentOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr totalOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr previousBalanceOk,
      bind_ok_iff.mpr ⟨_, liftAccessor_ok.mpr currentBalanceOk, weighOk⟩⟩⟩⟩⟩⟩

end EthLib.Consensus

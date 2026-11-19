module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Cohorts

/-!
# The producer statements

The statements that later modules prove, the funding ceiling and the retained funding potential.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section RunContracts
variable {g x y : ForkedBeaconState preset}

def FloorProducer : Prop := ∀ (shared : Run config checks g x) (tail : Run config checks x y)
  high, Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  ∀ events, tail.balanceEvents high = .ok events →
  ∀ i v w, x.state.validators.data[i]? = some v → y.state.validators.data[i]? = some w →
    v.slashed = false → v.activationEpoch ≠ FAR_FUTURE_EPOCH →
    high + 1 < w.exitEpoch.toNat →
    effectiveAt x i ≤ effectiveAt y i + (effectiveAt x i - actualBalanceAt x i) +
      (events.map (floorPenaltyDebit i)).sum +
          (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
      (if w.slashed then
        (if x.fork < .pectra then min (max (effectiveAt x i) (actualBalanceAt x i))
          preset.MAX_EFFECTIVE_BALANCE.toNat else max (effectiveAt x i) (actualBalanceAt x i)) /
        minSlashingPenaltyQuotient preset (preElectraEpochs config x high) else 0) +
      if FirstDown tail i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0
def SelectedReleaseProducer : Prop :=
  ∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
  Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  ∀ events, tail.balanceEvents high = .ok events →
  ∀ electra : .pectra ≤ x.fork, ∀ selected payments tags,
  ActualPaymentCoverage events payments (x.state.pendingConsolidations electra).data.toList →
  SelectedPayments (preset := preset) selected payments tags →
  ∀ final consumed calls,
  FreshPaymentCoverage (config := config) events
    (initialTags (x.state.pendingConsolidations electra).data.toList)
    final consumed tags payments calls →
  FreshTags (config := config) (consumed ++ final) calls →
  ∀ ledger : RoundLedger tail high,
  ∃ allocations : List OwnedRelease, ∃ before after : Ownership,
  ∃ tokens : BLSPubkey → Finset TokenOrigin,
    OwnedInitial x high before ∧
    (∃ allPayments allAllocations,
      ReservedReplay (checks := checks) x high
        (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
        x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0 events
        (initialTags (x.state.pendingConsolidations electra).data.toList) final
        allPayments allAllocations calls before after ∧
      let fresh := (allPayments.zip allAllocations).filter fun pair =>
        pair.1.1.tag.isFresh
      payments = fresh.map (fun pair => pair.1.2) ∧ allocations = fresh.map Prod.snd) ∧
    CumulativeFunding (config := config) x y high events selected allocations before after ∧
    TerminalAllocation x y after tokens ∧
    Nonempty (NewCohortAllocation tail high ledger after tokens) ∧
    Nonempty (ScheduledAllocation x y high) ∧
    EndpointDemand x y after ∧ after.issued.card ≤ gainBudget (config := config) x high ∧
    ReleasePartition selected payments allocations ∧
    (∀ j : Fin allocations.length, ∃ p, payments[j.val]? = some p ∧
      allocations[j].sourceRound =
        if p.source ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) ∧
    (allocations.map (·.sourceRound)).sum ≤ roundingBudget (config := config) x high ∧
    (allocations.map (·.baseline)).sum ≤ (selected.map (·.amount)).sum +
        roundingBudget (config := config) x high
def PenaltyProducer : Prop := ∀ (shared : Run config checks g x) (tail : Run config checks x y)
  high, Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  ∀ events, tail.balanceEvents high = .ok events →
    (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
      fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
        else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (ix x y + 1)
theorem floor_initial_le_reference (x : ForkedBeaconState preset) (high : Nat) :
    stakeFloorAt config x high 0 ≤ referenceStake x := by
  simp only [stakeFloorAt, stakeFloor, stakeFloorPath, stakeFloorStart]
  exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _)
    (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _)
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _))))))
/-- From Electra, the funded stake at `x` is at most the first ceiling. -/
theorem funded_le_ceiling_initial {x : ForkedBeaconState preset} {high : Nat}
    (electra : .pectra ≤ x.fork) : fundedStake x ≤ stakeCeilingAt config x high 0 := by
  have zero : preElectraEpochs config x high = 0 := by
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    simp only [preElectraEpochs, notBefore, ↓reduceIte]
  simp only [stakeCeilingAt, stakeCeiling, zero, Nat.lt_irrefl, ↓reduceIte]
  omega
private theorem reference_le_ceiling_initial
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (electra : .pectra ≤ x.fork) :
    referenceStake x ≤ stakeCeilingAt config x high 0 :=
  (funding_active_le x early (shared.pubkeysDistinct genesis)).trans
    (funded_le_ceiling_initial electra)
theorem floor_le_initial (x : ForkedBeaconState preset) (high t : Nat) :
    stakeFloorAt config x high t ≤ stakeFloorAt config x high 0 := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans ih)
theorem floor_le_ceiling
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : x.fork < .glamsterdam) (electra : .pectra ≤ x.fork) (t : Nat) :
    stakeFloorAt config x high t ≤ stakeCeilingAt config x high t :=
  (floor_le_initial x high t).trans ((floor_initial_le_reference x high).trans
    ((reference_le_ceiling_initial shared genesis early electra).trans
      (ceilingAt_mono electra high (Nat.zero_le t))))
theorem total_same_epoch {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (_electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch x.state) {total : Gwei}
    (computed : getTotalActiveBalance y.state = .ok total) :
    getTotalActiveBalance x.state = .ok total := by
  have startEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member =>
    lt_size_of_mem_getActiveValidatorIndices member
  have weights := run_same_epoch_effective tail early same
  have active := (activeKept_of_chainSteps tail.chainSteps).getActiveValidatorIndices_eq
    (getCurrentEpoch_le_activityFixedEpoch x.state)
  have totalValue := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok computed)).2.2
  have equal : (∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset,
      effectiveAt y i.toNat) = ∑ i ∈
        (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset,
      effectiveAt x i.toNat := Finset.sum_congr rfl fun i member =>
        weights i.toNat (inside i (List.mem_toFinset.mp member))
  rw [same, active] at totalValue
  change total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (∑ i ∈ (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset,
      effectiveAt y i.toNat) at totalValue
  rw [equal] at totalValue
  obtain ⟨initial, initialOk, initialValue⟩ := totalActive_exists (s := x.state) startEarly
    ((Nat.le_max_right _ _).trans_lt (totalValue ▸ UInt64.toNat_lt total))
  have values : total.toNat = initial.toNat := totalValue.trans initialValue.symm
  have amounts : total = initial := UInt64.toNat_inj.mp values
  simpa only [amounts] using initialOk

theorem increment_le_reference
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : x.fork < .glamsterdam)
    (guard : aprioriGuardAt config x high) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ referenceStake x := by
  have positiveFloor : 0 < stakeFloorAt config x high 0 := by
    exact guard.2.2.2.2.2.2.2.2.2.2.2.1 0 (by omega)
  have positiveStake : 0 < referenceStake x :=
    positiveFloor.trans_le (floor_initial_le_reference x high)
  have unique := (shared.pubkeysDistinct genesis)
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member =>
    lt_size_of_mem_getActiveValidatorIndices member
  have value : referenceStake x = ∑ i ∈
      (getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset,
        effectiveAt x i.toNat := by
    unfold referenceStake
    rw [activeKeys, keys_weight _ _ unique inside]
    rfl
  have divides : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ referenceStake x := by
    rw [value]
    apply Finset.dvd_sum
    intro i member
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp
      (List.mem_toFinset.mp member)
    have whole := reachable_effective_alignment shared genesis aligned v
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
    simpa only [effectiveAt, found, Option.map_some, Option.getD_some] using
      (Nat.dvd_of_mod_eq_zero whole)
  exact Nat.le_of_dvd positiveStake divides

theorem ceiling_unit_of_guard
    (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (aligned : MaxEffectiveBalancesAligned preset)
    (early : x.fork < .glamsterdam) (electra : .pectra ≤ x.fork)
    (guard : aprioriGuardAt config x high) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0 :=
  (increment_le_reference shared genesis aligned early guard).trans
    (reference_le_ceiling_initial shared genesis early electra)
def retainedFundingPotential {fork : Fork} (x : ForkedBeaconState preset)
    (s : BeaconState preset fork) (queue : List PendingConsolidation) (cutoff : Epoch) : Nat :=
  ∑ i ∈ Finset.range s.validators.data.size,
    (s.validators.data[i]?.map fun v =>
      if isActiveValidator v (getCurrentEpoch s) ||
          decide (getCurrentEpoch s < v.activationEpoch) ||
          queue.any (fun c => c.sourceIndex.toNat == i) ||
          ((x.state.validators.data[i]?).any (fun old =>
            isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
              decide (cutoff < v.withdrawableEpoch)) then
        max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i)
      else 0).getD 0
theorem retainedFundingPotential_initial (x : ForkedBeaconState preset)
    (queue : List PendingConsolidation) (cutoff : Epoch) :
    retainedFundingPotential x x.state queue cutoff = fundingPotential x.state queue := by
  unfold retainedFundingPotential fundingPotential
  apply Finset.sum_congr rfl
  intro i _
  cases found : x.state.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some, Option.any_some]
    by_cases active : isActiveValidator v (getCurrentEpoch x.state) = true
    · simp only [active, Bool.true_or, Bool.true_and]
    · have inactive : isActiveValidator v (getCurrentEpoch x.state) = false :=
        Bool.eq_false_iff.mpr active
      simp only [inactive, Bool.false_or, Bool.false_and, Bool.or_false]
theorem retainedFundingPotential_cutoff_mono {fork : Fork}
    (x : ForkedBeaconState preset) (s : BeaconState preset fork)
    (queue : List PendingConsolidation) {before after : Epoch} (later : before ≤ after) :
    retainedFundingPotential x s queue after ≤ retainedFundingPotential x s queue before := by
  unfold retainedFundingPotential
  apply Finset.sum_le_sum
  intro i _
  cases found : s.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some]
    split
    · rename_i supported
      have prior : (isActiveValidator v (getCurrentEpoch s) ||
          decide (getCurrentEpoch s < v.activationEpoch) ||
          queue.any (fun c => c.sourceIndex.toNat == i) ||
          ((x.state.validators.data[i]?).any (fun old =>
            isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
              decide (before < v.withdrawableEpoch))) = true := by
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at supported ⊢
        rcases supported with ordinary | ⟨cohort, retained⟩
        · exact .inl ordinary
        · exact .inr ⟨cohort, UInt64.lt_of_le_of_lt later retained⟩
      simp only [prior, ↓reduceIte, Nat.le_refl]
    · exact Nat.zero_le _
/-- Take two states `z` and `s`.

Suppose each eligible key at `z` is supported at `s` with at least its weight there.

Then the eligible stake of keys at `z` is at most the retained potential at `s`. -/
theorem retainedFundingPotential_eligible_le {fork' fork : Fork}
    (x : ForkedBeaconState preset) (z : BeaconState preset fork') (s : BeaconState preset fork)
    (queue : List PendingConsolidation) (cutoff : Epoch) (S : Finset Nat)
    (inside : ∀ i ∈ S, i < s.validators.data.size)
    (support : ∀ i ∈ S, ∀ w, z.validators.data[i]? = some w →
      isEligibleValidator (getPreviousEpoch z) w = .ok true →
      ∃ v, s.validators.data[i]? = some v ∧
        (isActiveValidator v (getCurrentEpoch s) ||
          decide (getCurrentEpoch s < v.activationEpoch) ||
          queue.any (fun c => c.sourceIndex.toNat == i) ||
          ((x.state.validators.data[i]?).any (fun old =>
            isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
              decide (cutoff < v.withdrawableEpoch))) = true ∧
        w.effectiveBalance.toNat ≤ effectiveAt ⟨fork, s⟩ i) :
    (∑ i ∈ S, eligibleWeight z i) ≤ retainedFundingPotential x s queue cutoff := by
  apply (Finset.sum_le_sum fun i member => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg
      (fun i member => Finset.mem_range.mpr (inside i member)) (by intros; exact Nat.zero_le _))
  unfold eligibleWeight
  cases found : z.validators.data[i]? with
  | none => simp
  | some w =>
    cases eligible : isEligibleValidator (getPreviousEpoch z) w with
    | error err => simp [eligible]
    | ok flag =>
      cases flag with
      | false => simp [eligible]
      | true =>
        obtain ⟨v, read, supported, weight⟩ := support i member w found eligible
        simp only [eligible, read, Option.map_some, Option.getD_some, supported, ↓reduceIte]
        exact weight.trans (Nat.le_max_left _ _)
private theorem eligible_withdrawable_future {fork : Fork}
    {s : BeaconState preset fork} {v : Validator}
    (ordered : v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (eligible : isEligibleValidator (getPreviousEpoch s) v = .ok true) :
    getCurrentEpoch s < v.withdrawableEpoch := by
  by_cases active : isActiveValidator v (getPreviousEpoch s) = true
  · have exit := (show v.activationEpoch ≤ getPreviousEpoch s ∧
        getPreviousEpoch s < v.exitEpoch from by
          simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using active).2
    have previous := getPreviousEpoch_toNat s
    rw [UInt64.lt_iff_toNat_lt] at exit ⊢
    omega
  · simp only [isEligibleValidator, active, Bool.false_eq_true, ↓reduceIte] at eligible
    split at eligible
    · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        pure, Except.pure, Except.ok.injEq] at eligible
      obtain ⟨next, read, less⟩ := eligible
      have value := (addChecked_ok_iff.mp read).2
      have previous := getPreviousEpoch_toNat s
      have below : next < v.withdrawableEpoch := by simpa using less
      rw [UInt64.lt_iff_toNat_lt] at below ⊢
      change next.toNat = (getPreviousEpoch s).toNat + 1 at value
      omega
    · exact False.elim (Bool.noConfusion (Except.ok.inj eligible))
theorem eligible_active_or_withdrawable {fork : Fork}
    {s : BeaconState preset fork} {v : Validator}
    (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (ordered : v.exitEpoch ≠ FAR_FUTURE_EPOCH →
      v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat)
    (eligible : isEligibleValidator (getPreviousEpoch s) v = .ok true) :
    isActiveValidator v (getCurrentEpoch s) = true ∨
      getCurrentEpoch s < v.withdrawableEpoch := by
  by_cases assigned : v.exitEpoch = FAR_FUTURE_EPOCH
  · by_cases active : isActiveValidator v (getPreviousEpoch s) = true
    · left
      have activation : v.activationEpoch ≤ getPreviousEpoch s := by
        have bounds : v.activationEpoch ≤ getPreviousEpoch s ∧
            getPreviousEpoch s < v.exitEpoch := by
          simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using active
        exact bounds.1
      simp [isActiveValidator, UInt64.le_trans activation (getPreviousEpoch_le s),
        assigned, finite]
    · right
      have previous := getPreviousEpoch_toNat s
      simp only [isEligibleValidator, active, Bool.false_eq_true, ↓reduceIte] at eligible
      split at eligible
      · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
          pure, Except.pure, Except.ok.injEq] at eligible
        obtain ⟨next, read, less⟩ := eligible
        have value := (addChecked_ok_iff.mp read).2
        have below : next < v.withdrawableEpoch := by simpa using less
        rw [UInt64.lt_iff_toNat_lt] at below ⊢
        change next.toNat = (getPreviousEpoch s).toNat + 1 at value
        omega
      · exact False.elim (Bool.noConfusion (Except.ok.inj eligible))
  · exact Or.inr (eligible_withdrawable_future (ordered assigned) eligible)
theorem retainedFundingPotential_balance_change {fork : Fork}
    (x : ForkedBeaconState preset) {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (cutoff : Epoch)
    (registry : t.validators = s.validators) (slot : t.slot = s.slot) :
    retainedFundingPotential x t queue cutoff ≤ retainedFundingPotential x s queue cutoff +
      ∑ i ∈ Finset.range s.validators.data.size,
        (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i) := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp [getCurrentEpoch, slot]
  unfold retainedFundingPotential
  rw [registry, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  cases found : s.validators.data[i]? with
  | none => simp
  | some v =>
    simp only [Option.map_some, Option.getD_some, epoch]
    have effective : effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i := by
      simp [effectiveAt, registry]
    rw [effective]
    split <;> omega
theorem retainedFundingPotential_change {fork : Fork}
    (x : ForkedBeaconState preset) {s t : BeaconState preset fork}
    (queue beforeQueue : List PendingConsolidation) (cutoff beforeCutoff : Epoch)
    (credits : Nat → Nat)
    (size : t.validators.data.size = s.validators.data.size)
    (support : ∀ i v w, s.validators.data[i]? = some v →
      t.validators.data[i]? = some w →
      (isActiveValidator w (getCurrentEpoch t) ||
        decide (getCurrentEpoch t < w.activationEpoch) ||
        queue.any (fun c => c.sourceIndex.toNat == i) ||
        ((x.state.validators.data[i]?).any (fun old =>
          isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
            decide (cutoff < w.withdrawableEpoch))) = true →
      (isActiveValidator v (getCurrentEpoch s) ||
        decide (getCurrentEpoch s < v.activationEpoch) ||
        beforeQueue.any (fun c => c.sourceIndex.toNat == i) ||
        ((x.state.validators.data[i]?).any (fun old =>
          isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
            decide (beforeCutoff < v.withdrawableEpoch))) = true)
    (funding : ∀ i, max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i) + credits i) :
    retainedFundingPotential x t queue cutoff ≤
      retainedFundingPotential x s beforeQueue beforeCutoff +
        ∑ i ∈ Finset.range s.validators.data.size, credits i := by
  unfold retainedFundingPotential
  rw [size, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i member
  have inside := Finset.mem_range.mp member
  have found : s.validators.data[i]? = some s.validators.data[i] := by simp [inside]
  have located : t.validators.data[i]? = some t.validators.data[i] := by simp [size, inside]
  simp only [found, located, Option.map_some, Option.getD_some]
  split
  · rename_i chosen
    have prior := support i _ _ found located chosen
    simpa only [prior, ↓reduceIte] using funding i
  · exact Nat.zero_le _
theorem retainedFundingPotential_effective_updates {fork : Fork}
    (x : ForkedBeaconState preset) {s t : BeaconState preset fork}
    (queue : List PendingConsolidation) (cutoff : Epoch)
    (matched : BalancesMatch s) (ok : processEffectiveBalanceUpdates s = .ok t) :
    retainedFundingPotential x t queue cutoff ≤ retainedFundingPotential x s queue cutoff := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp [getCurrentEpoch, (frame_processEffectiveBalanceUpdates ok).slot]
  have bound := retainedFundingPotential_change x queue queue cutoff cutoff (fun _ => 0)
    (sameSizes_processEffectiveBalanceUpdates ok).1 (fun i v w found read => ?_)
    (fun i => by simpa using processEffectiveBalanceUpdates_max_le ok i)
  · simpa using bound
  · have inside := (Array.getElem?_eq_some_iff.mp found).1
    have balanceInside : i < s.balances.data.size := by
      unfold BalancesMatch at matched
      omega
    obtain ⟨effective, located, _⟩ := processEffectiveBalanceUpdates_effectiveBalance_eq
      ok found (Array.getElem?_eq_getElem balanceInside)
    obtain rfl : w = { v with effectiveBalance := effective } :=
      Option.some.inj (read.symm.trans located)
    simpa only [isActiveValidator, epoch] using id
theorem total_le_ceiling_of_read
    {u : ForkedBeaconState preset} {total : Gwei}
    (read : getTotalActiveBalance u.state = .ok total)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high t)
    (stake : (∑ i ∈ (getActiveValidatorIndices u.state (getCurrentEpoch u.state)).toFinset,
      effectiveAt u i.toNat) ≤ stakeCeilingAt config x high t) :
    total.toNat ≤ stakeCeilingAt config x high t := by
  obtain ⟨_, _, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok read)
  rw [value]
  exact max_le unit stake
theorem NewCohortCuts.debit_budget_of_penaltyProducer
    (producer : PenaltyProducer (config := config) (checks := checks)
      (g := g) (x := x) (y := y))
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (ledger : RoundLedger tail high)
    (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (parts : Nat → List (BalanceEvent preset))
    (reads : ∀ i, (ledger.headRun i).balanceEvents high = .ok (parts i)) :
    (∑ i ∈ cohort.cohort,
      ((effectiveAt x i - actualBalanceAt x i) +
        ((parts i).map (floorPenaltyDebit i)).sum +
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0))) ≤
      (∑ i ∈ cohort.cohort,
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) + startSlack x +
        windowPenalties (config := config) x high (driftHorizon x high + 1) +
            roundingBudget (config := config) x high := by
  have early := supported.2.2.2.2.1
  have startEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have included (i : Nat) : parts i <+: events := by
    have replay := replayed
    rw [← ledger.split i] at replay
    obtain ⟨part, read, initial⟩ :=
      (ledger.headRun i).balanceEvents_prefix (ledger.suffix i) high events replay
    have same := Except.ok.inj ((reads i).symm.trans read)
    simpa only [same] using initial
  have bounds := cohort.slack_penalty_bounds startEarly parts events (fun i _ => included i)
  have numeric := producer shared tail high supported twoSlots events replayed
  have horizon : ix x y + 1 ≤ driftHorizon x high + 1 := by
    have endpoint := supported.2.2.2.2.2.1
    unfold ix driftHorizon
    omega
  have penalty := bounds.2.trans (numeric.trans (penalties_monotone x high horizon))
  have rounding : (∑ i ∈ cohort.cohort,
      if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) ≤
      roundingBudget (config := config) x high := by
    calc
      _ = ∑ i ∈ cohort.cohort.filter (· ∈ ledger.falling),
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
        rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ ledger.falling, preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun _ member => (Finset.mem_filter.mp member).2) (fun _ _ _ => Nat.zero_le _)
      _ = preset.EFFECTIVE_BALANCE_INCREMENT.toNat * ledger.falling.card := by
        simp [Nat.mul_comm]
      _ ≤ _ := ledger.roundBound
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  omega
private theorem NewCohortCuts.allocation_of_replay
    (producer : PenaltyProducer (config := config) (checks := checks)
      (g := g) (x := x) (y := y))
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (ledger : RoundLedger tail high)
    (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (parts : Nat → List (BalanceEvent preset))
    (reads : ∀ i, (ledger.headRun i).balanceEvents high = .ok (parts i))
    (joint : (∑ i ∈ cohort.boundary ∪ cohort.departed, cohort.charge i) +
      (∑ i ∈ cohort.cohort,
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
          departureBudgetAt (config := config) x high +
              duePartialWithdrawals x (driftHorizon x high))
    (owned : Ownership) (tokens : BLSPubkey → Finset TokenOrigin) :
    let debit := fun i => (effectiveAt x i - actualBalanceAt x i) +
      ((parts i).map (floorPenaltyDebit i)).sum +
      ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum +
      (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
    (∀ i ∈ cohort.boundary ∪ cohort.departed,
      effectiveAt x i ≤ cohort.charge i + debit i) →
    (∀ i ∈ cohort.cohort, i ∈ cohort.supported → i ∉ cohort.boundary →
      effectiveAt x i ≤ effectiveAt y i + debit i) →
    (∀ i ∈ cohort.boundary, ∃ v, y.state.validators.data[i]? = some v ∧
      tokens v.pubkey ⊆ held owned i ∩ owned.endpoint ∧
      (tokens v.pubkey).card = effectiveAt y i - effectiveAt x i) →
    ∃ allocation : NewCohortAllocation tail high ledger owned tokens,
      allocation.toNewCohortCuts = cohort ∧ allocation.debit = debit ∧
      (∀ i, allocation.partialDebit i =
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) := by
  dsimp only
  intro stopped retained selected
  have early := supported.2.2.2.2.1
  have startEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have included (i : Nat) : parts i <+: events := by
    have replay := replayed
    rw [← ledger.split i] at replay
    obtain ⟨part, read, initial⟩ :=
      (ledger.headRun i).balanceEvents_prefix (ledger.suffix i) high events replay
    have same := Except.ok.inj ((reads i).symm.trans read)
    simpa only [same] using initial
  have bounds := cohort.slack_penalty_bounds startEarly parts events (fun i _ => included i)
  have numeric := producer shared tail high supported twoSlots events replayed
  have horizon : ix x y + 1 ≤ driftHorizon x high + 1 := by
    have endpoint := supported.2.2.2.2.2.1
    unfold ix driftHorizon
    omega
  let allocation : NewCohortAllocation tail high ledger owned tokens := {
    toNewCohortCuts := cohort
    debit := fun i => (effectiveAt x i - actualBalanceAt x i) +
      ((parts i).map (floorPenaltyDebit i)).sum +
      ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum +
      (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
    slack := fun i => effectiveAt x i - actualBalanceAt x i
    penalty := fun i => ((parts i).map (floorPenaltyDebit i)).sum
    partialDebit := fun i => ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum
    exactDebit := fun _ _ => rfl
    slackBudget := bounds.1
    penaltyBudget := bounds.2.trans (numeric.trans (penalties_monotone x high horizon))
    stopped := stopped
    retained := retained
    selected := selected
    partialTotal := ∑ i ∈ cohort.cohort,
      ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum
    partialBudget := Nat.le_refl _
    queueBudget := joint
    debitBudget := cohort.debit_budget_of_penaltyProducer producer shared tail supported
      ledger twoSlots replayed parts reads }
  exact ⟨allocation, rfl, rfl, fun _ => rfl⟩
private theorem NewCohortCuts.allocation_electra_of_replay
    (producer : PenaltyProducer (config := config) (checks := checks)
      (g := g) (x := x) (y := y))
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (ledger : RoundLedger tail high)
    (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (unique : PubkeysDistinct y.state) (electra : .pectra ≤ x.fork)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (parts : Nat → List (BalanceEvent preset))
    (reads : ∀ i, (ledger.headRun i).balanceEvents high = .ok (parts i))
    (joint : (∑ i ∈ cohort.boundary ∪ cohort.departed, cohort.charge i) +
      (∑ i ∈ cohort.cohort,
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
          departureBudgetAt (config := config) x high +
              duePartialWithdrawals x (driftHorizon x high))
    (owned : Ownership) (tokens : BLSPubkey → Finset TokenOrigin)
    (selected : ∀ i ∈ cohort.boundary, ∃ v, y.state.validators.data[i]? = some v ∧
      tokens v.pubkey ⊆ held owned i ∩ owned.endpoint ∧
      (tokens v.pubkey).card = effectiveAt y i - effectiveAt x i) :
    ∃ allocation : NewCohortAllocation tail high ledger owned tokens,
      allocation.toNewCohortCuts = cohort ∧
      allocation.debit = (fun i => (effectiveAt x i - actualBalanceAt x i) +
        ((parts i).map (floorPenaltyDebit i)).sum +
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum +
        (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) ∧
      (∀ i, allocation.partialDebit i =
        ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) := by
  apply cohort.allocation_of_replay producer shared tail supported ledger twoSlots
    replayed parts reads joint owned tokens
  · intro i member
    exact cohort.stopped_debit_electra shared supported unique electra twoSlots member (reads i)
  · intro i member retained notBoundary
    exact cohort.retained_debit_electra shared supported unique electra member retained
      notBoundary (reads i)
  · exact selected
theorem NewCohortCuts.allocation_electra_of_ceiling
    (producer : PenaltyProducer (config := config) (checks := checks)
      (g := g) (x := x) (y := y))
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (ledger : RoundLedger tail high)
    (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (unique : PubkeysDistinct y.state) (electra : .pectra ≤ x.fork)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (others : ∀ {u : ForkedBeaconState preset} (head : Run config checks x u),
      u.fork < .glamsterdam → (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ found,
        head.balanceEvents high = .ok found → (found.map otherCredit).sum ≤
          whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
            (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
            (driftHorizon x high) (preElectraEpochs config x high))
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) ≤ total.toNat)
    (replayed : tail.balanceEvents high = .ok events)
    (owned : Ownership) (tokens : BLSPubkey → Finset TokenOrigin)
    (selected : ∀ i ∈ cohort.boundary, ∃ v, y.state.validators.data[i]? = some v ∧
      tokens v.pubkey ⊆ held owned i ∩ owned.endpoint ∧
      (tokens v.pubkey).card = effectiveAt y i - effectiveAt x i) :
    ∃ parts : Nat → List (BalanceEvent preset),
      (∀ i, (ledger.headRun i).balanceEvents high = .ok (parts i)) ∧
      ∃ allocation : NewCohortAllocation tail high ledger owned tokens,
        allocation.toNewCohortCuts = cohort ∧
        allocation.debit = (fun i => (effectiveAt x i - actualBalanceAt x i) +
          ((parts i).map (floorPenaltyDebit i)).sum +
          ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum +
          (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) ∧
        (∀ i, allocation.partialDebit i =
          ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) := by
  have support := supported
  obtain ⟨genesis, _parameters, _caps, aligned, early, endpoint, guard⟩ := supported
  obtain ⟨parts, reads, joint⟩ := cohort.ledger_budget_of_ceiling shared genesis electra early
    unique endpoint guard aligned unit others floor replayed
  obtain ⟨allocation, same, debit, partials⟩ := cohort.allocation_electra_of_replay producer
    shared tail support ledger unique electra twoSlots replayed parts reads joint owned tokens
        selected
  exact ⟨parts, reads, allocation, same, debit, partials⟩
def ScheduledBoundaryProducer : Prop :=
  ∀ (shared : Run config checks g x) (tail : Run config checks x y) high,
  Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  ∀ j, (getCurrentEpoch x.state).toNat ≤ j → j ≤ horizonEnd x high →
  (getCurrentEpoch y.state).toNat = j →
  (∑ i ∈ Finset.range x.state.validators.data.size,
    if (x.state.validators.data[i]?).any (fun v =>
        isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
        decide (v.exitEpoch.toNat = j)) then effectiveAt y i - 2 * effectiveAt x i else 0) ≤
      exitCohortGrowth x high
def StateProducer : Prop := ∀ (shared : Run config checks g x) (tail : Run config checks x y)
  high, Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
    stateDrift x y ≤ drift (config := config) x high
def DerivedProducer : Prop :=
  ∀ (_shared : Run config checks g x) (tail : Run config checks x y),
  Genesis (config := config) (checks := checks) g → Parameters preset → CapOrder preset →
  MaxEffectiveBalancesAligned preset → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  y.fork < .glamsterdam → ∀ high,
    (getCurrentEpoch x.state).toNat ≤ high + 1 → aprioriGuardAt config x high →
    derivedDrift high tail ≤ drift (config := config) x high
def CommonLedger : Prop := ∀ (shared : Run config checks g x) (tail : Run config checks x y)
  high, Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → ∀ cutoff,
    exitedBefore x cutoff ∩ recentKeys y.state = ∅ → cutoff ≤ high + 1 →
    stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤ drift (config := config) x high
def ReducedIdentity (x y : ForkedBeaconState preset) (c : Finset BLSPubkey) : Prop :=
  c ⊆ unslashedKeys x.state → c ∩ recentKeys y.state = ∅ →
    reducedDrift x y c + 2 * (Models.stake (effectiveWeight x.state) c - commonSlashed x y c) =
      stateDrift x y
end RunContracts

def CachedAbsenceProducer : Prop := ∀ {g x a b : ForkedBeaconState preset}
  (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b),
  Genesis (config := config) (checks := checks) g → Parameters preset →
  ∀ one two : EitherCall (shared.append left) (shared.append right),
  (getCurrentEpoch x.state).toNat < min one.targetEpoch two.targetEpoch →
  exitedBefore x (min one.targetEpoch two.targetEpoch) ∩ recentKeys one.state.state = ∅ ∧
    exitedBefore x (min one.targetEpoch two.targetEpoch) ∩ recentKeys two.state.state = ∅

def ReducedTransferProducer : Prop := ∀ {g x a b : ForkedBeaconState preset}
  (shared : Run config checks g x) (left : Run config checks x a) (right : Run config checks x b),
  Parameters preset → Genesis (config := config) (checks := checks) g →
  EnoughStake (shared.append left) b.state.finalizedCheckpoint.epoch.toNat →
  EnoughStake (shared.append right) b.state.finalizedCheckpoint.epoch.toNat →
  a.state.finalizedCheckpoint.epoch ≤ b.state.finalizedCheckpoint.epoch →
  Conflict (shared.append left) (shared.append right)
    a.state.finalizedCheckpoint b.state.finalizedCheckpoint →
  (∃ one two : EitherCall (shared.append left) (shared.append right),
    a.state.finalizedCheckpoint.epoch.toNat ≤ one.targetEpoch ∧
    one.targetEpoch ≤ b.state.finalizedCheckpoint.epoch.toNat ∧
    a.state.finalizedCheckpoint.epoch.toNat ≤ two.targetEpoch ∧
    two.targetEpoch ≤ b.state.finalizedCheckpoint.epoch.toNat ∧
    let c := exitedBefore x (min one.targetEpoch two.targetEpoch)
    Models.stake (effectiveWeight x.state) (unslashedKeys x.state \ c) ≤
      3 * Models.stake (effectiveWeight x.state) (accountableKeys shared left right \ c) +
        reducedDrift x one.state c + reducedDrift x two.state c) ∨
    HashEvidence ((shared.append left).hashObjects ++ (shared.append right).hashObjects)

/-- The sync debits of one epoch fit the part of `lambda_t` that the rewards pass leaves free.

The sync debits, times `28`, are at most the issuance envelope `BRF * (sqrt T + 2)`.

With `sqrt T * sqrt L <= W` and `L <= W`, that is at most `72 * BRF * W / (64 * sqrt L)`.

The rewards pass takes `40 / 64` of `BRF * W / sqrt L`, and `40 + 72 = 112 = 64 * 7 / 4`. -/
private theorem sync_le_penaltySlack {sync total lower weight : Nat}
    (syncLe : sync * 28 ≤ preset.epochIssuanceBeforeAltair total)
    (roots : total.sqrt * lower.sqrt ≤ weight) (small : lower ≤ weight) (positive : 0 < lower) :
    sync ≤ 72 * preset.BASE_REWARD_FACTOR.toNat * weight / (64 * lower.sqrt) := by
  have rootPositive : 0 < lower.sqrt := Nat.sqrt_pos.mpr positive
  have rootSmall : lower.sqrt ≤ weight := (Nat.sqrt_le_self lower).trans small
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) rootPositive)]
  unfold Preset.epochIssuanceBeforeAltair at syncLe
  generalize preset.BASE_REWARD_FACTOR.toNat = factor at *
  generalize total.sqrt = q at *
  generalize lower.sqrt = s at *
  -- Seven times the product is at most `48 * factor * weight`, well below `7 * 72`.
  have scaled : sync * (64 * s) * 7 ≤ 72 * factor * weight * 7 :=
    calc sync * (64 * s) * 7 = 16 * s * (sync * 28) := by ring
      _ ≤ 16 * s * (factor * (q + 2)) := Nat.mul_le_mul_left _ syncLe
      _ = 16 * factor * (q * s) + 32 * factor * s := by ring
      _ ≤ 16 * factor * weight + 32 * factor * weight :=
          Nat.add_le_add (Nat.mul_le_mul_left _ roots) (Nat.mul_le_mul_left _ rootSmall)
      _ = 48 * (factor * weight) := by ring
      _ ≤ 504 * (factor * weight) := Nat.mul_le_mul_right _ (by decide)
      _ = 72 * factor * weight * 7 := by ring
  exact Nat.le_of_mul_le_mul_right scaled (by decide)

/-- The first part of `lambda_t` holds `40 / 64` of the pass and `72 / 64` of the sync debits. -/
private theorem penaltyParts_le {first sync factor weight root : Nat}
    (firstLe : first ≤ 40 * factor * weight / (64 * root))
    (syncLe : sync ≤ 72 * factor * weight / (64 * root)) :
    first + sync ≤ (3 + BASE_REWARDS_PER_EPOCH.toNat) * factor * weight /
      (BASE_REWARDS_PER_EPOCH.toNat * root) := by
  have joined := (Nat.add_le_add firstLe syncLe).trans
    (Nat.div_add_div_le_add_div (x := 40 * factor * weight) (y := 72 * factor * weight)
      (z := 64 * root))
  change first + sync ≤ 7 * factor * weight / (4 * root)
  have same : 40 * factor * weight + 72 * factor * weight = 16 * (7 * factor * weight) := by ring
  rw [same, show 64 * root = 16 * (4 * root) by ring,
    Nat.mul_div_mul_left _ _ (by decide : 0 < 16)] at joined
  exact joined

/-- The penalties of one rewards pass and the sync debits of its epoch fit `lambda_t`.

The pass is replayed from `state`, after the update of the scores, over a set `S` of keys.

Each score of `S` is at most `sigma + bias * (t + 1)`, and their eligible stake at most `W_t`.

`W_t` is the ceiling `T_plus_t` plus `Y`.

The total active balance `T` lies between `T_minus_t` and `W_t`.

The sync debits of the epoch, times `28`, are at most the issuance envelope of `T`. -/
theorem epoch_penalty_envelope
    {fork : Fork} {state : BeaconState preset fork} {total : Gwei} {x : ForkedBeaconState preset}
    {high t : Nat} (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    {rewarded : BalanceReplay preset fork}
    (replayed : replayRewards (config := config) (state, []) = .ok rewarded)
    (active : getTotalActiveBalance state = .ok total) (S : Finset Nat)
    (inside : ∀ j ∈ S, j < state.validators.data.size)
    (scores : ∀ j ∈ S, ∀ score : UInt64,
      (state.inactivityScores altair).data[j]? = some score →
        score.toNat ≤ startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1))
    (weight : (∑ j ∈ S, eligibleWeight state j) ≤
      stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (floor : stakeFloorAt config x high t ≤ total.toNat)
    (totalLe : total.toNat ≤ stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (positive : 0 < stakeFloorAt config x high t)
    (divisor : 0 < inactivityPenaltyDivisor preset config)
    {sync : Nat} (syncLe : sync * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat) :
    (∑ j ∈ S, (rewarded.2.map (penaltyDebit j)).sum) + sync ≤
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) (stakeFloorAt config x high t)
            t := by
  have bound := passPenalties_le altair within replayed active S inside scores
  generalize stakeCeilingAt config x high t + slashedUnwithdrawnStake x = cap at *
  generalize stakeFloorAt config x high t = lower at *
  have rootPositive : 0 < lower.sqrt := Nat.sqrt_pos.mpr positive
  have roots := Nat.sqrt_le_sqrt floor
  have quotient : inactivityPenaltyDivisor preset config ≤ config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat := by
    unfold inactivityPenaltyDivisor
    apply Nat.mul_le_mul_left
    simp only [parameters]
    split_ifs <;> omega
  -- `sqrt T * sqrt L <= T <= W` and `L <= T <= W` place the sync debits in the free part.
  have product : total.toNat.sqrt * lower.sqrt ≤ cap :=
    (Nat.mul_le_mul_left _ roots).trans ((Nat.sqrt_le _).trans totalLe)
  have syncFree := sync_le_penaltySlack syncLe product (floor.trans totalLe) positive
  -- The pass takes `40 / 64` of the base rewards of its eligible stake, at `sqrt L <= sqrt T`.
  have firstLe : (TIMELY_SOURCE_WEIGHT.toNat + TIMELY_TARGET_WEIGHT.toNat) *
      preset.BASE_REWARD_FACTOR.toNat * (∑ j ∈ S, eligibleWeight state j) /
        (WEIGHT_DENOMINATOR.toNat * total.toNat.sqrt) ≤
      40 * preset.BASE_REWARD_FACTOR.toNat * cap / (64 * lower.sqrt) := by
    change 40 * preset.BASE_REWARD_FACTOR.toNat * _ / (64 * _) ≤ _
    exact (Nat.div_le_div_right (Nat.mul_le_mul_left _ weight)).trans
      (Nat.div_le_div_left (Nat.mul_le_mul_left 64 roots) (Nat.mul_pos (by decide) rootPositive))
  have leakLe : (∑ j ∈ S, eligibleWeight state j) *
      (startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) ≤
      cap * (startInactivityScore config x + config.INACTIVITY_SCORE_BIAS.toNat * (t + 1)) /
        inactivityPenaltyDivisor preset config :=
    (Nat.div_le_div_right (Nat.mul_le_mul_right _ weight)).trans
      (Nat.div_le_div_left quotient divisor)
  have parts := penaltyParts_le firstLe syncFree
  unfold epochPenalty
  omega

/-- The sync debits of an epoch with no rewards pass fit `lambda_t` alone.

The total active balance `T` is at most `W_t`, and so is the floor `T_minus_t`.

No lower bound of `T` is needed: `sqrt T * sqrt L` is at most the larger of `T` and `L`. -/
theorem sync_penalty_envelope {x : ForkedBeaconState preset} {high t total sync : Nat}
    (syncLe : sync * 28 ≤ preset.epochIssuanceBeforeAltair total)
    (totalLe : total ≤ stakeCeilingAt config x high t + slashedUnwithdrawnStake x)
    (lowerLe : stakeFloorAt config x high t ≤ stakeCeilingAt config x high t +
          slashedUnwithdrawnStake x)
    (positive : 0 < stakeFloorAt config x high t) :
    sync ≤ epochPenalty preset config (startInactivityScore config x)
      (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) (stakeFloorAt config x high t)
          t := by
  generalize stakeCeilingAt config x high t + slashedUnwithdrawnStake x = cap at *
  generalize stakeFloorAt config x high t = lower at *
  have product : total.sqrt * lower.sqrt ≤ cap := by
    rcases Nat.le_total total lower with low | low
    · exact (Nat.mul_le_mul_right _ (Nat.sqrt_le_sqrt low)).trans ((Nat.sqrt_le _).trans lowerLe)
    · exact (Nat.mul_le_mul_left _ (Nat.sqrt_le_sqrt low)).trans ((Nat.sqrt_le _).trans totalLe)
  have parts := penaltyParts_le (first := 0) (Nat.zero_le _)
    (sync_le_penaltySlack syncLe product lowerLe positive)
  rw [Nat.zero_add] at parts
  unfold epochPenalty
  exact parts.trans (Nat.le_add_right _ _)

end

end EthLib.Consensus.DirectSafety.Apriori.Internal

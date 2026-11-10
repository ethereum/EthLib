module

public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Totality.Bound

/-!
# Proofs: the slashing penalties of an epoch succeed

The step sums the slashed balances of the recent epochs, and scales the sum by a multiplier.

It also sums the active effective balances.

Each slashed validator halfway to its withdrawal then loses a share of the scaled sum.

Each sum and each product is checked, so large amounts can make the step fail.

The step succeeds when the sums and the effective balances are small enough.

The registry must hold one balance for each validator, and stay within its limit.

Before Electra the share is a product of the effective balance in increments and the active balance.

That product must stay below 2^64 Gwei.

From Electra the step divides the active balance by the increment.

So the increment must be positive.

The specification also fails there on a zero increment.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state : BeaconState preset fork}

/-- A fold of checked sums succeeds when the start and the list sum below 2^64.

It returns the sum on natural numbers. -/
private theorem foldlM_addChecked_exists (list : List Gwei) (start : Gwei)
    (fits : start.toNat + (list.map (·.toNat)).sum < 2 ^ 64) :
    ∃ sum, list.foldlM addChecked start = .ok sum ∧
      sum.toNat = start.toNat + (list.map (·.toNat)).sum := by
  induction list generalizing start with
  | nil => exact ⟨start, rfl, by simp⟩
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons] at fits ⊢
    have step := addChecked_of_lt (a := start) (b := head) (by omega)
    obtain ⟨sum, computed, value⟩ := ih (start + head) (by rw [toNat_add_of_lt (by omega)]; omega)
    exact ⟨sum, by rw [List.foldlM_cons, step]; exact computed,
      by rw [value, toNat_add_of_lt (by omega)]; omega⟩

/-- The marked sum of the effective balances is at most the sum of all of them. -/
private theorem sumMarked_le_effectiveBalanceSum (marks : Array Bool) :
    sumMarked state.validators.data marks ≤ effectiveBalanceSum state := by
  rw [sumMarked_eq_sum]
  have : effectiveBalanceSum state = ((List.range state.validators.data.size).map fun j =>
      ((state.validators.data[j]?).map (·.effectiveBalance.toNat)).getD 0).sum := by
    unfold effectiveBalanceSum
    congr 1
    apply List.ext_getElem
    · simp
    · intro i first second
      simp [Array.getElem?_eq_getElem (by simpa using first)]
  rw [this]
  refine sum_map_le_sum_map fun j _ => ?_
  split <;> omega

/-- The total active balance succeeds, and is one increment or at most the sum of the balances.

It is at least one increment. -/
private theorem getTotalActiveBalance_exists (within : state.RegistryWithinLimit)
    (summed : effectiveBalanceSum state < 2 ^ 64) :
    ∃ total, getTotalActiveBalance state = .ok total ∧
      preset.EFFECTIVE_BALANCE_INCREMENT ≤ total ∧
      (total = preset.EFFECTIVE_BALANCE_INCREMENT ∨ total.toNat ≤ effectiveBalanceSum state) := by
  have inside : ∀ i ∈ getActiveValidatorIndices state (getCurrentEpoch state),
      i.toNat < state.validators.data.size := by
    intro i member
    obtain ⟨_, found, -⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have lt := Nat.lt_of_le_of_lt (sumMarked_le_effectiveBalanceSum (state := state)
    (markIndices state.validators.data.size
      (getActiveValidatorIndices state (getCurrentEpoch state)))) summed
  have ok : getTotalActiveBalance state = .ok (max preset.EFFECTIVE_BALANCE_INCREMENT
      (sumMarked state.validators.data (markIndices state.validators.data.size
        (getActiveValidatorIndices state (getCurrentEpoch state)))).toUInt64) :=
    getTotalBalance_ok_iff.mpr ⟨inside, lt, rfl⟩
  refine ⟨_, ok, le_getTotalBalance ok, ?_⟩
  rw [UInt64.max_def]
  split
  · right
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt lt]
    exact sumMarked_le_effectiveBalanceSum _
  · exact .inl rfl

/-- A state has the registry, the slot and the sizes of another. -/
private def Kept (state current : BeaconState preset fork) : Prop :=
  current.validators = state.validators ∧ current.slot = state.slot ∧ SameSizes state current

/-- Lowering a balance at a position of the registry succeeds and keeps the state. -/
private theorem decreaseBalance_kept {current : BeaconState preset fork}
    (matched : BalancesMatch state) (kept : Kept state current) {index : Nat}
    (lt : index < state.validators.data.size) (within : state.RegistryWithinLimit)
    (penalty : Gwei) :
    ∃ after, decreaseBalance current index.toUInt64 penalty = .ok after ∧ Kept state after := by
  have round := toNat_toUInt64_of_lt within lt
  have inside : index.toUInt64.toNat < current.balances.data.size := by
    rw [round, kept.2.2.2, matched]
    exact lt
  refine ⟨_, decreaseBalance_eq_ok_iff.mpr ⟨inside, rfl⟩, ?_⟩
  exact ⟨kept.1, kept.2.1, by simp [SameSizes, BeaconState.putBalance, kept.2.2.1, kept.2.2.2]⟩

/-- The validator read at a position of the registry is the one of the registry. -/
private theorem getValidator_kept {current : BeaconState preset fork} (kept : Kept state current)
    (within : state.RegistryWithinLimit) {index : Nat} (lt : index < state.validators.data.size) :
    getValidator current index.toUInt64 = .ok state.validators.data[index] := by
  rw [getValidator_eq_ok_iff, toNat_toUInt64_of_lt within lt, kept.1,
    Array.getElem?_eq_getElem lt]

/-- The penalty step from Electra succeeds when the penalty per increment fits the balances. -/
private theorem applySlashingPenaltyElectra_exists (within : state.RegistryWithinLimit)
    (matched : BalancesMatch state) (perIncrement : Gwei)
    (halfway : (getCurrentEpoch state).toNat +
      (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < 2 ^ 64)
    (fits : ∀ validator ∈ state.validators.data, perIncrement.toNat *
      (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat < 2 ^ 64)
    {current : BeaconState preset fork} (kept : Kept state current) {index : Nat}
    (lt : index < state.validators.data.size) :
    ∃ after, applySlashingPenaltyElectra current perIncrement index = .ok after ∧
      Kept state after := by
  have found := getValidator_kept kept within lt
  have epoch : getCurrentEpoch current = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [kept.2.1]
  have read : liftAccessor (getValidator current index.toUInt64) =
      .ok state.validators.data[index] := by rw [found]; rfl
  have due : liftAccessor (liftArith (addChecked (getCurrentEpoch current)
      (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2))) =
      .ok (getCurrentEpoch state + preset.EPOCHS_PER_SLASHINGS_VECTOR / 2) := by
    rw [epoch, addChecked_of_lt halfway]; rfl
  unfold applySlashingPenaltyElectra
  rw [read]
  simp only [bind, Except.bind]
  by_cases isSlashed : state.validators.data[index].slashed = true
  · simp only [isSlashed, ↓reduceIte]
    rw [due]
    simp only
    by_cases isDue : getCurrentEpoch state + preset.EPOCHS_PER_SLASHINGS_VECTOR / 2 =
        state.validators.data[index].withdrawableEpoch
    · simp only [isDue, ↓reduceIte]
      have product := fits _ (Array.getElem_mem lt)
      have penalty : liftAccessor (liftArith (mulChecked perIncrement
          (state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT))) = .ok (perIncrement *
          (state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT)) := by
        rw [mulChecked_of_lt product]; rfl
      rw [penalty]
      obtain ⟨after, lowered, kept'⟩ := decreaseBalance_kept matched kept lt within
        (perIncrement * (state.validators.data[index].effectiveBalance /
          preset.EFFECTIVE_BALANCE_INCREMENT))
      exact ⟨after, liftAccessor_ok.mpr lowered, kept'⟩
    · simp only [isDue, ↓reduceIte]
      exact ⟨current, rfl, kept⟩
  · simp only [isSlashed]
    exact ⟨current, rfl, kept⟩

/-- The penalty step before Electra succeeds when its two products fit. -/
private theorem applySlashingPenalty_exists (within : state.RegistryWithinLimit)
    (matched : BalancesMatch state) (total adjusted : Gwei)
    (halfway : (getCurrentEpoch state).toNat +
      (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < 2 ^ 64)
    (numeratorFits : ∀ validator ∈ state.validators.data,
      (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat * adjusted.toNat <
        2 ^ 64)
    (penaltyFits : ∀ validator ∈ state.validators.data,
      ((validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat * adjusted.toNat /
        total.toNat) * preset.EFFECTIVE_BALANCE_INCREMENT.toNat < 2 ^ 64)
    {current : BeaconState preset fork} (kept : Kept state current) {index : Nat}
    (lt : index < state.validators.data.size) :
    ∃ after, applySlashingPenalty current total adjusted index = .ok after ∧
      Kept state after := by
  have found := getValidator_kept kept within lt
  have epoch : getCurrentEpoch current = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [kept.2.1]
  have read : liftAccessor (getValidator current index.toUInt64) =
      .ok state.validators.data[index] := by rw [found]; rfl
  have due : liftAccessor (liftArith (addChecked (getCurrentEpoch current)
      (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2))) =
      .ok (getCurrentEpoch state + preset.EPOCHS_PER_SLASHINGS_VECTOR / 2) := by
    rw [epoch, addChecked_of_lt halfway]; rfl
  unfold applySlashingPenalty
  rw [read]
  simp only [bind, Except.bind]
  by_cases isSlashed : state.validators.data[index].slashed = true
  · simp only [isSlashed, ↓reduceIte]
    rw [due]
    simp only
    by_cases isDue : getCurrentEpoch state + preset.EPOCHS_PER_SLASHINGS_VECTOR / 2 =
        state.validators.data[index].withdrawableEpoch
    · simp only [isDue, ↓reduceIte]
      have first := numeratorFits _ (Array.getElem_mem lt)
      have second := penaltyFits _ (Array.getElem_mem lt)
      have numerator : liftAccessor (liftArith (mulChecked
          (state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT) adjusted)) = .ok
          ((state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT) * adjusted) := by
        rw [mulChecked_of_lt first]; rfl
      rw [numerator]
      simp only
      have penalty : liftAccessor (liftArith (mulChecked
          (((state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT) * adjusted) / total)
          preset.EFFECTIVE_BALANCE_INCREMENT)) = .ok
          ((((state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT) * adjusted) / total) *
            preset.EFFECTIVE_BALANCE_INCREMENT) := by
        rw [mulChecked_of_lt (by
          rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt first]
          exact second)]
        rfl
      rw [penalty]
      obtain ⟨after, lowered, kept'⟩ := decreaseBalance_kept matched kept lt within
        ((((state.validators.data[index].effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT) * adjusted) / total) *
            preset.EFFECTIVE_BALANCE_INCREMENT)
      exact ⟨after, liftAccessor_ok.mpr lowered, kept'⟩
    · simp only [isDue]
      exact ⟨current, rfl, kept⟩
  · simp only [isSlashed]
    exact ⟨current, rfl, kept⟩

/-- The slashing penalties of an epoch succeed when every sum and product fits in 64 bits.

The sum of the effective balances must be below 2^64 Gwei, and each one below 2^63 Gwei.

The sum of the slashed balances of the recent epochs must fit, and so must its scaled value.

The epoch at which a slashed validator is halfway to its withdrawal must exist.

Before Electra the effective balance in increments must fit when multiplied by a sum.

That sum is the sum of the effective balances.

The divisors of the preset must be positive, as the step from Electra divides by the increment.

The registry must hold one balance for each validator, and stay within its limit. -/
theorem processSlashings_total (divisors : preset.DivisorsPositive)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (summed : effectiveBalanceSum state < 2 ^ 64)
    (effective : ∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < 2 ^ 63)
    (fits : slashedBalanceSum state < 2 ^ 64)
    (slashed : slashedBalanceSum state *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat < 2 ^ 64)
    (halfway : (getCurrentEpoch state).toNat + (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat <
      2 ^ 64)
    (product : fork < .pectra → ∀ validator ∈ state.validators.data,
      (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
        effectiveBalanceSum state < 2 ^ 64) :
    ∃ after, processSlashings state = .ok after := by
  obtain ⟨total, totalOk, incLe, totalCases⟩ := getTotalActiveBalance_exists within summed
  obtain ⟨sum, sumOk, sumVal⟩ := foldlM_addChecked_exists state.slashings.elements.toList 0
    (by simpa [slashedBalanceSum] using fits)
  have sumOk' : slashingsSum state = .ok sum := by
    unfold slashingsSum
    rw [sumOk]
    rfl
  have product' : (sum * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER).toNat =
      sum.toNat * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt]
    rw [sumVal]
    simpa [slashedBalanceSum] using slashed
  have mulOk : liftAccessor (liftArith (mulChecked sum
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER)) =
      .ok (sum * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER) := by
    rw [mulChecked_of_lt (by rw [sumVal]; simpa [slashedBalanceSum] using slashed)]
    rfl
  have totalOk' : liftAccessor (getTotalActiveBalance state) = .ok total := by
    rw [totalOk]
    rfl
  unfold processSlashings
  simp only [bind, Except.bind, totalOk', sumOk', mulOk]
  generalize sum * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER = scaled
  have minLe : (min scaled total).toNat ≤ total.toNat :=
    UInt64.le_iff_toNat_le.mp (by
      rw [UInt64.min_def]
      split
      · assumption
      · exact UInt64.le_refl _)
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.pos_of_ne_zero fun zero => divisors.increment (UInt64.toNat_inj.mp zero)
  have incLe' : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ total.toNat :=
    UInt64.le_iff_toNat_le.mp incLe
  have quotient : ∀ validator : Validator,
      (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ validator.effectiveBalance.toNat := by
    intro validator
    rw [UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  by_cases electra : Fork.pectra ≤ fork
  · simp only [electra, ↓reduceIte]
    obtain ⟨quotientValue, quotientOk⟩ : ∃ r, divChecked total
        preset.EFFECTIVE_BALANCE_INCREMENT = .ok r :=
      ⟨_, divChecked_ok_iff.mpr ⟨divisors.increment, UInt64.toNat_div _ _⟩⟩
    have rValue := (divChecked_ok_iff.mp quotientOk).2
    have rPos : 0 < quotientValue.toNat := by
      rw [rValue]
      exact Nat.div_pos incLe' incPos
    obtain ⟨perIncrement, perOk⟩ : ∃ c, divChecked (min scaled total) quotientValue = .ok c :=
      ⟨_, divChecked_ok_iff.mpr ⟨fun zero => by simp [zero] at rPos, UInt64.toNat_div _ _⟩⟩
    have cValue := (divChecked_ok_iff.mp perOk).2
    simp only [quotientOk, perOk, liftArith, Except.mapError, liftAccessor]
    have small : perIncrement.toNat < 2 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      have above : total.toNat < preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat + 1) :=
        Nat.lt_mul_div_succ _ incPos
      have times : perIncrement.toNat * quotientValue.toNat ≤ (min scaled total).toNat := by
        rw [cValue]
        exact Nat.div_mul_le_self _ _
      rw [← rValue] at above
      have grow : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (quotientValue.toNat + 1) =
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * quotientValue.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat := Nat.mul_succ _ _
      have atLeast : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * quotientValue.toNat :=
        Nat.le_mul_of_pos_right _ rPos
      have double : 2 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat * quotientValue.toNat =
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * quotientValue.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat * quotientValue.toNat := by
        rw [Nat.mul_assoc, Nat.two_mul]
      refine Nat.lt_of_mul_lt_mul_right (a := quotientValue.toNat) ?_
      omega
    refine foldlM_exists_ok_of_invariant (Kept state) (fun current index member kept => ?_)
      state ⟨rfl, rfl, SameSizes.refl state⟩
    refine applySlashingPenaltyElectra_exists within matched perIncrement halfway
      (fun validator member => ?_) kept (List.mem_range.mp member)
    have := quotient validator
    have := effective validator member
    have : perIncrement.toNat * (validator.effectiveBalance /
        preset.EFFECTIVE_BALANCE_INCREMENT).toNat ≤
        (2 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * (validator.effectiveBalance /
          preset.EFFECTIVE_BALANCE_INCREMENT).toNat :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt small)
    have double : 2 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (validator.effectiveBalance /
        preset.EFFECTIVE_BALANCE_INCREMENT).toNat = 2 * ((validator.effectiveBalance /
          preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
      rw [Nat.mul_assoc, Nat.mul_comm preset.EFFECTIVE_BALANCE_INCREMENT.toNat]
    omega
  · have before : fork < Fork.pectra := Nat.lt_of_not_le electra
    simp only [electra, ↓reduceIte]
    refine foldlM_exists_ok_of_invariant (Kept state) (fun current index member kept => ?_)
      state ⟨rfl, rfl, SameSizes.refl state⟩
    refine applySlashingPenalty_exists within matched total (min scaled total) halfway
      (fun validator member => ?_) (fun validator member => ?_) kept (List.mem_range.mp member)
    · have times : (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
          (min scaled total).toNat ≤ (validator.effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT).toNat * total.toNat :=
        Nat.mul_le_mul_left _ minLe
      have := quotient validator
      have := effective validator member
      rcases totalCases with same | bounded
      · have same' : (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
            total.toNat = (validator.effectiveBalance /
              preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by rw [same]
        omega
      · have := product before validator member
        have : (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
            total.toNat ≤ (validator.effectiveBalance /
              preset.EFFECTIVE_BALANCE_INCREMENT).toNat * effectiveBalanceSum state :=
          Nat.mul_le_mul_left _ bounded
        omega
    · have times : (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT).toNat *
          (min scaled total).toNat ≤ total.toNat * (validator.effectiveBalance /
            preset.EFFECTIVE_BALANCE_INCREMENT).toNat := by
        rw [Nat.mul_comm total.toNat]
        exact Nat.mul_le_mul_left _ minLe
      have share := Nat.div_le_of_le_mul times
      have := quotient validator
      have := effective validator member
      have := Nat.mul_le_mul_right preset.EFFECTIVE_BALANCE_INCREMENT.toNat share
      omega

end EthLib.Consensus

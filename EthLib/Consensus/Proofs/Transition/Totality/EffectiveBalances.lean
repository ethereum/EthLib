module

public import EthLib.Consensus.Proofs.Transition.EpochUpdates

/-!
# Proofs: the update of the effective balances succeeds

The update adds a band of hysteresis to each balance and to each effective balance.

Each sum is checked, so an amount near 2^64 Gwei makes the update fail.

The update succeeds when each balance and each effective balance is below 2^63 Gwei.

The two bands of the preset must also be below 2^63 Gwei, as they are on mainnet and minimal.

The registry must hold one balance for each validator, and stay within its limit.

The update leaves the balances unchanged.

It changes only the effective balance of each validator.

The new effective balance is the old one, or at most both the balance and its largest value.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The two bands of hysteresis of a preset are each below 2^63 Gwei. -/
abbrev Preset.HysteresisBandsBelow (preset : Preset) : Prop :=
  (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT).toNat *
      preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat < 2 ^ 63 ∧
    (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT).toNat *
      preset.HYSTERESIS_UPWARD_MULTIPLIER.toNat < 2 ^ 63

/-- The bands of hysteresis of the mainnet preset are below 2^63 Gwei. -/
theorem Preset.hysteresisBandsBelow_mainnet : Preset.mainnet.HysteresisBandsBelow := by
  decide

/-- The bands of hysteresis of the minimal preset are below 2^63 Gwei. -/
theorem Preset.hysteresisBandsBelow_minimal : Preset.minimal.HysteresisBandsBelow := by
  decide

/-- An updated effective balance succeeds when each amount is below 2^63 Gwei. -/
private theorem updatedEffectiveBalance_exists_ok {largest balance effectiveBalance : Gwei}
    (bands : preset.HysteresisBandsBelow) (low : balance.toNat < 2 ^ 63)
    (old : effectiveBalance.toNat < 2 ^ 63) :
    ∃ result, updatedEffectiveBalance preset largest balance effectiveBalance = .ok result := by
  obtain ⟨down, up⟩ := bands
  have downOk := mulChecked_of_lt (Nat.lt_trans down (by decide))
  have upOk := mulChecked_of_lt (Nat.lt_trans up (by decide))
  have downNat := (mulChecked_ok_iff.mp downOk).2
  have upNat := (mulChecked_ok_iff.mp upOk).2
  have sumDown := addChecked_of_lt (a := balance)
    (b := preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT *
      preset.HYSTERESIS_DOWNWARD_MULTIPLIER) (by omega)
  have sumUp := addChecked_of_lt (a := effectiveBalance)
    (b := preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT *
      preset.HYSTERESIS_UPWARD_MULTIPLIER) (by omega)
  simp only [updatedEffectiveBalance, leavesBand, liftAccessor, liftArith, downOk, upOk, sumDown,
    sumUp, Except.mapError, bind, Except.bind, pure, Except.pure]
  split <;> rename_i heq <;> split at heq <;> simp_all

/-- An updated effective balance stays below 2^63 Gwei when the old one and the balance are. -/
private theorem updatedEffectiveBalance_lt {largest balance effectiveBalance result : Gwei}
    (low : balance.toNat < 2 ^ 63) (old : effectiveBalance.toNat < 2 ^ 63)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result.toNat < 2 ^ 63 := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact old
  · have rounded := UInt64.le_iff_toNat_le.mp (UInt64.sub_le
      (a := balance) (b := balance % preset.EFFECTIVE_BALANCE_INCREMENT)
      (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)))
    rw [UInt64.min_def]
    split
    · omega
    · rename_i h
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
      omega

/-- The update of one effective balance keeps the balances, and the bound on effective balances.

The balances and the effective balances must be below 2^63 Gwei before. -/
private theorem updateEffectiveBalance_keeps {index : Nat}
    (balances : ∀ balance ∈ state.balances.data, balance.toNat < 2 ^ 63)
    (effective : ∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < 2 ^ 63)
    (computed : updateEffectiveBalance state index = .ok after) :
    after.balances = state.balances ∧
      ∀ validator ∈ after.validators.data, validator.effectiveBalance.toNat < 2 ^ 63 := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, balance, read, effectiveBalance, updated, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨rfl, fun other member => ?_⟩
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set (w := inside) member with old | rfl
  · exact effective other old
  · exact updatedEffectiveBalance_lt
      (balances _ (Array.mem_of_getElem? (getBalance_eq_ok_iff.mp read)))
      (effective _ (Array.mem_of_getElem? (getValidator_eq_ok_iff.mp found))) updated

/-- The update of one effective balance keeps the balances, and replaces one validator.

The new validator is the old one at the position, with its updated effective balance. -/
private theorem updateEffectiveBalance_ok {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) :
    after.balances = state.balances ∧ ∃ validator balance effectiveBalance,
      state.validators.data[index.toUInt64.toNat]? = some validator ∧
        state.balances.data[index.toUInt64.toNat]? = some balance ∧
        updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork validator)
          balance validator.effectiveBalance = .ok effectiveBalance ∧
        ∀ j, after.validators.data[j]? = if index.toUInt64.toNat = j
          then some { validator with effectiveBalance } else state.validators.data[j]? := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, balance, read, effectiveBalance, updated, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨rfl, validator, balance, effectiveBalance, getValidator_eq_ok_iff.mp found,
    getBalance_eq_ok_iff.mp read, updated, fun j => ?_⟩
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set]

/-- The update of one effective balance succeeds at a position of the registry.

Every amount must be below 2^63 Gwei, and the registry must hold one balance per validator. -/
private theorem updateEffectiveBalance_exists_ok {index : Nat} (bands : preset.HysteresisBandsBelow)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (lt : index < state.validators.data.size)
    (balances : ∀ balance ∈ state.balances.data, balance.toNat < 2 ^ 63)
    (effective : ∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < 2 ^ 63) :
    ∃ after, updateEffectiveBalance state index = .ok after := by
  have round := toNat_toUInt64_of_lt within lt
  have balanceLt : index < state.balances.data.size := by
    unfold BalancesMatch at matched
    omega
  have found : getValidator state index.toUInt64 = .ok state.validators.data[index] := by
    rw [getValidator_eq_ok_iff, round, Array.getElem?_eq_getElem lt]
  have read : getBalance state index.toUInt64 = .ok state.balances.data[index] := by
    rw [getBalance_eq_ok_iff, round, Array.getElem?_eq_getElem balanceLt]
  obtain ⟨effectiveBalance, updated⟩ := updatedEffectiveBalance_exists_ok
    (largest := withdrawalMaxEffectiveBalance preset fork state.validators.data[index]) bands
    (balances _ (Array.getElem_mem balanceLt)) (effective _ (Array.getElem_mem lt))
  have inside : index.toUInt64.toNat < state.validators.data.size := round.symm ▸ lt
  have set : state.setValidator index.toUInt64
      { state.validators.data[index] with effectiveBalance } =
        .ok (state.putValidator index.toUInt64.toNat inside
          { state.validators.data[index] with effectiveBalance }) := by
    unfold BeaconState.setValidator
    rw [dite_eq_left_of_eq_true (eq_true inside)]
  refine ⟨state.putValidator index.toUInt64.toNat inside
    { state.validators.data[index] with effectiveBalance }, ?_⟩
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok]
  exact ⟨_, found, _, read, _, updated, set⟩

/-- The update of the effective balances succeeds when every amount is below 2^63 Gwei.

The amounts are the balances, the effective balances and the two bands of the preset.

The registry must hold one balance for each validator, and stay within its limit. -/
theorem processEffectiveBalanceUpdates_total (bands : preset.HysteresisBandsBelow)
    (within : state.RegistryWithinLimit) (matched : BalancesMatch state)
    (balances : ∀ balance ∈ state.balances.data, balance.toNat < 2 ^ 63)
    (effective : ∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < 2 ^ 63) :
    ∃ after, processEffectiveBalanceUpdates state = .ok after := by
  unfold processEffectiveBalanceUpdates
  refine foldlM_exists_ok_of_invariant (fun current : BeaconState preset fork =>
      SameSizes state current ∧ current.balances = state.balances ∧
        ∀ validator ∈ current.validators.data, validator.effectiveBalance.toNat < 2 ^ 63)
    ?_ state ⟨SameSizes.refl state, rfl, effective⟩
  rintro current index member ⟨sizes, kept, bounded⟩
  have currentBalances : ∀ balance ∈ current.balances.data, balance.toNat < 2 ^ 63 :=
    kept ▸ balances
  obtain ⟨next, computed⟩ := updateEffectiveBalance_exists_ok bands
    (show current.validators.data.size ≤ _ by rw [sizes.1]; exact within)
    (balancesMatch_of_sameSizes sizes matched)
    (by rw [sizes.1]; exact List.mem_range.mp member) currentBalances bounded
  obtain ⟨same, below⟩ := updateEffectiveBalance_keeps currentBalances bounded computed
  exact ⟨next, computed, sizes.trans (sameSizes_updateEffectiveBalance computed),
    same.trans kept, below⟩

/-- The update of the effective balances leaves the balances unchanged. -/
theorem processEffectiveBalanceUpdates_balances
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    after.balances = state.balances := by
  unfold processEffectiveBalanceUpdates at computed
  exact foldlM_ok_invariant (fun current : BeaconState preset fork =>
      current.balances = state.balances)
    (fun _ _ _ kept step => (updateEffectiveBalance_ok step).1.trans kept) rfl computed

/-- The update changes only the effective balance of each validator.

The new effective balance is the old one, or at most both the balance and its largest value.

The largest value is that of the fork, which from Electra depends on the credentials.

The registry must stay within its limit, so that each position is read and written once. -/
theorem processEffectiveBalanceUpdates_effectiveBalance (within : state.RegistryWithinLimit)
    (computed : processEffectiveBalanceUpdates state = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    {balance : Gwei} (owned : state.balances.data[index]? = some balance) :
    ∃ effectiveBalance : Gwei,
      after.validators.data[index]? = some { validator with effectiveBalance } ∧
        (effectiveBalance = validator.effectiveBalance ∨
          effectiveBalance ≤ balance ∧
            effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator) := by
  unfold processEffectiveBalanceUpdates at computed
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  let H : Nat → Option Validator → Option Validator := fun _ current => current.map fun old =>
    match updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork old) balance
        old.effectiveBalance with
    | .ok effectiveBalance => { old with effectiveBalance }
    | .error _ => old
  have round : ∀ current : BeaconState preset fork, SameSizes state current →
      ∀ j ∈ List.range state.validators.data.size, j.toUInt64.toNat = j :=
    fun current sizes j member => toNat_toUInt64_of_lt
      (show current.validators.data.size ≤ _ by rw [sizes.1]; exact within)
      (by rw [sizes.1]; exact List.mem_range.mp member)
  obtain ⟨-, -, changed⟩ := foldlM_ok_pointwise
    (fun current => SameSizes state current ∧ current.balances = state.balances)
    (fun current => current.validators.data[index]?) id index H
    (by simpa using List.nodup_range)
    (fun _ _ _ _ ⟨sizes, kept⟩ step =>
      ⟨sizes.trans (sameSizes_updateEffectiveBalance step),
        (updateEffectiveBalance_ok step).1.trans kept⟩)
    (fun j member current _ ⟨sizes, _⟩ step other => by
      obtain ⟨-, _, _, _, _, _, _, view⟩ := updateEffectiveBalance_ok step
      simp only [view, round current sizes j member, show j ≠ index from other, ite_false])
    (fun j member current _ ⟨sizes, kept⟩ step same => by
      obtain ⟨-, old, read, _, located, owner, updated, view⟩ := updateEffectiveBalance_ok step
      rw [round current sizes j member] at located owner view
      rw [id] at same
      subst same
      rw [kept, owned, Option.some.injEq] at owner
      subst owner
      simp only [view, ite_true, located, H, Option.map_some, updated])
    ⟨SameSizes.refl state, rfl⟩ computed
  rw [changed index (List.mem_range.mpr inside) rfl, found]
  simp only [H, Option.map_some]
  split
  · rename_i effectiveBalance updated
    refine ⟨effectiveBalance, rfl, ?_⟩
    rcases updatedEffectiveBalance_cases updated with rfl | rfl
    · exact Or.inl rfl
    · have rounded := UInt64.le_iff_toNat_le.mp (UInt64.sub_le
        (a := balance) (b := balance % preset.EFFECTIVE_BALANCE_INCREMENT)
        (UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)))
      rw [UInt64.min_def]
      split
      · rename_i below
        exact Or.inr ⟨UInt64.le_iff_toNat_le.mpr rounded, below⟩
      · rename_i above
        have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp above)
        exact Or.inr ⟨UInt64.le_iff_toNat_le.mpr (by omega), UInt64.le_refl _⟩
  · exact ⟨validator.effectiveBalance, rfl, Or.inl rfl⟩

end EthLib.Consensus

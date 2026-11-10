module

public import EthLib.Consensus.Proofs.Transition.EpochUpdates

/-!
# Proofs: the update of the effective balances succeeds

The update adds a band of hysteresis to each balance and to each effective balance.

Each sum is checked, so an amount near 2^64 Gwei makes the update fail.

The update succeeds when each balance and each effective balance is below 2^63 Gwei.

The two bands of the preset must also be below 2^63 Gwei, as they are on mainnet and minimal.

The registry must hold one balance for each validator, and stay within its limit.

Each new effective balance is then below 2^63 Gwei too, so the bound carries to the next epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The two bands of hysteresis of a preset are each below 2^63 Gwei. -/
abbrev Preset.HysteresisBelow (preset : Preset) : Prop :=
  (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT).toNat *
      preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat < 2 ^ 63 ∧
    (preset.EFFECTIVE_BALANCE_INCREMENT / preset.HYSTERESIS_QUOTIENT).toNat *
      preset.HYSTERESIS_UPWARD_MULTIPLIER.toNat < 2 ^ 63

/-- The bands of hysteresis of the mainnet and minimal presets are below 2^63 Gwei. -/
theorem Preset.hysteresisBelow_named :
    Preset.mainnet.HysteresisBelow ∧ Preset.minimal.HysteresisBelow := by
  decide

/-- An updated effective balance succeeds when each amount is below 2^63 Gwei. -/
private theorem updatedEffectiveBalance_exists_ok {largest balance effectiveBalance : Gwei}
    (bands : preset.HysteresisBelow) (low : balance.toNat < 2 ^ 63)
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

/-- The update of one effective balance succeeds at a position of the registry.

Every amount must be below 2^63 Gwei, and the registry must hold one balance per validator. -/
private theorem updateEffectiveBalance_exists_ok {index : Nat} (bands : preset.HysteresisBelow)
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
theorem processEffectiveBalanceUpdates_total (bands : preset.HysteresisBelow)
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

/-- After the update, each effective balance is below 2^63 Gwei when every amount was before.

Each new effective balance is the old one, or at most the balance. -/
theorem processEffectiveBalanceUpdates_effective_lt
    (balances : ∀ balance ∈ state.balances.data, balance.toNat < 2 ^ 63)
    (effective : ∀ validator ∈ state.validators.data, validator.effectiveBalance.toNat < 2 ^ 63)
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    ∀ validator ∈ after.validators.data, validator.effectiveBalance.toNat < 2 ^ 63 := by
  unfold processEffectiveBalanceUpdates at computed
  refine (foldlM_ok_invariant (fun current : BeaconState preset fork =>
      (∀ balance ∈ current.balances.data, balance.toNat < 2 ^ 63) ∧
        ∀ validator ∈ current.validators.data, validator.effectiveBalance.toNat < 2 ^ 63)
    (fun _ _ _ ⟨low, old⟩ step => ?_) ⟨balances, effective⟩ computed).2
  obtain ⟨same, below⟩ := updateEffectiveBalance_keeps low old step
  exact ⟨same ▸ low, below⟩

end EthLib.Consensus

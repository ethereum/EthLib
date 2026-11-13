module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
public import EthLib.Consensus.Proofs.Transition.EpochDecomposition
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.Totality.EffectiveBalances
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
public import EthLib.Consensus.Proofs.Transition.Totality.Rewards
public import EthLib.Consensus.Proofs.Transition.Totality.RegistryLoad

/-!
# Proofs: the supply grows by at most the issuance over one epoch

The ceiling on a balance after the rewards grows about 4.5 times per epoch on mainnet.

So it cannot bound the next epoch.

The supply grows slowly: the sum of the balances and of the amounts of the pending deposits.

From Altair, only the rewards of the three flags raise it in the epoch transition.

The pending deposits move amounts from the queue to the balances, or drop them.

The other steps keep or lower the balances.

When no flag was set by more balance than is active, the rise is small.

It is at most 54/64 of one base reward for each active increment.

That is at most the base reward factor times two more than the root of the active balance.

The weights of the flags then take 54/64 of it.

The effective balances follow the balances within the hysteresis band.

If each positive effective balance is a whole number of increments, the band is a fraction of it.

So their sum stays at most a fixed multiple of the sum of the balances, 4/3 on mainnet.

From Electra, the pending deposits do not raise the effective balances plus the pending amounts.

A new validator takes at most the amount of its deposit as effective balance.

The pending consolidations keep both sums.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 EpochStage EpochTrace

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- A bound on what the rewards of one epoch add to the supply, from Altair.

It is the base reward factor times two more than the root of the active balance, times 54/64.

The weights of the three flags add up to 54, out of a denominator of 64. -/
def Preset.epochIssuance (preset : Preset) (total : Nat) : Nat :=
  preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt total + 2) * 54 / 64

/-- The bound on the issuance grows with the active balance. -/
theorem Preset.epochIssuance_mono {total total' : Nat} (le : total ≤ total') :
    preset.epochIssuance total ≤ preset.epochIssuance total' := by
  unfold Preset.epochIssuance
  gcongr

/-- On mainnet, at an active balance of `2^57` Gwei, the issuance bound is below `2^35` Gwei.

That is about 1.44 * 10^8 ETH at stake, and about 20.5 ETH of rewards. -/
theorem Preset.epochIssuance_mainnet : Preset.mainnet.epochIssuance (2 ^ 57) < 2 ^ 35 := by
  have root : Nat.sqrt (2 ^ 57) = 379625062 := (Nat.eq_sqrt.mpr ⟨by decide, by decide⟩).symm
  simp only [Preset.epochIssuance, root]
  decide

/-- A whole number of increments within the downward band is at most a multiple of the balance.

The band is the increment over the quotient, times the multiplier. -/
private theorem aligned_mul_le {increment quotient multiplier value balance : Nat}
    (aligned : value % increment = 0)
    (band : value ≤ balance + increment / quotient * multiplier) :
    value * (quotient - multiplier) ≤ balance * quotient := by
  rcases Nat.eq_zero_or_pos value with rfl | positive
  · simp
  have large : increment ≤ value := Nat.le_of_dvd positive (Nat.dvd_of_mod_eq_zero aligned)
  have scaled : value * quotient ≤
      balance * quotient + increment / quotient * quotient * multiplier := by
    calc value * quotient ≤ (balance + increment / quotient * multiplier) * quotient :=
          Nat.mul_le_mul_right _ band
      _ = balance * quotient + increment / quotient * quotient * multiplier := by
          rw [Nat.add_mul, Nat.mul_right_comm]
  have small : increment / quotient * quotient * multiplier ≤ value * multiplier :=
    Nat.mul_le_mul_right _ ((Nat.div_mul_le_self _ _).trans large)
  rw [Nat.mul_sub]
  omega

/-- An updated effective balance is at most a multiple of the balance, if the old one is aligned.

The multiple is the hysteresis quotient over that quotient less the downward multiplier. -/
private theorem updatedEffectiveBalance_mul_le {largest balance effectiveBalance result : Gwei}
    (aligned : effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result.toNat *
        (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
      balance.toNat * preset.HYSTERESIS_QUOTIENT.toNat := by
  have band := updatedEffectiveBalance_le_add computed
  rw [Preset.downwardBand, UInt64.toNat_div] at band
  rcases updatedEffectiveBalance_eq_or_le computed with rfl | ⟨below, -⟩
  · refine aligned_mul_le (increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ?_ band
    rw [← UInt64.toNat_mod, aligned]
    rfl
  · exact Nat.mul_le_mul (UInt64.le_iff_toNat_le.mp below) (Nat.sub_le _ _)

/-- The sum of the balances reads them at each position below their size. -/
private theorem balanceSum_eq_sum_range (state : BeaconState preset fork) :
    balanceSum state = ((List.range state.balances.data.size).map fun j =>
      ((state.balances.data[j]?).map (·.toNat)).getD 0).sum := by
  unfold balanceSum
  congr 1
  apply List.ext_getElem
  · simp
  · intro i first second
    simp [Array.getElem?_eq_getElem (by simpa using first)]

/-- After the update of the effective balances, their sum is at most a multiple of the balances.

The multiple is the hysteresis quotient over that quotient less the downward multiplier.

It says something only when the downward multiplier is below the quotient.

On mainnet it is 4/3.

Each effective balance before the update must be a whole number of increments.

The balances and the registry must have the same size. -/
theorem processEffectiveBalanceUpdates_effectiveBalanceSum_le (matched : BalancesMatch state)
    (aligned : EffectiveBalancesAligned state)
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    effectiveBalanceSum after *
        (preset.HYSTERESIS_QUOTIENT.toNat - preset.HYSTERESIS_DOWNWARD_MULTIPLIER.toNat) ≤
      balanceSum after * preset.HYSTERESIS_QUOTIENT.toNat := by
  have sizes := sameSizes_processEffectiveBalanceUpdates computed
  rw [effectiveBalanceSum_eq_sum_range, balanceSum_eq_sum_range,
    processEffectiveBalanceUpdates_balances computed, sizes.1, matched,
    ← sum_map_mul_right, ← sum_map_mul_right]
  refine sum_map_le_sum_map fun index member => ?_
  have inside := List.mem_range.mp member
  have found := Array.getElem?_eq_getElem inside
  have owned := Array.getElem?_eq_getElem (xs := state.balances.data)
    (by rw [matched]; exact inside)
  obtain ⟨effectiveBalance, updated, scalar⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance_eq computed found owned
  rw [updated, owned]
  exact updatedEffectiveBalance_mul_le (aligned _ (Array.getElem_mem _)) scalar

/-- The rise of the rewards over one epoch is at most the issuance bound.

The rise is one base reward per increment for each active increment, times 54/64. -/
private theorem rise_le_epochIssuance {total increment : Nat} (positive : 0 < total) :
    total / increment * (increment * preset.BASE_REWARD_FACTOR.toNat / Nat.sqrt total) * 54 / 64 ≤
      preset.epochIssuance total := by
  unfold Preset.epochIssuance
  refine Nat.div_le_div_right (Nat.mul_le_mul_right _ ?_)
  have rootPositive : 0 < Nat.sqrt total := Nat.sqrt_pos.mpr positive
  -- The total is below the square of the root plus one.
  have below : total ≤ Nat.sqrt total * (Nat.sqrt total + 2) := by
    have := Nat.lt_succ_sqrt total
    rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.mul_add] at this
    rw [Nat.mul_add]
    omega
  calc total / increment * (increment * preset.BASE_REWARD_FACTOR.toNat / Nat.sqrt total)
      ≤ total / increment * (increment * preset.BASE_REWARD_FACTOR.toNat) / Nat.sqrt total :=
        Nat.mul_div_le_mul_div_assoc _ _ _
    _ ≤ total * preset.BASE_REWARD_FACTOR.toNat / Nat.sqrt total := by
        refine Nat.div_le_div_right ?_
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ ≤ Nat.sqrt total * ((Nat.sqrt total + 2) * preset.BASE_REWARD_FACTOR.toNat) /
          Nat.sqrt total := by
        refine Nat.div_le_div_right ?_
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ below
    _ = preset.BASE_REWARD_FACTOR.toNat * (Nat.sqrt total + 2) := by
        rw [Nat.mul_div_cancel_left _ rootPositive, Nat.mul_comm]

/-- The base reward per increment is the increment times the factor over the root of the total.

It succeeds when the total is at least one positive increment and the product fits. -/
private theorem getBaseRewardPerIncrement_eq
    (positive : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (fits : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    {total : Gwei} (low : preset.EFFECTIVE_BALANCE_INCREMENT ≤ total) :
    ∃ per, getBaseRewardPerIncrement preset total = .ok per ∧
      per.toNat = preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat /
        Nat.sqrt total.toNat := by
  have root := toNat_integerSquareroot total
  have rootPositive : 0 < Nat.sqrt total.toNat :=
    Nat.sqrt_pos.mpr (Nat.lt_of_lt_of_le positive (UInt64.le_iff_toNat_le.mp low))
  have nonzero : integerSquareroot total ≠ 0 := fun zero => by
    rw [zero, UInt64.toNat_zero] at root
    omega
  refine ⟨preset.EFFECTIVE_BALANCE_INCREMENT * preset.BASE_REWARD_FACTOR /
    integerSquareroot total, ?_, ?_⟩
  · simp only [getBaseRewardPerIncrement, liftArith, mulChecked_of_lt fits, bind, Except.bind,
      divChecked, nonzero, ite_false, Except.mapError]
  · rw [UInt64.toNat_div, UInt64.toNat_mul, Nat.mod_eq_of_lt fits, root]

/-- Two states with the same registry, slot and flags have the same reads of the rewards.

These are the total active balance, the total balance of indices and the participating indices.

The previous epoch is the same too.

From Altair, they read the flags of both recent epochs. -/
private theorem rewardReads_congr {other : BeaconState preset fork}
    (validators : other.validators = state.validators) (slot : other.slot = state.slot)
    (previous : other.previousEpochParticipation = state.previousEpochParticipation)
    (current : other.currentEpochParticipation = state.currentEpochParticipation) :
    getTotalActiveBalance other = getTotalActiveBalance state ∧
      (∀ indices, getTotalBalance other indices = getTotalBalance state indices) ∧
      (∀ altair flagIndex epoch, getUnslashedParticipatingIndices other altair flagIndex epoch =
        getUnslashedParticipatingIndices state altair flagIndex epoch) ∧
      getPreviousEpoch other = getPreviousEpoch state := by
  refine ⟨?_, fun indices => ?_, fun altair flagIndex epoch => ?_, ?_⟩
  · simp only [getTotalActiveBalance, getActiveValidatorIndicesChecked, getTotalBalance,
      getCurrentEpoch, validators, slot]
    rfl
  · simp only [getTotalBalance, validators]
  · simp only [getUnslashedParticipatingIndices, getActiveValidatorIndicesChecked, getValidator,
      getPreviousEpoch, getCurrentEpoch, validators, slot, previous, current]
    rfl
  · simp only [getPreviousEpoch, getCurrentEpoch, slot]

/-- A step that keeps the queue of pending deposits keeps their sum. -/
private theorem pendingDepositSum_eq_of_pendingDeposits
    (same : after.pendingDeposits = state.pendingDeposits) :
    pendingDepositSum after = pendingDepositSum state := by
  unfold pendingDepositSum
  rw [same]

/-- A step that keeps the balances keeps their sum. -/
private theorem balanceSum_eq_of_balances (same : after.balances = state.balances) :
    balanceSum after = balanceSum state := by
  unfold balanceSum
  rw [same]

/-- The slashings never raise the sum of the balances. -/
private theorem balanceSum_processSlashings_le (computed : processSlashings state = .ok after) :
    balanceSum after ≤ balanceSum state := by
  rw [balanceSum_eq_sum_range, balanceSum_eq_sum_range, (sameSizes_processSlashings computed).2]
  refine sum_map_le_sum_map fun index _ => ?_
  cases found : after.balances.data[index]? with
  | none => exact Nat.zero_le _
  | some later =>
    obtain ⟨earlier, atState, low⟩ := balanceNotRaised_processSlashings computed index later found
    rw [atState]
    exact low

/-- A step from the registry updates to the effective balances raises no supply.

The supply is the sum of the balances and of the amounts of the pending deposits. -/
theorem supply_le_of_action {config : Config} {checks : SignatureChecks}
    {stage : EpochStage}
    (member : stage ∈ [.registry, .slashings, .eth1Reset, .pendingDeposits,
      .pendingConsolidations, .payments, .effectiveBalances])
    (computed : action config checks stage state = .ok after) :
    balanceSum after + pendingDepositSum after ≤ balanceSum state + pendingDepositSum state := by
  have edge := action_cases.mp computed
  cases stage <;> simp only [Edge] at edge <;> try (simp at member; done)
  case pendingDeposits =>
    split at edge
    · rename_i electra
      unfold pendingDepositSum
      simp only [electra, ↓reduceDIte]
      exact processPendingDeposits_total_le edge
    · subst edge
      exact Nat.le_refl _
  case payments =>
    split at edge
    · rw [processBuilderPendingPayments_eq edge]
      exact Nat.le_refl _
    · subst edge
      exact Nat.le_refl _
  all_goals
    have pending := pendingDepositSum_eq_of_pendingDeposits
      (loadKeptLaws.epochEdge (by simp) computed).2
    refine Nat.add_le_add ?_ (Nat.le_of_eq pending)
  case registry => exact Nat.le_of_eq (balanceSum_eq_of_balances
    (processRegistryUpdates_balances edge))
  case slashings => exact balanceSum_processSlashings_le edge
  case eth1Reset =>
    split at edge
    · rw [processEth1DataReset_frame edge]
      exact Nat.le_refl _
    · subst edge
      exact Nat.le_refl _
  case pendingConsolidations =>
    split at edge
    · exact Nat.le_of_eq (processPendingConsolidations_kept edge).2
    · subst edge
      exact Nat.le_refl _
  case effectiveBalances => exact Nat.le_of_eq (balanceSum_eq_of_balances
    (processEffectiveBalanceUpdates_balances edge))

/-- From Altair, the steps after the rewards raise no supply. -/
private theorem supply_le_of_tail {config : Config} {checks : SignatureChecks}
    (altair : .altair ≤ fork)
    (trace : EpochTrace (action config checks) [.registry, .slashings, .eth1Reset,
      .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances, .slashingsReset,
      .randaoReset, .history, .participation, .syncCommittees, .proposerLookahead,
      .ptcWindow] state after) :
    balanceSum after + pendingDepositSum after ≤ balanceSum state + pendingDepositSum state := by
  change EpochTrace _ ([.registry, .slashings, .eth1Reset, .pendingDeposits,
    .pendingConsolidations, .payments, .effectiveBalances] ++ [.slashingsReset, .randaoReset,
    .history, .participation, .syncCommittees, .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨middle, head, last⟩ := append_iff.mp trace
  have raised := head.transport
    (fun first second =>
      balanceSum second + pendingDepositSum second ≤ balanceSum first + pendingDepositSum first)
    (fun _ => Nat.le_refl _) (fun one two => Nat.le_trans two one)
    (fun _ member _ _ ok => supply_le_of_action member ok)
  -- The last steps keep the balances and the queue of pending deposits.
  have balances := balanceSum_eq_of_balances (sameBalancesRegistryScores_tail altair last).1
  have queue := last.transport LoadKept LoadKept.refl LoadKept.trans fun stage member _ _ ok => by
    by_cases rotation : stage = .participation
    · subst rotation
      have edge := action_cases.mp ok
      simp only [Edge, altair, ↓reduceDIte] at edge
      subst edge
      exact ⟨rfl, rfl⟩
    · refine loadKeptLaws.epochEdge ⟨?_, ?_, rotation, ?_⟩ ok <;> rintro rfl <;> simp at member
  rw [balances, pendingDepositSum_eq_of_pendingDeposits queue.2]
  exact raised

/-- From Altair, the first three steps of the epoch raise the supply by at most the issuance bound.

They are justification and finalization, the update of the inactivity scores, and the rewards.

The bound reads the active balance of the state before the epoch.

No flag of the previous epoch may have been set by more balance than is active.

The registry must be within its limit, the increment positive, and the base reward fit. -/
theorem supply_le_of_head {config : Config} {checks : SignatureChecks}
    (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (perIncrement :
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {participatingBalance : Fin PARTICIPATION_FLAG_WEIGHTS.length → Gwei}
    (weighed : ∀ flagIndex, ∃ indices,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
          (getPreviousEpoch state) = .ok indices ∧
        getTotalBalance state indices = .ok (participatingBalance flagIndex))
    (kept : ∀ flagIndex, participatingBalance flagIndex ≤ total)
    (trace : EpochTrace (action config checks) [.justification, .inactivity, .rewards]
      state after) :
    balanceSum after + pendingDepositSum after ≤
      balanceSum state + pendingDepositSum state + preset.epochIssuance total.toNat := by
  obtain _ | ⟨justifiedOk, trace⟩ := trace
  obtain _ | ⟨scoredOk, trace⟩ := trace
  obtain _ | ⟨rewardedOk, trace⟩ := trace
  cases trace
  rename_i justified scored
  have justifiedEq : processJustificationAndFinalization state = .ok justified :=
    action_cases.mp justifiedOk
  have scoredEq := action_cases.mp scoredOk
  simp only [Edge, altair, ↓reduceDIte] at scoredEq
  have rewardedEq : processRewardsAndPenalties config scored = .ok after :=
    action_cases.mp rewardedOk
  have pendingRewarded := (loadKeptLaws.processRewardsAndPenalties rewardedEq).2
  -- Justification changes only the checkpoints and their bits, and the scores only the scores.
  obtain ⟨-, -, -, -, -, validators1, -, -, previous1, current1⟩ :=
    processJustificationAndFinalization_keeps justifiedEq
  have slot1 := processJustificationAndFinalization_slot justifiedEq
  have kept1 : justified.balances = state.balances ∧
      justified.pendingDeposits = state.pendingDeposits := by
    obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedEq
    · exact ⟨rfl, rfl⟩
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      exact ⟨by rw [← rest], by rw [← rest]⟩
  have scoredFrame := processInactivityUpdates_frame scoredEq
  have field {α : Type} (read : BeaconState preset fork → α)
      (same : ∀ scores, read { justified with inactivityScores := scores } = read justified) :
      read scored = read justified := by
    rw [scoredFrame]
    exact same _
  -- So the rewards read the registry, the slot and the flags of the state before the epoch.
  obtain ⟨activeSame, totalSame, indicesSame, previousSame⟩ := rewardReads_congr
    ((field _ fun _ => rfl).trans validators1) ((field _ fun _ => rfl).trans slot1)
    ((field _ fun _ => rfl).trans previous1) ((field _ fun _ => rfl).trans current1)
  obtain ⟨perIncrement, per, perValue⟩ := getBaseRewardPerIncrement_eq increment perIncrement
    (le_getTotalBalance (getTotalActiveBalance_ok active))
  have rise := processRewardsAndPenalties_balanceSum_le_of_participating_le altair
    (by
      unfold BeaconState.RegistryWithinLimit
      rw [(field _ fun _ => rfl).trans validators1]
      exact within)
    rewardedEq (activeSame.trans active) per
    (fun flagIndex => by
      obtain ⟨indices, listed, weighs⟩ := weighed flagIndex
      exact ⟨indices, by rw [indicesSame, previousSame]; exact listed,
        by rw [totalSame]; exact weighs⟩)
    kept increment
  have bounded := rise_le_epochIssuance (preset := preset)
    (increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (Nat.lt_of_lt_of_le increment (UInt64.le_iff_toNat_le.mp
      (le_getTotalBalance (getTotalActiveBalance_ok active))))
  rw [← perValue] at bounded
  -- The scores and justification keep the balances and the queue of pending deposits.
  have balances : balanceSum scored = balanceSum state :=
    balanceSum_eq_of_balances ((field _ fun _ => rfl).trans kept1.1)
  have pending : pendingDepositSum after = pendingDepositSum state :=
    pendingDepositSum_eq_of_pendingDeposits
      (pendingRewarded.trans ((field _ fun _ => rfl).trans kept1.2))
  omega

/-- A deposit raises the sum of the effective balances by at most its amount.

A new validator takes the amount rounded down to an increment, capped by its largest one. -/
private theorem effectiveBalanceSum_applyPendingDeposit_le {config : Config}
    {checks : SignatureChecks} {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    effectiveBalanceSum after ≤ effectiveBalanceSum state + deposit.amount.toNat := by
  rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact Nat.le_add_right _ _
  · unfold effectiveBalanceSum
    rw [increaseBalance_validators raised]
    exact Nat.le_add_right _ _
  · unfold effectiveBalanceSum
    rw [addValidatorToRegistry_validators_eq_push added, Array.toList_push, List.map_append,
      List.sum_append_nat]
    refine Nat.add_le_add_left ?_ _
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      getValidatorFromDeposit]
    rw [← UInt64.le_iff_toNat_le]
    have mod : deposit.amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ deposit.amount := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    exact UInt64.le_trans Std.min_le_left (UInt64.sub_le mod)

/-- Deposits applied in order raise the sum of the effective balances by at most their amounts. -/
private theorem effectiveBalanceSum_foldlM_applyPendingDeposit_le {config : Config}
    {checks : SignatureChecks} :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset fork},
      deposits.foldlM (applyPendingDeposit config checks) state = .ok after →
      effectiveBalanceSum after ≤ effectiveBalanceSum state + pendingAmount deposits
  | [], _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [pendingAmount]
  | deposit :: rest, state, after, computed => by
    simp only [List.foldlM_cons, bind, Except.bind] at computed
    split at computed
    · cases computed
    rename_i next applied
    have first := effectiveBalanceSum_applyPendingDeposit_le applied
    have later := effectiveBalanceSum_foldlM_applyPendingDeposit_le computed
    simp only [pendingAmount, List.map_cons, List.sum_cons] at later ⊢
    omega

/-- From Electra, the pending deposits do not raise the effective balances plus the pending amounts.

A deposit to a known validator raises only its balance.

A new validator takes an effective balance at most the amount of its deposit.

A postponed deposit stays in the queue, and a dropped one leaves it. -/
theorem processPendingDeposits_effectiveSupply_le {config : Config} {checks : SignatureChecks}
    {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    effectiveBalanceSum after + pendingDepositSum after ≤
      effectiveBalanceSum state + pendingDepositSum state := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, _, _, _, perm,
    later, rfl⟩ := processPendingDeposits_applied computed
  have raised := effectiveBalanceSum_foldlM_applyPendingDeposit_le later
  have amounts := (perm.map (·.amount.toNat)).sum_nat
  change effectiveBalanceSum next + pendingDepositSum { next with
    pendingDeposits := fun _ => pending, depositBalanceToConsume := fun _ => carried } ≤ _
  unfold pendingDepositSum
  simp only [electra, ↓reduceDIte]
  rw [queue, kept]
  simp only [pendingAmount, List.map_append, List.sum_append_nat] at amounts raised ⊢
  omega

/-- From Electra, the pending consolidations keep the sum of the effective balances.

They also keep the sum of the pending deposits.

They move balances, and only the next update of the effective balances reads them. -/
theorem processPendingConsolidations_effectiveSupply_eq {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    effectiveBalanceSum after = effectiveBalanceSum state ∧
      pendingDepositSum after = pendingDepositSum state := by
  obtain ⟨validators, -, -, -, pending, -⟩ := processPendingConsolidations_fields computed
  exact ⟨by unfold effectiveBalanceSum; rw [validators],
    pendingDepositSum_eq_of_pendingDeposits pending⟩

/-- From Altair, the epoch transition raises the supply by at most the issuance bound.

The supply is the sum of the balances and of the amounts of the pending deposits.

The bound reads the active balance of the state before the epoch.

No flag of the previous epoch may have been set by more balance than is active.

The registry must be within its limit, the increment positive, and the base reward fit. -/
theorem processEpoch_supply_le {config : Config} {checks : SignatureChecks}
    (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (perIncrement :
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    {total : Gwei} (active : getTotalActiveBalance state = .ok total)
    {participatingBalance : Fin PARTICIPATION_FLAG_WEIGHTS.length → Gwei}
    (weighed : ∀ flagIndex, ∃ indices,
      getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
          (getPreviousEpoch state) = .ok indices ∧
        getTotalBalance state indices = .ok (participatingBalance flagIndex))
    (kept : ∀ flagIndex, participatingBalance flagIndex ≤ total)
    (computed : processEpoch config checks state = .ok after) :
    balanceSum after + pendingDepositSum after ≤
      balanceSum state + pendingDepositSum state + preset.epochIssuance total.toNat := by
  have trace := processEpoch_trace computed
  change EpochTrace _ ([.justification, .inactivity, .rewards] ++ [.registry, .slashings,
    .eth1Reset, .pendingDeposits, .pendingConsolidations, .payments, .effectiveBalances,
    .slashingsReset, .randaoReset, .history, .participation, .syncCommittees,
    .proposerLookahead, .ptcWindow]) _ _ at trace
  obtain ⟨middle, head, tail⟩ := append_iff.mp trace
  have raised := supply_le_of_head altair within increment perIncrement active weighed kept head
  have lowered := supply_le_of_tail altair tail
  omega

/-- From Altair, when no flag is set, no flag has more participating balance than is active.

Without a flag set, no validator participates, so the total is the floor of one increment.

The active balance has the same floor, so the hypothesis on the flags of the supply bound holds.

A run of slots without blocks sets no flag, so these hypotheses hold from its third epoch on.

Both lists of flags are read, since in the first epoch the previous epoch is the current one. -/
theorem participatingBalance_le_of_unset (altair : .altair ≤ fork) {flagIndex : UInt64}
    (previousUnset : ∀ flags ∈ (state.previousEpochParticipation altair).data, flags = 0)
    (currentUnset : ∀ flags ∈ (state.currentEpochParticipation altair).data, flags = 0)
    {indices : List ValidatorIndex} {participatingBalance total : Gwei}
    (listed : getUnslashedParticipatingIndices state altair flagIndex (getPreviousEpoch state) =
      .ok indices)
    (weighed : getTotalBalance state indices = .ok participatingBalance)
    (active : getTotalActiveBalance state = .ok total) :
    participatingBalance ≤ total := by
  have empty : indices = [] := by
    unfold getUnslashedParticipatingIndices at listed
    have bits : hasFlag 0 flagIndex = false := by
      have shifted : ∀ k : UInt8, (1 <<< k : UInt8) ≠ 0 := by
        intro k h
        have := congrArg UInt8.toNat h
        rw [UInt8.toNat_shiftLeft] at this
        simp at this
        have h8 : k.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
        generalize k.toNat % 8 = m at *
        rw [Nat.shiftLeft_eq, Nat.one_mul] at this
        have a := Nat.pow_lt_pow_right (by omega : 1 < 2) h8
        have b := Nat.two_pow_pos m
        omega
      have := shifted flagIndex.toUInt8
      simp only [hasFlag, flagBit]
      simp
      exact fun h => this h.symm
    have key : ∀ (participation : Array ParticipationFlags),
        (∀ flags ∈ participation, flags = 0) → ∀ (L : List ValidatorIndex)
          (r : List (ValidatorIndex × Bool)),
        (List.mapM (fun index =>
              match participation[UInt64.toNat index]? with
              | some flags => do
                let v ← getValidator state index
                pure (index, hasFlag flags flagIndex && !v.slashed)
              | x => throw (AccessorError.indexOutOfRange index)) L :
          Except AccessorError (List (ValidatorIndex × Bool))) = .ok r →
          ∀ x ∈ r, x.2 = false := by
      intro participation zero L
      induction L with
      | nil => intro r h x hx; simp [pure, Except.pure] at h; subst h; simp at hx
      | cons a t ih =>
        intro r h x hx
        simp only [List.mapM_cons] at h
        cases hp : participation[a.toNat]? with
        | none => simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        | some flags =>
          have f0 := zero flags (Array.mem_of_getElem? hp)
          simp only [hp, f0, bits] at h
          cases hv : getValidator state a with
          | error e => simp [hv, bind, Except.bind] at h
          | ok v =>
            simp only [hv, bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · rename_i rest ht
              cases h
              rcases List.mem_cons.mp hx with rfl | member
              · simp
              · exact ih rest ht x member
    have pickZero := key (if getPreviousEpoch state = getCurrentEpoch state then
        (state.currentEpochParticipation altair).data
      else (state.previousEpochParticipation altair).data) (by split <;> assumption)
    simp only [bind, Except.bind, pure, Except.pure] at pickZero
    simp only [true_or, ↓reduceIte, bind, Except.bind, pure, Except.pure] at listed
    split at listed
    · cases listed
    · split at listed
      · cases listed
      · rename_i read marked
        cases listed
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro i hi
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
        have := pickZero _ _ marked x (List.mem_of_mem_filter hx)
        have := (List.mem_filter.mp hx).2
        simp_all
  subst empty
  obtain ⟨-, -, rfl⟩ := getTotalBalance_ok_iff.mp weighed
  have zero : sumMarked state.validators.data
      (markIndices state.validators.data.size []) = 0 := by
    rw [sumMarked_eq_sum]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    simp only [getElem?_markIndices]
    split_ifs <;> simp_all
  rw [zero]
  have := le_getTotalBalance (getTotalActiveBalance_ok active)
  rw [UInt64.max_def]
  split
  · simp
  · exact this

end EthLib.Consensus

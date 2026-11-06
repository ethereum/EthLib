module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Churn

/-!
# Proofs: the balance churn

A queue never places an amount before its earliest open epoch, or before the first epoch allowed.

The queue spends exactly the amount.

The churn left plus the amount equals the churn available, plus a full churn for each added epoch.

An amount that needs later epochs takes the fewest, so less than one churn is left in the last.

An amount that fits the churn available always finds its place in the current epoch.

In Electra, the churns of consolidations and of activations and exits add up to the whole churn.

So their difference does not wrap.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- The queue places an amount no earlier than its earliest open epoch and the first epoch.

The churn left plus the amount equals the churn available at the first open epoch.

Each epoch that the queue adds contributes one more full churn to that sum.

If the queue adds epochs, less than one full churn is left in the last. -/
theorem churnQueue_spend {earliestEpoch firstEpoch perEpochChurn churnLeft amount epoch left :
    UInt64}
    (computed :
      churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount = .ok (epoch, left)) :
    max earliestEpoch firstEpoch ≤ epoch ∧
      left.toNat + amount.toNat =
        (if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft).toNat +
          (epoch.toNat - (max earliestEpoch firstEpoch).toNat) * perEpochChurn.toNat ∧
      (epoch = max earliestEpoch firstEpoch ∨ left.toNat < perEpochChurn.toNat) := by
  unfold churnQueue at computed
  dsimp only at computed
  generalize max earliestEpoch firstEpoch = first at computed ⊢
  generalize (if earliestEpoch < first then perEpochChurn else churnLeft) = available at computed ⊢
  split at computed
  · rename_i fits
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    have fits := UInt64.le_iff_toNat_le.mp fits
    refine ⟨UInt64.le_refl _, ?_, .inl rfl⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr fits)]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    omega
  · rename_i over
    have over : available.toNat < amount.toNat := by
      rw [UInt64.le_iff_toNat_le] at over
      omega
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨quotient, divided, later, added, product, multiplied, total, summed, rfl, rfl⟩ :=
      computed
    obtain ⟨nonzero, quotientValue⟩ := divChecked_ok_iff.mp divided
    have positive : 0 < perEpochChurn.toNat := by
      rcases Nat.eq_zero_or_pos perEpochChurn.toNat with zero | positive
      · exact absurd (UInt64.toNat_inj.mp (by simpa using zero)) nonzero
      · exact positive
    -- The rest of the amount, less one, on natural numbers.
    have rest : (amount - available - 1).toNat = amount.toNat - available.toNat - 1 := by
      have difference : (amount - available).toNat = amount.toNat - available.toNat :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt over))
      have one : (1 : UInt64) ≤ amount - available := by
        rw [UInt64.le_iff_toNat_le, difference]
        show 1 ≤ _
        omega
      rw [UInt64.toNat_sub_of_le _ _ one, difference]
      rfl
    rw [rest] at quotientValue
    have quotientSmall : quotient.toNat < amount.toNat := by
      rw [quotientValue]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have additional : (quotient + 1).toNat = quotient.toNat + 1 := by
      have := amount.toNat_lt
      exact toNat_add_of_lt (by simp; omega)
    obtain ⟨_, laterValue⟩ := addChecked_ok_iff.mp added
    obtain ⟨_, productValue⟩ := mulChecked_ok_iff.mp multiplied
    obtain ⟨_, totalValue⟩ := addChecked_ok_iff.mp summed
    rw [additional] at laterValue productValue
    -- The added epochs cover the rest of the amount, with less than one churn to spare.
    have cover : amount.toNat - available.toNat ≤ (quotient.toNat + 1) * perEpochChurn.toNat ∧
        (quotient.toNat + 1) * perEpochChurn.toNat <
          amount.toNat - available.toNat + perEpochChurn.toNat := by
      rw [quotientValue, Nat.add_mul, Nat.one_mul]
      have below := Nat.div_mul_le_self (amount.toNat - available.toNat - 1) perEpochChurn.toNat
      have above := Nat.lt_div_mul_add (a := amount.toNat - available.toNat - 1) positive
      omega
    have enough : amount ≤ total := by
      rw [UInt64.le_iff_toNat_le, totalValue, productValue]
      omega
    rw [UInt64.toNat_sub_of_le _ _ enough, totalValue, productValue, laterValue]
    refine ⟨UInt64.le_iff_toNat_le.mpr (by omega), ?_, .inr ?_⟩
    · rw [Nat.add_sub_cancel_left]
      omega
    · omega

/-- An amount that fits the churn available takes the first open epoch, and leaves the rest. -/
theorem churnQueue_of_le {earliestEpoch firstEpoch perEpochChurn churnLeft amount : UInt64}
    (fits :
      amount ≤ if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft) :
    churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount =
      .ok (max earliestEpoch firstEpoch,
        (if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft) -
          amount) := by
  simp only [churnQueue, fits, ↓reduceIte, pure, Except.pure]

/-- In Electra, the churns of consolidations and of activations and exits add up to the whole churn.
-/
theorem getConsolidationChurnLimit_add {config : Config} {state : BeaconState preset fork}
    {consolidation activationExit whole : Gwei} (before : fork < .glamsterdam)
    (consolidationOk : getConsolidationChurnLimit config state = .ok consolidation)
    (activationExitOk : getActivationExitChurnLimit config state = .ok activationExit)
    (wholeOk : getBalanceChurnLimit config state = .ok whole) :
    consolidation.toNat + activationExit.toNat = whole.toNat := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte, bind_ok_iff, wholeOk,
    activationExitOk, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at consolidationOk
  simp only [getActivationExitChurnLimit, bind_ok_iff, wholeOk, pure, Except.pure,
    Except.ok.injEq, exists_eq_left'] at activationExitOk
  subst consolidationOk activationExitOk
  have le : min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT whole ≤ whole := by
    rw [UInt64.min_def]
    split
    · assumption
    · exact UInt64.le_refl _
  rw [UInt64.toNat_sub_of_le _ _ le]
  have := UInt64.le_iff_toNat_le.mp le
  omega

/-- The churn update of an exit records its epoch as the earliest open one. -/
theorem computeExitEpochAndUpdateChurn_earliest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    after.earliestExitEpoch electra = epoch ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨queued, left⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨rfl, rfl, rfl⟩

/-- The churn update of a consolidation records its epoch as the earliest open one. -/
theorem computeConsolidationEpochAndUpdateChurn_earliest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    after.earliestConsolidationEpoch electra = epoch ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨queued, left⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨rfl, rfl, rfl⟩

/-- An exit from Electra leaves no earlier than the first epoch an exit may take. -/
theorem computeExitEpochAndUpdateChurn_first {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch firstEpoch : Epoch}
    (first : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok firstEpoch)
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    firstEpoch ≤ epoch ∧ state.earliestExitEpoch electra ≤ epoch := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, first,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
  obtain ⟨_, _, ⟨queued, left⟩, queue, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨_, rfl⟩ := final
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend queue).1
  rw [UInt64.max_def] at placed
  split at placed <;> rename_i order <;> simp only [UInt64.le_iff_toNat_le] at order ⊢ <;>
    omega

end EthLib.Consensus

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

Amounts queued in turn spend exactly their sum, with one full churn for each added epoch.

So the amounts placed up to an epoch take at most the churn left, then a full churn per epoch.

In Electra, the churns of consolidations and of activations and exits add up to the whole churn.

So their difference does not wrap.

From Gloas, the churn of exits is a whole number of increments.

The churn of activations is the churn of exits up to a maximum, and pending deposits take it.
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

/-- The queue reads its state only through the first open epoch and the churn available there.

So it places an amount as it would from that epoch, with that churn left. -/
theorem churnQueue_normalize {earliestEpoch firstEpoch perEpochChurn churnLeft amount : UInt64} :
    churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount =
      churnQueue (max earliestEpoch firstEpoch) firstEpoch perEpochChurn
        (if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft)
        amount := by
  have same : max (max earliestEpoch firstEpoch) firstEpoch = max earliestEpoch firstEpoch := by
    by_cases order : earliestEpoch ≤ firstEpoch
    · simp only [UInt64.max_def, order, ↓reduceIte, UInt64.le_refl]
    · simp only [UInt64.max_def, order, ↓reduceIte]
  simp only [churnQueue, same, UInt64.lt_irrefl, ↓reduceIte]

/-- Amounts queued in turn, from an open epoch no earlier than the first epoch allowed.

The queue never moves back, and it spends exactly the amounts, one full churn per added epoch. -/
private theorem churnQueue_foldlM {firstEpoch perEpochChurn : UInt64} :
    ∀ {amounts : List UInt64} {earliestEpoch churnLeft epoch left : UInt64},
      firstEpoch ≤ earliestEpoch →
      amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
          churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
        (earliestEpoch, churnLeft) = .ok (epoch, left) →
      earliestEpoch ≤ epoch ∧
        left.toNat + (amounts.map UInt64.toNat).sum =
          churnLeft.toNat + (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat
  | [], earliestEpoch, churnLeft, epoch, left, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    simp
  | amount :: rest, earliestEpoch, churnLeft, epoch, left, first, computed => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleLeft⟩, step, folded⟩ := computed
    have open_ : max earliestEpoch firstEpoch = earliestEpoch := by
      rw [UInt64.max_def]
      split
      · exact UInt64.le_antisymm first ‹_›
      · rfl
    obtain ⟨placed, spent, -⟩ := churnQueue_spend step
    rw [open_] at placed spent
    simp only [UInt64.lt_irrefl, ↓reduceIte] at spent
    obtain ⟨later, total⟩ := churnQueue_foldlM (UInt64.le_trans first placed) folded
    refine ⟨UInt64.le_trans placed later, ?_⟩
    have placed := UInt64.le_iff_toNat_le.mp placed
    have later := UInt64.le_iff_toNat_le.mp later
    have epochs : (middle.toNat - earliestEpoch.toNat) * perEpochChurn.toNat +
        (epoch.toNat - middle.toNat) * perEpochChurn.toNat =
          (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat := by
      rw [← Nat.add_mul]
      congr 1
      omega
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Amounts queued in turn, from an open epoch no earlier than the first epoch allowed.

The last amount takes an epoch no earlier than the open epoch at the start. -/
theorem churnQueue_foldlM_epoch {firstEpoch perEpochChurn earliestEpoch churnLeft epoch left :
    UInt64} {amounts : List UInt64} (first : firstEpoch ≤ earliestEpoch)
    (computed : amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
      (earliestEpoch, churnLeft) = .ok (epoch, left)) :
    earliestEpoch ≤ epoch :=
  (churnQueue_foldlM first computed).1

/-- Amounts queued in turn, from an open epoch no earlier than the first epoch allowed.

The churn left at the end plus the amounts equals the churn left at the start.

Each epoch that the queue moves past adds one full churn to that sum. -/
theorem churnQueue_foldlM_spend {firstEpoch perEpochChurn earliestEpoch churnLeft epoch left :
    UInt64} {amounts : List UInt64} (first : firstEpoch ≤ earliestEpoch)
    (computed : amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
      (earliestEpoch, churnLeft) = .ok (epoch, left)) :
    left.toNat + (amounts.map UInt64.toNat).sum =
      churnLeft.toNat + (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat :=
  (churnQueue_foldlM first computed).2

/-- Amounts queued in turn take at most the churn left at the start of the queue.

Each epoch that the queue moves past allows one more full churn.

The epochs never move back, so the amounts placed up to an epoch are the first ones queued.

So the balance placed up to an epoch is at most the churn left, plus a full churn per later epoch.
-/
theorem churnQueue_foldlM_le {firstEpoch perEpochChurn earliestEpoch churnLeft epoch left :
    UInt64} {amounts : List UInt64}
    (computed : amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
      (earliestEpoch, churnLeft) = .ok (epoch, left)) :
    (amounts.map UInt64.toNat).sum ≤
      churnLeft.toNat + (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat := by
  by_cases first : firstEpoch ≤ earliestEpoch
  · have := churnQueue_foldlM_spend first computed
    omega
  cases amounts with
  | nil => simp
  | cons amount rest =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleLeft⟩, step, folded⟩ := computed
    have idle : earliestEpoch < firstEpoch := UInt64.not_le.mp first
    have open_ : max earliestEpoch firstEpoch = firstEpoch := by
      simp only [UInt64.max_def, UInt64.le_of_lt idle, ↓reduceIte]
    -- An idle queue starts with a full churn at the first permitted epoch.
    rw [churnQueue_normalize] at step
    simp only [open_, idle, ↓reduceIte] at step
    have normalized : (amount :: rest).foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
        (firstEpoch, perEpochChurn) = .ok (epoch, left) := by
      rw [List.foldlM_cons, step]
      exact folded
    have total := churnQueue_foldlM_spend (UInt64.le_refl _) normalized
    have later := churnQueue_foldlM_epoch (UInt64.le_refl _) normalized
    simp only [List.map_cons, List.sum_cons] at total
    -- The epochs skipped while idle pay for that full churn in the original budget.
    have gap : epoch.toNat - firstEpoch.toNat + 1 ≤ epoch.toNat - earliestEpoch.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp idle
      have := UInt64.le_iff_toNat_le.mp later
      omega
    have allowance := Nat.mul_le_mul_right perEpochChurn.toNat gap
    simp only [Nat.add_mul, Nat.one_mul] at allowance
    simp only [List.map_cons, List.sum_cons]
    omega

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

/-- A balance rounded down to an increment is a whole number of increments. -/
theorem sub_mod_mod_self (balance increment : Gwei) :
    (balance - balance % increment) % increment = 0 := by
  have le : balance % increment ≤ balance := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_mod]
  simpa using Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

/-- A balance rounded down to an increment and capped is whole, when the cap is whole. -/
theorem min_sub_mod_mod_self {cap increment : Gwei} (balance : Gwei)
    (capAligned : cap % increment = 0) :
    min (balance - balance % increment) cap % increment = 0 := by
  rw [UInt64.min_def]
  split
  · exact sub_mod_mod_self _ _
  · exact capAligned

/-- From Gloas, the churn of exits is a whole number of effective balance increments. -/
theorem getExitChurnLimit_mod {config : Config} {state : BeaconState preset fork} {exit : Gwei}
    (computed : getExitChurnLimit config state = .ok exit) :
    exit % preset.EFFECTIVE_BALANCE_INCREMENT = 0 := by
  simp only [getExitChurnLimit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact sub_mod_mod_self _ _

/-- From Gloas, the churn of activations is the churn of exits up to its maximum. -/
theorem getActivationChurnLimit_of_exit {config : Config} {state : BeaconState preset fork}
    {exit : Gwei} (exitOk : getExitChurnLimit config state = .ok exit) :
    getActivationChurnLimit config state =
      .ok (min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS exit) := by
  simp only [getActivationChurnLimit, exitOk, bind, Except.bind, pure, Except.pure]

/-- From Gloas, the pending deposits take the churn of activations. -/
theorem depositChurnLimit_of_gloas {config : Config} {state : BeaconState preset fork}
    (gloas : .glamsterdam ≤ fork) :
    depositChurnLimit config state = getActivationChurnLimit config state := by
  simp only [depositChurnLimit, gloas, ↓reduceIte]

/-- Before Gloas, the pending deposits take the churn that activations and exits share. -/
theorem depositChurnLimit_of_lt {config : Config} {state : BeaconState preset fork}
    (before : fork < .glamsterdam) :
    depositChurnLimit config state = getActivationExitChurnLimit config state := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [depositChurnLimit, notGloas, ↓reduceIte]

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

/-- A consolidation from Electra lands no earlier than the first epoch an exit may take.

It also lands no earlier than the earliest consolidation epoch of the state. -/
theorem computeConsolidationEpochAndUpdateChurn_first {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch firstEpoch : Epoch}
    (first : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok firstEpoch)
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    firstEpoch ≤ epoch ∧ state.earliestConsolidationEpoch electra ≤ epoch := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    first, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
  obtain ⟨_, _, ⟨queued, left⟩, queue, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨_, rfl⟩ := final
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend queue).1
  rw [UInt64.max_def] at placed
  split at placed <;> rename_i order <;> simp only [UInt64.le_iff_toNat_le] at order ⊢ <;>
    omega

end EthLib.Consensus

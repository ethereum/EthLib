module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.FundingEpoch

/-!
# Funding across a slot

From Electra, one slot conserves the funded stake and the deposit carry.

The exceptions are the credits recorded by its replay and, at an epoch boundary, one epoch of churn.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem funding_slot_increment {fork : Fork} (s : BeaconState preset fork)
    (electra : .pectra ≤ fork) (next : Slot) (later : s.slot.toNat ≤ next.toNat) :
    fundedStake ⟨fork, { s with slot := next }⟩ ≤ fundedStake ⟨fork, s⟩ := by
  rw [← funding_potential_eq _ electra, ← funding_potential_eq _ electra]
  -- Advancing the epoch can remove support, but cannot create support for an unchanged validator.
  have bound := funding_potential_change
    (s.pendingConsolidations electra).data.toList
    (s.pendingConsolidations electra).data.toList (fun _ => 0)
    (s := s) (t := { s with slot := next }) rfl
    (.of_data rfl) (by
      simp only [getCurrentEpoch_toNat]
      exact Nat.div_le_div_right later)
    (fun _ h => Or.inl h) (by intro i; simp [effectiveAt, actualBalanceAt])
  simpa using bound

private theorem funding_slot_upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (electra : .pectra ≤ s.fork)
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) :
    fundedStake t.val = fundedStake s := by
  obtain ⟨fork, state⟩ := s
  cases fork <;> try (exact False.elim (of_decide_eq_false rfl electra))
  all_goals
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  -- Fulu changes the proposer lookahead, not the funding fields.
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    rfl
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

private theorem funding_slot_upgrades {s t : ForkedBeaconState preset}
    (electra : .pectra ≤ s.fork) (ok : processUpgrades config checks s = .ok t)
    (early : t.fork < .glamsterdam) : fundedStake t = fundedStake s := by
  fun_induction processUpgrades config checks s generalizing t with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    exact (ih next (Nat.le_trans electra (Nat.le_of_lt next.property)) rest early).trans
      (funding_slot_upgrade electra nextOk
        (Nat.lt_of_le_of_lt (processUpgrades_fork_le rest) early))
  | case2 s notDue => cases ok; rfl

/-- Slot conservation follows from epoch conservation, without an epoch-step placeholder. -/
private theorem funding_slot_of_epoch_bound
    (epochBound : ∀ {fork : Fork} {s t middle : BeaconState preset fork},
      .pectra ≤ fork → fork < .glamsterdam →
      2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat →
      BalancesMatch s → ExitsOrdered s → ActivationExitOrder s →
      PendingConsolidationInvariant config s → processEpoch config checks s = .ok t →
      ∀ events : List (BalanceEvent preset),
      epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events) →
      fundedStake ⟨fork, t⟩ + funding_carry ⟨fork, t⟩ ≤
        fundedStake ⟨fork, s⟩ + funding_carry ⟨fork, s⟩ +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
          (events.map fundingCredit).sum)
    {x y : ForkedBeaconState preset}
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch x.state) (ordered : ExitsOrdered x.state)
    (activation : ActivationExitOrder x.state)
    (pending : PendingConsolidationInvariant config x.state)
    (ok : advanceSlotAcross config checks x = .ok y)
    (events : List (BalanceEvent preset))
    (replayed : (Step.slot ok).balanceEvents = .ok events) :
    fundedStake y + funding_carry y ≤ fundedStake x + funding_carry x +
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      (events.map fundingCredit).sum := by
  have before : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
  have fundedUpgrade := funding_slot_upgrades (s := ⟨x.fork, advanced⟩) electra upgrades early
  have carryUpgrade := depositCarry_processUpgrades upgrades early
  change funding_carry y = funding_carry ⟨x.fork, advanced⟩ at carryUpgrade
  rw [fundedUpgrade, carryUpgrade]
  have slotUpgrade := processUpgrades_slot upgrades
  have advanceCopy := advanceOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, advancedEq⟩ := advanceCopy
  have sum := (Uint64.addChecked_ok_iff.mp
    (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  simp only [UInt64.toNat_one] at sum
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedFund : fundedStake ⟨x.fork, cached⟩ = fundedStake x := by
    rw [cachedEq]; rfl
  have cachedCarry : funding_carry ⟨x.fork, cached⟩ = funding_carry x := by
    rw [cachedEq]; rfl
  have cachedSlot : cached.slot = x.state.slot := by rw [cachedEq]
  have epochedSlot : epoched.slot = cached.slot := by
    by_cases last : next % preset.SLOTS_PER_EPOCH = 0
    · simp only [epochIfLast, last, ↓reduceIte] at epochOk
      obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochOk
      apply frame.slot.trans
      obtain rfl | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
      · rfl
      · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
        rw [← rest]
    · simp only [epochIfLast, last, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at epochOk
      rw [← epochOk]
  have increment := funding_slot_increment epoched electra next (by
    rw [epochedSlot, cachedSlot]; omega)
  have finalBound : fundedStake ⟨x.fork, advanced⟩ + funding_carry ⟨x.fork, advanced⟩ ≤
      fundedStake ⟨x.fork, epoched⟩ + funding_carry ⟨x.fork, epoched⟩ := by
    subst advanced
    exact Nat.add_le_add_right increment _
  apply finalBound.trans
  -- Only a boundary slot spends one epoch's churn allowance.
  by_cases last : next % preset.SLOTS_PER_EPOCH = 0
  · simp only [epochIfLast, last, ↓reduceIte] at epochOk
    obtain ⟨middle, updated, added, replay, _⟩ :=
      epochBalanceReplay_result cached epoched before epochOk
    have bound := epochBound electra before delay
      ((frame_processSlot cachedOk).balancesMatch matched)
      ((frame_processSlot cachedOk).exitsOrdered ordered)
      (by rw [cachedEq]; exact activation) (by rw [cachedEq]; exact pending)
      epochOk added replay
    simp only [Step.balanceEvents, cachedOk, nextOk, last, ↓reduceIte,
      replay, advanceOk, crossingOk, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at replayed
    subst events
    have epochDiff : (getCurrentEpoch y.state).toNat -
        (getCurrentEpoch x.state).toNat = 1 := by
      have epochs := nextSlot_epoch_of_boundary sum last
      rw [getCurrentEpoch_toNat, slotUpgrade]
      dsimp only
      rw [← advancedEq]
      dsimp only
      rw [getCurrentEpoch_toNat]
      omega
    rw [epochDiff, one_mul, List.map_append, List.sum_append]
    rw [cachedFund, cachedCarry] at bound
    -- Crossing credits are nonnegative, so the exact replay can retain them.
    omega
  · simp only [epochIfLast, last, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epoched
    rw [cachedFund, cachedCarry]
    omega

/-- One post-Electra slot conserves funding up to epoch churn and recorded source credits. -/
theorem funding_slot {x y : ForkedBeaconState preset}
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch x.state) (ordered : ExitsOrdered x.state)
    (activation : ActivationExitOrder x.state)
    (pending : PendingConsolidationInvariant config x.state)
    (ok : advanceSlotAcross config checks x = .ok y)
    (events : List (BalanceEvent preset))
    (replayed : (Step.slot ok).balanceEvents = .ok events) :
    fundedStake y + funding_carry y ≤ fundedStake x + funding_carry x +
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      (events.map fundingCredit).sum :=
  funding_slot_of_epoch_bound funding_epoch electra early delay matched ordered
    activation pending ok events replayed

end EthLib.Consensus.DirectSafety

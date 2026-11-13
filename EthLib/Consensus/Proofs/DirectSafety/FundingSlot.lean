module

public import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
public import EthLib.Consensus.Proofs.DirectSafety.FundingEpoch

/-!
# Funding across a slot

Before Gloas, one slot conserves the funded stake and the deposit carry.

An upgrade can only lower the funded stake.

The exceptions are the credits recorded by its replay and, at an epoch boundary, one epoch of churn.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

private theorem funding_slot_increment {fork : Fork} (s : BeaconState preset fork)
    (next : Slot) (later : s.slot.toNat ≤ next.toNat) :
    fundedStake ⟨fork, { s with slot := next }⟩ ≤ fundedStake ⟨fork, s⟩ := by
  rw [← funding_potential_eq, ← funding_potential_eq]
  -- Advancing the epoch can remove support, but cannot create support for an unchanged validator.
  have bound := funding_potential_change (fundingSources s) (fundingSources s) (fun _ => 0)
    (s := s) (t := { s with slot := next }) rfl
    (.of_data rfl) (by
      simp only [getCurrentEpoch_toNat]
      exact Nat.div_le_div_right later)
    (fun _ h => Or.inl h) (by intro i; simp [effectiveAt, actualBalanceAt])
  simpa [fundingSources] using bound

/-- A step that lowers the funding at each position does not raise the funded stake.

It must keep the lifecycles, the slot and the pending consolidations. -/
private theorem funding_lowered {fork : Fork} {s t : BeaconState preset fork}
    (size : t.validators.data.size = s.validators.data.size) (life : RegistryLifecycle s t)
    (slot : t.slot = s.slot) (queue : t.pendingConsolidations = s.pendingConsolidations)
    (lowered : ∀ i, max (effectiveAt ⟨fork, t⟩ i) (actualBalanceAt ⟨fork, t⟩ i) ≤
      max (effectiveAt ⟨fork, s⟩ i) (actualBalanceAt ⟨fork, s⟩ i)) :
    fundedStake ⟨fork, t⟩ ≤ fundedStake ⟨fork, s⟩ := by
  have sources : fundingSources t = fundingSources s := by
    unfold fundingSources
    rw [queue]
  rw [← funding_potential_eq, ← funding_potential_eq]
  simpa using funding_potential_change (fundingSources t) (fundingSources s) (fun _ => 0) size
    life (by simp [getCurrentEpoch, slot]) (fun _ h => Or.inl (sources ▸ h))
    (fun i => by simpa using lowered i)

/-- Queueing a validator that is not yet active empties its balance and its effective balance. -/
private theorem funding_queuePreActivation {s t : BeaconState preset .pectra}
    {index : ValidatorIndex} (ok : queuePreActivation s (by decide) index = .ok t) :
    fundedStake ⟨.pectra, t⟩ ≤ fundedStake ⟨.pectra, s⟩ := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨v, found, _, _, _, _, _, setBalance, _, setValidator, rfl⟩ := ok
  obtain ⟨_, rfl⟩ := setBalance_ok setBalance
  have life := RegistryLifecycle.setValidator (state := s.putBalance _ _ 0) found setValidator
    ⟨fun _ => rfl, fun _ => rfl⟩
  obtain ⟨inside, rfl⟩ := setValidator_ok setValidator
  refine funding_lowered (by simp [BeaconState.putValidator, BeaconState.putBalance])
    ⟨life.size_le, life.validators⟩ rfl rfl ?_
  intro i
  by_cases same : i = index.toNat
  · subst i
    simp [effectiveAt, actualBalanceAt, BeaconState.putValidator, BeaconState.putBalance,
      Serialization.Ssz.RootedForkList.data_set]
  · simp [effectiveAt, actualBalanceAt, BeaconState.putValidator, BeaconState.putBalance,
      Serialization.Ssz.RootedForkList.data_set, Ne.symm same]

/-- Queueing the excess of a compounding validator lowers only its balance. -/
private theorem funding_queueCompoundingExcess {s t : BeaconState preset .pectra} {index : Nat}
    (ok : queueCompoundingExcess s (by decide) index = .ok t) :
    fundedStake ⟨.pectra, t⟩ ≤ fundedStake ⟨.pectra, s⟩ := by
  unfold queueCompoundingExcess at ok
  split at ok
  · split at ok
    · have queued := liftAccessor_ok.mp ok
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨balance, read, queued⟩ := queued
      split at queued
      · rename_i excess
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        have old := getBalance_eq_ok_iff.mp read
        refine funding_lowered (by simp [BeaconState.putBalance]) (.of_data rfl) rfl rfl ?_
        intro i
        by_cases same : i = index.toUInt64.toNat
        · rw [same]
          simp only [effectiveAt, actualBalanceAt, BeaconState.putBalance,
            Array.getElem?_set_self, old, Option.map_some, Option.getD_some]
          exact max_le_max_left _ (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt excess))
        · simp only [effectiveAt, actualBalanceAt, BeaconState.putBalance, Array.getElem?_set,
            Ne.symm same, ↓reduceIte, Nat.le_refl]
      · cases queued
        exact Nat.le_refl _
    · cases ok
      exact Nat.le_refl _
  · cases ok
    exact Nat.le_refl _

/-- The upgrade to Electra does not raise the funded stake.

It empties the balance of each validator that is not yet active, and lowers compounding balances.

It queues both amounts as pending deposits, which the Electra deposit churn later spends. -/
private theorem funding_upgradeToElectra {s : BeaconState preset .dencun}
    {t : BeaconState preset .pectra} (ok : upgradeToElectra config s = .ok t) :
    fundedStake ⟨.pectra, t⟩ ≤ fundedStake ⟨.dencun, s⟩ := by
  have fold {α : Type} {f : BeaconState preset .pectra → α →
      Except TransitionError (BeaconState preset .pectra)}
      (step : ∀ a x b, f a x = .ok b → fundedStake ⟨.pectra, b⟩ ≤ fundedStake ⟨.pectra, a⟩)
      {xs : List α} {a b : BeaconState preset .pectra} (ok : xs.foldlM f a = .ok b) :
      fundedStake ⟨.pectra, b⟩ ≤ fundedStake ⟨.pectra, a⟩ :=
    foldlM_ok_invariant (fun c => fundedStake ⟨.pectra, c⟩ ≤ fundedStake ⟨.pectra, a⟩)
      (fun _ _ _ prior ok => (step _ _ _ ok).trans prior) (Nat.le_refl _) ok
  simp only [upgradeToElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, first, last⟩ := ok
  refine (fold (fun _ _ _ => funding_queueCompoundingExcess) last).trans
    ((fold (fun _ _ _ => funding_queuePreActivation) first).trans (Nat.le_of_eq ?_))
  -- The carried state has the same registry, balances and slot, and no pending consolidation.
  simp [fundedStake, effectiveAt, actualBalanceAt, getCurrentEpoch, carryFields, carryRooted,
    carryList, (by decide : ¬ Fork.pectra ≤ Fork.dencun)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro _ _
  congr 1
  exact propext (or_congr_right decide_eq_true_iff.symm)

/-- An upgrade before Gloas does not raise the funded stake.

The other upgrades keep the registry, the balances and the slot. -/
private theorem funding_slot_upgrade {s : ForkedBeaconState preset}
    {t : {t : ForkedBeaconState preset // s.fork < t.fork}}
    (ok : upgradeNext config checks s = .ok t) (early : t.val.fork < .glamsterdam) :
    fundedStake t.val ≤ fundedStake s := by
  have slot := (upgradeFrame_upgradeNext ok).slot
  obtain ⟨fork, state⟩ := s
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at ok
  · obtain ⟨_, upgraded, rfl⟩ := ok
    obtain ⟨validators, balances, -⟩ := upgradeToAltair_spec upgraded
    apply Nat.le_of_eq
    simp only at slot
    simp [fundedStake, effectiveAt, actualBalanceAt, getCurrentEpoch, validators, balances, slot,
      (by decide : ¬ Fork.pectra ≤ Fork.altair), (by decide : ¬ Fork.pectra ≤ Fork.phase0)]
    apply congrArg List.sum
    apply List.map_congr_left
    intro _ _
    congr 1
    exact propext (or_congr_right decide_eq_true_iff.symm)
  · subst ok
    exact Nat.le_refl _
  · subst ok
    exact Nat.le_refl _
  · subst ok
    exact Nat.le_refl _
  · obtain ⟨_, upgraded, rfl⟩ := ok
    exact funding_upgradeToElectra upgraded
  -- Fulu changes the proposer lookahead, not the funding fields.
  · obtain ⟨_, upgraded, rfl⟩ := ok
    simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    exact Nat.le_refl _
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim (Nat.lt_irrefl _ early)
  · obtain ⟨_, _, rfl⟩ := ok
    exact False.elim ((by decide : ¬Fork.hegota < Fork.glamsterdam) early)

private theorem funding_slot_upgrades {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t)
    (early : t.fork < .glamsterdam) : fundedStake t ≤ fundedStake s :=
  processUpgrades_induction (property := fun u => u.fork < .glamsterdam →
      fundedStake u ≤ fundedStake s)
    (fun {_ post} held nextOk later =>
      (funding_slot_upgrade nextOk later).trans (held (Nat.lt_trans post.property later)))
    (fun _ => Nat.le_refl _) ok early

/-- One slot before Gloas conserves funding up to epoch churn and recorded source credits. -/
theorem funding_slot {x y : ForkedBeaconState preset}
    (early : y.fork < .glamsterdam)
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
  have fundedUpgrade := funding_slot_upgrades (s := ⟨x.fork, advanced⟩) upgrades early
  have carryUpgrade := depositCarry_processUpgrades upgrades early
  change funding_carry y = funding_carry ⟨x.fork, advanced⟩ at carryUpgrade
  rw [carryUpgrade]
  apply (Nat.add_le_add_right fundedUpgrade _).trans
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
  have increment := funding_slot_increment epoched next (by
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
    have bound := funding_epoch before delay
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

end EthLib.Consensus.DirectSafety

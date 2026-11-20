module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Credits

/-!
# The active-stake ceiling

From Electra, the active stake at each state of a branch is at most a ceiling of its epoch.

The ceiling reads only the reference state and the epochs before the state.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-! ## The active-stake ceiling

From a start `v` from Electra, the effective stake active at each state of a branch has a ceiling.

It is the ceiling of the epoch of the state.

The ceiling grows each epoch by twice the issuance envelope and one epoch of deposit churn.

The proof runs over the prefixes of the branch, one epoch at a time.

At the start of epoch `t`, the keys active at `t - 1` and at `t` weigh at most the ceiling of `t`.

Then the blocks and the rewards pass of `t` issue at most twice the envelope of that ceiling.

So the funding at the start of `t + 1` is at most the ceiling of `t + 1`.

The other credits, the floor of the active stake and a few facts of the preset are hypotheses.

The floor is read only at earlier epochs, so a strong induction can supply it.
-/

/-- The funding credit of an event, unless it is a reward or a sync credit. -/
def otherCredit (event : BalanceEvent preset) : Nat :=
  if event.source = .rewards ∨ event.source = .sync then 0 else fundingCredit event

/-- The funding credits of some events are their rewards, their sync credits and the others. -/
theorem fundingCredit_sum (events : List (BalanceEvent preset)) :
    (events.map fundingCredit).sum = sourceCredits .rewards events +
      sourceCredits .sync events + (events.map otherCredit).sum := by
  induction events with
  | nil => simp [sourceCredits]
  | cons event rest ih =>
    simp only [List.map_cons, List.sum_cons, sourceCredits] at ih ⊢
    have single : fundingCredit event =
        (if event.source = .rewards then event.creditLimit else 0) +
          (if event.source = .sync then event.creditLimit else 0) + otherCredit event := by
      obtain ⟨source, _, _, _, _⟩ := event
      cases source <;> simp [fundingCredit, otherCredit]
    omega

/-- Other credits are slashing credits and the immediate deposits before Electra. -/
private theorem otherCredit_sum {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {high : Nat} {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map otherCredit).sum = (events.map fun e =>
      (if e.source = .slashings then e.creditLimit else 0) +
        (if e.source = .deposits ∧ e.before.fork < .pectra then e.creditLimit else 0)).sum := by
  have sites := shared.withdrawnConsolidationCredit_eq_zero tail genesis early delay replayed
  apply congrArg List.sum
  apply List.map_congr_left
  intro e member
  obtain ⟨withdrawn, sources, _⟩ := sites e member
  have zero : ¬ (e.source = .rewards ∨ e.source = .sync ∨ e.source = .slashings ∨
      e.source = .deposits ∨ e.source = .consolidations) → e.creditLimit = 0 := by
    intro outside
    by_contra nonzero
    exact outside (sources (Nat.pos_of_ne_zero nonzero))
  cases source : e.source <;>
    simp_all [otherCredit, fundingCredit]
  by_cases electra : .pectra ≤ e.before.fork
  · have before : ¬ e.before.fork < .pectra := Nat.not_lt_of_ge electra
    simp [electra, before]
  · have before : e.before.fork < .pectra := Nat.lt_of_not_ge electra
    simp [electra, before]

/-- From Electra, only slashing events contribute other funding credits. -/
theorem otherCredit_sum_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {high : Nat} {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map otherCredit).sum =
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  rw [otherCredit_sum shared tail genesis early delay replayed]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e member
  have fork := (shared.withdrawnConsolidationCredit_eq_zero tail genesis early delay
    replayed e member).2.2
  have before : ¬ e.before.fork < .pectra := Nat.not_lt_of_ge (Nat.le_trans electra fork)
  simp [before]

/-- The credit limits of one source are at most all the credit limits. -/
private theorem sourceCredits_le (source : BalanceSource) (events : List (BalanceEvent preset)) :
    sourceCredits source events ≤ (events.map (·.creditLimit)).sum :=
  List.sum_le_sum fun event _ => by split <;> omega

/-- The events of two runs in a row are those of the first and then those of the second. -/
theorem balanceEvents_append {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (tail : Run config checks m y) (high : Nat)
    {first second : List (BalanceEvent preset)} (one : pre.balanceEvents high = .ok first)
    (two : tail.balanceEvents high = .ok second) :
    (pre.append tail).balanceEvents high = .ok (first ++ second) := by
  induction tail generalizing second with
  | nil =>
    cases two
    simpa [Run.append] using one
  | snoc tail step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at two
    obtain ⟨prior, priorOk, rest⟩ := two
    simp only [Run.append, Run.balanceEvents, ih priorOk, bind, Except.bind]
    split at rest
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      rename_i within
      simp [within, addedOk, pure, Except.pure]
    · cases rest
      rename_i outside
      simp [outside, pure, Except.pure]

/-- The upgrades of a slot record no reward and no sync credit. -/
private theorem upgradeBalanceReplay_credits {s t : ForkedBeaconState preset}
    (ok : processUpgrades config checks s = .ok t) {events : List (BalanceEvent preset)}
    (replayed : upgradeBalanceReplay (config := config) (checks := checks) s = .ok events) :
    sourceCredits .rewards events = 0 ∧ sourceCredits .sync events = 0 := by
  fun_induction processUpgrades config checks s generalizing t events with
  | case1 s due ih =>
    obtain ⟨next, nextOk, restOk⟩ := bind_ok_iff.mp ok
    rw [upgradeBalanceReplay] at replayed
    simp only [due, ↓reduceIte, nextOk, bind, Except.bind] at replayed
    cases rest : upgradeBalanceReplay (config := config) (checks := checks) next.val with
    | error => simp [rest] at replayed
    | ok later =>
      have kept := ih next restOk rest
      simp only [rest] at replayed
      split at replayed
      · split at replayed
        · simp only [pure, Except.pure, Except.ok.injEq] at replayed
          subst replayed
          simpa [sourceCredits] using kept
        · simp only [pure, Except.pure, Except.ok.injEq] at replayed
          subst replayed
          exact kept
      · simp only [pure, Except.pure, Except.ok.injEq] at replayed
        subst replayed
        exact kept
  | case2 s due =>
    rw [upgradeBalanceReplay] at replayed
    simp only [due, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at replayed
    subst replayed
    simp [sourceCredits]

/-- A list with no event of a source records no credit of that source. -/
private theorem sourceCredits_eq_zero {source : BalanceSource} {events : List (BalanceEvent preset)}
    (absent : ∀ e ∈ events, e.source ≠ source) : sourceCredits source events = 0 :=
  List.sum_eq_zero fun _ member => by
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    simp [absent e inside]

/-- The replay of an epoch, from Altair, runs justification and inactivity, then the rewards.

Its reward credits are those of the rewards, and it records no sync credit. -/
private theorem epochReplay_rewards {f : Fork} (altair : .altair ≤ f)
    {cached : BeaconState preset f} {post : BalanceReplay preset f}
    (trace : EpochTrace (epochReplayAction (config := config) (checks := checks))
      EpochStage.prefixStages (cached, []) post) :
    ∃ just pass rewarded, EpochStage.Edge config checks .justification cached just ∧
      EpochStage.Edge config checks .inactivity just pass ∧
      replayRewards (config := config) (pass, []) = .ok rewarded ∧
      sourceCredits .rewards post.2 = sourceCredits .rewards rewarded.2 ∧
      sourceCredits .sync post.2 = 0 := by
  obtain ⟨just, pass, rewarded, later, justOk, passOk, replayed, split, laterSources,
    rewardSources⟩ := epochReplay_events altair trace
  have quiet (source : BalanceSource) (other : source ≠ .slashings ∧ source ≠ .deposits ∧
      source ≠ .consolidations) : sourceCredits source later = 0 :=
    sourceCredits_eq_zero fun e member same => by
      rcases laterSources e member with s | s | s <;> rw [s] at same <;> simp_all
  have silent : sourceCredits .sync rewarded.2 = 0 :=
    sourceCredits_eq_zero fun e member same => by
      rcases rewardSources e member with s | s | s <;> rw [s] at same <;> cases same
  refine ⟨just, pass, rewarded, justOk, passOk, replayed, ?_, ?_⟩
  · rw [split, sourceCredits_append, quiet .rewards (by decide), Nat.add_zero]
  · rw [split, sourceCredits_append, quiet .sync (by decide), silent]

/-- With effective stake below `2^64`, the total active balance exists.

It is that stake, or one increment if the stake is smaller. -/
theorem totalActive_exists {f : Fork} {s : BeaconState preset f}
    (early : f < .glamsterdam)
    (fits : ∑ i ∈ (getActiveValidatorIndices s (getCurrentEpoch s)).toFinset,
      effectiveAt ⟨f, s⟩ i.toNat < 2 ^ 64) :
    ∃ total, getTotalActiveBalance s = .ok total ∧
      total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (∑ i ∈ (getActiveValidatorIndices s (getCurrentEpoch s)).toFinset,
          effectiveAt ⟨f, s⟩ i.toNat) := by
  have within := s.validators.bound early
  have inside : ∀ i ∈ getActiveValidatorIndices s (getCurrentEpoch s),
      i.toNat < s.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices within).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have stakeEq := sumMarked_markIndices_eq_stake s (getActiveValidatorIndices s (getCurrentEpoch s))
  have totalOk := getTotalBalance_ok_iff.mpr ⟨inside, by rw [stakeEq]; exact fits, rfl⟩
  refine ⟨_, ?_, (getTotalBalance_ok_iff_stake.mp totalOk).2.2⟩
  unfold getTotalActiveBalance
  rw [getActiveValidatorIndicesChecked_of_within within]
  exact totalOk

/-- With aligned effective balances, the total active balance is a whole number of increments. -/
private theorem increment_dvd_total {f : Fork} {s : BeaconState preset f}
    (aligned : EffectiveBalancesAligned s) {total : Gwei}
    (ok : getTotalActiveBalance s = .ok total) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ total.toNat := by
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok ok)
  rw [value]
  have parts := Finset.dvd_sum fun i (_ : i ∈ (getActiveValidatorIndices s
    (getCurrentEpoch s)).toFinset) => dvd_balanceAt_of_aligned aligned (dvd_refl _) i.toNat
  rcases Nat.le_total preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (Models.stake (fun i => balanceAt s i.toNat)
      (getActiveValidatorIndices s (getCurrentEpoch s)).toFinset) with low | high
  · rw [Nat.max_eq_right low]
    exact parts
  · rw [Nat.max_eq_left high]

/-- The base reward per increment exists at a positive total, if the scaled factor fits. -/
theorem perIncrement_exists {total : Gwei} (positive : 0 < total.toNat)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat <
      2 ^ 64) :
    ∃ perIncrement, getBaseRewardPerIncrement preset total = .ok perIncrement := by
  refine ⟨preset.EFFECTIVE_BALANCE_INCREMENT * preset.BASE_REWARD_FACTOR /
    integerSquareroot total, ?_⟩
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff]
  refine ⟨_, mulChecked_ok_iff.mpr ⟨scaled, by rw [UInt64.toNat_mul, Nat.mod_eq_of_lt scaled]⟩,
    divChecked_ok_iff.mpr ⟨fun zero => ?_, by rw [UInt64.toNat_div]⟩⟩
  have root := congrArg UInt64.toNat zero
  rw [toNat_integerSquareroot, UInt64.toNat_zero, Nat.sqrt_eq_zero] at root
  omega

/-- The flag and block credit bounds imply twice the ceiling's issuance envelope. -/
private theorem epoch_issuance_certificate {r : ForkedBeaconState preset}
    (aligned : EffectiveBalancesAligned r.state)
    (inc : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {total perIncrement : Gwei} (totalOk : getTotalActiveBalance r.state = .ok total)
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement)
    {ceiling : Nat} (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ ceiling)
    (previousLe : ∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling)
    (currentLe : ∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling)
    (ratio : 2 * ceiling ≤ 3 * total.toNat) {F G Y : Nat}
    (flags : F * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * 64) ≤
      54 * perIncrement.toNat * (ceiling / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ^ 2)
    (proposers : G * 448 ≤ 54 * perIncrement.toNat *
      ((∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (sync : Y * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat) :
    F + G + Y ≤ 2 * preset.epochIssuanceBeforeAltair ceiling := by
  have value := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)).2.2
  have divides := increment_dvd_total aligned totalOk
  have positive : 0 < total.toNat := by
    rw [value]
    exact inc.trans_le (Nat.le_max_left _ _)
  have rate : perIncrement.toNat * total.toNat.sqrt ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat := by
    rw [toNat_getBaseRewardPerIncrement per]
    exact Nat.div_mul_le_self _ _
  have attesters := Nat.add_le_add
    (Nat.div_mul_le_self (∑ i ∈ (getActiveValidatorIndices r.state
      (getPreviousEpoch r.state)).toFinset, effectiveAt r i.toNat)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (Nat.div_mul_le_self (∑ i ∈ (getActiveValidatorIndices r.state
      (getCurrentEpoch r.state)).toFinset, effectiveAt r i.toNat)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
  rw [← Nat.add_mul] at attesters
  exact issuance_certificate inc (Nat.div_mul_cancel divides) positive ratio
    (by rw [value]; exact max_le unit currentLe) rate
    (Nat.div_mul_le_self ceiling _) (by omega) flags proposers sync

/-- An overflowing reward factor leaves every flag reward zero in a successful replay. -/
private theorem replayRewards_unscaled_credits_zero
    {fork : Fork} {state after : BeaconState preset fork} {events : List (BalanceEvent preset)}
    (altair : .altair ≤ fork) (within : state.RegistryWithinLimit)
    (replayed : replayRewards (config := config) (state, []) = .ok (after, events))
    (unscaled : ¬ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64) :
    (events.map (·.creditLimit)).sum = 0 := by
  rcases replayRewards_credit_sum altair replayed with ⟨_, zero⟩ |
    ⟨source, target, head, sourceOk, targetOk, headOk, creditSum⟩
  · exact zero
  have zero {index : Fin PARTICIPATION_FLAG_WEIGHTS.length} {deltas : Array Gwei × Array Gwei}
      (computed : getFlagIndexDeltas state altair index = .ok deltas) :
      ((List.range state.validators.data.size).map fun i => (deltas.1.getD i 0).toNat).sum = 0 := by
    obtain ⟨_, _, _, _, _, _, each⟩ := getFlagIndexDeltas_getD within computed
    apply List.sum_eq_zero
    intro value member
    obtain ⟨j, rangeMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨eligible, _, absent, paid⟩ := each j (List.mem_range.mp rangeMember)
    cases eligible with
    | false => rw [(absent rfl).1]; rfl
    | true =>
      obtain ⟨base, baseOk, _⟩ := paid rfl
      simp only [getBaseReward, altair, ↓reduceIte, bind_ok_iff] at baseOk
      obtain ⟨_, _, perIncrement, per, _⟩ := baseOk
      simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at per
      obtain ⟨_, scaled, _⟩ := per
      exact (unscaled (mulChecked_ok_iff.mp scaled).1).elim
  rw [creditSum, zero sourceOk, zero targetOk, zero headOk]

/-- The issuance of one epoch from Electra is at most twice the issuance envelope of the ceiling.

It is the proposer and sync credits of the blocks of the epoch, and the rewards of its pass.

The epoch runs from `r` to `s`, and the slot from `s` to `w` ends it.

The keys active at the previous and the current epoch of `r` weigh at most the ceiling.

Twice the ceiling is at most three times the total active balance.

The slot moves the epoch on by one. -/
private theorem epoch_issuance_actual {r s w : ForkedBeaconState preset}
    (inner : Run config checks r s) (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (electra : .pectra ≤ r.fork) (boundary : advanceSlotAcross config checks s = .ok w)
    (early : w.fork < .glamsterdam)
    (crossing : getCurrentEpoch s.state < getCurrentEpoch w.state)
    (high : Nat) {inside after : List (BalanceEvent preset)}
    (insideOk : inner.balanceEvents high = .ok inside)
    (afterOk : (Step.slot boundary).balanceEvents = .ok after)
    (aligned : EffectiveBalancesAligned r.state)
    (inc : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {ceiling : Nat} (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ ceiling)
    (previousLe : ∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling)
    (currentLe : ∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling)
    (ratio : ∀ total, getTotalActiveBalance r.state = .ok total →
      2 * ceiling ≤ 3 * total.toNat) :
    sourceCredits .rewards inside + sourceCredits .sync inside +
        (sourceCredits .rewards after + sourceCredits .sync after) ≤
      2 * preset.epochIssuanceBeforeAltair ceiling ∧
      (getCurrentEpoch w.state).toNat = (getCurrentEpoch s.state).toNat + 1 := by
  have sEarly : s.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot boundary).chainStep.fork_le early
  have rEarly : r.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) sEarly
  have sElectra : .pectra ≤ s.fork := Nat.le_trans electra (fork_le_of_chainSteps inner.chainSteps)
  have altair : .altair ≤ s.fork := Nat.le_trans (by decide) sElectra
  obtain ⟨reads, creditBound⟩ := epoch_credits_data inner electra sEarly same high insideOk
  -- The slot from `s` runs the epoch transition, whose replay holds the rewards pass.
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp boundary
  have advanceCopy := advanceOk
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
  obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, advancedEq⟩ := advanceCopy
  have sum := (Uint64.addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
  simp only [UInt64.toNat_one] at sum
  have wSlot : w.state.slot = next := by rw [processUpgrades_slot upgrades, ← advancedEq]
  have last : next % preset.SLOTS_PER_EPOCH = 0 := by
    by_contra inside
    have epochs := nextSlot_epoch_of_inside sum inside
    have later := UInt64.lt_iff_toNat_lt.mp crossing
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, wSlot] at later
    omega
  have epochs := nextSlot_epoch_of_boundary sum last
  simp only [epochIfLast, last, ↓reduceIte] at epochOk
  obtain ⟨middle, -, epochEvents, epochReplay, -⟩ :=
    epochBalanceReplay_result cached epoched sEarly epochOk
  obtain ⟨crossings, crossingOk, _⟩ := upgradeBalanceReplay_bounded upgrades
  have split := Step.balanceEvents_epoch_slot boundary cachedOk nextOk last epochReplay
    advanceOk crossingOk
  obtain rfl := Except.ok.inj (afterOk.symm.trans split)
  have crossed := upgradeBalanceReplay_credits upgrades crossingOk
  obtain ⟨just, pass, ⟨rewardState, rewardEvents⟩, justified, scored, rewarded, rewardsSame,
    syncNone⟩ := epochReplay_rewards altair (epochBalanceReplay_trace epochReplay)
  -- The pass reads the total of `r`, and its participants weigh at most the ceiling.
  obtain ⟨activeKept, effectiveKept, passEpoch⟩ := pass_kept inner electra sEarly same cachedOk
    justified scored
  have totalSame := total_active_congr rEarly sEarly
    (activeKept.mono (getCurrentEpoch_le_activityFixedEpoch _)) passEpoch effectiveKept
  have cases : (∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
      (sourceCredits .rewards inside = 0 ∧ sourceCredits .sync inside = 0 ∧
        (rewardEvents.map (·.creditLimit)).sum = 0) := by
    rcases reads with reads | quiet
    · exact .inl reads
    rcases replayRewards_credit_sum altair rewarded with ⟨_, zero⟩ |
      ⟨source, _, _, sourceOk, _⟩
    · exact .inr ⟨quiet.1, quiet.2.1, zero⟩
    by_cases scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64
    · simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok] at sourceOk
      obtain ⟨_, _, _, _, total, passTotal, _⟩ := sourceOk
      have totalOk : getTotalActiveBalance r.state = .ok total := totalSame.symm.trans passTotal
      have value := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)).2.2
      have positive : 0 < total.toNat := by
        rw [value]
        exact inc.trans_le (Nat.le_max_left _ _)
      obtain ⟨perIncrement, per⟩ := perIncrement_exists positive scaled
      exact .inl ⟨total, perIncrement, totalOk, per⟩
    exact .inr ⟨quiet.1, quiet.2.1, replayRewards_unscaled_credits_zero altair
      (pass.validators.bound sEarly) rewarded scaled⟩
  rcases cases with ⟨total, perIncrement, totalOk, per⟩ | ⟨quietRewards, quietSync, quietPass⟩
  swap
  · have zero : sourceCredits .rewards rewardEvents = 0 := by
      have := sourceCredits_le .rewards rewardEvents
      omega
    refine ⟨?_, ?_⟩
    · simp only [sourceCredits_append, crossed.1, crossed.2, rewardsSame, syncNone,
        quietRewards, quietSync, zero, Nat.zero_add]
      exact Nat.zero_le _
    · rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, wSlot]
      exact epochs
  obtain ⟨proposers, sync, _⟩ := creditBound total perIncrement totalOk per
  have passTotal : getTotalActiveBalance pass = .ok total := totalSame.trans totalOk
  have flags := replayRewards_credits_le altair (pass.validators.bound sEarly) rewarded passTotal
    per ceiling fun _ _ _ flagged weighed =>
      (participating_le_previous inner same electra sEarly cachedOk justified scored altair
        flagged weighed).trans (max_le unit previousLe)
  have bound := epoch_issuance_certificate aligned inc totalOk per unit previousLe currentLe
    (ratio total totalOk) flags proposers sync
  have rewardsLe := sourceCredits_le .rewards rewardEvents
  simp only [sourceCredits_append, crossed.1, crossed.2, rewardsSame, syncNone, Nat.add_zero]
  refine ⟨by omega, ?_⟩
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, wSlot]
  exact epochs

/-- Actual block reads bound a same-epoch prefix; a quiet prefix has zero issuance. -/
theorem epoch_prefix_issuance_le {r s : ForkedBeaconState preset}
    (inner : Run config checks r s) (electra : .pectra ≤ r.fork)
    (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (aligned : EffectiveBalancesAligned r.state)
    (inc : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {ceiling : Nat} (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ ceiling)
    (previousLe : ∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling)
    (currentLe : ∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling)
    (ratio : ∀ total, getTotalActiveBalance r.state = .ok total →
      2 * ceiling ≤ 3 * total.toNat)
    (high : Nat) {events : List (BalanceEvent preset)}
    (replayed : inner.balanceEvents high = .ok events) :
    sourceCredits .rewards events + sourceCredits .sync events ≤
      2 * preset.epochIssuanceBeforeAltair ceiling := by
  obtain ⟨reads, credits⟩ := epoch_credits_data inner electra early same high replayed
  rcases reads with ⟨total, perIncrement, totalOk, per⟩ | ⟨quietRewards, quietSync, _⟩
  swap
  · rw [quietRewards, quietSync]
    exact Nat.zero_le _
  obtain ⟨proposers, sync, _⟩ := credits total perIncrement totalOk per
  have bound := epoch_issuance_certificate (F := 0) aligned inc totalOk per unit previousLe
    currentLe (ratio total totalOk) (by simp) proposers sync
  simpa only [Nat.zero_add] using bound

/-- The funding of a branch from `v`, after `t` epochs, is at most the ceiling of epoch `t`.

The ceiling starts at `start` plus `allowance`, and grows by the issuance and the churn. -/
theorem ceiling_ge (ceiling : Nat → Nat) {start allowance : Nat}
    (base : start + allowance ≤ ceiling 0)
    (grows : ∀ t, ceiling t + 2 * preset.epochIssuanceBeforeAltair (ceiling t) +
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ≤ ceiling (t + 1)) (t : Nat) :
    start + allowance + t * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
      ∑ s ∈ Finset.range t, 2 * preset.epochIssuanceBeforeAltair (ceiling s) ≤ ceiling t := by
  induction t with
  | zero => simpa using base
  | succ t ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, Nat.one_mul]
    have := grows t
    omega

/-- The active-stake ceiling over the prefixes of a branch from `v`, one epoch at a time.

Each prefix ends inside an epoch that started at a state `r`.

The run to `r` issues at most twice the envelope of each earlier ceiling.

At `r` the keys active at the previous and at the current epoch weigh at most its ceiling.

The ratio of the ceiling to the total active balance is read only before the epoch of `y`.

At `y` the keys active at the current and at the previous epoch weigh at most that ceiling. -/
private theorem apriori_prefix_witness {g v y : ForkedBeaconState preset}
    (shared : Run config checks g v) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks v y) (electra : .pectra ≤ v.fork) (early : y.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (inc : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (ceiling : Nat → Nat) {start allowance : Nat}
    (startLe : fundedStake v + previousOnlyStake v + fundingCarry v ≤ start)
    (base : start + allowance ≤ ceiling 0)
    (grows : ∀ t, ceiling t + 2 * preset.epochIssuanceBeforeAltair (ceiling t) +
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ≤ ceiling (t + 1))
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ ceiling 0)
    (others : ∀ {u : ForkedBeaconState preset} (head : Run config checks v u),
      u.fork < .glamsterdam → (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ found,
        head.balanceEvents high = .ok found → (found.map otherCredit).sum ≤ allowance)
    (ratio : ∀ {u : ForkedBeaconState preset}, Run config checks v u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        2 * ceiling ((getCurrentEpoch u.state).toNat - (getCurrentEpoch v.state).toNat) ≤
          3 * total.toNat) :
    ∃ (r : ForkedBeaconState preset) (pre : Run config checks v r)
      (inner : Run config checks r y) (before during : List (BalanceEvent preset)),
      tail = pre.append inner ∧
      pre.balanceEvents high = .ok before ∧ inner.balanceEvents high = .ok during ∧
      getCurrentEpoch y.state = getCurrentEpoch r.state ∧
      (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
        effectiveAt r i.toNat) ≤
        ceiling ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat) ∧
      (∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
        effectiveAt r i.toNat) ≤
        ceiling ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat) ∧
      sourceCredits .rewards before + sourceCredits .sync before ≤
        ∑ s ∈ Finset.range ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat),
          2 * preset.epochIssuanceBeforeAltair (ceiling s) := by
  have mono : Monotone ceiling := monotone_nat_of_le_succ fun t =>
    (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (grows t))
  have total := ceiling_ge (config := config) ceiling base grows
  let issued (t : Nat) := ∑ s ∈ Finset.range t, 2 * preset.epochIssuanceBeforeAltair (ceiling s)
  let index (u : ForkedBeaconState preset) :=
    (getCurrentEpoch u.state).toNat - (getCurrentEpoch v.state).toNat
  let previousStake (r : ForkedBeaconState preset) :=
    ∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
      effectiveAt r i.toNat
  let currentStake (r : ForkedBeaconState preset) :=
    ∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
      effectiveAt r i.toNat
  have vEarly : v.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have vUnique := shared.pubkeysDistinct genesis
  -- Each head ends inside an epoch that started at `r`, with the facts above at `r`.
  have key : ∀ {u : ForkedBeaconState preset} (head : Run config checks v u),
      u.fork < .glamsterdam → (getCurrentEpoch u.state).toNat ≤ high + 1 →
      (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch y.state).toNat →
      ∃ (r : ForkedBeaconState preset) (pre : Run config checks v r)
        (inner : Run config checks r u) (before during : List (BalanceEvent preset)),
        head = pre.append inner ∧
        pre.balanceEvents high = .ok before ∧ inner.balanceEvents high = .ok during ∧
        getCurrentEpoch u.state = getCurrentEpoch r.state ∧
        currentStake r ≤ ceiling (index r) ∧ previousStake r ≤ ceiling (index r) ∧
        sourceCredits .rewards before + sourceCredits .sync before ≤ issued (index r) := by
    intro u head
    induction head with
    | nil =>
      intro _ _ _
      refine ⟨v, .nil, .nil, [], [], rfl, rfl, rfl, rfl, ?_, ?_, by simp [sourceCredits]⟩
      · have funded : currentStake v ≤ fundedStake v := activeEffective_le_funded v vEarly vUnique
        have zero : ceiling 0 ≤ ceiling (index v) := mono (Nat.zero_le _)
        omega
      · have previous : previousStake v ≤ fundedStake v + previousOnlyStake v :=
          previousStake_le_start v vEarly vUnique
        have zero : ceiling 0 ≤ ceiling (index v) := mono (Nat.zero_le _)
        omega
    | @snoc u u' pre step ih =>
      intro lEarly lEpoch lEnd
      have uEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le lEarly
      have uEpoch := (UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le).trans lEpoch
      obtain ⟨r, toR, inner, before, during, split, beforeOk, duringOk, same, current, previous,
        issuance⟩ := ih uEarly uEpoch
        ((UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le).trans lEnd)
      obtain ⟨added, addedOk⟩ := step.balanceEvents_ok lEarly
      have stepEvents : (inner.snoc step).balanceEvents high = .ok (during ++ added) := by
        simp [Run.balanceEvents, duringOk, addedOk, uEpoch, pure, Except.pure, bind,
          Except.bind]
      by_cases kept : getCurrentEpoch u'.state = getCurrentEpoch u.state
      · -- The step stays inside the epoch, which still started at `r`.
        exact ⟨r, toR, inner.snoc step, before, during ++ added,
          congrArg (fun p => p.snoc step) split, beforeOk, stepEvents,
          kept.trans same, current, previous, issuance⟩
      -- A step that leaves the epoch is a slot at its boundary.
      have crossing : getCurrentEpoch u.state < getCurrentEpoch u'.state :=
        UInt64.lt_of_le_of_ne step.chainStep.currentEpoch_le (Ne.symm kept)
      obtain ⟨boundary, rfl⟩ : ∃ boundary, step = .slot boundary := by
        cases step with
        | block engine signed due ok =>
          exact absurd (by simp only [getCurrentEpoch, (frame_processBlock
            (applySignedBlock_ok ok).2.1).slot]) kept
        | slot ok => exact ⟨ok, rfl⟩
      have rElectra : .pectra ≤ r.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps toR.chainSteps)
      have uElectra : .pectra ≤ u.fork :=
        Nat.le_trans rElectra (fork_le_of_chainSteps inner.chainSteps)
      have rEpoch := congrArg UInt64.toNat same
      have aligned := (run_justified_separated (shared.append toR) genesis).1.aligned maxAligned
      obtain ⟨issue, next⟩ :=
          epoch_issuance_actual inner same rElectra boundary lEarly crossing high
        duringOk addedOk aligned inc ((unit.trans (mono (Nat.zero_le _))))
        previous current
        (ratio toR (Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) uEarly) (by
          have := UInt64.lt_iff_toNat_lt.mp crossing
          omega))
      -- The new epoch starts at `u'`, after the run to `u` and the slot.
      let toNext := (toR.append inner).snoc (.slot boundary)
      have middleOk := balanceEvents_append toR inner high beforeOk duringOk
      have nextOk : toNext.balanceEvents high = .ok (before ++ during ++ added) := by
        simp [toNext, Run.balanceEvents, middleOk, addedOk, uEpoch, pure, Except.pure, bind,
          Except.bind]
      have nextIndex : index u' = index r + 1 := by
        simp only [index]
        have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toR.chainSteps)
        omega
      have nextIssued : sourceCredits .rewards (before ++ during ++ added) +
          sourceCredits .sync (before ++ during ++ added) ≤
            ∑ s ∈ Finset.range (index r + 1), 2 * preset.epochIssuanceBeforeAltair (ceiling s) := by
        simp only [sourceCredits_append, Finset.sum_range_succ]
        simp only [issued] at issuance
        omega
      have nextOthers := others toNext lEarly lEpoch _ nextOk
      have nextFunding := fundingCredit_sum (before ++ during ++ added)
      have fundingSplit : ((before ++ during ++ added).map fundingCredit).sum =
          ((before ++ during).map fundingCredit).sum + (added.map fundingCredit).sum := by
        rw [List.map_append, List.sum_append]
      have bound := total (index r + 1)
      have funded := funding_le_ceiling shared toNext genesis lEarly delay high lEpoch _ nextOk
        (start := start) (by omega)
      have uFunded := funding_le_ceiling shared (toR.append inner) genesis uEarly delay high
        uEpoch _ middleOk (start := start) (by omega)
      have previousNext := previousStake_le_ceiling (shared.append (toR.append inner)) genesis
        boundary crossing uElectra lEarly delay addedOk
      have currentNext := activeEffective_le_funded u' lEarly
        ((shared.append toNext).pubkeysDistinct genesis)
      have epochNext : (getCurrentEpoch u'.state).toNat - (getCurrentEpoch v.state).toNat =
          index r + 1 := nextIndex
      have epochHere : (getCurrentEpoch u.state).toNat - (getCurrentEpoch v.state).toNat =
          index r := by
        simp only [index]
        omega
      rw [epochNext] at funded
      rw [epochHere] at uFunded
      have churnNext : (index r + 1) * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat =
          index r * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
            config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := Nat.succ_mul _ _
      refine ⟨u', toNext, .nil, before ++ during ++ added, [],
        congrArg (fun p => p.snoc (.slot boundary)) split, nextOk, rfl, rfl, ?_, ?_, ?_⟩
      · simp only [currentStake, nextIndex]
        omega
      · simp only [previousStake, nextIndex]
        omega
      · simpa only [issued, nextIndex] using nextIssued
  exact key tail early endEpoch (Nat.le_refl _)

/-- The effective balances active in an epoch sum the same at two states of one epoch of a run.

The epoch is at most the epoch of the first state. -/
theorem activeStake_eq_of_same_epoch {r y : ForkedBeaconState preset}
    (inner : Run config checks r y) (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch r.state) (epoch : Epoch)
    (low : epoch ≤ getCurrentEpoch r.state) :
    ∑ i ∈ (getActiveValidatorIndices y.state epoch).toFinset, effectiveAt y i.toNat =
      ∑ i ∈ (getActiveValidatorIndices r.state epoch).toFinset, effectiveAt r i.toNat := by
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  have weights := run_same_epoch_effective inner early same
  rw [(activeKept_of_chainSteps inner.chainSteps).getActiveValidatorIndices_eq
    (UInt64.le_trans low (getCurrentEpoch_le_activityFixedEpoch _))]
  refine Finset.sum_congr rfl fun i member => weights i.toNat ?_
  obtain ⟨_, found, _⟩ := (mem_getActiveValidatorIndices (r.state.validators.bound rEarly)).mp
    (List.mem_toFinset.mp member)
  exact (Array.getElem?_eq_some_iff.mp found).1

theorem activeStake_same_epoch {r y : ForkedBeaconState preset}
    (inner : Run config checks r y) (_electra : .pectra ≤ r.fork)
    (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch r.state) {bound : Nat}
    (current : (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
      effectiveAt r i.toNat) ≤ bound)
    (previous : (∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
      effectiveAt r i.toNat) ≤ bound) :
    (∑ i ∈ (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).toFinset,
      effectiveAt y i.toNat) ≤ bound ∧
    (∑ i ∈ (getActiveValidatorIndices y.state (getPreviousEpoch y.state)).toFinset,
      effectiveAt y i.toNat) ≤ bound := by
  have previousSame : getPreviousEpoch y.state = getPreviousEpoch r.state := by
    simp only [getPreviousEpoch, same]
  rw [same, activeStake_eq_of_same_epoch inner early same _ (UInt64.le_refl _), previousSame,
    activeStake_eq_of_same_epoch inner early same _ (getPreviousEpoch_le _)]
  exact ⟨current, previous⟩

/-- From Electra, the ceiling `T_plus` does not decrease from one epoch to the next. -/
theorem ceilingAt_mono {x : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (high : Nat) : Monotone (stakeCeilingAt config x high) := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [stakeCeilingAt, stakeCeiling, zero, Nat.lt_irrefl, false_and, ↓reduceIte]
  omega

/-- From an Electra start `x`, the stake active at each state of a branch is at most `T_plus`.

`T_plus` is read at the epoch of the state, and the stake is the effective stake of the active keys.

The keys active at the previous epoch of the state weigh at most the same `T_plus`.

Two hypotheses remain: a floor and the whistleblower allowance.

The floor `T_minus` bounds the total active balance of each state of an earlier epoch from below.

The credits other than rewards and sync credits fit the whistleblower allowance `Omega`.

Four facts of the preset and the ceiling are hypotheses too. -/
theorem activeStake_prefix_witness {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) (maxAligned : MaxEffectiveBalancesAligned preset)
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
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) ≤ total.toNat) :
    ∃ (r : ForkedBeaconState preset) (pre : Run config checks x r)
      (inner : Run config checks r y) (before during : List (BalanceEvent preset)),
      tail = pre.append inner ∧
      pre.balanceEvents high = .ok before ∧ inner.balanceEvents high = .ok during ∧
      getCurrentEpoch y.state = getCurrentEpoch r.state ∧
      (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
        effectiveAt r i.toNat) ≤ stakeCeilingAt config x high
          ((getCurrentEpoch r.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
        effectiveAt r i.toNat) ≤ stakeCeilingAt config x high
          ((getCurrentEpoch r.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      sourceCredits .rewards before + sourceCredits .sync before ≤
        ∑ s ∈ Finset.range ((getCurrentEpoch r.state).toNat - (getCurrentEpoch x.state).toNat),
          2 * preset.epochIssuanceBeforeAltair (stakeCeilingAt config x high s) := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  obtain ⟨inc, -, -, -, -, -, -, -, -, delay, -, -, ratioGuard, -⟩ := guard
  rw [zero] at ratioGuard
  have grows (t : Nat) : stakeCeilingAt config x high t + 2 * preset.epochIssuanceBeforeAltair
      (stakeCeilingAt config x high t) + config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ≤
      stakeCeilingAt config x high (t + 1) := by
    simp [stakeCeilingAt, stakeCeiling, zero]
  have base : fundedStake x + previousOnlyStake x + fundingCarry x +
      whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
          (unassignedPreStake x)
        (fundingCarry x) (exitedSlashableCount x) (driftHorizon x high) 0 ≤
      stakeCeilingAt config x high 0 := by
    simp only [stakeCeilingAt, stakeCeiling, zero, Nat.lt_irrefl, ↓reduceIte, Nat.le_refl]
  refine apriori_prefix_witness shared genesis tail electra early delay maxAligned inc
    high endEpoch (stakeCeilingAt config x high) (Nat.le_refl _) base grows unit
    (fun head early within found ok => by simpa only [zero] using others head early within found ok)
    fun {u} head uEarly within total ok => by
      have ratio := ratioGuard ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat)
        (Nat.zero_le _) (by unfold driftHorizon; omega)
      have lower := floor head uEarly within total ok
      simp only [stakeCeilingAt, stakeFloorAt, zero] at lower ⊢
      omega

theorem activeStake_le_ceiling {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) (maxAligned : MaxEffectiveBalancesAligned preset)
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
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) ≤ total.toNat) :
    ∑ i ∈ (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).toFinset,
        effectiveAt y i.toNat ≤
      stakeCeilingAt config x high
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
    ∑ i ∈ (getActiveValidatorIndices y.state (getPreviousEpoch y.state)).toFinset,
        effectiveAt y i.toNat ≤
      stakeCeilingAt config x high
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) := by
  obtain ⟨r, pre, inner, _, _, _, _, _, same, current, previous, _⟩ :=
    activeStake_prefix_witness shared genesis tail electra early high endEpoch guard maxAligned
      unit others floor
  have rElectra : .pectra ≤ r.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  simpa only [same] using activeStake_same_epoch inner rElectra early same current previous

/-- Before the epoch sentinel, the unassigned resource pot is exactly the stake `PreU`.

`PreU` is the pre-active stake of the validators with no assigned activation epoch. -/
private theorem unassigned_resources_eq_pre {g x : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    (∑ i ∈ Finset.range x.state.validators.data.size,
      if (x.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
          FAR_FUTURE_EPOCH then
        ((x.state.validators.data[i]?).map fun v => max v.effectiveBalance.toNat
          (min (actualBalanceAt x i)
            (withdrawalMaxEffectiveBalance preset x.fork v).toNat)).getD 0
      else 0) = unassignedPreStake x := by
  have order := shared.activationExitOrder genesis
  unfold unassignedPreStake
  rw [funding_sum_zipIdx x.state.validators.data.toList (fun v i =>
    if !isActiveValidator v (getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.exitEpoch) &&
        v.activationEpoch == FAR_FUTURE_EPOCH then
      max (effectiveAt x i)
        (min (actualBalanceAt x i) (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    else 0)]
  simp only [Array.length_toList, Array.getElem?_toList]
  apply Finset.sum_congr rfl
  intro i _
  cases found : x.state.validators.data[i]? with
  | none => simp
  | some v =>
    by_cases pending : v.activationEpoch = FAR_FUTURE_EPOCH
    · have exit : v.exitEpoch = FAR_FUTURE_EPOCH := by
        have ordered := UInt64.le_iff_toNat_le.mp
          (order v (Array.mem_of_getElem? found))
        have limit := v.exitEpoch.toNat_lt
        apply UInt64.toNat_inj.mp
        rw [pending] at ordered
        change v.exitEpoch.toNat = 18446744073709551615
        change 18446744073709551615 ≤ v.exitEpoch.toNat at ordered
        omega
      have inactive : isActiveValidator v (getCurrentEpoch x.state) = false := by
        have lower := UInt64.lt_iff_toNat_lt.mp finite
        simp only [isActiveValidator, pending, exit, UInt64.le_iff_toNat_le,
          UInt64.lt_iff_toNat_lt, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        left
        omega
      simp [found, pending, exit, inactive, finite, effectiveAt]
    · simp [pending]

/-- Newly assigned candidates are paid from three sources.

They are the unassigned pre-active stake `PreU`, the carry and the epoch deposit allowance. -/
private theorem unassigned_assignment_budget {g x u : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (head : Run config checks x u) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : u.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH) :
    preset.MAX_EFFECTIVE_BALANCE.toNat *
      ((Finset.range u.state.validators.data.size).filter fun i =>
        (x.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
            FAR_FUTURE_EPOCH ∧
          (u.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH ≠
            FAR_FUTURE_EPOCH).card ≤
      unassignedPreStake x + fundingCarry x +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat + 1) := by
  have bound := shared.unassigned_assignment_resources genesis head caps.activation
    caps.compounding aligned electra early
  dsimp only at bound
  change _ ≤ _ at bound
  have initial := unassigned_resources_eq_pre shared genesis finite
  dsimp only [actualBalanceAt] at initial
  rw [initial] at bound
  simp only [fundingCarry, electra, ↓reduceDIte, not_not] at bound ⊢
  omega

/-- Dividing the shared assignment budget by MEB bounds newly assigned keys. -/
private theorem unassigned_assignment_count {g x u : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (head : Run config checks x u) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : u.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat) :
    ((Finset.range u.state.validators.data.size).filter fun i =>
      (x.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH =
          FAR_FUTURE_EPOCH ∧
        (u.state.validators.data[i]?.map (·.activationEpoch)).getD FAR_FUTURE_EPOCH ≠
          FAR_FUTURE_EPOCH).card ≤
      (unassignedPreStake x + fundingCarry x +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat + 1)) /
        preset.MAX_EFFECTIVE_BALANCE.toNat := by
  apply (Nat.le_div_iff_mul_le positive).mpr
  rw [Nat.mul_comm]
  exact unassigned_assignment_budget shared genesis head caps aligned electra early finite

/-- Initial active and scheduled keys plus the assignment budget cover window assignments. -/
theorem windowAssignments_le_budget {g x u : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (head : Run config checks x u) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : u.fork < .glamsterdam)
    (finite : getCurrentEpoch x.state < FAR_FUTURE_EPOCH)
    (positive : 0 < preset.MAX_EFFECTIVE_BALANCE.toNat) :
    ((Finset.range u.state.validators.data.size).filter fun i =>
      (u.state.validators.data[i]?).any (·.activationEpoch != FAR_FUTURE_EPOCH) &&
        (x.state.validators.data[i]?).all fun w => w.activationEpoch == FAR_FUTURE_EPOCH ||
          decide (getCurrentEpoch x.state < w.exitEpoch)).card ≤
      referenceCount x + scheduledActivationCount x +
        (unassignedPreStake x + fundingCarry x +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat *
            ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat + 1)) /
          preset.MAX_EFFECTIVE_BALANCE.toNat := by
  exact head.windowAssignments_le_initial_add_new.trans
    (Nat.add_le_add (Nat.add_le_add_right (activeCount_le_refCount shared genesis
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps head.chainSteps) early)) _)
      (unassigned_assignment_count shared genesis head caps aligned electra early finite positive))

/-- A newly slashed assigned key is a window assignment or an initially slashable exited key. -/
private theorem newly_slashed_initial_classification {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (finite : getCurrentEpoch y.state < FAR_FUTURE_EPOCH)
    (i : Nat) (w : Validator) (after : y.state.validators.data[i]? = some w)
    (initialFlag : (x.state.validators.data[i]?.map (·.slashed)).getD false = false)
    (slashed : w.slashed = true) :
    ((y.state.validators.data[i]?).any (·.activationEpoch != FAR_FUTURE_EPOCH) &&
      (x.state.validators.data[i]?).all fun v => v.activationEpoch == FAR_FUTURE_EPOCH ||
        decide (getCurrentEpoch x.state < v.exitEpoch)) = true ∨
    ∃ v, x.state.validators.data[i]? = some v ∧ v.slashed = false ∧
      v.exitEpoch ≤ getCurrentEpoch x.state ∧ getCurrentEpoch x.state < v.withdrawableEpoch := by
  have assigned := (shared.append tail).slashed_activation_assigned genesis caps.activation
    caps.compounding aligned early finite i w after slashed
  cases before : x.state.validators.data[i]? with
  | none => exact .inl (by simp [after, assigned])
  | some v =>
    have unslashed : v.slashed = false := by simpa [before] using initialFlag
    by_cases exited : v.exitEpoch ≤ getCurrentEpoch x.state
    · exact .inr ⟨v, rfl, unslashed, exited,
        tail.newly_slashed_initial_exited_unwithdrawable caps.activation caps.compounding
          early i v w before after unslashed slashed exited⟩
    · have live := UInt64.not_le.mp exited
      exact .inl (by simp [after, assigned, live])

/-- The initially exited slashable keys are counted over their registry positions. -/
private theorem slashableInactiveCount_eq_card (x : ForkedBeaconState preset) :
    exitedSlashableCount x = ((Finset.range x.state.validators.data.size).filter fun i =>
      (x.state.validators.data[i]?).any fun v => !v.slashed &&
        decide (v.exitEpoch ≤ getCurrentEpoch x.state) &&
        decide (getCurrentEpoch x.state < v.withdrawableEpoch)).card := by
  let p := fun v : Validator => !v.slashed &&
    decide (v.exitEpoch ≤ getCurrentEpoch x.state) &&
    decide (getCurrentEpoch x.state < v.withdrawableEpoch)
  have count (l : List Validator) : l.countP p =
      (l.map fun v => if p v then 1 else 0).sum := by
    induction l with
    | nil => simp
    | cons v l ih => cases chosen : p v <;> simp [chosen, ih, Nat.add_comm]
  have mapped : (x.state.validators.data.toList.zipIdx.map fun (v, _i) =>
      if p v then 1 else 0) =
      x.state.validators.data.toList.map (fun v => if p v then 1 else 0) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map fun v => if p v then 1 else 0)
        (List.zipIdx_map_fst 0 x.state.validators.data.toList)
  rw [exitedSlashableCount, count, ← mapped,
    funding_sum_zipIdx x.state.validators.data.toList (fun v _ => if p v then 1 else 0),
    Array.length_toList, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases found : x.state.validators.data[i]? with
  | none => simp [Array.getElem?_toList, found]
  | some v => simp [Array.getElem?_toList, found, p]

/-- Newly slashed keys belong to the window assignments or to the initial exited cohort. -/
theorem newly_slashed_count_le {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (early : y.fork < .glamsterdam)
    (finite : getCurrentEpoch y.state < FAR_FUTURE_EPOCH) :
    ((Finset.range y.state.validators.data.size).filter fun i =>
      !(x.state.validators.data[i]?.map (·.slashed)).getD false &&
        (y.state.validators.data[i]?.map (·.slashed)).getD false).card ≤
      ((Finset.range y.state.validators.data.size).filter fun i =>
        (y.state.validators.data[i]?).any (·.activationEpoch != FAR_FUTURE_EPOCH) &&
          (x.state.validators.data[i]?).all fun v => v.activationEpoch == FAR_FUTURE_EPOCH ||
            decide (getCurrentEpoch x.state < v.exitEpoch)).card + exitedSlashableCount x := by
  rw [slashableInactiveCount_eq_card]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro i member
  obtain ⟨inside, marked⟩ := Finset.mem_filter.mp member
  have flags : (x.state.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (y.state.validators.data[i]?.map (·.slashed)).getD false = true := by
    simpa only [Bool.and_eq_true, Bool.not_eq_true'] using marked
  cases found : y.state.validators.data[i]? with
  | none => simp [found] at flags
  | some w =>
    have slashed : w.slashed = true := by simpa [found] using flags.2
    rcases newly_slashed_initial_classification shared genesis tail caps aligned early finite
        i w found flags.1 slashed with assigned | ⟨v, before, unslashed, exited, withdrawn⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inside, assigned⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp before).1,
          by simp [before, unslashed, exited, withdrawn]⟩)

/-- Before Electra, the active validators at each state of a branch from `x` follow `A_t`.

Each of them is given an activation epoch, and it had not exited at `x`.

So it is one of the validators given an activation epoch in the window.

Their count follows `A_t`. -/
theorem activeCount_le_countPath {g x z : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x z) (early : z.fork < .pectra) :
    activeCount z.state ≤ activeCountPath config (referenceCount x + scheduledActivationCount x)
      ((getCurrentEpoch z.state).toNat - (getCurrentEpoch x.state).toNat) := by
  have within := z.state.validators.bound (Nat.lt_trans early (by decide))
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have later := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have life := tail.registryLifecycle
  refine Nat.le_trans ?_ (windowActivations_le_countPath shared genesis tail early)
  have nodup : (getActiveValidatorIndices z.state (getCurrentEpoch z.state)).Nodup :=
    (getActiveValidatorIndices_sorted within _).imp fun {a b} less (same : a = b) => by
      subst same; exact UInt64.lt_irrefl _ less
  rw [activeCount, ← List.toFinset_card_of_nodup nodup,
    ← Finset.card_image_of_injective _ (fun a b same => UInt64.toNat_inj.mp same)]
  refine Finset.card_le_card fun i member => ?_
  obtain ⟨j, chosen, rfl⟩ := Finset.mem_image.mp member
  obtain ⟨v, found, active⟩ := (mem_getActiveValidatorIndices within).mp
    (List.mem_toFinset.mp chosen)
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
    UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at active
  have exitBound := v.exitEpoch.toNat_lt
  simp only [Finset.mem_filter, Finset.mem_range, found, Option.any_some, bne_iff_ne, ne_eq,
    Bool.and_eq_true]
  refine ⟨(Array.getElem?_eq_some_iff.mp found).1, fun same => ?_, ?_⟩
  · rw [same, far] at active
    omega
  -- A validator that had exited at `x` keeps its exit epoch, so it is not active at `z`.
  cases old : x.state.validators.data[j.toNat]? with
  | none => rfl
  | some w =>
    obtain ⟨v', found', kept⟩ := life.validators _ w old
    obtain rfl : v' = v := Option.some.inj (found'.symm.trans found)
    simp only [Option.all_some, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    by_cases assigned : w.exitEpoch = FAR_FUTURE_EPOCH
    · right
      rw [UInt64.lt_iff_toNat_lt, assigned, far]
      omega
    · right
      have same := kept.exitEpoch assigned
      rw [UInt64.lt_iff_toNat_lt, ← same]
      omega

/-- The consolidation churn of a state before Gloas is at most `C` of its total active balance.

It rounds the balance churn down to an increment, then takes off the activation and exit part.

`C` takes off the same part, but its balance churn rounds only the share. -/
theorem consolidationChurnLimit_le {f : Fork} {s : BeaconState preset f}
    (early : f < .glamsterdam) {total rate : Gwei} (read : getTotalActiveBalance s = .ok total)
    (computed : getConsolidationChurnLimit config s = .ok rate) :
    rate.toNat ≤ consolidationChurn preset config total.toNat := by
  have wholeOk : getBalanceChurnLimit config s = .ok (roundToIncrement preset
      (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA (total / config.CHURN_LIMIT_QUOTIENT))) := by
    simp [getBalanceChurnLimit, read, bind, Except.bind, pure, Except.pure]
  have exitOk : getActivationExitChurnLimit config s = .ok
      (min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT (roundToIncrement preset
        (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA (total / config.CHURN_LIMIT_QUOTIENT)))) := by
    simp [getActivationExitChurnLimit, wholeOk, bind, Except.bind, pure, Except.pure]
  have sum := getConsolidationChurnLimit_add early computed exitOk wholeOk
  rw [Uint64.toNat_min] at sum
  generalize hAmount : max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
    (total / config.CHURN_LIMIT_QUOTIENT) = amount at sum
  have value := congrArg UInt64.toNat hAmount
  rw [Uint64.toNat_max, UInt64.toNat_div] at value
  rw [toNat_roundToIncrement] at sum
  -- The rounded churn is at most the churn of the formula, which rounds only the share.
  have share := Nat.div_add_mod (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat)
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  have rounded : amount.toNat - amount.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      balanceChurn preset config total.toNat := by
    unfold balanceChurn
    rw [← value, Nat.mul_comm (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)]
    rcases Nat.le_total config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) with low | high
    · rw [Nat.max_eq_right low]
      omega
    · rw [Nat.max_eq_left high]
      omega
  unfold consolidationChurn activationExitChurn
  omega

/-- `C` does not decrease when the total active stake grows. -/
theorem consolidationChurn_mono {low high : Nat} (le : low ≤ high) :
    consolidationChurn preset config low ≤ consolidationChurn preset config high := by
  have churns : balanceChurn preset config low ≤ balanceChurn preset config high :=
    max_le_max_left _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right (Nat.div_le_div_right le)))
  unfold consolidationChurn activationExitChurn
  omega

/-- A delayed-slashing site keeps the withdrawal bound of a newly slashed Run prefix.

The epoch prefix starts after slot processing, which keeps the validator registry. -/
private theorem newly_slashed_epoch_prefix {x m : ForkedBeaconState preset}
    (pre : Run config checks x m) (caps : CapOrder preset) (early : m.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {s t : BeaconState preset m.fork}
    (same : s.validators = m.state.validators)
    (trace : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry] s t)
    (i : Nat) (v u w : Validator)
    (initial : x.state.validators.data[i]? = some v)
    (middle : m.state.validators.data[i]? = some u)
    (site : t.validators.data[i]? = some w)
    (unslashed : v.slashed = false) (slashed : u.slashed = true) :
    w.slashed = true ∧ w.exitEpoch = u.exitEpoch ∧
      (getCurrentEpoch x.state).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat := by
  have lower := pre.newly_slashed_withdrawableEpoch caps.activation caps.compounding early
    delay i v u initial middle unslashed slashed
  have located : s.validators.data[i]? = some u := by rwa [same]
  have kept := trace.slashed_withdrawableEpoch_mono i u w located site slashed lower.1
  exact ⟨kept.1, kept.2.1, lower.2.trans (UInt64.le_iff_toNat_le.mp kept.2.2)⟩

/-- A withdrawal bound excludes the delayed penalty throughout the short window. -/
private theorem newly_slashed_epoch_not_due (start epoch : Epoch) (w : Validator)
    (lower : start.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      w.withdrawableEpoch.toNat)
    (short : epoch.toNat < start.toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) :
    ¬ SlashingPenaltyDue preset epoch w := by
  intro due
  have equal := congrArg UInt64.toNat due.2
  rw [UInt64.toNat_add] at equal
  have bounded := Nat.mod_le (epoch.toNat +
    (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) (2 ^ 64)
  omega

/-- Per-key accounting retains gross routed debits and the high-water mark at its first slashing.

The high-water mark starts at the initial effective balance, independently of the allowance base. -/
structure FloorAccount where
  balance : Nat
  debt : Nat
  high : Nat
  slashedHigh : Option Nat

/-- An accounting trace classifies only the effects relevant to the per-key floor.

The event bridge supplies these cases from the actual replay and effective updates. -/
inductive FloorTrace (low base quotient : Nat) : FloorAccount → FloorAccount → Prop where
  | nil : FloorTrace low base quotient a a
  | credit : FloorTrace low base quotient a b → b.balance ≤ balance →
      FloorTrace low base quotient a { b with balance := balance }
  | debit : FloorTrace low base quotient a b → b.balance ≤ balance + debit →
      FloorTrace low base quotient a { b with balance := balance, debt := b.debt + debit }
  | sweep : FloorTrace low base quotient a b → max low b.high ≤ balance →
      FloorTrace low base quotient a { b with balance := balance }
  | update : FloorTrace low base quotient a b → effective ≤ b.balance →
      FloorTrace low base quotient a { b with high := max b.high effective }
  | slash : FloorTrace low base quotient a b → b.slashedHigh = none →
      b.balance ≤ balance + penalty → penalty ≤ base / quotient + (b.high - base) →
      FloorTrace low base quotient a { b with balance := balance, slashedHigh := some b.high }

/-- The delayed-slashing operation recorded by an epoch replay cannot debit a newly slashed key.

Its withdrawal bound comes from the Run prefix, transported through the actual registry stage. -/
private theorem epoch_delayed_slashing_nondebit {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m n)
    (caps : CapOrder preset) (early : n.fork < .glamsterdam) (holds : Invariant m.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {cached middle : BeaconState preset m.fork}
    (processed : epochBeforePayments config checks cached = .ok middle)
    {recorded events : List (BalanceEvent preset)}
    (epochReplay : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, recorded))
    (replayed : step.balanceEvents = .ok events) (included : recorded ⊆ events)
    (i : ValidatorIndex) (v u : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (located : m.state.validators.data[i.toNat]? = some u)
    (cachedOk : processSlot m.state = .ok cached)
    (assigned : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (start : (v.slashed = false ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∨
      (v.slashed = true ∧ (getCurrentEpoch m.state).toNat +
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat)) :
    ∀ event ∈ recorded, event.source = .slashings →
      actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat ∧
        event.after.state.validators.data = event.before.state.validators.data := by
  have same : cached.validators = m.state.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have sameEpoch : getCurrentEpoch cached = getCurrentEpoch m.state := by
    simp only [getCurrentEpoch, (frame_processSlot cachedOk).slot]
  obtain ⟨justified, scored, rewarded, registered, after, reset, deposited,
    rewards, limit, _, justifiedOk, scoredOk, rewardedOk, registeredOk,
    slashOk, _, _, _, rewardReplay, shape⟩ := funding_epoch_site processed epochReplay
  have quiet := replayRewards_induction
    (fun pre => ∀ e ∈ pre.2, e.source ≠ .slashings)
    (fun held ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · simp only [List.mem_singleton] at added
        subst e
        simp)
    (fun penalty held ok => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, _, _, rfl⟩ := ok
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact held e old
      · simp only [List.mem_singleton] at added
        subst e
        rcases penalty with rfl | rfl <;> simp)
    (by simp) rewardReplay
  -- The recorded operation starts at the endpoint of these four actual stages.
  have fixed : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry] cached registered :=
    .cons (EpochStage.action_cases.mpr justifiedOk) <|
      .cons (EpochStage.action_cases.mpr scoredOk) <|
      .cons (EpochStage.action_cases.mpr rewardedOk) <|
      .cons (EpochStage.action_cases.mpr registeredOk) .nil
  have one := justifiedOk.validators_eq ⟨nofun, nofun, nofun⟩
  have two := scoredOk.validators_eq ⟨nofun, nofun, nofun⟩
  have three := (EpochStage.action_cases.mp
    (show EpochStage.action config checks .rewards scored = .ok rewarded from rewardedOk)
      ).validators_eq ⟨nofun, nofun, nofun⟩
  have atRegistry : rewarded.validators.data[i.toNat]? = some u := by
    rw [three, two, one, same]; exact located
  obtain ⟨w, found, sameValidator⟩ :=
    (processRegistryUpdates_kept registeredOk).1 i.toNat u atRegistry
  have slot : registered.slot = cached.slot := by
    refine fixed.transport (fun a b => b.slot = a.slot) (fun _ => rfl)
      (fun {a b c} (one : b.slot = a.slot) (two : c.slot = b.slot) => two.trans one) ?_
    intro k member a b computed
    have edge := EpochStage.action_cases.mp computed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2
    · exact (edge.records ⟨nofun, nofun, nofun, nofun, nofun, nofun⟩).2.2.2.2
    · exact (frame_processRewardsAndPenalties edge).slot
    · exact (frame_processRegistryUpdates edge).slot
  have epoch : getCurrentEpoch registered = getCurrentEpoch m.state := by
    simpa only [getCurrentEpoch, slot] using sameEpoch
  let recordedSlash : BalanceEvent preset :=
    ⟨.slashings, ⟨m.fork, registered⟩, ⟨m.fork, after⟩, 0, limit⟩
  intro event member source
  have equal : event = recordedSlash := by
    rw [shape] at member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with (reward | slash) | pending
    · exact False.elim (quiet event reward source)
    · exact slash
    · split at pending
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at pending
        rcases pending with rfl | rfl <;> cases source
      · simp at pending
  subst event
  refine ⟨?_, congrArg (·.data) (EpochStage.Edge.validators_eq
    (config := config) (checks := checks) (stage := .slashings) slashOk ⟨nofun, nofun, nofun⟩)⟩
  have sites :=
    step.balanceEvents_sites early holds caps.compounding replayed recordedSlash (included member)
  cases slashed : u.slashed with
  | true =>
    rcases start with ⟨unslashed, short⟩ | ⟨vslashed, wait⟩
    · have kept := newly_slashed_epoch_prefix pre caps
        (Nat.lt_of_le_of_lt step.chainStep.fork_le early) delay same fixed
        i.toNat v u w initial located found unslashed slashed
      exact sites.2.2.2.2.2.1 rfl i w found kept.1
        (newly_slashed_epoch_not_due (getCurrentEpoch x.state)
          (getCurrentEpoch registered) w kept.2.2 (by rwa [epoch]))
    · -- A key slashed at the start keeps its slash and its withdrawable epoch.
      obtain ⟨flag, -, lower⟩ := Run.slashed_withdrawableEpoch_mono_epoch pre caps.activation
        caps.compounding (Nat.lt_of_le_of_lt step.chainStep.fork_le early) cachedOk fixed
        i.toNat v w initial found vslashed (assigned vslashed)
      refine sites.2.2.2.2.2.1 rfl i w found flag ?_
      intro due
      have equal := congrArg UInt64.toNat due.2
      rw [UInt64.toNat_add] at equal
      have bounded := Nat.mod_le (((getCurrentEpoch registered).toNat +
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat)) (2 ^ 64)
      have lowered := UInt64.le_iff_toNat_le.mp lower
      rw [epoch] at equal bounded
      omega
  | false =>
    have atStart : slashedFlag registered i = .ok false := by
      simp [slashedFlag, getValidator, found, Except.map, sameValidator.2.2.2, slashed]
    have atEnd : slashedFlag after i = .ok false := by
      have same := EpochStage.Edge.validators_eq (config := config) (checks := checks)
        (stage := .slashings) slashOk ⟨nofun, nofun, nofun⟩
      simpa only [slashedFlag, getValidator, same] using atStart
    simpa [recordedSlash, atEnd] using sites.1 rfl i
      (Array.getElem?_eq_some_iff.mp located).1 atStart

/-- Slot dispatch reads the actual epoch prefix exposed by the slot replay.

The key is unslashed at the start and the slot is within the short window of its slash.

Or it is slashed at the start, with an assigned exit, and its penalty is not due in this epoch. -/
private theorem slot_delayed_slashing_nondebit_general {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (ok : advanceSlotAcross config checks m = .ok n)
    (caps : CapOrder preset) (early : n.fork < .glamsterdam) (holds : Invariant m.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (i : ValidatorIndex) (v u : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (located : m.state.validators.data[i.toNat]? = some u)
    (assigned : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (start : (v.slashed = false ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∨
      (v.slashed = true ∧ (getCurrentEpoch m.state).toNat +
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat)) :
    ∀ event ∈ events, event.source = .slashings →
      actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat ∧
        event.after.state.validators.data = event.before.state.validators.data := by
  intro event member source
  obtain ⟨advanced, cached, crossings, _, _, cachedOk, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  rcases split with ⟨_, rfl⟩ |
    ⟨middle, _, recorded, recordedOk, _, _, _, shape, _, _, _, _, prefixOk⟩
  · have crossing := upgradeBalanceReplay_crossing crossingOk event member
    rw [crossing] at source
    cases source
  have included : event ∈ recorded := by
    rw [shape] at member
    rcases List.mem_append.mp member with recorded | crossing
    · exact recorded
    · have crossed := upgradeBalanceReplay_crossing crossingOk event crossing
      rw [crossed] at source
      cases source
  exact epoch_delayed_slashing_nondebit pre (.slot ok)
    caps early holds delay prefixOk recordedOk replayed
      (shape ▸ List.subset_append_left recorded crossings)
        i v u initial located cachedOk assigned start event included source

/-- Slot dispatch reads the actual epoch prefix exposed by the slot replay. -/
theorem slot_delayed_slashing_nondebit {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (ok : advanceSlotAcross config checks m = .ok n)
    (caps : CapOrder preset) (early : n.fork < .glamsterdam) (holds : Invariant m.state)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (i : ValidatorIndex) (v u : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (located : m.state.validators.data[i.toNat]? = some u)
    (unslashed : v.slashed = false)
    (short : (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) :
    ∀ event ∈ events, event.source = .slashings →
      actualBalanceAt event.before i.toNat ≤ actualBalanceAt event.after i.toNat ∧
        event.after.state.validators.data = event.before.state.validators.data :=
  slot_delayed_slashing_nondebit_general pre ok caps early holds delay replayed i v u initial
    located (fun slashed => absurd slashed (by simp [unslashed])) (.inl ⟨unslashed, short⟩)

/-- Gross penalty accounting also retains the net debit of each sync event. -/
def floorPenaltyDebit (i : Nat) (event : BalanceEvent preset) : Nat :=
  penaltyDebit i event + if event.source = .sync then
    actualBalanceAt event.before i - actualBalanceAt event.after i else 0

/-- Only payments from the pending-partial pass enter the withdrawal debit account. -/
def floorPartialDebit (i : ValidatorIndex) (event : BalanceEvent preset) : Nat :=
  if event.source = .withdrawals then
    if electra : .pectra ≤ event.before.fork then
      match getPendingPartialWithdrawals event.before.state electra
          (event.before.state.nextWithdrawalIndex (Nat.le_trans (by decide) electra)) #[] with
      | .ok (partials, _, _) => withdrawnFrom partials i
      | .error _ => 0
    else 0
  else 0

/-- Count recorded false-to-true changes, not a flag equivalence across unrecorded gaps. -/
def floorSlash (i : Nat) (event : BalanceEvent preset) : Bool :=
  decide (event.source = .slashings) &&
    !(event.before.state.validators.data[i]?.map (·.slashed)).getD true &&
    (event.after.state.validators.data[i]?.map (·.slashed)).getD false

/-- A step with no new slashing at an index has no replay event newly slashing that index. -/
theorem slashing_step_count_le {config : Config} {checks : SignatureChecks}
    {x y : ForkedBeaconState preset} (step : Step config checks x y)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) (i : Nat) :
    (events.countP fun e =>
      !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
        (e.after.state.validators.data[i]?.map (·.slashed)).getD false) ≤
      if !(x.state.validators.data[i]?.map (·.slashed)).getD false &&
          (y.state.validators.data[i]?.map (·.slashed)).getD false then 1 else 0 := by
  have sites := step.balanceEvents_sites early holds compounding replayed
  by_cases active : (!(x.state.validators.data[i]?.map (·.slashed)).getD false &&
      (y.state.validators.data[i]?.map (·.slashed)).getD false) = true
  · rw [ite_eq_left active]
    cases events with
    | nil => simp
    | cons e rest => exact (sites e (by simp)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
  · rw [ite_eq_right active]
    apply Nat.le_zero.mpr
    apply List.countP_eq_zero.mpr
    intro e member marked
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, first, _, last, _⟩ := sites e member
    have flags : (!(e.before.state.validators.data[i]?.map (·.slashed)).getD true) = true ∧
        (e.after.state.validators.data[i]?.map (·.slashed)).getD false = true := by
      simpa only [Bool.and_eq_true] using marked
    cases after : e.after.state.validators.data[i]? with
    | none => simp [after] at flags
    | some v =>
      have slashed : v.slashed = true := by simpa [after] using flags.2
      obtain ⟨w, final, flag⟩ := last i v after slashed
      have start : (x.state.validators.data[i]?.map (·.slashed)).getD false = false := by
        cases before : x.state.validators.data[i]? with
        | none => simp
        | some u =>
          cases was : u.slashed with
          | false => simp [was]
          | true =>
            obtain ⟨z, atEvent, was'⟩ := first i u before was
            simp [atEvent, was'] at flags
      exact active (by simp [start, final, flag])

/-- M1's occurrence count and persistence bound the charge by the endpoint slashed flag. -/
theorem floorSlash_step_bound {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : Nat) (v w : Validator) (initial : x.state.validators.data[i]? = some v)
    (final : y.state.validators.data[i]? = some w) :
    (if v.slashed then 1 else 0) + events.countP (floorSlash i) ≤
      if w.slashed then 1 else 0 := by
  have filtered := List.countP_mono_left (l := events) (p := floorSlash i)
    (q := fun e => !(e.before.state.validators.data[i]?.map (·.slashed)).getD true &&
      (e.after.state.validators.data[i]?.map (·.slashed)).getD false)
    (by
      intro event _ marked
      simp only [floorSlash, Bool.and_eq_true] at marked
      simp only [Bool.and_eq_true]
      exact ⟨marked.1.2, marked.2⟩)
  have counted := filtered.trans (slashing_step_count_le step early holds caps.compounding
    replayed i)
  simp only [initial, final, Option.map_some, Option.getD_some] at counted
  cases first : v.slashed with
  | true =>
    obtain ⟨last, read, flag⟩ := step.slashedPersistence i v initial first
    have same := Option.some.inj (read.symm.trans final)
    subst last
    simpa [first, flag] using counted
  | false =>
    simpa [first] using counted

/-- The occurrence budget supplies the first-slash side condition at each recorded event.

A slash recorded along the events marks the high-water mark of the account before them. -/
private theorem FloorTrace.events_general {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (i : ValidatorIndex)
    (events : List (BalanceEvent preset))
    (linked : events.IsChain (fun e e' =>
      actualBalanceAt e.after i.toNat = actualBalanceAt e'.before i.toNat))
    (start : ∀ e ∈ events.head?, b.balance = actualBalanceAt e.before i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) ≤ 1)
    (classify : ∀ e ∈ events, ∀ c, FloorTrace low base quotient a c →
      c.balance = actualBalanceAt e.before i.toNat →
      c.high = b.high →
      (floorSlash i.toNat e = true → c.slashedHigh = none) →
      ∃ d, FloorTrace low base quotient a d ∧
        d.balance = actualBalanceAt e.after i.toNat ∧
        d.debt = c.debt + floorPenaltyDebit i.toNat e + floorPartialDebit i e ∧
        d.high = c.high ∧ d.slashedHigh =
          if floorSlash i.toNat e then some c.high else c.slashedHigh) :
    ∃ last, FloorTrace low base quotient a last ∧
      (events = [] → last = b) ∧
      (∀ e ∈ events.getLast?, last.balance = actualBalanceAt e.after i.toNat) ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧ last.high = b.high ∧
      (if last.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) ∧
      ∀ h, last.slashedHigh = some h → b.slashedHigh = some h ∨ h = b.high := by
  induction events generalizing b with
  | nil => exact ⟨b, trace, fun _ => rfl, by simp, by simp, rfl, by simp, fun h hh => .inl hh⟩
  | cons e rest ih =>
    have first (marked : floorSlash i.toNat e = true) : b.slashedHigh = none := by
      cases flag : b.slashedHigh with
      | none => rfl
      | some h => simp [marked, flag] at budget
    obtain ⟨c, next, balance, debt, high, flag⟩ :=
      classify e (by simp) b trace (start e (by simp)) rfl first
    have count : (if c.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) +
          (if floorSlash i.toNat e then 1 else 0) := by
      by_cases marked : floorSlash i.toNat e = true
      · simp [flag, marked, first marked]
      · simp [flag, marked]
    have remaining : (if c.slashedHigh.isSome then 1 else 0) +
        rest.countP (floorSlash i.toNat) ≤ 1 := by
      rw [count]; simp only [List.countP_cons] at budget; omega
    obtain ⟨last, done, empty, finish, total, kept, used, marks⟩ := ih next linked.tail
      (fun e' member => balance.trans (linked.rel_head? member)) remaining
      (fun e' member d prior balance kept =>
        classify e' (by simp [member]) d prior balance (kept.trans high))
    refine ⟨last, done, nofun, ?_, ?_, kept.trans high, ?_, ?_⟩
    · cases rest with
      | nil => simpa [empty rfl] using balance
      | cons e' rest => simpa using finish
    · simp only [List.map_cons, List.sum_cons]; omega
    · rw [used, count, List.countP_cons]; omega
    · intro h hh
      rcases marks h hh with seen | top
      · rw [flag] at seen
        by_cases marked : floorSlash i.toNat e = true
        · rw [ite_eq_left marked] at seen
          exact .inr (Option.some.inj seen).symm
        · rw [ite_eq_right marked] at seen
          exact .inl seen
      · exact .inr (top.trans high)

/-- The occurrence budget supplies the first-slash side condition at each recorded event. -/
theorem FloorTrace.events {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (i : ValidatorIndex)
    (events : List (BalanceEvent preset))
    (linked : events.IsChain (fun e e' =>
      actualBalanceAt e.after i.toNat = actualBalanceAt e'.before i.toNat))
    (start : ∀ e ∈ events.head?, b.balance = actualBalanceAt e.before i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) ≤ 1)
    (classify : ∀ e ∈ events, ∀ c, FloorTrace low base quotient a c →
      c.balance = actualBalanceAt e.before i.toNat →
      c.high = b.high →
      (floorSlash i.toNat e = true → c.slashedHigh = none) →
      ∃ d, FloorTrace low base quotient a d ∧
        d.balance = actualBalanceAt e.after i.toNat ∧
        d.debt = c.debt + floorPenaltyDebit i.toNat e + floorPartialDebit i e ∧
        d.high = c.high ∧ d.slashedHigh =
          if floorSlash i.toNat e then some c.high else c.slashedHigh) :
    ∃ last, FloorTrace low base quotient a last ∧
      (events = [] → last = b) ∧
      (∀ e ∈ events.getLast?, last.balance = actualBalanceAt e.after i.toNat) ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧ last.high = b.high ∧
      (if last.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) := by
  obtain ⟨last, done, nil, finish, debt, kept, used, -⟩ :=
    trace.events_general i events linked start budget classify
  exact ⟨last, done, nil, finish, debt, kept, used⟩

/-- Every routed penalty debit pays for the actual loss at its event. -/
private theorem floorPenaltyDebit_covers (i : Nat) (event : BalanceEvent preset)
    (source : event.source = .penalties ∨ event.source = .inactivity ∨ event.source = .sync) :
    actualBalanceAt event.before i ≤ actualBalanceAt event.after i +
      floorPenaltyDebit i event := by
  unfold floorPenaltyDebit penaltyDebit
  rcases source with source | source | source <;> simp [source] <;> omega

/-- The mixed withdrawal event retains a capped floor after charging only pending payments. -/
private theorem floorPartialDebit_sweep {fork : Fork} {s : BeaconState preset fork}
    (early : fork < .glamsterdam) (capella : .shapella ≤ fork)
    (expected : ExpectedWithdrawals) (computed : getExpectedWithdrawals s capella = .ok expected)
    (event : BalanceEvent preset) (source : event.source = .withdrawals)
    (before : event.before = ⟨fork, s⟩)
    (paid : ∀ i : ValidatorIndex, actualBalanceAt event.after i.toNat =
      actualBalanceAt event.before i.toNat - withdrawnFrom expected.withdrawals i)
    (i : ValidatorIndex) (v : Validator) (found : s.validators.data[i.toNat]? = some v)
    (alive : getCurrentEpoch s < v.withdrawableEpoch) (matched : BalancesMatch s) :
    min (actualBalanceAt event.before i.toNat - floorPartialDebit i event)
        (withdrawalMaxEffectiveBalance preset fork v).toNat ≤
      actualBalanceAt event.after i.toNat := by
  rcases event with ⟨tag, start, finish, debit, credit⟩
  dsimp only at before
  subst start
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have insideBalance : i.toNat < s.balances.data.size := by rw [matched]; exact inside
  let balance := s.balances.data[i.toNat]
  have held : s.balances.data[i.toNat]? = some balance :=
    Array.getElem?_eq_some_iff.mpr ⟨insideBalance, rfl⟩
  obtain ⟨partials, next, partialOk, floor⟩ :=
    getExpectedWithdrawals_sweep_floor early computed found alive held
  have actual : actualBalanceAt ⟨fork, s⟩ i.toNat = balance.toNat := by
    simp [actualBalanceAt, held]
  have partialPaid : floorPartialDebit i ⟨tag, ⟨fork, s⟩, finish, debit, credit⟩ =
      withdrawnFrom partials i := by
    unfold floorPartialDebit
    dsimp only at source ⊢
    simp only [source, ↓reduceIte]
    by_cases electra : .pectra ≤ fork
    · simp only [electra, ↓reduceDIte] at partialOk ⊢
      rw [partialOk]
    · simp only [electra, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at partialOk
      simp [electra, ← partialOk.1, withdrawnFrom]
  rw [paid, actual, partialPaid]
  exact floor

/-- Pending payments are charged first; the ordinary sweep uses no debit allowance. -/
private theorem FloorTrace.withdrawal {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (balance pending cap : Nat)
    (retained : min (b.balance - pending) cap ≤ balance)
    (capped : max low b.high ≤ cap) :
    FloorTrace low base quotient a { b with balance := balance, debt := b.debt + pending } := by
  have paid : b.balance ≤ (b.balance - pending) + pending := by omega
  have charged := trace.debit paid
  by_cases enough : b.balance - pending ≤ balance
  · exact charged.credit enough
  · have floor : max low b.high ≤ balance := by omega
    exact charged.sweep floor

/-- A compounding switch spends no debit allowance when the high-water mark fits its old cap. -/
theorem FloorTrace.excess {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events) (source : event.source = .excess)
    (i : Nat) (v : Validator) (found : x.state.validators.data[i]? = some v)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt event.before i)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat) :
    FloorTrace low base quotient a { b with balance := actualBalanceAt event.after i } := by
  obtain ⟨_, _, excess, _⟩ :=
    step.balanceEvents_sites early holds caps.compounding replayed event member
  rcases excess source i with unchanged | ⟨paid, cap⟩
  · exact trace.credit (by omega)
  · have upper := UInt64.le_iff_toNat_le.mp (cap v found)
    by_cases enough : b.balance ≤ preset.MIN_ACTIVATION_BALANCE.toNat
    · exact trace.credit (by omega)
    · exact trace.sweep (by omega)

/-- An assigned exit is fixed; an unassigned exit is at least every later exit. -/
theorem floor_exit_le {v w : Validator} (kept : ValidatorLifecycle v w) :
    w.exitEpoch.toNat ≤ v.exitEpoch.toNat := by
  by_cases assigned : v.exitEpoch = FAR_FUTURE_EPOCH
  · rw [assigned]; exact Nat.le_of_lt_succ w.exitEpoch.toNat_lt
  · rw [kept.exitEpoch assigned]

/-- A recorded withdrawal event uses the actual header state and the final validator's exit. -/
private theorem withdrawal_site_floor {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events)
    (source : event.source = .withdrawals) (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (high : Nat) (epoch : (getCurrentEpoch event.before.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat ∨
      (high + 1 < v.withdrawableEpoch.toNat ∧
        0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)) :
    ∃ u, event.before.state.validators.data[i.toNat]? = some u ∧
      withdrawalMaxEffectiveBalance preset event.before.fork u =
        withdrawalMaxEffectiveBalance preset x.fork v ∧
      min (actualBalanceAt event.before i.toNat - floorPartialDebit i event)
        (withdrawalMaxEffectiveBalance preset event.before.fork u).toNat ≤
          actualBalanceAt event.after i.toNat := by
  obtain ⟨_, withdrawals, _, _, _, _, _, ordered, beforeLife, during, suffix, _⟩ :=
    step.balanceEvents_sites early holds caps.compounding replayed event member
  obtain ⟨u, found, _⟩ := beforeLife.validators i.toNat v initial
  have startSame : u = v := by
    obtain ⟨block, s, before, header, _⟩ := withdrawals source
    rw [before] at found
    obtain ⟨_, _, same⟩ := processBlockHeader_eq header
    rw [same] at found
    exact Option.some.inj (found.symm.trans initial)
  have waiting : getCurrentEpoch event.before.state < u.withdrawableEpoch := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rcases retained with old | ⟨start, _⟩
    · obtain ⟨last, lastFound, kept⟩ := (during.trans suffix).validators i.toNat u found
      have same : last = w := Option.some.inj (lastFound.symm.trans final)
      subst last
      have exitBound := floor_exit_le kept
      have order := UInt64.le_iff_toNat_le.mp (ordered u (Array.mem_of_getElem? found))
      omega
    · rw [startSame]
      omega
  have cap : withdrawalMaxEffectiveBalance preset event.before.fork u =
      withdrawalMaxEffectiveBalance preset x.fork v := by
    obtain ⟨block, s, before, _⟩ := withdrawals source
    simp only [startSame, before]
  refine ⟨u, found, cap, ?_⟩
  obtain ⟨block, s, before, header, unchanged | ⟨capella, expected, computed, paid⟩⟩ :=
    withdrawals source
  · have kept := unchanged i.toNat
    have below := Nat.min_le_left
      (actualBalanceAt event.before i.toNat - floorPartialDebit i event)
      (withdrawalMaxEffectiveBalance preset event.before.fork u).toNat
    omega
  · have headerFrame := frame_processBlockHeader header
    have matched := headerFrame.balancesMatch holds.balancesMatch
    have beforeEarly : x.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt step.chainStep.fork_le early
    rcases event with ⟨tag, start, finish, debit, credit⟩
    dsimp only at before
    subst start
    exact floorPartialDebit_sweep beforeEarly capella expected computed
      ⟨tag, ⟨x.fork, s⟩, finish, debit, credit⟩ source rfl paid i u found waiting matched

/-- The sweep reader pays only pending partials and keeps the trace's high-water mark. -/
private theorem FloorTrace.withdrawal_site {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events)
    (source : event.source = .withdrawals) (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (high : Nat) (epoch : (getCurrentEpoch event.before.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat ∨
      (high + 1 < v.withdrawableEpoch.toNat ∧ 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat))
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt event.before i.toNat)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat) :
    FloorTrace low base quotient a
      ⟨actualBalanceAt event.after i.toNat, b.debt + floorPartialDebit i event,
        b.high, b.slashedHigh⟩ := by
  obtain ⟨u, _, cap, floor⟩ := withdrawal_site_floor step caps early holds replayed
    event member source i v w initial final high epoch retained
  apply trace.withdrawal _ (floorPartialDebit i event)
    (withdrawalMaxEffectiveBalance preset event.before.fork u).toNat
  · simpa only [balance] using floor
  · simpa only [cap] using capped

/-- Non-slashing sites charge only routed penalties and pending partial payments. -/
private theorem FloorTrace.event {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (e : BalanceEvent preset) (member : e ∈ events)
    (ordinary : e.source ≠ .slashings) (noCrossing : e.source ≠ .crossing)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (high : Nat) (epoch : (getCurrentEpoch e.before.state).toNat ≤ high + 1)
    (pendingEpoch : e.source = .consolidations →
      (getCurrentEpoch e.before.state).toNat ≤ high)
    (retained : high + 1 < w.exitEpoch.toNat ∨
      (high + 1 < v.withdrawableEpoch.toNat ∧ 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat))
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt e.before i.toNat)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat) :
    FloorTrace low base quotient a
      ⟨actualBalanceAt e.after i.toNat,
        b.debt + floorPenaltyDebit i.toNat e + floorPartialDebit i e, b.high, b.slashedHigh⟩ := by
  have sites := step.balanceEvents_sites early holds caps.compounding replayed e member
  have inside := (Array.getElem?_eq_some_iff.mp initial).1
  have rise (paid : actualBalanceAt e.before i.toNat ≤ actualBalanceAt e.after i.toNat) :
      FloorTrace low base quotient a { b with balance := actualBalanceAt e.after i.toNat } :=
    trace.credit (by omega)
  have penalty (source : e.source = .penalties ∨ e.source = .inactivity ∨ e.source = .sync) :
      FloorTrace low base quotient a
        { b with balance := actualBalanceAt e.after i.toNat,
                 debt := b.debt + floorPenaltyDebit i.toNat e } :=
    trace.debit (by have paid := floorPenaltyDebit_covers i.toNat e source; omega)
  cases source : e.source with
  | slashings => exact False.elim (ordinary source)
  | crossing => exact False.elim (noCrossing source)
  | withdrawals =>
    simpa [floorPenaltyDebit, penaltyDebit, source] using
      trace.withdrawal_site step caps early holds replayed e member source i v w initial final
        high epoch retained balance capped
  | excess =>
    simpa [floorPenaltyDebit, penaltyDebit, floorPartialDebit, source] using
      trace.excess step caps early holds replayed e member source i.toNat v initial balance capped
  | penalties | inactivity | sync =>
    simpa [floorPartialDebit, source] using penalty (by simp [source])
  | rewards | deposits =>
    simpa [floorPenaltyDebit, penaltyDebit, floorPartialDebit, source] using
      rise (sites.2.2.2.1 (by simp [source]) i.toNat inside)
  | consolidations =>
    obtain ⟨_, _, _, _, consolidation, _, _, ordered, beforeLife, during, suffix, _⟩ := sites
    obtain ⟨u, found, _⟩ := beforeLife.validators i.toNat v initial
    have waiting : getCurrentEpoch e.before.state + 1 < u.withdrawableEpoch := by
      have atEpoch := pendingEpoch source
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [UInt64.toNat_add]
      simp only [UInt64.reduceToNat]
      refine (Nat.mod_le _ _).trans_lt ?_
      rcases retained with old | ⟨start, delay⟩
      · obtain ⟨z, located, kept⟩ := (during.trans suffix).validators i.toNat u found
        have same : z = w := Option.some.inj (located.symm.trans final)
        subst z
        have exitBound := floor_exit_le kept
        have order := UInt64.le_iff_toNat_le.mp (ordered u (Array.mem_of_getElem? found))
        omega
      · obtain ⟨z, read, arm⟩ := step.consolidation_withdrawable early holds delay replayed member
          source i.toNat v initial
        obtain rfl : z = u := Option.some.inj (read.symm.trans found)
        rcases arm with same | late
        · rw [same]
          omega
        · omega
    simpa [floorPenaltyDebit, penaltyDebit, floorPartialDebit, source] using
      rise (consolidation source i.toNat u found (.inr waiting))

/-- A step's existing occurrence bound and balance chain compose its classified sites.

A slash recorded along them marks the high-water mark of the account before them. -/
private theorem FloorTrace.step_events_general {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (high : Nat) (epochs : ∀ e ∈ events, (getCurrentEpoch e.before.state).toNat ≤ high + 1)
    (pendingEpochs : ∀ e ∈ events, e.source = .consolidations →
      (getCurrentEpoch e.before.state).toNat ≤ high)
    (retained : high + 1 < w.exitEpoch.toNat ∨
      (high + 1 < v.withdrawableEpoch.toNat ∧ 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat))
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {part : List (BalanceEvent preset)} (sublist : part.Sublist events)
    (linked : part.IsChain (fun e e' =>
      actualBalanceAt e.after i.toNat = actualBalanceAt e'.before i.toNat))
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (start : ∀ e ∈ part.head?, b.balance = actualBalanceAt e.before i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) +
      part.countP (floorSlash i.toNat) ≤ 1)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    (slash : ∀ e ∈ part, e.source = .slashings → ∀ c,
      FloorTrace low base quotient a c → c.balance = actualBalanceAt e.before i.toNat →
      c.high = b.high → (floorSlash i.toNat e = true → c.slashedHigh = none) →
      ∃ d, FloorTrace low base quotient a d ∧ d.balance = actualBalanceAt e.after i.toNat ∧
        d.debt = c.debt + floorPenaltyDebit i.toNat e + floorPartialDebit i e ∧
        d.high = c.high ∧ d.slashedHigh =
          if floorSlash i.toNat e then some c.high else c.slashedHigh) :
    ∃ last, FloorTrace low base quotient a last ∧
      (part = [] → last.balance = b.balance) ∧
      (∀ e ∈ part.getLast?, last.balance = actualBalanceAt e.after i.toNat) ∧
      last.debt = b.debt + (part.map (floorPenaltyDebit i.toNat)).sum +
        (part.map (floorPartialDebit i)).sum ∧ last.high = b.high ∧
      (if last.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + part.countP (floorSlash i.toNat) ∧
      ∀ h, last.slashedHigh = some h → b.slashedHigh = some h ∨ h = b.high := by
  have included := sublist.subset
  obtain ⟨last, done, nil, finish, debt, kept, used, marks⟩ :=
    (show FloorTrace low base quotient a b from trace).events_general i part linked start
      budget (fun e member c prior balance kept first => by
        by_cases source : e.source = .slashings
        · exact slash e member source c prior balance kept first
        · refine ⟨_, prior.event step caps early holds replayed e (included member) source
            (noCrossing e (included member)) i v w initial final high (epochs e (included member))
            (pendingEpochs e (included member)) retained balance ?_, rfl, rfl, rfl, ?_⟩
          · simpa only [kept] using capped
          · simp [floorSlash, source])
  exact ⟨last, done, fun h => congrArg FloorAccount.balance (nil h), finish, debt, kept, used,
    marks⟩

/-- A step's existing occurrence bound and balance chain compose its classified sites. -/
theorem FloorTrace.step_events {x y : ForkedBeaconState preset}
    (step : Step config checks x y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) (holds : Invariant x.state)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ValidatorIndex) (v w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (high : Nat) (epochs : ∀ e ∈ events, (getCurrentEpoch e.before.state).toNat ≤ high + 1)
    (pendingEpochs : ∀ e ∈ events, e.source = .consolidations →
      (getCurrentEpoch e.before.state).toNat ≤ high)
    (retained : high + 1 < w.exitEpoch.toNat)
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {part : List (BalanceEvent preset)} (sublist : part.Sublist events)
    (linked : part.IsChain (fun e e' =>
      actualBalanceAt e.after i.toNat = actualBalanceAt e'.before i.toNat))
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (start : ∀ e ∈ part.head?, b.balance = actualBalanceAt e.before i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) +
      part.countP (floorSlash i.toNat) ≤ 1)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    (slash : ∀ e ∈ part, e.source = .slashings → ∀ c,
      FloorTrace low base quotient a c → c.balance = actualBalanceAt e.before i.toNat →
      c.high = b.high → (floorSlash i.toNat e = true → c.slashedHigh = none) →
      ∃ d, FloorTrace low base quotient a d ∧ d.balance = actualBalanceAt e.after i.toNat ∧
        d.debt = c.debt + floorPenaltyDebit i.toNat e + floorPartialDebit i e ∧
        d.high = c.high ∧ d.slashedHigh =
          if floorSlash i.toNat e then some c.high else c.slashedHigh) :
    ∃ last, FloorTrace low base quotient a last ∧
      (part = [] → last.balance = b.balance) ∧
      (∀ e ∈ part.getLast?, last.balance = actualBalanceAt e.after i.toNat) ∧
      last.debt = b.debt + (part.map (floorPenaltyDebit i.toNat)).sum +
        (part.map (floorPartialDebit i)).sum ∧ last.high = b.high ∧
      (if last.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + part.countP (floorSlash i.toNat) := by
  obtain ⟨last, done, nil, finish, debt, kept, used, -⟩ :=
    trace.step_events_general step caps early holds replayed i v w initial final high epochs
      pendingEpochs (Or.inl retained) noCrossing sublist linked start budget capped slash
  exact ⟨last, done, nil, finish, debt, kept, used⟩

/-- Block slashings spend the allowance once, at the recorded change of the slashed flag. -/
private theorem FloorTrace.block_slashing {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (early : fork < .glamsterdam) (holds : Invariant s)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events) (source : event.source = .slashings)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (i : ValidatorIndex) (v : Validator) (found : event.before.state.validators.data[i.toNat]? =
      some v) (inside : i.toNat < s.validators.data.size)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt event.before i.toNat)
    (first : v.slashed = false → slashedFlag event.after.state i = .ok true →
      b.slashedHigh = none)
    (high : effectiveAt ⟨fork, s⟩ i.toNat ≤ b.high)
    (positive : 0 < quotient)
    (quotient_le : quotient ≤
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) :
    ∃ last, FloorTrace low base quotient a last ∧
      last.balance = actualBalanceAt event.after i.toNat ∧ last.debt = b.debt ∧
      last.high = b.high ∧
      last.slashedHigh = if v.slashed = false ∧ slashedFlag event.after.state i = .ok true
        then some b.high else b.slashedHigh := by
  have beforeFlag : slashedFlag event.before.state i = .ok v.slashed := by
    simp [slashedFlag, getValidator, found, Except.map]
  have sites := (Step.block engine signed due ok).balanceEvents_sites early holds compounding
    replayed event member
  have facts := sites
  obtain ⟨_, _, _, _, _, _, _, _, _, during, _, _, markedAfter, _⟩ :=
    facts
  obtain ⟨w, afterFound, _⟩ := during.validators i.toNat v found
  have afterFlag : slashedFlag event.after.state i = .ok w.slashed := by
    simp [slashedFlag, getValidator, afterFound, Except.map]
  by_cases marked : v.slashed = true
  · have paid := Step.block_balanceEvents_slashed_nondebit early
      replayed event member source i v found marked
    exact ⟨{ b with balance := actualBalanceAt event.after i.toNat },
      trace.credit (by omega), rfl, rfl, rfl, by simp [marked]⟩
  · have unmarked : v.slashed = false := Bool.eq_false_iff.mpr marked
    have paid := sites.1 source i inside
        (by simpa [unmarked] using beforeFlag)
    cases finalFlag : w.slashed with
    | false =>
      simp [afterFlag, finalFlag] at paid
      exact ⟨{ b with balance := actualBalanceAt event.after i.toNat },
        trace.credit (by omega), rfl, rfl, rfl, by simp [afterFlag, finalFlag]⟩
    | true =>
      simp only [afterFlag, finalFlag, ↓reduceIte] at paid
      let penalty := effectiveAt ⟨fork, s⟩ i.toNat /
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat
      have bounded : penalty ≤ base / quotient + (b.high - base) := by
        have one := Nat.div_le_div_left quotient_le positive
          (a := effectiveAt ⟨fork, s⟩ i.toNat)
        have two := Nat.div_le_div_right high (c := quotient)
        have three : b.high / quotient ≤ base / quotient + (b.high - base) := by
          have scaled : b.high - base ≤ quotient * (b.high - base) := by
            simpa using Nat.mul_le_mul_right (b.high - base) positive
          have upper : b.high ≤ base + quotient * (b.high - base) := by omega
          have bound := Nat.div_le_div_right upper (c := quotient)
          rwa [Nat.add_mul_div_left _ _ positive] at bound
        exact one.trans (two.trans three)
      exact ⟨⟨actualBalanceAt event.after i.toNat, b.debt, b.high, some b.high⟩,
        trace.slash (first unmarked (by simp [afterFlag, finalFlag]))
          (by simpa only [balance] using paid) bounded,
        rfl, rfl, rfl, by simp [unmarked, afterFlag, finalFlag]⟩

/-- The block handler reads the recorded operation and the fold's first-occurrence budget. -/
private theorem FloorTrace.block_event {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (early : fork < .glamsterdam) (holds : Invariant s) (caps : CapOrder preset)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (event : BalanceEvent preset) (member : event ∈ events) (source : event.source = .slashings)
    (i : ValidatorIndex) (v : Validator) (initial : s.validators.data[i.toNat]? = some v)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt event.before i.toNat)
    (first : floorSlash i.toNat event = true → b.slashedHigh = none)
    (high : effectiveAt ⟨fork, s⟩ i.toNat ≤ b.high) (positive : 0 < quotient)
    (quotient_le : quotient ≤
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) :
    ∃ last, FloorTrace low base quotient a last ∧
      last.balance = actualBalanceAt event.after i.toNat ∧
      last.debt = b.debt + floorPenaltyDebit i.toNat event + floorPartialDebit i event ∧
      last.high = b.high ∧ last.slashedHigh =
        if floorSlash i.toNat event then some b.high else b.slashedHigh := by
  have sites := (Step.block engine signed due ok).balanceEvents_sites early holds caps.compounding
    replayed event member
  obtain ⟨u, found, _⟩ := sites.2.2.2.2.2.2.2.2.1.validators i.toNat v initial
  obtain ⟨w, located, _⟩ := sites.2.2.2.2.2.2.2.2.2.1.validators i.toNat u found
  have flag : floorSlash i.toNat event =
      decide (u.slashed = false ∧ slashedFlag event.after.state i = .ok true) := by
    simp [floorSlash, source, found, slashedFlag, getValidator, located, Except.map]
  obtain ⟨last, done, balance, debt, high, marked⟩ := trace.block_slashing early holds replayed
    event member source caps.compounding i u found (Array.getElem?_eq_some_iff.mp initial).1
    balance (fun unmarked marked => first (by simp [flag, unmarked, marked])) high positive
    quotient_le
  refine ⟨last, done, balance, ?_, high, ?_⟩
  · simpa [floorPenaltyDebit, penaltyDebit, floorPartialDebit, source] using debt
  · simpa only [flag, decide_eq_true_eq] using marked

/-- A concrete block composes its operation sites with the carried occurrence account. -/
private theorem FloorTrace.block_step {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (early : fork < .glamsterdam) (holds : Invariant s) (caps : CapOrder preset)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (i : ValidatorIndex) (v w : Validator) (initial : s.validators.data[i.toNat]? = some v)
    (final : t.validators.data[i.toNat]? = some w) (high : Nat)
    (endEpoch : (getCurrentEpoch t).toNat ≤ high + 1) (retained : high + 1 < w.exitEpoch.toNat ∨
      (high + 1 < v.withdrawableEpoch.toNat ∧ 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat))
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt ⟨fork, s⟩ i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) +
      events.countP (floorSlash i.toNat) ≤ 1)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset fork v).toNat)
    (effective : effectiveAt ⟨fork, s⟩ i.toNat ≤ b.high) (positive : 0 < quotient)
    (quotient_le : quotient ≤
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) :
    ∃ last, FloorTrace low base quotient a last ∧
      last.balance = actualBalanceAt ⟨fork, t⟩ i.toNat ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧ last.high = b.high ∧
      (if last.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) ∧
      ∀ h, last.slashedHigh = some h → b.slashedHigh = some h ∨ h = b.high := by
  let step := Step.block engine signed due ok
  obtain ⟨p, first, second, path, split, empty, start, finish, linked,
    empty', start', finish', linked', _⟩ := step.balanceChain early replayed
  have point : p = ⟨fork, s⟩ := by
    simp only [step, Step.balancePath] at path
    rcases path with ⟨_, rfl⟩ | impossible
    · rfl
    · simp at impossible
  subst p
  have chain : events.IsChain (fun e e' =>
      actualBalanceAt e.after i.toNat = actualBalanceAt e'.before i.toNat) := by
    rw [split]
    exact (linked.imp (fun _ _ h => h i.toNat)).append
      (linked'.imp (fun _ _ h => h i.toNat))
      (fun e member e' member' => (finish e member i.toNat).trans
        (start' e' member' i.toNat).symm)
  have begins : ∀ e ∈ events.head?, b.balance = actualBalanceAt e.before i.toNat := by
    rw [split]
    cases first with
    | nil => simpa using fun e member => balance.trans (start' e member i.toNat).symm
    | cons e rest => simpa using balance.trans (start e (by simp) i.toNat).symm
  have ends : ∀ e ∈ events.getLast?,
      actualBalanceAt e.after i.toNat = actualBalanceAt ⟨fork, t⟩ i.toNat := by
    rw [split]
    cases second with
    | nil => simpa using fun e member => (finish e member i.toNat).trans (empty' rfl i.toNat).symm
    | cons e rest => simpa using fun e member => finish' e member i.toNat
  have emptyAll (nil : events = []) :
      actualBalanceAt ⟨fork, t⟩ i.toNat = actualBalanceAt ⟨fork, s⟩ i.toNat := by
    rw [nil, List.nil_eq_append_iff] at split
    exact (empty' split.2 i.toNat).trans (empty split.1 i.toNat)
  have facts := step.balanceEvents_sites early holds caps.compounding replayed
  obtain ⟨last, done, nil, finish, debt, kept, used, marks⟩ :=
    trace.step_events_general step caps early holds
    replayed i v w initial final high
    (fun e member => (facts e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans endEpoch)
    (fun e member pending => by
      have bound := (facts e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 pending
      dsimp only at bound
      omega) retained
    (fun e member crossing => by
      have bound := (facts e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 crossing
      obtain ⟨before, after⟩ := bound
      dsimp only at before after
      exact Nat.not_le_of_lt before after)
    (List.Sublist.refl events) chain begins budget capped
    (fun e member source c prior balance kept first =>
      prior.block_event early holds caps replayed e member source i v initial balance first
        (by simpa only [kept] using effective) positive quotient_le)
  refine ⟨last, done, ?_, debt, kept, used, marks⟩
  cases events with
  | nil => exact (nil rfl).trans (balance.trans (emptyAll rfl).symm)
  | cons e rest =>
    have found : (e :: rest).getLast? = some ((e :: rest).getLast (by simp)) :=
      List.getLast?_eq_some_getLast (by simp)
    exact (finish _ found).trans (ends _ found)

/-- The existing slot upper bound raises the account only at its actual backing-balance point. -/
private theorem FloorTrace.slot_update {fork : Fork} {s t : BeaconState preset fork}
    (computed : advanceSlot config checks s = .ok t) (i : Nat)
    (inside : i < s.validators.data.size)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt ⟨fork, t⟩ i)
    (high : effectiveAt ⟨fork, s⟩ i ≤ b.high) :
    ∃ last, FloorTrace low base quotient a last ∧ last.balance = b.balance ∧
      last.debt = b.debt ∧ last.slashedHigh = b.slashedHigh ∧
      last.high = max b.high (effectiveAt ⟨fork, t⟩ i) := by
  have bound := balanceDrift_slot_upper computed i inside
  by_cases unchanged : effectiveAt ⟨fork, t⟩ i ≤ b.high
  · exact ⟨b, trace, rfl, rfl, rfl, (Nat.max_eq_left unchanged).symm⟩
  · refine ⟨{ b with high := max b.high (effectiveAt ⟨fork, t⟩ i) },
      trace.update ?_, rfl, rfl, rfl, rfl⟩
    rw [balance]
    omega

/-- Between the first fork of Fulu and Gloas, the upgrades leave the state as it is. -/
theorem processUpgrades_eq_of_window {z z' : ForkedBeaconState preset}
    (ok : processUpgrades config checks z = .ok z') (fulu : .fusaka ≤ z.fork)
    (early : z'.fork < .glamsterdam) : z' = z := by
  have stays : z'.fork ≤ z.fork := by
    rw [processUpgrades] at ok
    split at ok
    · obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
      have later := processUpgrades_fork_le rest
      have reached : Fork.glamsterdam ≤ next.val.fork := by
        obtain ⟨fork, state⟩ := z
        cases fork <;> dsimp only at fulu <;>
          first
            | exact absurd fulu (by decide)
            | (simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
                throwThe, MonadExceptOf.throw, reduceCtorEq] at nextOk
               -- The simp closes some cases itself, and then no goal is left.
               first
                 | done
                 | (obtain ⟨_, -, rfl⟩ := nextOk; exact Nat.le_refl _)
                 | (obtain ⟨_, -, rfl⟩ := nextOk
                    exact Nat.le_of_lt (by decide : Fork.glamsterdam < Fork.hegota)))
      exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans reached later) early) (Nat.lt_irrefl _)
    · cases ok
      exact Nat.le_refl _
  exact processUpgrades_eq_of_fork_le ok stays

/-- Upgrades keep the effective balance of an activated key, or of any key from Fulu.

The reachable cap covers its high. -/
private theorem FloorTrace.slot_transport {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (ok : advanceSlotAcross config checks x = .ok y) (caps : CapOrder preset)
    (early : y.fork < .glamsterdam) {advanced : BeaconState preset x.fork}
    (advanceOk : advanceSlot config checks x.state = .ok advanced)
    (upgrades : processUpgrades config checks ⟨x.fork, advanced⟩ = .ok y)
    (i : Nat) (v w : Validator) (initial : x.state.validators.data[i]? = some v)
    (final : y.state.validators.data[i]? = some w)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ .fusaka ≤ x.fork)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt ⟨x.fork, advanced⟩ i)
    (high : effectiveAt x i ≤ b.high)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat) :
    ∃ last, FloorTrace low base quotient a last ∧ last.balance = b.balance ∧
      last.debt = b.debt ∧ last.slashedHigh = b.slashedHigh ∧
      effectiveAt y i ≤ last.high ∧
      max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
      last.high = max b.high (effectiveAt y i) := by
  obtain ⟨u, found, life⟩ := (registryLifecycle_advanceSlot advanceOk).validators i v initial
  have kept : effectiveAt y i = effectiveAt ⟨x.fork, advanced⟩ i := by
    rcases activated with activated | fulu
    · exact balanceDrift_upgrades_active upgrades early i u found
        (by rwa [life.activationEpoch activated])
    · rw [processUpgrades_eq_of_window upgrades fulu early]
  obtain ⟨last, done, balance, debt, slashed, raised⟩ := trace.slot_update advanceOk i
    (Array.getElem?_eq_some_iff.mp initial).1 balance high
  have tail : Run config checks x y := Run.nil.snoc (.slot ok)
  obtain ⟨z, located, mono⟩ := tail.validatorCap_mono caps.activation caps.compounding
    early i v initial
  have equal := Option.some.inj (located.symm.trans final)
  subst z
  have endpoint := (shared.append tail).effectiveBalance_capped genesis caps.activation
    caps.compounding early w (Array.mem_of_getElem? final)
  have old := capped.trans (UInt64.le_iff_toNat_le.mp mono)
  have current : effectiveAt y i ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat := by
    simpa [effectiveAt, final] using UInt64.le_iff_toNat_le.mp endpoint
  refine ⟨last, done, balance, debt, slashed, ?_, ?_, ?_⟩
  · rw [raised, ← kept]
    exact Nat.le_max_right _ _
  · rw [raised, ← kept]
    omega
  · rw [raised, ← kept]

/-- A slot folds its epoch sites before updating the backed high-water mark. -/
private theorem FloorTrace.slot_step {g x m y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (ok : advanceSlotAcross config checks m = .ok y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (middle : m.state.validators.data[i.toNat]? = some u)
    (final : y.state.validators.data[i.toNat]? = some w)
    (assigned : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (activated : u.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ .fusaka ≤ m.fork)
    (window : (v.slashed = false ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∨
      (v.slashed = true ∧ (getCurrentEpoch m.state).toNat +
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat))
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat ∨
      (high + 1 < u.withdrawableEpoch.toNat ∧ 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat))
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt m i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) +
      events.countP (floorSlash i.toNat) ≤ 1)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset m.fork u).toNat)
    (effective : effectiveAt m i.toNat ≤ b.high) :
    ∃ before last, FloorTrace low base quotient a before ∧
      FloorTrace low base quotient a last ∧
      (∃ advanced, advanceSlot config checks m.state = .ok advanced ∧
        before.balance = actualBalanceAt ⟨m.fork, advanced⟩ i.toNat) ∧
      last.balance = actualBalanceAt y i.toNat ∧ before.debt = last.debt ∧
      before.slashedHigh = last.slashedHigh ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
      (if last.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) ∧
      last.high = max b.high (effectiveAt y i.toNat) ∧
      ∀ h, last.slashedHigh = some h → b.slashedHigh = some h ∨ h = b.high := by
  let step := Step.slot ok
  have holds := (run_justified_separated (shared.append pre) genesis).1
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨p, first, second, path, split, empty, start, ends, linked,
    empty', _, _, _, crossed⟩ := step.balanceChain early replayed
  have pathEq : step.balancePath = [m, ⟨m.fork, advanced⟩, y] := by
    simp [step, Step.balancePath, advanceOk, Except.toOption]
  have point : p = ⟨m.fork, advanced⟩ := by
    rw [pathEq] at path
    rcases path with ⟨impossible, _⟩ | same
    · simp at impossible
    · simpa using same.symm
  subst p
  have none : second = [] := List.eq_nil_iff_forall_not_mem.mpr (fun e member =>
    noCrossing e (split ▸ List.mem_append_right first member) (crossed pathEq e member))
  subst second
  simp only [List.append_nil] at split
  subst first
  have sites := step.balanceEvents_sites early holds caps.compounding replayed
  have slash := slot_delayed_slashing_nondebit_general pre ok caps early holds delay replayed
    i v u initial middle assigned window
  obtain ⟨before, folded, nil, finish, debt, kept, used, marks⟩ :=
    trace.step_events_general step caps early
    holds replayed i u w middle final high
    (fun e member => (sites e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans endEpoch)
    (fun e member pending => by
      have bound := (sites e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 pending
      omega) retained noCrossing (List.Sublist.refl events)
    (linked.imp (fun _ _ h => h i.toNat))
    (fun e member => balance.trans (start e member i.toNat).symm) budget capped
    (fun e member source c prior balance _ _ => by
      obtain ⟨paid, validators⟩ := slash e member source
      have zero : floorSlash i.toNat e = false := by
        simp only [floorSlash, validators]
        cases found : e.before.state.validators.data[i.toNat]? with
        | none => simp
        | some z => cases z.slashed <;> simp
      exact ⟨{ c with balance := actualBalanceAt e.after i.toNat },
        prior.credit (by omega), rfl, by simp [floorPenaltyDebit, penaltyDebit,
          floorPartialDebit, source], rfl, by simp [zero]⟩)
  have atBefore : before.balance = actualBalanceAt ⟨m.fork, advanced⟩ i.toNat := by
    cases events with
    | nil => exact (nil rfl).trans (balance.trans (empty rfl i.toNat).symm)
    | cons e rest =>
      have found := List.getLast?_eq_some_getLast (l := e :: rest) (by simp)
      exact (finish _ found).trans (ends _ found i.toNat)
  obtain ⟨last, done, atLast, lastDebt, flag, effective, cap, lastHigh⟩ := folded.slot_transport
    (shared.append pre) genesis ok caps early advanceOk upgrades i.toNat u w middle final
      activated atBefore (by simpa only [kept] using effective)
      (by simpa only [kept] using capped)
  exact ⟨before, last, folded, done, ⟨advanced, advanceOk, atBefore⟩,
    atLast.trans (atBefore.trans (empty' rfl i.toNat).symm), lastDebt.symm,
    flag.symm, lastDebt.trans debt, effective, cap, by simpa only [flag] using used,
    by rw [lastHigh, kept], fun h hh => marks h (flag.symm.trans hh)⟩

/-- One step of the floor trace, guarded by the final key's exit or its start withdrawable epoch. -/
theorem FloorTrace.step_general_or_fulu {g x m y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (step : Step config checks m y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (middle : m.state.validators.data[i.toNat]? = some u)
    (final : y.state.validators.data[i.toNat]? = some w)
    (assigned : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (activated : u.activationEpoch ≠ FAR_FUTURE_EPOCH ∨ .fusaka ≤ m.fork)
    (window : (v.slashed = false ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∨
      (v.slashed = true ∧ (getCurrentEpoch m.state).toNat +
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat))
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat ∨ high + 1 < u.withdrawableEpoch.toNat)
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt m i.toNat)
    (consumed : (if b.slashedHigh.isSome then 1 else 0) ≤ if u.slashed then 1 else 0)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset m.fork u).toNat)
    (effective : effectiveAt m i.toNat ≤ b.high) (positive : 0 < quotient)
    (quotient_le : quotient ≤
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) :
    ∃ last, FloorTrace low base quotient a last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
      (if last.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) ∧
      (∀ p ∈ step.balancePath, ∃ c, FloorTrace low base quotient a c ∧
        c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧
        (if c.slashedHigh.isSome then 1 else 0) ≤ (if last.slashedHigh.isSome then 1 else 0)) ∧
      last.high ≤ max b.high (effectiveAt y i.toNat) ∧
      (∀ h, last.slashedHigh = some h → b.slashedHigh = some h ∨ h = b.high) ∧
      (u.slashed = true → b.slashedHigh = none → last.slashedHigh = none) := by
  have holds := (run_justified_separated (shared.append pre) genesis).1
  have count := floorSlash_step_bound step caps early holds replayed i.toNat u w middle final
  have noNew : u.slashed = true → events.countP (floorSlash i.toNat) = 0 := fun slashed =>
    List.countP_eq_zero.mpr fun e member => by
      have sites := step.balanceEvents_sites early holds caps.compounding replayed e member
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, first, _⟩ := sites
      obtain ⟨z, atEvent, was⟩ := first i.toNat u middle slashed
      simp [floorSlash, atEvent, was]
  have budget : (if b.slashedHigh.isSome then 1 else 0) +
      events.countP (floorSlash i.toNat) ≤ 1 := by
    have bound : (if w.slashed then 1 else 0) ≤ (1 : Nat) := by split <;> omega
    omega
  cases step with
  | @block fork s t engine signed due ok =>
    obtain ⟨last, done, balance', debt, kept, used, marks⟩ := trace.block_step early holds caps
      replayed i u w middle final high endEpoch
        (retained.imp_right (fun r => ⟨r, delay⟩)) balance budget capped effective
        positive quotient_le
    have tail : Run config checks ⟨fork, s⟩ ⟨fork, t⟩ := .snoc .nil (.block engine signed due ok)
    obtain ⟨z, located, mono⟩ := tail.validatorCap_mono caps.activation caps.compounding
      early i.toNat u middle
    have same := Option.some.inj (located.symm.trans final)
    subst z
    refine ⟨last, done, balance', debt, ?_, ?_, by omega, ?_, ?_, marks, ?_⟩
    · rw [kept, effectiveKept_processBlock (applySignedBlock_ok ok).2.1 i.toNat
        (Array.getElem?_eq_some_iff.mp middle).1]
      exact effective
    · rw [kept]; exact capped.trans (UInt64.le_iff_toNat_le.mp mono)
    · intro p member
      simp only [Step.balancePath, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨b, trace, balance, by omega, by omega⟩
      · exact ⟨last, done, balance', le_rfl, le_rfl⟩
    · rw [kept]
      exact Nat.le_max_left _ _
    · intro slashed noFlag
      cases flagLast : last.slashedHigh with
      | none => rfl
      | some _ => simp [flagLast, noFlag, noNew slashed] at used
  | slot ok =>
    obtain ⟨before, last, folded, done, ⟨advanced, advanceOk, atBefore⟩,
      balance', sameDebt, sameFlag, debt, effective, cap, used, raised, marks⟩ :=
      trace.slot_step shared pre genesis caps ok early delay replayed i v u w initial middle
        final assigned activated window high endEpoch
        (retained.imp_right (fun r => ⟨r, delay⟩)) noCrossing balance budget capped
        effective
    refine ⟨last, done, balance', debt, effective, cap, by omega, ?_, raised.le, marks, ?_⟩
    swap
    · intro slashed noFlag
      cases flagLast : last.slashedHigh with
      | none => rfl
      | some _ => simp [flagLast, noFlag, noNew slashed] at used
    intro p member
    simp only [Step.balancePath, advanceOk, Except.toOption, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨b, trace, balance, by omega, by omega⟩
    · exact ⟨before, folded, atBefore, by omega, by rw [sameFlag]⟩
    · exact ⟨last, done, balance', le_rfl, le_rfl⟩

/-- Concrete Steps preserve the carried account and cover each balance-path point.

The key is unslashed at the start of the run and within the short window of a slash.

Or it is slashed at the start with an assigned exit.

Then its delayed penalty is not due in the epoch of the step.

The high-water mark of the carried account rises at most to the effective balance after the step. -/
private theorem FloorTrace.step_general {g x m y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (step : Step config checks m y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (middle : m.state.validators.data[i.toNat]? = some u)
    (final : y.state.validators.data[i.toNat]? = some w)
    (assigned : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (activated : u.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (window : (v.slashed = false ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∨
      (v.slashed = true ∧ (getCurrentEpoch m.state).toNat +
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat))
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat)
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt m i.toNat)
    (consumed : (if b.slashedHigh.isSome then 1 else 0) ≤ if u.slashed then 1 else 0)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset m.fork u).toNat)
    (effective : effectiveAt m i.toNat ≤ b.high) (positive : 0 < quotient)
    (quotient_le : quotient ≤
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) :
    ∃ last, FloorTrace low base quotient a last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
      (if last.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) ∧
      (∀ p ∈ step.balancePath, ∃ c, FloorTrace low base quotient a c ∧
        c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧
        (if c.slashedHigh.isSome then 1 else 0) ≤ (if last.slashedHigh.isSome then 1 else 0)) ∧
      last.high ≤ max b.high (effectiveAt y i.toNat) ∧
      (∀ h, last.slashedHigh = some h → b.slashedHigh = some h ∨ h = b.high) ∧
      (u.slashed = true → b.slashedHigh = none → last.slashedHigh = none) :=
  FloorTrace.step_general_or_fulu shared pre genesis caps step early delay replayed i v u w initial
    middle final assigned (Or.inl activated) window high endEpoch (Or.inl retained) noCrossing trace
    balance
    consumed capped effective positive quotient_le

/-- Concrete Steps preserve the carried account and cover each balance-path point. -/
theorem FloorTrace.step {g x m y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (step : Step config checks m y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (middle : m.state.validators.data[i.toNat]? = some u)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (activated : u.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (short : (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat)
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt m i.toNat)
    (consumed : (if b.slashedHigh.isSome then 1 else 0) ≤ if u.slashed then 1 else 0)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset m.fork u).toNat)
    (effective : effectiveAt m i.toNat ≤ b.high) (positive : 0 < quotient)
    (quotient_le : quotient ≤
      (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) :
    ∃ last, FloorTrace low base quotient a last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
      (if last.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) ∧
      ∀ p ∈ step.balancePath, ∃ c, FloorTrace low base quotient a c ∧
        c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧
        (if c.slashedHigh.isSome then 1 else 0) ≤ (if last.slashedHigh.isSome then 1 else 0) := by
  obtain ⟨last, done, balance', debt, effective', cap, used, path, -, -, -⟩ :=
    trace.step_general shared pre genesis caps step early delay replayed i v u w initial middle
      final (fun slashed => absurd slashed (by simp [unslashed])) activated
      (.inl ⟨unslashed, short⟩) high endEpoch retained noCrossing balance consumed capped effective
      positive quotient_le
  exact ⟨last, done, balance', debt, effective', cap, used, path⟩

/-- The numeric guard keeps every bounded reachable endpoint in the starting fork regime. -/
theorem guarded_fork_regime {g x y : ForkedBeaconState preset}
    (reached : Run config checks g y)
    (genesis : Genesis (config := config) (checks := checks) g)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high) :
    ((0 < preElectraEpochs config x high) ↔ x.fork < .pectra) ∧
      (.pectra ≤ x.fork ∨ y.fork < .pectra) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, crossing⟩ := guard
  have forks : (0 < preElectraEpochs config x high) ↔ x.fork < .pectra := by
    by_cases before : x.fork < .pectra
    · simp only [before, iff_true]
      unfold preElectraEpochs
      simp only [before, ↓reduceIte]
      split_ifs <;> omega
    · simp [preElectraEpochs, before]
  refine ⟨forks, ?_⟩
  by_cases electra : .pectra ≤ x.fork
  · exact .inl electra
  · right
    have before := Nat.lt_of_not_ge electra
    have ends := crossing.resolve_left (Nat.ne_of_gt (forks.mpr before))
    have late : high + 1 < config.ELECTRA_FORK_EPOCH.toNat := by
      simp only [preElectraEpochs, driftHorizon] at ends
      split_ifs at ends <;> omega
    apply Nat.lt_of_not_ge
    intro electraY
    have epoch := reachable_electra_epoch reached genesis electraY
    omega

end

end EthLib.Consensus.DirectSafety.Apriori.Internal

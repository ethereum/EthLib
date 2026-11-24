module

public import EthLib.Consensus.Proofs.Transition.BalanceCappedBlock
public import EthLib.Consensus.Proofs.Transition.InactivityLeakRun
public import EthLib.Consensus.Proofs.Transition.InactivityLeakVoter
import EthLib.Base.Proofs.Nat

/-!
# Proofs: the voters of a leak keep a stake read at the start of the run

The bound on an inactivity leak compares the stake of the absent validators with that of the voters.

This module states that bound with the stake of the voters read at the start of the run.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- The lesser of a balance and a cap, rounded down to a whole number of increments. -/
def cappedFloor (preset : Preset) (cap balance : Gwei) : Nat :=
  (min balance cap).toNat - (min balance cap).toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat

/-- An updated effective balance is at least the old one or the rounded capped balance.

The cap is the largest effective balance that the update takes. -/
theorem min_le_updatedEffectiveBalance {cap balance effective updated : Gwei}
    (computed : updatedEffectiveBalance preset cap balance effective = .ok updated) :
    min effective.toNat (cappedFloor preset cap balance) ≤ updated.toNat := by
  -- The effective balance stays, or becomes its rounded balance, at most its cap.
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact Nat.min_le_left _ _
  refine Nat.le_trans (Nat.min_le_right _ _) ?_
  rw [cappedFloor, Uint64.toNat_min, Uint64.toNat_min, toNat_rounded]
  exact Nat.le_min.mpr ⟨rounded_mono _ (Nat.min_le_left _ _),
    Nat.le_trans (Nat.sub_le _ _) (Nat.min_le_right _ _)⟩

/-- A larger capped balance stays at least as large once rounded down to an increment. -/
theorem cappedFloor_mono {cap low high : Gwei} (le : min low cap ≤ min high cap) :
    cappedFloor preset cap low ≤ cappedFloor preset cap high :=
  rounded_mono _ (UInt64.le_iff_toNat_le.mp le)

/-- A run of a leak keeps the effective balance of a voter above a bound read at the start.

This holds from Altair.

Each epoch transition starts in a leak, with the voter unslashed and voting when eligible. -/
theorem effectiveBalance_ge_of_voterRun (altair : .altair ≤ fork)
    -- The run visits a state before each of its epoch transitions.
    {states slotted : Nat → BeaconState preset fork} {epochs index : Nat}
    {key : Cryptography.Bls.BLSPubkey}
    -- The slot that leaves each such state ends an epoch.
    (ends : ∀ t < epochs, ((states t).slot + 1) % preset.SLOTS_PER_EPOCH = 0)
    -- That slot leads to a second state.
    (epochSlot : ∀ t < epochs, advanceSlot config checks (states t) = .ok (slotted t))
    -- Between them the voter takes only steps that cannot lower the lesser of its balance and cap.
    (steps : ∀ t < epochs,
      Relation.ReflTransGen (VoterStep config checks index key) (slotted t) (states (t + 1)))
    -- The registry stays within its limit.
    (within : ∀ t < epochs, (states t).RegistryWithinLimit)
    -- Each epoch transition starts in a leak.
    (leak : ∀ t < epochs, isInInactivityLeak (states t) = .ok true)
    -- Each epoch transition does not raise the finalized epoch.
    (stalled : ∀ t < epochs,
      (slotted t).finalizedCheckpoint.epoch ≤ (states t).finalizedCheckpoint.epoch)
    -- At each visited state the voter is unslashed.
    (unslashed : ∀ t < epochs, ∀ validator,
      (states t).validators.data[index]? = some validator → validator.slashed = false)
    -- Suppose it is eligible at a visited state.
    --
    -- Then its flags of the previous epoch there have the timely source and target.
    (voted : ∀ t < epochs, ∀ validator,
      (states t).validators.data[index]? = some validator →
        isEligibleValidator (getPreviousEpoch (states t)) validator = .ok true →
        ∃ flags, ((states t).previousEpochParticipation altair).data[index]? = some flags ∧
          hasFlag flags TIMELY_SOURCE_FLAG_INDEX = true ∧
          hasFlag flags TIMELY_TARGET_FLAG_INDEX = true)
    -- At each visited state, no pending consolidation has it as its source.
    (unsourced : ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ ((states t).pendingConsolidations electra).data,
        consolidation.sourceIndex.toNat ≠ index)
    {validator : Validator} (found : (states 0).validators.data[index]? = some validator)
    -- The key is that of the voter at the start of the run.
    (keyed : validator.pubkey = key)
    {balance : Gwei} (held : (states 0).balances.data[index]? = some balance) :
    -- Then at the end of the run the voter keeps its position.
    ∃ now, (states epochs).validators.data[index]? = some now ∧
      -- The capped balance is the lesser of the balance and the largest effective balance.
      --
      -- Its effective balance is at least its starting one or its starting rounded capped balance.
      --
      -- The cap there is its largest effective balance at the start.
      min validator.effectiveBalance.toNat
        (cappedFloor preset (withdrawalMaxEffectiveBalance preset fork validator) balance) ≤
        now.effectiveBalance.toNat := by
  -- The stake of a voter is its effective balance, so it changes only at the epoch transitions.
  --
  -- Along the run the voter keeps its key and cap, its capped balance does not fall.
  have kept : ∀ t ≤ epochs, ∃ current later,
      (states t).validators.data[index]? = some current ∧ current.pubkey = key ∧
      withdrawalMaxEffectiveBalance preset fork current =
        withdrawalMaxEffectiveBalance preset fork validator ∧
      (states t).balances.data[index]? = some later ∧
      (min balance (withdrawalMaxEffectiveBalance preset fork validator)).toNat ≤
        (min later (withdrawalMaxEffectiveBalance preset fork validator)).toNat ∧
      min validator.effectiveBalance.toNat
        (cappedFloor preset (withdrawalMaxEffectiveBalance preset fork validator) balance) ≤
        current.effectiveBalance.toNat := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨validator, balance, found, keyed, rfl, held, Nat.le_refl _,
        Nat.min_le_left _ _⟩
    | succ t step =>
      intro bound
      have during : t < epochs := by omega
      obtain ⟨current, later, atCurrent, currentKey, currentCap, atLater, capLow, effectiveLow⟩ :=
        step (by omega)
      obtain ⟨before, settled, effective, now, atBefore, atSettled, raised, effectiveOk, atNow,
        nowEffective, nowKey, nowCredentials⟩ :=
        voterEpoch_advanceSlot altair (epochSlot t during) (ends t during) (within t during)
          (leak t during) (stalled t during) atCurrent (unslashed t during current atCurrent)
          (voted t during current atCurrent) (unsourced t during)
      rw [atLater, Option.some.injEq] at atBefore
      subst atBefore
      -- Between epoch transitions, the steps of a voter do not lower its capped balance.
      obtain ⟨final, atFinal, finalKey, finalEffective, finalCap, capped⟩ :=
        voterSteps_kept (steps t during) atNow (nowKey.trans currentKey)
      have nowCap := (withdrawalMaxEffectiveBalance_of_credentials (preset := preset)
        (fork := fork) nowCredentials).trans currentCap
      rw [nowCap] at capped finalCap
      rw [currentCap] at effectiveOk
      obtain ⟨last, atLast, settledLow⟩ := capped settled atSettled
      have settledNat := UInt64.le_iff_toNat_le.mp settledLow
      have raisedNat := UInt64.le_iff_toNat_le.mp raised
      rw [Uint64.toNat_min, Uint64.toNat_min] at settledNat capLow
      have floorLow := cappedFloor_mono (preset := preset)
        (cap := withdrawalMaxEffectiveBalance preset fork validator) (low := balance)
        (high := settled) (UInt64.le_iff_toNat_le.mpr (by
          rw [Uint64.toNat_min, Uint64.toNat_min]; omega))
      have updatedLow := min_le_updatedEffectiveBalance effectiveOk
      refine ⟨final, last, atFinal, finalKey, finalCap, atLast, ?_, ?_⟩
      · rw [Uint64.toNat_min, Uint64.toNat_min]
        omega
      · rw [finalEffective, nowEffective]
        omega
  obtain ⟨current, -, atCurrent, -, -, -, -, low⟩ := kept epochs (Nat.le_refl _)
  exact ⟨current, atCurrent, low⟩

/-- A leak returns two thirds of the active stake to the voters, with stakes read at the start.

This holds from Altair, under the hypotheses on the constants and the absent validators.

Those are the hypotheses of the bound with the stake of the voters read at the end. -/
theorem twoThirds_of_leakRun_start (altair : .altair ≤ fork)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (bands : preset.IncrementWithinUpwardBand)
    (biasPos : 0 < config.INACTIVITY_SCORE_BIAS.toNat)
    (quotientPos : 0 < (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)
    {states slotted : Nat → BeaconState preset fork} {epochs threshold start : Nat}
    {voters : List ValidatorIndex} {absents : List Nat}
    {keys : Nat → Cryptography.Bls.BLSPubkey} {largest : Nat → Gwei}
    {voterKeys : ValidatorIndex → Cryptography.Bls.BLSPubkey} {stake : ValidatorIndex → Nat}
    {total voterTotal : Gwei}
    (ends : ∀ t < epochs, ((states t).slot + 1) % preset.SLOTS_PER_EPOCH = 0)
    (epochSlot : ∀ t < epochs, advanceSlot config checks (states t) = .ok (slotted t))
    (quiet : ∀ j ∈ absents, ∀ t < epochs,
      Relation.ReflTransGen (QuietStep config checks j (keys j)) (slotted t) (states (t + 1)))
    (within : ∀ t ≤ epochs, (states t).RegistryWithinLimit)
    (unnamed : ∀ j ∈ absents, ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ deposit ∈ ((states t).pendingDeposits electra).data, deposit.pubkey ≠ keys j)
    (untargeted : ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ ((states t).pendingConsolidations electra).data,
        consolidation.targetIndex.toNat ∉ absents)
    (capped : ∀ j ∈ absents, ∀ t < epochs, ∀ validator,
      (states t).validators.data[j]? = some validator →
        withdrawalMaxEffectiveBalance preset fork validator = largest j)
    -- On mainnet a validator that exits is no longer eligible.
    --
    -- So the threshold must be at least the effective balance of an absent validator when it exits.
    (absent : ∀ j ∈ absents, ∀ t < epochs, ∀ validator,
      (states t).validators.data[j]? = some validator →
        threshold < validator.effectiveBalance.toNat →
        isEligibleValidator (getPreviousEpoch (states t)) validator = .ok true ∧
          ∀ flags, ((states t).previousEpochParticipation altair).data[j]? = some flags →
            hasFlag flags TIMELY_TARGET_FLAG_INDEX = false)
    (started : ∀ j ∈ absents, ∃ validator balance,
      (states 0).validators.data[j]? = some validator ∧ validator.pubkey = keys j ∧
      (states 0).balances.data[j]? = some balance ∧
      validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      (balance.toNat ≤ validator.effectiveBalance.toNat + preset.upwardBand ∨
        largest j ≤ validator.effectiveBalance) ∧
      balance.toNat ≤ start)
    (largestAligned : ∀ j ∈ absents, largest j % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (thresholdAligned : threshold % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (wide : preset.downwardBand < threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    -- The voters are distinct.
    (distinct : voters.Nodup)
    -- Between epoch transitions, each voter takes only steps that cannot lower its capped balance.
    (steady : ∀ v ∈ voters, ∀ t < epochs,
      Relation.ReflTransGen (VoterStep config checks v.toNat (voterKeys v)) (slotted t)
        (states (t + 1)))
    -- At each visited state each voter is unslashed.
    (unslashed : ∀ v ∈ voters, ∀ t < epochs, ∀ validator,
      (states t).validators.data[v.toNat]? = some validator → validator.slashed = false)
    -- Suppose a voter is eligible at a visited state.
    --
    -- Then its flags of the previous epoch there have the timely source and target.
    (voted : ∀ v ∈ voters, ∀ t < epochs, ∀ validator,
      (states t).validators.data[v.toNat]? = some validator →
        isEligibleValidator (getPreviousEpoch (states t)) validator = .ok true →
        ∃ flags, ((states t).previousEpochParticipation altair).data[v.toNat]? = some flags ∧
          hasFlag flags TIMELY_SOURCE_FLAG_INDEX = true ∧
          hasFlag flags TIMELY_TARGET_FLAG_INDEX = true)
    -- At each visited state, no pending consolidation has a voter as its source.
    (unsourced : ∀ t < epochs, ∀ electra : .pectra ≤ fork,
      ∀ consolidation ∈ ((states t).pendingConsolidations electra).data,
        consolidation.sourceIndex ∉ voters)
    -- Each voter has a given key at the start.
    --
    -- Each one is in the registry at the start, with its key and a balance.
    --
    -- Its starting stake is at most its effective balance and its rounded capped balance there.
    (voterStarted : ∀ v ∈ voters, ∃ validator balance,
      (states 0).validators.data[v.toNat]? = some validator ∧ validator.pubkey = voterKeys v ∧
      (states 0).balances.data[v.toNat]? = some balance ∧
      stake v ≤ min validator.effectiveBalance.toNat
        (cappedFloor preset (withdrawalMaxEffectiveBalance preset fork validator) balance))
    -- The starting stake of the voters is at least twice the threshold per absent validator.
    (strong : 2 * absents.length * threshold ≤ (voters.map stake).sum)
    -- In the final state, these two only name the totals.
    (active : getTotalActiveBalance (states epochs) = .ok total)
    (voting : getTotalBalance (states epochs) voters = .ok voterTotal)
    -- In the final state, each active validator is a voter or an absent validator.
    --
    -- That is the only assumption on the final state.
    (covered : ∀ j (inside : j < (states epochs).validators.data.size),
      isActiveValidator (states epochs).validators.data[j] (getCurrentEpoch (states epochs)) =
        true → j.toUInt64 ∈ voters ∨ j ∈ absents)
    -- The run lasts at least the number of epochs of the trace bound.
    --
    -- That number depends only on the threshold, the starting absent balances and the constants.
    (long : leakEpochs (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      config.INACTIVITY_SCORE_BIAS.toNat
      (config.INACTIVITY_SCORE_BIAS.toNat *
        (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)
      (start + preset.downwardBand + 1 -
        (threshold + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ epochs) :
    -- Either some visited state does not leak or sees finality rise in the slot that leaves it.
    (∃ t < epochs, isInInactivityLeak (states t) ≠ .ok true ∨
      (states t).finalizedCheckpoint.epoch < (slotted t).finalizedCheckpoint.epoch) ∨
      -- Otherwise, in the final state, twice the active balance is at most three times the voters'.
      2 * total.toNat ≤ 3 * voterTotal.toNat := by
  by_cases stopped : ∃ t < epochs, isInInactivityLeak (states t) ≠ .ok true ∨
      (states t).finalizedCheckpoint.epoch < (slotted t).finalizedCheckpoint.epoch
  · exact .inl stopped
  simp only [not_exists, not_and, not_or, ne_eq, not_not, UInt64.not_lt] at stopped
  have leak : ∀ t < epochs, isInInactivityLeak (states t) = .ok true :=
    fun t during => (stopped t during).1
  have stalled : ∀ t < epochs,
      (slotted t).finalizedCheckpoint.epoch ≤ (states t).finalizedCheckpoint.epoch :=
    fun t during => (stopped t during).2
  -- Each voter ends the run with an effective balance at least its starting stake.
  have each : ∀ v ∈ voters, stake v ≤ balanceAt (states epochs) v.toNat := by
    intro v member
    obtain ⟨validator, balance, found, keyed, held, low⟩ := voterStarted v member
    obtain ⟨now, atNow, high⟩ := effectiveBalance_ge_of_voterRun altair ends epochSlot
      (steady v member) (fun t during => within t (Nat.le_of_lt during)) leak stalled
      (unslashed v member) (voted v member)
      (fun t during electra consolidation listed same => unsourced t during electra consolidation
        listed (UInt64.toNat_inj.mp same ▸ member))
      found keyed held
    simp only [balanceAt, atNow, Option.map_some, Option.getD_some]
    omega
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp voting
  have summed : (voters.map stake).sum ≤ voterTotal.toNat := by
    rw [totalEq, Models.stake, List.sum_toFinset _ distinct]
    exact Nat.le_trans (List.sum_le_sum each) (Nat.le_max_right _ _)
  exact twoThirds_of_leakRun altair apart bands biasPos quotientPos ends epochSlot quiet within
    unnamed untargeted capped absent started largestAligned thresholdAligned wide active voting
    covered (Nat.le_trans strong summed) long

end EthLib.Consensus

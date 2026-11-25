module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Producers
import EthLib.Consensus.Proofs.Transition.ActiveKept

/-!
# The penalty envelope of a branch

The penalties of the epochs of a branch fit an envelope read at the reference state.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section

open Cryptography.Bls Uint64

/-! ## The penalty envelope of a branch

The producer sums, over the events of a branch, the penalty and sync debits of a cohort.

The cohort is the keys active and unslashed at the start `x`.

The branch splits into one segment per epoch, at the epochs of the starts of its steps.

The blocks of a segment pay the sync debits of its epoch.

The slot that ends the epoch pays its rewards pass.

Together they fit the penalty `lambda_t` of the epoch. -/

/-- The cohort of the producer, by registry position: the keys active and unslashed at `x`. -/
def penaltyCohort (x : ForkedBeaconState preset) : Finset Nat :=
  ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset.filter fun i =>
    (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true = false).image UInt64.toNat

/-- A key of the cohort is in the registry at `x`. -/
private theorem penaltyCohort_inside {x : ForkedBeaconState preset} (early : x.fork < .glamsterdam)
    {j : Nat} (member : j ∈ penaltyCohort x) : j < x.state.validators.data.size := by
  obtain ⟨i, chosen, rfl⟩ := Finset.mem_image.mp member
  obtain ⟨v, found, _⟩ := (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp
    (List.mem_toFinset.mp (Finset.mem_filter.mp chosen).1)
  exact (Array.getElem?_eq_some_iff.mp found).1

/-- A key of the cohort is an active, unslashed key of `x`. -/
private theorem penaltyCohort_cohort {x : ForkedBeaconState preset} (early : x.fork < .glamsterdam)
    {i : Nat} (member : i ∈ penaltyCohort x) :
    (x.state.validators.data[i]?).any (fun old =>
      isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) = true := by
  obtain ⟨j, chosen, rfl⟩ := Finset.mem_image.mp member
  obtain ⟨active, unslashed⟩ := Finset.mem_filter.mp chosen
  obtain ⟨v, found, active⟩ := (mem_getActiveValidatorIndices
    (x.state.validators.bound early)).mp (List.mem_toFinset.mp active)
  simpa only [found, Option.map_some, Option.getD_some, Option.any_some, active,
    Bool.true_and, Bool.not_eq_true'] using unslashed

/-- The producer's sum at one event is the sum over the cohort.

The active indices are distinct, and each unslashed one is the position of its key. -/
theorem producer_le_cohort (x : ForkedBeaconState preset) (early : x.fork < .glamsterdam)
    (debit : Nat → Nat) :
    ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
      if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
        else debit i.toNat).sum ≤ ∑ j ∈ penaltyCohort x, debit j := by
  have unique := (getActiveValidatorIndices_sorted (x.state.validators.bound early)
    (getCurrentEpoch x.state)).imp
    (fun {a b} less (same : a = b) => by subst same; exact UInt64.lt_irrefl _ less)
  rw [← List.sum_toFinset _ unique, penaltyCohort,
    Finset.sum_image fun a _ b _ same => UInt64.toNat_inj.mp same, Finset.sum_filter]
  refine Finset.sum_le_sum fun i _ => ?_
  cases (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true <;> simp

/-- The debits of one event over a set of keys are at most its debits over the registry. -/
theorem keys_debits_le (S : Finset Nat) (e : BalanceEvent preset) :
    ∑ j ∈ S, (actualBalanceAt e.before j - actualBalanceAt e.after j) ≤ e.debits := by
  unfold BalanceEvent.debits
  refine Finset.sum_le_sum_of_ne_zero fun j _ positive => Finset.mem_range.mpr ?_
  by_contra outside
  apply positive
  simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]

/-- Let the events stay within their limits.

Then the cohort's debits over them are its penalty debits and the sync limits. -/
private theorem cohort_debits_le (S : Finset Nat) :
    ∀ {events : List (BalanceEvent preset)}, EventsBounded events →
      (events.map fun e => ∑ j ∈ S, floorPenaltyDebit j e).sum ≤
        (events.map fun e => ∑ j ∈ S, penaltyDebit j e).sum + sourceDebits .sync events
  | [], _ => by simp
  | e :: rest, bounded => by
    have tail := cohort_debits_le S (events := rest) fun e' member => bounded e' (.tail _ member)
    have limits := (bounded e (.head _)).2
    have point : ∑ j ∈ S, floorPenaltyDebit j e ≤
        ∑ j ∈ S, penaltyDebit j e + if e.source = .sync then e.debitLimit else 0 := by
      unfold floorPenaltyDebit
      rw [Finset.sum_add_distrib]
      apply Nat.add_le_add_left
      split
      · exact (keys_debits_le S e).trans limits
      · simp
    simp only [List.map_cons, List.sum_cons, sourceDebits] at tail ⊢
    omega

/-- Events with no penalty or inactivity source have no penalty debit. -/
private theorem penaltyDebits_zero (S : Finset Nat) {events : List (BalanceEvent preset)}
    (free : PenaltyFree events) : (events.map fun e => ∑ j ∈ S, penaltyDebit j e).sum = 0 :=
  List.sum_eq_zero fun _ member => by
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    exact Finset.sum_eq_zero fun j _ => by simp [penaltyDebit, (free e inside).1, (free e inside).2]

/-- A list with no sync event records no sync debit limit. -/
private theorem syncDebits_zero {events : List (BalanceEvent preset)}
    (absent : ∀ e ∈ events, e.source ≠ .sync) : sourceDebits .sync events = 0 :=
  List.sum_eq_zero fun _ member => by
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    simp [absent e inside]

/-- A step of a run starts no earlier than the run and no later than its end. -/
private theorem contains_epochs {g a u w : ForkedBeaconState preset} (run : Run config checks g a)
    {step : Step config checks u w} (member : run.Contains step) :
    getCurrentEpoch g.state ≤ getCurrentEpoch u.state ∧
      getCurrentEpoch u.state ≤ getCurrentEpoch a.state := by
  obtain ⟨pre, post, -⟩ := run.contains_split step member
  exact ⟨currentEpoch_le_of_chainSteps pre.chainSteps,
    UInt64.le_trans step.chainStep.currentEpoch_le (currentEpoch_le_of_chainSteps post.chainSteps)⟩

/-- A segment of a branch that starts in an epoch either stays in it or ends it with one slot. -/
theorem segment_events_cases {m n : ForkedBeaconState preset}
    (mid : Run config checks m n) (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork)
    (high : Nat) (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    -- Every step of the segment `mid` starts at the epoch of its start `m`.
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    {found : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok found) :
    getCurrentEpoch n.state = getCurrentEpoch m.state ∨
      ∃ (u : ForkedBeaconState preset) (inner : Run config checks m u)
        (boundary : advanceSlotAcross config checks u = .ok n)
        (during crossings : List (BalanceEvent preset)) (cached : BeaconState preset u.fork),
        mid = inner.snoc (.slot boundary) ∧ u.fork < .glamsterdam ∧
        getCurrentEpoch u.state = getCurrentEpoch m.state ∧
        getCurrentEpoch u.state < getCurrentEpoch n.state ∧
        inner.balanceEvents high = .ok during ∧ processSlot u.state = .ok cached ∧
        PenaltyFree crossings ∧ (∀ e ∈ crossings, e.source ≠ .sync) ∧
        (found = during ++ crossings ∨
          ∃ just pass rewarded later, EpochStage.Edge config checks .justification cached just ∧
            EpochStage.Edge config checks .inactivity just pass ∧
            replayRewards (config := config) (pass, []) = .ok rewarded ∧
            found = during ++ ((rewarded.2 ++ later) ++ crossings) ∧
            (∀ e ∈ later,
              e.source = .slashings ∨ e.source = .deposits ∨ e.source = .consolidations) ∧
            (∀ e ∈ rewarded.2,
              e.source = .rewards ∨ e.source = .penalties ∨ e.source = .inactivity)) := by
  -- If the segment leaves the epoch, its last step is the slot that ends it, after an inner run.
  --
  -- That slot records the fork crossings of its upgrades, which pay no penalty and no sync debit.
  --
  -- When it also runs the epoch passes, it records the rewards pass and then the later passes.
  rcases segment_slot_cases mid starts with same | ⟨u, inner, boundary, rfl, uEpoch, crossing⟩
  · exact .inl same
  right
  have uEarly : u.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (Step.slot boundary).chainStep.fork_le early
  obtain ⟨added, addedOk⟩ := (Step.slot boundary).balanceEvents_ok early
  obtain ⟨during, duringOk⟩ := inner.balanceEvents_ok uEarly high
  have split : found = during ++ added := by
    simp only [Run.balanceEvents, duringOk, addedOk, bind, Except.bind,
      show (getCurrentEpoch u.state).toNat ≤ high + 1 by
        have := UInt64.lt_iff_toNat_lt.mp crossing; omega,
      ↓reduceIte, pure, Except.pure, Except.ok.injEq] at replayed
    exact replayed.symm
  subst split
  -- The slot records the epoch passes, then the upgrades, which are fork crossings.
  obtain ⟨advanced, cached, crossings, -, -, cachedOk, crossingOk, kind⟩ :=
    Step.balanceEvents_slot boundary early addedOk
  have crossed := upgradeBalanceReplay_crossing crossingOk
  refine ⟨u, inner, boundary, during, crossings, cached, rfl, uEarly, uEpoch, crossing, duringOk,
    cachedOk, fun e member => by simp [crossed e member], fun e member => by
      simp [crossed e member], ?_⟩
  rcases kind with ⟨-, rfl⟩ | ⟨middle, -, recorded, recordOk, -, -, -, rfl, -⟩
  · exact .inl rfl
  -- The epoch passes are the rewards pass, then slashings, deposits and consolidations.
  have altairU : .altair ≤ u.fork := Nat.le_trans altair (fork_le_of_chainSteps inner.chainSteps)
  obtain ⟨just, pass, rewarded, later, justified, scored, rewardedOk, recordedEq, laterSources,
    rewardSources⟩ := epochReplay_events altairU (epochBalanceReplay_trace recordOk)
  simp only at recordedEq
  subst recordedEq
  exact .inr ⟨just, pass, rewarded, later, justified, scored, rewardedOk, rfl, laterSources,
    rewardSources⟩

/-- The cohort's penalty and sync debits in one segment of a branch fit its epoch's `lambda_t`. -/
private theorem segment_penalties_core {g x m n : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (altairX : .altair ≤ x.fork) (era : .pectra ≤ x.fork ∨ n.fork < .pectra)
    (high : Nat) (guard : aprioriGuardAt config x high)
    -- `t` is the number of epochs from `x` to `m`.
    (toM : Run config checks x m) (mid : Run config checks m n) (early : n.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    -- The blocks of the segment read the total of `m`, and so does its rewards pass, if it has one.
    --
    -- That total is at most `W_t`, by the active-stake ceiling.
    --
    -- The floor of that ceiling reads only earlier epochs.
    (totalBound : ∀ total, getTotalActiveBalance m.state = .ok total →
      total.toNat ≤ stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
    (floorCeiling : stakeFloorAt config x high (ix x m) ≤
      stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
    -- The segment `mid` runs from `m`, and each of its steps starts at the epoch of `m`.
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    -- The floor `T_minus_t` bounds it below only when the segment ends the epoch.
    --
    -- Only then does the segment run a pass.
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch n.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    -- The eligible stake of the cohort at the last state of the epoch must be at most `W_t`.
    --
    -- That state is read through a split of the segment, so its run is a prefix of the branch.
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (post : Run config checks z n), mid = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    {events : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high (ix x m)) (ix x m) := by
  -- A segment runs inside its epoch, and its last step may be the slot that ends the epoch.
  --
  -- The blocks of the segment pay the sync debits of the epoch.
  --
  -- That slot pays its rewards pass.
  have mEarly : m.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps mid.chainSteps) early
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps toM.chainSteps) mEarly
  have mAltair : .altair ≤ m.fork := Nat.le_trans altairX (fork_le_of_chainSteps toM.chainSteps)
  have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
  have mn := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps mid.chainSteps)
  -- Every event is within its limits, so the sync debits of the cohort are sync debit limits.
  obtain ⟨found, foundOk, bounded⟩ :=
    Run.balanceEvents_bounded (shared.append toM) mid genesis early high
  obtain rfl := Except.ok.inj (foundOk.symm.trans replayed)
  have debits := cohort_debits_le (penaltyCohort x) bounded
  obtain ⟨-, -, -, -, -, -, divisor, -, -, -, -, positiveFloor, -, -⟩ := id guard
  have floorPositive : 0 < stakeFloorAt config x high (ix x m) :=
    positiveFloor _ (by unfold ix driftHorizon; omega)
  have syncOnly {z : ForkedBeaconState preset} (inner : Run config checks m z)
      (zEarly : z.fork < .glamsterdam) (same : getCurrentEpoch z.state = getCurrentEpoch m.state)
      {during : List (BalanceEvent preset)} (duringOk : inner.balanceEvents high = .ok during) :
      (∀ i, i < m.state.validators.data.size → effectiveAt z i = effectiveAt m i) ∧
      PenaltyFree during ∧ sourceDebits .sync during ≤
        epochPenalty preset config (startInactivityScore config x)
          (stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
          (stakeFloorAt config x high (ix x m)) (ix x m) ∧
      ∀ total perIncrement, getTotalActiveBalance m.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        sourceDebits .sync during * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat := by
    obtain ⟨effective, free, reads, syncCredits⟩ :=
      epoch_sync_data inner mAltair zEarly same high duringOk
    refine ⟨effective, free, ?_, fun total _ totalOk _ => syncCredits total totalOk⟩
    rcases reads with ⟨total, perIncrement, totalOk, per⟩ | quiet
    · exact sync_penalty_envelope (syncCredits total totalOk) (totalBound total totalOk)
        floorCeiling floorPositive
    · exact quiet ▸ Nat.zero_le _
  rcases segment_events_cases mid early mAltair high endEpoch starts replayed with same |
    ⟨u, inner, boundary, during, crossings, cached, rfl, uEarly, uEpoch, crossing, duringOk,
      cachedOk, crossingsFree, crossingsQuiet, kind⟩
  · -- A segment inside its epoch pays only the sync debits of its blocks.
    obtain ⟨_, free, syncBound, _⟩ := syncOnly mid early same replayed
    rw [penaltyDebits_zero _ free, Nat.zero_add] at debits
    exact debits.trans syncBound
  -- The blocks inside the epoch pay its sync debits and no penalty.
  obtain ⟨effective, free, syncBound, syncCredits⟩ := syncOnly inner uEarly uEpoch duringOk
  rcases kind with rfl | ⟨just, pass, rewarded, later, justified, scored, rewardedOk, rfl,
    laterSources, rewardSources⟩
  · -- Without epoch passes, the slot records only fork crossings.
    have penalties : ((during ++ crossings).map fun e =>
        ∑ j ∈ penaltyCohort x, penaltyDebit j e).sum = 0 :=
      penaltyDebits_zero _ (free.append crossingsFree)
    simp only [List.map_append, List.sum_append, sourceDebits_append,
      syncDebits_zero crossingsQuiet] at debits penalties ⊢
    omega
  have altair : .altair ≤ u.fork :=
    Nat.le_trans mAltair (fork_le_of_chainSteps inner.chainSteps)
  have laterFree : PenaltyFree later := fun e member => by
    rcases laterSources e member with s | s | s <;> simp [s]
  have laterQuiet : ∀ e ∈ later, e.source ≠ .sync := fun e member => by
    rcases laterSources e member with s | s | s <;> simp [s]
  have rewardQuiet : ∀ e ∈ rewarded.2, e.source ≠ .sync := fun e member => by
    rcases rewardSources e member with s | s | s <;> simp [s]
  have penalties : ((during ++ later ++ crossings).map fun e =>
      ∑ j ∈ penaltyCohort x, penaltyDebit j e).sum = 0 :=
    penaltyDebits_zero _ ((free.append laterFree).append crossingsFree)
  -- The sums over the events and over the cohort commute.
  have passDebits : (rewarded.2.map fun e => ∑ j ∈ penaltyCohort x, penaltyDebit j e).sum =
      ∑ j ∈ penaltyCohort x, (rewarded.2.map (penaltyDebit j)).sum := by
    simpa using Multiset.sum_map_sum (m := (rewarded.2 : Multiset (BalanceEvent preset)))
      (s := penaltyCohort x) (f := fun e j => penaltyDebit j e)
  simp only [List.map_append, List.sum_append, sourceDebits_append,
    syncDebits_zero laterQuiet, syncDebits_zero crossingsQuiet, syncDebits_zero rewardQuiet]
    at debits penalties ⊢
  -- The pass reads the registry and the total of `m`, and the scores of the start `x`.
  obtain ⟨activeKept, effectiveKept, passEpoch, registry⟩ :=
    pass_kept_of_effective inner effective uEpoch cachedOk justified scored
  have totalSame := total_active_congr
    (activeKept.mono (getCurrentEpoch_le_activityFixedEpoch _)) passEpoch effectiveKept
  have sizes : x.state.validators.data.size ≤ pass.validators.data.size := by
    rw [registry.1]
    exact registryGrows_of_chainSteps (toM.append inner).chainSteps
  rcases replayRewards_penalty_scalar_cases altair (pass.validators.bound uEarly) rewardedOk
      (penaltyCohort x)
      (fun j member => Nat.lt_of_lt_of_le (penaltyCohort_inside xEarly member) sizes) with
    ⟨total, perIncrement, passTotal, per⟩ | quiet
  swap
  · omega
  have totalOk : getTotalActiveBalance m.state = .ok total := totalSame.symm.trans passTotal
  have syncLe := syncCredits total perIncrement totalOk per
  have uIndex : ix x u = ix x m := by
    unfold ix
    rw [uEpoch]
  have weights : ∑ j ∈ penaltyCohort x, eligibleWeight pass j ≤
      stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x := by
    have bound := eligible inner (.snoc .nil (.slot boundary)) rfl
      (UInt64.lt_iff_toNat_lt.mp crossing)
    rw [uIndex] at bound
    refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ => ?_) bound
    simp only [eligibleWeight, getPreviousEpoch, getCurrentEpoch, registry.1, registry.2]
  have envelope := epoch_penalty_envelope (x := x) (high := high) (t := ix x m) altair
    (pass.validators.bound uEarly) rewardedOk passTotal (penaltyCohort x)
    (fun j member => Nat.lt_of_lt_of_le (penaltyCohort_inside xEarly member) sizes)
    (fun j member score found => by
      have bound := referenceScores_le (toM.append inner) altairX uEarly
        (era.imp_right (fun before => Nat.lt_of_le_of_lt
          (Step.slot boundary).chainStep.fork_le before))
        cachedOk justified scored (penaltyCohort_inside xEarly member) altair found
      rw [show (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat = ix x m by
        rw [← uIndex]] at bound
      exact bound)
    weights (floor toM mEarly (by rw [← uEpoch]; exact UInt64.lt_iff_toNat_lt.mp crossing) total
          totalOk)
    (totalBound total totalOk) floorPositive divisor syncLe
  omega

/-- The Electra ceiling supplies the actual-total callback of the shared segment proof. -/
private theorem segment_penalties_le {g x m n : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (guard : aprioriGuardAt config x high)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (toM : Run config checks x m) (mid : Run config checks m n) (early : n.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch n.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (post : Run config checks z n), mid = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    {events : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high (ix x m)) (ix x m) := by
  have mEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps mid.chainSteps) early
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps toM.chainSteps) mEarly
  have mn := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps mid.chainSteps)
  obtain ⟨r, pre, inner, _, _, _, _, _, sameM, current, previous, _⟩ :=
    activeStake_prefix_witness shared genesis toM electra mEarly high (by omega) guard
      aligned unit
      (fun head headEarly within found ok => otherCredit_le_allowance_electra shared genesis head
        caps aligned electra headEarly twoSlots high within guard ok)
      (fun head headEarly before total ok => floor head headEarly (by omega) total ok)
  have ceilingM := activeStake_same_epoch inner
    (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) mEarly sameM current previous
  rw [← sameM] at ceilingM
  have mono := ceilingAt_mono (config := config) electra high
  apply segment_penalties_core shared genesis (Nat.le_trans (by decide) electra) (.inl electra)
    high guard toM mid early endEpoch ?_
    ((floor_le_ceiling shared genesis xEarly electra _).trans (Nat.le_add_right _ _))
    starts floor eligible replayed
  intro total totalOk
  have totalValue := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)).2.2
  rw [totalValue]
  exact (max_le (unit.trans (mono (Nat.zero_le _))) ceilingM.1).trans (Nat.le_add_right _ _)

/-- The penalties of `t + 1` epochs are those of `t` epochs and `lambda_t`. -/
private theorem penalties_succ (x : ForkedBeaconState preset) (high t : Nat) :
    windowPenalties (config := config) x high (t + 1) =
        windowPenalties (config := config) x high t +
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) (stakeFloorAt config x high t)
            t := by
  simp [windowPenalties, List.range_succ, List.map_append, List.sum_append]

/-- A cost that adds across consecutive runs fits a bound summed over the first `t` epochs. -/
theorem run_cuts_of_additive {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (P : ForkedBeaconState preset → Prop)
    (F : ∀ {a b : ForkedBeaconState preset}, Run config checks a b → Nat) (bound : Nat → Nat)
    (add : ∀ {a m n : ForkedBeaconState preset} (pre : Run config checks a m)
      (post : Run config checks m n), n.fork < .glamsterdam → F (pre.append post) = F pre + F post)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat → P z)
    (segment : ∀ {m n : ForkedBeaconState preset} (_toM : Run config checks x m)
      (mid : Run config checks m n) (_ : Run config checks n y),
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), mid.Contains step →
        getCurrentEpoch u.state = getCurrentEpoch m.state) →
      (∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
        (post : Run config checks z n), mid = pre.append post →
        (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat → P z) →
      F mid ≤ bound (ix x m))
    (t : Nat) (bounded : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch x.state).toNat + t) :
    F tail ≤ ((List.range t).map bound).sum := by
  let start := (getCurrentEpoch x.state).toNat
  -- A run without a step adds nothing: it is `.nil`, and `.nil.append .nil` is `.nil`.
  have quiet : ∀ {a b : ForkedBeaconState preset} (run : Run config checks a b),
      b.fork < .glamsterdam → (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
        ¬ run.Contains step) → F run = 0 := by
    intro a b run bEarly empty
    cases run with
    | nil =>
      have := add (Run.nil : Run config checks a a) Run.nil bEarly
      change F Run.nil = F Run.nil + F Run.nil at this
      omega
    | snoc pre step => exact absurd (.last _ _) (empty step)
  -- After `t + 1` cuts, the first part pays at most the bound of `t + 1` epochs.
  have key : ∀ t, ∃ (m : ForkedBeaconState preset) (cut : Run config checks x m)
      (rest : Run config checks m y), tail = cut.append rest ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), rest.Contains step →
        start + t < (getCurrentEpoch u.state).toNat) ∧
      (start + t < (getCurrentEpoch m.state).toNat ∨
        ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), ¬ rest.Contains step) ∧
      F cut ≤ ((List.range (t + 1)).map bound).sum := by
    intro t
    induction t with
    | zero =>
      obtain ⟨m, cut, rest, same, inside, outside, -, begins⟩ := window_cut tail early start
      refine ⟨m, cut, rest, same, outside, begins, ?_⟩
      rw [List.range_succ, List.map_append, List.sum_append]
      have bound := segment .nil cut rest (fun step member => by
        have inner := contains_epochs cut member
        have low := UInt64.le_iff_toNat_le.mp inner.1
        exact UInt64.toNat_inj.mp (Nat.le_antisymm (inside step member) low))
        (fun pre post split before => by
          have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
          exact eligible pre (post.append rest)
            (by rw [same, split]; exact (Run.append_assoc _ _ _).symm)
            (by omega))
      simpa [ix] using bound
    | succ t ih =>
      obtain ⟨m, cut, rest, rfl, later, begins, bound⟩ := ih
      obtain ⟨n, mid, last, rfl, inside, outside, -, ends⟩ :=
        window_cut rest early (start + (t + 1))
      have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps last.chainSteps) early
      refine ⟨n, cut.append mid, last, Run.append_assoc _ _ _, outside, ends, ?_⟩
      rw [add cut mid nEarly, List.range_succ, List.map_append, List.sum_append]
      refine Nat.add_le_add bound ?_
      by_cases empty : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
          ¬ mid.Contains step
      · rw [quiet mid nEarly empty]
        exact Nat.zero_le _
      -- A step of the segment starts after `start + t`, so the segment starts there too.
      simp only [not_forall, not_not] at empty
      obtain ⟨u, w, step, member⟩ := empty
      have first := later step ((Run.contains_append mid last step).mpr (.inl member))
      have mStart : (getCurrentEpoch m.state).toNat = start + (t + 1) := by
        rcases begins with after | none
        · have low := UInt64.le_iff_toNat_le.mp (contains_epochs mid member).1
          have high' := inside step member
          omega
        · exact absurd ((Run.contains_append mid last step).mpr (.inl member)) (none step)
      have index : ix x m = t + 1 := by
        simp only [ix]
        omega
      have each := segment cut mid last (fun step' member' => by
        have low := later step' ((Run.contains_append mid last step').mpr (.inl member'))
        have up := inside step' member'
        exact UInt64.toNat_inj.mp (by omega))
        (fun pre post split before => by
          have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps last.chainSteps)
          exact eligible (cut.append pre) (post.append last)
            (by rw [split, ← Run.append_assoc pre post last, Run.append_assoc cut pre])
            (by omega))
      simpa [index] using each
  cases t with
  | zero =>
    -- No step starts before the epoch of `x`, so the branch is empty.
    have empty : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
        ¬ tail.Contains step := fun step member => by
      have low := UInt64.le_iff_toNat_le.mp (contains_epochs tail member).1
      have up := bounded step member
      omega
    rw [quiet tail early empty]
    simp
  | succ t =>
    obtain ⟨m, cut, rest, rfl, after, -, bound⟩ := key t
    -- No step of the branch starts at the epoch `epoch x + t + 1` or later.
    have empty : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
        ¬ rest.Contains step := fun step member => by
      have late := after step member
      have up := bounded step ((Run.contains_append cut rest step).mpr (.inr member))
      simp only [start] at late
      omega
    rw [add cut rest early, quiet rest early empty, Nat.add_zero]
    exact bound

/-- The costs of a branch's replayed events fit a bound summed over its first `t` epochs. -/
theorem run_cuts_le {x y : ForkedBeaconState preset}
    (high : Nat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (P : ForkedBeaconState preset → Prop) (cost : BalanceEvent preset → Nat) (bound : Nat → Nat)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat → P z)
    (segment : ∀ {m n : ForkedBeaconState preset} (_toM : Run config checks x m)
      (mid : Run config checks m n) (_ : Run config checks n y),
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), mid.Contains step →
        getCurrentEpoch u.state = getCurrentEpoch m.state) →
      (∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
        (post : Run config checks z n), mid = pre.append post →
        (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat → P z) →
      ∀ {found : List (BalanceEvent preset)}, mid.balanceEvents high = .ok found →
      (found.map cost).sum ≤ bound (ix x m))
    (t : Nat) (bounded : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch x.state).toNat + t)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map cost).sum ≤ ((List.range t).map bound).sum := by
  have total := run_cuts_of_additive tail early P
    (fun r => (((r.balanceEvents high).toOption.getD []).map cost).sum) bound
    (fun {a m n} pre post nEarly => by
      obtain ⟨one, oneOk⟩ := pre.balanceEvents_ok
        (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) nEarly) high
      obtain ⟨two, twoOk⟩ := post.balanceEvents_ok nEarly high
      simp [balanceEvents_append pre post high oneOk twoOk, oneOk, twoOk, Except.toOption])
    eligible
    (fun {m n} toM mid rest starts elig => by
      obtain ⟨found, foundOk⟩ := mid.balanceEvents_ok
        (Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early) high
      simpa [foundOk, Except.toOption] using segment toM mid rest starts elig foundOk)
    t bounded
  simpa [replayed, Except.toOption] using total

/-- The penalty and sync debits of the cohort over a branch fit the penalties of `t` epochs.

At each epoch cut the cohort must have eligible stake. -/
private theorem run_penalties_core {x y : ForkedBeaconState preset}
    (high : Nat)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    (segment : ∀ {m n : ForkedBeaconState preset} (_toM : Run config checks x m)
      (mid : Run config checks m n) (_ : Run config checks n y),
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), mid.Contains step →
        getCurrentEpoch u.state = getCurrentEpoch m.state) →
      (∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
        (post : Run config checks z n), mid = pre.append post →
        (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
        ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
          stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x) →
      ∀ {found : List (BalanceEvent preset)}, mid.balanceEvents high = .ok found →
      (found.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
        epochPenalty preset config (startInactivityScore config x)
          (stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
          (stakeFloorAt config x high (ix x m)) (ix x m))
    (t : Nat) (bounded : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch x.state).toNat + t)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      windowPenalties (config := config) x high t :=
  run_cuts_le high tail early (fun z => ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
      stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x) _
    (fun t => epochPenalty preset config (startInactivityScore config x)
      (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) (stakeFloorAt config x high t) t)
    eligible segment t bounded replayed

/-- The Electra segment bound supplies the shared cut induction. -/
private theorem run_penalties_upto {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (guard : aprioriGuardAt config x high)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    (t : Nat) (bounded : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch x.state).toNat + t)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      windowPenalties (config := config) x high t := by
  apply run_penalties_core high tail early eligible ?_ t bounded replayed
  intro m n toM mid rest starts weights found ok
  have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  exact segment_penalties_le shared genesis caps aligned electra twoSlots high guard unit
    toM mid (Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early) (by omega)
    starts (fun head headEarly before => floor head headEarly (by omega)) weights ok

/-- Every step of a branch starts before the epoch after the end of the branch. -/
theorem steps_before_end {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {u w : ForkedBeaconState preset} (step : Step config checks u w)
    (member : tail.Contains step) :
    (getCurrentEpoch u.state).toNat < (getCurrentEpoch x.state).toNat + (ix x y + 1) := by
  have up := UInt64.le_iff_toNat_le.mp (contains_epochs tail member).2
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  simp only [ix]
  omega

/-- The penalty and sync debits of the cohort over a branch fit the penalties of its epochs.

The branch from `x` to `y` splits after its last step starting at each epoch `epoch x + t`.

The steps between two such cuts start at one epoch, and so form one segment.

The floor and the eligible stake are read at the states before the epoch of `y`. -/
private theorem run_penalties_le {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (guard : aprioriGuardAt config x high)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      windowPenalties (config := config) x high (ix x y + 1) := by
  -- Every step of the branch starts by the epoch of `y`.
  exact run_penalties_upto shared genesis caps aligned electra twoSlots high guard unit
    tail early endEpoch floor eligible (ix x y + 1) (steps_before_end tail) replayed

/-- The penalty envelope of the a priori bound, from Electra, under the floor of the active stake.

It takes three hypotheses that the active-stake ceiling also reads.

The penalties are those of the epochs from `x` through the epoch of `y`. -/
private theorem penaltyProducer_of_floor {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    -- The first is the lower bound on the initial ceiling.
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    -- The second is the floor `T_minus` of the total active balance before the epoch of `y`.
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high
          ((getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat) ≤ total.toNat)
    -- The third bounds the cohort's eligible stake at each such state by `T_plus + Y`.
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
      fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
        else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (ix x y + 1) := by
  obtain ⟨genesis, -, caps, aligned, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  refine (List.sum_le_sum fun e _ => producer_le_cohort x xEarly (floorPenaltyDebit · e)).trans ?_
  exact run_penalties_le shared genesis caps aligned electra twoSlots high guard unit
    tail early endEpoch floor eligible replayed

private theorem LedgerCuts.roundLedger_of_floor
    {tail : Run config checks x y} (ledger : LedgerCuts tail)
    (shared : Run config checks g x) (supported : Supported shared tail high)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks x z)
      (post : Run config checks z y), tail = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x) :
    ∃ result : RoundLedger tail high, result.toLedgerCuts = ledger := by
  have startEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps)
    supported.2.2.2.2.1
  have unit := ceiling_unit_of_guard shared supported.1 supported.2.2.2.1
    startEarly electra supported.2.2.2.2.2.2
  obtain ⟨events, replayed⟩ := tail.balanceEvents_ok supported.2.2.2.2.1 high
  have numeric := penaltyProducer_of_floor shared tail high supported twoSlots electra
    unit floor eligible events replayed
  have horizon : ix x y + 1 ≤ driftHorizon x high + 1 := by
    have endpoint := supported.2.2.2.2.2.1
    unfold ix driftHorizon
    omega
  exact ledger.roundLedger_electra shared supported electra twoSlots replayed
    (numeric.trans (penalties_monotone x high horizon))
    (run_partials_le_paid_of_endpoint_floor shared supported.1 tail electra
      supported.2.2.2.2.1 high supported.2.2.2.2.2.1 supported.2.2.2.2.2.2
      supported.2.2.2.1 unit
      (fun head early within found replayed => otherCredit_le_allowance_electra shared
        supported.1 head supported.2.2.1 supported.2.2.2.1 electra early twoSlots high within
        supported.2.2.2.2.2.2 replayed) floor replayed)

/-- The cohort keys of `x` still retained at `cutoff`, as a queue of virtual consolidations.

The retained potential counts them as the funded potential counts pending sources. -/
private def retainedSources {fork : Fork} (x : ForkedBeaconState preset)
    (s : BeaconState preset fork) (cutoff : Epoch) : List PendingConsolidation :=
  ((List.range s.validators.data.size).filter fun i =>
    (x.state.validators.data[i]?).any (fun old =>
      isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
    (s.validators.data[i]?).any (fun v => decide (cutoff < v.withdrawableEpoch))).map
    fun i => ⟨i.toUInt64, 0⟩

/-- A position of the registry is a virtual source exactly when it is retained. -/
private theorem retainedSources_any {fork : Fork} (x : ForkedBeaconState preset)
    {s : BeaconState preset fork} (cutoff : Epoch) (within : s.RegistryWithinLimit) {i : Nat}
    (inside : i < s.validators.data.size) :
    (retainedSources x s cutoff).any (fun c => c.sourceIndex.toNat == i) =
      ((x.state.validators.data[i]?).any (fun old =>
          isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) &&
        (s.validators.data[i]?).any (fun v => decide (cutoff < v.withdrawableEpoch))) := by
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨c, member, same⟩
    obtain ⟨j, chosen, rfl⟩ := List.mem_map.mp member
    obtain ⟨range, retained⟩ := List.mem_filter.mp chosen
    have equal : j = i := by
      simpa [toNat_toUInt64_of_lt within (List.mem_range.mp range)] using same
    subst equal
    exact retained
  · intro retained
    exact ⟨⟨i.toUInt64, 0⟩, List.mem_map.mpr ⟨i, List.mem_filter.mpr
      ⟨List.mem_range.mpr inside, retained⟩, rfl⟩,
      by simp [toNat_toUInt64_of_lt within inside]⟩

/-- Take a step that keeps the old registry and only appends new keys.

After it, the retained potential equals a funded potential.

This funded potential has the virtual sources of the old state queued.

The appended keys are not keys of `x`, so they are never retained. -/
private theorem retained_eq_funding_after {fork : Fork} (x : ForkedBeaconState preset)
    (s t : BeaconState preset fork) (queue : List PendingConsolidation) (cutoff : Epoch)
    (within : s.RegistryWithinLimit)
    (kept : ∀ i, i < s.validators.data.size → t.validators.data[i]? = s.validators.data[i]?)
    (fresh : ∀ i, s.validators.data.size ≤ i → i < t.validators.data.size →
      x.state.validators.data[i]? = none) :
    retainedFundingPotential x t queue cutoff =
      fundingPotential t (queue ++ retainedSources x s cutoff) := by
  unfold retainedFundingPotential fundingPotential
  apply Finset.sum_congr rfl
  intro i member
  by_cases inside : i < s.validators.data.size
  · have virtual := retainedSources_any x cutoff within inside
    rw [← kept i inside] at virtual
    cases found : t.validators.data[i]? with
    | none => simp
    | some v =>
      rw [found] at virtual
      simp only [Option.map_some, Option.getD_some, List.any_append, virtual, Option.any_some,
        Bool.or_assoc]
  -- A new key is not a key of `x`, and every virtual source is an old key.
  have absent := fresh i (Nat.le_of_not_lt inside) (Finset.mem_range.mp member)
  have virtual : (retainedSources x s cutoff).any (fun c => c.sourceIndex.toNat == i) = false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨c, chosen, same⟩ := List.any_eq_true.mp hit
    obtain ⟨j, picked, rfl⟩ := List.mem_map.mp chosen
    have range := List.mem_range.mp (List.mem_filter.mp picked).1
    have equal : j = i := by simpa [toNat_toUInt64_of_lt within range] using same
    exact inside (equal ▸ range)
  simp only [absent, Option.any_none, Bool.false_and, Bool.or_false, List.any_append, virtual]

/-- The retained potential is the funded potential with the virtual sources queued. -/
private theorem retained_eq_funding {fork : Fork} (x : ForkedBeaconState preset)
    (s : BeaconState preset fork) (queue : List PendingConsolidation) (cutoff : Epoch)
    (within : s.RegistryWithinLimit) :
    retainedFundingPotential x s queue cutoff =
      fundingPotential s (queue ++ retainedSources x s cutoff) :=
  retained_eq_funding_after x s s queue cutoff within (fun _ _ => rfl)
    (fun _ low high => absurd high (Nat.not_lt.mpr low))

/-- The pass of pending consolidations, at `next`, does not raise the retained potential. -/
private theorem retained_pass_consolidations {fork : Fork} {next : Epoch}
    (x : ForkedBeaconState preset)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {queue : List PendingConsolidation} {s : BeaconState preset fork} {result}
    (ok : passPendingConsolidations next s queue = .ok result)
    -- Its cutoff is `next`, the epoch after the pass.
    (nextEq : next.toNat = (getCurrentEpoch s).toNat + 1)
    (distinct : (queue.map (·.sourceIndex)).Nodup)
    (sources : ∀ c ∈ queue, ∃ v, s.validators.data[c.sourceIndex.toNat]? = some v ∧
      v.activationEpoch ≤ getCurrentEpoch s ∧
      v.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
        v.withdrawableEpoch.toNat)
    (within : s.RegistryWithinLimit) :
    retainedFundingPotential x result.1 (queue.drop result.2) next ≤
      retainedFundingPotential x s queue next := by
  -- A retained key cannot withdraw at `next`, so the pass never moves it, and it keeps its support.
  --
  -- A slashed source leaves the queue, and keeps its retained cohort support if it has one.
  --
  -- The pass keeps the registry, so the virtual sources of its output are those of its input.
  have registry := (passPendingConsolidations_kept ok).1
  have resultWithin : result.1.RegistryWithinLimit := by
    simpa only [BeaconState.RegistryWithinLimit, registry] using within
  have same : retainedSources x result.1 next = retainedSources x s next := by
    unfold retainedSources
    rw [registry]
  rw [retained_eq_funding x _ _ next resultWithin, same, retained_eq_funding x s queue next within]
  refine funding_pass_consolidations_extra delay _ ok nextEq distinct sources fun d member => ?_
  -- Each virtual source is a key whose withdrawable epoch is after `next`.
  obtain ⟨i, chosen, rfl⟩ := List.mem_map.mp member
  obtain ⟨range, retained⟩ := List.mem_filter.mp chosen
  simp only [Bool.and_eq_true] at retained
  cases found : s.validators.data[i]? with
  | none => simp [found] at retained
  | some w =>
    simp only [found, Option.any_some, decide_eq_true_eq] at retained
    exact ⟨w, by simp [toNat_toUInt64_of_lt within (List.mem_range.mp range), found], retained.2⟩

/-- Pending deposits keep every old key of the registry, and only append new ones. -/
private theorem retained_pending_registry {fork : Fork} {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} (ok : processPendingDeposits config checks s electra = .ok t) :
    ∀ i, i < s.validators.data.size → t.validators.data[i]? = s.validators.data[i]? := by
  obtain ⟨_, _, applied, _, next, _, _, _, _, _, _, _, _, folded, rfl⟩ :=
    processPendingDeposits_applied ok
  refine foldlM_ok_invariant (fun u => ∀ i, i < s.validators.data.size →
      u.validators.data[i]? = s.validators.data[i]?) ?_ (fun _ _ => rfl) folded
  intro a deposit b prior credited i inside
  -- An old key is still in the registry before this deposit.
  have atA : i < a.validators.data.size := by
    by_contra outside
    have absent : a.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
    have present : s.validators.data[i]? ≠ none := by simp [inside]
    exact present ((prior i inside).symm.trans absent)
  rcases applyPendingDeposit_cases credited with rfl | ⟨_, raised⟩ | ⟨_, added⟩
  · exact prior i inside
  · rw [increaseBalance_validators raised]
    exact prior i inside
  · rw [addValidatorToRegistry_validators_eq_push added, Array.getElem?_push]
    simpa only [show i ≠ a.validators.data.size by omega, ↓reduceIte] using prior i inside

/-- The pending deposits raise the retained potential at cutoff `next` by a bounded amount.

The bound is one epoch of churn plus the credit to withdrawn sources of the queue.

A retained key cannot withdraw at the current epoch, so its deposits are applied within the churn.

The keys the deposits add are not keys of `x`, so they are never retained. -/
private theorem retained_pending_funded {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) {next : Epoch}
    (nextEq : next.toNat = (getCurrentEpoch s).toNat + 1)
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s)
    (activation : ∀ v ∈ s.validators.data, v.activationEpoch ≤ v.exitEpoch)
    (oldSize : x.state.validators.data.size ≤ s.validators.data.size)
    (ok : processPendingDeposits config checks s electra = .ok t) :
    retainedFundingPotential x t (fundingSources t) next +
        (t.depositBalanceToConsume electra).toNat ≤
      retainedFundingPotential x s (fundingSources s) next +
        (s.depositBalanceToConsume electra).toNat +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        withdrawnConsolidationCredit ⟨.deposits, ⟨fork, s⟩, ⟨fork, t⟩, 0, 0⟩ := by
  have within : s.RegistryWithinLimit := s.validators.bound early
  rw [retained_eq_funding_after x s t _ next within (retained_pending_registry ok)
      (fun i low _ => Array.getElem?_eq_none (by omega)),
    retained_eq_funding x s _ next within]
  refine funding_pending_funded_extra electra early matched ordered activation _ ?_ ok
  -- Each virtual source is a key whose withdrawable epoch is after `next`.
  intro d member v read
  obtain ⟨i, chosen, rfl⟩ := List.mem_map.mp member
  obtain ⟨range, retained⟩ := List.mem_filter.mp chosen
  rw [toNat_toUInt64_of_lt within (List.mem_range.mp range)] at read
  simp only [read, Bool.and_eq_true, Option.any_some, decide_eq_true_eq] at retained
  have later := UInt64.lt_iff_toNat_lt.mp retained.2
  omega

private theorem retained_epoch_change {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (queue : List PendingConsolidation) (cutoff : Epoch)
    (registry : t.validators = s.validators) (balances : t.balances = s.balances)
    (later : getCurrentEpoch s ≤ getCurrentEpoch t) :
    retainedFundingPotential x t queue cutoff ≤ retainedFundingPotential x s queue cutoff := by
  have bound := retainedFundingPotential_change x queue queue cutoff cutoff (fun _ => 0)
    (congrArg (·.data.size) registry) (fun i v w found read chosen => ?_)
    (fun i => by simp [effectiveAt, actualBalanceAt, registry, balances])
  · simpa using bound
  · have equal : w = v := Option.some.inj ((registry ▸ read).symm.trans found)
    subst w
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at chosen ⊢
    rcases chosen with ordinary | retained
    · rcases ordinary with active | queued
      · have prior := funding_lifecycle_support (ValidatorLifecycle.refl v)
          (UInt64.le_iff_toNat_le.mp later) active
        exact .inl (.inl prior)
      · exact .inl (.inr queued)
    · exact .inr retained

private theorem retained_slashings {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (queue : List PendingConsolidation) (cutoff : Epoch)
    (ok : processSlashings s = .ok t) :
    retainedFundingPotential x t queue cutoff ≤ retainedFundingPotential x s queue cutoff := by
  have registry : t.validators = s.validators := by rw [processSlashings_frame ok]
  have bound := retainedFundingPotential_balance_change x queue cutoff registry
    (frame_processSlashings ok).slot
  have zero : (∑ i ∈ Finset.range s.validators.data.size,
      (actualBalanceAt ⟨fork, t⟩ i - actualBalanceAt ⟨fork, s⟩ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases found : t.balances.data[i]? with
    | none => simp [actualBalanceAt, found]
    | some balance =>
      obtain ⟨before, read, below⟩ := balanceNotRaised_processSlashings ok i balance found
      simp only [actualBalanceAt, found, read, Option.map_some, Option.getD_some]
      exact Nat.sub_eq_zero_of_le (UInt64.le_iff_toNat_le.mp below)
  simpa only [zero, Nat.add_zero] using bound

private theorem retained_registry {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (queue : List PendingConsolidation) (cutoff : Epoch)
    (electra : .pectra ≤ fork) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (ok : processRegistryUpdates config s = .ok t) :
    retainedFundingPotential x t queue cutoff ≤ retainedFundingPotential x s queue cutoff := by
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp [getCurrentEpoch, (frame_processRegistryUpdates ok).slot]
  obtain ⟨kept, -⟩ := processRegistryUpdates_kept ok
  have balances := processRegistryUpdates_balances ok
  have life := registryLifecycle_processRegistryUpdates ok
  have bound := retainedFundingPotential_change x queue queue cutoff cutoff (fun _ => 0)
    (sameSizes_processRegistryUpdates ok).1 (fun i v w found read chosen => ?_) (fun i => ?_)
  · simpa using bound
  · -- The same key at the same position, with its lifecycle and its kept fields.
    obtain ⟨later, laterRead, lifecycle⟩ := life.validators i v found
    obtain rfl : later = w := Option.some.inj (laterRead.symm.trans read)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, epoch] at chosen ⊢
    have recent := fun (support : isActiveValidator later (getCurrentEpoch s) = true ∨
        getCurrentEpoch s < later.activationEpoch) =>
      funding_lifecycle_support lifecycle (Nat.le_refl _) support
    rcases chosen with ((active | future) | queued) | ⟨cohort, retained⟩
    · exact .inl (.inl (by simpa using recent (.inl active)))
    · rcases recent (.inr future) with active | future
      · exact .inl (.inl (.inl active))
      · exact .inl (.inl (.inr future))
    · exact .inl (.inr queued)
    by_cases unassigned : v.exitEpoch = FAR_FUTURE_EPOCH
    · -- With no exit yet, the key was active or still to activate.
      by_cases ahead : getCurrentEpoch s < v.activationEpoch
      · exact .inl (.inl (.inr ahead))
      · refine .inl (.inl (.inl ?_))
        simp [isActiveValidator, UInt64.not_lt.mp ahead, unassigned, finite]
    -- An assigned exit keeps its withdrawable epoch.
    obtain ⟨w', read', equal⟩ :=
      processRegistryUpdates_withdrawableEpoch_of_assigned electra ok i v found unassigned
    obtain rfl : w' = later := Option.some.inj (read'.symm.trans laterRead)
    exact .inr ⟨cohort, equal ▸ retained⟩
  · -- The balances and the effective balances are kept.
    have effective : effectiveAt ⟨fork, t⟩ i = effectiveAt ⟨fork, s⟩ i := by
      cases found : s.validators.data[i]? with
      | none =>
        have size := (sameSizes_processRegistryUpdates ok).1
        have outside := Array.getElem?_eq_none_iff.mp found
        have absent : t.validators.data[i]? = none := Array.getElem?_eq_none (by omega)
        simp [effectiveAt, found, absent]
      | some v =>
        obtain ⟨w, read, -, effective, -, -⟩ := kept i v found
        simp [effectiveAt, found, read, effective]
    simp [effective, actualBalanceAt, balances]

private theorem retained_rewards {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (queue : List PendingConsolidation) (cutoff : Epoch)
    (ok : processRewardsAndPenalties config s = .ok t)
    {events : List (BalanceEvent preset)}
    (replayed : replayRewards (config := config) (s, []) = .ok (t, events)) :
    retainedFundingPotential x t queue cutoff ≤ retainedFundingPotential x s queue cutoff +
      (events.map fundingCredit).sum := by
  have registry : t.validators = s.validators := by rw [processRewardsAndPenalties_frame ok]
  have bound := retainedFundingPotential_balance_change x queue cutoff registry
    (frame_processRewardsAndPenalties ok).slot
  exact bound.trans (Nat.add_le_add_left (funding_rewards_balance replayed) _)

private theorem retained_consolidations {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (holds : PendingConsolidationInvariant config s) {next : Epoch}
    (nextEq : next.toNat = (getCurrentEpoch s).toNat + 1)
    (ok : processPendingConsolidations s electra = .ok t) :
    retainedFundingPotential x t (fundingSources t) next ≤
      retainedFundingPotential x s (fundingSources s) next := by
  simp only [processPendingConsolidations, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨computed, computedOk, result, passed, rfl⟩ := ok
  have computedEq := (Uint64.addChecked_ok_iff.mp
    (mapError_ok_iff.mp (liftAccessor_ok.mp computedOk))).2
  have same : computed = next := UInt64.toNat_inj.mp (by simpa using computedEq.trans nextEq.symm)
  subst computed
  obtain ⟨distinct, sources⟩ := holds electra
  have bound := retained_pass_consolidations x delay passed nextEq distinct
    (fun c member => by
      obtain ⟨v, found, activated, ordered, -⟩ := sources c member
      exact ⟨v, found, activated, ordered⟩) (s.validators.bound early)
  simp only [fundingSources, electra, ↓reduceDIte]
  have takeEq : ((s.pendingConsolidations electra).data.toList.drop result.2).take
      ((s.pendingConsolidations electra).data.size - result.2) =
      (s.pendingConsolidations electra).data.toList.drop result.2 :=
    List.take_of_length_le (by simp)
  convert bound using 1
  simp only [retainedFundingPotential, Array.toList_extract, takeEq, effectiveAt, actualBalanceAt,
    getCurrentEpoch]
  congr 3

private theorem retained_stage {fork : Fork} {k : EpochStage} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (cutoff : Epoch)
    (edge : EpochStage.Edge config checks k s t)
    (other : k ≠ .rewards ∧ k ≠ .registry ∧ k ≠ .slashings ∧ k ≠ .pendingDeposits ∧
      k ≠ .pendingConsolidations ∧ k ≠ .effectiveBalances) :
    retainedFundingPotential x t (fundingSources t) cutoff =
      retainedFundingPotential x s (fundingSources s) cutoff := by
  obtain ⟨registry, balances, queue, _, slot⟩ := edge.records other
  simp only [retainedFundingPotential, fundingSources, registry, balances,
    effectiveAt, actualBalanceAt, getCurrentEpoch, slot, queue]
  rfl

private theorem retained_pending_balances {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s) (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (oldSize : x.state.validators.data.size ≤ s.validators.data.size) {next : Epoch}
    (nextEq : next.toNat = (getCurrentEpoch s).toNat + 1)
    (ok : processPendingBalances config checks s = .ok t) :
    ∃ deposited, processPendingDeposits config checks s electra = .ok deposited ∧
      processPendingConsolidations deposited electra = .ok t ∧
      retainedFundingPotential x t (fundingSources t) next +
          (t.depositBalanceToConsume electra).toNat ≤
        retainedFundingPotential x s (fundingSources s) next +
          (s.depositBalanceToConsume electra).toNat +
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
          withdrawnConsolidationCredit ⟨.deposits, ⟨fork, s⟩, ⟨fork, deposited⟩, 0, 0⟩ := by
  simp only [processPendingBalances, electra, ↓reduceDIte, bind_ok_iff] at ok
  obtain ⟨deposited, depositedOk, consolidatedOk⟩ := ok
  have deposit := retained_pending_funded x nextEq electra early matched ordered activation
    oldSize depositedOk
  have depositedNext : next.toNat = (getCurrentEpoch deposited).toNat + 1 := by
    simpa only [getCurrentEpoch, (frame_processPendingDeposits depositedOk).slot] using nextEq
  have consolidate := retained_consolidations x electra early delay
    (pending.pendingDeposits depositedOk) depositedNext consolidatedOk
  have carry := depositCarryLaws.processPendingConsolidations consolidatedOk
  refine ⟨deposited, depositedOk, consolidatedOk, ?_⟩
  rw [carry]
  omega

private theorem retained_before {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s) (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (oldSize : x.state.validators.data.size ≤ s.validators.data.size)
    (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) {next : Epoch}
    (nextEq : next.toNat = (getCurrentEpoch s).toNat + 1)
    (ok : epochBeforePayments config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (t, events)) :
    retainedFundingPotential x t (fundingSources t) next + fundingCarry ⟨fork, t⟩ ≤
      retainedFundingPotential x s (fundingSources s) next + fundingCarry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  apply funding_before_of (fun a => retainedFundingPotential x a (fundingSources a) next)
    (retained_stage x next) (fun {a b events} ok replayed => ?_)
    (fun {a b} slot ok => ?_) (fun {a b} ok => ?_)
    (fun electra slot size matched ordered activation pending ok => ?_)
    early matched ordered activation pending ok events replayed
  · have queue : fundingSources b = fundingSources a := by
      unfold fundingSources
      rw [processRewardsAndPenalties_frame ok]
    simpa only [queue] using retained_rewards x (fundingSources a) next ok replayed
  · have queue : fundingSources b = fundingSources a := by
      unfold fundingSources
      rw [(processRegistryUpdates_kept ok).2]
    have localFinite : getCurrentEpoch a < FAR_FUTURE_EPOCH := by
      simpa only [getCurrentEpoch, slot] using finite
    simpa only [queue] using retained_registry x (fundingSources a) next electra localFinite ok
  · have queue : fundingSources b = fundingSources a := by
      unfold fundingSources
      rw [processSlashings_frame ok]
    simpa only [queue] using retained_slashings x (fundingSources a) next ok
  · exact retained_pending_balances x electra early delay matched ordered activation pending
      (oldSize.trans size) (by simpa only [getCurrentEpoch, slot] using nextEq) ok

private theorem retained_epoch {fork : Fork} {s t middle : BeaconState preset fork}
    (x : ForkedBeaconState preset) (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch s) (ordered : ExitsOrdered s) (activation : ActivationExitOrder s)
    (pending : PendingConsolidationInvariant config s)
    (oldSize : x.state.validators.data.size ≤ s.validators.data.size)
    (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) {next : Epoch}
    (nextEq : next.toNat = (getCurrentEpoch s).toNat + 1)
    (ok : processEpoch config checks s = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : epochBalanceReplay (config := config) (checks := checks) s = .ok (middle, events)) :
    retainedFundingPotential x t (fundingSources t) next + fundingCarry ⟨fork, t⟩ ≤
      retainedFundingPotential x s (fundingSources s) next + fundingCarry ⟨fork, s⟩ +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  apply funding_epoch_of (fun a => retainedFundingPotential x a (fundingSources a) next)
    (retained_stage x next)
    (fun events ok replayed => retained_before x electra early delay matched ordered activation
      pending oldSize finite nextEq ok events replayed)
    (fun {a b} matched ok => ?_) early matched ok events replayed
  have queue : fundingSources b = fundingSources a := by
    unfold fundingSources
    rw [(show EpochStage.Edge config checks .effectiveBalances a b from ok).samePendingQueue nofun]
  simpa only [queue] using
    retainedFundingPotential_effective_updates x (fundingSources a) next matched ok

private theorem reached_exit_delay {g x z : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (pre : Run config checks x z)
    (genesis : Genesis (config := config) (checks := checks) g)
    (guard : aprioriGuardAt config x high) :
    ∀ (i : Nat) (v : Validator), z.state.validators.data[i]? = some v →
      v.exitEpoch ≠ FAR_FUTURE_EPOCH → v.exitEpoch.toNat + 2 ≤ v.withdrawableEpoch.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, delay, -, -, -, -⟩ := guard
  intro i v found assigned
  have delayed := (shared.append pre).exit_withdrawable_delay genesis i v found assigned
  omega

private theorem finite_of_earlier {z y : ForkedBeaconState preset}
    (before : (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat) :
    getCurrentEpoch z.state < FAR_FUTURE_EPOCH := by
  have bound := (getCurrentEpoch y.state).toNat_lt
  rw [UInt64.lt_iff_toNat_lt]
  change _ < 2 ^ 64 - 1
  change _ < 2 ^ 64 at bound
  omega

private theorem retained_credits_le_allowance {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fundingCredit).sum ≤ sourceCredits .rewards events + sourceCredits .sync events +
      whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
        (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
        (driftHorizon x high) (preElectraEpochs config x high) := by
  rw [fundingCredit_sum]
  exact Nat.add_le_add_left (otherCredit_le_allowance_electra shared genesis tail caps aligned
    electra early twoSlots high endEpoch guard replayed) _

private theorem retained_upgrades {s t : ForkedBeaconState preset}
    (x : ForkedBeaconState preset) (cutoff : Epoch)
    (electra : .pectra ≤ s.fork) (early : t.fork < .glamsterdam)
    (ok : processUpgrades config checks s = .ok t) :
    retainedFundingPotential x t.state (fundingSources t.state) cutoff =
      retainedFundingPotential x s.state (fundingSources s.state) cutoff := by
  have target : .pectra ≤ t.fork := Nat.le_trans electra (processUpgrades_fork_le ok)
  obtain ⟨registry, balances, pending⟩ := processUpgrades_retained_data electra early ok target
  simp only [retainedFundingPotential, fundingSources, electra, target, ↓reduceDIte,
    registry, effectiveAt, actualBalanceAt, balances, pending, getCurrentEpoch,
    processUpgrades_slot ok]
  rfl

private theorem retained_slot {a b : ForkedBeaconState preset}
    (x : ForkedBeaconState preset) (electra : .pectra ≤ a.fork)
    (early : b.fork < .glamsterdam)
    (delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (matched : BalancesMatch a.state) (ordered : ExitsOrdered a.state)
    (activation : ActivationExitOrder a.state)
    (pending : PendingConsolidationInvariant config a.state)
    (oldSize : x.state.validators.data.size ≤ a.state.validators.data.size)
    (ok : advanceSlotAcross config checks a = .ok b)
    (events : List (BalanceEvent preset))
    (replayed : (Step.slot ok).balanceEvents = .ok events) :
    retainedFundingPotential x b.state (fundingSources b.state) (getCurrentEpoch b.state) +
        fundingCarry b ≤
      retainedFundingPotential x a.state (fundingSources a.state) (getCurrentEpoch a.state) +
        fundingCarry a +
        ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have bound : retainedFundingPotential x b.state (fundingSources b.state)
        (getCurrentEpoch b.state) + fundingCarry b ≤
      retainedFundingPotential x a.state (fundingSources a.state) (getCurrentEpoch b.state) +
        fundingCarry a +
        ((getCurrentEpoch b.state).toNat - (getCurrentEpoch a.state).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
    apply funding_slot_of (x := a) (y := b)
      (fun u => retainedFundingPotential x u.state (fundingSources u.state)
        (getCurrentEpoch b.state))
      (fun cachedOk => by obtain ⟨_, _, _, _, eq⟩ := processSlot_ok cachedOk; rw [eq]; rfl)
      (fun s next later => ?_)
      (fun {advanced} upgrades =>
        (retained_upgrades (s := ⟨a.fork, advanced⟩) x _ electra early upgrades).le)
      (fun {cached epoched} cachedOk nextEq epochOk middle added replay => ?_)
      early ok events replayed
    · exact retained_epoch_change x (fundingSources s) _ rfl rfl (by
        rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
        exact Nat.div_le_div_right later)
    · obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
      have before : a.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (Step.slot ok).chainStep.fork_le early
      have finite : getCurrentEpoch cached < FAR_FUTURE_EPOCH :=
        finite_of_earlier (z := ⟨a.fork, cached⟩) (y := b) (by
          change (getCurrentEpoch cached).toNat < (getCurrentEpoch b.state).toNat
          omega)
      exact retained_epoch x electra before delay
        ((frame_processSlot cachedOk).balancesMatch matched)
        ((frame_processSlot cachedOk).exitsOrdered ordered)
        (by rw [cachedEq]; exact activation) (by rw [cachedEq]; exact pending)
        (by rw [cachedEq]; exact oldSize) finite nextEq epochOk added replay
  have cutoff := retainedFundingPotential_cutoff_mono x a.state (fundingSources a.state)
    (Step.slot ok).chainStep.currentEpoch_le
  omega

/-- A key retained after a block was retained before it, at a cutoff by the block's epoch.

The key is a key of `x`, so it was already in the registry before the block.

A slashed key is past the cutoff by `slashedBound`.

An unslashed key that could withdraw by the cutoff had exited by then, so the block keeps it. -/
private theorem retained_block_sources {fork : Fork} {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (x : ForkedBeaconState preset) (cutoff : Epoch)
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (ok : processBlock config checks engine s block = .ok t)
    (ordered : ExitsOrdered s)
    (oldSize : x.state.validators.data.size ≤ s.validators.data.size)
    (cutoffLe : cutoff ≤ getCurrentEpoch s)
    (slashedBound : ∀ (i : Nat) (v : Validator), (x.state.validators.data[i]?).any (fun old =>
        isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) = true →
      s.validators.data[i]? = some v → v.slashed = true → cutoff < v.withdrawableEpoch) :
    ∀ c ∈ retainedSources x t cutoff, c ∈ retainedSources x s cutoff := by
  intro c member
  obtain ⟨i, chosen, rfl⟩ := List.mem_map.mp member
  obtain ⟨range, retained⟩ := List.mem_filter.mp chosen
  simp only [Bool.and_eq_true] at retained
  obtain ⟨cohort, later⟩ := retained
  -- A key of `x` is an old key of the registry.
  have inside : i < s.validators.data.size := by
    cases old : x.state.validators.data[i]? with
    | none => simp [old] at cohort
    | some _ => exact Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp old).1 oldSize
  have found : s.validators.data[i]? = some s.validators.data[i] := by simp [inside]
  obtain ⟨w, read, -⟩ := processBlock_validatorCap_mono order ok i _ found
  simp only [read, Option.any_some, decide_eq_true_eq] at later
  have before : cutoff < s.validators.data[i].withdrawableEpoch := by
    by_cases slashed : s.validators.data[i].slashed = true
    · exact slashedBound i _ cohort found slashed
    · -- Otherwise the block keeps a key that could already withdraw by the cutoff.
      apply UInt64.not_le.mp
      intro withdrawn
      have reached := UInt64.le_trans withdrawn cutoffLe
      have exited := UInt64.le_trans (ordered _ (Array.getElem_mem inside)) reached
      have kept := processBlock_retired_validator order ok i _ w found read exited
        (Bool.eq_false_iff.mpr slashed) reached
      rw [kept.2.2] at later
      exact absurd later (UInt64.not_lt.mpr withdrawn)
  refine List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr inside, ?_⟩, rfl⟩
  simp only [cohort, found, Option.any_some, before, Bool.and_self, decide_true]

/-- A block raises the retained potential, at a cutoff by its epoch, by at most its funding credits.

Both potentials are the funded potential with the virtual sources of the start queued.

Every virtual source after the block was one before it, and the block keeps fixed supports. -/
private theorem retained_block {fork : Fork} {s t : BeaconState preset fork}
    (x : ForkedBeaconState preset) (cutoff : Epoch) (early : fork < .glamsterdam)
    (matched : BalancesMatch s)
    (order : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok (t, events))
    (ordered : ExitsOrdered s)
    (oldSize : x.state.validators.data.size ≤ s.validators.data.size)
    (cutoffLe : cutoff ≤ getCurrentEpoch s)
    (slashedBound : ∀ (i : Nat) (v : Validator), (x.state.validators.data[i]?).any (fun old =>
        isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) = true →
      s.validators.data[i]? = some v → v.slashed = true → cutoff < v.withdrawableEpoch) :
    retainedFundingPotential x t (fundingSources t) cutoff ≤
      retainedFundingPotential x s (fundingSources s) cutoff + (events.map fundingCredit).sum := by
  have within : s.RegistryWithinLimit := s.validators.bound early
  have tWithin : t.RegistryWithinLimit := t.validators.bound early
  have sources := retained_block_sources x cutoff order ok ordered oldSize cutoffLe slashedBound
  have bound := funding_block_extra (extra := retainedSources x s cutoff) early matched engine
    block ok events replayed
  have carry := depositCarry_processBlock ok
  have same : fundingCarry ⟨fork, t⟩ = fundingCarry ⟨fork, s⟩ := by
    simp only [fundingCarry, carry]
  have fewer : fundingPotential t (fundingSources t ++ retainedSources x t cutoff) ≤
      fundingPotential t (fundingSources t ++ retainedSources x s cutoff) :=
    fundingPotential_mono t fun c member => by
      rcases List.mem_append.mp member with queued | virtual
      · exact List.mem_append.mpr (.inl queued)
      · exact List.mem_append.mpr (.inr (sources c virtual))
  rw [retained_eq_funding x t _ cutoff tWithin, retained_eq_funding x s _ cutoff within]
  omega

/-- Take a branch from `x` within its window.

On it, a cohort key slashed by `s` is past any cutoff by `high + 1`.

The key was unslashed at `x`, so its new slashing delays withdrawal by the slashings vector.

The guard keeps the window below half that vector. -/
private theorem retained_slashed_bound {x s : ForkedBeaconState preset} {high : Nat}
    (pre : Run config checks x s) (caps : CapOrder preset)
    (guard : aprioriGuardAt config x high) (cutoff : Epoch) (cutoffLe : cutoff.toNat ≤ high + 1) :
    ∀ (i : Nat) (v : Validator), (x.state.validators.data[i]?).any (fun old =>
        isActiveValidator old (getCurrentEpoch x.state) && !old.slashed) = true →
      s.state.validators.data[i]? = some v → v.slashed = true → cutoff < v.withdrawableEpoch := by
  obtain ⟨-, -, -, -, -, -, -, -, -, delay, short, -, -, -⟩ := guard
  intro i v cohort found slashed
  cases old : x.state.validators.data[i]? with
  | none => simp [old] at cohort
  | some u =>
    simp only [old, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at cohort
    have lower := pre.newly_slashed_withdrawableEpoch caps
      (by omega) i u v old found cohort.2 slashed
    rw [UInt64.lt_iff_toNat_lt]
    unfold driftHorizon at short
    omega

/-- Take a block of a branch from `x` within its window, and a cutoff by the block's epoch.

The block raises the retained potential at that cutoff by at most its funding credits. -/
private theorem retained_block_reachable {g x : ForkedBeaconState preset} {high : Nat}
    {fork : Fork} {s t : BeaconState preset fork}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (pre : Run config checks x ⟨fork, s⟩) (caps : CapOrder preset)
    (guard : aprioriGuardAt config x high) (early : fork < .glamsterdam)
    (engine : ExecutionEngine preset fork) (block : BeaconBlock preset fork)
    (ok : processBlock config checks engine s block = .ok t)
    (events : List (BalanceEvent preset))
    (replayed : blockBalanceReplay (config := config) (checks := checks)
      early engine s block = .ok (t, events))
    (cutoff : Epoch) (cutoffLe : cutoff ≤ getCurrentEpoch s)
    (endEpoch : (getCurrentEpoch s).toNat ≤ high + 1) :
    retainedFundingPotential x t (fundingSources t) cutoff ≤
      retainedFundingPotential x s (fundingSources s) cutoff + (events.map fundingCredit).sum := by
  have holds := (run_justified_separated (shared.append pre) genesis).1
  exact retained_block x cutoff early holds.balancesMatch caps.compounding engine block ok events
    replayed holds.exitsOrdered (registryGrows_of_chainSteps pre.chainSteps) cutoffLe
    (retained_slashed_bound pre caps guard cutoff
      ((UInt64.le_iff_toNat_le.mp cutoffLe).trans endEpoch))

end

private theorem retained_run_bound {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (tail : Run config checks x y) (caps : CapOrder preset)
    (electra : .pectra ≤ x.fork) (early : y.fork < .glamsterdam)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    retainedFundingPotential x y.state (fundingSources y.state) (getCurrentEpoch y.state) +
        fundingCarry y ≤
      fundedStake x + fundingCarry x +
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (events.map fundingCredit).sum := by
  have delay : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := guard.2.2.2.2.2.2.2.2.2.1
  have bound := funding_run_bound_of
    (fun u => retainedFundingPotential x u.state (fundingSources u.state)
      (getCurrentEpoch u.state) + fundingCarry u) (fun _ => 0) fundingCredit
    tail early high endEpoch events replayed (fun {a b} pre step before bWithin added addedOk => by
      have reached := shared.append pre
      have holds := (run_justified_separated reached genesis).1
      have aEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le before
      have aElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      have within : (getCurrentEpoch a.state).toNat ≤ high + 1 := by
        have := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
        omega
      cases step with
      | slot ok =>
        simpa using retained_slot x aElectra before delay holds.balancesMatch holds.exitsOrdered
          (reached.activationExitOrder genesis)
          (fun witness => reached.pendingConsolidation_invariant genesis witness (by omega))
          (registryGrows_of_chainSteps pre.chainSteps) ok added addedOk
      | @block fork s t engine signed due ok =>
        have processed := (applySignedBlock_ok ok).2.1
        have result := retained_block_reachable shared genesis pre caps guard before engine
          signed.message processed added (Step.balanceEvents_block before addedOk)
          (getCurrentEpoch s) (UInt64.le_refl _) within
        have carry := depositCarry_processBlock processed
        have slot := (frame_processBlock processed).slot
        have spent : (added.map fun _ => (0 : Nat)).sum = 0 := by simp
        simpa only [getCurrentEpoch, slot, fundingCarry, carry, spent,
          Nat.sub_self, Nat.zero_mul, Nat.add_zero, Nat.add_right_comm] using
          Nat.add_le_add_right result (fundingCarry ⟨fork, s⟩))
  simp only [List.map_const', List.sum_replicate,
    retainedFundingPotential_initial, fundingPotential_eq] at bound
  exact bound

private theorem retained_anchor_le_ceiling {g x r : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (pre : Run config checks x r) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (early : r.fork < .glamsterdam)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch r.state).toNat ≤ high + 1)
    (guard : aprioriGuardAt config x high)
    {before : List (BalanceEvent preset)} (beforeOk : pre.balanceEvents high = .ok before)
    (issued : sourceCredits .rewards before + sourceCredits .sync before ≤
      ∑ s ∈ Finset.range (ix x r), 2 *
          preset.epochIssuanceBeforeAltair (stakeCeilingAt config x high s)) :
    retainedFundingPotential x r.state (fundingSources r.state) (getCurrentEpoch r.state) ≤
      stakeCeilingAt config x high (ix x r) := by
  have conserved := retained_run_bound shared genesis pre caps electra early high endEpoch guard
    beforeOk
  have credit := retained_credits_le_allowance shared genesis pre caps aligned electra early
    twoSlots high endEpoch guard beforeOk
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by simp [preElectraEpochs, notBefore]
  have base : fundedStake x + previousOnlyStake x + fundingCarry x +
      whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
          (unassignedPreStake x)
        (fundingCarry x) (exitedSlashableCount x) (driftHorizon x high) 0 ≤
      stakeCeilingAt config x high 0 := by
    simp only [stakeCeilingAt, stakeCeiling, zero, Nat.lt_irrefl, ↓reduceIte, Nat.le_refl]
  have grows (t : Nat) : stakeCeilingAt config x high t +
      2 * preset.epochIssuanceBeforeAltair (stakeCeilingAt config x high t) +
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ≤
      stakeCeilingAt config x high (t + 1) := by
    simp [stakeCeilingAt, stakeCeiling, zero]
  have ceiling := ceiling_ge (config := config) (stakeCeilingAt config x high) base grows (ix x r)
  simp only [zero] at credit
  change _ ≤ _ + ix x r * _ + _ at conserved
  omega

section

open Cryptography.Bls Uint64

/-- Let `r` be a state earlier than a state `z`, in the same epoch.

Then the eligible stake of the cohort at `z` is at most the retained potential at `r`.

The retained potential uses the cutoff at that epoch. -/
private theorem eligible_le_retained_anchor {g x r z y : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (guard : aprioriGuardAt config x high) (_electra : .pectra ≤ x.fork)
    (pre : Run config checks x r) (inner : Run config checks r z) (post : Run config checks z y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch z.state = getCurrentEpoch r.state)
    (before : (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1) :
    (∑ i ∈ penaltyCohort x, eligibleWeight z.state i) ≤
      retainedFundingPotential x r.state (fundingSources r.state) (getCurrentEpoch r.state) := by
  -- Within one epoch the effective balances of old keys stay fixed, so each weight is read at `r`.
  --
  -- A key eligible at `z` is active there, or not yet withdrawable.
  --
  -- An active key at `z` is active or still pending activation at `r`.
  --
  -- The reason is that an assigned exit never moves.
  --
  -- A key not yet withdrawable at `z` was not withdrawable at `r` either.
  --
  -- If it was slashed at `r`, its slashing pushed withdrawal past the window.
  --
  -- Otherwise a key that could withdraw by `r` keeps that withdrawable epoch through the epoch.
  have zEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) zEarly
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) rEarly
  have sizes := registryGrows_of_chainSteps pre.chainSteps
  have finite := finite_of_earlier before
  rw [same] at finite before
  have ordered := reached_exit_delay shared (pre.append inner) genesis guard
  have effective := run_same_epoch_effective inner same
  have exits := (run_justified_separated (shared.append pre) genesis).1.exitsOrdered
  have slashedBound := retained_slashed_bound pre caps guard (getCurrentEpoch r.state)
    (by omega)
  have inside : ∀ i ∈ penaltyCohort x, i < r.state.validators.data.size := fun i member =>
    Nat.lt_of_lt_of_le (penaltyCohort_inside xEarly member) sizes
  apply retainedFundingPotential_eligible_le x z.state r.state _ _ _ inside
  intro i member w foundZ eligible
  have cohort := penaltyCohort_cohort xEarly member
  obtain ⟨v, foundR⟩ : ∃ v, r.state.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem (inside i member)⟩
  obtain ⟨w', foundZ', kept⟩ := inner.registryLifecycle.validators i v foundR
  obtain rfl : w' = w := Option.some.inj (foundZ'.symm.trans foundZ)
  have live := eligible_active_or_withdrawable (s := z.state)
    (by rw [same]; exact finite) (ordered i w' foundZ) eligible
  rw [same] at live
  refine ⟨v, foundR, ?_, ?_⟩
  · rcases live with active | notWithdrawable
    · -- An exit assigned by `r` is the exit at `z`, which is after the epoch.
      by_cases activeR : isActiveValidator v (getCurrentEpoch r.state) = true
      · simp [activeR]
      by_cases pending : getCurrentEpoch r.state < v.activationEpoch
      · simp [pending]
      exfalso
      have bounds : w'.activationEpoch ≤ getCurrentEpoch r.state ∧
          getCurrentEpoch r.state < w'.exitEpoch := by
        simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using active
      have exited : v.exitEpoch ≤ getCurrentEpoch r.state := by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, not_and,
          UInt64.not_lt] at activeR
        exact activeR (UInt64.not_lt.mp pending)
      have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far =>
        absurd (UInt64.lt_of_le_of_lt exited finite) (by rw [far]; exact UInt64.lt_irrefl _)
      rw [kept.exitEpoch assigned] at bounds
      exact absurd (UInt64.lt_of_lt_of_le bounds.2 exited) (UInt64.lt_irrefl _)
    · -- A key of the cohort not withdrawable at `z` was not withdrawable at `r`.
      have later : getCurrentEpoch r.state < v.withdrawableEpoch := by
        by_cases slashed : v.slashed = true
        · exact slashedBound i v cohort foundR slashed
        apply UInt64.not_le.mp
        intro withdrawn
        have exited := UInt64.le_trans (exits _ (Array.mem_of_getElem? foundR)) withdrawn
        have stays := inner.retired_validator caps
          i v w' foundR foundZ exited (Bool.eq_false_iff.mpr slashed) withdrawn
        rw [stays.2.2] at notWithdrawable
        exact absurd (UInt64.lt_of_lt_of_le notWithdrawable withdrawn) (UInt64.lt_irrefl _)
      simp [cohort, later]
  · -- Within one epoch the effective balance of an old key is the one at `r`.
    rw [← effective i (inside i member)]
    simp [effectiveAt, foundZ]

/-- A branch splits at the first state of the epoch of its end.

Every step before the split starts at an earlier epoch.

Within one epoch the split is the start of the branch. -/
private theorem epoch_anchor {x u : ForkedBeaconState preset} (tail : Run config checks x u)
    (early : u.fork < .glamsterdam) :
    ∃ (r : ForkedBeaconState preset) (pre : Run config checks x r)
      (inner : Run config checks r u), tail = pre.append inner ∧
      getCurrentEpoch u.state = getCurrentEpoch r.state ∧
      ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b), pre.Contains step →
        (getCurrentEpoch a.state).toNat < (getCurrentEpoch r.state).toNat := by
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  by_cases same : getCurrentEpoch u.state = getCurrentEpoch x.state
  · exact ⟨x, .nil, tail, tail.nil_append.symm, same, fun _ member => by cases member⟩
  have later : (getCurrentEpoch x.state).toNat < (getCurrentEpoch u.state).toNat := by
    exact Nat.lt_of_le_of_ne order fun equal => same (UInt64.toNat_inj.mp equal.symm)
  obtain ⟨r, pre, inner, split, inside, outside, -, begins⟩ :=
    window_cut tail early ((getCurrentEpoch u.state).toNat - 1)
  have upper := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps inner.chainSteps)
  -- The split is at the epoch of `u`, or it is `u` itself.
  have epochR : getCurrentEpoch u.state = getCurrentEpoch r.state := by
    rcases begins with after | empty
    · exact UInt64.toNat_inj.mp (by omega)
    · cases inner with
      | nil => rfl
      | snoc _ step => exact absurd (Run.Contains.last _ step) (empty step)
  refine ⟨r, pre, inner, split, epochR, fun step member => ?_⟩
  have low := inside step member
  rw [← epochR]
  omega

/-- From the guard, the window ends well below the far-future epoch.

An epoch is a slot divided by at least two slots, so it is below `2^63`.

The window after the start is shorter than half the slashings vector. -/
private theorem window_below_far {x : ForkedBeaconState preset} {high : Nat}
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (guard : aprioriGuardAt config x high) :
    high + 1 < FAR_FUTURE_EPOCH.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, short, -, -, -⟩ := guard
  have vector := preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat_lt
  have slot := x.state.slot.toNat_lt
  have epoch : (getCurrentEpoch x.state).toNat ≤ x.state.slot.toNat / 2 := by
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_left twoSlots (by decide)
  have half : x.state.slot.toNat / 2 < 2 ^ 63 := by omega
  unfold driftHorizon at short
  change high + 1 < 2 ^ 64 - 1
  omega

/-- The floor at epoch `t` of the window is its start less the penalties of `t` epochs. -/
private theorem floorAt_eq (x : ForkedBeaconState preset) (high : Nat) :
    ∀ t, stakeFloorAt config x high t = stakeFloorAt config x high 0 -
        windowPenalties (config := config) x high t
  | 0 => by simp [windowPenalties]
  | t + 1 => by
    rw [penalties_succ, ← Nat.sub_sub, ← floorAt_eq x high t]
    show stakeFloorAt config x high t - 0 -
        epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high t + slashedUnwithdrawnStake x) (stakeFloorAt config x high t)
            t = _
    rw [Nat.sub_zero]

/-- The unslashed active stake at `x` is at most the effective stake of the cohort.

With distinct keys, a key active at `x` names one validator.

That validator is unslashed exactly when its key is. -/
private theorem unslashed_le_cohort {x : ForkedBeaconState preset}
    (early : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    referenceStake x - slashedActiveStake x ≤ ∑ i ∈ penaltyCohort x, effectiveAt x i := by
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ :=
      (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have nodup := (getActiveValidatorIndices_sorted (x.state.validators.bound early)
    (getCurrentEpoch x.state)).imp
    (fun {a b} less (same : a = b) => by subst same; exact UInt64.lt_irrefl _ less)
  have value : Models.stake (effectiveWeight x.state) (unslashedKeys x.state) =
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map fun i =>
        if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
          else effectiveAt x i.toNat).sum := by
    unfold Models.stake unslashedKeys activeKeys
    rw [Finset.sum_filter, keys_sum x.state _ unique inside, List.sum_toFinset _ nodup]
    congr 1
    refine List.map_congr_left fun i member => ?_
    obtain ⟨v, found⟩ : ∃ v, x.state.validators.data[i.toNat]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (inside i member)⟩
    have mem := Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
    cases slashed : v.slashed
    · simp [found, slashed, not_slashedAt unique mem slashed, effectiveWeight_of_member unique mem,
        effectiveAt]
    · simp [found, slashed, show SlashedAt x.state v.pubkey from ⟨v, mem, rfl, slashed⟩]
  unfold slashedActiveStake
  rw [value]
  have bound := producer_le_cohort x early (effectiveAt x)
  omega

/-- The cohort has at most as many keys as `x` has active keys. -/
private theorem cohort_card_le {x : ForkedBeaconState preset}
    (early : x.fork < .glamsterdam) (unique : PubkeysDistinct x.state) :
    (penaltyCohort x).card ≤ referenceCount x := by
  have inside : ∀ i ∈ getActiveValidatorIndices x.state (getCurrentEpoch x.state),
      i.toNat < x.state.validators.data.size := fun i member => by
    obtain ⟨v, found, _⟩ :=
      (mem_getActiveValidatorIndices (x.state.validators.bound early)).mp member
    exact (Array.getElem?_eq_some_iff.mp found).1
  have count : referenceCount x =
      ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset).card := by
    unfold referenceCount activeKeys
    rw [Finset.card_eq_sum_ones, keys_sum x.state _ unique inside (fun _ => 1),
      Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun i member => ?_
    simp [Array.getElem?_eq_getElem (inside i (List.mem_toFinset.mp member))]
  rw [count]
  exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

/-- The sum over a list is the sum over its positions, by Mathlib's `Fin` sums. -/
theorem list_map_sum_range {α : Type} (l : List α) (g : α → Nat) :
    (l.map g).sum = ∑ i ∈ Finset.range l.length, (l[i]?.map g).getD 0 := by
  rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- Let `r` be the first state of an epoch, at any fork.

Given the budgets of its keys, the total active balance at `r` is at least the floor there. -/
private theorem anchor_floor_core {g x r : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (pre : Run config checks x r)
    (supported : Supported shared pre high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (producer : ∀ {y : ForkedBeaconState preset},
      FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    -- The keys select stops and prefixes of the replay, and the budgets are read only there.
    --
    -- The budgets are of three kinds.
    (stops : (i : Nat) → Stop pre i)
    {events : List (BalanceEvent preset)} (replayed : pre.balanceEvents high = .ok events)
    -- The first fits the charges with the partial withdrawals.
    (joint : ∀ (keys carrier : Finset Nat) (charge : Nat → Nat)
        (parts : Nat → List (BalanceEvent preset)), keys ⊆ penaltyCohort x →
      (∀ i ∈ carrier, ∃ c, (stops i).charge = some c ∧ charge i = c.amount ∧ c.epoch ≤ high + 1) →
      (∀ i ∈ keys, parts i <+: events) →
      (∑ i ∈ carrier, charge i) +
        (∑ i ∈ keys, ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
          departureBudgetAt (config := config) x high +
              duePartialWithdrawals x (driftHorizon x high))
    -- The second fits the penalty debits.
    (penalty : (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      windowPenalties (config := config) x high (ix x r))
    -- The third fits the slashing penalties.
    (slashing : ∀ (keys : Finset Nat) (flag : Nat → Bool), keys ⊆ penaltyCohort x →
      (∑ i ∈ keys,
            if flag i then base x i / minSlashingPenaltyQuotient preset
          (preElectraEpochs config x high)
        else 0) ≤ stakeCeilingAt config x high (driftHorizon x high + 1) /
          minSlashingPenaltyQuotient preset (preElectraEpochs config x high))
    {total : Gwei} (computed : getTotalActiveBalance r.state = .ok total) :
    stakeFloorAt config x high (ix x r) ≤ total.toNat := by
  -- The floor starts from the unslashed active stake at `x` and subtracts every way it can leave.
  --
  -- Each key of the cohort that is not scheduled to exit at `x` falls in one of two cases.
  --
  -- Take a key whose exit at `r` is after the window.
  --
  -- At `r` it keeps its stake less its slack, debits, any slashing penalty and one increment.
  --
  -- This follows from the balance floor of one key over the branch to `r`.
  --
  -- A key whose exit at `r` is within the window was given that exit on the branch.
  --
  -- The step that set it charged the departure queue its effective balance then.
  --
  -- That balance meets the same bound by the balance floor of one key over the branch to that step.
  have support := supported
  obtain ⟨genesis, parameters, caps, aligned, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) early
  have far := window_below_far twoSlots guard
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  -- A part of the branch to `r` is supported too.
  have prefixSupported : ∀ {m : ForkedBeaconState preset} (head : Run config checks x m),
      Run config checks m r → Supported shared head high := fun head post =>
    ⟨genesis, parameters, caps, aligned,
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early,
      (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)).trans
        endEpoch, guard⟩
  -- The keys of the cohort scheduled to exit within the window at `x`, and the others.
  let S := (penaltyCohort x).filter fun i => (x.state.validators.data[i]?).any fun v =>
    decide (v.exitEpoch.toNat ≤ horizonEnd x high)
  let R := (penaltyCohort x).filter fun i => ¬ (x.state.validators.data[i]?).any fun v =>
    decide (v.exitEpoch.toNat ≤ horizonEnd x high)
  have cohort : ∀ i ∈ penaltyCohort x, ∃ v, x.state.validators.data[i]? = some v ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false := by
    intro i member
    have chosen := penaltyCohort_cohort xEarly member
    cases found : x.state.validators.data[i]? with
    | none => simp [found] at chosen
    | some v =>
      simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at chosen
      exact ⟨v, rfl, chosen⟩
  -- Each other key meets the bound of `FloorProducer`, at `r` or at the step that set its exit.
  have key : ∀ i, ∃ (part : List (BalanceEvent preset)) (kept charged : Nat) (flag : Bool),
      i ∈ R → part <+: events ∧
        effectiveAt x i ≤ kept + charged + (effectiveAt x i - actualBalanceAt x i) +
          (part.map (floorPenaltyDebit i)).sum +
          (part.map (floorPartialDebit (UInt64.ofNat i))).sum +
          (if flag then base x i / minSlashingPenaltyQuotient preset
                (preElectraEpochs config x high) else 0) +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        (kept = 0 ∨ ∃ w, r.state.validators.data[i]? = some w ∧
          isActiveValidator w (getCurrentEpoch r.state) = true ∧ kept = effectiveAt r i) ∧
        (charged = 0 ∨ ∃ c, (stops i).charge = some c ∧ charged = c.amount ∧
          c.epoch ≤ high + 1) := by
    intro i
    by_cases member : i ∈ R
    swap
    · exact ⟨[], 0, 0, false, fun inside => absurd inside member⟩
    obtain ⟨inCohort, notScheduled⟩ := Finset.mem_filter.mp member
    obtain ⟨v, found, active, unslashed⟩ := cohort i inCohort
    simp only [found, Option.any_some, decide_eq_true_eq] at notScheduled
    have bounds : v.activationEpoch ≤ getCurrentEpoch x.state ∧
        getCurrentEpoch x.state < v.exitEpoch := by
      simpa only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] using active
    have set := Consensus.Internal.assigned_of_active active
    obtain ⟨w, foundR, life⟩ := pre.registryLifecycle.validators i v found
    have round (tail : Run config checks x r) (j : Nat) :
        (if FirstDown tail j then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      split <;> omega
    by_cases later : high + 1 < w.exitEpoch.toNat
    · -- The key is still active at `r`.
      have bound := producer shared pre high support twoSlots events replayed i v w found foundR
        unslashed set later
      have activeR : isActiveValidator w (getCurrentEpoch r.state) = true := by
        have start := UInt64.le_iff_toNat_le.mp (show w.activationEpoch ≤ getCurrentEpoch x.state
          from (life.activationEpoch set).symm ▸ bounds.1)
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
        omega
      have once := round pre i
      refine ⟨events, effectiveAt r i, 0, w.slashed, fun _ =>
        ⟨List.prefix_refl _, by unfold base; omega, .inr ⟨w, foundR, activeR, rfl⟩, .inl rfl⟩⟩
    · -- The exit of the key was set on the branch, within the window.
      have unset : v.exitEpoch = FAR_FUTURE_EPOCH := by
        by_contra assigned
        rw [life.exitEpoch assigned] at later
        unfold horizonEnd driftHorizon at notScheduled
        omega
      have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far' => by
        rw [far'] at later
        omega
      obtain ⟨c, chosen, amount⟩ := (stops i).charge_of_new_exit found foundR unset assigned
      have cutoff := (stops i).charge_cutoff chosen (high + 1) ⟨w, foundR, by omega⟩
      have actual := (stops i).selected
      rw [chosen] at actual
      obtain ⟨-, -, -, -, -, -, -, -, vs, -, atStop, -, unsetStop, -, -⟩ := actual
      have replay : ((stops i).pre.append (stops i).post).balanceEvents high = .ok events := by
        rw [(stops i).split]
        exact replayed
      obtain ⟨part, partOk, included⟩ :=
        (stops i).pre.balanceEvents_prefix (stops i).post high events replay
      have bound := producer shared (stops i).pre high (prefixSupported _ (stops i).post)
        twoSlots part partOk i v vs found atStop unslashed set (by rw [unsetStop]; exact far)
      have once : (if FirstDown (stops i).pre i then
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
        split <;> omega
      refine ⟨part, 0, c.amount, vs.slashed, fun _ =>
        ⟨included, by unfold base; rw [amount]; omega, .inl rfl, .inr ⟨c, chosen, rfl, cutoff⟩⟩⟩
  choose part kept charged flag facts using key
  have unique := shared.pubkeysDistinct genesis
  have inCohort : ∀ i ∈ R, i ∈ penaltyCohort x := fun i member => (Finset.mem_filter.mp member).1
  have indices : ∀ i ∈ penaltyCohort x, i < x.state.validators.data.size :=
    fun i member => penaltyCohort_inside xEarly member
  -- The kept stake is counted in the total at `r`.
  have keptTotal : (∑ i ∈ R, kept i) ≤ total.toNat := by
    have rWithin := r.state.validators.bound early
    have size := registryGrows_of_chainSteps pre.chainSteps
    have back : ∀ i ∈ R, i.toUInt64.toNat = i := fun i member =>
      toNat_toUInt64_of_lt rWithin ((indices i (inCohort i member)).trans_le size)
    obtain ⟨_, _, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok computed)
    rw [value]
    refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    unfold Models.stake
    let F := R.filter fun i => kept i ≠ 0
    have inF : ∀ i ∈ F, i ∈ R ∧ ∃ w, r.state.validators.data[i]? = some w ∧
        isActiveValidator w (getCurrentEpoch r.state) = true ∧ kept i = effectiveAt r i :=
      fun i member => by
        obtain ⟨inR, positive⟩ := Finset.mem_filter.mp member
        rcases (facts i inR).2.2.1 with zero | found
        · exact absurd zero positive
        · exact ⟨inR, found⟩
    calc (∑ i ∈ R, kept i) = ∑ i ∈ F, kept i := (Finset.sum_filter_ne_zero _).symm
      _ ≤ ∑ i ∈ F, balanceAt r.state i.toUInt64.toNat := Finset.sum_le_sum fun i member => by
          obtain ⟨inR, w, foundR, _, equal⟩ := inF i member
          simp only [back i inR, balanceAt, foundR, equal, effectiveAt, Option.map_some,
            Option.getD_some, le_refl]
      _ = ∑ j ∈ F.image Nat.toUInt64, balanceAt r.state j.toNat :=
          (Finset.sum_image (f := fun j : UInt64 => balanceAt r.state j.toNat) (s := F)
            (g := Nat.toUInt64) fun a member b member' same => by
              have equal := congrArg UInt64.toNat same
              rwa [back a (inF a member).1, back b (inF b member').1] at equal).symm
      _ ≤ ∑ j ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
            balanceAt r.state j.toNat := Finset.sum_le_sum_of_subset_of_nonneg (fun j member => by
          obtain ⟨i, chosen, rfl⟩ := Finset.mem_image.mp member
          obtain ⟨inR, w, foundR, activeR, _⟩ := inF i chosen
          exact List.mem_toFinset.mpr ((mem_getActiveValidatorIndices rWithin).mpr
            ⟨w, by rw [back i inR]; exact foundR, activeR⟩)) fun _ _ _ => Nat.zero_le _
  -- The charges and the partial withdrawals fit the departure budget and the due partials.
  have joint := joint R (R.filter fun i => charged i ≠ 0) charged part
    (Finset.filter_subset _ _) (fun i member => by
      obtain ⟨inR, positive⟩ := Finset.mem_filter.mp member
      rcases (facts i inR).2.2.2 with zero | found
      · exact absurd zero positive
      · exact found) (fun i member => (facts i member).1)
  rw [Finset.sum_filter_ne_zero] at joint
  -- The penalty debits fit the penalties of the epochs before `r`.
  have debits := (prefix_resource_sum_le R part events (fun i => floorPenaltyDebit i)
    fun i member => (facts i member).1).trans (List.sum_le_sum fun e _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (fun i member => inCohort i member)
        fun _ _ _ => Nat.zero_le _) |>.trans penalty
  have slack := initial_active_slack_le R xEarly fun i member => by
    obtain ⟨v, found, active, _⟩ := cohort i (inCohort i member)
    exact ⟨v, found, active⟩
  have slashing := slashing R flag (Finset.filter_subset _ _)
  -- One increment per key, at most one key per active key at `x`.
  have count : R.card ≤ finalKeyCount preset (referenceStake x) (referenceCount x)
      (stakeCeilingAt config x high (driftHorizon x high + 1)) :=
    (Finset.card_filter_le _ _).trans ((cohort_card_le xEarly unique).trans (by
      unfold finalKeyCount; exact Nat.le_add_right _ _))
  -- The keys scheduled to exit at `x` fit the scheduled departures.
  have scheduled : (∑ i ∈ S, effectiveAt x i) ≤ scheduledExitStake x (driftHorizon x high) := by
    unfold scheduledExitStake
    rw [list_map_sum_range, Array.length_toList]
    refine (Finset.sum_le_sum fun i member => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun i member => Finset.mem_range.mpr
        (indices i (Finset.mem_filter.mp member).1)) fun _ _ _ => Nat.zero_le _)
    obtain ⟨inC, within⟩ := Finset.mem_filter.mp member
    obtain ⟨v, found, active, _⟩ := cohort i inC
    simp only [found, Option.any_some, decide_eq_true_eq] at within
    simp [Array.getElem?_toList, found, active, effectiveAt, within]
  have split : (∑ i ∈ S, effectiveAt x i) + (∑ i ∈ R, effectiveAt x i) =
      ∑ i ∈ penaltyCohort x, effectiveAt x i :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have unslashed := unslashed_le_cohort xEarly unique
  have per := Finset.sum_le_sum fun i member => (facts i member).2.1
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at per
  have rounded : R.card * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          finalKeyCount preset (referenceStake x) (referenceCount x)
        (stakeCeilingAt config x high (driftHorizon x high + 1)) := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ count
  rw [floorAt_eq]
  change referenceStake x - slashedActiveStake x - startSlack x -
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        finalKeyCount preset (referenceStake x) (referenceCount x)
      (stakeCeilingAt config x high (driftHorizon x high + 1)) -
    stakeCeilingAt config x high (driftHorizon x high + 1) /
      minSlashingPenaltyQuotient preset (preElectraEpochs config x high) -
    duePartialWithdrawals x (driftHorizon x high) - scheduledExitStake x (driftHorizon x high) -
    departureBudgetAt (config := config) x high -
        windowPenalties (config := config) x high (ix x r) ≤ _
  omega

/-- Let `r` be the first state of an epoch.

From Electra, the key budgets that the floor at `r` reads hold for any stops of a branch to `r`.

The charges and partial withdrawals fit the departure budget and the due partials.

The penalty debits fit the penalties of the epochs before `r`.

That holds since every step to `r` starts before its epoch. -/
private theorem electra_anchor_budgets {g x r : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (pre : Run config checks x r)
    (supported : Supported shared pre high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (others : ∀ {u : ForkedBeaconState preset} (head : Run config checks x u),
      u.fork < .glamsterdam → (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ found,
        head.balanceEvents high = .ok found → (found.map otherCredit).sum ≤
          whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
            (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
            (driftHorizon x high) (preElectraEpochs config x high))
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch r.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (head : Run config checks x z)
      (post : Run config checks z r), pre = head.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch r.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    (starts : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      pre.Contains step → (getCurrentEpoch a.state).toNat < (getCurrentEpoch r.state).toNat)
    (stops : (i : Nat) → Stop pre i)
    {events : List (BalanceEvent preset)} (replayed : pre.balanceEvents high = .ok events) :
    (∀ (keys carrier : Finset Nat) (charge : Nat → Nat)
        (parts : Nat → List (BalanceEvent preset)), keys ⊆ penaltyCohort x →
      (∀ i ∈ carrier, ∃ c, (stops i).charge = some c ∧ charge i = c.amount ∧ c.epoch ≤ high + 1) →
      (∀ i ∈ keys, parts i <+: events) →
      (∑ i ∈ carrier, charge i) +
        (∑ i ∈ keys, ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
          departureBudgetAt (config := config) x high +
              duePartialWithdrawals x (driftHorizon x high)) ∧
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      windowPenalties (config := config) x high (ix x r) := by
  obtain ⟨genesis, -, caps, aligned, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) early
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  refine ⟨fun keys carrier charge parts inside selected prefixes => ?_,
    run_penalties_upto shared genesis caps aligned electra twoSlots high guard unit
      pre early endEpoch floor eligible (ix x r)
      (fun step member => by have := starts step member; simp only [ix]; omega) replayed⟩
  exact stopped_joint_budget_of_ceiling shared genesis pre electra early high endEpoch guard aligned
    unit others floor replayed stops carrier charge selected _
    (stopped_partial_occurrences shared genesis pre early endEpoch replayed keys parts
      (fun i member => penaltyCohort_inside xEarly (inside member)) prefixes)

/-- From Electra, the slashing penalty base of a key is the larger of two values.

These are its effective balance and its balance.

The cohort's bases fit the first ceiling, and so the last. -/
private theorem electra_slashing {x : ForkedBeaconState preset} {high : Nat}
    (early : x.fork < .glamsterdam) (electra : .pectra ≤ x.fork) :
    ∀ (keys : Finset Nat) (flag : Nat → Bool), keys ⊆ penaltyCohort x →
      (∑ i ∈ keys,
            if flag i then base x i / minSlashingPenaltyQuotient preset
          (preElectraEpochs config x high)
        else 0) ≤ stakeCeilingAt config x high (driftHorizon x high + 1) /
          minSlashingPenaltyQuotient preset (preElectraEpochs config x high) := by
  intro keys flag inside
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have funded : (∑ i ∈ keys, base x i) ≤
      stakeCeilingAt config x high (driftHorizon x high + 1) := by
    refine Nat.le_trans ?_ ((funded_le_ceiling_initial electra).trans
      (ceilingAt_mono electra high (Nat.zero_le _)))
    rw [← fundingPotential_eq x.state]
    unfold fundingPotential
    refine (Finset.sum_le_sum fun i member => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun i member => Finset.mem_range.mpr (penaltyCohort_inside early (inside member)))
      fun _ _ _ => Nat.zero_le _)
    have chosen := penaltyCohort_cohort early (inside member)
    cases found : x.state.validators.data[i]? with
    | none => simp [found] at chosen
    | some v =>
      simp only [found, Option.any_some, Bool.and_eq_true] at chosen
      simp only [base, notBefore, chosen.1, Bool.true_or, ↓reduceIte, Option.map_some,
        Option.getD_some]
      exact le_refl _
  refine ((Finset.sum_le_sum fun i _ => show (if flag i then
      base x i / minSlashingPenaltyQuotient preset (preElectraEpochs config x high) else 0) ≤
      base x i / minSlashingPenaltyQuotient preset (preElectraEpochs config x high) by
        split
        · exact le_refl _
        · exact Nat.zero_le _).trans (sum_div_le keys _ _)).trans (Nat.div_le_div_right funded)

/-- Let `u` be the end of a branch from `x`, at any fork.

Let `r` be the first state of the epoch of `u`.

Then the total active balance at `u` is at least the floor at its epoch. -/
private theorem endpoint_floor_core {g x u : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (tail : Run config checks x u)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (producer : ∀ {y : ForkedBeaconState preset},
      FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (transport : ∀ {r : ForkedBeaconState preset}, Run config checks x r →
      Run config checks r u → getCurrentEpoch u.state = getCurrentEpoch r.state → ∀ {total : Gwei},
        getTotalActiveBalance u.state = .ok total → getTotalActiveBalance r.state = .ok total)
    -- Take as given the budgets at `r` and the total there.
    (budgets : ∀ {r : ForkedBeaconState preset} (pre : Run config checks x r)
      (inner : Run config checks r u), tail = pre.append inner →
      getCurrentEpoch u.state = getCurrentEpoch r.state →
      (∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
        pre.Contains step → (getCurrentEpoch a.state).toNat < (getCurrentEpoch r.state).toNat) →
      ∀ (stops : (i : Nat) → Stop pre i) {events : List (BalanceEvent preset)},
        pre.balanceEvents high = .ok events →
        (∀ (keys carrier : Finset Nat) (charge : Nat → Nat)
            (parts : Nat → List (BalanceEvent preset)), keys ⊆ penaltyCohort x →
          (∀ i ∈ carrier, ∃ c, (stops i).charge = some c ∧ charge i = c.amount ∧
            c.epoch ≤ high + 1) →
          (∀ i ∈ keys, parts i <+: events) →
          (∑ i ∈ carrier, charge i) +
            (∑ i ∈ keys, ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum) ≤
              departureBudgetAt (config := config) x high +
                  duePartialWithdrawals x (driftHorizon x high)) ∧
        (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
          windowPenalties (config := config) x high (ix x r))
    (slashing : ∀ (keys : Finset Nat) (flag : Nat → Bool), keys ⊆ penaltyCohort x →
      (∑ i ∈ keys,
            if flag i then base x i / minSlashingPenaltyQuotient preset
          (preElectraEpochs config x high)
        else 0) ≤ stakeCeilingAt config x high (driftHorizon x high + 1) /
          minSlashingPenaltyQuotient preset (preElectraEpochs config x high))
    {total : Gwei} (computed : getTotalActiveBalance u.state = .ok total) :
    stakeFloorAt config x high (ix x u) ≤ total.toNat := by
  -- The branch splits at `r` once.
  obtain ⟨genesis, parameters, caps, aligned, early, endEpoch, guard⟩ := supported
  obtain ⟨r, pre, inner, split, same, starts⟩ := epoch_anchor tail early
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  have rEnd := (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps inner.chainSteps)).trans
    endEpoch
  have support : Supported shared pre high :=
    ⟨genesis, parameters, caps, aligned, rEarly, rEnd, guard⟩
  obtain ⟨events, replayed⟩ := pre.balanceEvents_ok rEarly high
  let stops := fun i => Classical.choice (Stop.exists pre i)
  have read := budgets pre inner split same starts stops replayed
  have index : ix x u = ix x r := by simp only [ix, same]
  rw [index]
  exact anchor_floor_core shared pre support twoSlots producer stops replayed read.1 read.2
    slashing (transport pre inner same computed)

/-- Let `u` be the end of a branch from `x`.

From Electra, the total active balance at `u` is at least the floor at its epoch.

The branch splits at the first state `r` of that epoch, where the total is the same.

The floor and the eligible stake are read only at states of earlier epochs. -/
private theorem endpoint_floor_le_total {g x u : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (tail : Run config checks x u)
    (supported : Supported shared tail high) (electra : .pectra ≤ x.fork)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (others : ∀ {v : ForkedBeaconState preset} (head : Run config checks x v),
      v.fork < .glamsterdam → (getCurrentEpoch v.state).toNat ≤ high + 1 → ∀ found,
        head.balanceEvents high = .ok found → (found.map otherCredit).sum ≤
          whistleblowerAllowance preset config (referenceCount x) (scheduledActivationCount x)
            (unassignedPreStake x) (fundingCarry x) (exitedSlashableCount x)
            (driftHorizon x high) (preElectraEpochs config x high))
    (floor : ∀ {v : ForkedBeaconState preset}, Run config checks x v → v.fork < .glamsterdam →
      (getCurrentEpoch v.state).toNat < (getCurrentEpoch u.state).toNat → ∀ total,
        getTotalActiveBalance v.state = .ok total →
        stakeFloorAt config x high (ix x v) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (head : Run config checks x z)
      (post : Run config checks z u), tail = head.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch u.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    (producer : ∀ {y : ForkedBeaconState preset},
      FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    {total : Gwei} (computed : getTotalActiveBalance u.state = .ok total) :
    stakeFloorAt config x high (ix x u) ≤ total.toNat := by
  obtain ⟨genesis, parameters, caps, aligned, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  refine endpoint_floor_core shared tail ⟨genesis, parameters, caps, aligned, early, endEpoch,
    guard⟩ twoSlots producer (fun pre inner same => total_same_epoch inner
      (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) early same) ?_
    (electra_slashing xEarly electra) computed
  intro r pre inner split same starts stops events replayed
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  have rEnd := (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps inner.chainSteps)).trans
    endEpoch
  exact electra_anchor_budgets shared pre ⟨genesis, parameters, caps, aligned, rEarly, rEnd, guard⟩
    twoSlots electra unit others
    (fun head headEarly before => floor head headEarly (by rw [same]; exact before))
    (fun head post divided before => eligible head (post.append inner)
      (by rw [split, divided, Run.append_assoc]) (by rw [same]; exact before)) starts stops replayed

end

/-- Along a trace, the balance plus the debt stays above `low`.

Once the key is slashed, the bound is `low` less one slashing penalty `base / quotient`. -/
private theorem FloorTrace.balance_floor {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (initial : low ≤ a.balance + a.debt)
    (start : low + (a.high - a.balance) ≤ base) :
    low ≤ b.balance + b.debt + if b.slashedHigh.isSome then base / quotient else 0 := by
  -- Before the slashing, the effective balance exceeds the balance by a bounded amount.
  --
  -- The bound is the starting slack plus the debt.
  --
  -- So the part of the penalty above `base / quotient`, which the high-water mark pays, was funded.
  induction trace with
  | nil =>
    generalize base / quotient = pay
    split <;> omega
  | credit prior paid ih =>
    dsimp only at *
    generalize base / quotient = pay at *
    omega
  | debit prior paid ih =>
    dsimp only at *
    generalize base / quotient = pay at *
    omega
  | sweep prior paid ih =>
    dsimp only at *
    generalize base / quotient = pay at *
    split <;> omega
  | update prior backed ih =>
    dsimp only at *
    generalize base / quotient = pay at *
    omega
  | slash prior unused paid cap ih =>
    have floor := FloorTrace.unslashed_balance_floor prior initial unused
    have deficit := FloorTrace.unslashed_high_deficit prior unused
    simp only [Option.isSome_some, ↓reduceIte]
    generalize base / quotient = pay at *
    omega

/-- The balance floor of one key, at any fork, given three facts that depend on the fork. -/
private theorem floor_bound_of_guards {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (i : Nat) (v w : Validator) (initial : x.state.validators.data[i]? = some v)
    (final : y.state.validators.data[i]? = some w) (unslashed : v.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) (later : high + 1 < w.exitEpoch.toNat)
    -- Every step's slashing quotient is at least the window's, and no step is the Electra crossing.
    (quotients : ∀ {m n : ForkedBeaconState preset}, Run config checks x m →
      Step config checks m n → Run config checks n y →
      minSlashingPenaltyQuotient preset (preElectraEpochs config x high) ≤
        (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat)
    (regime : ∀ {m n : ForkedBeaconState preset}, Run config checks x m →
      Step config checks m n → Run config checks n y → .pectra ≤ m.fork ∨ n.fork < .pectra)
    -- The slashing base covers the smaller of the key's effective balance and its balance.
    --
    -- That balance counts its slack.
    (start : min (effectiveAt x i) (actualBalanceAt x i) +
      (effectiveAt x i - actualBalanceAt x i) ≤ base x i) :
    effectiveAt x i ≤ effectiveAt y i + (effectiveAt x i - actualBalanceAt x i) +
      (events.map (floorPenaltyDebit i)).sum +
      (events.map (floorPartialDebit (UInt64.ofNat i))).sum +
      (if w.slashed then
        (if x.fork < .pectra then min (max (effectiveAt x i) (actualBalanceAt x i))
          preset.MAX_EFFECTIVE_BALANCE.toNat else max (effectiveAt x i) (actualBalanceAt x i)) /
        minSlashingPenaltyQuotient preset (preElectraEpochs config x high) else 0) +
      if FirstDown tail i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0 := by
  -- The per-key trace of the branch gives a floor on its balance at every state.
  --
  -- The effective balance follows the balance down.
  obtain ⟨genesis, _, caps, _, early, endEpoch, guard⟩ := supported
  have positive := guard
  obtain ⟨increment, _, _, _, _, _, _, quotient, _, delay, _⟩ := positive
  have far := window_below_far (config := config) twoSlots guard
  have inside : i < y.state.validators.data.size := (Array.getElem?_eq_some_iff.mp final).1
  have back := toNat_toUInt64_of_lt (y.state.validators.bound early) inside
  rw [Nat.toUInt64_eq] at back
  -- Each step of the branch keeps the key assigned past the window, in the short window.
  have guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ u,
      n.state.validators.data[(UInt64.ofNat i).toNat]? = some u →
      high + 1 < u.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      minSlashingPenaltyQuotient preset (preElectraEpochs config x high) ≤
        (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ added, step.balanceEvents = .ok added → ∀ e ∈ added, e.source ≠ .crossing := by
    intro m n pre step post _ u found
    rw [back] at found
    refine ⟨?_, short_window_of_guard guard endEpoch ((Run.nil.snoc step).append post),
      quotients pre step post, fun added addedOk =>
        no_crossing_of_regime shared pre genesis caps step
          (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early)
          (regime pre step post) addedOk⟩
    -- An assigned exit stays until `y`; an unassigned one is past the window.
    by_cases assigned : u.exitEpoch = FAR_FUTURE_EPOCH
    · rw [assigned]; exact far
    · obtain ⟨z, located, life⟩ := post.registryLifecycle.validators i u found
      have same := Option.some.inj (located.symm.trans final)
      subst z
      rw [← life.exitEpoch assigned]
      exact later
  obtain ⟨last, _, _, debt, _, z, located, _, _, path⟩ :=
    FloorTrace.run shared tail genesis caps (by omega) early high endEpoch (UInt64.ofNat i) v
      (by rwa [back]) unslashed activated (min (effectiveAt x i) (actualBalanceAt x i))
      (base x i) (minSlashingPenaltyQuotient preset (preElectraEpochs config x high))
      (by rw [back]; exact Nat.min_le_left _ _)
      quotient guards replayed
  rw [back] at located debt path
  have same := Option.some.inj (located.symm.trans final)
  subst z
  have bound := effective_loss_le_of_floor shared tail genesis caps increment early v initial
    activated (last.debt + if w.slashed then base x i /
      minSlashingPenaltyQuotient preset (preElectraEpochs config x high) else 0) (fun p member => by
      obtain ⟨c, trace, balance, spent, flag⟩ := path p member
      have lower := FloorTrace.balance_floor trace (by dsimp only; omega) (by
        dsimp only
        omega)
      have charged : (if c.slashedHigh.isSome then base x i /
          minSlashingPenaltyQuotient preset (preElectraEpochs config x high) else 0) ≤
          if w.slashed then base x i / minSlashingPenaltyQuotient preset
              (preElectraEpochs config x high)
            else 0 := by
        cases hc : c.slashedHigh.isSome <;> cases hw : w.slashed <;> simp_all
      rw [balance] at lower
      omega)
  rw [debt] at bound
  unfold base at bound
  omega

/-- From Electra, the balance floor of each key holds.

Each step's quotient is the Electra quotient.

The slashing base is the larger of the key's effective balance and balance. -/
private theorem floorProducer_electra {g x y : ForkedBeaconState preset}
    (electra : .pectra ≤ x.fork) :
    FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail high supported twoSlots events replayed i v w initial final unslashed
    activated later
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  exact floor_bound_of_guards shared tail high supported twoSlots replayed i v w initial final
    unslashed activated later (fun pre _ _ => (slashing_quotient_of_electra pre electra).le)
    (fun pre _ _ => .inl (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)))
    (by simp only [base, notBefore, ↓reduceIte]; omega)

/-- Before Electra, the balance floor of each key holds. -/
private theorem floorProducer_pre {g x y : ForkedBeaconState preset}
    (before : x.fork < .pectra) :
    FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  -- The guard keeps the whole window before the fork.
  --
  -- Each step's quotient is at least the least pre-Electra quotient.
  --
  -- The slashing base is the larger of the key's effective balance and balance.
  --
  -- That larger value is capped at `MAX_EFFECTIVE_BALANCE`.
  --
  -- The effective balance is within that cap before Electra.
  intro shared tail high supported twoSlots events replayed i v w initial final unslashed
    activated later
  have support := supported
  obtain ⟨genesis, _, caps, _, early, endEpoch, guard⟩ := support
  have regimes := guarded_fork_regime (shared.append tail) genesis high endEpoch guard
  have positive := regimes.1.mpr before
  have yBefore := regimes.2.resolve_left (Nat.not_le_of_gt before)
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  refine floor_bound_of_guards shared tail high supported twoSlots replayed i v w initial final
    unslashed activated later (fun {m n} pre step post => ?_)
    (fun _ _ post => .inr (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) yBefore))
    ?_
  · have mBefore : ¬ m.fork ≥ .pectra := Nat.not_le_of_gt (Nat.lt_of_le_of_lt
      (fork_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps) yBefore)
    simp only
        [minSlashingPenaltyQuotient, positive, ↓reduceIte, EthLib.Consensus.parameters, mBefore]
    split_ifs <;> omega
  · have cap := shared.effectiveBalance_capped genesis caps v
      (Array.mem_of_getElem? initial)
    have notAfter : ¬ .pectra ≤ x.fork := Nat.not_le_of_gt before
    simp only [withdrawalMaxEffectiveBalance, notAfter, ↓reduceIte] at cap
    have numeric := UInt64.le_iff_toNat_le.mp cap
    have atStart : effectiveAt x i = v.effectiveBalance.toNat := by simp [effectiveAt, initial]
    simp only [base, before, ↓reduceIte]
    omega

/-- The balance floor of each key holds at every fork. -/
theorem floorProducer_proved {g x y : ForkedBeaconState preset} :
    FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) :=
  if before : x.fork < .pectra then floorProducer_pre before
  else floorProducer_electra (Nat.le_of_not_lt before)

private theorem prefix_witness_issuance_actual {v r y : ForkedBeaconState preset}
    (tail : Run config checks v y) (pre : Run config checks v r)
    (inner : Run config checks r y) (split : tail = pre.append inner)
    (electra : .pectra ≤ r.fork) (early : y.fork < .glamsterdam)
    (same : getCurrentEpoch y.state = getCurrentEpoch r.state)
    (aligned : EffectiveBalancesAligned r.state)
    (inc : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (ceiling : Nat → Nat)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ ceiling
      ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat))
    (previousLe : ∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling
        ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat))
    (currentLe : ∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
      effectiveAt r i.toNat ≤ ceiling
        ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat))
    (ratio : ∀ total, getTotalActiveBalance r.state = .ok total →
      2 * ceiling ((getCurrentEpoch r.state).toNat -
        (getCurrentEpoch v.state).toNat) ≤ 3 * total.toNat)
    (high : Nat) {events before during : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (beforeOk : pre.balanceEvents high = .ok before)
    (duringOk : inner.balanceEvents high = .ok during)
    (issued : sourceCredits .rewards before + sourceCredits .sync before ≤
      ∑ s ∈ Finset.range ((getCurrentEpoch r.state).toNat - (getCurrentEpoch v.state).toNat),
        2 * preset.epochIssuanceBeforeAltair (ceiling s)) :
    sourceCredits .rewards events + sourceCredits .sync events ≤
      ∑ s ∈ Finset.range ((getCurrentEpoch y.state).toNat -
        (getCurrentEpoch v.state).toNat + 1), 2 * preset.epochIssuanceBeforeAltair (ceiling s) := by
  have exactReplay := balanceEvents_append pre inner high beforeOk duringOk
  rw [← split] at exactReplay
  obtain rfl := Except.ok.inj (replayed.symm.trans exactReplay)
  have insideBound := epoch_prefix_issuance_le inner electra early same aligned inc unit
    previousLe currentLe ratio high duringOk
  simp only [sourceCredits_append, same, Finset.sum_range_succ]
  omega

private theorem issuance_of_endpoint_floor {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    sourceCredits .rewards events + sourceCredits .sync events ≤
        windowIssuance (config := config) x high := by
  obtain ⟨genesis, _, caps, aligned, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  obtain ⟨r, pre, inner, before, during, split, beforeOk, duringOk, same, current, previous,
    issued⟩ := activeStake_prefix_witness shared genesis tail electra early high endEpoch guard
      aligned unit
      (fun head early within found ok => otherCredit_le_allowance_electra shared genesis head
        caps aligned electra early twoSlots high within guard ok)
      (fun head headEarly earlier => floor head headEarly (Nat.le_of_lt earlier))
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  have rElectra := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have mono := ceilingAt_mono (config := config) electra high
  have index : ix x r ≤ driftHorizon x high + 1 := by
    unfold ix driftHorizon
    rw [same] at endEpoch
    omega
  have noFork : preElectraEpochs config x high = 0 := by
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    simp [preElectraEpochs, notBefore]
  have ratioGuard := guard.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ratio := ratioGuard (ix x r) (by rw [noFork]; exact Nat.zero_le _) index
  have ratioActual : ∀ total, getTotalActiveBalance r.state = .ok total →
      2 * stakeCeilingAt config x high (ix x r) ≤ 3 * total.toNat := by
    intro total totalOk
    have lower := floor pre rEarly (by rw [same]) total totalOk
    exact ratio.trans (Nat.mul_le_mul_left _ lower)
  have all := prefix_witness_issuance_actual tail pre inner split rElectra early same
    ((run_justified_separated (shared.append pre) genesis).1.aligned aligned) guard.1
    (stakeCeilingAt config x high) (unit.trans (mono (Nat.zero_le _))) previous current
    ratioActual high replayed beforeOk duringOk issued
  have within : ix x y + 1 ≤ driftHorizon x high + 1 := by
    unfold ix driftHorizon
    omega
  have sumLe := Finset.sum_le_sum_of_subset (f := fun t =>
    2 * preset.epochIssuanceBeforeAltair (stakeCeilingAt config x high t))
      (Finset.range_mono within)
  apply all.trans
  simpa [windowIssuance, noFork, ix, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range] using sumLe

private theorem eligible_le_ceiling_of_floor {g x z y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (toZ : Run config checks x z) (post : Run config checks z y)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (before : (getCurrentEpoch z.state).toNat < (getCurrentEpoch y.state).toNat)
    (guard : aprioriGuardAt config x high)
    (unit : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high 0)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat) :
    (∑ i ∈ penaltyCohort x, eligibleWeight z.state i) ≤ stakeCeilingAt config x high (ix x z) := by
  have zEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  obtain ⟨r, pre, inner, _, _, _, beforeOk, _, same, _, _, issued⟩ :=
    activeStake_prefix_witness shared genesis toZ electra zEarly high (by omega) guard aligned
      unit
      (fun head early within events ok => otherCredit_le_allowance_electra shared genesis head
        caps aligned electra early twoSlots high within guard ok)
      (fun head headEarly earlier => floor head headEarly (by omega))
  have retained := eligible_le_retained_anchor shared genesis caps guard electra pre inner post
    early same before endEpoch
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) zEarly
  have bound := retained_anchor_le_ceiling shared genesis pre caps aligned electra rEarly
    twoSlots high (by rw [same] at before; omega) guard beforeOk issued
  have indices : ix x z = ix x r := by simp only [ix, same]
  rw [indices]
  exact retained.trans bound

private theorem penaltyProducer_of_prior_floor {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
      fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
        else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (ix x y + 1) := by
  obtain ⟨genesis, _, caps, aligned, early, endEpoch, guard⟩ := id supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  apply penaltyProducer_of_floor shared tail high supported twoSlots electra unit floor
    (fun pre post _ before => ?_) events replayed
  exact (eligible_le_ceiling_of_floor shared genesis caps aligned electra twoSlots pre post early
    high endEpoch before guard unit floor).trans (Nat.le_add_right _ _)

/-- A floor step that reads only strictly earlier epochs gives the floor throughout the window. -/
theorem floor_by_epoch_induction {x : ForkedBeaconState preset} {high : Nat}
    (bound : Fork)
    (step : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < bound →
      (getCurrentEpoch u.state).toNat ≤ high + 1 →
      (∀ {v : ForkedBeaconState preset}, Run config checks x v → v.fork < bound →
        (getCurrentEpoch v.state).toNat < (getCurrentEpoch u.state).toNat → ∀ total,
        getTotalActiveBalance v.state = .ok total →
        stakeFloorAt config x high (ix x v) ≤ total.toNat) → ∀ total,
      getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat) :
    ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < bound →
      (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ total,
      getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat := by
  suffices all : ∀ n, ∀ {u : ForkedBeaconState preset}, Run config checks x u →
      (getCurrentEpoch u.state).toNat = n → u.fork < bound →
      (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ total,
      getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat from
    fun {_} head early within total computed => all _ head rfl early within total computed
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u head epoch early within total computed
    exact step head early within (fun run vEarly before amount read =>
      ih _ (epoch ▸ before) run rfl vEarly (by omega) amount read) total computed

/-- From Electra, take a branch from `x` within its window, and a pre-Glamsterdam state of it.

The total active balance at that state is at least the floor at its epoch. -/
private theorem floor_all_runs {g x : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (guard : aprioriGuardAt config x high)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (producer : ∀ {y : ForkedBeaconState preset},
      FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y)) :
    ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat := by
  -- The proof is a strong induction on the epoch of the state.
  --
  -- At a state `u`, the floor at every earlier epoch holds by induction.
  --
  -- The eligible stake at every earlier split of the branch to `u` then fits the ceiling.
  --
  -- This follows from the retained anchor of its epoch.
  --
  -- Both feed the floor at `u`, which assumes no floor or eligible fact at the epoch of `u`.
  apply floor_by_epoch_induction .glamsterdam
  intro u head early within strict total computed
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps head.chainSteps) early
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  exact endpoint_floor_le_total shared head
    ⟨genesis, parameters, caps, aligned, early, within, guard⟩ electra twoSlots unit
    (fun head early within found ok => otherCredit_le_allowance_electra shared genesis head
      caps aligned electra early twoSlots high within guard ok) strict
    (fun pre post _ before => (eligible_le_ceiling_of_floor shared genesis caps aligned
      electra twoSlots pre post early high within before guard unit strict).trans
      (Nat.le_add_right _ _)) producer computed

/-- From Electra, the reward and sync credits of a branch fit the issuance envelope.

The floor at every epoch through the end of the branch comes from an induction on the epoch. -/
private theorem issuance_of_floor_all_runs {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    (producer : ∀ {y : ForkedBeaconState preset},
      FloorProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    sourceCredits .rewards events + sourceCredits .sync events ≤
      windowIssuance (config := config) x high := by
  have support := supported
  obtain ⟨genesis, parameters, caps, aligned, _, endEpoch, guard⟩ := supported
  exact issuance_of_endpoint_floor shared tail high support twoSlots electra
    (fun head early within total read => floor_all_runs shared genesis parameters caps aligned
      guard electra twoSlots producer head early (within.trans endEpoch) total read)
    replayed

/-- From Electra, take a branch from `x` within its window, and a pre-Glamsterdam state of it.

The total active balance at that state is at least the floor at its epoch.

This statement has the balance floor of each key proved. -/
theorem floor_all_runs_electra {g x : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (guard : aprioriGuardAt config x high)
    (electra : .pectra ≤ x.fork) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat :=
  floor_all_runs shared genesis parameters caps aligned guard electra twoSlots
    (floorProducer_electra electra)

/-- From Electra, this is the penalty bound of a branch with every floor proved.

The cohort's penalty and sync debits over a branch fit the penalties of its epochs. -/
theorem penaltyProducer_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    (events : List (BalanceEvent preset)) (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).map
      fun i => if (x.state.validators.data[i.toNat]?.map (·.slashed)).getD true then 0
        else floorPenaltyDebit i.toNat e).sum).sum ≤
      windowPenalties (config := config) x high (ix x y + 1) := by
  have support := supported
  obtain ⟨genesis, parameters, caps, aligned, _, endEpoch, guard⟩ := supported
  exact penaltyProducer_of_prior_floor shared tail high support twoSlots electra
    (fun head early before total read => floor_all_runs_electra shared genesis parameters caps
      aligned guard electra twoSlots head early (by omega) total read) events replayed

/-- From Electra, the reward and sync credits of a branch fit the issuance envelope.

Every floor here is proved. -/
theorem issuance_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    sourceCredits .rewards events + sourceCredits .sync events ≤
      windowIssuance (config := config) x high :=
  issuance_of_floor_all_runs shared tail high supported twoSlots electra
    (floorProducer_electra electra) replayed

theorem ceilingFloor_electra {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) :
    (∑ i ∈ (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).toFinset,
      effectiveAt y i.toNat) ≤ stakeCeilingAt config x high (ix x y) ∧
    (∑ i ∈ (getActiveValidatorIndices y.state (getPreviousEpoch y.state)).toFinset,
      effectiveAt y i.toNat) ≤ stakeCeilingAt config x high (ix x y) ∧
    ∀ total, getTotalActiveBalance y.state = .ok total →
      stakeFloorAt config x high (ix x y) ≤ total.toNat := by
  obtain ⟨genesis, parameters, caps, aligned, early, endEpoch, guard⟩ := id supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  have ceilings := activeStake_le_ceiling shared genesis tail electra early high endEpoch
    guard aligned unit
    (fun head uEarly within events read => otherCredit_le_allowance_electra shared genesis head
      caps aligned electra uEarly twoSlots high within guard read)
    (fun head uEarly before total read => floor_all_runs_electra shared genesis parameters caps
      aligned guard electra twoSlots head uEarly (by omega) total read)
  exact ⟨ceilings.1, ceilings.2,
    floor_all_runs_electra shared genesis parameters caps aligned guard electra twoSlots tail
      early endEpoch⟩

theorem LedgerCuts.roundLedger_closed_electra
    {g x y : ForkedBeaconState preset} {high : Nat} {tail : Run config checks x y}
    (ledger : LedgerCuts tail) (shared : Run config checks g x)
    (supported : Supported shared tail high) (electra : .pectra ≤ x.fork)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    ∃ result : RoundLedger tail high, result.toLedgerCuts = ledger := by
  obtain ⟨genesis, parameters, caps, aligned, early, endEpoch, guard⟩ := id supported
  have strict : ∀ {u : ForkedBeaconState preset}, Run config checks x u →
      u.fork < .glamsterdam → (getCurrentEpoch u.state).toNat <
        (getCurrentEpoch y.state).toNat → ∀ total,
      getTotalActiveBalance u.state = .ok total →
      stakeFloorAt config x high (ix x u) ≤ total.toNat :=
    fun head uEarly before total read => floor_all_runs_electra shared genesis parameters caps
      aligned guard electra twoSlots head uEarly (by omega) total read
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  exact ledger.roundLedger_of_floor shared supported electra twoSlots strict
    (fun pre post _ before => (eligible_le_ceiling_of_floor shared genesis caps aligned
      electra twoSlots pre post early high endEpoch before guard unit strict).trans
        (Nat.le_add_right _ _))

section
variable {g x y : ForkedBeaconState preset}

private theorem pre_supported_prefix (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    {z : ForkedBeaconState preset} (pre : Run config checks x z) (post : Run config checks z y) :
    Supported shared pre high := by
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  exact ⟨supported.1, supported.2.1, supported.2.2.1, supported.2.2.2.1,
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) supported.2.2.2.2.1,
    order.trans supported.2.2.2.2.2.1, supported.2.2.2.2.2.2⟩

private theorem pre_no_crossing (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) : driftHorizon x high + 2 ≤ preElectraEpochs config x high := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have positive := ((guarded_fork_regime (shared.append tail) supported.1 high
    supported.2.2.2.2.2.1 supported.2.2.2.2.2.2).1).mpr xEarly
  have crossing := supported.2.2.2.2.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, crossing⟩ := crossing
  exact crossing.resolve_left (Nat.ne_of_gt positive)

/-- Before the guarded fork, the ceiling is the activation cap times the count path. -/
private theorem pre_ceiling_eq (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {t : Nat} (within : t ≤ driftHorizon x high + 1) :
    stakeCeilingAt config x high t = preset.MIN_ACTIVATION_BALANCE.toNat *
      activeCountPath config (referenceCount x + scheduledActivationCount x) t := by
  have noCrossing := pre_no_crossing shared tail high supported early
  have positive : 0 < preElectraEpochs config x high := by omega
  cases t with
  | zero => simp [stakeCeilingAt, stakeCeiling, positive, activeCountPath]
  | succ t =>
    simp only
        [stakeCeilingAt, stakeCeiling, positive, show t + 1 ≤
          preElectraEpochs config x high by omega,
      and_self, ↓reduceIte]

private theorem pre_refCount_le_path (config : Config) (x : ForkedBeaconState preset) (t : Nat) :
    referenceCount x ≤ activeCountPath config (referenceCount x + scheduledActivationCount x) t :=
  (Nat.le_add_right _ _).trans (countPath_monotone config _ (Nat.zero_le t))

private theorem pre_meb_count_le_ceiling (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {t k : Nat} (within : t ≤ driftHorizon x high + 1)
    (count : k ≤ activeCountPath config (referenceCount x + scheduledActivationCount x) t) :
    preset.MAX_EFFECTIVE_BALANCE.toNat * k ≤ stakeCeilingAt config x high t := by
  rw [pre_ceiling_eq shared tail high supported early within]
  exact (Nat.mul_le_mul_left _ count).trans
    (Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp supported.2.2.1.activation))

private theorem pre_validator_cap (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) (v : Validator) (member : v ∈ y.state.validators.data) :
    v.effectiveBalance.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
  have caps := supported.2.2.1
  have bound := (shared.append tail).effectiveBalance_capped supported.1 caps v member
  have notElectra : ¬ Fork.pectra ≤ y.fork := Nat.not_le_of_lt early
  simpa [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance, notElectra] using
    UInt64.le_iff_toNat_le.mp bound

/-- The current active stake is bounded independently of the endpoint floor. -/
private theorem pre_current_ceiling (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) :
    (∑ i ∈ (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).toFinset,
      effectiveAt y i.toNat) ≤ stakeCeilingAt config x high (ix x y) := by
  have genesis := supported.1
  have yEarly : y.fork < .glamsterdam := Nat.lt_trans early (by decide)
  have count := activeCount_le_countPath shared genesis tail early
  have stake : (∑ i ∈ (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).toFinset,
      effectiveAt y i.toNat) ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * activeCount y.state := by
    have nodup := getActiveValidatorIndices_sorted (y.state.validators.bound yEarly)
      (getCurrentEpoch y.state)
    have distinct : (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).Nodup :=
      nodup.imp fun {a b} less same => by subst same; exact UInt64.lt_irrefl _ less
    calc _ ≤ ∑ i ∈ (getActiveValidatorIndices y.state (getCurrentEpoch y.state)).toFinset,
          preset.MAX_EFFECTIVE_BALANCE.toNat := by
            apply Finset.sum_le_sum
            intro i member
            obtain ⟨v, found, _⟩ :=
                (mem_getActiveValidatorIndices (y.state.validators.bound yEarly)).mp
              (List.mem_toFinset.mp member)
            simpa [effectiveAt, found] using
              pre_validator_cap shared tail high supported early v (Array.mem_of_getElem? found)
         _ = _ := by simp [activeCount, List.toFinset_card_of_nodup distinct, Nat.mul_comm]
  have endpoint := supported.2.2.2.2.2.1
  exact stake.trans (pre_meb_count_le_ceiling shared tail high supported early
    (by unfold ix driftHorizon; omega) count)

/-- A capped weight on the initial cohort fits the pre-Electra count ceiling. -/
private theorem pre_cohort_cap (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) (weight : Nat → Nat)
    (each : ∀ j ∈ penaltyCohort x, weight j ≤ preset.MAX_EFFECTIVE_BALANCE.toNat)
    {t : Nat} (within : t ≤ driftHorizon x high + 1) :
    (∑ j ∈ penaltyCohort x, weight j) ≤ stakeCeilingAt config x high t := by
  have genesis := supported.1
  have yEarly : y.fork < .glamsterdam := Nat.lt_trans early (by decide)
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) yEarly
  have size : (penaltyCohort x).card ≤ referenceCount x := by
    have indices : (penaltyCohort x).card ≤ activeCount x.state := by
      unfold penaltyCohort activeCount
      exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans
        (List.toFinset_card_le _))
    exact indices.trans (activeCount_le_refCount shared genesis xEarly)
  have path := pre_refCount_le_path config x t
  calc _ ≤ (penaltyCohort x).card * preset.MAX_EFFECTIVE_BALANCE.toNat := by
          simpa using Finset.sum_le_sum each
       _ ≤ _ := by
         rw [Nat.mul_comm]
         exact pre_meb_count_le_ceiling shared tail high supported early within (size.trans path)

/-- An initial active cohort retains at most one pre-Electra cap per initial active key. -/
private theorem pre_eligible_cohort_cap (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) :
    (∑ j ∈ penaltyCohort x, eligibleWeight y.state j) ≤
      stakeCeilingAt config x high (ix x y) := by
  have endpoint := supported.2.2.2.2.2.1
  apply pre_cohort_cap shared tail high supported early _ _
    (by unfold ix driftHorizon; omega)
  intro j _
  unfold eligibleWeight
  split
  · rename_i v found
    split
    · exact pre_validator_cap shared tail high supported early v (Array.mem_of_getElem? found)
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The capped pre-Electra slash charge fits the last ceiling, for every retained subset. -/
private theorem pre_slashing_envelope (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) (R : Finset Nat) (subset : R ⊆ penaltyCohort x)
    (flag : Nat → Bool) :
    (∑ i ∈ R, if flag i then
      min (max (effectiveAt x i) (actualBalanceAt x i)) preset.MAX_EFFECTIVE_BALANCE.toNat /
        minSlashingPenaltyQuotient preset (preElectraEpochs config x high) else 0) ≤
      stakeCeilingAt config x high (driftHorizon x high + 1) /
        minSlashingPenaltyQuotient preset (preElectraEpochs config x high) := by
  let weight := fun i => min (max (effectiveAt x i) (actualBalanceAt x i))
    preset.MAX_EFFECTIVE_BALANCE.toNat
  have capped := pre_cohort_cap shared tail high supported early weight
    (fun _ _ => Nat.min_le_right _ _) (Nat.le_refl (driftHorizon x high + 1))
  have kept : (∑ i ∈ R, weight i) ≤ stakeCeilingAt config x high (driftHorizon x high + 1) :=
    (Finset.sum_le_sum_of_subset subset).trans capped
  calc _ ≤ ∑ i ∈ R,
      weight i / minSlashingPenaltyQuotient preset (preElectraEpochs config x high) := by
          apply Finset.sum_le_sum
          intro i _
          split
          · exact le_refl _
          · exact Nat.zero_le _
       _ ≤ (∑ i ∈ R, weight i) / minSlashingPenaltyQuotient preset
           (preElectraEpochs config x high) :=
          sum_div_le R _ _
       _ ≤ _ := Nat.div_le_div_right kept

/-- Pre-Electra departure charges fit the frozen count-based departure budget. -/
private theorem pre_departure_budget (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) :
    ((tail.departureCharges.filter fun c => c.epoch ≤ high + 1).map (·.amount)).sum ≤
      departureBudgetAt (config := config) x high := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have yEarly : y.fork < .glamsterdam := Nat.lt_trans early (by decide)
  let bound :=
      activeCountPath config (referenceCount x + scheduledActivationCount x)
      (driftHorizon x high + 1)
  have counted : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → u.fork < .pectra → activeCount u.state ≤ bound := by
    intro u w step member uEarly
    obtain ⟨pre, _, _, _, order⟩ := Run.contains_step_facts member yEarly
    have endpoint := supported.2.2.2.2.2.1
    have mono : Monotone (activeCountPath config (referenceCount x + scheduledActivationCount x)) :=
      countPath_monotone _ _
    exact (activeCount_le_countPath shared supported.1 pre uEarly).trans
      (mono (by unfold driftHorizon; omega))
  apply departures_le_budget shared tail supported.1 supported.2.2.1 yEarly high
    supported.2.2.2.2.2.2
  · intro u w step member _ uEarly
    exact counted step member uEarly
  · intro u w step member _ electra
    obtain ⟨_, post, _⟩ := tail.contains_split step member
    have uEarly := Nat.lt_of_le_of_lt
      (Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)) early
    exact False.elim (Nat.not_le_of_lt uEarly electra)

/-- No event of a pre-Electra branch pays a pending partial withdrawal. -/
theorem pre_partial_zero (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ∑ i ∈ Finset.range e.before.state.validators.data.size,
      floorPartialDebit (UInt64.ofNat i) e).sum = 0 := by
  apply List.sum_eq_zero
  intro amount member
  obtain ⟨e, present, rfl⟩ := List.mem_map.mp member
  have order := replay_event_fork_le shared tail supported.1 supported.2.2.2.2.1 high
    supported.2.2.2.2.2.1 events replayed e present
  have before : ¬ .pectra ≤ e.before.fork := Nat.not_le_of_lt (Nat.lt_of_le_of_lt order early)
  apply Finset.sum_eq_zero
  intro i _
  simp [floorPartialDebit, before]

/-- Selected stopped charges and partials share the same pre-Electra replay budget. -/
theorem pre_stopped_joint_budget (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (stops : (i : Nat) → Stop tail i) (carrier : Finset Nat) (charge : Nat → Nat)
    (selected : ∀ i ∈ carrier, ∃ c, (stops i).charge = some c ∧
      charge i = c.amount ∧ c.epoch ≤ high + 1)
    (partialTotal : Nat)
    (partialBudget : partialTotal ≤ (events.map fun e =>
      ∑ i ∈ Finset.range e.before.state.validators.data.size,
        floorPartialDebit (UInt64.ofNat i) e).sum) :
    (∑ i ∈ carrier, charge i) + partialTotal ≤ departureBudgetAt (config := config) x high +
        duePartialWithdrawals x (driftHorizon x high) := by
  have charges := (stopped_charges_le_run tail stops carrier charge (high + 1) selected).trans
    (pre_departure_budget shared tail high supported early)
  rw [pre_partial_zero shared tail high supported early replayed] at partialBudget
  omega

end
section
variable {g x y : ForkedBeaconState preset}

/-- The pre-fork guard excludes a branch that starts before Altair. -/
private theorem pre_altair (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) : .altair ≤ x.fork := by
  have span := pre_no_crossing shared tail high supported early
  by_contra before
  have before : x.fork < .altair := Nat.lt_of_not_ge before
  simp only [preElectraEpochs, before, ↓reduceIte] at span
  split_ifs at span <;> omega

/-- The generic epoch master supplies the successful-total transport of the pre floor core. -/
private theorem pre_total_transport (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {r : ForkedBeaconState preset}
    (pre : Run config checks x r) (inner : Run config checks r y)
    (same : getCurrentEpoch y.state = getCurrentEpoch r.state) {total : Gwei}
    (computed : getTotalActiveBalance y.state = .ok total) :
    getTotalActiveBalance r.state = .ok total := by
  have altair := Nat.le_trans (pre_altair shared tail high supported early)
    (fork_le_of_chainSteps pre.chainSteps)
  obtain ⟨events, replayed⟩ := inner.balanceEvents_ok supported.2.2.2.2.1 high
  exact epoch_total_transport inner altair supported.2.2.2.2.1 same high replayed computed

end
section
variable {g x y : ForkedBeaconState preset}

/-- The initial reference stake fits every pre count ceiling in the guarded window. -/
private theorem pre_reference_le_ceiling (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {t : Nat} (within : t ≤ driftHorizon x high + 1) :
    referenceStake x ≤ stakeCeilingAt config x high t := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have caps := supported.2.2.1
  have reference := refStake_le_cap_count shared supported.1 caps xEarly
  exact reference.trans (pre_meb_count_le_ceiling shared tail high supported early within
    (pre_refCount_le_path config x t))

/-- The pre count ceiling bounds one increment without assuming a numerical unit bound. -/
private theorem pre_increment_le_ceiling (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) {t : Nat} (within : t ≤ driftHorizon x high + 1) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ stakeCeilingAt config x high t := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  exact (increment_le_reference shared supported.1 supported.2.2.2.1
    (Nat.lt_trans xEarly (by decide)) supported.2.2.2.2.2.2).trans
    (pre_reference_le_ceiling shared tail high supported early within)

end
section
variable {g x m n : ForkedBeaconState preset}

/-- A pre-Electra segment uses the count ceiling and the shared actual-replay proof. -/
private theorem pre_segment_penalties_le (shared : Run config checks g x)
    (toM : Run config checks x m) (mid : Run config checks m n) (high : Nat)
    (supported : Supported shared (toM.append mid) high) (early : n.fork < .pectra)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch n.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (eligible : ∀ {z : ForkedBeaconState preset} (pre : Run config checks m z)
      (post : Run config checks z n), mid = pre.append post →
      (getCurrentEpoch z.state).toNat < (getCurrentEpoch n.state).toNat →
      ∑ j ∈ penaltyCohort x, eligibleWeight z.state j ≤
        stakeCeilingAt config x high (ix x z) + slashedUnwithdrawnStake x)
    {events : List (BalanceEvent preset)} (replayed : mid.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      epochPenalty preset config (startInactivityScore config x)
        (stakeCeilingAt config x high (ix x m) + slashedUnwithdrawnStake x)
        (stakeFloorAt config x high (ix x m)) (ix x m) := by
  have mEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps mid.chainSteps) early
  have endpoint := supported.2.2.2.2.2.1
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps mid.chainSteps)
  have supportedM := pre_supported_prefix shared (toM.append mid) high supported toM mid
  have within : ix x m ≤ driftHorizon x high + 1 := by unfold ix driftHorizon; omega
  apply segment_penalties_core shared supported.1
    (pre_altair shared (toM.append mid) high supported early) (.inr early)
    high supported.2.2.2.2.2.2 toM mid (Nat.lt_trans early (by decide)) endpoint ?_ ?_
    starts floor eligible replayed
  · intro total totalOk
    have value := (getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)).2.2
    rw [value]
    exact (max_le (pre_increment_le_ceiling shared (toM.append mid) high supported early within)
      (pre_current_ceiling shared toM high supportedM mEarly)).trans (Nat.le_add_right _ _)
  · exact ((floor_le_initial x high _).trans ((floor_initial_le_reference x high).trans
      (pre_reference_le_ceiling shared (toM.append mid) high supported early within))).trans
      (Nat.le_add_right _ _)

end
section
variable {g x y : ForkedBeaconState preset}

/-- A wholly pre-Electra window supplies the segments of the shared cut induction. -/
theorem pre_run_penalties_upto (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra)
    (floor : ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat < (getCurrentEpoch y.state).toNat → ∀ total,
        getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat)
    (t : Nat) (bounded : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch x.state).toNat + t)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    (events.map fun e => ∑ j ∈ penaltyCohort x, floorPenaltyDebit j e).sum ≤
      windowPenalties (config := config) x high t := by
  apply run_penalties_core high tail supported.2.2.2.2.1 ?_ ?_ t bounded replayed
  · intro z pre post _ _
    have zEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
    have supportedZ := pre_supported_prefix shared tail high supported pre post
    exact (pre_eligible_cohort_cap shared pre high supportedZ zEarly).trans (Nat.le_add_right _ _)
  · intro m n toM mid rest starts eligible found ok
    have nEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) early
    have ny := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
    have supportedN := pre_supported_prefix shared tail high supported (toM.append mid) rest
    exact pre_segment_penalties_le shared toM mid high supportedN nEarly starts
      (fun head headEarly before => floor head headEarly (by omega)) eligible ok

end
section
variable {g x y : ForkedBeaconState preset}

/-- The pre-Electra floor reads only floors at strictly earlier epochs. -/
private theorem pre_endpoint_floor (shared : Run config checks g x)
    (tail : Run config checks x y) (high : Nat) (supported : Supported shared tail high)
    (early : y.fork < .pectra) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (floor : ∀ {v : ForkedBeaconState preset}, Run config checks x v →
      v.fork < .glamsterdam → (getCurrentEpoch v.state).toNat <
        (getCurrentEpoch y.state).toNat → ∀ total,
      getTotalActiveBalance v.state = .ok total →
        stakeFloorAt config x high (ix x v) ≤ total.toNat)
    {total : Gwei} (computed : getTotalActiveBalance y.state = .ok total) :
    stakeFloorAt config x high (ix x y) ≤ total.toNat := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  refine endpoint_floor_core shared tail supported twoSlots floorProducer_proved
    (fun pre inner same => pre_total_transport shared tail high supported early pre inner same)
    ?_ ?_ computed
  · intro r pre inner split same starts stops events replayed
    have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
    have support := pre_supported_prefix shared tail high supported pre inner
    refine ⟨?_, pre_run_penalties_upto shared pre high support rEarly
      (fun head headEarly before => floor head headEarly (by rw [same]; exact before))
      (ix x r) (fun step member => by
        have := starts step member
        simp only [ix]
        omega) replayed⟩
    intro keys carrier charge parts inside selected prefixes
    exact pre_stopped_joint_budget shared pre high support rEarly replayed stops carrier charge
      selected _ (stopped_partial_occurrences shared supported.1 pre support.2.2.2.2.1
        support.2.2.2.2.2.1 replayed keys parts
        (fun i member => penaltyCohort_inside (Nat.lt_trans xEarly (by decide)) (inside member))
        prefixes)
  · intro keys flag inside
    have before : x.fork < .pectra := xEarly
    simp only [base, ite_eq_left before]
    exact pre_slashing_envelope shared tail high supported early keys inside flag

/-- Every wholly pre-Electra endpoint has the floor, by strict-prior epoch induction. -/
theorem pre_floor_all_runs (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (guard : aprioriGuardAt config x high)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    ∀ {u : ForkedBeaconState preset}, Run config checks x u → u.fork < .pectra →
      (getCurrentEpoch u.state).toNat ≤ high + 1 → ∀ total,
      getTotalActiveBalance u.state = .ok total →
        stakeFloorAt config x high (ix x u) ≤ total.toNat := by
  apply floor_by_epoch_induction .pectra
  intro u head early within strict total computed
  have supported : Supported shared head high :=
    ⟨genesis, parameters, caps, aligned, Nat.lt_trans early (by decide), within, guard⟩
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps head.chainSteps) early
  apply pre_endpoint_floor shared head high supported early twoSlots ?_ computed
  intro v run vEarly before amount read
  have bounded : (getCurrentEpoch v.state).toNat ≤ high + 1 := by omega
  have preFork : v.fork < .pectra := by
    exact (guarded_fork_regime (shared.append run) genesis high bounded guard).2.resolve_left
      (Nat.not_le_of_gt xEarly)
  exact strict run preFork before amount read

end

end

end EthLib.Consensus.DirectSafety.Apriori.Internal

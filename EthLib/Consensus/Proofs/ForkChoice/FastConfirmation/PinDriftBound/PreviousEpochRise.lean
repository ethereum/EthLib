module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Ledger
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Reserved.Operations
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Whistleblower
import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.Trace
import Mathlib.Data.Nat.Notation
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.Transition.EffectiveFall
import EthLib.Consensus.Proofs.DirectSafety.Evidence
import EthLib.Consensus.Proofs.DirectSafety.Fields
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
import EthLib.Consensus.Proofs.Transition.BlockCredits
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Issuance
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Branch
import EthLib.Consensus.Proofs.Transition.EpochRewards
import EthLib.Consensus.Proofs.Transition.RewardDeltas
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Time
import EthLib.Consensus.Proofs.Participation
import Mathlib.Algebra.Order.Floor.Div
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.ActiveRise

/-! The pin reserve: the previous-epoch keys' rise and the reserve's assembly. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety PinKeys
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- The charge of a charged key of `K5`: the run splits at the step that starts its exit.

The charge is the key's effective balance before that step.

It counts as `exitQ`, since a key of `K5` exits at C's epoch. -/
private theorem K5_charge_site (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ Internal.K5 counted V) (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      :
    ∃ (a b : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ a)
      (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩),
      (pre.snoc step).append post = tailC ∧
        step.departureCharges.any (·.index == v.toNat) = true ∧
        (∀ w, a.state.validators.data[v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH) ∧
        v.toNat < a.state.validators.data.size ∧
        Internal.exitQ tailC v.toNat = effectiveAt a v.toNat := by
  obtain ⟨c, cMember, cIndex⟩ := charged
  obtain ⟨a, b, pre, step, post, site, vv, w, found, foundB, unset, set, amount, epoch⟩ :=
    tailC.departure_charge_site c cMember
  rw [cIndex] at found foundB
  -- the key exits at C's epoch, so the charge counts
  obtain ⟨wc, foundC, life⟩ := post.registryLifecycle.validators v.toNat w foundB
  have exitSame := life.exitEpoch set
  obtain ⟨u, foundU, activeBefore, notNow⟩ := Internal.K5_previous_only h member
  have exitC := ((previous_only_iff_exit counted u).mp ⟨activeBefore, notNow⟩).2
  have same : u = wc := Option.some.inj (foundU.symm.trans foundC)
  have counts : c.epoch ≤ (getCurrentEpoch counted).toNat := by
    have exitNat := congrArg UInt64.toNat exitSame
    subst same
    omega
  have exitQEq : Internal.exitQ tailC v.toNat = c.amount := by
    rcases Internal.exitQ_cases tailC v.toNat with ⟨none, -⟩ | ⟨d, dMember, dIndex, -, dQ⟩
    · exact absurd counts (none c cMember cIndex)
    · rw [dQ, Internal.charge_unique tailC dMember cMember (dIndex.trans cIndex.symm)]
  obtain ⟨d, dMember, dIndex, -⟩ :=
    (Run.nil.snoc step).departure_charge_of_assigned v.toNat vv w found foundB unset set
  refine ⟨a, b, pre, step, post, site, ?_, fun x hx => ?_, ?_, ?_⟩
  · refine List.any_eq_true.mpr ⟨d, ?_, by simpa using dIndex⟩
    simpa [Run.departureCharges] using dMember
  · exact (Option.some.inj (found.symm.trans hx)) ▸ unset
  · exact (Array.getElem?_eq_some_iff.mp found).1
  · simp only [exitQEq, amount, effectiveAt, found, Option.map_some, Option.getD_some]

/-- Within one epoch, a key's balance rises at most by its block credits.

A slot step inside the epoch keeps the balances.

A block step counts the net rise of the balance across it. -/
private theorem same_epoch_balance_le (i high : ℕ) {c a : ForkedBeaconState preset}
    (r : Run config checks c a) (early : a.fork < .glamsterdam)
    (same : getCurrentEpoch a.state = getCurrentEpoch c.state)
    (endEpoch : (getCurrentEpoch a.state).toNat ≤ high + 1) :
    actualBalanceAt a i ≤ actualBalanceAt c i + Internal.netScan i high r +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high r) := by
  refine Run.induction_of_same_epoch (fun z r' => (getCurrentEpoch z.state).toNat ≤ high + 1 →
      actualBalanceAt z i ≤ actualBalanceAt c i + Internal.netScan i high r' +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high r'))
    (fun _ => by simp [Internal.netScan_nil, Internal.creditScan_nil]) ?_ ?_ r early same endEpoch
  · intro f s t engine signed due ok pre' _ prior within
    have epoch : (getCurrentEpoch t).toNat = (getCurrentEpoch s).toNat := by
      simp only [getCurrentEpoch, processBlock_slot (applySignedBlock_ok ok).2.1]
    have before := prior (by simp only at within ⊢; omega)
    have net := Internal.netScan_snoc i high pre' (Step.block engine signed due ok)
    have credit := Internal.creditScan_snoc (fun _ => false) (fun s => decide (s ≠ .rewards)) i high
      pre' (Step.block engine signed due ok)
    simp only at within net credit
    simp only [show (getCurrentEpoch s).toNat ≤ high + 1 by omega, ↓reduceIte] at net credit
    rw [net, credit]
    simp only [Internal.stepNet]
    omega
  · intro middle last cached next pre' ok lastEq cachedOk kept prior within
    subst lastEq
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    have net := Internal.netScan_snoc i high pre' (Step.slot ok)
    have credit := Internal.creditScan_snoc (fun _ => false) (fun s => decide (s ≠ .rewards)) i high
      pre' (Step.slot ok)
    simp only at within kept
    rw [kept] at within
    have before := prior within
    simp only [within, ↓reduceIte] at net credit
    rw [net, credit]
    simp only [Internal.stepNet, actualBalanceAt] at before ⊢
    omega

/-- A slot step that stays in its epoch records no balance event.

It is no epoch's last slot, so no epoch pass runs.

From Electra, the upgrades record no crossing. -/
private theorem slot_events_nil {u w : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks u = .ok w) (electra : .pectra ≤ u.fork)
    (early : w.fork < .glamsterdam) (same : getCurrentEpoch w.state = getCurrentEpoch u.state)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok : Step config checks u w).balanceEvents = .ok events) :
    events = [] := by
  obtain ⟨advanced, _, crossings, -, upgrades, -, crossingOk, branch⟩ :=
    Step.balanceEvents_slot ok early replayed
  have noCrossings : crossings = [] :=
    DirectSafety.Apriori.Internal.upgradeBalanceReplay_electra_nil
      (u := ⟨u.fork, advanced⟩) electra crossingOk
  rcases branch with ⟨_, eventsEq⟩ | ⟨middle, updated, recorded, recordOk, updatedOk,
      validatorsEq, _, eventsEq, next, nextNat, nextSlot, nextMod, -⟩
  · rw [eventsEq, noCrossings]
  · exfalso
    have mod0 := congrArg UInt64.toNat nextMod
    rw [UInt64.toNat_mod] at mod0
    have sameNat := congrArg UInt64.toNat same
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat,
      (processUpgrades_slot upgrades).trans nextSlot, nextNat, Nat.succ_div] at sameNat
    rw [nextNat] at mod0
    have dvd := Nat.dvd_of_mod_eq_zero mod0
    simp only [dvd, ↓reduceIte] at sameNat
    omega

/-- Within one epoch, a key has no consolidation credit and no deposit credit.

A block step records no consolidation, and a deposit of a block credits no balance.

A slot step inside the epoch records no event.

Each consolidation and deposit event of the run lies in a slot step that crosses an epoch.

So the run has none. -/
private theorem same_epoch_no_epoch_credits (v : ValidatorIndex) (high : ℕ)
    {c a : ForkedBeaconState preset}
    (r : Run config checks c a) (electra : .pectra ≤ c.fork) (early : a.fork < .glamsterdam)
    (same : getCurrentEpoch a.state = getCurrentEpoch c.state) :
    (Internal.creditScan (fun s => decide (s = .consolidations)) (fun s => decide (s =
      .consolidations))
        v.toNat high r) = 0 ∧
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high r) = 0 :=
        by
  obtain ⟨events, replayed⟩ := r.balanceEvents_ok early high
  obtain ⟨deposits, consolidations⟩ := Internal.run_located r electra early high replayed
  -- a slot step of the run starts and ends in the epoch of the run, so it records no event
  have quiet : ∀ (u w : ForkedBeaconState preset) (ok : advanceSlotAcross config checks u = .ok w)
      (es : List (BalanceEvent preset)), r.Contains (Step.slot ok) →
      (Step.slot ok : Step config checks u w).balanceEvents = .ok es → es = [] := by
    intro u w ok es contained replayedEs
    obtain ⟨p1, p2, rfl⟩ := r.contains_split (Step.slot ok) contained
    have uElectra : .pectra ≤ u.fork := Nat.le_trans electra (fork_le_of_chainSteps p1.chainSteps)
    have wEarly : w.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps p2.chainSteps) early
    have lo := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps p1.chainSteps)
    have mid := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      (Run.nil.snoc (Step.slot ok) : Run config checks u w).chainSteps)
    have hi := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps p2.chainSteps)
    have sameNat := congrArg UInt64.toNat same
    exact slot_events_nil ok uElectra wEarly (UInt64.toNat_inj.mp (by omega)) replayedEs
  refine ⟨Nat.le_zero.mp ((Internal.scan_le_events _ _ (· = .consolidations) (by intro s; simp) r
    high v
    replayed).trans (le_of_eq (List.sum_eq_zero fun n member => ?_))),
    Nat.le_zero.mp ((Internal.scan_le_events _ _ (· = .deposits) (by intro s; simp) r high v
    replayed).trans (le_of_eq (List.sum_eq_zero fun n member => ?_)))⟩
  · obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
    obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
    obtain ⟨u, w, ok, es, contained, replayedEs, inStep⟩ :=
      consolidations e inEvents (of_decide_eq_true sourceEq)
    simp [quiet u w ok es contained replayedEs] at inStep
  · obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp member
    obtain ⟨inEvents, sourceEq⟩ := List.mem_filter.mp filtered
    rcases deposits e inEvents (of_decide_eq_true sourceEq) with unconditional |
      ⟨u, w, ok, es, contained, replayedEs, inStep, -⟩
    · have := unconditional v.toNat
      simp only [Internal.keyCredit]
      omega
    · simp [quiet u w ok es contained replayedEs] at inStep

/-- A state that starts its epoch on a run from genesis is within the bands of hysteresis.

The steps of the run before it are all in earlier epochs.

So the last one is a slot step that crossed into the epoch of `b`.

The epoch transition of that step sets the bands, and the upgrades of the slot keep them.

A run with no step ends at genesis, which is a Phase 0 state, so it ends before Fulu. -/
private theorem hysteresis_at_epoch_start
    (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (earlier : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      toB.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch b).toNat) :
    Hysteresis b := by
  have crossed : ∀ {x : ForkedBeaconState preset} (run : Run config checks g x),
      x = ⟨fork, b⟩ → (∀ {u w : ForkedBeaconState preset} (st : Step config checks u w),
        run.Contains st → (getCurrentEpoch u.state).toNat < (getCurrentEpoch b).toNat) →
      Hysteresis b := by
    intro x run hx before
    cases run with
    | nil =>
      have fulu : .fusaka ≤ g.fork := by rw [hx]; exact h.fulu
      obtain ⟨_, _, _, initialized⟩ := h.genesis
      obtain ⟨phase0, -⟩ := initializeBeaconStateFromEth1_ok initialized
      exact absurd (Nat.lt_of_le_of_lt fulu phase0) (by decide)
    | @snoc middle last pre' st =>
      subst hx
      have crossing := before st (.last pre' st)
      have ok := DirectSafety.Apriori.Internal.slot_of_crossing st crossing
      have first : b.slot % preset.SLOTS_PER_EPOCH = 0 := by
        have next : b.slot.toNat = middle.state.slot.toNat + 1 :=
          (advanceSlotAcross_cases ok).1
        by_contra inside
        have notDvd : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ middle.state.slot.toNat + 1 := by
          rw [Nat.dvd_iff_mod_eq_zero, ← next]
          intro zero
          exact inside (UInt64.toNat_inj.mp (by rw [UInt64.toNat_mod, zero, UInt64.toNat_zero]))
        simp only [getCurrentEpoch_toNat, next, Nat.succ_div, notDvd, ↓reduceIte,
          Nat.add_zero, Nat.lt_irrefl] at crossing
      exact hysteresis_of_run_slot h.genesis h.bands h.caps h.facts.activation pre' ok h.early
        first
  exact crossed toB rfl earlier

/-- A key charged at a step is in the registry at any state of the epoch that it started.

The state `n` has the bands of hysteresis.

A run leads from `n` to the step's start `a`, inside one epoch.

There the key's balance is within the upward band of its effective balance.

The effective balance stays to the charge.

Over the rest of that epoch the balance rises at most by the key's block credits.

The key is active at the charge step, so it is in the registry at `n`. -/
private theorem charge_start_at (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) {n a b : ForkedBeaconState preset} (rest : Run config checks n a)
    (step : Step config checks a b) (i : ℕ) (inside : i < a.state.validators.data.size)
    (unset : ∀ w, a.state.validators.data[i]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    (aFulu : .fusaka ≤ a.fork) (aEarly : a.fork < .glamsterdam)
    (same : getCurrentEpoch n.state = getCurrentEpoch a.state) (hyst : Hysteresis n.state)
    (endEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1)
    (charged : step.departureCharges.any (·.index == i) = true) :
    i < n.state.validators.data.size ∧ effectiveAt n i = effectiveAt a i ∧
      min (actualBalanceAt n i) (PinTerms.capAt n i) ≤ effectiveAt n i + preset.upwardBand ∧
      (effectiveAt n i < PinTerms.capAt n i →
        actualBalanceAt n i ≤ effectiveAt n i + preset.upwardBand) ∧
      actualBalanceAt a i ≤ actualBalanceAt n i + Internal.netScan i highC rest +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC rest) := by
  -- the key is active at the charge, so it is in the registry at the start of the epoch
  obtain ⟨charge, member, index⟩ := List.any_eq_true.mp charged
  obtain ⟨w, later, assigned, -⟩ := (Run.nil.snoc step).departure_charge_exit charge
    (by simpa [Run.departureCharges] using member)
  rw [beq_iff_eq.mp index] at later
  obtain ⟨v, found⟩ : ∃ v, a.state.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have far := unset v found
  have activated := step.chainStep.exit_assigned_activated (Nat.le_trans (by decide) aFulu)
    found later far assigned
  have activeA : isActiveAt a.state (getCurrentEpoch a.state) i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨v, found, ?_⟩
    have below : getCurrentEpoch a.state < FAR_FUTURE_EPOCH := by
      rw [UInt64.lt_iff_toNat_lt, getCurrentEpoch_toNat]
      have := a.state.slot.toNat_lt
      have := Nat.div_le_div_left (a := a.state.slot.toNat) h.twoSlots (by decide : 0 < 2)
      have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, far]
    exact ⟨activated, below⟩
  have activeN : isActiveAt n.state (getCurrentEpoch a.state) i = true := by
    rw [← activeKept_of_chainSteps rest.chainSteps _
      (same ▸ getCurrentEpoch_le_activityFixedEpoch n.state)]
    exact activeA
  obtain ⟨vn, foundN, -⟩ := isActiveAt_eq_true_iff.mp activeN
  have insideN : i < n.state.validators.data.size := (Array.getElem?_eq_some_iff.mp foundN).1
  have up : effectiveAt n i < PinTerms.capAt n i →
      actualBalanceAt n i ≤ effectiveAt n i + preset.upwardBand := by
    intro lt
    cases bal : n.state.balances.data[i]? with
    | none => simp [actualBalanceAt, bal]
    | some balance =>
      simp only [effectiveAt, PinTerms.capAt, foundN, Option.map_some, Option.getD_some] at lt
      simpa [actualBalanceAt, effectiveAt, bal, foundN] using
        hyst.up i vn balance foundN bal (UInt64.lt_iff_toNat_lt.mpr lt)
  refine ⟨insideN, (DirectSafety.run_same_epoch_effective rest aEarly same.symm i insideN).symm,
    ?_, up, same_epoch_balance_le i highC rest aEarly same.symm endEpoch⟩
  by_cases lt : effectiveAt n i < PinTerms.capAt n i
  · exact (Nat.min_le_left _ _).trans (up lt)
  · exact (Nat.min_le_right _ _).trans (by omega)

/-- The start-of-epoch half of the charge arm, for a charge after the split's epoch.

The run to the charge crosses an epoch boundary, at the state `c`.

There the key's balance is within the upward band of its effective balance.

The effective balance stays to the charge.

Over the rest of that epoch the balance rises at most by the key's block credits.

The key is active at the charge step, so it is in the registry at `c`.

The fork of `a` is before Gloas, since `post` runs on to C.

The epoch of `a` is at most `highC + 1`, since `post` runs on to C. -/
private theorem charge_epoch_start (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) {y : ForkedBeaconState preset} (yFork : y.fork = fork)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b y) (i : ℕ)
    (inside : i < a.state.validators.data.size)
    (unset : ∀ w, a.state.validators.data[i]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    (started : (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat)
    (endEpochC : (getCurrentEpoch y.state).toNat ≤ highC + 1)
    (charged : step.departureCharges.any (·.index == i) = true) :
    ∃ (c : ForkedBeaconState preset) (before : Run config checks ⟨fork, split⟩ c)
      (r : Run config checks c a), before.append r = pre ∧ i < c.state.validators.data.size ∧
      getCurrentEpoch c.state = getCurrentEpoch a.state ∧ effectiveAt c i = effectiveAt a i ∧
      min (actualBalanceAt c i) (PinTerms.capAt c i) ≤ effectiveAt c i + preset.upwardBand ∧
      (effectiveAt c i < PinTerms.capAt c i →
        actualBalanceAt c i ≤ effectiveAt c i + preset.upwardBand) ∧
      actualBalanceAt a i ≤ actualBalanceAt c i + Internal.netScan i highC r +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC r) := by
  have aFork : a.fork = fork := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post)
    (by rw [yFork]; exact Nat.le_refl _)
  have aEarly : a.fork < .glamsterdam := by rw [aFork]; exact h.early
  have aFulu : .fusaka ≤ a.fork := by rw [aFork]; exact h.fulu
  have aCounted := UInt64.le_iff_toNat_le.mp
    (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
  obtain ⟨z, n, pre0, ok, rest, cut, hz, hn⟩ :=
    Run.cross_split pre ((getCurrentEpoch a.state).toNat - 1) (by simp only; omega) (by omega)
  have same : getCurrentEpoch n.state = getCurrentEpoch a.state := UInt64.toNat_inj.mp (by omega)
  have zFulu : .fusaka ≤ z.fork := Nat.le_trans h.fulu (fork_le_of_chainSteps pre0.chainSteps)
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) aEarly
  -- the bands of hysteresis at the start of the epoch
  have hyst := DirectSafety.Apriori.Internal.hysteresis_of_crossing_slot ok h.bands zFulu nEarly
    (by omega)
  obtain ⟨insideN, effEq, floor, up, rise⟩ := charge_start_at h highC rest step i inside unset
    aFulu aEarly same hyst (by omega) charged
  exact ⟨n, pre0.snoc (Step.slot ok), rest, cut.symm, insideN, same, effEq, floor, up, rise⟩

/-- The switch case of the start of the epoch.

A key at its cap that switches to compounding in the epoch keeps at most the old cap of balance.

The switch moves the balance beyond the old cap into the pending deposits.

The step that switches also takes the block credits that follow the switch in it.

So the credits are the gross ones: the net rise of that step can be zero while a credit is not. -/
private theorem charge_flip (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) {c a : ForkedBeaconState preset}
    (toC : Run config checks g c) (r : Run config checks c a) (i : ℕ)
    (inside : i < c.state.validators.data.size)
    (same : getCurrentEpoch c.state = getCurrentEpoch a.state)
    (sameFork : a.fork = fork) (cFork : c.fork = fork)
    (endEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1)
    (flipped : PinTerms.capAt c i ≠ PinTerms.capAt a i)
    (atCap : ¬ effectiveAt c i < PinTerms.capAt c i) :
    min (actualBalanceAt a i) (PinTerms.capAt a i) ≤ effectiveAt c i + Internal.grossScan i highC r
      +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC r) := by
  classical
  have sameC : fork = c.fork := cFork.symm
  obtain ⟨cf, cs⟩ := c
  obtain ⟨af, as⟩ := a
  simp only at sameC sameFork endEpoch same
  have sameA : fork = af := sameFork.symm
  subst sameC sameA
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- the caps: the key's cap is the activation balance at C and the largest balance after
  have insideA : i < as.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps r.chainSteps)
  obtain ⟨kindC, -, -⟩ := Internal.capAt_kind (z := cs) h i inside
  obtain ⟨kindA, -, -⟩ := Internal.capAt_kind (z := as) h i insideA
  have capMono := Internal.cap_le_cap_of_run h.caps r h.early i
  have minMax := UInt64.le_iff_toNat_le.mp h.caps.compounding
  have capC : PinTerms.capAt (⟨fork, cs⟩ : ForkedBeaconState preset) i =
      preset.MIN_ACTIVATION_BALANCE.toNat := by omega
  have capA : PinTerms.capAt (⟨fork, as⟩ : ForkedBeaconState preset) i =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by omega
  have strict : preset.MIN_ACTIVATION_BALANCE.toNat <
      PinTerms.capAt (⟨fork, as⟩ : ForkedBeaconState preset) i := by omega
  have effC : preset.MIN_ACTIVATION_BALANCE.toNat ≤
      effectiveAt (⟨fork, cs⟩ : ForkedBeaconState preset) i := by omega
  -- the run splits at the step that makes the key compound
  obtain ⟨m, n, pre, step, post, cut, flatM, largeN, balN, sameEpoch⟩ :=
    Internal.Run.flip_split r h.early h.fulu (Run.invariant (Genesis.invariant h.genesis)
      toC) i (by omega) strict
  obtain ⟨mf, ms⟩ := m
  obtain ⟨nf, ns⟩ := n
  have sameM : fork = mf :=
    (Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
  have sameN : fork = nf := (Internal.fork_eq_of_run (pre.snoc step) post (Nat.le_refl _)).symm
  subst sameM sameN
  have epochPre := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
  have epochPost := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have sameNat := congrArg UInt64.toNat same
  simp only at epochPre epochStep epochPost sameNat sameEpoch
  have epochsEq : (getCurrentEpoch ns).toNat = (getCurrentEpoch as).toNat := by omega
  -- the credits of the step that switches are gross, since it is a block step
  have gross : Internal.stepCredit (fun _ => true) (fun _ => true) i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
        false) i
        step := by
    cases step with
    | slot ok =>
      exact absurd rfl (Internal.step_flip_not_slot (Step.slot ok) h.early h.fulu i
        (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))
        (by omega) largeN ok)
    | block engine signed due ok =>
      exact Internal.block_credit_le_gross (due := due) (ok := ok) (toC.append pre)
        h.genesis h.early electra i
  -- after the switch the balance rises by the credits alone
  have after := same_epoch_balance_le i highC post h.early (UInt64.toNat_inj.mp epochsEq.symm)
    endEpoch
  obtain ⟨eventsPost, replayedPost⟩ := post.balanceEvents_ok h.early highC
  have net := (Internal.credits_le_sources (toC.append (pre.snoc step)) h.genesis post
    h.early (Nat.le_trans (by decide) h.fulu) i highC replayedPost).2.1
  subst cut
  have grossAll := Internal.grossScan_append i highC (pre.snoc step) post
  have grossStep := Internal.grossScan_snoc i highC pre step
  have creditAll := Internal.creditScan_append (fun _ => false) (fun s => decide (s ≠ .rewards)) i
    highC
    (pre.snoc step) post
  have within :
      (getCurrentEpoch (⟨fork, ms⟩ : ForkedBeaconState preset).state).toNat ≤ highC + 1 := by
    show (getCurrentEpoch ms).toNat ≤ highC + 1
    omega
  simp only [within, ↓reduceIte] at grossStep
  rw [grossAll, grossStep, creditAll]
  rw [capA]
  omega

/-- The exact rise fold: from a run that has the key's charge, its balance rises by the steps after.

The sum includes epoch rewards from the step that first charges the key onward.

It also adds its net block credits and the credits of its slot steps other than the rewards.

The cumulative rewards do not decrease along the run. -/
private theorem rise_fold (i high : ℕ) {x m : ForkedBeaconState preset}
    (pre : Run config checks x m) (seen : (Internal.riseScan i high pre).1 = true) :
    ∀ {y : ForkedBeaconState preset} (t : Run config checks m y), y.fork < .glamsterdam →
      (getCurrentEpoch y.state).toNat ≤ high + 1 →
      (Internal.riseScan i high (pre.append t)).1 = true ∧
      (Internal.riseScan i high pre).2 ≤ (Internal.riseScan i high (pre.append t)).2 ∧
      actualBalanceAt y i + (Internal.riseScan i high pre).2 ≤ actualBalanceAt m i +
        (Internal.riseScan i high (pre.append t)).2 + Internal.netScan i high t +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high t) := by
  intro y t
  induction t with
  | nil =>
    intro _ _
    refine ⟨seen, Nat.le_refl _, ?_⟩
    show actualBalanceAt m i + (Internal.riseScan i high pre).2 ≤
      actualBalanceAt m i + (Internal.riseScan i high pre).2 + 0 + 0
    omega
  | @snoc n y t step ih =>
    intro early endEpoch
    have nEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have ny := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    obtain ⟨flag, mono, fold⟩ := ih nEarly (by omega)
    have within : (getCurrentEpoch n.state).toNat ≤ high + 1 := by omega
    have bound := Internal.step_balance_le step early i
    have net := Internal.netScan_snoc i high t step
    have credit := Internal.creditScan_snoc (fun _ => false) (fun s => decide (s ≠ .rewards)) i high
      t step
    simp only [within, ↓reduceIte] at net credit
    change (Internal.riseScan i high ((pre.append t).snoc step)).1 = true ∧
      (Internal.riseScan i high pre).2 ≤ (Internal.riseScan i high ((pre.append t).snoc step)).2 ∧
      actualBalanceAt y i + (Internal.riseScan i high pre).2 ≤ actualBalanceAt m i +
        (Internal.riseScan i high ((pre.append t).snoc step)).2 + Internal.netScan i high (t.snoc
          step) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high (t.snoc step))
    simp only [Internal.riseScan, flag, Bool.true_or, true_or, true_and, within, ↓reduceIte]
    rw [net, credit]
    exact ⟨by omega, by omega⟩

/-- A key with an assigned exit has no larger cap at the end of a run than at its start.

Compounding needs an unset exit, so the run cannot switch the key to it. -/
private theorem capAt_le_of_exit {x z : ForkedBeaconState preset} (r : Run config checks x z)
    (caps : CapOrder preset) (electraX : .pectra ≤ x.fork) (electraZ : .pectra ≤ z.fork)
    (early : z.fork < .glamsterdam) (i : ℕ) {w : Validator}
    (found : x.state.validators.data[i]? = some w) (assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    PinTerms.capAt z i ≤ PinTerms.capAt x i := by
  obtain ⟨wz, foundZ, kept⟩ := r.compounding_of_exit_assigned caps.activation caps.compounding
    early i w found assigned
  rw [Internal.capAt_of_found electraZ foundZ, Internal.capAt_of_found electraX found]
  have order := UInt64.le_iff_toNat_le.mp caps.compounding
  cases hz : hasCompoundingWithdrawalCredential wz <;>
    cases hb : hasCompoundingWithdrawalCredential w <;> simp_all

/-- The exact rise of a charged key's balance after its charge.

The cap is fixed from the state `b` after the step that starts the exit.

The step itself can switch the key to compounding: one payload can switch it, then start its exit.

So the cap is at most `capAt b` on the whole run, and on `post`.

From `a` the balance can rise by the epoch rewards after the charge and by other credits.

From `b` it rises by the same rewards and the credits of `post`. -/
private theorem charge_rise_fold (h : Setting config checks g split fin pulled anc counted V)
    {xs : BeaconState preset fork}
    (highC : ℕ) {y : ForkedBeaconState preset} (yFork : y.fork = fork)
    (endEpochC : (getCurrentEpoch y.state).toNat ≤ highC + 1)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, xs⟩ a)
    (step : Step config checks a b) (post : Run config checks b y) (i : ℕ)
    (charged : step.departureCharges.any (·.index == i) = true) :
    (∀ z ∈ ((Run.nil.snoc step).append post).balancePath,
      PinTerms.capAt z i ≤ PinTerms.capAt b i) ∧
    (∀ z ∈ post.balancePath, PinTerms.capAt z i ≤ PinTerms.capAt b i) ∧
    (∀ z ∈ ((Run.nil.snoc step).append post).balancePath, actualBalanceAt z i ≤
      actualBalanceAt a i + (Internal.riseScan i highC ((pre.snoc step).append post)).2 +
        Internal.netScan i highC ((Run.nil.snoc step).append post) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC
          ((Run.nil.snoc step).append post))) ∧
    ∀ z ∈ post.balancePath, actualBalanceAt z i ≤
      actualBalanceAt b i + (Internal.riseScan i highC ((pre.snoc step).append post)).2 +
        Internal.netScan i highC post +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC post) := by
  have yBack : y.fork ≤ fork := by rw [yFork]; exact Nat.le_refl _
  have yEarly : y.fork < .glamsterdam := by rw [yFork]; exact h.early
  have aFork : a.fork = fork := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) yBack
  have bFork : b.fork = fork := Internal.fork_eq_of_run (pre.snoc step) post yBack
  have aFulu : .fusaka ≤ a.fork := by rw [aFork]; exact h.fulu
  have bEarly : b.fork < .glamsterdam := by rw [bFork]; exact h.early
  have stepPath : ∀ p ∈ step.balancePath, p = a ∨ p = b := by
    cases step with
    | block => intro p hp; simpa [Step.balancePath] using hp
    | slot ok =>
      obtain ⟨next, advanced, upgraded⟩ := bind_ok_iff.mp ok
      have same := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded
        aFulu bEarly
      subst same
      intro p hp
      simpa [Step.balancePath, advanced, Except.toOption] using hp
  have bCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have ab := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
  have within : (getCurrentEpoch a.state).toNat ≤ highC + 1 := by omega
  -- the charge: the key's exit is set at `b`
  obtain ⟨charge, member, index⟩ := List.any_eq_true.mp charged
  obtain ⟨w, foundB, assigned, -⟩ := (Run.nil.snoc step).departure_charge_exit charge
    (by simpa [Run.departureCharges] using member)
  rw [beq_iff_eq.mp index] at foundB
  -- a state of the path of `post` splits it
  have splitPost : ∀ z ∈ post.balancePath, ∃ (r1 : Run config checks b z)
      (r2 : Run config checks z y), r1.append r2 = post := fun z hz => by
    obtain ⟨r1, r2, eq⟩ := Internal.balancePath_endpoint post (Run.nil : Run config checks y y)
      (by rw [bFork]; exact yBack) hz
    exact ⟨r1, r2, eq⟩
  -- the cap: compounding needs an unset exit, so the cap is fixed from `b`
  have capPost : ∀ z ∈ post.balancePath, PinTerms.capAt z i ≤ PinTerms.capAt b i := by
    intro z hz
    obtain ⟨r1, r2, -⟩ := splitPost z hz
    have zFork : z.fork = fork := Internal.fork_eq_of_run ((pre.snoc step).append r1) r2 yBack
    exact capAt_le_of_exit r1 h.caps (by rw [bFork]; exact Nat.le_trans (by decide) h.fulu)
      (by rw [zFork]; exact Nat.le_trans (by decide) h.fulu) (by rw [zFork]; exact h.early) i
      foundB assigned
  -- the fold from `b`, through the charged prefix
  have seen : (Internal.riseScan i highC (pre.snoc step)).1 = true := by
    simp [Internal.riseScan, charged]
  have riseStep : (Internal.riseScan i highC (pre.snoc step)).2 =
      (Internal.riseScan i highC pre).2 + Internal.epochRewards i step := by
    simp [Internal.riseScan, charged, within]
  have stepBound := Internal.step_balance_le step bEarly i
  have netStep : Internal.netScan i highC ((Run.nil.snoc step).append post) =
      Internal.stepNet i step + Internal.netScan i highC post := by
    rw [Internal.netScan_append, Internal.netScan_snoc, Internal.netScan_nil]
    simp [within]
  have creditStep : (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC
      ((Run.nil.snoc step).append post)) =
      Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC post) := by
    rw [Internal.creditScan_append, Internal.creditScan_snoc, Internal.creditScan_nil]
    simp [within]
  have fromB : ∀ z ∈ post.balancePath, actualBalanceAt z i + (Internal.riseScan i highC (pre.snoc
    step)).2 ≤
      actualBalanceAt b i + (Internal.riseScan i highC ((pre.snoc step).append post)).2 +
        Internal.netScan i highC post +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC post) := by
    intro z hz
    obtain ⟨r1, r2, eq⟩ := splitPost z hz
    have zEarly : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) yEarly
    have zCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
    obtain ⟨flag, -, fold⟩ := rise_fold i highC (pre.snoc step) seen r1 zEarly (by omega)
    obtain ⟨-, mono, -⟩ := rise_fold i highC ((pre.snoc step).append r1) flag r2 yEarly endEpochC
    rw [← Run.append_assoc, eq] at mono
    have net := Internal.netScan_append i highC r1 r2
    have credit := Internal.creditScan_append (fun _ => false) (fun s => decide (s ≠ .rewards)) i
      highC r1 r2
    rw [eq] at net credit
    omega
  refine ⟨fun z hz => ?_, capPost, fun z hz => ?_, fun z hz => ?_⟩
  · rw [Run.balancePath_append] at hz
    rcases List.mem_append.mp hz with head | tail
    · simp only [Run.balancePath, List.mem_append, List.mem_singleton] at head
      have capA := Internal.cap_le_cap_of_run h.caps (Run.nil.snoc step) bEarly i
      rcases head with rfl | onStep
      · exact capA
      · rcases stepPath z onStep with rfl | rfl
        · exact capA
        · exact Nat.le_refl _
    · exact capPost z (List.mem_of_mem_tail tail)
  · have riseLe := (rise_fold i highC (pre.snoc step) seen post yEarly endEpochC).2.1
    rw [Run.balancePath_append] at hz
    rcases List.mem_append.mp hz with head | tail
    · simp only [Run.balancePath, List.mem_append, List.mem_singleton] at head
      rcases head with rfl | onStep
      · omega
      · rcases stepPath z onStep with rfl | rfl
        · omega
        · rw [netStep, creditStep]
          omega
    · have := fromB z (List.mem_of_mem_tail tail)
      rw [netStep, creditStep]
      omega
  · have := fromB z hz
    omega

/-- The credits of a charged key from the epoch's start to a state `y`.

Proposer, consolidation, whistleblower and sync credits bound them.

The key is not yet withdrawable at `y` (`held`), so its deposits from the charge on are postponed.

The credits before the charge are the gross ones, which bound the net ones.

The first bound adds the credits of the run from the charge on, read net.

The second bound adds the whole credits of the charge step, then those of `post`, read net.

It needs the charge step to be a block step.

A slot step's whole credits hold its epoch rewards, which none of the three sources pays. -/
private theorem charge_credits_to (h : Setting config checks g split fin pulled anc counted V)
    {xs : BeaconState preset fork} (toX : Run config checks g ⟨fork, xs⟩)
    {y : ForkedBeaconState preset} (yFork : y.fork = fork)
    (tailY : Run config checks ⟨fork, xs⟩ y) (highC : ℕ)
    (endEpochY : (getCurrentEpoch y.state).toNat ≤ highC + 1)
    {eventsY : List (BalanceEvent preset)} (replayedY : tailY.balanceEvents highC = .ok eventsY)
    {v : ValidatorIndex}
    {a b c : ForkedBeaconState preset} (pre : Run config checks ⟨fork, xs⟩ a)
    (step : Step config checks a b) (post : Run config checks b y)
    (site : (pre.snoc step).append post = tailY)
    (charged : step.departureCharges.any (·.index == v.toNat) = true)
    (before : Run config checks ⟨fork, xs⟩ c) (r : Run config checks c a)
    (cut : before.append r = pre) (same : getCurrentEpoch c.state = getCurrentEpoch a.state)
    (held : ∀ w, b.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch y.state).toNat < w.withdrawableEpoch.toNat) :
    (Internal.grossScan v.toNat highC r + (Internal.creditScan (fun _ => false) (fun s => decide (s
      ≠ .rewards))
        v.toNat highC r) +
      (Internal.netScan v.toNat highC ((Run.nil.snoc step).append post) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC
          ((Run.nil.snoc step).append post))) ≤
      Internal.propC tailY highC v.toNat + Internal.whistC tailY highC v.toNat + Internal.syncCr
        eventsY v.toNat) ∧
    ((∀ ok, step ≠ Step.slot ok) →
      Internal.grossScan v.toNat highC r + (Internal.creditScan (fun _ => false) (fun s => decide (s
        ≠ .rewards))
        v.toNat highC r) + Internal.stepCredit (fun _ => true) (fun _ => true) v.toNat step +
      (Internal.netScan v.toNat highC post +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC post))
          ≤
      Internal.propC tailY highC v.toNat + Internal.whistC tailY highC v.toNat + Internal.syncCr
        eventsY v.toNat) := by
  subst site
  subst cut
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have yBack : y.fork ≤ fork := by rw [yFork]; exact Nat.le_refl _
  have yEarly : y.fork < .glamsterdam := by rw [yFork]; exact h.early
  have cFork : c.fork = fork :=
    Internal.fork_eq_of_run before (r.append ((Run.nil.snoc step).append post)) yBack
  have aFork : a.fork = fork :=
    Internal.fork_eq_of_run (before.append r) ((Run.nil.snoc step).append post) yBack
  have bFork : b.fork = fork := Internal.fork_eq_of_run ((before.append r).snoc step) post yBack
  have cEarly : c.fork < .glamsterdam := by rw [cFork]; exact h.early
  have aEarly : a.fork < .glamsterdam := by rw [aFork]; exact h.early
  have bEarly : b.fork < .glamsterdam := by rw [bFork]; exact h.early
  have cElectra : .pectra ≤ c.fork := by rw [cFork]; exact electra
  have aElectra : .pectra ≤ a.fork := by rw [aFork]; exact electra
  have aEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      ((Run.nil.snoc step).append post).chainSteps)) endEpochY
  obtain ⟨e0, h0⟩ := before.balanceEvents_ok cEarly highC
  obtain ⟨er, hr⟩ := r.balanceEvents_ok aEarly highC
  obtain ⟨es, hs⟩ := step.balanceEvents_ok bEarly
  obtain ⟨ep, hp⟩ := post.balanceEvents_ok yEarly highC
  have one : (Run.nil.snoc step : Run config checks a b).balanceEvents highC = .ok es := by
    simp [Run.balanceEvents, aEpoch, hs, pure, Except.pure]
    rfl
  have hR := DirectSafety.Apriori.Internal.balanceEvents_append _ post highC one hp
  have hX := DirectSafety.Apriori.Internal.balanceEvents_append r _ highC hr hR
  have eqX := (r.snoc_append_eq step post).symm
  have eqTail : ((before.append r).snoc step).append post =
      before.append (r.append ((Run.nil.snoc step).append post)) :=
    ((before.append r).snoc_append_eq step post).trans (Run.append_assoc before r _).symm
  rw [eqTail, DirectSafety.Apriori.Internal.balanceEvents_append _ _ highC h0 hX] at replayedY
  obtain rfl := Except.ok.inj replayedY
  rw [eqTail]
  -- the key has no deposit credit from the epoch's start to C
  obtain ⟨_, w, foundA, foundB, unset, set⟩ := Internal.charge_exits step charged
  have inside : v.toNat < a.state.validators.data.size := (Array.getElem?_eq_some_iff.mp foundA).1
  have exited := Internal.exitEpoch_toNat_lt_of_ne_far set
  have depR : (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
    r) =
      0 := by
    refine Nat.le_zero.mp
      ((Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits)) (· = .deposits)
        (by intro s; simp) r highC v hr).trans (Nat.le_of_eq ?_))
    refine Internal.Run.exiting_deposit_credit_zero_of_exited r cElectra aEarly highC hr v.toNat ?_
    intro u' w' ok contains es' replayedEs e inStep sourceEq
    exfalso
    obtain ⟨pre', post', -⟩ := Run.contains_split r (Step.slot ok) contains
    have fuluU : .fusaka ≤ u'.fork := Nat.le_trans (by rw [cFork]; exact h.fulu)
      (fork_le_of_chainSteps pre'.chainSteps)
    have earlyW : w'.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps post'.chainSteps) aEarly
    have strict :=
      (Internal.Step.deposit_input ok fuluU earlyW replayedEs e inStep sourceEq).2.2.2.2
    have e1 := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre'.chainSteps)
    have e2 := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post'.chainSteps)
    have eq := congrArg UInt64.toNat same
    omega
  have depR' : (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
      ((Run.nil.snoc step).append post)) = 0 := by
    refine Nat.le_zero.mp
      ((Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits)) (· = .deposits)
        (by intro s; simp) _ highC v hR).trans (Nat.le_of_eq ?_))
    exact Internal.Run.charge_deposit_credit_zero (toX.append (before.append r))
      h.genesis step post (by rw [aFork]; exact h.fulu) yEarly highC aEpoch hR v.toNat inside w
      foundB exited (held w foundB)
  -- the credits of the run from the epoch's start, by source
  have gross := Internal.credits_le_sources (toX.append before) h.genesis
    (r.append ((Run.nil.snoc step).append post)) yEarly cElectra v.toNat highC hX
  have netR := (Internal.credits_le_sources (toX.append (before.append r)) h.genesis
    ((Run.nil.snoc step).append post) yEarly aElectra v.toNat highC hR).2.1
  have split := Internal.credC_split (r.append ((Run.nil.snoc step).append post)) highC v.toNat
  have splitN := Internal.credN_split (r.append ((Run.nil.snoc step).append post)) highC v.toNat
  have splitP := Internal.propC_split (r.append ((Run.nil.snoc step).append post)) highC v.toNat
  simp only [List.map_append, List.sum_append] at gross
  unfold Internal.propC Internal.whistC Internal.syncCr
  simp only [List.map_append, List.sum_append]
  unfold Internal.propC at splitP
  unfold Internal.whistC at gross
  simp only [Internal.creditScan_append, Internal.grossScan_append,
    Internal.netScan_append] at gross netR split splitN splitP
  simp only [Internal.creditScan_append, Internal.netScan_append] at depR' ⊢
  refine ⟨by omega, fun notSlot => ?_⟩
  have flip := (Internal.flip_credits_le_sources (toX.append before) h.genesis r step
    post notSlot yEarly cElectra v.toNat highC aEpoch (events := er ++ (es ++ ep))
    (by rw [← eqX]; exact hX)).2
  rw [← eqX] at flip
  unfold Internal.whistC at flip
  simp only [List.map_append, List.sum_append, Internal.creditScan_append] at flip
  omega

/-- The effective balance of a charged key at a state `y` of the run, after its charge.

It is the key's effective balance before the charge step, plus the upward band.

It adds the key's credits since the epoch's start.

It also adds the exact epoch rewards of the steps from the charge on.

The run starts at any state `xs` with a run `toX` from genesis.

The epoch's start is given as data.

It is the state `c`, the run `r` from it to the charge, and the hysteresis there.

The key is not yet withdrawable at `y` (`held`). -/
private theorem charge_effective_bound_of
    (h : Setting config checks g split fin pulled anc counted V)
    {xs : BeaconState preset fork} (toX : Run config checks g ⟨fork, xs⟩)
    {y : ForkedBeaconState preset} (yFork : y.fork = fork)
    (tailY : Run config checks ⟨fork, xs⟩ y) (highC : ℕ)
    (endEpochY : (getCurrentEpoch y.state).toNat ≤ highC + 1)
    {eventsY : List (BalanceEvent preset)} (replayedY : tailY.balanceEvents highC = .ok eventsY)
    {v : ValidatorIndex} {a b : ForkedBeaconState preset}
    (pre : Run config checks ⟨fork, xs⟩ a) (step : Step config checks a b)
    (post : Run config checks b y) (site : (pre.snoc step).append post = tailY)
    (hcharge : step.departureCharges.any (·.index == v.toNat) = true)
    (start : ∃ (c : ForkedBeaconState preset) (before : Run config checks ⟨fork, xs⟩ c)
      (r : Run config checks c a), before.append r = pre ∧
      v.toNat < c.state.validators.data.size ∧ getCurrentEpoch c.state = getCurrentEpoch a.state ∧
      effectiveAt c v.toNat = effectiveAt a v.toNat ∧
      min (actualBalanceAt c v.toNat) (PinTerms.capAt c v.toNat) ≤
        effectiveAt c v.toNat + preset.upwardBand ∧
      (effectiveAt c v.toNat < PinTerms.capAt c v.toNat →
        actualBalanceAt c v.toNat ≤ effectiveAt c v.toNat + preset.upwardBand) ∧
      actualBalanceAt a v.toNat ≤ actualBalanceAt c v.toNat + Internal.netScan v.toNat highC r +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC r))
    (held : ∀ w, b.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch y.state).toNat < w.withdrawableEpoch.toNat) :
    effectiveAt y v.toNat ≤ effectiveAt a v.toNat + preset.upwardBand +
      (Internal.propC tailY highC v.toNat + Internal.whistC tailY highC v.toNat + Internal.syncCr
        eventsY v.toNat) +
      (Internal.riseScan v.toNat highC tailY).2 := by
  obtain ⟨_, -, foundA0, -, unset, -⟩ := Internal.charge_exits step hcharge
  have hin : v.toNat < a.state.validators.data.size := (Array.getElem?_eq_some_iff.mp foundA0).1
  subst site
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have yBack : y.fork ≤ fork := by rw [yFork]; exact Nat.le_refl _
  have yEarly : y.fork < .glamsterdam := by rw [yFork]; exact h.early
  have aFork : a.fork = fork := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) yBack
  have bFork : b.fork = fork := Internal.fork_eq_of_run (pre.snoc step) post yBack
  have aEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      ((Run.nil.snoc step).append post).chainSteps)) endEpochY
  obtain ⟨c, before, r, cut, hc, same, effEq, hyst, hystLt, scanR⟩ := start
  subst cut
  have cFork : c.fork = fork := Internal.fork_eq_of_run before
    (r.append ((Run.nil.snoc step).append post)) yBack
  obtain ⟨er, hr⟩ := r.balanceEvents_ok (aFork ▸ h.early) highC
  have netLe := (Internal.credits_le_sources (toX.append before) h.genesis r
    (aFork ▸ h.early) (cFork ▸ electra) v.toNat highC hr).2.1
  have start : min (actualBalanceAt a v.toNat) (PinTerms.capAt a v.toNat) ≤
      effectiveAt a v.toNat + preset.upwardBand + (Internal.grossScan v.toNat highC r +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC r)) :=
          by
    by_cases capEq : PinTerms.capAt c v.toNat = PinTerms.capAt a v.toNat
    · omega
    · by_cases lt : effectiveAt c v.toNat < PinTerms.capAt c v.toNat
      · have := hystLt lt
        omega
      · have := charge_flip h highC (toX.append before) r v.toNat hc same
          aFork cFork aEpoch capEq lt
        omega
  obtain ⟨capAll, capPost, ceilings, ceilingsPost⟩ :=
    charge_rise_fold h highC yFork endEpochY _ step post v.toNat hcharge
  obtain ⟨creditsAll, creditsStep⟩ := charge_credits_to h toX yFork _ highC endEpochY replayedY _
    step post rfl hcharge before r rfl same held
  set TC : Run config checks ⟨fork, xs⟩ y := ((before.append r).snoc step).append post with hTC
  obtain ⟨_, foundA⟩ : ∃ w, a.state.validators.data[v.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem hin⟩
  have final : effectiveAt y v.toNat ≤
      effectiveAt a v.toNat + preset.upwardBand + (Internal.propC TC
        highC v.toNat + Internal.whistC TC highC v.toNat +
        Internal.syncCr eventsY v.toNat) +
      (Internal.riseScan v.toNat highC TC).2 := by
    by_cases capEq : PinTerms.capAt b v.toNat = PinTerms.capAt a v.toNat
    · -- no switch at the charge step: the rise is read from `a`
      have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax
        (toX.append (before.append r)) h.genesis h.caps (aFork ▸ h.early)
        foundA
      have startCap : effectiveAt a v.toNat ≤ PinTerms.capAt a v.toNat := by
        simpa [PinTerms.capAt, foundA] using capped
      have alignedCap := Internal.capAt_aligned h.aligned (aFork ▸ electra) foundA
      have ceil := Internal.Run.effective_ceiling_of_balance_ceiling
        ((Run.nil.snoc step).append post) yEarly (aFork ▸ h.fulu) v.toNat hin
        (effectiveAt a v.toNat + preset.upwardBand + (Internal.propC TC
          highC v.toNat + Internal.whistC TC highC v.toNat +
          Internal.syncCr eventsY v.toNat) +
          (Internal.riseScan v.toNat highC TC).2)
        _ alignedCap startCap
        (fun z member => by have := ceilings z member; omega)
        (fun z member => by have := capAll z member; omega)
      have := ceil.1
      omega
    · -- the charge step switches the key: the rise is read from `b`
      have insideB : v.toNat < b.state.validators.data.size :=
        Nat.lt_of_lt_of_le hin
          (Run.nil.snoc step : Run config checks a b).registryLifecycle.size_le
      obtain ⟨_, foundB⟩ : ∃ w, b.state.validators.data[v.toNat]? = some w :=
        ⟨_, Array.getElem?_eq_getElem insideB⟩
      have capMono := Internal.cap_le_cap_of_run h.caps (Run.nil.snoc step : Run config checks a b)
        (bFork ▸ h.early) v.toNat
      obtain ⟨capAmin, large⟩ : PinTerms.capAt a v.toNat = preset.MIN_ACTIVATION_BALANCE.toNat ∧
          preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt b v.toNat := by
        have ca := Internal.capAt_of_found (aFork ▸ electra) foundA
        have cb := Internal.capAt_of_found (bFork ▸ electra) foundB
        have order := UInt64.le_iff_toNat_le.mp h.caps.compounding
        split at ca <;> split at cb <;> omega
      have flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt a v.toNat := by omega
      have epochEq := Internal.step_flip_epoch step (bFork ▸ h.early) (aFork ▸ h.fulu) v.toNat hin
        flat
        large
      have creditsFlip := creditsStep (Internal.step_flip_not_slot step (bFork ▸ h.early)
        (aFork ▸ h.fulu) v.toNat hin flat large)
      have effB := run_same_epoch_effective (Run.nil.snoc step : Run config checks a b)
        (bFork ▸ h.early) (UInt64.toNat_inj.mp (by omega)) v.toNat hin
      have bound := Internal.step_flip_min step (bFork ▸ h.early) (aFork ▸ h.fulu)
        ((toX.append (before.append r)).invariant h.genesis.invariant)
        v.toNat flat large
      have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax
        (toX.append ((before.append r).snoc step)) h.genesis h.caps
        (bFork ▸ h.early) foundB
      have startCap : effectiveAt b v.toNat ≤ PinTerms.capAt b v.toNat := by
        simpa [PinTerms.capAt, foundB] using capped
      have alignedCap := Internal.capAt_aligned h.aligned (bFork ▸ electra) foundB
      have ceil := Internal.Run.effective_ceiling_of_balance_ceiling post yEarly
        (bFork ▸ h.fulu) v.toNat insideB
        (effectiveAt a v.toNat + preset.upwardBand + (Internal.propC TC
          highC v.toNat + Internal.whistC TC highC v.toNat +
          Internal.syncCr eventsY v.toNat) +
          (Internal.riseScan v.toNat highC TC).2)
        _ alignedCap startCap
        (fun z member => by have := ceilingsPost z member; omega) capPost
      have := ceil.1
      omega
  exact final

/-- The effective balance of a charged key at a state `y` of the run, after its charge.

It is the key's effective balance before the charge step, plus the upward band.

It adds the key's credits since the epoch's start.

It also adds the exact epoch rewards of the steps from the charge on.

The charge is in an epoch after the split's.

The key is not yet withdrawable at `y` (`held`). -/
private theorem charge_effective_bound (h : Setting config checks g split fin pulled anc counted V)
    {y : ForkedBeaconState preset} (yFork : y.fork = fork)
    (tailY : Run config checks ⟨fork, split⟩ y) (highC : ℕ)
    (endEpochY : (getCurrentEpoch y.state).toNat ≤ highC + 1)
    {eventsY : List (BalanceEvent preset)} (replayedY : tailY.balanceEvents highC = .ok eventsY)
    {v : ValidatorIndex} {a b : ForkedBeaconState preset}
    (pre : Run config checks ⟨fork, split⟩ a) (step : Step config checks a b)
    (post : Run config checks b y) (site : (pre.snoc step).append post = tailY)
    (hcharge : step.departureCharges.any (·.index == v.toNat) = true)
    (started : (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat)
    (held : ∀ w, b.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch y.state).toNat < w.withdrawableEpoch.toNat) :
    effectiveAt y v.toNat ≤ effectiveAt a v.toNat + preset.upwardBand +
      (Internal.propC tailY highC v.toNat + Internal.whistC tailY highC v.toNat + Internal.syncCr
        eventsY v.toNat) +
      (Internal.riseScan v.toNat highC tailY).2 := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨_, -, foundA0, -, unset, -⟩ := Internal.charge_exits step hcharge
  exact charge_effective_bound_of h (shared.append fromFin) yFork tailY highC endEpochY replayedY
    pre step post site hcharge
    (charge_epoch_start h highC yFork pre step post v.toNat
      (Array.getElem?_eq_some_iff.mp foundA0).1 unset started endEpochY hcharge) held

/-- A charged key of `K5` is not yet withdrawable at C, in the state after its charge step.

A key of `K5` exits at C's epoch, so it is not withdrawable at C. -/
private theorem K5_charged_held (h : Setting config checks g split fin pulled anc counted V)
    {v : ValidatorIndex} (member : v ∈ Internal.K5 counted V)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩)
    (charged : step.departureCharges.any (·.index == v.toNat) = true) :
    ∀ w, b.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch counted).toNat < w.withdrawableEpoch.toNat := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨_, w0, foundA, foundB0, unset, set⟩ := Internal.charge_exits step charged
  have bFork : b.fork = fork := Internal.fork_eq_of_run (pre.snoc step) post (Nat.le_refl _)
  intro w foundB
  obtain rfl : w = w0 := Option.some.inj (foundB.symm.trans foundB0)
  obtain ⟨u, foundU, activeBefore, notNow⟩ := Internal.K5_previous_only h member
  have exitU := ((previous_only_iff_exit counted u).mp ⟨activeBefore, notNow⟩).2
  have kept := Internal.kept_run (shared.append (fromFin.append (pre.snoc step)))
    h.genesis (by rw [bFork]; exact h.fulu) post h.early
  obtain ⟨x, foundX, life⟩ := kept.life.validators v.toNat w foundB
  obtain rfl : x = u := Option.some.inj (foundX.symm.trans foundU)
  have exitX := congrArg UInt64.toNat (life.exitEpoch set)
  obtain ⟨-, wdEq⟩ := kept.withdrawable v.toNat w x foundB foundX set
  have wdSame : x.withdrawableEpoch = w.withdrawableEpoch := by
    rcases wdEq with slashed | same
    · exact absurd slashed (by simp [Internal.K5_unslashed member x foundU])
    · exact same
  have delayed := (shared.append (fromFin.append
    ((pre.snoc step).append post))).exit_withdrawable_delay h.genesis v.toNat x foundU
    (by rw [life.exitEpoch set]; exact set)
  rw [← wdSame]
  have := (Internal.Setting.delay h)
  omega

/-- A key with no charge on a run has not started its rise on it. -/
private theorem riseScan_of_none (v high : ℕ) {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (uncharged : ∀ c ∈ run.departureCharges, c.index ≠ v) :
    Internal.riseScan v high run = (false, 0) := by
  induction run with
  | nil => rfl
  | snoc pre step ih =>
    have before := ih fun c member => uncharged c (by simp [Run.departureCharges, member])
    have notCharged : step.departureCharges.any (·.index == v) = false := by
      refine Bool.eq_false_iff.mpr fun any => ?_
      obtain ⟨c, member, index⟩ := List.any_eq_true.mp any
      exact uncharged c (by simp [Run.departureCharges, member]) (beq_iff_eq.mp index)
    simp [Internal.riseScan, before, notCharged]

/-- A run after a run with no charge of the key reads the same rise as it does alone. -/
private theorem riseScan_append_of_none (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y)
    (uncharged : ∀ c ∈ pre.departureCharges, c.index ≠ v) :
    Internal.riseScan v high (pre.append post) = Internal.riseScan v high post := by
  induction post with
  | nil => exact riseScan_of_none v high pre uncharged
  | snoc post step ih => simp only [Run.append, Internal.riseScan, ih]

/-- An assigned exit persists, so an unset key has no charge on a prefix of the run. -/
private theorem no_prefix_charge_of_unset {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) (i : ℕ)
    (unset : ∀ w, y.state.validators.data[i]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH) :
    ∀ c ∈ pre.departureCharges, c.index ≠ i := by
  intro c member index
  obtain ⟨w, found, assigned, -⟩ := (pre.append post).departure_charge_exit c
    (by simp [Run.departureCharges_append, member])
  exact assigned (unset w (index ▸ found))

/-- The credits and the rise of the shared run `pre` add to those of the run `rest` after it.

The run `pre` is inside one epoch, so it holds no consolidation or deposit credit.

The key has no charge on `pre`. -/
private theorem prefix_append_credits (v : ValidatorIndex) (highC : ℕ)
    {t : BeaconState preset fork} (pre : Run config checks ⟨fork, t⟩ ⟨fork, split⟩)
    {m : ForkedBeaconState preset} (rest : Run config checks ⟨fork, split⟩ m)
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch t)
    (noneBefore : ∀ c ∈ pre.departureCharges, c.index ≠ v.toNat) :
    Internal.propC (pre.append rest) highC v.toNat = Internal.propN pre highC v.toNat +
      Internal.propC rest highC v.toNat ∧
      Internal.whistC (pre.append rest) highC v.toNat =
        Internal.whistC pre highC v.toNat + Internal.whistC rest highC v.toNat ∧
      Internal.riseScan v.toNat highC (pre.append rest) = Internal.riseScan v.toNat highC rest := by
  have noCons := (same_epoch_no_epoch_credits v highC pre electra early sameEpoch).1
  have propPre := Internal.propC_split pre highC v.toNat
  have propSplit : Internal.propC (pre.append rest) highC v.toNat =
      Internal.propC pre highC v.toNat + Internal.propC rest highC v.toNat :=
        Internal.creditScan_append _ _ _ _ pre rest
  exact ⟨by omega, Internal.creditScan_append _ _ _ _ pre rest,
    riseScan_append_of_none v.toNat highC pre rest noneBefore⟩

/-- The data at the start of the split's epoch that bounds a key charged in that epoch.

The key's charge step starts in the split's epoch, whose first state `t` is on the shared run.

The run from `t` to the charge is `pre` and the front of C's run.

Its balance at the charge is within the upward band of its effective balance at `t`.

From `t` it rises at most by the credits of the run. -/
private theorem split_epoch_start_data (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) {t : BeaconState preset fork} (toT : Run config checks g ⟨fork, t⟩)
    (pre : Run config checks ⟨fork, t⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch t)
    (earlier : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      toT.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch t).toNat)
    {p q : ForkedBeaconState preset} (cf : Run config checks ⟨fork, split⟩ p)
    (step : Step config checks p q) (rest : Run config checks q ⟨fork, counted⟩)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) {v : ValidatorIndex}
    (inSplitEpoch : ¬ (getCurrentEpoch split).toNat < (getCurrentEpoch p.state).toNat)
    (charged : step.departureCharges.any (·.index == v.toNat) = true) :
    ∃ (c : ForkedBeaconState preset) (before : Run config checks ⟨fork, t⟩ c)
      (r : Run config checks c p), before.append r = pre.append cf ∧
      v.toNat < c.state.validators.data.size ∧ getCurrentEpoch c.state = getCurrentEpoch p.state ∧
      effectiveAt c v.toNat = effectiveAt p v.toNat ∧
      min (actualBalanceAt c v.toNat) (PinTerms.capAt c v.toNat) ≤
        effectiveAt c v.toNat + preset.upwardBand ∧
      (effectiveAt c v.toNat < PinTerms.capAt c v.toNat →
        actualBalanceAt c v.toNat ≤ effectiveAt c v.toNat + preset.upwardBand) ∧
      actualBalanceAt p v.toNat ≤ actualBalanceAt c v.toNat + Internal.netScan v.toNat highC r +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC r) :=
          by
  obtain ⟨u0, -, foundP, -, unset, -⟩ := Internal.charge_exits step charged
  have hin : v.toNat < p.state.validators.data.size := (Array.getElem?_eq_some_iff.mp foundP).1
  have pFork : p.fork = fork :=
    Internal.fork_eq_of_run cf ((Run.nil.snoc step).append rest) (Nat.le_refl _)
  have pEarly : p.fork < .glamsterdam := by rw [pFork]; exact h.early
  have pFulu : .fusaka ≤ p.fork := by rw [pFork]; exact h.fulu
  have pEpoch : (getCurrentEpoch p.state).toNat ≤ highC + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      ((Run.nil.snoc step).append rest).chainSteps)) endEpochC
  have splitLe := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps cf.chainSteps)
  have sameNat := congrArg UInt64.toNat sameEpoch
  have sameT : getCurrentEpoch (⟨fork, t⟩ : ForkedBeaconState preset).state =
      getCurrentEpoch p.state := UInt64.toNat_inj.mp (by simp only at splitLe sameNat ⊢; omega)
  have hystT := hysteresis_at_epoch_start h toT earlier
  obtain ⟨insideT, effEq, floor, up, rise⟩ := charge_start_at h highC (pre.append cf) step
    v.toNat hin unset pFulu pEarly sameT hystT pEpoch charged
  exact ⟨⟨fork, t⟩, Run.nil, pre.append cf, Run.nil_append _, insideT, sameT, effEq, floor, up,
    rise⟩

/-- Two splits of a run at steps that charge the same key start at the same state.

One split is a prefix of the other.

If the first step comes first, the exit it assigns stays assigned.

So the second step cannot charge it. -/
private theorem charge_site_start {x y p q cp cq : ForkedBeaconState preset}
    {tail : Run config checks x y} (front : Run config checks x p) (step : Step config checks p q)
    (post : Run config checks q y) (site : (front.snoc step).append post = tail)
    (cfront : Run config checks x cp) (cstep : Step config checks cp cq)
    (cpost : Run config checks cq y) (csite : (cfront.snoc cstep).append cpost = tail) {i : ℕ}
    (charges : step.departureCharges.any (·.index == i) = true)
    (cCharges : cstep.departureCharges.any (·.index == i) = true) : p = cp := by
  obtain ⟨-, w, -, foundQ, unset, assigned⟩ := Internal.charge_exits step charges
  obtain ⟨-, cw, -, foundCq, cUnset, cAssigned⟩ := Internal.charge_exits cstep cCharges
  rcases Run.prefix_total (cfront.snoc cstep) cpost (front.snoc step) post csite site with
    ⟨r, extended⟩ | ⟨r, extended⟩
  · rcases Run.prefix_snoc (cfront.snoc cstep) r front step extended with
      ⟨rfl, same⟩ | ⟨r', earlier⟩
    · cases eq_of_heq same
      rfl
    · obtain ⟨later, foundLater, life⟩ := r'.registryLifecycle.validators i cw foundCq
      exact absurd (by rw [← life.exitEpoch cAssigned]; exact unset later foundLater) cAssigned
  · rcases Run.prefix_snoc (front.snoc step) r cfront cstep extended with
      ⟨rfl, same⟩ | ⟨r', earlier⟩
    · cases eq_of_heq same
      rfl
    · obtain ⟨later, foundLater, life⟩ := r'.registryLifecycle.validators i w foundQ
      exact absurd (by rw [← life.exitEpoch assigned]; exact cUnset later foundLater) assigned

/-- The effective balance at its slashing of a charged key of the split's registry.

The run `pre` is the shared run from a state `t` of the split's epoch, or the empty run.

The bound at the charge is given as `bound`, from the charge step and the run to it.

If the slashing step assigns the exit, that step is the charge.

If an earlier step assigned it, the balance before the slashing is bounded by the charge step.

The key is not withdrawable at the slashing, since it is still slashable there.

The credits are at most the slack's credits, at eleven tenths. -/
private theorem registry_charge_of (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    {t : BeaconState preset fork} (pre : Run config checks ⟨fork, t⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch t)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {eventsP : List (BalanceEvent preset)}
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (v : ValidatorIndex) (inside : v.toNat < split.validators.data.size)
    (flag : (!(a.state.validators.data[v.toNat]?.map (·.slashed)).getD false &&
      (b.state.validators.data[v.toNat]?.map (·.slashed)).getD false) = true)
    (charged : (tailC.departureCharges.any fun c => c.index == v.toNat) = true)
    (bound : ∀ {front : Run config checks ⟨fork, split⟩ a}
        {post : Run config checks b ⟨fork, counted⟩} {p q : ForkedBeaconState preset}
        {eventsY : List (BalanceEvent preset)}
        (cf : Run config checks ⟨fork, split⟩ p) (step' : Step config checks p q)
        (post' : Run config checks q a),
        (cf.snoc step').append post' = front →
        (cf.snoc step').append ((post'.snoc step).append post) = tailC →
        step'.departureCharges.any (·.index == v.toNat) = true →
        a.fork = fork → (getCurrentEpoch a.state).toNat ≤ highC + 1 →
        front.balanceEvents highC = .ok eventsY →
        (∀ w, q.state.validators.data[v.toNat]? = some w →
          (getCurrentEpoch a.state).toNat < w.withdrawableEpoch.toNat) →
        effectiveAt a v.toNat ≤ effectiveAt p v.toNat + preset.upwardBand +
          (Internal.propC (pre.append front) highC v.toNat + Internal.whistC (pre.append front)
            highC v.toNat +
            Internal.syncCr (eventsP ++ eventsY) v.toNat) + (Internal.riseScan v.toNat highC
              (pre.append front)).2) :
    effectiveAt a v.toNat ≤ Internal.chargeAmt tailC v.toNat + Internal.riseQ tailC highC v.toNat +
      (Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
        eventsP v.toNat) +
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin v.toNat := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at flag
  obtain ⟨flagA, flagB⟩ := flag
  obtain ⟨front, post, cut, aEarly, aEpoch⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have insideA : v.toNat < a.state.validators.data.size :=
    Nat.lt_of_lt_of_le inside front.registryLifecycle.size_le
  have insideB : v.toNat < b.state.validators.data.size :=
    Nat.lt_of_lt_of_le insideA (Run.nil.snoc step : Run config checks a b).registryLifecycle.size_le
  obtain ⟨old, foundA⟩ : ∃ w, a.state.validators.data[v.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem insideA⟩
  obtain ⟨new, foundB⟩ : ∃ w, b.state.validators.data[v.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem insideB⟩
  have cleanA : old.slashed = false := by simpa [foundA] using flagA
  have markedB : new.slashed = true := by simpa [foundB] using flagB
  by_cases unset : old.exitEpoch = FAR_FUTURE_EPOCH
  · -- the slashing assigns the exit, so it is the charge
    have := Internal.slash_exit_charge h fromFin tailC step member v.toNat old new foundA foundB
      unset
      markedB
    omega
  -- an earlier step assigned the exit
  subst cut
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have aFork : a.fork = fork :=
    Internal.fork_eq_of_run front ((Run.nil.snoc step).append post) (Nat.le_refl _)
  have aEpoch' : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch counted).toNat := aEpoch
  have unsetSplit : ∀ w, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[
      v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH := by
    intro w0 found0
    by_contra assigned0
    obtain ⟨c, cMember, cIndex⟩ := List.any_eq_true.mp charged
    have cIndex' : c.index = v.toNat := by simpa using cIndex
    obtain ⟨p', q', pre', step', post', -, vv, ww, foundP, -, unsetP, -, -, -⟩ :=
      ((front.snoc step).append post).departure_charge_site c cMember
    rw [cIndex'] at foundP
    obtain ⟨x, foundX, life⟩ := pre'.registryLifecycle.validators v.toNat w0 found0
    obtain rfl : x = vv := Option.some.inj (foundX.symm.trans foundP)
    exact assigned0 (by rw [← life.exitEpoch assigned0]; exact unsetP)
  obtain ⟨c0, c0Member, c0Index, -⟩ :=
    Internal.Run.charge_of_exit front electra aEarly v.toNat unsetSplit old foundA unset
  obtain ⟨p, q, cf, step', post', cut', vv, ww, foundP, foundQ, unsetP, setQ, amount, -⟩ :=
    front.departure_charge_site c0 c0Member
  rw [c0Index] at foundP foundQ
  have inRun : c0 ∈ ((front.snoc step).append post).departureCharges := by
    rw [Run.departureCharges_append]
    simp [Run.departureCharges, c0Member]
  have chargeEq : Internal.chargeAmt ((front.snoc step).append post) v.toNat = c0.amount := by
    unfold Internal.chargeAmt
    rw [Internal.find_charge inRun (by simp [c0Index])
      (fun d inD hd =>
        Internal.charge_unique ((front.snoc step).append post) inD inRun (by simpa [c0Index] using
          hd))]
    rfl
  have amountEq : c0.amount = effectiveAt p v.toNat := by simp [amount, effectiveAt, foundP]
  -- the charge step
  obtain ⟨d, dMember, dIndex, -⟩ :=
    (Run.nil.snoc step').departure_charge_of_assigned v.toNat vv ww foundP foundQ unsetP setQ
  have hcharge : step'.departureCharges.any (·.index == v.toNat) = true :=
    List.any_eq_true.mpr ⟨d, by simpa [Run.departureCharges] using dMember, by simpa using dIndex⟩
  have site : (cf.snoc step').append ((post'.snoc step).append post) =
      (front.snoc step).append post := by
    rw [← cut']
    exact Run.append_assoc _ _ _
  -- the key is not withdrawable at the slashing
  have held : ∀ w, q.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch a.state).toNat < w.withdrawableEpoch.toNat := by
    intro w foundW
    have eqW : w = ww := Option.some.inj (foundW.symm.trans foundQ)
    have lateA : (getCurrentEpoch a.state).toNat < old.withdrawableEpoch.toNat :=
      Internal.newly_slashed_unwithdrawable h.genesis h.caps (shared.append (fromFin.append front))
        step
        bEarly foundA foundB cleanA markedB
    have kept := Internal.kept_run (shared.append (fromFin.append (cf.snoc step'))) h.genesis
      (Nat.le_trans h.fulu (fork_le_of_chainSteps (cf.snoc step').chainSteps)) post' aEarly
    obtain ⟨-, wdEq⟩ := kept.withdrawable v.toNat ww old foundQ foundA setQ
    have same : old.withdrawableEpoch = ww.withdrawableEpoch :=
      wdEq.resolve_left (by simp [cleanA])
    rw [eqW, ← same]
    exact lateA
  obtain ⟨eventsY, replayedY⟩ := front.balanceEvents_ok aEarly highC
  have whole := bound cf step' post' cut' site hcharge aFork (by omega) replayedY held
  -- the credits of `pre` are its proposer, whistleblower and sync credits
  have noneBefore := no_prefix_charge_of_unset pre Run.nil v.toNat unsetSplit
  obtain ⟨propSplit, whistSplit, riseSame⟩ := prefix_append_credits v highC pre front electra
    h.early sameEpoch noneBefore
  rw [riseSame] at whole
  -- the rise of the whole run is at least the rise before the slashing
  obtain ⟨seenC, riseMono, -⟩ := rise_fold v.toNat highC (front.snoc step)
    ((Internal.riseScan_fst _ _ _).mpr ⟨c0, by simp [Run.departureCharges, c0Member], c0Index⟩) post
    h.early endEpochC
  have riseSnoc : (Internal.riseScan v.toNat highC front).2 ≤
      (Internal.riseScan v.toNat highC (front.snoc step)).2 := by
    simp only [Internal.riseScan]
    split_ifs <;> omega
  have rise := Internal.riseQ_eq_of_seen _ _ _ seenC
  -- the credits before the slashing are at most those of the run
  have propLe := Internal.creditScan_prefix_le (fun s => decide (s = .rewards ∨ s =
      .consolidations))
    (fun s => decide (s = .consolidations)) v.toNat highC front step post
  have whistLe := Internal.creditScan_prefix_le (fun s => decide (s = .slashings)) (fun _ => false)
    v.toNat highC front step post
  have parts := (Internal.credit_parts_le ((front.snoc step).append post) highC v replayedC).2
  have syncSplit : Internal.syncCr (eventsP ++ eventsY) v.toNat =
      Internal.syncCr eventsP v.toNat + Internal.syncCr eventsY v.toNat := by
    simp only [Internal.syncCr, List.map_append, List.sum_append]
  have syncLe := Internal.syncCr_prefix_le front step post highC replayedY replayedC v.toNat
  unfold Internal.whistleSlack Internal.whistleSlackBase
  simp only [Internal.propC, Internal.whistC] at whole propSplit whistSplit parts ⊢
  omega

/-- The effective balance at its slashing of a charged key of the split's registry.

The charge of the key is on C's run, in an epoch after the split's.

The charge reads the effective balance immediately before the exit is assigned.

This bound leaves out the credits of the shared prefix. -/
private theorem registry_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (inside : i < split.validators.data.size)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true)
    (charged : (tailC.departureCharges.any fun c => c.index == i) = true)
    {cp cq : ForkedBeaconState preset} (cfront : Run config checks ⟨fork, split⟩ cp)
    (cstep : Step config checks cp cq) (cpost : Run config checks cq ⟨fork, counted⟩)
    (csite : (cfront.snoc cstep).append cpost = tailC)
    (charge : cstep.departureCharges.any (·.index == i) = true)
    (started : (getCurrentEpoch split).toNat < (getCurrentEpoch cp.state).toNat) :
    effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin i := by
  obtain ⟨v, rfl⟩ := Uint64.exists_toNat_eq
    (inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split))
  have core := registry_charge_of h fromFin tail high (Run.nil : Run config checks ⟨fork, split⟩ _)
    rfl tailC highC endEpochC replayedC (eventsP := []) step member v inside flag charged
    (eventsF := eventsF) (events := events) (by
      intro front post p q eventsY cf step' post' cut' site hcharge aFork aEpoch replayedY held
      have sameStart := charge_site_start cf step' _ site cfront cstep cpost csite hcharge charge
      have later : (getCurrentEpoch split).toNat < (getCurrentEpoch p.state).toNat := by
        rw [sameStart]
        exact started
      have := charge_effective_bound h (y := a) aFork front highC aEpoch replayedY cf step' post'
        cut' hcharge later held
      simpa only [Run.nil_append, List.nil_append] using this)
  simp only [Internal.propN, Internal.whistC, Internal.creditScan_nil, Internal.syncCr,
    List.map_nil, List.sum_nil,
    Nat.add_zero] at core
  exact core

/-- The effective balance at its slashing of a charged key whose charge is in the split's epoch.

The epoch's start `t` is on the shared run, before the split.

The key's credits from `t` come through the shared suffix `pre`, and then through C's run.

`pre` holds no consolidation or deposit credit, since it is inside one epoch.

So its credits are the proposer, whistleblower and sync credits.

The bands of hysteresis at `t` come from the slot step that crossed into its epoch.

This bound includes the credits from the start of the split epoch. -/
private theorem registry_charge_split_epoch
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    {t : BeaconState preset fork} (toT : Run config checks g ⟨fork, t⟩)
    (pre : Run config checks ⟨fork, t⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch t)
    (earlier : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      toT.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch t).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {eventsP : List (BalanceEvent preset)} (replayedP : pre.balanceEvents highC = .ok eventsP)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (inside : i < split.validators.data.size)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true)
    (charged : (tailC.departureCharges.any fun c => c.index == i) = true)
    {cp cq : ForkedBeaconState preset} (cfront : Run config checks ⟨fork, split⟩ cp)
    (cstep : Step config checks cp cq) (cpost : Run config checks cq ⟨fork, counted⟩)
    (csite : (cfront.snoc cstep).append cpost = tailC)
    (charge : cstep.departureCharges.any (·.index == i) = true)
    (inSplitEpoch : ¬ (getCurrentEpoch split).toNat < (getCurrentEpoch cp.state).toNat) :
    effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
      (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin i := by
  obtain ⟨v, rfl⟩ := Uint64.exists_toNat_eq
    (inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split))
  refine registry_charge_of h fromFin tail high pre sameEpoch tailC highC endEpochC replayedC step
    member v inside flag charged ?_
  intro front post p q eventsY cf step' post' cut' site hcharge aFork aEpoch replayedY held
  have sameStart := charge_site_start cf step' _ site cfront cstep cpost csite hcharge charge
  have notStarted : ¬ (getCurrentEpoch split).toNat < (getCurrentEpoch p.state).toNat := by
    rw [sameStart]
    exact inSplitEpoch
  have start := split_epoch_start_data h highC toT pre sameEpoch earlier cf step'
    ((post'.snoc step).append post) endEpochC notStarted hcharge
  exact charge_effective_bound_of h toT (y := a) aFork (pre.append front) highC aEpoch
    (DirectSafety.Apriori.Internal.balanceEvents_append pre front highC replayedP replayedY)
    (pre.append cf) step' post'
    (by rw [← cut']; exact (Run.append_assoc pre (cf.snoc step') post').symm) hcharge
    start held

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The registry keys of the split are bounded at each slashing step on C's branch.

Every key is read at `whistleEnv` and the slack.

A key that C's branch charges to depart is also read at its charge.

A charge in the split's own epoch also reads the credits of `pre`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.registry_bounds (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (earlier : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      toB.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch b).toNat)
    {eventsP : List (BalanceEvent preset)} (replayedP : pre.balanceEvents highC = .ok eventsP) :
    (∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i) ∧
    (∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
            (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i) := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  refine ⟨fun {a b} step member i inside unslashed flag => ?_,
    fun {a b} step member i inside unslashed flag charged => ?_⟩
  · by_cases beyond : fin.validators.data.size ≤ i
    · -- A key created after the finalized state.
      by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
      · obtain ⟨v, rfl⟩ := Uint64.exists_toNat_eq
          (inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split))
        obtain ⟨c, toC, fromC, cutC, insideC, -, before, floorStart, -⟩ :=
          Internal.created_first_state h fromFin beyond inside
        exact Internal.registry_frozen h tail high endEpoch replayed fromFin replayedF tailC highC
          endEpochC replayedC step member v.toNat toC fromC cutC insideC before (.inr floorStart)
          unslashed flag
          (fun w found _ => Internal.late_of_exitAfterFin h v.toNat (Internal.created_exitAfterFin h
              beyond)
            w found)
          kept
      · exact Internal.registry_headroom (config := config) h tailC step member i kept _
    · have inFin : i < fin.validators.data.size := Nat.lt_of_not_le beyond
      obtain ⟨w, found⟩ : ∃ w, pulled.validators.data[i]? = some w :=
        ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside grows)⟩
      by_cases exited : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat
      · by_cases slashedR : (pinTerms config pulled anc fin).slashedRB i = true
        · by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
          · refine Internal.registry_frozen h tail high endEpoch replayed fromFin replayedF tailC
                highC
              endEpochC replayedC step member i Run.nil fromFin (Run.nil_append fromFin) inFin
              (Internal.finalized_start h i).1 (.inl (Internal.finalized_start h i).2) unslashed
                  flag
              (fun w' found' unslashedR => ?_) kept
            -- R slashes the key, so it is not unslashed there
            rw [Internal.slashedRB_eq] at slashedR
            have := (of_decide_eq_true slashedR).1
            simp [found'] at this
            rw [this] at unslashedR
            exact absurd unslashedR (by decide)
          · exact Internal.registry_headroom (config := config) h tailC step member i kept _
        · exact Internal.registry_exited h fromFin tail high endEpoch replayedF tailC highC
              endEpochC
            replayedC step member i inside
            (fun w' found' => by
              obtain rfl := Option.some.inj (found.symm.trans found')
              exact exited) flag slashedR
      · -- A finalized key that exits at or after the finalized epoch.
        by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
        · exact Internal.registry_frozen h tail high endEpoch replayed fromFin replayedF tailC highC
            endEpochC replayedC step member i Run.nil fromFin (Run.nil_append fromFin) inFin
            (Internal.finalized_start h i).1 (.inl (Internal.finalized_start h i).2) unslashed flag
            (fun w' found' _ => Internal.late_of_exitAfterFin h i
              (fun w'' found'' => by
                obtain rfl := Option.some.inj (found.symm.trans found'')
                omega) w' found') kept
        · exact Internal.registry_headroom (config := config) h tailC step member i kept _
  · -- the charge of the key on C's run, found from the exit that the step assigns
    obtain ⟨c, chargeMember, chargeIndex⟩ := List.any_eq_true.mp charged
    have indexEq : c.index = i := by simpa using chargeIndex
    obtain ⟨cp, cq, cfront, cstep, cpost, csite, u, w, foundU, foundW, unset, assigned, -, -⟩ :=
      tailC.departure_charge_site c chargeMember
    have charge : cstep.departureCharges.any (·.index == i) = true := by
      rw [← indexEq]
      exact Internal.step_charges_of_exits cstep foundU foundW unset assigned
    by_cases started : (getCurrentEpoch split).toNat < (getCurrentEpoch cp.state).toNat
    · have bound := registry_charge (eventsF := eventsF) (events := events) h fromFin tail high
        tailC highC endEpochC replayedC step member i inside flag charged cfront cstep cpost
        csite charge started
      omega
    · exact registry_charge_split_epoch h fromFin tail high toB pre sameEpoch earlier tailC highC
        endEpochC replayedC replayedP step member i inside flag charged cfront cstep cpost csite
        charge started

/-- A charged key of `K5` whose charge is in the split's epoch.

The epoch's start `b` is on the shared run, before the split.

The key's credits from `b` come through the shared suffix `pre` of the split's epoch.

Then they come through C's run.

The bands of hysteresis at `b` come from the slot step that crossed into its epoch. -/
private theorem K5_charged_split_epoch
    (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (earlier : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      toB.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch b).toNat)
    {eventsF : List (BalanceEvent preset)}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {eventsP : List (BalanceEvent preset)} (replayedP : pre.balanceEvents highC = .ok eventsP)
    {v : ValidatorIndex} (member : v ∈ Internal.K5 counted V)
    {a c : ForkedBeaconState preset} (front : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a c) (post : Run config checks c ⟨fork, counted⟩)
    (site : (front.snoc step).append post = tailC)
    (charged : step.departureCharges.any (·.index == v.toNat) = true)
    (inSplitEpoch : ¬ (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat)
    (hexit : Internal.exitQ tailC v.toNat = effectiveAt a v.toNat) :
    Internal.eC counted v ≤ Internal.exitQ tailC v.toNat + Internal.riseQ tailC highC v.toNat +
      ((Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
        eventsP v.toNat +
          Internal.propC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (Internal.propC tailC highC v.toNat)) +
        Internal.whistC tailC highC v.toNat +
        (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
        Internal.bandR (eventsF ++ events) v.toNat + Internal.bandX fin highC v.toNat) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  subst site
  obtain ⟨-, -, -, -, unset, -⟩ := Internal.charge_exits step charged
  have charges : ∃ c ∈ ((front.snoc step).append post).departureCharges, c.index = v.toNat := by
    obtain ⟨charge, member, index⟩ := List.any_eq_true.mp charged
    exact ⟨charge, by simp [Run.departureCharges_append, Run.departureCharges, member],
      beq_iff_eq.mp index⟩
  have start := split_epoch_start_data h highC toB pre sameEpoch earlier front step post endEpochC
    inSplitEpoch charged
  -- the whole run from `b`: the shared part `pre`, then C's run from the split
  have whole := charge_effective_bound_of h toB (y := ⟨fork, counted⟩) rfl
    (pre.append ((front.snoc step).append post)) highC endEpochC
    (DirectSafety.Apriori.Internal.balanceEvents_append pre _ highC replayedP replayedC)
    (pre.append front) step post (Run.append_assoc pre (front.snoc step) post).symm charged
    start (K5_charged_held h member front step post charged)
  -- the credits of `pre` are its proposer, whistleblower and sync credits
  have noneBefore := no_prefix_charge_of_unset pre front v.toNat unset
  obtain ⟨propSplit, whistSplit, riseSame⟩ := prefix_append_credits v highC pre
    ((front.snoc step).append post) electra h.early sameEpoch noneBefore
  have rise := Internal.riseQ_eq_of_seen _ _ _ ((Internal.riseScan_fst v.toNat highC _).mpr charges)
  have syncLe : Internal.syncCr eventsC v.toNat ≤ Internal.syncF eventsC v.toNat := by
    have := Internal.syncF_eq eventsC v.toNat
    unfold Internal.syncCr
    omega
  have syncSplit : Internal.syncCr (eventsP ++ eventsC) v.toNat =
      Internal.syncCr eventsP v.toNat + Internal.syncCr eventsC v.toNat := by
    simp only [Internal.syncCr, List.map_append, List.sum_append]
  have eCeq : Internal.eC counted v = effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset)
    v.toNat :=
    rfl
  rw [riseSame] at whole
  omega

/-- A key of `K5` whose exit R reads: no charge on C's run.

Its exit is assigned at the split, so its deposits on C's run are postponed.

So only proposer credits count. -/
private theorem K5_uncharged_key (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (member : v ∈ Internal.K5 counted V)
    (uncharged : ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    Internal.eC counted v ≤ Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
      ((Internal.propC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (Internal.propC tailC highC v.toNat)) +
        Internal.whistC tailC highC v.toNat +
        (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
        Internal.bandR (eventsF ++ events) v.toNat + Internal.bandX fin highC v.toNat) := by
  obtain ⟨shared⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨u, foundU, activeBefore, notNow⟩ := Internal.K5_previous_only h member
  have exitU := ((previous_only_iff_exit counted u).mp ⟨activeBefore, notNow⟩).2
  have notFar := getCurrentEpoch_ne_farFuture h.twoSlots counted
  have assignedU : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far =>
    notFar (UInt64.toNat_inj.mp (by rw [← exitU, far]))
  -- every exit is a charge, so the key's exit was assigned before the split
  have insideSplit : v.toNat < split.validators.data.size := by
    by_contra out
    obtain ⟨c, listed, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early v.toNat
      (fun w hw => absurd (Array.getElem?_eq_some_iff.mp hw).1 out) u foundU assignedU
    exact uncharged ⟨c, listed, index⟩
  obtain ⟨v0, found0⟩ : ∃ w, split.validators.data[v.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem insideSplit⟩
  have assigned0 : v0.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    obtain ⟨c, listed, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early v.toNat
      (fun w hw => by
        obtain rfl := Option.some.inj (found0.symm.trans hw)
        exact far) u foundU assignedU
    exact uncharged ⟨c, listed, index⟩
  obtain ⟨x, foundX, life⟩ := tailC.registryLifecycle.validators v.toNat v0 found0
  obtain rfl : x = u := Option.some.inj (foundX.symm.trans foundU)
  have exit0 := congrArg UInt64.toNat (life.exitEpoch assigned0)
  have delayed := (shared.append fromFin).exit_withdrawable_delay h.genesis v.toNat v0 found0
    assigned0
  have held : (getCurrentEpoch counted).toNat < v0.withdrawableEpoch.toNat := by
    have := (Internal.Setting.delay h)
    omega
  have exited := Internal.exitEpoch_toNat_lt_of_ne_far assigned0
  have dep : (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
    tailC) =
      0 := by
    refine Nat.le_zero.mp
      ((Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits)) (· = .deposits)
        (by intro s; simp) tailC highC v replayedC).trans (Nat.le_of_eq ?_))
    exact Internal.Run.exiting_deposit_credit_zero (shared.append fromFin) h.genesis tailC h.fulu
      h.early highC replayedC v.toNat v0 found0 exited held
  have credEq : Internal.credC tailC highC v.toNat = Internal.propC tailC highC v.toNat := by
    have split := Internal.credC_split tailC highC v.toNat
    have splitN := Internal.credN_split tailC highC v.toNat
    have splitP := Internal.propC_split tailC highC v.toNat
    omega
  have core := Internal.key_core h tail high endEpoch replayed fromFin replayedF tailC highC
      endEpochC
    replayedC v.toNat (Nat.lt_of_lt_of_le insideSplit tail.registryLifecycle.size_le)
    (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp member).1)
  unfold Internal.keyCeiling at core
  rw [credEq] at core
  simp only [Internal.eC, Internal.eR]
  omega

/-- The other keys that are previous-epoch-only in C, and their exits.

A key with a departure charge on C's run is at its charge plus its rise after that.

Any other key has its exit assigned before the split, so it is at its balance at R plus its rise.

Both add C's proposer credits and sync seats.

The credit term counts proposer and consolidation credits because deposits are postponed.

The run `pre` is the shared run from the start of the split's epoch.

A charge in that epoch reads the balance before the credits of `pre`.

So the key's proposer, whistleblower and sync credits over `pre` are read too. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cP_le (h : Setting config checks g
  split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (earlier : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      toB.Contains step → (getCurrentEpoch u.state).toNat < (getCurrentEpoch b).toNat)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {eventsP : List (BalanceEvent preset)} (replayedP : pre.balanceEvents highC = .ok eventsP) :
    Internal.cP pulled counted V ≤ ((∑ v ∈ (Internal.K5 counted V) with
        ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (Internal.exitQ tailC v.toNat + Internal.riseQ tailC highC v.toNat)) +
      (∑ v ∈ (Internal.K5 counted V), ((Internal.propN pre highC v.toNat + Internal.whistC pre highC
        v.toNat +
          Internal.syncCr eventsP v.toNat + Internal.propC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (Internal.propC tailC highC v.toNat)) +
        Internal.whistC tailC highC v.toNat +
        (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
        Internal.bandR (eventsF ++ events) v.toNat + Internal.bandX fin highC v.toNat)) : ℕ) := by
  set T : ValidatorIndex → ℕ := fun v => (Internal.propN pre highC v.toNat + Internal.whistC pre
    highC v.toNat +
          Internal.syncCr eventsP v.toNat + Internal.propC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat (Internal.propC tailC highC v.toNat)) +
        Internal.whistC tailC highC v.toNat +
        (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
        Internal.bandR (eventsF ++ events) v.toNat + Internal.bandX fin highC v.toNat with hT
  -- a charged key: its charge, the start of its epoch, and its exact rise after the charge
  have charged : ∀ v ∈ Internal.K5 counted V, (∃ c ∈ tailC.departureCharges, c.index = v.toNat) →
      Internal.eC counted v ≤ Internal.exitQ tailC v.toNat + Internal.riseQ tailC highC v.toNat + T
        v := by
    intro v member ch
    obtain ⟨a, c, front, step, post, site, hcharge, unset, hin, hexit⟩ :=
      K5_charge_site h tailC member ch
    subst site
    by_cases started : (getCurrentEpoch split).toNat < (getCurrentEpoch a.state).toNat
    swap
    · exact K5_charged_split_epoch h tail fromFin toB pre sameEpoch earlier _ highC endEpochC
        replayedC replayedP member front step post rfl hcharge started hexit
    have bound := charge_effective_bound h (y := ⟨fork, counted⟩) rfl _ highC endEpochC replayedC
      front step post rfl hcharge started (K5_charged_held h member front step post hcharge)
    have rise := Internal.riseQ_eq_of_seen _ _ _ ((Internal.riseScan_fst v.toNat highC _).mpr ch)
    have sync := Internal.syncF_eq eventsC v.toNat
    unfold Internal.syncCr at bound
    have slack : Internal.propC ((front.snoc step).append post) highC v.toNat +
        Internal.whistC ((front.snoc step).append post) highC v.toNat + Internal.syncF eventsC
          v.toNat ≤ T v := by
      simp only [hT]
      omega
    have eCeq : Internal.eC counted v = effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset)
      v.toNat :=
      rfl
    omega
  have eq : Internal.cP pulled counted V = ∑ v ∈ Internal.K5 counted V, (Internal.eC counted v : ℤ)
    := by
    unfold Internal.cP
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Internal.K5]
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Internal.U, Internal.AC, Internal.AR, Internal.Q, Finset.mem_union]
    tauto
  rw [eq, ← Nat.cast_sum]
  refine Nat.cast_le.mpr ?_
  show _ ≤ _ + _ + ∑ v ∈ Internal.K5 counted V, T v
  have splitE := Finset.sum_filter_add_sum_filter_not (Internal.K5 counted V)
    (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) (Internal.eC counted)
  have splitT := Finset.sum_filter_add_sum_filter_not (Internal.K5 counted V)
    (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) T
  have onCharged : ∑ v ∈ (Internal.K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index =
    v.toNat,
      Internal.eC counted v ≤ ∑ v ∈ (Internal.K5 counted V) with ∃ c ∈ tailC.departureCharges,
        c.index = v.toNat,
        (Internal.exitQ tailC v.toNat + Internal.riseQ tailC highC v.toNat) +
      ∑ v ∈ (Internal.K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat, T v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v hv => charged v (Finset.mem_filter.mp hv).1
      (Finset.mem_filter.mp hv).2
  have onUncharged : ∑ v ∈ (Internal.K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges,
        c.index = v.toNat, Internal.eC counted v ≤ ∑ v ∈ (Internal.K5 counted V) with ¬ ∃ c ∈
          tailC.departureCharges,
        c.index = v.toNat, (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) +
      ∑ v ∈ (Internal.K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat, T v :=
        by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun v hv => ?_
    obtain ⟨member, none⟩ := Finset.mem_filter.mp hv
    have key := K5_uncharged_key h tail high endEpoch replayed fromFin replayedF tailC highC
      endEpochC replayedC member none
    simp only [hT]
    omega
  omega

/-- The cap takes over exactly when the weighted gain bound exceeds it. -/
private theorem gainHigh_eq_true_iff : (pinTerms config pulled anc fin).gainHigh = true ↔
    ¬ 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
  change (!decide (11 * (pinTerms config pulled anc fin).depth *
    ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)) = true ↔ _
  simp

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of `K6` beyond R's registry rises by its credits and their gains, when the rate is low.

The key is not in R's registry, so its flow gain is charged when the largest rate is low.

The depth of the window is below an eleventh of an increment against the rate.

The low rate bounds how much the credits can compound. -/
private theorem beyond_key (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (low : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    {v : ValidatorIndex} (member : v ∈ Internal.K6 pulled counted)
    (created : pulled.validators.data.size ≤ v.toNat) :
    balanceAt counted v.toNat ≤
      (((Internal.credC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
          Internal.whistC tailC highC v.toNat) +
        (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
        (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
          Internal.bandR (eventsF ++ events) v.toNat)) + Internal.bandX fin highC v.toNat := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  have activated := Internal.activated_of_activeVoters h.early (Finset.mem_filter.mp member).1
  have absent := Nat.le_trans grows created
  -- the key is beyond R's registry, so its flow gain is charged while the rate is low
  have notPosition : v.toNat ∉ (pinTerms config pulled anc fin).positions := by
    show v.toNat ∉ Finset.range pulled.validators.data.size
    rw [Finset.mem_range]
    omega
  have lowGain : (pinTerms config pulled anc fin).gainHigh = false :=
    Bool.eq_false_iff.mpr fun high => gainHigh_eq_true_iff.mp high low
  exact Internal.created_key_ceiling h tail fromFin tailC highC endEpochC replayedC activated absent
    (Internal.key_of_lowGain h lowGain) (Or.inr ⟨notPosition, lowGain⟩)
    (Internal.created_band h fromFin high endEpoch replayedF tailC highC endEpochC replayedC
        activated
      absent)

/-- The units of the active keys of `CS` are held by the units of the keys of `CS`.

Off the high gain rate each active key of `CS` charges one `unitGain` for its stake at the slashing.

Each of them was created by a deposit of C's run, so its flows are positive and its unit is one.

The reserve already counts a rounding unit for the deposit that creates the key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_csUnits (h : Setting config
  checks g split fin pulled anc counted V)
    {events eventsF : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    (if (pinTerms config pulled anc fin).gainHigh = true then 0 else
      ((Internal.CS counted split).filter fun v =>
        isActiveAt counted (getCurrentEpoch counted) v.toNat = true).card *
          (pinTerms config pulled anc fin).unitGain) ≤
      ∑ v ∈ Internal.CS counted split,
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
          := by
  split_ifs
  · exact Nat.zero_le _
  obtain ⟨_, replayedF⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  rw [Internal.sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC
      v.toNat,
    Nat.mul_comm]
  refine Nat.mul_le_mul_left _ (Finset.card_le_card fun v member => ?_)
  obtain ⟨inCS, active⟩ := Finset.mem_filter.mp member
  refine Finset.mem_filter.mpr ⟨inCS, ?_⟩
  obtain ⟨-, absent, -⟩ := Finset.mem_filter.mp inCS
  obtain ⟨w, found, live⟩ := isActiveAt_eq_true_iff.mp active
  have deposit := Internal.created_deposit h fromFin replayedF tailC highC endEpochC replayedC
    ⟨w, found, Consensus.Internal.assigned_of_active live, activationLe_of_active live⟩ absent
  have cSplit := Internal.credC_split tailC highC v.toNat
  have nSplit := Internal.credN_split tailC highC v.toNat
  unfold Internal.flowCredit
  omega

/-- The keys of `K6` beyond R's registry and the active keys of `CS` fit the deposit slots.

Each is created after the split and activated by C, so a deposit of C's run credits it.

The two sets are apart, since the keys of `K6` are unslashed at C and those of `CS` are slashed.

The deposits of C's run credit at most one epoch's slots in each epoch since the split. -/
private theorem created_slots_le (h : Setting config checks g split fin pulled anc counted V) :
    ((Internal.K6 pulled counted).filter fun v => pulled.validators.data.size ≤ v.toNat).card +
      ((Internal.CS counted split).filter fun v =>
        isActiveAt counted (getCurrentEpoch counted) v.toNat = true).card ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨tailC⟩ := h.toCounted
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  obtain ⟨eventsF, replayedF⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  obtain ⟨eventsC, replayedC⟩ := tailC.balanceEvents_ok h.early (getCurrentEpoch counted).toNat
  have deposit : ∀ v : ValidatorIndex, (∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted) →
      split.validators.data.size ≤ v.toNat →
        0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat
          (getCurrentEpoch counted).toNat tailC) := fun v activated absent =>
    Internal.created_deposit h fromFin replayedF tailC (getCurrentEpoch counted).toNat (Nat.le_succ
        _)
      replayedC activated absent
  have apart := (Internal.cs_disjoint h).1
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun v inK6 inCS =>
    Finset.disjoint_left.mp apart (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mp inK6).1)) (Finset.mem_filter.mp inCS).1)]
  have image : ((((Internal.K6 pulled counted).filter fun v => pulled.validators.data.size ≤
    v.toNat) ∪
      ((Internal.CS counted split).filter fun v =>
        isActiveAt counted (getCurrentEpoch counted) v.toNat = true)).image
          fun v : ValidatorIndex => v.toNat).card = (((Internal.K6 pulled counted).filter fun v =>
            pulled.validators.data.size ≤ v.toNat) ∪ ((Internal.CS counted split).filter fun v =>
              isActiveAt counted (getCurrentEpoch counted) v.toNat = true)).card :=
    Finset.card_image_of_injOn fun a _ b _ same => UInt64.toNat_inj.mp same
  rw [← image]
  refine Internal.deposit_scan_card_le h tailC (getCurrentEpoch counted).toNat _ fun i hi => ?_
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  rcases Finset.mem_union.mp hv with inK6 | inCS
  · obtain ⟨member, beyond⟩ := Finset.mem_filter.mp inK6
    exact deposit v (Internal.activated_of_activeVoters h.early (Finset.mem_filter.mp member).1)
      (Nat.le_trans grows beyond)
  · obtain ⟨member, active⟩ := Finset.mem_filter.mp inCS
    obtain ⟨w, found, isActive⟩ := isActiveAt_eq_true_iff.mp active
    exact deposit v
      ⟨w, found, Consensus.Internal.assigned_of_active isActive, activationLe_of_active isActive⟩
      (Finset.mem_filter.mp member).2.1

/-- The keys of `CS` that are active at C fit the deposit slots that the keys beyond R leave.

At a high gain rate each deposit slot is charged at the largest cap.

The keys of `K6` outside R's registry share that budget without counting any slot twice.

Each key created after R's registry came through a pending deposit of the window. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_capSlots (h : Setting config
  checks g split fin pulled anc counted V) :
    Internal.capUse config pulled anc fin counted +
      (if (pinTerms config pulled anc fin).gainHigh = true then
        ((Internal.CS counted split).filter fun v =>
          isActiveAt counted (getCurrentEpoch counted) v.toNat = true).card *
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat else 0) ≤
      (pinTerms config pulled anc fin).creditCap := by
  classical
  by_cases high : (pinTerms config pulled anc fin).gainHigh = true
  · have cap : (pinTerms config pulled anc fin).creditCap =
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
      have low := gainHigh_eq_true_iff.mp high
      show (if 11 * (pinTerms config pulled anc fin).depth *
          ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat then 0 else
              (pinTerms config pulled anc fin).depthFin *
                preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
                  preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) = _
      rw [ite_eq_right_of_eq_false _ _ (eq_false low)]
      rfl
    unfold Internal.capUse
    rw [ite_eq_left high, ite_eq_left high, cap, ← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by
      rw [Nat.mul_comm _ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat]
      exact (created_slots_le h).trans (Nat.le_of_eq (Nat.mul_comm _ _)))
  · unfold Internal.capUse
    rw [ite_eq_right high, ite_eq_right high]
    exact Nat.zero_le _

/-- A key beyond the split's registry that C slashes has a positive deposit scan on C's run.

Its exit is assigned on C's run, so the run holds its departure charge.

The charge's step activates the key, and the activation is at most C's epoch.

A key created on C's branch and active at C has a deposit on that branch. -/
private theorem whist_created (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC) :=
        by
  classical
  intro i member
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨inSlashed, outside⟩ := Finset.mem_filter.mp member
  simp only [Internal.slashedOnC, Finset.mem_filter, Finset.mem_range] at inSlashed
  obtain ⟨insideC, -, flagC⟩ := inSlashed
  have foundC : counted.validators.data[i]? = some counted.validators.data[i] :=
    Array.getElem?_eq_some_iff.mpr ⟨insideC, rfl⟩
  have slashedW : counted.validators.data[i].slashed = true := by simpa [foundC] using flagC
  have exitAssigned := run_slashed_exit_assigned ((toFin.append fromFin).append tailC) h.genesis
    h.caps.activation h.caps.compounding h.early (Internal.Setting.delay h) i _ foundC slashedW
  have unset : ∀ v, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[i]? =
      some v → v.exitEpoch = FAR_FUTURE_EPOCH := fun v found => by
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt outside)] at found
    cases found
  obtain ⟨c, cMember, cIndex, -⟩ := Internal.Run.charge_of_exit tailC electra h.early i unset _
    foundC exitAssigned
  obtain ⟨a, b, pre, step, post, -, vv, ww, found, foundB, -, set, activated, -, -⟩ :=
    Internal.charge_activated (x := ⟨fork, split⟩) electra tailC c (tailC.departure_charge_site c
      cMember)
  rw [cIndex] at found foundB
  obtain ⟨wc, foundWc, lifeB⟩ := post.registryLifecycle.validators i ww foundB
  have sameWc : wc = counted.validators.data[i] :=
    Option.some.inj (foundWc.symm.trans foundC)
  have finite : (getCurrentEpoch a.state).toNat < FAR_FUTURE_EPOCH.toNat := by
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have two := h.twoSlots
    have slotLt := a.state.slot.toNat_lt
    rw [getCurrentEpoch_toNat, farNat]
    calc a.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ a.state.slot.toNat / 2 :=
          Nat.div_le_div_left two (by norm_num)
      _ < 2 ^ 64 - 1 := by omega
  have notFar : vv.activationEpoch ≠ FAR_FUTURE_EPOCH := fun same =>
    absurd (UInt64.le_iff_toNat_le.mp (same ▸ activated)) (Nat.not_le.mpr finite)
  obtain ⟨u, foundU, keptStep⟩ := (RegistryLifecycle.chainStep step.chainStep).validators i vv
    found
  have sameU : u = ww := Option.some.inj (foundU.symm.trans foundB)
  have actEq : counted.validators.data[i].activationEpoch = vv.activationEpoch := by
    rw [← sameWc, lifeB.activationEpoch (by rw [← sameU, keptStep.activationEpoch notFar]; exact
      notFar), ← sameU, keptStep.activationEpoch notFar]
  have epochLe : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch counted).toNat :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.single step.chainStep)))
      (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps))
  have within := BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted
  have same : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans insideC within)
  have replayedF' := Internal.replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called
      h)
    replayedF
  have actLe : counted.validators.data[i].activationEpoch ≤ getCurrentEpoch counted := by
    rw [actEq]
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_trans (UInt64.le_iff_toNat_le.mp activated) epochLe)
  have := Internal.created_deposit h fromFin replayedF' tailC highC endEpochC replayedC
    (v := UInt64.ofNat i)
    ⟨counted.validators.data[i], by rw [same]; exact foundC, by rw [actEq]; exact notFar, actLe⟩
    (by rw [same]; exact Nat.le_of_not_lt outside)
  rwa [same] at this

/-- The seat bands of the registry keys that C slashes fit the seat term of the base.

A key with a band holds a seat on the run from the finalized state to R.

An exited key's shared credit is a gross credit of that run, and the key is no proposer on it.

The seats of one run are the committees of the periods from the finalized state's to R's. -/
private theorem whist_seat (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (T : Finset ℕ) :
    ∑ i ∈ T, (Internal.bandR (eventsF ++ events) i +
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) ≤
      2 * (((pinTerms config pulled anc fin).depthFin /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
        preset.SYNC_COMMITTEE_SIZE.toNat *
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand)) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  generalize hP : max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat = P
  have periods : (getCurrentEpoch pulled).toNat / P =
      (getCurrentEpoch fin).toNat / P +
        ((getCurrentEpoch pulled).toNat / P - (getCurrentEpoch fin).toNat / P) := by
    have := Nat.div_le_div_right (c := P) (Nat.le_trans finSplit called)
    omega
  have replayedR : (fromFin.append tail).balanceEvents high = .ok (eventsF ++ events) :=
    DirectSafety.Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  obtain ⟨Ls, B, S, D, -, cardS, -, hBS, -, -, hProposer, hDebit, -⟩ :=
    Internal.credited_pieces_seated h.genesis h.parameters.lookahead (y := ⟨fork, pulled⟩) h.early
      (Internal.Setting.delay h) high ((getCurrentEpoch pulled).toNat /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      toFin (fromFin.append tail) h.fulu (by rw [hP]; exact periods)
  rw [hP] at cardS
  -- the keys with a band hold a seat of the run
  obtain ⟨term, hterm⟩ : ∃ term : ℕ → ℕ, ∀ i, term i = Internal.bandR (eventsF ++ events) i +
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0 := ⟨_, fun _ => rfl⟩
  have seated : ∀ i, term i ≠ 0 → i ∈ S := by
    intro i nonzero
    rw [hterm] at nonzero
    by_cases debit : 0 < ((eventsF ++ events).map (Internal.syncDebit i)).sum
    · exact (hDebit _ replayedR i debit).1
    · simp only [Internal.bandR_eq, debit, ↓reduceIte, Nat.zero_add] at nonzero
      by_cases exited : (pinTerms config pulled anc fin).exitBeforeFin i = true
      · simp only [exited, ↓reduceIte] at nonzero
        have credit : 0 < Internal.syncCr eventsF i := by
          by_contra none
          simp [none] at nonzero
        have gross := Internal.syncCr_gross_shared h fromFin tail high replayedF i credit
        rcases hBS i gross with proposer | seat
        · exfalso
          obtain ⟨u, run, p, early, found, same⟩ := hProposer i proposer
          obtain ⟨w, foundW, exit⟩ : ∃ w, pulled.validators.data[i]? = some w ∧
              w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat := by
            have flag : ((pulled.validators.data[i]?).any fun v =>
                decide (v.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = true := exited
            cases found : pulled.validators.data[i]? with
            | none => simp [found] at flag
            | some w =>
              rw [found] at flag
              exact ⟨w, rfl, of_decide_eq_true (by simpa using flag)⟩
          exact Internal.exited_not_proposer h foundW exit u run p early found same
        · exact seat
      · simp only [exited] at nonzero
        exact absurd rfl nonzero
  have perKey : ∀ i, term i ≤ 2 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      preset.downwardBand) := by
    intro i
    have up := h.facts.upward
    rw [hterm, Internal.bandR_eq]
    split_ifs <;> omega
  have cover : ∑ i ∈ T, term i ≤
      (T.filter fun i => term i ≠ 0).card * (2 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        preset.downwardBand)) := by
    rw [← Finset.sum_filter_ne_zero]
    exact (Finset.sum_le_card_nsmul _ _ _ fun i _ => perKey i).trans (by rw [smul_eq_mul])
  have count : (T.filter fun i => term i ≠ 0).card ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
      ((pinTerms config pulled anc fin).depthFin / P + 2) := by
    refine (Finset.card_le_card fun i member => seated i (Finset.mem_filter.mp member).2).trans
      (cardS.trans (Nat.mul_le_mul_left _ ?_))
    have := Nat.add_div_le_div_add_div_add_one
      ((getCurrentEpoch pulled).toNat - (getCurrentEpoch fin).toNat) (getCurrentEpoch fin).toNat P
    have back : (getCurrentEpoch pulled).toNat - (getCurrentEpoch fin).toNat +
        (getCurrentEpoch fin).toNat = (getCurrentEpoch pulled).toNat := by omega
    rw [back] at this
    have wide := Nat.div_le_div_right (c := P)
      (show (getCurrentEpoch pulled).toNat - (getCurrentEpoch fin).toNat ≤
        (pinTerms config pulled anc fin).depthFin from by
          show _ ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat
          omega)
    omega
  rw [show ∑ i ∈ T, (Internal.bandR (eventsF ++ events) i +
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) = ∑ i ∈ T, term i
          from
    Finset.sum_congr rfl fun i _ => (hterm i).symm]
  calc ∑ i ∈ T, term i ≤ _ := cover
    _ ≤ 2 * (((pinTerms config pulled anc fin).depthFin / P + 2) *
        preset.SYNC_COMMITTEE_SIZE.toNat *
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand)) := by
      have := Nat.mul_le_mul_right (2 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        preset.downwardBand)) count
      calc _ ≤ _ := this
        _ = _ := by ring

/-- The reward budget covers rounding units and induced leak for keys newly slashed on C's branch.

It counts these keys of the split's registry at weight one.

A key that R slashes holds a second unit, counted against the number of slashings on R. -/
private theorem whist_units (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (T : Finset ℕ)
    (sub : T ⊆ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size))
        :
    ∑ i ∈ T, (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0)) ≤
      (pinTerms config pulled anc fin).creditUnits + (pinTerms config pulled anc fin).syncLeak +
        (pinTerms config pulled anc fin).unitGain *
          ((pinTerms config pulled anc fin).consolidationsXCount +
            2 * (pinTerms config pulled anc fin).slashedR) +
        (pinTerms config pulled anc fin).slashedR *
          (pinTerms config pulled anc fin).slashLeak := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have units := (Internal.bud_units h tail high replayed fromFin replayedF tailC highC endEpochC
    replayedC).2
  have leak := (Internal.bud_syncLeak h tail high endEpoch replayed fromFin replayedF).2
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  have within := BeaconState.validators_size_lt_of_lt_glamsterdam h.early pulled
  have insideT : ∀ i ∈ T, i < split.validators.data.size := fun i member =>
    (Finset.mem_filter.mp (sub member)).2
  have small : ∀ i ∈ T, i < 2 ^ 64 := fun i member =>
    Nat.lt_trans (Nat.lt_of_lt_of_le (insideT i member) grows) within
  have inSC : T.image UInt64.ofNat ⊆ Internal.SC pulled counted split := by
    intro v member
    obtain ⟨i, mem, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨slashedOn, inside⟩ := Finset.mem_filter.mp (sub mem)
    simp only [Internal.slashedOnC, Finset.mem_filter, Finset.mem_range] at slashedOn
    obtain ⟨insideC, cleanSplit, slashedC⟩ := slashedOn
    simp only [Internal.SC, Finset.mem_filter, Finset.mem_image, Finset.mem_range,
      UInt64.toNat_ofNat_of_lt' (small i mem)]
    refine ⟨⟨i, Nat.lt_of_lt_of_le inside grows, rfl⟩, ?_, ?_⟩
    · have found : counted.validators.data[i]? = some counted.validators.data[i] :=
        Array.getElem?_eq_some_iff.mpr ⟨insideC, rfl⟩
      rw [found] at slashedC
      simp only [slashedFlagAt, found]
      simpa using slashedC
    · have found : split.validators.data[i]? = some split.validators.data[i] :=
        Array.getElem?_eq_some_iff.mpr ⟨inside, rfl⟩
      rw [found] at cleanSplit
      simp only [slashedFlagAt, found]
      simpa using cleanSplit
  have conv := Internal.sum_image_ofNat T small
  have sumSC : ∀ f : ℕ → ℕ, ∑ i ∈ T, f i ≤ ∑ v ∈ Internal.SC pulled counted split, f v.toNat := fun
    f => by
    rw [← conv f]
    exact Finset.sum_le_sum_of_subset inSC
  -- the second unit of the keys that R slashes
  have second : ∑ i ∈ T, (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
      (pinTerms config pulled anc fin).unitGain else 0) ≤
      (pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR := by
    rw [← conv (fun i => if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
      (pinTerms config pulled anc fin).unitGain else 0)]
    have pointwise : ∀ v ∈ T.image UInt64.ofNat,
        (if 0 < Internal.slashW (pinTerms config pulled anc fin) v.toNat then
          (pinTerms config pulled anc fin).unitGain else 0) ≤
        if (pinTerms config pulled anc fin).slashedRB v.toNat = true then
          (pinTerms config pulled anc fin).unitGain else 0 := fun v _ => by
      by_cases pos : 0 < Internal.slashW (pinTerms config pulled anc fin) v.toNat
      · have flag : (pinTerms config pulled anc fin).slashedRB v.toNat = true := by
          by_contra no
          simp [Internal.slashW, no] at pos
        simp [pos, flag]
      · simp [pos]
    refine (Finset.sum_le_sum pointwise).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (Internal.slashedRB_card_le config pulled anc fin _)
  simp only [Finset.sum_add_distrib]
  have u := sumSC (fun i => Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC
    events
    eventsF i)
  have l := sumSC (fun i => Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail)
    i)
  have expand : (pinTerms config pulled anc fin).unitGain *
      ((pinTerms config pulled anc fin).consolidationsXCount +
        2 * (pinTerms config pulled anc fin).slashedR) =
      (pinTerms config pulled anc fin).unitGain *
        ((pinTerms config pulled anc fin).consolidationsXCount +
          (pinTerms config pulled anc fin).slashedR) +
      (pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR := by
    ring
  omega

/-- The slack of the keys and the extra terms fit twice the credit, band and unit totals. -/
private theorem whist_slack_arith (S Yp Y X0 Wc u SB SU slotsInc B F cu sl e1 e2 : ℕ)
    (hs : S ≤ 2 * ((11 * Yp + 9) / 10) + 2 * Wc + u + SB + SU) (hY : Yp + X0 ≤ Y)
    (hu : u ≤ 2 * slotsInc) (hB : slotsInc ≤ B) (hSB : SB ≤ 2 * F) (hSU : SU ≤ cu + sl + e1 + e2) :
    S + X0 ≤ 2 * ((11 * Y + 9) / 10) + 2 * (B + F + cu + sl + e1 + e2) + 2 * Wc := by
  have rise : (11 * Yp + 9) / 10 + X0 ≤ (11 * Y + 9) / 10 := by omega
  omega

/-- The reserve's whistleblower budget bounds the credits to any set of keys on C's branch.

The base reads each key of R's registry at twice its bound.

It reads each deposited or created key at the largest cap.

The reserve includes both the balance at the slashing and the slack in that bound. -/
private theorem flow_whist (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {eventsP : List (BalanceEvent preset)}
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    (registryCharge : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
            (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i) :
    ∃ WB : ℕ, (pinTerms config pulled anc fin).otherGain =
        (3 * (WB + (((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
            preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
              PinTerms.syncEnvelope preset
                ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
            (pinTerms config pulled anc fin).depth *
              (pinTerms config pulled anc fin).syncProposer))) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).perIncrement *
            (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ∧
      ∀ keys : Finset ValidatorIndex, ∑ v ∈ keys, Internal.whistC tailC highC v.toNat ≤ WB := by
  classical
  have count := Internal.whist_count h tailC highC endEpochC replayedC
    (whist_created h fromFin high endEpoch replayedF tailC highC endEpochC replayedC)
  set t := pinTerms config pulled anc fin with ht
  have hdf : t.depthFin = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := rfl
  have inc_pos := h.bands.1
  set inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat with hinc
  set M := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat with hM
  set MPD := preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat with hMPD
  set SCS := preset.SYNC_COMMITTEE_SIZE.toNat with hSCS
  set slots := preset.SLOTS_PER_EPOCH.toNat with hslots
  set P := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat with hP
  set env := PinTerms.syncEnvelope preset
    ((getTotalActiveBalance pulled).toOption.getD 0).toNat
    with henv
  set W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hW
  set Sx := ∑ i ∈ t.positions, max (max (t.ebUp i) (balanceAt pulled i + t.rise i)) (t.bF i)
    with hSx
  set Y := t.depthFin * MPD * M + t.consolidationsX + t.depth * t.proposerCredit +
    t.depthFin * t.syncProposer + t.depth * slots * SCS * env + t.depthFin * slots * SCS * env
    with hY
  set F := (t.depthFin / P + 2) * SCS * (inc + preset.downwardBand) with hF
  set e1 := t.unitGain * (t.consolidationsXCount + 2 * t.slashedR) with he1
  set e2 := t.slashedR * t.slashLeak with he2
  set slots' := t.depth * slots + (t.depth / P + 2) * SCS + t.depth * MPD with hslots'
  obtain ⟨L, hX⟩ : ∃ L : ℕ, t.otherGain = (3 * (2 * (Sx + (11 * Y + 9) / 10 +
        (slots' + L) * inc + F + t.creditUnits + t.syncLeak + e1 + e2) / (W - 2) +
      (t.depth + ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) * slots * SCS *
        env + t.depth * t.syncProposer)) / inc * t.perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat :=
    ⟨_, rfl⟩
  refine ⟨2 * (Sx + (11 * Y + 9) / 10 + (slots' + L) * inc + F + t.creditUnits + t.syncLeak + e1 +
    e2) / (W - 2), ?_, fun keys => ?_⟩
  · rw [hX, Nat.add_assoc _ ((t.depth + _) * _ * _ * _)]
  -- the slack of the registry keys that C slashes and no deposit credits
  set T1 := (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size)
      with hT1
  have subT : T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i) ⊆
      (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size) := by
    rw [← hT1]
    exact Finset.filter_subset _ _
  have slackT := Internal.slack_le h fromFin tail high endEpoch replayed replayedF highLeR tailC
      highC
    endEpochC replayedC highLe (T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i))
    (fun i member => by
      have inT1 := (Finset.mem_filter.mp member).1
      rw [hT1] at inT1
      exact (Finset.mem_filter.mp inT1).2)
    (fun i member => Nat.eq_zero_of_not_pos (Finset.mem_filter.mp member).2) _ _
    (whist_seat h fromFin tail high replayed replayedF _)
    (whist_units h fromFin tail high endEpoch replayed replayedF tailC highC endEpochC replayedC _
      subT)
  have ub : preset.upwardBand * slots' ≤ 2 * (slots' * inc) := by
    have up := h.facts.upward
    have quarter := h.facts.quarterBand
    have le : preset.upwardBand ≤ 2 * inc := by omega
    calc preset.upwardBand * slots' ≤ 2 * inc * slots' := Nat.mul_le_mul_right _ le
      _ = 2 * (slots' * inc) := by ring
  have hB : slots' * inc ≤ (slots' + L) * inc := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hM' : t.depthFin * MPD * M = M * (t.depthFin * MPD) := by ring
  have hYY : (t.consolidationsX + t.depth * t.proposerCredit + t.depth * slots * SCS * env +
      t.depthFin * slots * SCS * env + t.depthFin * t.syncProposer) +
        M * (t.depthFin * MPD) ≤ Y := by
    rw [hY, hM']
    omega
  have slack := whist_slack_arith _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ slackT hYY ub hB le_rfl le_rfl
  exact (Internal.flow_whist_of h fromFin tail high tailC highC endEpochC replayedC pre registry
    registryCharge Sx Y ((slots' + L) * inc + F + t.creditUnits + t.syncLeak + e1 + e2) hSx count
    slack keys).trans
    (le_of_eq (by congr 2; omega))

/-- The low-rate credit budget covers the weighted gains from the counted keys' flows.

They also take the surplus of the slash charge over R's slashed keys.

They take a tenth of the keys' credits too.

The bound is scaled by ten, so the tenth is exact.

One floor of all of a key's flows bounds its gain, and each split by kind costs one step.

`registry` and `registryCharge` are the bounds of the registry keys at their slashing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_split_of (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {eventsP : List (BalanceEvent preset)}
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    (registryCharge : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
            (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    :
    10 * ((∑ v ∈ (Internal.K4 pulled counted V),
        Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)
          +
      3 * (∑ v ∈ (Internal.K5 counted V),
          Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
            (Internal.propC tailC highC v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted),
          Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat)) ≤
      10 * ((pinTerms config pulled anc fin).creditLow +
        3 * ((pinTerms config pulled anc fin).slashedR *
          (2 * (pinTerms config pulled anc fin).depthFin *
            (pinTerms config pulled anc fin).flagRate))) +
        (((∑ v ∈ (Internal.K4 pulled counted V), Internal.credN tailC highC v.toNat) +
          (∑ v ∈ (Internal.K6 pulled counted), Internal.credN tailC highC v.toNat) +
          (∑ v ∈ (Internal.K5 counted V), Internal.propN tailC highC v.toNat)) +
          2 * (∑ v ∈ (Internal.K5 counted V), Internal.propN tailC highC v.toNat)) := by
  classical
  have incPos := h.bands.1
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  -- The consolidations are read at the pulled epoch, where `bud_consolidations_base` holds.
  have whole : (∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
    have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    obtain ⟨onF, onR⟩ := Internal.replays_at_pulled tail high endEpoch replayed fromFin replayedF
    have onC := (DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tailC
      (high := highC) (localHigh := (getCurrentEpoch pulled).toNat) endEpochC
      (by simp only; omega)).symm.trans replayedC
    exact (Internal.bud_consolidations_base h fromFin tail _ (by omega) onR onF le_rfl tailC _ (by
      omega)
      onC le_rfl).2
  set t := pinTerms config pulled anc fin with ht
  obtain ⟨B, hOther, hB⟩ : ∃ B : ℕ,
      t.otherGain = (3 * B) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ∧
      ∀ keys : Finset ValidatorIndex, ∑ v ∈ keys, (Internal.whistC tailC highC v.toNat +
        (Internal.syncCr eventsC v.toNat + Internal.syncD events v.toNat + Internal.syncD eventsF
          v.toNat)) ≤ B := by
    obtain ⟨WB, hOther, hWhist⟩ := flow_whist h tail high endEpoch replayed fromFin replayedF tailC
      highC endEpochC replayedC highLeR highLe pre registry registryCharge
    refine ⟨WB + _, hOther, fun keys => ?_⟩
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add (hWhist keys)
      ((voters_sum_le (fun i => Internal.syncCr eventsC i + Internal.syncD events i + Internal.syncD
        eventsF i)
        fun v member => Finset.mem_image_of_mem _ member).trans
        (Internal.flow_sync h tail high replayed fromFin replayedF tailC highC replayedC _))
  -- The credits of each class split by kind: the credit part, the consolidations, the rest.
  have split4 : ∀ (S : Finset ValidatorIndex) (r cr : ℕ → ℕ),
      (∀ v ∈ S, Internal.flowCredit t tailC highC eventsC events eventsF v.toNat (cr v.toNat) ≤
        r v.toNat + Internal.consAmt eventsC v.toNat +
          (Internal.whistC tailC highC v.toNat + (Internal.syncCr eventsC v.toNat + Internal.syncD
            events v.toNat +
            Internal.syncD eventsF v.toNat)) + Internal.slashW t v.toNat) →
      ∑ v ∈ S, Internal.flowCredit t tailC highC eventsC events eventsF v.toNat (cr v.toNat) ≤
        ∑ v ∈ S, r v.toNat + ∑ v ∈ S, Internal.consAmt eventsC v.toNat +
          ∑ v ∈ S, (Internal.whistC tailC highC v.toNat + (Internal.syncCr eventsC v.toNat +
            Internal.syncD events v.toNat +
            Internal.syncD eventsF v.toNat)) + ∑ v ∈ S, Internal.slashW t v.toNat := by
    intro S r cr each
    refine (Finset.sum_le_sum each).trans (le_of_eq ?_)
    simp only [Finset.sum_add_distrib]
  have z4 := split4 (Internal.K4 pulled counted V) (fun i => Internal.credN tailC highC i)
      (fun i => Internal.credC tailC highC i) fun v _ => by
    have := (Internal.credit_parts_le tailC highC v replayedC).1
    unfold Internal.flowCredit
    omega
  have z5 := split4 (Internal.K5 counted V) (fun i => Internal.propN tailC highC i)
      (fun i => Internal.propC tailC highC i) fun v _ => by
    have := (Internal.credit_parts_le tailC highC v replayedC).2
    unfold Internal.flowCredit
    omega
  have z6 := split4 (Internal.K6 pulled counted) (fun i => Internal.credN tailC highC i)
      (fun i => Internal.credC tailC highC i) fun v _ => by
    have := (Internal.credit_parts_le tailC highC v replayedC).1
    unfold Internal.flowCredit
    omega
  -- The other flows and the slashed keys fit their bases, once over the three classes.
  have others : ∑ v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted,
      (Internal.whistC tailC highC v.toNat + (Internal.syncCr eventsC v.toNat + Internal.syncD
        events v.toNat +
        Internal.syncD eventsF v.toNat)) ≤ B :=
    hB _
  have slashed : ∑ v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted, Internal.slashW t v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * t.slashedR :=
    Internal.flow_slash h (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
        counted)
  have weightOther := Internal.weighted_le (fun v : ValidatorIndex => Internal.whistC tailC highC
    v.toNat +
    (Internal.syncCr eventsC v.toNat + Internal.syncD events v.toNat + Internal.syncD eventsF
      v.toNat)) d45 d46 d56
  have weightSlash := Internal.weighted_le (fun v : ValidatorIndex => Internal.slashW t v.toNat) d45
    d46 d56
  have lin := Internal.flow_lin t tailC highC eventsC events eventsF (Internal.K4 pulled counted V)
    (Internal.K5 counted V)
    (Internal.K6 pulled counted) (fun i => Internal.credC tailC highC i) (fun i => Internal.propC
      tailC highC i)
    (fun i => Internal.credC tailC highC i)
  beta_reduce at z4 z5 z6 weightOther weightSlash lin
  have aligned : t.consolidationsX % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    Internal.consolidationsX_aligned h
  have key : 0 < (∑ v ∈ Internal.K4 pulled counted V, Internal.flowK t tailC highC eventsC events
    eventsF v.toNat) +
      3 * (∑ v ∈ Internal.K5 counted V,
        Internal.flowK t tailC highC eventsC events eventsF v.toNat (Internal.propC tailC highC
          v.toNat)) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.flowK t tailC highC eventsC events eventsF
        v.toNat) →
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
        WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun pos => by
    obtain ⟨i, c, found⟩ := Internal.flow_pos t tailC highC eventsC events eventsF _ _ _
      (fun i => Internal.credC tailC highC i) (fun i => Internal.propC tailC highC i)
      (fun i => Internal.credC tailC highC i) pos
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (min_le_left _ _)))
      (Internal.flow_key h tailC highC eventsC events eventsF i c found)
  have rate : 0 < (∑ v ∈ Internal.K4 pulled counted V, Internal.flowK t tailC highC eventsC events
    eventsF v.toNat) +
      3 * (∑ v ∈ Internal.K5 counted V,
        Internal.flowK t tailC highC eventsC events eventsF v.toNat (Internal.propC tailC highC
          v.toNat)) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.flowK t tailC highC eventsC events eventsF
        v.toNat) →
      2 ≤ t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat := fun _ => Internal.flow_rate h
  have close := Internal.flow_close preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      WEIGHT_DENOMINATOR.toNat
    (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) (min t.depth t.depthFin)
    t.depth
    (t.consolidationsX / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (3 * B)
    ((∑ v ∈ Internal.K4 pulled counted V, Internal.credN tailC highC v.toNat) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.credN tailC highC v.toNat) +
      3 * (∑ v ∈ Internal.K5 counted V, Internal.propN tailC highC v.toNat))
    ((∑ v ∈ Internal.K4 pulled counted V, Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ Internal.K5 counted V, Internal.consAmt eventsC v.toNat))
    ((∑ v ∈ Internal.K4 pulled counted V, (Internal.whistC tailC highC v.toNat + (Internal.syncCr
      eventsC v.toNat +
        Internal.syncD events v.toNat + Internal.syncD eventsF v.toNat))) +
      (∑ v ∈ Internal.K6 pulled counted, (Internal.whistC tailC highC v.toNat + (Internal.syncCr
        eventsC v.toNat +
        Internal.syncD events v.toNat + Internal.syncD eventsF v.toNat))) +
      3 * (∑ v ∈ Internal.K5 counted V, (Internal.whistC tailC highC v.toNat + (Internal.syncCr
        eventsC v.toNat +
        Internal.syncD events v.toNat + Internal.syncD eventsF v.toNat))))
    ((∑ v ∈ Internal.K4 pulled counted V, Internal.slashW t v.toNat) + (∑ v ∈ Internal.K6 pulled
      counted, Internal.slashW t v.toNat) +
      3 * (∑ v ∈ Internal.K5 counted V, Internal.slashW t v.toNat))
    t.slashedR t.depthFin _ incPos (by decide) key rate (min_le_right _ _) (min_le_left _ _)
    (by
      have := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero aligned)
      omega)
    (by omega)
    (by omega)
    (lin.trans (Nat.mul_le_mul_left _ (by omega)))
  have creditLow : t.creditLow = (33 * t.depth * (t.consolidationsX /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * t.perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
      11 * t.depth * t.otherGain +
      30 * t.depth * (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat + 1) + 9) / 10 := rfl
  rw [hOther] at creditLow
  rw [Nat.mul_assoc (t.consolidationsX / preset.EFFECTIVE_BALANCE_INCREMENT.toNat),
    Nat.mul_assoc (3 * B / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)] at creditLow
  have rateEq : t.flagRate = t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
      WEIGHT_DENOMINATOR.toNat := rfl
  rw [rateEq, creditLow]
  linarith

/-- The keys of `K6` beyond R's registry are paid by the credits.

At a high rate these keys share the cap budget for new keys.

They joined the registry on C's branch, so their stake is the credits that reach them.

At a low gain rate the reserve charges for compounding credits.

Otherwise it charges each key up to the cap. -/
private theorem beyond_keys (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∑ v ∈ (Internal.K6 pulled counted) with pulled.validators.data.size ≤ v.toNat, Internal.eC
      counted v ≤
      (∑ v ∈ (Internal.K6 pulled counted) with pulled.validators.data.size ≤ v.toNat,
        (((Internal.credC tailC highC v.toNat +
            Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
            Internal.whistC tailC highC v.toNat) +
          (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
            v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat) + Internal.bandX fin highC v.toNat)) +
        Internal.capUse config pulled anc fin counted := by
  classical
  by_cases low : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  · refine Nat.le_trans (Finset.sum_le_sum fun v member => ?_) (Nat.le_add_right _ _)
    obtain ⟨inK6, beyond⟩ := Finset.mem_filter.mp member
    exact beyond_key h tail high endEpoch fromFin replayedF tailC highC endEpochC replayedC low
      inK6 beyond
  · -- Each key is at most the cap, and `capUse` is that cap for each key, at a high rate.
    obtain ⟨shared⟩ := h.toFin
    have capped (v : ValidatorIndex) : Internal.eC counted v ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      Internal.effectiveAt_le_capMax (shared.append (fromFin.append tailC)) h.genesis h.caps
        h.early v.toNat
    have highGain : (pinTerms config pulled anc fin).gainHigh = true :=
      gainHigh_eq_true_iff.mpr low
    have total := Finset.sum_le_card_nsmul
      ((Internal.K6 pulled counted).filter fun v => pulled.validators.data.size ≤ v.toNat)
        (Internal.eC counted)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat fun v _ => capped v
    rw [smul_eq_mul] at total
    unfold Internal.capUse
    rw [ite_eq_left highGain]
    exact Nat.le_trans total (Nat.le_add_left _ _)

/-- The keys counted in C and not active at R.

A key whose exit started on R's branch after the split is inactive at R and active in C.

The reserve charges that exit on R's branch.

Its stake in C is at most its stake at R and its rise.

The same bound applies to keys whose scheduled exits R can see. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cJ_le (h : Setting config checks g
  split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    Internal.cJ pulled counted ≤ (((pinTerms config pulled anc fin).joining +
      (∑ v ∈ (Internal.K6 pulled counted) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat =
        true,
        (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat =
        true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat =
        true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted), ((Internal.credC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
        Internal.whistC tailC highC v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted), (Internal.syncF events v.toNat + Internal.syncF eventsC
        v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted),
        (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
          Internal.bandR (eventsF ++ events) v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat =
        true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.bandX fin highC v.toNat) +
      Internal.capUse config pulled anc fin counted) : ℕ) := by
  classical
  -- `cJ` is the stake in C of the keys of `K6`.
  have cJ_eq : Internal.cJ pulled counted = ((∑ v ∈ Internal.K6 pulled counted, Internal.eC counted
    v : ℕ) : ℤ) := by
    unfold Internal.cJ
    push_cast
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [Finset.mem_filter, Internal.K6, Internal.U, Finset.mem_union]
    tauto
  rw [cJ_eq, Nat.cast_le]
  -- The keys at or beyond R's registry are paid by `creditGain` and the credits.
  have beyond := beyond_keys (events := events) h tail high endEpoch fromFin replayedF tailC highC
    endEpochC replayedC
  -- The keys inside R's registry rise by `key_core`, and R's record puts each in a class.
  have core : ∀ v ∈ Internal.K6 pulled counted, v.toNat < pulled.validators.data.size →
      Internal.eC counted v ≤ (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat
        +
          Internal.bandX fin highC v.toNat) +
        (((Internal.credC tailC highC v.toNat +
            Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
            Internal.whistC tailC highC v.toNat) +
          (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
            v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat)) := by
    intro v hv hin
    have := Internal.key_core (config := config) h tail high endEpoch replayed fromFin replayedF
        tailC highC
      endEpochC replayedC v.toNat hin
      (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp hv).2.1)
    unfold Internal.eC Internal.eR
    unfold Internal.keyCeiling at this
    omega
  have classes : ∀ v ∈ Internal.K6 pulled counted, v.toNat < pulled.validators.data.size →
      Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat ≤
        ((if (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
              isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true) then
            Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).lateB v.toNat = true then
            3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).exitedRB v.toNat = true then
            Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).exitingB v.toNat = true then
            Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0) +
          (if (pinTerms config pulled anc fin).pendingRB v.toNat = true then
            Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat else 0)) := by
    intro v hK hin
    obtain ⟨w, found⟩ : ∃ w, pulled.validators.data[v.toNat]? = some w :=
      ⟨_, Array.getElem?_eq_getElem hin⟩
    rcases Internal.K6_class h hK found with c | c | c | c | c
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_left c]; omega
  -- Sum the classes over the keys inside R's registry.
  set inside := (Internal.K6 pulled counted).filter (fun v => v.toNat < pulled.validators.data.size)
    with hInside
  have partition := Finset.sum_filter_add_sum_filter_not (Internal.K6 pulled counted)
    (fun v => v.toNat < pulled.validators.data.size) (Internal.eC counted)
  have notInside : (Internal.K6 pulled counted).filter (fun v => ¬ v.toNat <
    pulled.validators.data.size) =
      (Internal.K6 pulled counted).filter (fun v => pulled.validators.data.size ≤ v.toNat) := by
    refine Finset.filter_congr fun v _ => ?_
    omega
  rw [notInside, ← hInside] at partition
  have insideSum : ∑ v ∈ inside, Internal.eC counted v ≤
      ∑ v ∈ inside, (((Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          Internal.bandX fin highC v.toNat) +
        (((Internal.credC tailC highC v.toNat +
            Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
            Internal.whistC tailC highC v.toNat) +
          (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
            v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat)))) :=
    Finset.sum_le_sum fun v hv =>
      core v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  rw [Finset.sum_add_distrib] at insideSum
  -- The consolidation bands of the inside keys are within those of `K6`.
  have bandSplit : ∑ v ∈ inside, (Internal.eR pulled v + (pinTerms config pulled anc fin).rise
    v.toNat +
        Internal.bandX fin highC v.toNat) =
      ∑ v ∈ inside, (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) +
        ∑ v ∈ inside, Internal.bandX fin highC v.toNat := Finset.sum_add_distrib
  have bandAll : ∑ v ∈ Internal.K6 pulled counted, Internal.bandX fin highC v.toNat =
      ∑ v ∈ inside, Internal.bandX fin highC v.toNat +
        ∑ v ∈ (Internal.K6 pulled counted) with pulled.validators.data.size ≤ v.toNat,
          Internal.bandX fin highC v.toNat := by
    have split := Finset.sum_filter_add_sum_filter_not (Internal.K6 pulled counted)
      (fun v => v.toNat < pulled.validators.data.size) (fun v => Internal.bandX fin highC v.toNat)
    rw [notInside] at split
    exact split.symm
  have classSum : ∑ v ∈ inside, (Internal.eR pulled v + (pinTerms config pulled anc fin).rise
    v.toNat) ≤
      (∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).exitedRB v.toNat = true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).exitingB v.toNat = true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ inside with (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) := by
    refine Nat.le_trans (Finset.sum_le_sum fun v hv =>
      classes v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2) (Nat.le_of_eq ?_)
    simp only [Finset.sum_filter]
    simp only [Finset.sum_add_distrib]
  -- Each class of inside keys is within the matching class of `K6`.
  have restrict : ∀ (p : ValidatorIndex → Prop) [DecidablePred p] (f : ValidatorIndex → ℕ),
      ∑ v ∈ inside with p v, f v ≤ ∑ v ∈ (Internal.K6 pulled counted) with p v, f v := fun p _ f =>
    Finset.sum_le_sum_of_subset (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
  have joinStake : ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true), Internal.eR pulled v ≤
      (pinTerms config pulled anc fin).joining := by
    show _ ≤ joiningStake pulled
    unfold joiningStake
    refine voters_sum_le (fun i => balanceAt pulled i) fun v hv => ?_
    obtain ⟨hi, hj⟩ := Finset.mem_filter.mp hv
    obtain ⟨hK, hin⟩ := Finset.mem_filter.mp hi
    exact Internal.mem_positions_filter config pulled anc fin (Array.getElem?_eq_getElem hin) hj
  have joinRise : ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat ≤
      ∑ v ∈ (Internal.K6 pulled counted) with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat =
        false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat :=
    restrict (fun v => isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true)
      (fun v => (pinTerms config pulled anc fin).rise v.toNat)
  have joinSplit : ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) =
      (∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true), Internal.eR pulled v) +
      ∑ v ∈ inside with (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat := Finset.sum_add_distrib
  have late := restrict (fun v => (pinTerms config pulled anc fin).lateB v.toNat = true)
    (fun v => 3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  have exited := restrict (fun v => (pinTerms config pulled anc fin).exitedRB v.toNat = true)
    (fun v => Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  have exiting := restrict (fun v => (pinTerms config pulled anc fin).exitingB v.toNat = true)
    (fun v => Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  have pending := restrict (fun v => (pinTerms config pulled anc fin).pendingRB v.toNat = true)
    (fun v => Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
  -- The credits, sync flows and slash bands over `K6` split at R's registry.
  have bounds := Finset.sum_filter_add_sum_filter_not (Internal.K6 pulled counted)
    (fun v => v.toNat < pulled.validators.data.size)
    (fun v => (((Internal.credC tailC highC v.toNat +
        Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
          eventsC events eventsF v.toNat) +
            Internal.whistC tailC highC v.toNat) +
          (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
            v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat)))
  rw [notInside, ← hInside] at bounds
  have boundSplit : ∑ v ∈ Internal.K6 pulled counted,
      (((Internal.credC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
            Internal.whistC tailC highC v.toNat) +
          (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
            v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat)) =
      (∑ v ∈ Internal.K6 pulled counted, ((Internal.credC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) +
        Internal.whistC tailC highC v.toNat)) +
      (∑ v ∈ Internal.K6 pulled counted, (Internal.syncF events v.toNat + Internal.syncF eventsC
        v.toNat)) +
      ∑ v ∈ Internal.K6 pulled counted, (Internal.slashR (pinTerms config pulled anc fin) v.toNat +
        Internal.bandC tailC highC v.toNat + Internal.bandR (eventsF ++ events) v.toNat) := by
    simp only [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib] at beyond
  omega

end Terms

end PinDrift
end EthLib.Consensus.Models.Network

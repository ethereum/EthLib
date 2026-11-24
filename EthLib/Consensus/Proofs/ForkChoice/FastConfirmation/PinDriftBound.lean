module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.PreviousEpochRise

/-! The pin reserve bounds the drift of a call's quorum. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## The top-level step, from the bounds of the terms -/

section Closure
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The shared run to the split has a state `b` at the start of the split's epoch.

The run from `b` to the split, `pre`, is the end of the shared run.

The state `b` comes after the finalized state, or before it in its epoch.

No step of the run to `b` starts in the epoch of `b`, so no block of that epoch precedes it. -/
private theorem split_epoch_start (toFin : Run config checks g ⟨fork, fin⟩)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) :
    ∃ (b : BeaconState preset fork) (toB : Run config checks g ⟨fork, b⟩)
      (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩),
      getCurrentEpoch split = getCurrentEpoch b ∧
      (Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
        ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩,
          getCurrentEpoch fin = getCurrentEpoch b) ∧
      (∀ {u w : ForkedBeaconState preset} (step : Step config checks u w), toB.Contains step →
        (getCurrentEpoch u.state).toNat < (getCurrentEpoch b).toNat) ∧
      ((∃ fromB : Run config checks ⟨fork, fin⟩ ⟨fork, b⟩, fromFin = fromB.append pre) ∨
        ∃ toFinB : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, pre = toFinB.append fromFin) := by
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have gFin : (getCurrentEpoch g.state).toNat ≤ (getCurrentEpoch fin).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toFin.chainSteps)
  by_cases inFin : (getCurrentEpoch fin).toNat = (getCurrentEpoch split).toNat
  · by_cases atGenesis : (getCurrentEpoch g.state).toNat = (getCurrentEpoch fin).toNat
    · -- the whole shared run is in one epoch
      have gFork := Run.fork_eq_of_same_epoch toFin (UInt64.toNat_inj.mp atGenesis.symm)
      obtain ⟨gf, gs⟩ := g
      subst gFork
      dsimp only at atGenesis
      exact ⟨gs, Run.nil, toFin.append fromFin, UInt64.toNat_inj.mp (by omega),
        .inr ⟨toFin, UInt64.toNat_inj.mp (by omega)⟩, (fun _ member => by cases member),
        .inr ⟨toFin, rfl⟩⟩
    · -- the boundary into the split's epoch is in the run to the finalized state
      obtain ⟨z, ⟨nf, ns⟩, pre0, ok, rest, cut, hz, hn⟩ := Run.cross_split toFin
        ((getCurrentEpoch fin).toNat - 1) (by omega)
        (by change _ < (getCurrentEpoch fin).toNat; omega)
      dsimp only at hz hn
      have nEpoch : getCurrentEpoch fin = getCurrentEpoch ns :=
        UInt64.toNat_inj.mp (by omega)
      have nFork := Run.fork_eq_of_same_epoch rest nEpoch
      dsimp only at nFork
      subst nFork
      subst cut
      refine ⟨ns, pre0.snoc (Step.slot ok), rest.append fromFin,
        UInt64.toNat_inj.mp (by omega), .inr ⟨rest, nEpoch⟩, fun {u w} step member => ?_,
        .inr ⟨rest, rfl⟩⟩
      cases member with
      | last => omega
      | earlier inner =>
        have := steps_before_end pre0 step inner
        simp only [ix] at this
        omega
  · -- the boundary into the split's epoch is in the run from the finalized state
    obtain ⟨z, ⟨nf, ns⟩, pre0, ok, rest, cut, hz, hn⟩ := Run.cross_split fromFin
      ((getCurrentEpoch split).toNat - 1) (by change (getCurrentEpoch fin).toNat ≤ _; omega)
      (by change _ < (getCurrentEpoch split).toNat; omega)
    dsimp only at hz hn
    have nEpoch : getCurrentEpoch split = getCurrentEpoch ns :=
      UInt64.toNat_inj.mp (by omega)
    have nFork := Run.fork_eq_of_same_epoch rest nEpoch
    dsimp only at nFork
    subst nFork
    subst cut
    refine ⟨ns, toFin.append (pre0.snoc (Step.slot ok)), rest,
      nEpoch, .inl ⟨pre0.snoc (Step.slot ok)⟩, fun {u w} step member => ?_,
      .inl ⟨pre0.snoc (Step.slot ok), rfl⟩⟩
    rcases (Run.contains_append _ _ _).mp member with early | late
    · have := steps_before_end toFin step early
      simp only [ix] at this
      omega
    · cases late with
      | last => omega
      | earlier inner =>
        have := steps_before_end pre0 step inner
        simp only [ix] at this
        omega

/-- The weighted drift, key by key: exact per-key algebra, no reserve term. -/
private theorem drift_le_costs (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ v ∈ Internal.countedQuorum counted, (Internal.countedBalance counted v : ℤ)) +
        3 * (∑ v ∈ V, (Internal.pulledBalance pulled v : ℤ)) -
        2 * (∑ v ∈ Internal.countedActiveVoters counted, (Internal.countedBalance counted v : ℤ)) -
        (∑ v ∈ Internal.pulledActiveVoters pulled, (Internal.pulledBalance pulled v : ℤ)) -
        3 * (∑ v ∈ (Internal.countedQuorum counted).filter (· ∈ V),
          (Internal.countedBalance counted v : ℤ)) ≤
      2 * Internal.voterFallCost pulled counted V +
        2 * Internal.inactiveVoterCost pulled counted V +
        Internal.stayingRiseCost pulled counted V + 3 * Internal.previousOnlyCost pulled counted V +
        Internal.joinedCost pulled counted + Internal.outsideQuorumCost pulled counted +
        Internal.departedCost pulled counted V := by
  have hAR : ∀ v ∈ V, v ∈ Internal.pulledActiveVoters pulled := fun v m => (h.voting v m).1
  have hQ := Internal.glue_quorum h
  have subQ : Internal.countedQuorum counted ⊆ Internal.costKeys pulled counted :=
    fun v m => by simp [Internal.costKeys, m]
  have subAC : Internal.countedActiveVoters counted ⊆ Internal.costKeys pulled counted :=
    fun v m => by simp [Internal.costKeys, m]
  have subAR : Internal.pulledActiveVoters pulled ⊆ Internal.costKeys pulled counted :=
    fun v m => by simp [Internal.costKeys, m]
  have subV : V ⊆ Internal.costKeys pulled counted := fun v m => subAR (hAR v m)
  have subQV : (Internal.countedQuorum counted).filter (· ∈ V) ⊆ Internal.costKeys pulled counted :=
    fun v m => subQ (Finset.mem_filter.mp m).1
  rw [Internal.sum_eq_costKeys subQ, Internal.sum_eq_costKeys subV, Internal.sum_eq_costKeys subAC,
    Internal.sum_eq_costKeys subAR, Internal.sum_eq_costKeys subQV]
  unfold Internal.voterFallCost Internal.inactiveVoterCost Internal.stayingRiseCost
      Internal.previousOnlyCost Internal.joinedCost Internal.outsideQuorumCost Internal.departedCost
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro v _
  simp only [Finset.mem_filter]
  by_cases hv : v ∈ V
  · have hr := hAR v hv
    by_cases ha : v ∈ Internal.countedActiveVoters counted
    · have hq := hQ v hv ha
      simp [hv, ha, hr, hq]
      omega
    · by_cases hq : v ∈ Internal.countedQuorum counted <;> simp [hv, ha, hr, hq] <;> omega
  · by_cases hq : v ∈ Internal.countedQuorum counted <;>
      by_cases ha : v ∈ Internal.countedActiveVoters counted <;>
      by_cases hr : v ∈ Internal.pulledActiveVoters pulled <;> simp [hv, ha, hr, hq] <;> omega

/-- A bound on `x` gives the bound at weight two against weight three. -/
private theorem two_le_three {x : ℤ} {r : ℕ} (le : x ≤ r) : 2 * x ≤ 3 * (r : ℤ) := by omega

/-- The total read is at least the active stake. -/
private theorem stake_le_total {state : BeaconState preset fork} {total : Gwei}
    (ok : getTotalActiveBalance state = .ok total) :
    (∑ v ∈ activeVoters state, balanceAt state v.toNat) ≤ total.toNat := by
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok ok)
  rw [value]
  exact le_max_right _ _

/-- The quorum drifts from a call's pulled-up state to a counting state by at most the pin reserve.

The bound holds under the drift setting, which requires `fusaka ≤ fork < glamsterdam`. -/
theorem le_pinReserve (h : Setting config checks g split fin pulled anc counted V)
    {total pulledTotal : Gwei} (totalOk : getTotalActiveBalance counted = .ok total)
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    -- The quorum at the counting state and `V` at the pulled-up state weigh three each.
    3 * stake (fun v => balanceAt counted v.toNat) (quorumVoters counted) +
        3 * stake (fun v => balanceAt pulled v.toNat) V ≤
      -- Their sum is at most twice the counting total plus the pulled-up total and the pin reserve.
      2 * total.toNat + pulledTotal.toNat + pinReserve config pulled anc fin +
        -- It also adds three times the counting stake of the quorum voters that are in `V`.
        3 * stake (fun v => balanceAt counted v.toNat) {v ∈ quorumVoters counted | v ∈ V} := by
  have nn {ι : Type} (S : Finset ι) (f : ι → ℕ) : (0 : ℤ) ≤ ∑ x ∈ S, (f x : ℤ) :=
    Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
  obtain ⟨tail⟩ := h.toPulled
  obtain ⟨tailC⟩ := h.toCounted
  -- Both replays read the events up to the call's epoch.
  obtain ⟨high, hHigh⟩ : ∃ n, n = (getCurrentEpoch pulled).toNat := ⟨_, rfl⟩
  obtain ⟨highC, hHighC⟩ : ∃ n, n = (getCurrentEpoch pulled).toNat := ⟨_, rfl⟩
  have endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1 := by omega
  have endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1 := by have := h.near; omega
  have highLe : highC ≤ (getCurrentEpoch pulled).toNat := by omega
  have highLeR : high ≤ (getCurrentEpoch pulled).toNat := by omega
  clear hHigh hHighC
  obtain ⟨events, replayed⟩ := tail.balanceEvents_ok h.early high
  obtain ⟨eventsC, replayedC⟩ := tailC.balanceEvents_ok h.early highC
  have key := drift_le_costs h
  have tC := stake_le_total totalOk
  have tR := stake_le_total pulledOk
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨b, toB, pre, sameEpoch, link, earlier, shape⟩ := split_epoch_start toFin fromFin
  obtain ⟨eventsF, replayedF⟩ := fromFin.balanceEvents_ok h.early high
  obtain ⟨eventsP, replayedP⟩ := pre.balanceEvents_ok h.early highC
  have sV := two_le_three (Internal.cV_le (config := config) h high endEpoch events fromFin
    replayedF
    tailC highC endEpochC replayedC)
  have sN := Internal.stayingRiseCost_le (config := config) h tail high endEpoch replayed fromFin
    replayedF tailC highC endEpochC replayedC
  have sP := Internal.previousOnlyCost_le (config := config) h tail high endEpoch replayed fromFin
    toB pre sameEpoch earlier replayedF tailC highC endEpochC replayedC replayedP
  have sJ := Internal.joinedCost_le (config := config) h tail high endEpoch replayed fromFin
    replayedF tailC highC endEpochC replayedC
  -- The terms that `keyExtra` adds are paid by the flow split, the units and the induced leak.
  have reg := Internal.registry_bounds (config := config) h tail high endEpoch replayed fromFin
    replayedF
    tailC highC endEpochC replayedC toB pre sameEpoch earlier replayedP
  have f1 := Internal.flow_split_of (config := config) h tail high endEpoch replayed fromFin
    replayedF
    tailC highC endEpochC replayedC highLeR highLe pre reg.1 reg.2
  have u1 := (Internal.budget_units (config := config) h tail high replayed fromFin replayedF tailC
    highC
    endEpochC replayedC).1
  have u2 := Internal.budget_csUnits (config := config) (events := events) (eventsF := eventsF) h
    fromFin
    tailC highC endEpochC replayedC
  have l1 := (Internal.budget_syncLeak (config := config) h tail high endEpoch replayed fromFin
    replayedF).1
  have cg := Internal.creditGain_split config pulled anc fin
  have b1 := Internal.budget_exiting (config := config) h tailC
  have b2 := Internal.budget_late (config := config) h
  have b3 := Internal.budget_queues (config := config) h tailC
  have b4 := Internal.budget_credits (config := config) h toB link pre sameEpoch tailC highC
    endEpochC replayedC
  have b5 := Internal.budget_branchR (config := config) h tail high endEpoch replayed fromFin toB
    pre sameEpoch replayedF tailC highC endEpochC replayedC replayedP
  have replayedPHigh : pre.balanceEvents high = .ok eventsP := by
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have later := UInt64.le_iff_toNat_le.mp h.later
    rw [DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le pre (localHigh := highC)
      (by simp only; omega) (by simp only; omega)]
    exact replayedP
  have b6 := Internal.budget_sync (config := config) h tail high replayed fromFin pre sameEpoch
    shape replayedF
    tailC highC replayedC replayedPHigh
  have b7 := Internal.budget_fall (config := config) h
  have b8 := Internal.budget_rise (config := config) h
  have b10 := Internal.budget_deposits (config := config) h tail high endEpoch replayed
  have b11 := Internal.budget_queueRise (config := config) h tailC highC
  have b12 := Internal.budget_exitingRise (config := config) h tailC
  have b13 := Internal.budget_exitingCredits (config := config) h toB link pre sameEpoch tailC highC
    replayedC
  have b17 := Internal.budget_exitingBands (config := config) h tailC highC
  have b18 := Internal.budget_pendingR (config := config) h
  have b15 := Internal.budget_consolidations (config := config) h fromFin tail high endEpoch
    replayed replayedF
    highLeR tailC highC endEpochC replayedC highLe
  have b16 := Internal.budget_exitedR (config := config) (pulled := pulled) (anc := anc)
    (fin := fin) (counted := counted)
  -- `budget_consolidations` pays the band of each due entry: the counted keys' bands and V's share.
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have bandV : ∑ v ∈ Internal.stayingKeys pulled counted V, Internal.bandX fin highC v.toNat +
        ∑ v ∈ Internal.joinedKeys pulled counted, Internal.bandX fin highC v.toNat +
        3 * ∑ v ∈ Internal.previousOnlyKeys counted V, Internal.bandX fin highC v.toNat +
        3 * (preset.upwardBand * Internal.dueAt fin high V) =
      preset.upwardBand * (Internal.dueAt fin highC (Internal.stayingKeys pulled counted V) +
        Internal.dueAt fin highC (Internal.joinedKeys pulled counted) + 3 * Internal.dueAt fin highC
          (Internal.previousOnlyKeys counted V) +
        3 * Internal.dueAt fin high V) := by
    rw [Internal.bandX_sum fin electra highC, Internal.bandX_sum fin electra highC,
      Internal.bandX_sum fin electra highC]
    ring
  have b15' := Nat.le_trans (Nat.add_le_add_left (Nat.le_of_eq bandV) _) b15
  have qs := Internal.queues_split config pulled anc fin
  have b14 := Internal.budget_whistle_of (config := config) h tail high endEpoch replayed fromFin
    replayedF
    tailC highC endEpochC replayedC pre reg.1 reg.2
  simp only [Internal.whistleActiveRow] at b14
  have b19 := Internal.budget_joinRise (config := config) h
  have b20 := Internal.newlySlashed_active_split (config := config) h
  have b21 := Internal.budget_capSlots (config := config) h
  have w4 : 0 ≤ ∑ v ∈ (Internal.stayingKeys pulled counted V),
      (Internal.whistC tailC highC v.toNat : ℤ) :=
    nn _ _
  have w6 : 0 ≤ ∑ v ∈ (Internal.joinedKeys pulled counted),
      (Internal.whistC tailC highC v.toNat : ℤ) :=
    nn _ _
  have b9 := Internal.budget_joining (config := config) (pulled := pulled) (anc := anc) (fin := fin)
  -- The upward bands of the charged newly slashed keys are not read by the drift.
  have bandPosSC : (0 : ℤ) ≤ ((∑ v ∈ Internal.chargedNewlySlashed pulled counted split tailC,
      if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
        eventsP v.toNat then
        preset.upwardBand else 0 : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold pinReserve
  unfold PinTerms.total stake
  simp only [Internal.countedActiveVoters, Internal.pulledActiveVoters, Internal.countedQuorum,
      Internal.countedBalance, Internal.pulledBalance] at *
  simp only [Internal.activeNewlySlashed, Internal.newlySlashedWhistleReward] at *
  simp only [Internal.keyExtra, Finset.sum_add_distrib] at sV sN sP sJ b2 b5 b6 b14 b16 b18 b20 ⊢
  simp only [← Finset.mul_sum] at b6 b14
  zify at *
  have syncPos : 0 ≤ ∑ x ∈ Internal.stayingKeys pulled counted V,
      (Internal.syncF events x.toNat : ℤ) :=
    nn _ _
  have syncPosC : 0 ≤ ∑ x ∈ Internal.stayingKeys pulled counted V,
      (Internal.syncF eventsC x.toNat : ℤ) :=
    nn _ _
  -- `budget_sync` weighs the shared segment's staying-key debits three times.
  --
  -- `stayingRiseCost_le` weighs them once.
  have syncPosF : 0 ≤ ∑ x ∈ Internal.stayingKeys pulled counted V,
      (Internal.syncD eventsF x.toNat : ℤ) :=
    nn _ _
  -- `budget_units` also weighs newly and created slashed keys' units; the drift does not.
  have unitPosSC : 0 ≤ ∑ x ∈ Internal.newlySlashed pulled counted split,
      (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF x.toNat :
        ℤ) :=
    nn _ _
  have unitPosCS : 0 ≤ ∑ x ∈ Internal.createdSlashed counted split,
      (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF x.toNat :
        ℤ) :=
    nn _ _
  -- `budget_credits` compounds to pay a tenth of the shared credits `previousOnlyCost_le` reads.
  have scChargedPre : 0 ≤
      ∑ v ∈ Internal.chargedNewlySlashed pulled counted split tailC,
        (Internal.whistC pre highC v.toNat : ℤ) :=
    nn _ _
  have wShareSC : 0 ≤ ((Internal.wShare preset fork
      (∑ v ∈ Internal.newlySlashed pulled counted split, Internal.propN pre highC v.toNat) : ℕ) :
        ℤ) := Int.natCast_nonneg _
  have syncPre : 0 ≤ ∑ v ∈ Internal.newlySlashed pulled counted split,
      (Internal.syncCr eventsP v.toNat : ℤ) :=
    nn _ _
  have proposerPre : 0 ≤ ∑ x ∈ Internal.previousOnlyKeys counted V,
      (Internal.propN pre highC x.toNat : ℤ) :=
    nn _ _
  have xPos : 0 ≤ (33 * ((pinTerms config pulled anc fin).consolidationsX : ℤ) + 9) / 10 := by
    positivity
  have proposerPos : 0 ≤ ((pinTerms config pulled anc fin).depth : ℤ) *
      ((pinTerms config pulled anc fin).syncProposer : ℤ) := by positivity
  have unitPos : 0 ≤ ((pinTerms config pulled anc fin).unitGain : ℤ) *
      ((pinTerms config pulled anc fin).consolidationsXCount : ℤ) := by positivity
  -- A joined key whose exit R reads weighs once in the drift and three times in `exiting`.
  have exitingK6 : 0 ≤ ∑ v ∈ Internal.joinedKeys pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true, (balanceAt pulled v.toNat : ℤ) :=
    nn _ _
  have riseK6 : 0 ≤ ∑ v ∈ Internal.joinedKeys pulled counted with
      (pinTerms config pulled anc fin).exitingB v.toNat = true,
        ((pinTerms config pulled anc fin).rise v.toNat : ℤ) :=
    nn _ _
  -- The keys slashed at C add a nonnegative leak to the left side of `budget_syncLeak`.
  have leakSC : 0 ≤ ∑ v ∈ Internal.newlySlashed pulled counted split,
      (Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat : ℤ) :=
    nn _ _
  by_cases gH : (pinTerms config pulled anc fin).gainHigh = true
  · simp only [gH, ↓reduceIte] at b14 b21 u2
    linarith
  · simp only [gH, Bool.false_eq_true, ↓reduceIte] at b14 b21 u2
    linarith

end Closure

end PinDrift
end EthLib.Consensus.Models.Network

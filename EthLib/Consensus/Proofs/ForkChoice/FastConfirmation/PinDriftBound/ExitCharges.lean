module

import EthLib.Base.Proofs.Nat
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
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.Setting

/-! The pin reserve: exit charges, balance bounds and credit budgets. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety PinKeys
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## The bounds of the terms -/

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- Activity up to the seed lookahead after the split is the same at R and C. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.activity_shared {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) {e : Epoch}
    (fixed : e.toNat ≤ (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat)
    (i : ℕ) : isActiveAt pulled e i = isActiveAt counted e i := by
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨rc⟩ := h.toCounted
  have inside : e ≤ activityFixedEpoch split := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := e.toNat_lt
    omega
  exact (activeKept_of_chainSteps rp.chainSteps e inside i).trans
    (activeKept_of_chainSteps rc.chainSteps e inside i).symm

/-- A key active at C's epoch is activated by then at R, when that epoch is within the lookahead.

Activity up to the seed lookahead after the split is the same on both branches. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.activation_le_of_active {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V)
    (bound : (getCurrentEpoch counted).toNat ≤
      anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat)
    {v : ValidatorIndex} (member : v ∈ Internal.AC counted) {w : Validator}
    (found : pulled.validators.data[v.toNat]? = some w) :
    w.activationEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  obtain ⟨u, foundU, activeU⟩ := Internal.active_of_activeVoters h.early member
  have activeAtC : isActiveAt counted (getCurrentEpoch counted) v.toNat = true :=
    isActiveAt_eq_true_iff.mpr ⟨u, foundU, activeU⟩
  have activeAtR : isActiveAt pulled (getCurrentEpoch counted) v.toNat = true := by
    rw [Internal.activity_shared h (e := getCurrentEpoch counted) (by omega) v.toNat]
    exact activeAtC
  obtain ⟨w', found', active⟩ := isActiveAt_eq_true_iff.mp activeAtR
  rw [found] at found'
  cases found'
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  exact UInt64.le_iff_toNat_le.mp active.1

/-- Glue: an unslashed V key active in C counts in C's quorum. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.glue_quorum (h : Setting config
  checks g split fin pulled anc counted V) :
    ∀ v ∈ V, v ∈ Internal.AC counted → v ∈ Internal.Q counted := by
  intro v member active
  have unslashed := (h.voting v member).2
  have listed : v ∈ getActiveValidatorIndices counted (getCurrentEpoch counted) := by
    simpa [Internal.AC, activeVoters] using active
  have inside := lt_size_of_mem_getActiveValidatorIndices listed
  have found : counted.validators.data[v.toNat]? = some counted.validators.data[v.toNat] :=
    Array.getElem?_eq_getElem inside
  have flag : ((counted.validators.data[v.toNat]?).map (·.slashed)).getD true = false := by
    simpa [slashedFlagAt, found] using unslashed
  simp only [Internal.Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append]
  exact ⟨.inl listed, flag⟩

/-- The two costs of V keys are the fall of those active in C and the stake of the others. -/
private theorem cV_split (h : Setting config checks g split fin pulled anc counted V) :
    Internal.cV1 pulled counted V + Internal.cV2 pulled counted V =
      ∑ v ∈ V.filter (· ∈ Internal.AC counted), ((Internal.eR pulled v : ℤ) - Internal.eC counted v)
        +
        ∑ v ∈ Internal.VN counted V, (Internal.eR pulled v : ℤ) := by
  classical
  have sub : V ⊆ Internal.U pulled counted := fun v hv =>
    Finset.mem_union_right _ (h.voting v hv).1
  unfold Internal.cV1 Internal.cV2 Internal.VN
  congr 1
  · rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨sub a, a, b⟩⟩
  · rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨_, a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨sub a, a, b⟩⟩

/-- The fall of the V keys, from their per-key facts.

The first fact is for a V key that is active in C: its fall and what C's floor leaves out.

The floor leaves out the key's sync debits from the finalized block, and their rounding band.

The second is for a V key that is not active in C: the same, and the charges that the sum names.

The shared run from the finalized block adds the key's sync debits to the sum.

C's tail adds its sync movement. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cV_le_of (h : Setting config checks
  g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)}
    (active : ∀ v ∈ V, v ∈ Internal.AC counted → (Internal.eR pulled v : ℤ) - Internal.eC counted v
      ≤
      ((pinTerms config pulled anc fin).fall v.toNat : ℤ) +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
          Internal.bandR (eventsF ++ eventsC) v.toNat)
    (left : ∀ v ∈ Internal.VN counted V, (Internal.eR pulled v : ℤ) ≤
      ((pinTerms config pulled anc fin).fall v.toNat +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
        Internal.bandR (eventsF ++ eventsC) v.toNat + Internal.exitQ tailC v.toNat +
        (if (pinTerms config pulled anc fin).exitingB v.toNat = true then Internal.eR pulled v else
          0) +
        (if (pinTerms config pulled anc fin).lateB v.toNat = true then Internal.eR pulled v else 0)
          : ℕ)) :
    Internal.cV1 pulled counted V + Internal.cV2 pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat))
          +
        (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ (Internal.VN counted V), Internal.exitQ tailC v.toNat) +
        (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat =
          true,
          Internal.eR pulled v) +
        (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
          Internal.eR pulled v) : ℕ) := by
  classical
  rw [cV_split h]
  -- the bound of each key that does not depend on how it left
  let P : ValidatorIndex → ℕ := fun v =>
    (pinTerms config pulled anc fin).fall v.toNat +
      ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
        Internal.bandR (eventsF ++ eventsC) v.toNat
  let X : ValidatorIndex → ℕ := fun v =>
    Internal.exitQ tailC v.toNat +
      (if (pinTerms config pulled anc fin).exitingB v.toNat = true then Internal.eR pulled v else 0)
        +
      (if (pinTerms config pulled anc fin).lateB v.toNat = true then Internal.eR pulled v else 0)
  have first : ∑ v ∈ V.filter (· ∈ Internal.AC counted), ((Internal.eR pulled v : ℤ) - Internal.eC
    counted v) ≤
      ∑ v ∈ V.filter (· ∈ Internal.AC counted), (P v : ℤ) := by
    refine Finset.sum_le_sum fun v hv => ?_
    obtain ⟨member, act⟩ := Finset.mem_filter.mp hv
    have := active v member act
    simp only [P]
    push_cast at this ⊢
    omega
  have second : ∑ v ∈ Internal.VN counted V, (Internal.eR pulled v : ℤ) ≤
      ∑ v ∈ Internal.VN counted V, ((P v : ℤ) + X v) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have := left v hv
    simp only [P, X]
    push_cast at this ⊢
    omega
  have partition : ∑ v ∈ V, (P v : ℤ) =
      ∑ v ∈ V.filter (· ∈ Internal.AC counted), (P v : ℤ) + ∑ v ∈ Internal.VN counted V, (P v : ℤ)
        := by
    unfold Internal.VN
    exact (Finset.sum_filter_add_sum_filter_not V (· ∈ Internal.AC counted) _).symm
  have total : ∑ v ∈ V, (P v : ℤ) =
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat))
          +
        (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) : ℕ) := by
    simp only [P]
    push_cast
    simp only [Finset.sum_add_distrib]
  have exits : ∑ v ∈ Internal.VN counted V, (X v : ℤ) =
      ((∑ v ∈ (Internal.VN counted V), Internal.exitQ tailC v.toNat) +
        (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat =
          true,
          Internal.eR pulled v) +
        (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
          Internal.eR pulled v) : ℕ) := by
    simp only [X, Finset.sum_filter]
    push_cast
    simp only [Finset.sum_add_distrib]
  have split : ∑ v ∈ Internal.VN counted V, ((P v : ℤ) + X v) =
      ∑ v ∈ Internal.VN counted V, (P v : ℤ) + ∑ v ∈ Internal.VN counted V, (X v : ℤ) :=
        Finset.sum_add_distrib
  push_cast at total exits ⊢
  omega

/-- A key that is unslashed at the end of a run is unslashed at its start.

A slashed validator stays slashed at its index along a run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.unslashed_of_run {x y :
  ForkedBeaconState preset} (run : Run config checks x y)
    {i : ℕ} {a : Validator} (found : x.state.validators.data[i]? = some a)
    (clean : ∀ w, y.state.validators.data[i]? = some w → w.slashed = false) :
    a.slashed = false := by
  cases flag : a.slashed
  · rfl
  · obtain ⟨u, read, marked⟩ := run.slashedPersistence i a found flag
    simp [clean u read] at marked

/-- The guards of the floor trace of a run from a state `zs` of the run from the finalized block.

The run ends at any state `y` that is at most one epoch after `pulled`.

The slashing quotient at `zs` is the guard's, which is positive.

The window of the slashing vector and the slashing quotient of each step are the guard's.

No upgrade runs from Fulu, so no step records a crossing.

It is the part of the floor of a key, on R's run and on C's, that does not read the key. -/
private theorem floor_guards (h : Setting config checks g split fin pulled anc counted V)
    {zs y : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (endpoint : (getCurrentEpoch y).toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    0 < DirectSafety.Apriori.minSlashingPenaltyQuotient preset
      (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩ (getCurrentEpoch pulled).toNat) ∧
    ∀ {m n : ForkedBeaconState preset}, Run config checks ⟨fork, zs⟩ m →
      ∀ step : Step config checks m n, Run config checks n ⟨fork, y⟩ →
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch zs).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      DirectSafety.Apriori.minSlashingPenaltyQuotient preset
        (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩
          (getCurrentEpoch pulled).toNat) ≤
        (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing := by
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finZ : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch zs).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have atFin := DirectSafety.Apriori.Internal.slashing_quotient_of_electra (config := config)
    (checks := checks) (high := (getCurrentEpoch pulled).toNat)
    (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) electra
  have atZ := DirectSafety.Apriori.Internal.slashing_quotient_of_electra (config := config)
    (checks := checks) (high := (getCurrentEpoch pulled).toNat)
    (Run.nil : Run config checks ⟨fork, zs⟩ ⟨fork, zs⟩) electra
  refine ⟨?_, fun before step after => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨_, _, _, _, _, _, _, quotient, _⟩ := h.guard
    rw [atZ, ← atFin]
    exact quotient
  · have window := DirectSafety.Apriori.Internal.short_window_of_guard h.guard endpoint
      ((Run.nil.snoc step).append after)
    simp only at window ⊢
    omega
  · exact (DirectSafety.Apriori.Internal.slashing_quotient_of_electra before electra).le
  · intro added addedOk
    exact DirectSafety.Apriori.Internal.no_crossing_of_regime (toFin.append pre) before
      h.genesis h.caps step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps after.chainSteps) h.early)
      (.inl (Nat.le_trans electra (fork_le_of_chainSteps before.chainSteps))) addedOk

/-- R's balance of a key that does not exit in the window falls only by its debit events.

The floor starts from the smaller of the key's balance at a state `zs` of R's run and its cap.

The state `zs` lies on R's run from the finalized block, and the rest of the run leads to `pulled`.

The guards of the floor trace come from the setting's guard at the finalized block.

The window of the slashing vector and the slashing quotient are the guard's.

No upgrade runs from Fulu, so no step records a crossing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_floorR_from (h : Setting config
  checks g split fin pulled anc counted V)
    {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : rest.balanceEvents high = .ok events)
    (i : ValidatorIndex) (val : Validator)
    (initial : zs.validators.data[i.toNat]? = some val) (unslashed : val.slashed = false)
    (stays : ∀ w, pulled.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pulled⟩),
      (before.snoc step).append after = rest → ∀ w,
      n.state.validators.data[i.toNat]? = some w → high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u → high + 1 < u.withdrawableEpoch.toNat) :
    min (actualBalanceAt ⟨fork, zs⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat ≤
      actualBalanceAt ⟨fork, pulled⟩ i.toNat +
        (events.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum +
        (events.map (Internal.syncDebit i.toNat)).sum +
        (events.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨positive, guards⟩ := floor_guards h pre (y := pulled) (Nat.le_succ _)
  refine Internal.Run.balanceFloor_events_or_fulu (toFin.append pre) rest h.genesis h.caps
    (Internal.Setting.delay h)
    h.early high endEpoch i val initial unslashed (Or.inr h.fulu) _ positive ?_ stays replayed
  intro m n before step after cut w found
  exact ⟨retained before step after cut w found, guards before step after⟩

/-- From Fusaka and before Gloas, the parameters are those of Fusaka. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.parameters_of_fusaka {fork : Fork}
  (fusaka : .fusaka ≤ fork)
    (early : fork < .glamsterdam) :
    EthLib.Consensus.parameters preset fork = EthLib.Consensus.parameters preset .fusaka := by
  cases fork <;> first
    | rfl
    | exact absurd fusaka (by decide)
    | exact absurd early (by decide)

/-- The floor debit of a replay is its penalties plus its sync debits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.floorPenaltyDebit_sum (i : ℕ)
  (events : List (BalanceEvent preset)) :
    (events.map (DirectSafety.Apriori.Internal.floorPenaltyDebit i)).sum =
      (events.map (DirectSafety.Apriori.Internal.penaltyDebit i)).sum +
        (events.map (Internal.syncDebit i)).sum := by
  rw [← List.sum_map_add]
  rfl

/-- The debit that a segment's potential floor leaves is at most the debits of the whole run.

The run's events are the segment's, then the rest.

The debits are the sync debits and the partial withdrawals. -/
private theorem prefix_debit_le (i : ValidatorIndex) (before rest : List (BalanceEvent preset))
    (D : ℕ) (split : D + (before.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum =
      (before.map (DirectSafety.Apriori.Internal.floorPenaltyDebit i.toNat)).sum +
        (before.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum) :
    D ≤ ((before ++ rest).map (Internal.syncDebit i.toNat)).sum +
      ((before ++ rest).map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum := by
  have splitDebit := Internal.floorPenaltyDebit_sum i.toNat before
  simp only [List.map_append, List.sum_append]
  omega

/-- A run's debit events and one slashing penalty bound the fall of a key's balance.

The run starts at a state `zs` of R's run from the finalized block.

It ends within one epoch after the call.

The floor starts from the smaller of the key's balance at `zs` and its largest balance.

Its effective balance stays at most `top` along the run.

The key is unslashed at `zs`.

Or it is slashed there, with its withdrawal at least the slashings vector past the finalized epoch.

Then its delayed penalty is not due along the run, since the window is shorter than half the vector.

The slashing penalty is then at most `top` over the slashing quotient, whenever the run slashes it.

A key slashed at `zs` pays no slashing penalty along the run.

The guard at the finalized block supplies the conditions for the floor along the branch.

Nothing in the statement needs the key to be slashed, so it holds for a key that stays unslashed.

A step may assign the key's exit within the window, if its withdrawable epoch is beyond the window.

No upgrade runs from Fulu, so no step records a crossing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashed_floor (h : Setting config
  checks g split fin pulled anc counted V)
    {zs e : BeaconState preset fork}
    (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (tail : Run config checks ⟨fork, zs⟩ ⟨fork, e⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch e).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (i : ValidatorIndex) (val : Validator)
    (initial : zs.validators.data[i.toNat]? = some val)
    (slashedLate : val.slashed = true → (getCurrentEpoch fin).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ val.withdrawableEpoch.toNat)
    (top : ℕ)
    (envelope : ∀ z ∈ tail.balancePath, effectiveAt z i.toNat ≤ top)
    (retained : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (post : Run config checks n ⟨fork, e⟩),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u → high + 1 < u.withdrawableEpoch.toNat) :
    min (actualBalanceAt ⟨fork, zs⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat ≤
      actualBalanceAt ⟨fork, e⟩ i.toNat +
        (events.map (DirectSafety.Apriori.Internal.penaltyDebit i.toNat)).sum +
        (events.map (Internal.syncDebit i.toNat)).sum +
        (events.map (DirectSafety.Apriori.Internal.floorPartialDebit i)).sum +
        (if val.slashed = true then 0 else
          top / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) := by
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨positive, guards⟩ := floor_guards h toZ (y := e) near
  have member : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks ⟨fork, zs⟩ m)
      (step : Step config checks m n) (post : Run config checks n ⟨fork, e⟩),
      (pre.snoc step).append post = tail → m ∈ tail.balancePath := by
    intro m n pre step post cut
    obtain ⟨front, atEnd⟩ := Run.balancePath_last pre
    have path := Run.balancePath_append (pre.snoc step) post
    rw [cut] at path
    rw [path]
    simp [Run.balancePath, atEnd]
  have start : effectiveAt ⟨fork, zs⟩ i.toNat ≤ top := by
    obtain ⟨rest, atHead⟩ := Run.balancePath_head tail
    exact envelope _ (by rw [atHead]; exact List.mem_cons_self)
  obtain ⟨last, trace, balance, debt, -, w, final, -, -, -, ceiling, startNone⟩ :=
    DirectSafety.Apriori.Internal.FloorTrace.run_of_le_cap_general (toFin.append toZ) tail
      h.genesis h.caps (Internal.Setting.delay h) h.early high endEpoch i val initial (Or.inr
        h.fulu)
      (min (actualBalanceAt ⟨fork, zs⟩ i.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat) top _
      (Nat.min_le_right _ _) positive
      (fun pre step post cut w found =>
        ⟨retained pre step post cut w found,
          ⟨fun _ => (guards pre step post).1, fun s => by
            have window := DirectSafety.Apriori.Internal.short_window_of_guard h.guard near
              ((Run.nil.snoc step).append post)
            have late := slashedLate s
            simp only [UInt64.toNat_div, UInt64.reduceToNat] at window ⊢
            omega⟩,
          (guards pre step post).2⟩)
      replayed
  obtain ⟨-, below⟩ := ceiling top start fun pre step post cut =>
    envelope _ (member pre step post cut)
  have floor := DirectSafety.Apriori.Internal.FloorTrace.balance_floor_general trace
    (by simp)
  have penalty : last.slashedHigh.elim 0 (fun s =>
      top / DirectSafety.Apriori.minSlashingPenaltyQuotient preset
        (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩
          (getCurrentEpoch pulled).toNat) + (s - top)) ≤
      (if val.slashed = true then 0 else
        top / DirectSafety.Apriori.minSlashingPenaltyQuotient preset
          (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩
            (getCurrentEpoch pulled).toNat)) := by
    by_cases startSlashed : val.slashed = true
    · rw [startNone startSlashed, ite_eq_left startSlashed]
      exact Nat.le_refl _
    · rw [ite_eq_right startSlashed]
      cases flag : last.slashedHigh with
      | none => exact Nat.zero_le _
      | some s =>
        have capped := below s flag
        simp only [Option.elim]
        omega
  rw [balance, debt, Internal.floorPenaltyDebit_sum] at floor
  have same : DirectSafety.Apriori.minSlashingPenaltyQuotient preset
      (DirectSafety.Apriori.preElectraEpochs config ⟨fork, zs⟩ (getCurrentEpoch pulled).toNat) =
        (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat :=
    DirectSafety.Apriori.Internal.slashing_quotient_of_electra (config := config)
      (checks := checks) (high := (getCurrentEpoch pulled).toNat)
      (Run.nil : Run config checks ⟨fork, zs⟩ ⟨fork, zs⟩) electra
  rw [← same]
  split_ifs at penalty ⊢ <;> omega

/-- A state of the balance path of a run is the end of a prefix of the run.

The state inside a slot step comes after the epoch transition and before the upgrades.

It is the end of the step, since no fork upgrade runs when the fork does not rise. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.balancePath_endpoint {x m y :
  ForkedBeaconState preset}
    (rp : Run config checks x m) (rest : Run config checks m y) (back : y.fork ≤ x.fork)
    {p : ForkedBeaconState preset} (member : p ∈ rp.balancePath) :
    ∃ (r1 : Run config checks x p) (r2 : Run config checks p y),
      r1.append r2 = rp.append rest := by
  rcases rp.mem_balancePath_split member with
    ⟨rq, rest', eq⟩ | ⟨q, n, rq, ok, rest', adv, eq, -, hp, up⟩
  · subst eq
    exact ⟨rq, rest'.append rest, Run.append_assoc _ _ _⟩
  · subst eq
    have order : n.fork ≤ q.fork :=
      Nat.le_trans (fork_le_of_chainSteps rest'.chainSteps)
        (Nat.le_trans (fork_le_of_chainSteps rest.chainSteps)
          (Nat.le_trans back (fork_le_of_chainSteps rq.chainSteps)))
    have same := processUpgrades_eq_of_fork_le up order
    have pn : p = n := hp.trans same.symm
    subst pn
    exact ⟨rq.snoc (Step.slot ok), rest'.append rest, Run.append_assoc _ _ _⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The guards of the floor trace of a segment of C's run.

The segment runs from `wS` to `pS`, and a run to the end `e` of C's run follows it.

The floor also requires the key to stay within the segment's exit guard.

The slashing quotient is the fork's, and the segment ends by the call's cutoff. -/
private theorem segment_guards (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork}
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (i : ValidatorIndex)
    {wS pS : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, wS⟩)
    (seg : Run config checks ⟨fork, wS⟩ ⟨fork, pS⟩) (rest : Run config checks ⟨fork, pS⟩ ⟨fork, e⟩)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat)) :
    (getCurrentEpoch pS).toNat ≤ (getCurrentEpoch pulled).toNat + 1 ∧
      ∃ quotient : ℕ, 0 < quotient ∧
        quotient = (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
        ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
          (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
          (before.snoc step).append after = seg → ∀ w,
          n.state.validators.data[i.toNat]? = some w →
          ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
            ∀ u, m.state.validators.data[i.toNat]? = some u →
              (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) ∧
          (getCurrentEpoch m.state).toNat < (getCurrentEpoch wS).toNat +
            preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
              (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
          quotient ≤
            (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
          ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing := by
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
  simp only at order
  have endEpoch : (getCurrentEpoch pS).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  obtain ⟨positive, guards⟩ := floor_guards h (zs := wS) (y := pS) pre endEpoch
  exact ⟨endEpoch, _, positive,
    slashing_quotient_of_electra (high := (getCurrentEpoch pulled).toNat)
      (Run.nil : Run config checks ⟨fork, wS⟩ ⟨fork, wS⟩) (Nat.le_trans (by decide) h.fulu),
    fun before step after cut w found =>
      ⟨retained before step after cut w found, guards before step after⟩⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The potential floor of a segment of C's run, read at the state where the segment starts.

The segment runs from `wS` to `pS`.

A run from the finalized block to `wS` comes before it, and a run to the end `e` after it.

The key is unslashed at the end, and its exit is after the call's cutoff at each state of the run.

The rate bounds the pass penalties of each step by a fraction of its effective balance.

The closed form reads the balance and the cap of the key at the start of the segment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.segment_potential (h : Setting
  config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork}
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (i : ValidatorIndex)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    {wS pS : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, wS⟩)
    (seg : Run config checks ⟨fork, wS⟩ ⟨fork, pS⟩) (rest : Run config checks ⟨fork, pS⟩ ⟨fork, e⟩)
    (valW : Validator) (initialW : wS.validators.data[i.toNat]? = some valW)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd : ℕ)
    (start : effectiveAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    {segEvents : List (BalanceEvent preset)}
    (segOk : seg.balanceEvents (getCurrentEpoch pulled).toNat = .ok segEvents) :
    ∃ D, D + (segEvents.map (penaltyDebit i.toNat)).sum =
        (segEvents.map (floorPenaltyDebit i.toNat)).sum +
          (segEvents.map (floorPartialDebit i)).sum ∧
      (ρd - ρn * ((getCurrentEpoch pS).toNat - (getCurrentEpoch wS).toNat)) *
          (min (actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat)
              (withdrawalMaxEffectiveBalance preset fork valW).toNat +
            preset.downwardBand) ≤
        ρd * (actualBalanceAt (⟨fork, pS⟩ : ForkedBeaconState preset) i.toNat + D +
          preset.downwardBand) + ρn * slack := by
  obtain ⟨toFin⟩ := h.toFin
  have early : (⟨fork, pS⟩ : ForkedBeaconState preset).fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) h.early
  obtain ⟨endEpoch, quotient, positive, -, guards⟩ :=
    segment_guards h near i pre seg rest retained
  exact FloorTrace.run_potential_floor_once (toFin.append pre) seg h.genesis h.caps
    (Internal.Setting.delay h) early
    h.fulu h.bands (getCurrentEpoch pulled).toNat endEpoch i valW initialW
    (fun w found => Internal.unslashed_of_run rest found clean) quotient positive guards segOk slack
      ρn ρd
    start pass

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The potential floor of a segment of C's run for a key that is unslashed at its start.

The key may be slashed at the end of the segment, or at the end of C's run.

The closed form is the one of a slash with the fork's quotient, over one more epoch.

For a key still unslashed at the end, the floor needs no slashing deduction.

The slash form cannot give that one, so the lemmas stay apart. -/
private theorem segment_potential_slash (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork}
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (i : ValidatorIndex)
    {wS pS : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, wS⟩)
    (seg : Run config checks ⟨fork, wS⟩ ⟨fork, pS⟩) (rest : Run config checks ⟨fork, pS⟩ ⟨fork, e⟩)
    (valW : Validator) (initialW : wS.validators.data[i.toNat]? = some valW)
    (unslashed : valW.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd : ℕ)
    (start : effectiveAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, wS⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, pS⟩),
      (before.snoc step).append after = seg → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    {segEvents : List (BalanceEvent preset)}
    (segOk : seg.balanceEvents (getCurrentEpoch pulled).toNat = .ok segEvents) :
    ∃ D, D + (segEvents.map (penaltyDebit i.toNat)).sum =
        (segEvents.map (floorPenaltyDebit i.toNat)).sum +
          (segEvents.map (floorPartialDebit i)).sum ∧
      ((EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) *
          ((ρd - ρn * ((getCurrentEpoch pS).toNat - (getCurrentEpoch wS).toNat + 1)) *
            (min (actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat)
                (withdrawalMaxEffectiveBalance preset fork valW).toNat +
              preset.downwardBand)) ≤
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
          (ρd * (actualBalanceAt (⟨fork, pS⟩ : ForkedBeaconState preset) i.toNat + D +
          preset.downwardBand) + ρn * slack) + ρd * (preset.downwardBand + slack) := by
  obtain ⟨toFin⟩ := h.toFin
  have early : (⟨fork, pS⟩ : ForkedBeaconState preset).fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest.chainSteps) h.early
  obtain ⟨endEpoch, quotient, positive, same, guards⟩ :=
    segment_guards h near i pre seg rest retained
  have two : 2 ≤ quotient := by
    rw [same, Internal.parameters_of_fusaka h.fulu h.early]
    exact h.facts.quotient
  rw [← same]
  exact FloorTrace.run_potential_floor_slash (toFin.append pre) seg h.genesis h.caps
    (Internal.Setting.delay h) early
    h.fulu h.bands (getCurrentEpoch pulled).toNat endEpoch i valW initialW unslashed quotient two
    guards segOk slack ρn ρd start pass

/-- A state between two runs is of the fork of the start.

The end of the runs must not be of a later fork than the start.

A run never moves the fork back. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.fork_eq_of_run {x m y :
  ForkedBeaconState preset} (r1 : Run config checks x m)
    (r2 : Run config checks m y) (back : y.fork ≤ x.fork) : m.fork = x.fork :=
  Fork.ctorIdx_injective (Nat.le_antisymm
    (Nat.le_trans (fork_le_of_chainSteps r2.chainSteps) back) (fork_le_of_chainSteps r1.chainSteps))

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a key at every prefix end of C's run is above `floor`.

The run is C's from the finalized block, and `floor` is below what the potential floor gives.

The potential floor applies at the end of each prefix from the finalized block.

The floor uses the segment's exit guard and a bound on the rate of penalties per pass.

The step `arith` is the arithmetic that fits the closed form of the potential floor to `floor`.

It holds for each epoch count up to C's.

It also holds for each debit that is at most the key's sync and partial debits over the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cfloor_balance (h : Setting config
  checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd floor : ℕ)
    (start : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ evs,
      step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    (arith : ∀ a D k : ℕ,
      k ≤ (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat →
      D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
      (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
          (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
      floor ≤ a) :
    ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, e⟩), r1.append r2 = wholeRun →
      floor ≤ actualBalanceAt p i.toNat := by
  intro p r1 r2 whole
  obtain ⟨pFork, pState⟩ := p
  obtain rfl : fork = pFork := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
  simp only at order
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix r1 r2
    (getCurrentEpoch pulled).toNat events (by rw [whole]; exact replayed)
  obtain ⟨D, split, closed⟩ := Internal.segment_potential h near i clean Run.nil r1 r2 val initial
    (fun before' step after cut' w found => retained before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) w found)
    slack ρn ρd start
    (fun before' step after cut' evs ok => pass before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) evs ok)
    beforeOk
  obtain ⟨rest', rfl⟩ := isPrefix
  have window : (getCurrentEpoch pState).toNat - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat :=
    Nat.sub_le_sub_right order _
  exact arith _ D _ window (prefix_debit_le i before rest' D split) closed

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a key at every prefix end of C's run is above `floor`, less `loss`.

The key is unslashed at the finalized block, and it may be slashed on C's run.

The potential floor includes the loss from slashing.

It is read at the end of each prefix, from the finalized block.

The step `arithS` fits its closed form to `floor`, and `loss` is the slash's share.

If the key stays unslashed, the closed form can use one fewer epoch.

Setting the slashing loss to zero does not recover that sharper epoch bound. -/
private theorem cfloor_balance_slash (h : Setting config checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (unslashed : val.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd floor loss : ℕ)
    (start : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ evs,
      step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    (arithS : ∀ a D k : ℕ,
      k ≤ (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat →
      D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
      ((EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) *
        ((ρd - ρn * (k + 1)) *
          (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat + preset.downwardBand)) ≤
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
          (ρd * (a + D + preset.downwardBand) + ρn * slack) +
          ρd * (preset.downwardBand + slack) →
      floor ≤ a + loss) :
    ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, e⟩), r1.append r2 = wholeRun →
      floor ≤ actualBalanceAt p i.toNat + loss := by
  intro p r1 r2 whole
  obtain ⟨pFork, pState⟩ := p
  obtain rfl : fork = pFork := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
  simp only at order
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix r1 r2
    (getCurrentEpoch pulled).toNat events (by rw [whole]; exact replayed)
  obtain ⟨D, split, closed⟩ := segment_potential_slash h near i Run.nil r1 r2 val initial unslashed
    (fun before' step after cut' w found => retained before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) w found)
    slack ρn ρd start
    (fun before' step after cut' evs ok => pass before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) evs ok)
    beforeOk
  obtain ⟨rest', rfl⟩ := isPrefix
  have window : (getCurrentEpoch pState).toNat - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat :=
    Nat.sub_le_sub_right order _
  exact arithS _ D _ window (prefix_debit_le i before rest' D split) closed

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a prefix end of C's run is the finalized one or an update's.

An update is at a state of the prefix.

There the effective balance is aligned and at most the balance. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cfloor_origin (h : Setting config
  checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
    (r2 : Run config checks p ⟨fork, e⟩) (whole : r1.append r2 = wholeRun) :
    effectiveAt p i.toNat = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ∨
      ∃ (w : ForkedBeaconState preset) (pre : Run config checks ⟨fork, fin⟩ w)
          (post : Run config checks w p),
        pre.append post = r1 ∧ effectiveAt p i.toNat = effectiveAt w i.toNat ∧
          effectiveAt w i.toNat ≤ actualBalanceAt w i.toNat ∧
          effectiveAt w i.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨pFork, pState⟩ := p
  obtain rfl : fork = pFork := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  have early : (⟨fork, pState⟩ : ForkedBeaconState preset).fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  obtain ⟨before, beforeOk, -⟩ := Run.balanceEvents_prefix r1 r2
    (getCurrentEpoch pulled).toNat events (by rw [whole]; exact replayed)
  obtain ⟨endEpoch, quotient, positive, -, guards⟩ := segment_guards h near i
    Run.nil r1 r2 (fun before' step after cut' w found => retained before' step (after.append r2)
      (by rw [Run.append_assoc, cut', whole]) w found)
  exact FloorTrace.run_effective_origin toFin r1 h.genesis h.caps (Internal.Setting.delay h) early
    h.fulu h.aligned
    (getCurrentEpoch pulled).toNat endEpoch i val initial (fun w found => Internal.unslashed_of_run
      r2 found
      clean) quotient positive guards beforeOk

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a state of C's run is above a least value.

The key's balance stays above `floor` at every prefix end.

That value is the least of its effective balance and its cap at the finalized block.

And of `floor` rounded down to an increment. -/
private theorem cfloor_endpoint_of (h : Setting config checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (floor : ℕ)
    (endpointFloor : ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, e⟩), r1.append r2 = wholeRun →
      floor ≤ actualBalanceAt p i.toNat)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, e⟩) (cut : rp.append rest = wholeRun) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt z i.toNat := by
  have forkEnd : ∀ {p : ForkedBeaconState preset} (r2 : Run config checks p ⟨fork, e⟩),
      p.fork < .glamsterdam := fun r2 =>
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  have pathEndpoint : ∀ {p : ForkedBeaconState preset}, p ∈ rp.balancePath →
      ∃ (r1 : Run config checks ⟨fork, fin⟩ p) (r2 : Run config checks p ⟨fork, e⟩),
        r1.append r2 = wholeRun := fun member => by
    obtain ⟨r1, r2, whole⟩ := Internal.balancePath_endpoint rp rest (Nat.le_refl _) member
    exact ⟨r1, r2, whole.trans cut⟩
  have inside : i.toNat < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp initial).1
  refine Internal.Run.effective_floor_rounded rp (forkEnd rest) h.fulu i.toNat inside floor
    (withdrawalMaxEffectiveBalance preset fork val).toNat ?_ ?_
  · intro p member
    obtain ⟨r1, r2, whole⟩ := pathEndpoint member
    exact endpointFloor r1 r2 whole
  · intro p member
    obtain ⟨r1, r2, -⟩ := pathEndpoint member
    obtain ⟨w, found, mono⟩ := r1.validatorCap_mono h.caps.activation h.caps.compounding
      (forkEnd r2) i.toNat val initial
    simpa [PinTerms.capAt, found] using UInt64.le_iff_toNat_le.mp mono

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a state of C's run is above a least value.

The key's actual balance stays at least `floor` at every prefix end.

The effective balance of the key at the end of a prefix is then at least a least value.

That value is the least of its effective balance and its cap at the finalized block.

And of `floor` rounded down to an increment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cfloor_endpoint (h : Setting config
  checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, e.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd floor : ℕ)
    (start : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ evs,
      step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    (arith : ∀ a D k : ℕ,
      k ≤ (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat →
      D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
      (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
          (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
      floor ≤ a)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, e⟩) (cut : rp.append rest = wholeRun) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (floor - floor % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt z i.toNat := by
  exact cfloor_endpoint_of h e wholeRun i val initial floor
    (fun r1 r2 whole => Internal.cfloor_balance h e wholeRun near replayed i val initial clean
      retained
      slack ρn ρd floor start pass arith r1 r2 whole) rp rest cut

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a state of C's run is above a least value, for a slashed key.

The key's actual balance stays at least `floor - loss` at every prefix end.

The effective-balance floor uses that lower value before rounding to an increment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cfloor_endpoint_slash (h : Setting
  config checks g split fin pulled anc counted V)
    (e : BeaconState preset fork) (wholeRun : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : wholeRun.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (unslashed : val.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (slack ρn ρd floor loss : ℕ)
    (start : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
        (preset.downwardBand + slack))
    (pass : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = wholeRun → ∀ evs,
      step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd)
    (arithS : ∀ a D k : ℕ,
      k ≤ (getCurrentEpoch e).toNat - (getCurrentEpoch fin).toNat →
      D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
      ((EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) *
        ((ρd - ρn * (k + 1)) *
          (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat + preset.downwardBand)) ≤
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
          (ρd * (a + D + preset.downwardBand) + ρn * slack) +
          ρd * (preset.downwardBand + slack) →
      floor ≤ a + loss)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, e⟩) (cut : rp.append rest = wholeRun) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          ((floor - loss) - (floor - loss) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt z i.toNat := by
  refine cfloor_endpoint_of h e wholeRun i val initial (floor - loss) (fun r1 r2 whole => ?_)
    rp rest cut
  have := cfloor_balance_slash h e wholeRun near replayed i val initial unslashed retained slack
    ρn ρd floor loss start pass arithS r1 r2 whole
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key's effective balance on C's run is above the floor of its fall.

The run starts at the finalized block, and the bound holds at each state of it.

It is above that floor less the key's sync debits and their band.

The floor starts from the smaller of the key's balance and its cap at the finalized block.

The charge `X` covers leak and gain over the window and due partial withdrawals.

The hypothesis `margin` fits the closed form of the potential floor to the floor of the fall.

The hypothesis `stay` keeps the effective balance at its finalized value if the test holds.

This test applies when the key takes no sync debits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.floorC_at (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (base0 X low finEB floorC : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (hfin : finEB = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    (hfloorC : floorC = if max finEB base0 ≤ low + preset.downwardBand then finEB
      else min finEB (low - low % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC)
    (margin : ∃ slack ρn ρd : ℕ,
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          (preset.downwardBand + slack) ∧
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
        (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
        (before.snoc step).append after = fromFin.append tailC → ∀ evs,
        step.balanceEvents = .ok evs →
        (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd) ∧
      ∀ a D k : ℕ, k ≤ (getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat →
        D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
        (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat +
          preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
        low - (events.map (Internal.syncDebit i.toNat)).sum ≤ a)
    (stay : max finEB base0 ≤ low + preset.downwardBand →
      (events.map (Internal.syncDebit i.toNat)).sum = 0 → finEB ≤ effectiveAt z i.toNat) :
    floorC ≤ effectiveAt z i.toNat + (events.map (Internal.syncDebit i.toNat)).sum +
      Internal.bandR events i.toNat := by
  obtain ⟨slack, ρn, ρd, start, pass, arith⟩ := margin
  have eff := Internal.cfloor_endpoint h counted (fromFin.append tailC) h.near replayed i val
    initial clean
    retained slack ρn ρd
    (low - (events.map (Internal.syncDebit i.toNat)).sum) start pass arith rp rest cut
  have incPos := h.bands.1
  have bandEq := Internal.bandR_eq events i.toNat
  have lowLe : low ≤ (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    have := Nat.min_le_right (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat
    omega
  rw [hfloorC]
  rw [← hfin] at eff
  have lowMod := Nat.mod_lt low incPos
  have lowModLe := Nat.mod_le low preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  rcases Nat.eq_zero_or_pos (events.map (Internal.syncDebit i.toNat)).sum with zero | positive
  · have same : low - (events.map (Internal.syncDebit i.toNat)).sum = low := by omega
    rw [same] at eff
    have noBand : Internal.bandR events i.toNat = 0 := by
      rw [bandEq]
      simp [zero]
    split
    · next test =>
      have kept := stay test zero
      omega
    · omega
  · have mod := Nat.mod_lt (low - (events.map (Internal.syncDebit i.toNat)).sum) incPos
    have band : Internal.bandR events i.toNat =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 := by
      rw [bandEq]
      simp [positive]
    split <;> omega

/-- The floors `q` and `P` of `X` over `a` and `b` satisfy `q * S ≤ P * K`.

This holds if `X * S * b + K * a * b ≤ K * a * X`. -/
private theorem rate_final {X a b q P K S : ℕ} (hq : q * a ≤ X) (hP : X < (P + 1) * b)
    (ha : 0 < a) (hK : 0 < K)
    (key : X * S * b + K * a * b ≤ K * a * X) : q * S ≤ P * K := by
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h] at hP
    · exact h
  have h1 : q * S * (a * b) ≤ X * S * b := by
    calc q * S * (a * b) = (q * a) * (S * b) := by ring
      _ ≤ X * (S * b) := Nat.mul_le_mul_right _ hq
      _ = X * S * b := by ring
  have h2 : K * a * X < K * a * ((P + 1) * b) := by
    rw [Nat.mul_lt_mul_left (Nat.mul_pos hK ha)]
    exact hP
  have h3 : q * S * (a * b) < P * K * (a * b) := by nlinarith [h1, h2, key]
  exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right h3)

/-- Below eighteen increments of the pulled total, a fifth of an increment gives the pin's rate. -/
private theorem rate_small_key {X I a b K S M : ℕ} (hI : 10 ^ 8 ≤ I) (hIX : I ≤ X)
    (hM1 : K * I ≤ M) (hM : I ≤ M) (ha' : M < (a + 1) * (a + 1))
    (hb : b * b ≤ I / 5) (hb' : I / 5 < (b + 1) * (b + 1)) (hK : 1 ≤ K)
    (hS : 2 * S ≤ 3 * K + 2) :
    X * S * b + K * a * b ≤ K * a * X := by
  have hS2 : S ≤ 2 * K := by omega
  have hb5 : 5 * (b * b) ≤ I := by omega
  have hb4472 : 4472 ≤ b := by
    by_contra h
    have : b + 1 ≤ 4472 := by omega
    have : (b + 1) * (b + 1) ≤ 4472 * 4472 := Nat.mul_le_mul this this
    omega
  have ha1e4 : 10 ^ 4 ≤ a := by
    by_contra h
    have : a + 1 ≤ 10 ^ 4 := by omega
    have : (a + 1) * (a + 1) ≤ 10 ^ 4 * 10 ^ 4 := Nat.mul_le_mul this this
    omega
  -- `a² > 4.999 K b²`
  have shift : 10 ^ 4 * (a + 1) ≤ 10001 * a := by omega
  have sq : 10 ^ 4 * (a + 1) * (10 ^ 4 * (a + 1)) ≤ 10001 * a * (10001 * a) :=
    Nat.mul_le_mul shift shift
  have kb : 5 * K * (b * b) ≤ M := by
    have : K * (5 * (b * b)) ≤ K * I := Nat.mul_le_mul_left K hb5
    nlinarith
  have big : 500000000 * K * (b * b) < 100020001 * (a * a) := by nlinarith
  have kb1 : b * b ≤ K * (b * b) := by nlinarith
  have h40 : 40 * b ≤ 19 * a := by
    by_contra h
    have h' : 19 * a < 40 * b := by omega
    have := Nat.mul_self_lt_mul_self h'
    nlinarith
  have h20 : 20 * S * b ≤ 19 * K * a := by
    calc 20 * S * b ≤ 20 * (2 * K) * b := by
          have := Nat.mul_le_mul_right b (Nat.mul_le_mul_left 20 hS2)
          exact this
      _ = K * (40 * b) := by ring
      _ ≤ K * (19 * a) := Nat.mul_le_mul_left K h40
      _ = 19 * K * a := by ring
  have h20b : 20 * b ≤ X := by
    have : 20 * b ≤ b * b := Nat.mul_le_mul_right b (by omega)
    omega
  have e1 : X * (20 * S * b) ≤ X * (19 * K * a) := Nat.mul_le_mul_left X h20
  have e2 : K * a * (20 * b) ≤ K * a * X := Nat.mul_le_mul_left (K * a) h20b
  nlinarith [e1, e2]

/-- Three of the terms that the floors leave are small against `K * a * X`, for a large total. -/
private theorem rate_big_common {X K a : ℕ} (hK : 12 ≤ K) (s2 : 1000 ≤ a) (hX : 2 ^ 35 ≤ X) :
    1000 * (144 * K * X) ≤ 144 * (K * a * X) ∧ 12000 * (96 * X) ≤ 96 * (K * a * X) ∧
      2 ^ 28 * (96 * K * a) ≤ K * a * X := by
  have Ka : 12000 ≤ K * a := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_left (144 * K * X) s2
    linarith
  · have := Nat.mul_le_mul_left (96 * X) Ka
    linarith
  · have h96 : 2 ^ 28 * 96 ≤ X := by omega
    have := Nat.mul_le_mul_left (K * a) h96
    linarith

/-- With at least `2 ^ 20` increments, the terms that the floors leave fit in `13 * K * a * X`. -/
private theorem rate_big_large {X K a : ℕ} (hK : 2 ^ 20 ≤ K) (s2 : 1000 ≤ a) (hX : 2 ^ 35 ≤ X)
    (s3' : 8 * a ≤ X) :
    144 * K * X + 98 * a * X + 96 * X + 98 * K * a * a + 96 * K * a ≤ 13 * K * a * X := by
  obtain ⟨f1, f2, f3⟩ := rate_big_common (K := K) (by omega) s2 hX
  have f4 : 2 ^ 20 * (98 * a * X) ≤ 98 * (K * a * X) := by
    have := Nat.mul_le_mul_right (98 * a * X) hK
    linarith
  have f5 : 8 * (98 * K * a * a) ≤ 98 * K * a * X := by
    have := Nat.mul_le_mul_left (98 * K * a) s3'
    linarith
  have hu : 0 ≤ K * a * X := Nat.zero_le _
  linarith

/-- With fewer than `2 ^ 20` increments, the terms that the floors leave fit in `13 * K * a * X`. -/
private theorem rate_big_small {X K a : ℕ} (hK : 12 ≤ K) (small : K + 1 ≤ 2 ^ 20) (s2 : 1000 ≤ a)
    (hX : 2 ^ 35 ≤ X) (s4 : a * a < (K + 1) * X) :
    144 * K * X + 98 * a * X + 96 * X + 98 * K * a * a + 96 * K * a ≤ 13 * K * a * X := by
  obtain ⟨f1, f2, f3⟩ := rate_big_common hK s2 hX
  have g4 : 12 * (98 * a * X) ≤ 98 * (K * a * X) := by
    have := Nat.mul_le_mul_right (98 * a * X) hK
    linarith
  have g5 : 490 * a ≤ 3 * X := by
    by_contra h
    have h' : 3 * X < 490 * a := by omega
    have h2 := Nat.mul_self_lt_mul_self h'
    have h3 : a * a < 2 ^ 20 * X := by
      have := Nat.mul_le_mul_right X small
      nlinarith
    have h4 : 9 * X * X < 240100 * 2 ^ 20 * X := by nlinarith
    have h5 : 9 * X < 240100 * 2 ^ 20 := by
      exact Nat.lt_of_mul_lt_mul_right h4
    omega
  have g6 : 490 * K * a * a ≤ 3 * K * a * X := by
    have := Nat.mul_le_mul_left (K * a) g5
    linarith
  have hu : 0 ≤ K * a * X := Nat.zero_le _
  linarith

/-- From eighteen increments of the pulled total, a quarter of it gives the pin's rate. -/
private theorem rate_big_key {X I a b K S M T : ℕ} (hX : 2 ^ 35 ≤ X) (hIX : I ≤ X) (hI : 10 ^ 8 ≤ I)
    (hK : 12 ≤ K) (hM1 : K * I ≤ M) (hM2 : M < (K + 1) * I) (ha : a * a ≤ M)
    (ha' : M < (a + 1) * (a + 1)) (hMhi : M < 2 ^ 64) (hb : 4 * (b * b) ≤ T)
    (hT : 2 * T ≤ 3 * M) (hS : 2 * S ≤ 3 * K + 2) :
    X * S * b + K * a * b ≤ K * a * X := by
  have s1 : 80 * b ≤ 49 * a + 48 := by
    by_contra h
    have h1 : 49 * (a + 1) ≤ 80 * b := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  have s2 : 1000 ≤ a := by
    by_contra h
    have h1 : a + 1 ≤ 1000 := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  have s3 : a < 2 ^ 32 := by
    by_contra h
    have h1 : 2 ^ 32 ≤ a := by omega
    have h2 := Nat.mul_le_mul h1 h1
    nlinarith
  have s3' : 8 * a ≤ X := by omega
  have s4 : a * a < (K + 1) * X := by
    have := Nat.mul_le_mul_left (K + 1) hIX
    omega
  have T2 : 144 * K * X + 98 * a * X + 96 * X + 98 * K * a * a + 96 * K * a ≤
      13 * K * a * X := by
    by_cases large : 2 ^ 20 ≤ K
    · exact rate_big_large large s2 hX s3'
    · exact rate_big_small hK (by omega) s2 hX s4
  have e1 : (3 * K + 2) * X * (80 * b) ≤ (3 * K + 2) * X * (49 * a + 48) :=
    Nat.mul_le_mul_left _ s1
  have e2 : 2 * K * a * (80 * b) ≤ 2 * K * a * (49 * a + 48) := Nat.mul_le_mul_left _ s1
  have e3 : 2 * S * (X * b) ≤ (3 * K + 2) * (X * b) := Nat.mul_le_mul_right _ hS
  nlinarith [e1, e2, e3, T2]

/-- The reward per increment at the total, times the previous stake's increments, is bounded.

It is at most the pin's rate times the total's increments. -/
private theorem rate_arith {I c M T S : ℕ} (scale : 2 ^ 35 ≤ I * c) (size : 10 ^ 8 ≤ I)
    (factor : 1 ≤ c)
    (clamp : I ≤ M) (high : M < 2 ^ 64) (band : 2 * T ≤ 3 * M) (stake : 2 * S ≤ 3 * M) :
    I * c / Nat.sqrt M * (S / I) ≤
      I * c / Nat.sqrt (if 18 * I ≤ T then T / 4 else I / 5) * (M / I) := by
  have hI : 0 < I := by omega
  have hIX : I ≤ I * c := Nat.le_mul_of_pos_right I factor
  have hK1 : M / I * I ≤ M := Nat.div_mul_le_self M I
  have hK2 : M < (M / I + 1) * I := by
    have := Nat.lt_mul_div_succ M hI
    rw [Nat.mul_comm] at this
    exact this
  have hK0 : 1 ≤ M / I := (Nat.le_div_iff_mul_le hI).mpr (by omega)
  have hS : 2 * (S / I) ≤ 3 * (M / I) + 2 := by
    have h1 : S / I * I ≤ S := Nat.div_mul_le_self S I
    have h2 : 2 * (S / I) * I < 3 * (M / I + 1) * I := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right h2
    omega
  have ha := Nat.sqrt_le M
  have ha' := Nat.lt_succ_sqrt M
  have apos : 0 < Nat.sqrt M := Nat.sqrt_pos.mpr (by omega)
  by_cases big : 18 * I ≤ T
  · simp only [big, ↓reduceIte]
    have bpos : 0 < Nat.sqrt (T / 4) := Nat.sqrt_pos.mpr (by omega)
    have hb := Nat.sqrt_le (T / 4)
    have hK12 : 12 ≤ M / I := (Nat.le_div_iff_mul_le hI).mpr (by omega)
    refine rate_final (Nat.div_mul_le_self _ _) ?_ apos (by omega)
      (rate_big_key (a := Nat.sqrt M) (b := Nat.sqrt (T / 4)) scale hIX size hK12 hK1 hK2 ha
        ha' high (by omega) band hS)
    exact (Nat.lt_mul_div_succ (I * c) bpos).trans_eq (Nat.mul_comm _ _)
  · simp only [big, ↓reduceIte]
    have bpos : 0 < Nat.sqrt (I / 5) := Nat.sqrt_pos.mpr (by omega)
    have hb := Nat.sqrt_le (I / 5)
    have hb' := Nat.lt_succ_sqrt (I / 5)
    refine rate_final (Nat.div_mul_le_self _ _) ?_ apos (by omega)
      (rate_small_key (a := Nat.sqrt M) (b := Nat.sqrt (I / 5)) size hIX hK1 clamp ha' hb hb'
        hK0 hS)
    exact (Nat.lt_mul_div_succ (I * c) bpos).trans_eq (Nat.mul_comm _ _)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- From Electra and before Gloas, take a state reached from a guarded state in its window.

Its previous epoch's active stake is within three halves of its total. -/
private theorem prevStake_band_of_guard {g x z : ForkedBeaconState preset} {high : ℕ}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (parameters : DirectSafety.Parameters preset) (caps : CapOrder preset)
    (aligned : MaxEffectiveBalancesAligned preset) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (guard : aprioriGuardAt config x high)
    (toZ : Run config checks x z) (zEarly : z.fork < .glamsterdam)
    (zWithin : (getCurrentEpoch z.state).toNat ≤ high + 1) {total : Gwei}
    (totalOk : getTotalActiveBalance z.state = .ok total) :
    2 * ∑ i ∈ (getActiveValidatorIndices z.state (getPreviousEpoch z.state)).toFinset,
        effectiveAt z i.toNat ≤ 3 * total.toNat := by
  have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
  have zero : preElectraEpochs config x high = 0 := by
    simp [preElectraEpochs, notBefore]
  have ratio := Internal.ratio_of_guard electra guard
  obtain ⟨low, -⟩ := Internal.total_within_guard shared genesis parameters caps aligned twoSlots
    electra
    guard toZ zEarly zWithin totalOk
  obtain ⟨-, previous, -⟩ := ceilingFloor_electra shared toZ high
    ⟨genesis, parameters, caps, aligned, zEarly, zWithin, guard⟩ twoSlots electra
  have index : ix x z ≤ high + 1 - (getCurrentEpoch x.state).toNat := by
    simp only [ix]
    omega
  have mono := Internal.stakeCeilingAt_mono (config := config) (x := x) (high := high) electra index
  have anti := Internal.stakeFloorAt_anti (config := config) (x := x) (high := high) index
  simp only [stakeCeilingAt, stakeFloorAt, zero] at low previous mono anti ratio ⊢
  omega

private theorem total_band_of_setting (h : Setting config checks g split fin pulled anc counted V)
    {m : ForkedBeaconState preset} (toM : Run config checks ⟨fork, fin⟩ m)
    (early : m.fork < .glamsterdam)
    (inside : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {total T : Gwei} (totalOk : getTotalActiveBalance m.state = .ok total)
    (pulledOk : getTotalActiveBalance pulled = .ok T) :
    2 * T.toNat ≤ 3 * total.toNat ∧ 2 * total.toNat ≤ 3 * T.toNat := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have toP := fromFin.append toPulled
  exact ⟨Internal.total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
      electra h.guard toM early inside toP h.early (Nat.le_succ _) totalOk pulledOk,
    Internal.total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
      electra h.guard toP h.early (Nat.le_succ _) toM early inside pulledOk totalOk⟩

private theorem quarter_toNat (T : Gwei) :
    ((if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei)).toNat =
      if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T.toNat / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT.toNat / 5 := by
  split <;> simp [UInt64.toNat_div]

/-- The reward per increment at a state of a run from the finalized state is at most the pin's rate.

It is read times the increments active at the previous epoch or at the current one.

The pin's rate is read times the active increments. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.rate_of_guard
    (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {epoch : Epoch} (which : epoch = getPreviousEpoch m ∨ epoch = getCurrentEpoch m)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq) :
    ∀ total perIncrement : Gwei, getTotalActiveBalance m = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat *
          ((∑ i ∈ (getActiveValidatorIndices m epoch).toFinset,
            effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        pq.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  intro total perIncrement totalOk perOk
  obtain ⟨T, pulledOk⟩ := h.pulledTotal
  obtain ⟨shared⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have band := (total_band_of_setting h toM h.early inside totalOk pulledOk).1
  obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
  have stake : 2 * ∑ i ∈ (getActiveValidatorIndices m epoch).toFinset,
      effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat ≤ 3 * total.toNat := by
    rcases which with rfl | rfl
    · exact prevStake_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
        electra h.guard toM h.early inside totalOk
    · have current := le_max_right preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (stake (fun index => balanceAt m index.toNat)
          (getActiveValidatorIndices m (getCurrentEpoch m)).toFinset)
      rw [← value] at current
      exact Nat.le_trans (Nat.mul_le_mul_left 2 current) (Nat.mul_le_mul_right _ (by omega))
  have clamp : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ total.toNat := by
    rw [value]
    exact le_max_left _ _
  have high : total.toNat < 2 ^ 64 := total.toNat_lt
  rw [toNat_getBaseRewardPerIncrement perOk]
  simp only [pulledOk, Except.toOption, Option.getD_some] at pqOk
  rw [toNat_getBaseRewardPerIncrement pqOk, quarter_toNat]
  exact rate_arith h.facts.rewardScale h.facts.incrementSize (Internal.PinPresetFacts.reward
    h.facts) clamp high band stake

/-- Adding `S` to a number loses at most `U` of rounding down to a multiple of `inc`.

That holds if `S` is zero, or if `U` is at least `inc - 1`.

It also holds if `S` is below `inc` and `S + U` reaches `inc`.

A shift below `inc` moves the rounded value by `inc` or by nothing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.round_add_le {inc x S U : ℕ}
  (incPos : 0 < inc)
    (slack : S = 0 ∨ inc ≤ U + 1 ∨ (S < inc ∧ inc ≤ S + U)) :
    x + S - (x + S) % inc ≤ x - x % inc + S + U := by
  have := Nat.mod_lt x incPos
  have := Nat.mod_lt (x + S) incPos
  have := Nat.mod_le x inc
  have := Nat.mod_le (x + S) inc
  rcases slack with z | big | ⟨small, need⟩
  · subst z; simp only [Nat.add_zero]; omega
  · omega
  · have up : (x + S) / inc ≤ x / inc + 1 :=
      (Nat.div_le_div_right (by omega : x + S ≤ x + inc)).trans (Nat.add_div_right x incPos).le
    have := Nat.mul_le_mul_left inc up
    rw [Nat.mul_add, Nat.mul_one] at this
    have := Nat.div_add_mod x inc
    have := Nat.div_add_mod (x + S) inc
    omega

/-- An aligned start within the floor of the balance and the cap is within the rounded ceiling. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.aligned_le_round {inc e a cap c :
  ℕ} (aligned : e % inc = 0) (capped : e ≤ cap)
    (ceiling : min a cap ≤ c) (floorA : e ≤ a - a % inc) : e ≤ c - c % inc := by
  have within : e ≤ c := by
    have : e ≤ a := Nat.le_trans floorA (Nat.sub_le _ _)
    have := Nat.le_min.mpr ⟨this, capped⟩
    omega
  have rounded := rounded_mono inc within
  rw [aligned] at rounded
  simpa using rounded

/-- A floor start is within the rounded top of R's balance and the slack, from the balance ceiling.

The start is aligned and within the floor of its balance and its cap, so it is within the ceiling.

Rounding the ceiling `H + S` down adds at most the slack, and `H` is within `H` and the band. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.short_start_floor {inc e a cap H db
  S U : ℕ} (incPos : 0 < inc)
    (aligned : e % inc = 0) (capped : e ≤ cap) (ceiling : min a cap ≤ H + S)
    (floorA : e ≤ a - a % inc)
    (slack : S = 0 ∨ inc ≤ U + 1 ∨ (S < inc ∧ inc ≤ S + U)) :
    e ≤ (H + db) - (H + db) % inc + S + U := by
  have rounded := Internal.aligned_le_round aligned capped ceiling floorA
  have add := Internal.round_add_le (x := H) incPos slack
  have band := rounded_mono inc (show H ≤ H + db by omega)
  omega

/-- The effective balance of a key that stays on its path is at most the rise of the main regime.

Its `stay` has three cases: it equals R's, it ends at its start, or it is within the ceiling.

In the case where it ends at its start, `start` is within the cap and the rounded top.

The caller proves those two bounds of `start`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.rise_arith {inc band capFor high
  finEB start eR eC Bc capHigh S U : Nat}
    (incPos : 0 < inc)
    (stay : eC = eR ∨
      (eC ≤ start ∧ start ≤ capFor + S + U ∧ start ≤ (high + band) - (high + band) % inc + S + U) ∨
      (eC ≤ Bc + band ∧ eC ≤ max start (min (Bc - Bc % inc) capHigh)))
    (startLe : start ≤ max finEB ((high + S) - (high + S) % inc))
    (aligned : eC % inc = 0) (capped : eC ≤ capFor + S + U) (ceiling : Bc ≤ high + S)
    (slack : S = 0 ∨ inc ≤ U + 1 ∨ (S < inc ∧ inc ≤ S + U)) :
    eC ≤ eR + (min capFor (min (high + band - (high + band) % inc)
      (max finEB (high - high % inc))) - eR) + S + U := by
  rcases stay with same | ⟨atStart, viaCap, viaTop⟩ | ⟨boundary, update⟩
  · omega
  · have b := Internal.round_add_le (x := high) incPos slack
    omega
  · have alignedLe : ∀ x, eC ≤ x → eC ≤ x - x % inc := fun x le => by
      have := rounded_mono inc le
      rw [aligned] at this
      simpa using this
    have first := alignedLe _ (show eC ≤ high + band + S by omega)
    have second : eC ≤ max finEB (high - high % inc) + S + U := by
      have r := rounded_mono inc ceiling
      have b := Internal.round_add_le (x := high) incPos slack
      omega
    have third : eC ≤ high + band - (high + band) % inc + S + U := by
      have b := Internal.round_add_le (x := high + band) incPos slack
      omega
    omega

/-- The effective balance at the end of a run is at most the rounded bound on its balance.

The run starts at a state where the key's effective balance is within the largest one.

The starting balance, epoch rewards and other credits bound the actual balance at every state.

The effective-balance ceiling `E` must cover the rounded bound used to estimate epoch rewards.

Then the update of the effective balances reads that bound as its ceiling. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_credit_ceiling {n y :
  ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P E : ℕ)
    (aligned : preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (capCeil : ∀ z ∈ post.balancePath,
      PinTerms.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (rate : ∀ z ∈ post.balancePath,
      i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) ∨
      ∀ total perIncrement : Gwei,
        getTotalActiveBalance z.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
          (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (fixpoint : max (effectiveAt n i) (min preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      (Internal.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
        Internal.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ E) :
    effectiveAt y i ≤ max (effectiveAt n i) (min
      (Internal.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
        Internal.creditBound post i high E P preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) := by
  obtain ⟨-, -, third, fourth⟩ := Internal.Run.effective_floor_pair post early fulu i inside 0 0
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat high E P
  have balances := fourth aligned startCap capCeil rate endEpoch fixpoint
  exact (third _ aligned startCap
    (fun z member => balances z member) capCeil).1

/-- A cap above the activation balance belongs to a validator with compounding credentials. -/
private theorem compounding_of_cap {z : ForkedBeaconState preset} {i : ℕ}
    (electra : .pectra ≤ z.fork)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt z i) :
    ∃ v, z.state.validators.data[i]? = some v ∧ hasCompoundingWithdrawalCredential v = true := by
  unfold PinTerms.capAt at large
  cases found : z.state.validators.data[i]? with
  | none => simp [found] at large
  | some v =>
    refine ⟨v, rfl, ?_⟩
    by_contra not
    have plain : hasCompoundingWithdrawalCredential v = false := by simpa using not
    simp [found, withdrawalMaxEffectiveBalance, electra, getMaxEffectiveBalance, plain] at large

/-- The cap of a validator is the largest effective balance if it compounds.

Otherwise it is the activation balance. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capAt_of_found {z :
  ForkedBeaconState preset} {i : ℕ} {v : Validator}
    (electra : .pectra ≤ z.fork) (found : z.state.validators.data[i]? = some v) :
    PinTerms.capAt z i = if hasCompoundingWithdrawalCredential v = true then
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat else preset.MIN_ACTIVATION_BALANCE.toNat := by
  unfold PinTerms.capAt
  rw [found]
  by_cases compounds : hasCompoundingWithdrawalCredential v = true <;>
    simp [withdrawalMaxEffectiveBalance, electra, getMaxEffectiveBalance, compounds]

/-- The activation balance and the largest balance are whole numbers of increments. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cap_values_aligned (aligned :
  MaxEffectiveBalancesAligned preset) :
    preset.MIN_ACTIVATION_BALANCE.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
  ⟨by simpa [UInt64.toNat_mod] using congrArg UInt64.toNat aligned.2.1,
    by simpa [UInt64.toNat_mod] using congrArg UInt64.toNat aligned.2.2⟩

/-- A key's cap is a whole number of increments. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capAt_aligned (aligned :
  MaxEffectiveBalancesAligned preset)
    {z : ForkedBeaconState preset} (electra : .pectra ≤ z.fork) {i : ℕ} {w : Validator}
    (found : z.state.validators.data[i]? = some w) :
    PinTerms.capAt z i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  rw [Internal.capAt_of_found electra found]
  have values := Internal.cap_values_aligned aligned
  split <;> first | exact values.1 | exact values.2

/-- From Fusaka, a slot step before Gloas keeps whether each validator of its first state compounds.

It keeps the position of each such validator. -/
private theorem slot_compounding_kept {m n : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks m = .ok n) (fulu : .fusaka ≤ m.fork)
    (early : n.fork < .glamsterdam) {i : ℕ} {v : Validator}
    (found : m.state.validators.data[i]? = some v) :
    ∃ w, n.state.validators.data[i]? = some w ∧
      hasCompoundingWithdrawalCredential w = hasCompoundingWithdrawalCredential v := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
  obtain rfl := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded fulu early
  obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok advancedOk
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  rcases epochIfLast_cases epochedOk with ⟨_, epochOk⟩ | ⟨_, rfl⟩
  · have altair : .altair ≤ m.fork := Nat.le_trans (by decide) fulu
    simp only [processEpoch, altair, ↓reduceDIte] at epochOk
    obtain ⟨later, laterFound, same⟩ := processEpochAltair_credentials epochOk found
    exact ⟨later, laterFound, by unfold hasCompoundingWithdrawalCredential; rw [same]⟩
  · exact ⟨v, found, rfl⟩

/-- A consolidation request keeps whether a validator compounds.

Otherwise it makes the validator compound and leaves its balance within the activation balance. -/
private theorem consolidationRequest_flip {s t : BeaconState preset fork}
    {electra : .pectra ≤ fork} {request : ConsolidationRequest}
    (ok : processConsolidationRequest config s electra request = .ok t)
    {key : ValidatorIndex} {v : Validator} (found : s.validators.data[key.toNat]? = some v) :
    ∃ w, t.validators.data[key.toNat]? = some w ∧
      (hasCompoundingWithdrawalCredential w = hasCompoundingWithdrawalCredential v ∨
        (hasCompoundingWithdrawalCredential w = true ∧
          actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) key.toNat ≤
            preset.MIN_ACTIVATION_BALANCE.toNat)) := by
  obtain ⟨conv, ledger, -⟩ := BlockLedger.ledger_processConsolidationRequest ok
  by_cases member : key ∈ conv
  · obtain ⟨w, located, compounds⟩ := ledger.switched key member
    have capped := ledger.converted key member
    exact ⟨w, located, .inr ⟨compounds, by simpa using capped⟩⟩
  · obtain ⟨w, located, same⟩ := ledger.kept key v member found
    exact ⟨w, located, .inl same⟩

/-- A fold of consolidation requests that each record an excess event.

The balance of a key rises by at most the credits of the events.

The key may switch from plain to compounding credentials in the fold.

Then it ends within the activation balance plus the credits of the events. -/
private theorem excess_fold {electra : .pectra ≤ fork}
    (lim : ConsolidationRequest → BeaconState preset fork → Except TransitionError (ℕ × ℕ))
    (key : ValidatorIndex) :
    ∀ (requests : List ConsolidationRequest) (r rN : BeaconState preset fork)
      (E E' : List (BalanceEvent preset)),
      requests.foldlM (fun pre request => recordBalance .excess (lim request)
        (processConsolidationRequest config · electra request) pre) (r, E) = .ok (rN, E') →
      ∃ Ec : List (BalanceEvent preset), E' = E ++ Ec ∧
        actualBalanceAt (⟨fork, rN⟩ : ForkedBeaconState preset) key.toNat ≤
          actualBalanceAt (⟨fork, r⟩ : ForkedBeaconState preset) key.toNat +
            (Ec.map (Internal.keyCredit key.toNat)).sum ∧
        ∀ v, r.validators.data[key.toNat]? = some v →
          hasCompoundingWithdrawalCredential v = false → ∀ w,
          rN.validators.data[key.toNat]? = some w → hasCompoundingWithdrawalCredential w = true →
            actualBalanceAt (⟨fork, rN⟩ : ForkedBeaconState preset) key.toNat ≤
              preset.MIN_ACTIVATION_BALANCE.toNat + (Ec.map (Internal.keyCredit key.toNat)).sum :=
                by
  intro requests
  induction requests with
  | nil =>
    intro r rN E E' ok
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    refine ⟨[], by simp, by simp, fun v found plain w foundW switched => ?_⟩
    have same := Option.some.inj (found.symm.trans foundW)
    subst same
    exact absurd (switched.symm.trans plain) (by decide)
  | cons request rest ih =>
    intro r rN E E' ok
    rw [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨⟨after, recorded⟩, step, others⟩ := ok
    obtain ⟨credit, debit, -, actionOk, rfl⟩ :=
      DirectSafety.Apriori.Internal.recordBalance_single step
    obtain ⟨Ec, rfl, rise, later⟩ := ih after rN _ E' others
    refine ⟨⟨.excess, ⟨fork, r⟩, ⟨fork, after⟩, credit, debit⟩ :: Ec, by simp, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, Internal.keyCredit]
      omega
    · intro v found plain w foundW switched
      obtain ⟨v', found', changed⟩ := consolidationRequest_flip actionOk found
      rcases changed with same | ⟨_, capped⟩
      · have bound := later v' found' (same.trans plain) w foundW switched
        simp only [List.map_cons, List.sum_cons, Internal.keyCredit]
        omega
      · simp only [List.map_cons, List.sum_cons, Internal.keyCredit]
        omega

/-- Whether each validator compounds is the same at two states. -/
private def CompKept {f : Fork} (s t : BeaconState preset f) : Prop :=
  ∀ (v : ValidatorIndex) (validator : Validator), s.validators.data[v.toNat]? = some validator →
    ∃ later, t.validators.data[v.toNat]? = some later ∧
      hasCompoundingWithdrawalCredential later = hasCompoundingWithdrawalCredential validator

/-- Compounding is kept across two steps when each step keeps it. -/
private theorem CompKept.trans {f : Fork} {s u t : BeaconState preset f} (one : CompKept s u)
    (two : CompKept u t) : CompKept s t := fun v validator located => by
  obtain ⟨middle, middleFound, same⟩ := one v validator located
  obtain ⟨later, laterFound, same'⟩ := two v middle middleFound
  exact ⟨later, laterFound, same'.trans same⟩

/-- A block ledger with no credited keys keeps compounding. -/
private theorem CompKept.of_ledger {f : Fork} {s t : BeaconState preset f}
    {paid : Finset ValidatorIndex} {sync other slash : ValidatorIndex → ℕ}
    (ledger : BlockLedger.Ledger s t paid ∅ sync other slash) : CompKept s t :=
  fun v validator located => ledger.kept v validator (Finset.notMem_empty v) located

/-- From Fulu and before Gloas, a block's replay leaves a switched key within activation balance.

The key switches by a consolidation request.

The events after the switch then add their credits. -/
private theorem block_flip_balance {engine : ExecutionEngine preset fork}
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    {events : List (BalanceEvent preset)} (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (matched : BalancesMatch s)
    (replayed : blockBalanceReplay (config := config) (checks := checks) early engine s block =
      .ok (t, events))
    (key : ValidatorIndex) {v w : Validator} (found : s.validators.data[key.toNat]? = some v)
    (plain : hasCompoundingWithdrawalCredential v = false)
    (foundT : t.validators.data[key.toNat]? = some w)
    (switched : hasCompoundingWithdrawalCredential w = true) :
    actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) key.toNat ≤
      preset.MIN_ACTIVATION_BALANCE.toNat + (events.map (Internal.keyCredit key.toNat)).sum := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) fulu
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) fulu
  unfold blockBalanceReplay at replayed
  dsimp only at replayed
  obtain ⟨⟨u1, E1⟩, h1, replayed⟩ := bind_ok_iff.mp replayed
  rw [dite_eq_left_of_eq_true (eq_true bellatrix)] at replayed
  obtain ⟨⟨u2, E2⟩, h2, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u3, E3⟩, h3, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u4, E4⟩, h4, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨_, -, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨_, -, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p5, h5, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p6, h6, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p7, h7, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨p8, h8, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u9, E9⟩, h9, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u10, E10⟩, h10, replayed⟩ := bind_ok_iff.mp replayed
  rw [dite_eq_left_of_eq_true (eq_true electra)] at replayed
  obtain ⟨⟨u11, E11⟩, h11, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨u12, E12⟩, h12, replayed⟩ := bind_ok_iff.mp replayed
  obtain ⟨⟨rN, E13⟩, hfold, replayed⟩ := bind_ok_iff.mp replayed
  rw [dite_eq_left_of_eq_true (eq_true altair)] at replayed
  -- The states before the consolidation requests.
  obtain ⟨hu1, -⟩ := Internal.carryBalance_cases h1
  obtain ⟨_, _, -, hu2, -⟩ := DirectSafety.Apriori.Internal.recordBalance_single h2
  obtain ⟨hu3, -⟩ := Internal.carryBalance_cases h3
  obtain ⟨hu4, -⟩ := Internal.carryBalance_cases h4
  have f5 := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ h5
  have f6 := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ h6
  have f7 := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ h7
  have f8 := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ h8
  obtain ⟨hu9, -⟩ := Internal.carryBalance_cases h9
  obtain ⟨hu10, -⟩ := Internal.carryBalance_cases h10
  obtain ⟨hu11, -⟩ := Internal.carryBalance_cases h11
  obtain ⟨hu12, -⟩ := Internal.carryBalance_cases h12
  have matchedInput : BalancesMatch u4 :=
    ((frame_processBlockHeader hu1).toFrame.trans
      ((frame_processBlockExecution hu2).toFrame.trans
        ((frame_processRandao hu3).toFrame.trans
          (frame_processEth1Data hu4).toFrame))).balancesMatch matched
  obtain ⟨_, executed, -⟩ := BlockLedger.ledger_processBlockExecution early hu2
  have toInput : CompKept s u4 :=
    (CompKept.of_ledger (BlockLedger.ledger_processBlockHeader hu1)).trans <|
      (CompKept.of_ledger executed).trans <|
        (CompKept.of_ledger (BlockLedger.ledger_processRandao hu3)).trans
          (CompKept.of_ledger (BlockLedger.ledger_processEth1Data hu4))
  have toRequests : CompKept u4 u12 := BlockCredits.compoundingKept_beforeConsolidations
    early fulu electra matchedInput f5 f6 f7 f8 (by rw [Array.foldlM_toList]; exact hu9) hu10
    (by rw [Array.foldlM_toList]; exact hu11) (by rw [Array.foldlM_toList]; exact hu12)
  obtain ⟨v0, found0, same0⟩ := (toInput.trans toRequests) key v found
  -- The consolidation requests, then the sync aggregate.
  obtain ⟨Ec, rfl, -, switchedBound⟩ := excess_fold (electra := electra) _ key _ _ _ _ _ hfold
  obtain ⟨_, _, -, hu, rfl⟩ := DirectSafety.Apriori.Internal.recordBalance_single replayed
  have kept := (BlockLedger.processSyncAggregate_kept hu).1
  rw [kept] at foundT
  have bound := switchedBound v0 found0 (same0.trans plain) w foundT switched
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Internal.keyCredit]
  omega

/-- A step that makes a registered key compound is not a slot step.

A slot step keeps whether each validator of its first state compounds. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_flip_not_slot {m n :
  ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork)
    (i : ℕ) (inside : i < m.state.validators.data.size)
    (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt n i) :
    ∀ ok : advanceSlotAcross config checks m = .ok n, step ≠ Step.slot ok := by
  intro ok same
  subst same
  have electraM : .pectra ≤ m.fork := Nat.le_trans (by decide) fulu
  have electraN : .pectra ≤ n.fork := Nat.le_trans electraM (Step.slot ok).chainStep.fork_le
  obtain ⟨v, found⟩ : ∃ v, m.state.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨w, foundN, switched⟩ := compounding_of_cap electraN large
  have strict : preset.MIN_ACTIVATION_BALANCE.toNat <
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
    have large' := large
    rw [Internal.capAt_of_found electraN foundN, switched] at large'
    simpa using large'
  have plain : hasCompoundingWithdrawalCredential v = false := by
    by_contra compounds
    have yes : hasCompoundingWithdrawalCredential v = true := by simpa using compounds
    rw [Internal.capAt_of_found electraM found, yes] at flat
    simp at flat
    omega
  obtain ⟨w', found', same⟩ := slot_compounding_kept ok fulu early found
  have equal := Option.some.inj (found'.symm.trans foundN)
  subst equal
  simp [switched, plain] at same

/-- A step makes a key compound.

It leaves the balance of the key within the activation balance plus the credits of the step. -/
private theorem step_flip_balance {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork) (invariant : Invariant m.state)
    (i : ℕ) (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt n i) :
    actualBalanceAt n i ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
      Internal.stepCredit (fun _ => true) (fun _ => true) i step := by
  obtain ⟨events, replayed⟩ := step.balanceEvents_ok early
  have base := Internal.step_balance_le_events step early i replayed
  have credit : Internal.stepCredit (fun _ => true) (fun _ => true) i step =
      (events.map (Internal.keyCredit i)).sum := by
    cases step <;> simp [Internal.stepCredit, replayed, Except.toOption]
  rw [credit]
  cases found : m.state.validators.data[i]? with
  | none =>
    have out := Array.getElem?_eq_none_iff.mp found
    have sizes := invariant.balancesMatch
    unfold BalancesMatch at sizes
    have zero : actualBalanceAt m i = 0 := by
      simp [actualBalanceAt,
        Array.getElem?_eq_none (show m.state.balances.data.size ≤ i by omega)]
    omega
  | some v =>
    cases step with
    | slot ok =>
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      exact absurd rfl (Internal.step_flip_not_slot (Step.slot ok) early fulu i inside flat large
        ok)
    | @block f s t engine signed due ok =>
      have electra : .pectra ≤ f := Nat.le_trans (by decide) fulu
      obtain ⟨w, foundN, switched⟩ := compounding_of_cap electra large
      have strict : preset.MIN_ACTIVATION_BALANCE.toNat <
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
        rw [Internal.capAt_of_found electra foundN, switched] at large
        simpa using large
      have plain : hasCompoundingWithdrawalCredential v = false := by
        by_contra compounds
        have yes : hasCompoundingWithdrawalCredential v = true := by simpa using compounds
        rw [Internal.capAt_of_found electra found, yes] at flat
        simp at flat
        omega
      have replay := Step.balanceEvents_block (fork := f) early replayed
      have inside : i < s.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
      have bound := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam early s)
      obtain ⟨key, hkey⟩ : ∃ key : ValidatorIndex, key.toNat = i :=
        ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' bound⟩
      subst hkey
      exact block_flip_balance (fork := f) early fulu invariant.balancesMatch replay key found
        plain foundN switched

/-- A step that makes a key compound leaves its balance within the smaller of two bounds.

Those are its balance before the step and the activation balance, each plus the credits of the step.

Both bounds add the same credits, so the smaller of the two bases carries them. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_flip_min {m n :
  ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork) (invariant : Invariant m.state)
    (i : ℕ) (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt n i) :
    actualBalanceAt n i ≤ min (actualBalanceAt m i) preset.MIN_ACTIVATION_BALANCE.toNat +
      Internal.stepCredit (fun _ => true) (fun _ => true) i step := by
  obtain ⟨events, replayed⟩ := step.balanceEvents_ok early
  have base := Internal.step_balance_le_events step early i replayed
  have credit : Internal.stepCredit (fun _ => true) (fun _ => true) i step =
      (events.map (Internal.keyCredit i)).sum := by
    cases step <;> simp [Internal.stepCredit, replayed, Except.toOption]
  have flip := step_flip_balance step early fulu invariant i flat large
  rw [credit] at flip ⊢
  omega

/-- A step that makes a registered key compound stays in its epoch.

It is a block step, and a block keeps the slot. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_flip_epoch {m n :
  ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork)
    (i : ℕ) (inside : i < m.state.validators.data.size)
    (flat : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt m i)
    (large : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt n i) :
    (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat := by
  cases step with
  | slot ok =>
    exact absurd rfl (Internal.step_flip_not_slot (Step.slot ok) early fulu i inside flat large ok)
  | @block f s t engine signed due ok =>
    obtain ⟨-, processed, -⟩ := applySignedBlock_ok ok
    have slot := (frame_processBlock processed).slot
    simp only [getCurrentEpoch, slot]

/-- A run from a key with plain credentials to a key with compounding credentials splits at a step.

The step makes the key compound.

It leaves the balance of the key within the activation balance plus the credits of the step.

If the key is in the registry of the first state, the step does not cross an epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.Run.flip_split {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork) (invariant : Invariant x.state)
    (i : ℕ) (flat : PinTerms.capAt x i ≤ preset.MIN_ACTIVATION_BALANCE.toNat)
    (compounding : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt y i) :
    ∃ (m n : ForkedBeaconState preset) (pre : Run config checks x m) (step : Step config checks m n)
      (post : Run config checks n y),
      (pre.snoc step).append post = tail ∧
      PinTerms.capAt m i ≤ preset.MIN_ACTIVATION_BALANCE.toNat ∧
      preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt n i ∧
      actualBalanceAt n i ≤ preset.MIN_ACTIVATION_BALANCE.toNat +
        Internal.stepCredit (fun _ => true) (fun _ => true) i step ∧
      (i < x.state.validators.data.size →
        (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat) := by
  obtain ⟨m, n, pre, step, post, split, notYet, arrived⟩ := Run.split_at_flip tail
    (fun z => preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt z i)
    (show ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt x i by omega) compounding
  have before : ¬preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt m i := notYet
  have after : preset.MIN_ACTIVATION_BALANCE.toNat < PinTerms.capAt n i := arrived
  have fuluM : .fusaka ≤ m.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
  have earlyN : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  exact ⟨m, n, pre, step, post, split.symm, Nat.le_of_not_lt before, after,
    step_flip_balance step earlyN fuluM (Run.invariant invariant pre) i before after,
    fun inside => Internal.step_flip_epoch step earlyN fuluM i
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)) before after⟩

/-- The penalty rate of a rewards pass at a state of a run from the finalized state is bounded.

It is at most the pin's leak rate at the key's effective balance there. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.passRate_le_leakAt (h : Setting
  config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork} (toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩)
    (inside : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {total : Gwei} (totalOk : getTotalActiveBalance m = .ok total)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq) (v : ℕ) :
    Internal.passPenaltyRate config (⟨fork, m⟩ : ForkedBeaconState preset) v ≤
      (pinTerms config pulled anc fin).leakAt (effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) v)
        v := by
  obtain ⟨T, pulledOk⟩ := h.pulledTotal
  obtain ⟨shared⟩ := h.toFin
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have aligned : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣
      effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) v :=
    Nat.dvd_of_mod_eq_zero
      (DirectSafety.Apriori.Internal.FloorTrace.effective_aligned (shared.append toM) h.genesis
        h.aligned v)
  have bandTotal := (total_band_of_setting h toM h.early inside totalOk pulledOk).1
  have band : 2 * T.toNat ≤ 3 * activeBalanceTotal m := by
    rw [← getTotalActiveBalance_toNat totalOk]
    exact bandTotal
  have fromFinEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toM.chainSteps)
  simp only at fromFinEpoch
  have scored : (if altair : .altair ≤ fork then
        (((m.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      config.INACTIVITY_SCORE_BIAS.toNat ≤
      (if altair : .altair ≤ fork then
        (((fin.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        config.INACTIVITY_SCORE_BIAS.toNat := by
    simp only [altair, ↓reduceDIte]
    have depth : (getCurrentEpoch m).toNat - (getCurrentEpoch fin).toNat + 1 ≤
        (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
    have times := Nat.mul_le_mul_right config.INACTIVITY_SCORE_BIAS.toNat depth
    cases read : (m.inactivityScores altair).data[v]? with
    | none =>
      simp only [Option.map_none, Option.getD_none, Nat.zero_add]
      refine le_trans ?_ (Nat.le_add_left _ _)
      rw [Nat.add_mul, Nat.one_mul] at times
      omega
    | some score =>
      have grown := DirectSafety.Apriori.Internal.runScore_le_start toM altair h.early
        (.inl electra) altair (i := v) read
      simp only [Option.map_some, Option.getD_some]
      rw [Nat.add_mul, Nat.one_mul] at times
      simp only at grown
      rw [Nat.mul_comm (_ - _)] at times
      nlinarith
  have key := Internal.passPenaltyRate_le_leak (config := config)
    (⟨fork, m⟩ : ForkedBeaconState preset) v T.toNat _ h.facts T.toNat_lt aligned band scored
  dsimp only at key
  refine Nat.le_trans key ?_
  simp only [pinTerms]
  have totalRead : (getTotalActiveBalance pulled).toOption.getD 0 = T := by
    rw [pulledOk]
    rfl
  rw [totalRead] at pqOk ⊢
  rw [pqOk]
  simp only [Except.toOption, Option.getD_some]
  have perIncrement := toNat_getBaseRewardPerIncrement pqOk
  rw [quarter_toNat] at perIncrement
  refine Nat.le_of_eq ?_
  rw [perIncrement]

/-- The reserve counts only validators in R's registry as pending keys.

Each is not yet eligible at R's epoch, and has no activation epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.pendingRB_iff (config : Config)
  (pulled anc fin : BeaconState preset fork)
    (i : ℕ) : (pinTerms config pulled anc fin).pendingRB i = true ↔
      ∃ w, pulled.validators.data[i]? = some w ∧
        (getCurrentEpoch pulled).toNat < w.activationEligibilityEpoch.toNat ∧
        w.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [pinTerms]
  cases pulled.validators.data[i]? <;> simp

/-- The reserve counts only validators in R's registry as late keys.

Each has an eligibility epoch by R's epoch.

Its activation epoch is beyond the seed lookahead of the finalized epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.lateB_iff (config : Config) (pulled
  anc fin : BeaconState preset fork) (i : ℕ) :
    (pinTerms config pulled anc fin).lateB i = true ↔ ∃ w, pulled.validators.data[i]? = some w ∧
      w.activationEligibilityEpoch.toNat ≤ (getCurrentEpoch pulled).toNat ∧
      anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
        w.activationEpoch.toNat := by
  simp only [pinTerms]
  cases pulled.validators.data[i]? <;> simp

/-- The reserve reads scheduled exits from validators in R's registry.

Each is active in R's previous epoch or its current one, and unslashed or recently slashed.

Its exit epoch is at most one after R's epoch. -/
private theorem exitingB_iff (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) : (pinTerms config pulled anc fin).exitingB i = true ↔
      ∃ w, pulled.validators.data[i]? = some w ∧
        (isActiveAt pulled (getPreviousEpoch pulled) i = true ∨
          isActiveAt pulled (getCurrentEpoch pulled) i = true) ∧
        (w.slashed = false ∨ anc.finalizedCheckpoint.epoch.toNat +
          preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ w.withdrawableEpoch.toNat) ∧
        w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
  simp only [pinTerms]
  rcases Option.eq_none_or_eq_some (pulled.validators.data[i]?) with none | ⟨w, some⟩
  · simp [none]
  · simp [some]

/-- The reserve counts past exits from validators in R's registry.

The earliest exit it counts is one epoch plus the seed lookahead after the finalized epoch.

Each exit epoch is strictly before R's epoch. -/
private theorem exitedRB_iff (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) : (pinTerms config pulled anc fin).exitedRB i = true ↔
      ∃ w, pulled.validators.data[i]? = some w ∧
        anc.finalizedCheckpoint.epoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤
          w.exitEpoch.toNat ∧ w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch pulled).toNat := by
  simp only [pinTerms]
  cases pulled.validators.data[i]? <;> simp

/-- The finalized epoch of R is at most its current epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.finalized_le_current {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    pulled.finalizedCheckpoint.epoch ≤ getCurrentEpoch pulled := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have valid := Run.invariant (Genesis.invariant h.genesis) ((rf.append rs).append rp)
  exact UInt64.le_trans valid.ordered.1 (UInt64.le_trans valid.ordered.2
    (UInt64.le_trans valid.settled (getPreviousEpoch_le pulled)))

/-- The epochs of the setting, as natural numbers, in the order of its runs.

The finalized epoch of the ancestor is at most the split's, which is at most R's.

C's epoch is R's or the next, and the epoch after R's is below the far future. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.setting_epochs {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    anc.finalizedCheckpoint.epoch.toNat ≤ (getCurrentEpoch split).toNat ∧
      (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat ∧
      (getCurrentEpoch pulled).toNat ≤ (getCurrentEpoch counted).toNat ∧
      (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1 ∧
      (getCurrentEpoch pulled).toNat + 1 < FAR_FUTURE_EPOCH.toNat ∧
      FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 ∧
      (getCurrentEpoch pulled + 1).toNat = (getCurrentEpoch pulled).toNat + 1 ∧
      pulled.finalizedCheckpoint.epoch.toNat ≤ (getCurrentEpoch pulled).toNat := by
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  refine ⟨UInt64.le_iff_toNat_le.mp h.finalized, UInt64.le_iff_toNat_le.mp (Internal.Setting.called
    h),
    UInt64.le_iff_toNat_le.mp h.later, h.near, below, farNat, ?_,
    UInt64.le_iff_toNat_le.mp (Internal.finalized_le_current h)⟩
  have one : (1 : UInt64).toNat = 1 := rfl
  rw [UInt64.toNat_add, one]
  exact Nat.mod_eq_of_lt (by omega)

/-- A key of `K6` in R's registry has no exit, or an exit after the split's lookahead.

An exit at or before the split's epoch plus the seed lookahead is on the shared prefix of the runs.

Both runs then agree on the key's activity up to that exit, so C would not count the key.

The records of the key at R and at C, and what they say of its activity, are the premises. -/
private theorem K6_exit_late {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) {v : ValidatorIndex}
    {w u : Validator} (found : pulled.validators.data[v.toNat]? = some w)
    (rActive : ∀ e : Epoch, isActiveAt pulled e v.toNat = true ↔
      (w.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < w.exitEpoch.toNat))
    (cActive : ∀ e : Epoch, isActiveAt counted e v.toNat = true ↔
      (u.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < u.exitEpoch.toNat))
    (uExit : (getCurrentEpoch counted).toNat < u.exitEpoch.toNat)
    (notActive : ¬ (w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat ∧
      (getCurrentEpoch pulled).toNat < w.exitEpoch.toNat)) :
    w.exitEpoch = FAR_FUTURE_EPOCH ∨
      (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat < w.exitEpoch.toNat := by
  by_cases far : w.exitEpoch = FAR_FUTURE_EPOCH
  · exact .inl far
  refine .inr ?_
  by_contra early
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have gap := Run.exit_activation_gap ((rf.append rs).append rp) h.genesis v.toNat w found far
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have later := UInt64.le_iff_toNat_le.mp h.later
  have shareA := Internal.activity_shared h (e := w.activationEpoch) (by omega) v.toNat
  have shareX := Internal.activity_shared h (e := w.exitEpoch) (by omega) v.toNat
  have activeA : isActiveAt pulled w.activationEpoch v.toNat = true :=
    (rActive _).mpr ⟨Nat.le_refl _, by omega⟩
  have atA := (cActive _).mp (shareA.symm.trans activeA)
  have notX : ¬ isActiveAt counted w.exitEpoch v.toNat = true := by
    rw [← shareX]
    intro active
    have := (rActive _).mp active
    omega
  have ended := mt (cActive w.exitEpoch).mpr notX
  omega

/-- A key of the split's registry that R has withdrawable by the finalized epoch is not charged.

The charge would be on C's tail.

Its exit is at most its withdrawable epoch, so R's exit is assigned by the finalized epoch.

An exit assigned after the split is at least the split's epoch plus one and the seed lookahead.

So the split already holds the exit, and a run never charges an exit twice. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.no_charge_of_settled {g :
  ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {i : ℕ} {w : Validator}
    (inside : i < split.validators.data.size) (found : pulled.validators.data[i]? = some w)
    (settled : w.withdrawableEpoch.toNat ≤ anc.finalizedCheckpoint.epoch.toNat) :
    ∀ c ∈ tailC.departureCharges, c.index ≠ i := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have valid := Run.invariant (Genesis.invariant h.genesis) ((rf.append rs).append rp)
  have ordered := UInt64.le_iff_toNat_le.mp
    (valid.exitsOrdered w (Array.mem_of_getElem? found))
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots split
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have oldFound := Array.getElem?_eq_getElem inside
  have assigned : split.validators.data[i].exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro unset
    have wAssigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      rw [far, farNat] at ordered
      omega
    obtain ⟨c, member, -, epoch⟩ := rp.departure_charge_of_assigned i _ w oldFound found unset
      wAssigned
    have late : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
      DirectSafety.Run.departureCharges_epoch_ge_start rp (Nat.le_trans (by decide) h.fulu)
        h.early c member
    omega
  intro c member
  exact tailC.departure_charge_ne_of_assigned i _ oldFound assigned c member

/-- A deep key of R's registry that activates after R's next epoch is late or pending.

It is deep when the seed lookahead past the finalized epoch is before R's next epoch.

Without an activation epoch it is pending, if it is not yet eligible, and otherwise late.

With one, its eligibility is by the finalized epoch, which the seed lookahead precedes. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.late_or_pending (h : Setting config
  checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (found : pulled.validators.data[i]? = some w)
    (deep : anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
      (getCurrentEpoch pulled).toNat + 1)
    (after : (getCurrentEpoch pulled).toNat + 1 < w.activationEpoch.toNat) :
    (pinTerms config pulled anc fin).lateB i = true ∨
      (pinTerms config pulled anc fin).pendingRB i = true := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  by_cases far : w.activationEpoch = FAR_FUTURE_EPOCH
  · by_cases elig : (getCurrentEpoch pulled).toNat < w.activationEligibilityEpoch.toNat
    · exact .inr ((Internal.pendingRB_iff config pulled anc fin i).mpr ⟨w, found, elig, far⟩)
    · refine .inl ((Internal.lateB_iff config pulled anc fin i).mpr ⟨w, found, by omega, ?_⟩)
      rw [far, farNat]
      omega
  · have eligible := Run.eligibility_le_finalized ((rf.append rs).append rp) h.genesis i w found far
    have eligNat : w.activationEligibilityEpoch.toNat ≤ pulled.finalizedCheckpoint.epoch.toNat :=
      UInt64.le_iff_toNat_le.mp eligible
    have finCur := UInt64.le_iff_toNat_le.mp (Internal.finalized_le_current h)
    exact .inl ((Internal.lateB_iff config pulled anc fin i).mpr ⟨w, found, by omega, by omega⟩)

/-- A key counted in C and inactive at R, read at R's record, is in one of five classes.

It joins at R's next epoch.

Or it activates late, has exited at R, is exiting at R, or is not yet eligible at R. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K6_class {g : ForkedBeaconState
  preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) {v : ValidatorIndex}
    (member : v ∈ Internal.K6 pulled counted) {w : Validator}
    (found : pulled.validators.data[v.toNat]? = some w) :
    (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true) ∨
      (pinTerms config pulled anc fin).lateB v.toNat = true ∨
      (pinTerms config pulled anc fin).exitedRB v.toNat = true ∨
      (pinTerms config pulled anc fin).exitingB v.toNat = true ∨
      (pinTerms config pulled anc fin).pendingRB v.toNat = true := by
  classical
  obtain ⟨memberAC, memberQ, notAR⟩ := Finset.mem_filter.mp member
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨rc⟩ := h.toCounted
  have chain := (rf.append rs).append rp
  -- Epochs, as natural numbers.
  obtain ⟨finSplit, called, later, near, below, farNat, succNat, finCur⟩ := Internal.setting_epochs
    h
  -- The records of the key at R and at C, and the activity they give.
  obtain ⟨u, foundU, activeU⟩ := Internal.active_of_activeVoters h.early memberAC
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeU
  have uAct := UInt64.le_iff_toNat_le.mp activeU.1
  have uExit := UInt64.lt_iff_toNat_lt.mp activeU.2
  have uUnslashed : u.slashed = false := by
    have := (Finset.mem_filter.mp memberQ).2
    simpa [foundU] using this
  have rActive : ∀ e : Epoch, isActiveAt pulled e v.toNat = true ↔
      (w.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < w.exitEpoch.toNat) := by
    intro e
    simp [isActiveAt, found, isActiveValidator, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  have cActive : ∀ e : Epoch, isActiveAt counted e v.toNat = true ↔
      (u.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < u.exitEpoch.toNat) := by
    intro e
    simp [isActiveAt, foundU, isActiveValidator, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  have notActive : ¬ (w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat ∧
      (getCurrentEpoch pulled).toNat < w.exitEpoch.toNat) := by
    intro both
    apply notAR
    simpa [Internal.AR, activeVoters] using
      mem_getActiveValidatorIndices_of_isActiveAt ((rActive _).mpr both)
  -- The key joins at R's next epoch.
  have joins : w.activationEpoch.toNat = (getCurrentEpoch pulled).toNat + 1 →
      (w.exitEpoch = FAR_FUTURE_EPOCH ∨
        w.activationEpoch.toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ w.exitEpoch.toNat) →
      isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
        isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true := by
    intro first gap
    refine ⟨Bool.eq_false_iff.mpr fun active => ?_, (rActive _).mpr ⟨by omega, ?_⟩⟩
    · have := (rActive _).mp active
      omega
    · rcases gap with far | gap
      · rw [succNat, far, farNat]
        omega
      · rw [succNat]
        omega
  by_cases hA : (getCurrentEpoch pulled).toNat < w.activationEpoch.toNat
  · -- Not activated at R's epoch.
    by_cases window : (getCurrentEpoch counted).toNat ≤
        (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat
    · -- The key's activity at C's epoch is shared, so R activates it by then.
      have shared := Internal.activity_shared h (e := getCurrentEpoch counted) window v.toNat
      have activeAtC : isActiveAt counted (getCurrentEpoch counted) v.toNat = true :=
        (cActive _).mpr ⟨uAct, uExit⟩
      have atR := (rActive _).mp (shared.trans activeAtC)
      left
      refine joins (by omega) ?_
      by_cases far : w.exitEpoch = FAR_FUTURE_EPOCH
      · exact .inl far
      · exact .inr (Run.exit_activation_gap chain h.genesis v.toNat w found far)
    · -- Beyond the shared window, the finalized epoch is before R's epoch.
      by_cases first : w.activationEpoch.toNat = (getCurrentEpoch pulled).toNat + 1
      · left
        refine joins first ?_
        by_cases farExit : w.exitEpoch = FAR_FUTURE_EPOCH
        · exact .inl farExit
        · exact .inr (Run.exit_activation_gap chain h.genesis v.toNat w found farExit)
      · rcases Internal.late_or_pending h found (by omega) (by omega) with late | pending
        · exact .inr (.inl late)
        · exact .inr (.inr (.inr (.inr pending)))
  · -- Exited at R's epoch or before.
    have exited : w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by omega
    have exitNear : w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
      intro far
      rw [far, farNat] at exited
      omega
    have gap := Run.exit_activation_gap chain h.genesis v.toNat w found exitNear
    have afterFin : anc.finalizedCheckpoint.epoch.toNat + 1 +
        preset.MAX_SEED_LOOKAHEAD.toNat ≤ w.exitEpoch.toNat := by
      rcases K6_exit_late h found rActive cActive uExit notActive with far | late
      · exact absurd far exitNear
      · omega
    by_cases settled : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch pulled).toNat
    · exact .inr (.inr (.inl ((exitedRB_iff config pulled anc fin v.toNat).mpr
        ⟨w, found, afterFin, settled⟩)))
    · -- The exit is at R's epoch.
      refine .inr (.inr (.inr (.inl ((exitingB_iff config pulled anc fin v.toNat).mpr
        ⟨w, found, .inl ((rActive _).mpr ⟨?_, ?_⟩), ?_, by omega⟩))))
      · rw [getPreviousEpoch_toNat]
        omega
      · rw [getPreviousEpoch_toNat]
        omega
      · by_cases unslashed : w.slashed = false
        · exact .inl unslashed
        · right
          have slashed : w.slashed = true := by simpa using unslashed
          have delayed := Internal.slashed_waits (rf.append rs) h.genesis rp rc h.early h.caps
            (Internal.Setting.delay h)
            found slashed (by simp [foundU, uUnslashed])
          omega

/-- The reserve charges the rise of keys that join at R's next epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.joinRise_eq (config : Config)
  (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).joinRise =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (isActiveAt pulled (getCurrentEpoch pulled) i = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) i = true),
            (pinTerms config pulled anc fin).rise i := rfl

/-- The window is tight when its depth is at most one more than the seed lookahead. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.tight_iff (config : Config) (pulled
  anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).tight = true ↔
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat ≤
        1 + preset.MAX_SEED_LOOKAHEAD.toNat := by
  simp only [pinTerms, decide_eq_true_eq]

/-- Outside the tight window, `pendingR` is the stake and rise of the pending keys.

It also holds the reward of what the finalized balance exceeds them by. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.pendingR_eq (config : Config)
  (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).pendingR =
      if (pinTerms config pulled anc fin).tight = true then 0 else
        ∑ i ∈ (pinTerms config pulled anc fin).positions with
          (pinTerms config pulled anc fin).pendingRB i = true,
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
            3 * ((balanceAt fin i - balanceAt pulled i - (pinTerms config pulled anc fin).rise i +
              ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) := rfl

/-- The keys that `exitingB` marks have their effective balances in `exiting`. -/
private theorem sum_le_exiting (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (S : Finset ValidatorIndex)
    (member : ∀ v ∈ S, (pinTerms config state ancestor finalizedState).exitingB v.toNat = true) :
    ∑ v ∈ S, balanceAt state v.toNat ≤ (pinTerms config state ancestor finalizedState).exiting := by
  dsimp only [pinTerms]
  refine voters_sum_le (fun i => balanceAt state i) fun v hv => ?_
  have mark := of_decide_eq_true (member v hv)
  obtain ⟨w, found⟩ := Internal.validator_of_flag (state := state) (Or.inr mark.2.2)
  exact Internal.mem_positions_filter config state ancestor finalizedState found (member v hv)

/-- The exit budget adds two bands for each scheduled exit and each key the queues can exit. -/
private theorem exitingBands_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitingBands =
      2 * ((((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).exitingB i = true).card +
        (pinTerms config state ancestor finalizedState).queueKeys)) * preset.upwardBand := by
  dsimp only [pinTerms]
  simp only [decide_eq_true_eq]

/-- At most as many keys as the positions that `exitingB` marks are marked. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.card_exitingB_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (S : Finset ValidatorIndex)
    (member : ∀ v ∈ S, (pinTerms config state ancestor finalizedState).exitingB v.toNat = true) :
    S.card ≤ ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
      (pinTerms config state ancestor finalizedState).exitingB i = true).card := by
  refine Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat) (fun v hv => ?_)
    (fun a _ b _ same => UInt64.toNat_inj.mp same)
  have mark := of_decide_eq_true (member v hv)
  obtain ⟨w, found⟩ := Internal.validator_of_flag (state := state) (Or.inr mark.2.2)
  exact Internal.mem_positions_filter config state ancestor finalizedState found
    (p := fun i => (pinTerms config state ancestor finalizedState).exitingB i = true) (member v hv)

/-- The two further bands of the keys of `K5` are at most `exitingBands`, given their charges. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.two_bands_le_exitingBands (config :
  Config)
    (pulled anc fin counted : BeaconState preset fork) (V : Finset ValidatorIndex)
    {x : ForkedBeaconState preset} (tailC : Run config checks x ⟨fork, counted⟩) (highC : ℕ)
    (charged : ∀ v ∈ Internal.K5 counted V, (pinTerms config pulled anc fin).exitingB v.toNat =
      false →
      0 < Internal.bandC tailC highC v.toNat → ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (count : ((Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges,
      c.index = v.toNat).card ≤ (pinTerms config pulled anc fin).queueKeys) :
    2 * (∑ v ∈ Internal.K5 counted V, Internal.bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands := by
  have bounded (v : ℕ) : Internal.bandC tailC highC v ≤ preset.upwardBand := by
    unfold Internal.bandC
    split <;> omega
  rw [exitingBands_eq]
  set A := (Internal.K5 counted V).filter fun v => (pinTerms config pulled anc fin).exitingB v.toNat
    = true
  set B := (Internal.K5 counted V).filter fun v => (pinTerms config pulled anc fin).exitingB v.toNat
    = false
  have parts : ∑ v ∈ Internal.K5 counted V, Internal.bandC tailC highC v.toNat =
      ∑ v ∈ A, Internal.bandC tailC highC v.toNat + ∑ v ∈ B, Internal.bandC tailC highC v.toNat :=
        by
    rw [← Finset.sum_filter_add_sum_filter_not (Internal.K5 counted V)
      (fun v => (pinTerms config pulled anc fin).exitingB v.toNat = true)]
    simp [A, B]
  have first : ∑ v ∈ A, Internal.bandC tailC highC v.toNat ≤ A.card * preset.upwardBand := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun v _ => bounded _
  have second : ∑ v ∈ B, Internal.bandC tailC highC v.toNat ≤
      (B.filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card *
        preset.upwardBand := by
    have pointwise : ∀ v ∈ B, Internal.bandC tailC highC v.toNat ≤
        (if ∃ c ∈ tailC.departureCharges, c.index = v.toNat then preset.upwardBand else 0) := by
      intro v hv
      by_cases hc : ∃ c ∈ tailC.departureCharges, c.index = v.toNat
      · simp only [hc, ↓reduceIte]
        exact bounded _
      · simp only [hc, ↓reduceIte]
        have notBand : ¬ 0 < Internal.bandC tailC highC v.toNat := fun pos =>
          hc (charged v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2 pos)
        omega
    calc ∑ v ∈ B, Internal.bandC tailC highC v.toNat
        ≤ ∑ v ∈ B, (if ∃ c ∈ tailC.departureCharges, c.index = v.toNat
          then preset.upwardBand else 0) := Finset.sum_le_sum pointwise
      _ = (B.filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card *
          preset.upwardBand := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have inA := Internal.card_exitingB_le config pulled anc fin A fun v hv => (Finset.mem_filter.mp
    hv).2
  have times := Nat.mul_le_mul_right preset.upwardBand inA
  have countB : (B.filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys :=
    (Finset.card_le_card fun v hv => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1, (Finset.mem_filter.mp hv).2⟩).trans
        count
  have timesB := Nat.mul_le_mul_right preset.upwardBand countB
  rw [parts]
  nlinarith

/-- A key whose exit C assigned by C's epoch and that R does not read as exiting has a charge.

The key is active at R's epoch or the one before it, if R's record has the exit of C's.

The charge is on C's run, if the exit is not inherited from the split. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exit_charged (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    {u : Validator} (foundU : counted.validators.data[v.toNat]? = some u)
    (assignedC : u.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (exited : u.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat)
    (unslashedC : u.slashed = false)
    (atR : ∀ w, pulled.validators.data[v.toNat]? = some w → w.exitEpoch = u.exitEpoch →
      isActiveAt pulled (getPreviousEpoch pulled) v.toNat = true ∨
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true)
    (flag : (pinTerms config pulled anc fin).exitingB v.toNat = false) :
    ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  by_cases inherited : ∃ old, split.validators.data[v.toNat]? = some old ∧
      old.exitEpoch ≠ FAR_FUTURE_EPOCH
  · exfalso
    obtain ⟨old, oldFound, oldAssigned⟩ := inherited
    obtain ⟨uC, foundUC, keptC⟩ := tailC.registryLifecycle.validators v.toNat old oldFound
    have sameU : uC = u := Option.some.inj (foundUC.symm.trans foundU)
    rw [sameU] at keptC
    obtain ⟨w, foundW, keptP⟩ := toPulled.registryLifecycle.validators v.toNat old oldFound
    have exitU : u.exitEpoch = old.exitEpoch := keptC.exitEpoch oldAssigned
    have exitW : w.exitEpoch = old.exitEpoch := keptP.exitEpoch oldAssigned
    have exitWU : w.exitEpoch = u.exitEpoch := exitW.trans exitU.symm
    have exitWNat : w.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
      rw [exitWU]
      exact exited
    have nearNat := h.near
    have activeR := atR w foundW exitWU
    have notSlashed : w.slashed = false ∨ anc.finalizedCheckpoint.epoch.toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤ w.withdrawableEpoch.toNat := by
      cases slashed : w.slashed
      · exact .inl rfl
      · have delayed := Internal.slashed_waits (shared.append fromFin) h.genesis toPulled tailC
          h.early h.caps (Internal.Setting.delay h) foundW slashed (by simp [foundU, unslashedC])
        have := UInt64.le_iff_toNat_le.mp h.finalized
        exact .inr (Nat.le_trans (Nat.add_le_add_right this _) delayed)
    have marked : (pinTerms config pulled anc fin).exitingB v.toNat = true := by
      simp only [pinTerms, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩
      · rcases activeR with active | active <;> simp [active]
      · simpa [foundW] using notSlashed
      · simpa [foundW] using
          (show w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 by omega)
    rw [flag] at marked
    exact Bool.false_ne_true marked
  · obtain ⟨c, member, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early v.toNat
      (fun w hw => by
        by_contra far
        exact inherited ⟨w, hw, far⟩) u foundU assignedC
    exact ⟨c, member, index⟩

/-- A key of `K5` is unslashed in C's state. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K5_unslashed {v : ValidatorIndex}
  (member : v ∈ Internal.K5 counted V) :
    ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
  intro w found
  have inK5 := Finset.mem_filter.mp member
  simp only [Internal.Q, quorumVoters, Finset.mem_filter, List.mem_toFinset,
    List.mem_append] at inK5
  obtain ⟨⟨-, flag⟩, -, -⟩ := inK5
  simpa [slashedFlagAt, found] using flag

/-- A key of `K5` is a validator of C's registry that was active before C's epoch and is not now.

It is unslashed. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K5_previous_only (h : Setting
  config checks g split fin pulled anc counted V)
    {v : ValidatorIndex} (member : v ∈ Internal.K5 counted V) :
    ∃ u, counted.validators.data[v.toNat]? = some u ∧
      isActiveValidator u (getPreviousEpoch counted) = true ∧
      isActiveValidator u (getCurrentEpoch counted) = false := by
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inK5 := Finset.mem_filter.mp member
  simp only [Internal.Q, quorumVoters, Finset.mem_filter, List.mem_toFinset,
    List.mem_append] at inK5
  obtain ⟨⟨listed, -⟩, notActive, -⟩ := inK5
  have notCurrent : v ∉ getActiveValidatorIndices counted (getCurrentEpoch counted) := fun now =>
    notActive (by simpa [Internal.AC, activeVoters] using now)
  rcases listed with now | before
  · exact absurd now notCurrent
  obtain ⟨u, foundU, activeBefore⟩ := (mem_getActiveValidatorIndices within).mp before
  refine ⟨u, foundU, activeBefore, ?_⟩
  cases now : isActiveValidator u (getCurrentEpoch counted)
  · rfl
  · exact absurd ((mem_getActiveValidatorIndices within).mpr ⟨u, foundU, now⟩) notCurrent

/-- A key of `K5` that R does not read as exiting has a departure charge on C's run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K5_charged (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ Internal.K5 counted V) (flag : (pinTerms config pulled anc fin).exitingB v.toNat =
      false) :
    ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨u, foundU, activeBefore, notNow⟩ := Internal.K5_previous_only h member
  have unslashedC := Internal.K5_unslashed member u foundU
  have exitC := (previous_only_iff_exit counted u).mp ⟨activeBefore, notNow⟩
  have notFar := getCurrentEpoch_ne_farFuture h.twoSlots counted
  have assignedC : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far =>
    notFar (UInt64.toNat_inj.mp (by rw [← exitC.2, far]))
  refine Internal.exit_charged h tailC foundU assignedC (Nat.le_of_eq exitC.2) unslashedC
    (fun w foundW sameExit => ?_) flag
  have gap := ((shared.append fromFin).append toPulled).exit_activation_gap h.genesis v.toNat w
    foundW (sameExit ▸ assignedC)
  have exitW : w.exitEpoch.toNat = (getCurrentEpoch counted).toNat := by
    rw [sameExit]
    exact exitC.2
  have actLt : w.activationEpoch.toNat < (getCurrentEpoch counted).toNat := by omega
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have nearNat := h.near
  have previous := getPreviousEpoch_toNat pulled
  have activeAt (e : Epoch) (low : w.activationEpoch.toNat ≤ e.toNat)
      (high : e.toNat < w.exitEpoch.toNat) : isActiveAt pulled e v.toNat = true :=
    isActiveAt_eq_true_iff.mpr ⟨w, foundW, by
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
        UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
      exact ⟨low, high⟩⟩
  rcases Nat.lt_or_ge (getCurrentEpoch pulled).toNat (getCurrentEpoch counted).toNat with
    before | same
  · exact .inr (activeAt _ (by omega) (by omega))
  · exact .inl (activeAt _ (by omega) (by omega))

/-- A key of `K5` without a departure charge on C's run is one whose exit R reads. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.K5_exiting_of_not_charged
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ Internal.K5 counted V) (none : ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      :
    (pinTerms config pulled anc fin).exitingB v.toNat = true := by
  by_contra flag
  exact none (Internal.K5_charged h tailC member (by simpa using flag))

/-- The scheduled-exit budget covers the stake of keys whose exits R can see.

The keys of `K5` are those without a departure charge on C's run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_exiting (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat = true,
      Internal.eR pulled v) +
      (∑ v ∈ (Internal.K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        Internal.eR pulled v) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat =
        true,
        Internal.eR pulled v) ≤ (pinTerms config pulled anc fin).exiting := by
  have apartVK5 : Disjoint (Internal.VN counted V) (Internal.K5 counted V) := by
    rw [Finset.disjoint_left]
    intro v inV inK5
    simp only [Internal.VN, Internal.K5, Finset.mem_filter] at inV inK5
    exact inK5.2.2 inV.1
  have apartVK6 : Disjoint (Internal.VN counted V) (Internal.K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v inV inK6
    simp only [Internal.VN, Internal.K6, Finset.mem_filter] at inV inK6
    exact inV.2 inK6.1
  have apartK5K6 : Disjoint (Internal.K5 counted V) (Internal.K6 pulled counted) := by
    rw [Finset.disjoint_left]
    intro v inK5 inK6
    simp only [Internal.K5, Internal.K6, Finset.mem_filter] at inK5 inK6
    exact inK5.2.1 inK6.1
  rw [← Finset.sum_union (Finset.disjoint_filter_filter apartVK5),
    ← Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter_filter apartVK6, Finset.disjoint_filter_filter apartK5K6⟩)]
  exact sum_le_exiting config pulled anc fin _ fun v member => by
    rcases Finset.mem_union.mp member with member | member
    · rcases Finset.mem_union.mp member with member | member
      · exact (Finset.mem_filter.mp member).2
      · exact Internal.K5_exiting_of_not_charged h tailC (Finset.mem_filter.mp member).1
          (Finset.mem_filter.mp member).2
    · exact (Finset.mem_filter.mp member).2

/-- Outside the tight window, `late` is three times the stake of the late keys and their rise.

It also holds the reward of what the finalized balance exceeds them by. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.late_eq (config : Config) (pulled
  anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).late =
      if (pinTerms config pulled anc fin).tight = true then 0 else
        ∑ i ∈ (pinTerms config pulled anc fin).positions with
          (pinTerms config pulled anc fin).lateB i = true,
            (3 * balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
              3 * ((balanceAt fin i - balanceAt pulled i - (pinTerms config pulled anc fin).rise i +
                ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) := rfl

/-- Before Gloas, the queue budget covers the window's exit and consolidation churn and carries. -/
private theorem queueWindow_unfold (early : fork < .glamsterdam) (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueWindow =
      (pinTerms config state ancestor finalizedState).depth *
        (Apriori.activationExitChurn preset config (PinTerms.wide state) +
          Apriori.consolidationChurn preset config (PinTerms.wide state)) +
        max preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        max (if electra : .pectra ≤ fork then
          (finalizedState.consolidationBalanceToConsume electra).toNat else 0)
          (Apriori.consolidationChurn preset config (PinTerms.wide state)) := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  unfold pinTerms
  simp only [notGloas, ↓reduceIte]

/-- A state with a total of at most `wide` has an exit churn limit of at most the pin's. -/
private theorem exitRate_le {fork' : Fork} {s : BeaconState preset fork'}
    (early : fork' < .glamsterdam) {rate : Gwei} (wide : ℕ)
    (band : ∀ t : Gwei, getTotalActiveBalance s = .ok t → t.toNat ≤ wide)
    (computed : exitChurnLimit config s = .ok rate) :
    rate.toNat ≤ Apriori.activationExitChurn preset config wide := by
  obtain ⟨total, read⟩ := DirectSafety.exitChurnLimit_total early computed
  exact (Apriori.Internal.exit_rate_le_churn early read computed).trans
    (Apriori.Internal.exit_churn_mono (band total read))

/-- A state with a total of at most `wide` has a consolidation churn limit of at most the pin's.

The pin reads it at `wide`. -/
private theorem consRate_le {fork' : Fork} {s : BeaconState preset fork'}
    (early : fork' < .glamsterdam) {rate : Gwei} (wide : ℕ)
    (band : ∀ t : Gwei, getTotalActiveBalance s = .ok t → t.toNat ≤ wide)
    (computed : getConsolidationChurnLimit config s = .ok rate) :
    rate.toNat ≤ Apriori.consolidationChurn preset config wide := by
  obtain ⟨total, read⟩ := DirectSafety.consolidationChurnLimit_total early computed
  exact (Apriori.Internal.consolidationChurnLimit_le early read computed).trans
    (Apriori.Internal.consolidationChurn_mono (band total read))

/-- The amount that `exitQ` reads is at most the amounts of the charges at its position.

Those charges are the ones with an epoch up to a later one. -/
private theorem exitQ_amount_le (L : List DepartureCharge) (b₀ b v : ℕ) (le : b₀ ≤ b) :
    ((L.find? fun c => c.index == v && decide (c.epoch ≤ b₀)).map (·.amount)).getD 0 ≤
      ((L.filter fun c => c.epoch ≤ b).map fun c => if c.index = v then c.amount else 0).sum := by
  cases found : L.find? fun c => c.index == v && decide (c.epoch ≤ b₀) with
  | none => simp
  | some c =>
    have member := List.mem_of_find?_eq_some found
    have both := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at both
    have kept : c ∈ L.filter fun c => c.epoch ≤ b :=
      List.mem_filter.mpr ⟨member, by simpa using both.2.trans le⟩
    have term : c.amount ∈ (L.filter fun c => c.epoch ≤ b).map
        fun c => if c.index = v then c.amount else 0 :=
      List.mem_map.mpr ⟨c, kept, by simp [both.1]⟩
    simpa using List.single_le_sum (fun _ _ => Nat.zero_le _) _ term

/-- The `exitQ` of a set of keys is at most the amounts of the charges of the run.

Those charges are the ones with an epoch up to one that the run's end does not pass. -/
private theorem sum_exitQ_le {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (b : ℕ) (le : (getCurrentEpoch y.state).toNat ≤ b) (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.exitQ tail v.toNat ≤
      ((tail.departureCharges.filter fun c => c.epoch ≤ b).map (·.amount)).sum := by
  classical
  have each : ∀ v ∈ S, Internal.exitQ tail v.toNat ≤
      ((tail.departureCharges.filter fun c => c.epoch ≤ b).map
        fun c => if c.index = v.toNat then c.amount else 0).sum :=
    fun v _ => exitQ_amount_le _ _ b v.toNat le
  refine (Finset.sum_le_sum each).trans ?_
  refine (voters_sum_le (voters := S)
    (positions := S.image fun v : ValidatorIndex => v.toNat)
    (fun n => ((tail.departureCharges.filter fun c => c.epoch ≤ b).map
      fun c => if c.index = n then c.amount else 0).sum)
    fun v member => Finset.mem_image_of_mem _ member).trans ?_
  have swap := Multiset.sum_map_sum
    (m := (tail.departureCharges.filter fun c => c.epoch ≤ b : List DepartureCharge))
    (s := S.image fun v : ValidatorIndex => v.toNat)
    (f := fun (c : DepartureCharge) (n : ℕ) => if c.index = n then c.amount else 0)
  simp only [Multiset.map_coe, Multiset.sum_coe, Finset.sum_ite_eq] at swap
  rw [← swap]
  exact List.sum_le_sum fun c _ => by split <;> simp

/-- The departure charges of C's branch fit the window's churn and carries.

They are the charges with an epoch up to the run's last epoch.

The bound is the churn of the window and the two carries. -/
private theorem charges_le_queueWindow (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    ((tailC.departureCharges.filter fun c =>
      c.epoch ≤ (getCurrentEpoch counted).toNat - 1 + 1).map (·.amount)).sum ≤
        (pinTerms config pulled anc fin).queueWindow := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨_, pulledOk⟩ := h.pulledTotal
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨finalized, called, later, near, -⟩ := Internal.setting_epochs h
  -- the exit and consolidation churn of every state on the runs from the finalized state
  have band : ∀ (u : ForkedBeaconState preset) (run : Run config checks ⟨fork, fin⟩ u),
      u.fork < .glamsterdam →
      (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ t : Gwei, getTotalActiveBalance u.state = .ok t → t.toNat ≤ PinTerms.wide pulled := by
    intro u run uEarly uWithin t read
    have := (total_band_of_setting h run uEarly uWithin read pulledOk).2
    simp only [PinTerms.wide, pulledOk, Except.toOption, Option.getD_some]
    omega
  have exitBound : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tailC.Contains step → ∀ rate : Gwei, exitChurnLimit config u.state = .ok rate →
        rate.toNat ≤ Apriori.activationExitChurn preset config (PinTerms.wide pulled) := by
    intro u w step member rate computed
    obtain ⟨pre, post, _, uEarly, uEpoch⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
    have uEpoch' : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch counted).toNat := uEpoch
    exact exitRate_le uEarly _ (band u (fromFin.append pre) uEarly (by omega)) computed
  have consTail : ∀ site ∈ tailC.consolidationSites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate →
        rate.toNat ≤ Apriori.consolidationChurn preset config (PinTerms.wide pulled) := by
    intro site member _ rate computed
    obtain ⟨u, w, step, contained, _, same⟩ := consolidationSite_rate tailC h.early site member
    obtain ⟨pre, post, _, uEarly, uEpoch⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts contained h.early
    have uEpoch' : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch counted).toNat := uEpoch
    exact consRate_le uEarly _ (band u (fromFin.append pre) uEarly (by omega))
      (same rate computed)
  have consFin : ∀ site ∈ fromFin.consolidationSites, ∀ (_h : .pectra ≤ site.fork) (rate : Gwei),
      getConsolidationChurnLimit config site.state = .ok rate →
        rate.toNat ≤ Apriori.consolidationChurn preset config (PinTerms.wide pulled) := by
    intro site member _ rate computed
    obtain ⟨u, w, step, contained, _, same⟩ := consolidationSite_rate fromFin h.early site member
    obtain ⟨pre, post, _, uEarly, uEpoch⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts contained h.early
    have uEpoch' : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch split).toNat := uEpoch
    exact consRate_le uEarly _ (band u pre uEarly (by omega)) (same rate computed)
  obtain ⟨exitCarry, consolidationCarry⟩ :
      (split.exitBalanceToConsume electra).toNat ≤
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat ∧
      (split.consolidationBalanceToConsume electra).toNat ≤
        max (fin.consolidationBalanceToConsume electra).toNat
          (Apriori.consolidationChurn preset config (PinTerms.wide pulled)) :=
    queueCarry_le_of_run shared h.genesis fromFin electra h.early electra _ consFin
  have window := departure_charges_le_window_electra_cap tailC electra h.early
    ((getCurrentEpoch counted).toNat - 1)
    (Apriori.consolidationChurn preset config (PinTerms.wide pulled))
    (Apriori.activationExitChurn preset config (PinTerms.wide pulled)) exitBound consTail
  dsimp only at window
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  rw [queueWindow_unfold h.early]
  simp only [electra, ↓reduceDIte]
  generalize (pinTerms config pulled anc fin).depth = depth at depthEq ⊢
  generalize Apriori.activationExitChurn preset config (PinTerms.wide pulled) = E at *
  generalize Apriori.consolidationChurn preset config (PinTerms.wide pulled) = C at *
  have firstLe : (getCurrentEpoch counted).toNat - 1 + 2 - max (getCurrentEpoch split).toNat
      (split.earliestExitEpoch electra).toNat ≤ depth := by omega
  have secondLe : (getCurrentEpoch counted).toNat - 1 + 2 - max (getCurrentEpoch split).toNat
      (split.earliestConsolidationEpoch electra).toNat ≤ depth := by omega
  have exitTerm : (if (split.earliestExitEpoch electra).toNat ≤
        (getCurrentEpoch counted).toNat - 1 + 1
      then (split.exitBalanceToConsume electra).toNat else 0) ≤
      max preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := by
    split <;> omega
  have consolidationTerm : (if (split.earliestConsolidationEpoch electra).toNat ≤
        (getCurrentEpoch counted).toNat - 1 + 1
      then (split.consolidationBalanceToConsume electra).toNat else 0) ≤
      max (fin.consolidationBalanceToConsume electra).toNat C := by
    split <;> omega
  have a := Nat.mul_le_mul_right E firstLe
  have b := Nat.mul_le_mul_right C secondLe
  rw [Nat.mul_add depth E C]
  omega

/-- The keys with a charge of at least `exitFloor` are at most the window over `exitFloor`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.card_big_charges_le (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (S : Finset ValidatorIndex) :
    (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤ Internal.exitQ tailC
      v.toNat).card ≤
      (pinTerms config pulled anc fin).queueWindow /
        (pinTerms config pulled anc fin).exitFloor := by
  classical
  have positive : 0 < (pinTerms config pulled anc fin).exitFloor := by
    unfold pinTerms
    exact lt_max_of_lt_left Nat.one_pos
  rw [Nat.le_div_iff_mul_le positive]
  have each := Finset.card_nsmul_le_sum
    (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤ Internal.exitQ tailC v.toNat)
    (fun v => Internal.exitQ tailC v.toNat) (pinTerms config pulled anc fin).exitFloor
    fun v member => (Finset.mem_filter.mp member).2
  have subset := Finset.sum_le_sum_of_subset (f := fun v => Internal.exitQ tailC v.toNat)
    (Finset.filter_subset (fun v => (pinTerms config pulled anc fin).exitFloor ≤
      Internal.exitQ tailC v.toNat) S)
  have kept := sum_exitQ_le tailC ((getCurrentEpoch counted).toNat - 1 + 1)
    (by simp only; omega) S
  have window := charges_le_queueWindow h tailC
  simp only [smul_eq_mul] at each
  omega

/-- The exits and consolidations initiated on C's branch, against `queueExit`.

There are none in the tight window. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_queues (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    3 * ((∑ v ∈ (Internal.VN counted V), Internal.exitQ tailC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        Internal.exitQ tailC v.toNat)) ≤
      (pinTerms config pulled anc fin).queueExit := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have early := h.early
  obtain ⟨finalized, -, -, near, -⟩ := Internal.setting_epochs h
  -- the two sets are disjoint
  have apart : Disjoint (Internal.VN counted V)
      ((Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :=
        by
    refine Finset.disjoint_left.mpr fun v first second => ?_
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp second).1).2.2
      (Finset.mem_filter.mp first).1
  have queueExit_eq : (pinTerms config pulled anc fin).queueExit =
      if (pinTerms config pulled anc fin).tight = true then 0 else
        3 * (pinTerms config pulled anc fin).queueWindow := rfl
  rw [← Finset.sum_union apart, queueExit_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · -- the tight window has no exit of a counting key
    simp only [tight, ↓reduceIte]
    have tightLe : (pinTerms config pulled anc fin).depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat :=
      of_decide_eq_true tight
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    rw [depthEq] at tightLe
    have none : ∀ v : ValidatorIndex, Internal.exitQ tailC v.toNat = 0 := by
      intro v
      have missing : (tailC.departureCharges.find? fun c =>
          c.index == v.toNat && decide (c.epoch ≤ (getCurrentEpoch counted).toNat)) = none := by
        rw [List.find?_eq_none]
        intro c member
        have far : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
          DirectSafety.Run.departureCharges_epoch_ge_start tailC electra early c member
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and]
        intro _
        omega
      simp [Internal.exitQ, missing]
    simp [none]
  · simp only [tight, Bool.false_eq_true, ↓reduceIte]
    have window := charges_le_queueWindow h tailC
    have kept := sum_exitQ_le tailC ((getCurrentEpoch counted).toNat - 1 + 1)
      (by simp only; omega) ((Internal.VN counted V) ∪
        ((Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat))
    omega

/-- The deposit credits of a set of keys, as events, fit any per-event bound on them.

An event counts for a key only when `keep` holds there.

The bound reads the credits of the keys that the event keeps. -/
private theorem credDepR_sum_le (V : Finset ValidatorIndex) (events : List (BalanceEvent preset))
    (keep : BalanceEvent preset → ℕ → Prop) [∀ e i, Decidable (keep e i)]
    (T : BalanceEvent preset → ℕ)
    (each : ∀ e ∈ events, e.source = .deposits →
      ∑ v ∈ V.filter fun v => keep e v.toNat, Internal.keyCredit v.toNat e ≤ T e) :
    ∑ v ∈ V, ((events.filter fun e => e.source = .deposits ∧ keep e v.toNat).map
      (Internal.keyCredit v.toNat)).sum ≤ (events.map T).sum := by
  induction events with
  | nil => simp
  | cons e rest ih =>
    have tail := ih fun e' member => each e' (List.mem_cons_of_mem _ member)
    by_cases dep : e.source = .deposits
    · have head := each e List.mem_cons_self dep
      have split : ∑ v ∈ V, (((e :: rest).filter fun e => e.source = .deposits ∧
            keep e v.toNat).map (Internal.keyCredit v.toNat)).sum =
          ∑ v ∈ V.filter (fun v => keep e v.toNat), Internal.keyCredit v.toNat e +
            ∑ v ∈ V, ((rest.filter fun e => e.source = .deposits ∧ keep e v.toNat).map
              (Internal.keyCredit v.toNat)).sum := by
        rw [Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases kept : keep e v.toNat <;> simp [dep, kept]
      simp only [List.map_cons, List.sum_cons]
      omega
    · have same : ∑ v ∈ V, (((e :: rest).filter fun e => e.source = .deposits ∧
            keep e v.toNat).map (Internal.keyCredit v.toNat)).sum =
          ∑ v ∈ V, ((rest.filter fun e => e.source = .deposits ∧ keep e v.toNat).map
            (Internal.keyCredit v.toNat)).sum :=
        Finset.sum_congr rfl fun v _ => by simp [dep]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The deposit budget counts the window's deposit churn and carry at weight three. -/
private theorem queueDep_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueDep =
      3 * (((getCurrentEpoch state).toNat + 2 - (getCurrentEpoch finalizedState).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
        (if electra : .pectra ≤ fork then
          (finalizedState.depositBalanceToConsume electra).toNat else 0)) := rfl

/-- The funding credits of the deposit events of a run from the split fit the deposit churn.

The run ends within one epoch of R's, and its events are read at any horizon that its end allows.

The window is the carry of the finalized block and a churn for each epoch from it. -/
private theorem deposit_events_le (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (high : ℕ)
    (endEpoch : (getCurrentEpoch e).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (events.map DirectSafety.funding_deposit_credit).sum ≤
      (pinTerms config pulled anc fin).queueDep := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  -- Every step of the run starts within the epochs of `pulled`, so `high` can be that epoch.
  have same := DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tail endEpoch within
  have tailOk : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events := by
    rw [← same]
    exact replayed
  obtain ⟨ef, efOk⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  have fullOk := DirectSafety.Apriori.Internal.balanceEvents_append fromFin tail
    (getCurrentEpoch pulled).toNat efOk tailOk
  have capacity := DirectSafety.funding_deposit_capacity toFin (fromFin.append tail) h.genesis
    h.early (getCurrentEpoch pulled).toNat within (ef ++ events) fullOk
  have bound : ((ef ++ events).map DirectSafety.funding_deposit_credit).sum ≤
      (if electra : .pectra ≤ fork then (fin.depositBalanceToConsume electra).toNat else 0) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat := capacity
  rw [List.map_append, List.sum_append] at bound
  rw [queueDep_eq]
  omega

/-- The deposit queue bound, from the per-event bound of V's deposit credits.

The credits that a deposit event gives to V keys are at most its deposit credit.

That credit leaves out the keys that are withdrawn, which V keys never are.

The deposit credits of the run from the finalized block fit its carry and a churn for each epoch. -/
private theorem bud_deposits_of (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (each : ∀ e ∈ events, e.source = .deposits →
      ∑ v ∈ V, Internal.keyCredit v.toNat e ≤ DirectSafety.funding_deposit_credit e) :
    3 * (∑ v ∈ V, Internal.credDepR events v.toNat) ≤ (pinTerms config pulled anc fin).queueDep :=
      by
  have sum : ∑ v ∈ V, Internal.credDepR events v.toNat ≤
      (events.map DirectSafety.funding_deposit_credit).sum := by
    simpa [Internal.credDepR] using credDepR_sum_le V events (fun _ _ => True)
      DirectSafety.funding_deposit_credit (by simpa using each)
  have capacity := deposit_events_le h tail (Nat.le_succ _) high endEpoch replayed
  omega

/-- A deposit event credits a set of keys at most its funding credit, when none is withdrawable.

Each key of the set that is present before the event must not be withdrawable there.

A key absent before the event has no balance after it either, since its balances match. -/
private theorem deposit_each_le (e : BalanceEvent preset) (S : Finset ValidatorIndex)
    (dep : e.source = .deposits) (electra : .pectra ≤ e.before.fork)
    (matched : BalancesMatch e.after.state)
    (held : ∀ v ∈ S, ∀ w, e.before.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch e.before.state).toNat < w.withdrawableEpoch.toNat) :
    ∑ v ∈ S, Internal.keyCredit v.toNat e ≤ DirectSafety.funding_deposit_credit e := by
  have inj : Set.InjOn (fun v : ValidatorIndex => v.toNat) S := fun a _ b _ same =>
    UInt64.toNat_inj.mp same
  have image := selected_deposit_le (S.image fun v => v.toNat) e matched fun i member => by
    obtain ⟨v, inS, rfl⟩ := Finset.mem_image.mp member
    cases found : e.before.state.validators.data[v.toNat]? with
    | none => rfl
    | some w => simpa using held v inS w found
  rw [Finset.sum_image inj] at image
  simpa [DirectSafety.funding_deposit_credit, dep, electra, Internal.keyCredit] using image

/-- The deposits credited to two sets of keys on C's run fit the window's deposit churn.

The first set's credits are read as the scan of the deposit events.

The second set's are the deposits of events whose before-state does not hold the key slashed.

Each deposit event credits both sets together at most its funding credit. -/
private theorem deposits_scan_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (S P : Finset ValidatorIndex)
    (each : ∀ e ∈ eventsC, e.source = .deposits →
      ∑ v ∈ S, Internal.keyCredit v.toNat e +
        ∑ v ∈ P.filter (fun v => ¬ slashedFlagAt e.before.state v.toNat = some true),
          Internal.keyCredit v.toNat e ≤ DirectSafety.funding_deposit_credit e) :
    3 * (∑ v ∈ S, (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat
      highC
      tailC) + ∑ v ∈ P, Internal.depPre eventsC v.toNat) ≤ (pinTerms config pulled anc fin).queueDep
        := by
  obtain ⟨X, hX⟩ : ∃ X : BalanceEvent preset → ℕ, ∀ e, X e =
      ∑ v ∈ P.filter (fun v => ¬ slashedFlagAt e.before.state v.toNat = some true),
        Internal.keyCredit v.toNat e := ⟨_, fun _ => rfl⟩
  have scan := Internal.creditScan_sum_le S UInt64.toNat (fun _ => false) (fun s => decide (s =
    .deposits))
    highC (fun e => DirectSafety.funding_deposit_credit e - X e) tailC replayedC
    fun e member selected => by
      have := each e member (by simpa using selected)
      have := hX e
      omega
  have pre := credDepR_sum_le P eventsC (fun e i => ¬ slashedFlagAt e.before.state i = some true)
    (fun e => if e.source = .deposits then X e else 0) fun e _ dep => by simp [dep, hX e]
  have capacity := deposit_events_le h tailC h.near highC endEpochC replayedC
  have chain : (eventsC.map fun e => if (false = true ∨ decide (e.source = .deposits) = true)
        then DirectSafety.funding_deposit_credit e - X e else 0).sum +
      (eventsC.map fun e => if e.source = .deposits then X e else 0).sum ≤
        (eventsC.map DirectSafety.funding_deposit_credit).sum := by
    rw [← List.sum_map_add]
    refine List.sum_le_sum fun e member => ?_
    by_cases dep : e.source = .deposits
    · have := each e member dep
      have := hX e
      simp only [dep, decide_true, or_true, ↓reduceIte]
      omega
    · simp [dep]
  have exchange : ∑ v ∈ P, Internal.depPre eventsC v.toNat ≤
      (eventsC.map fun e => if e.source = .deposits then X e else 0).sum := pre
  omega

/-- A key that a step slashes is not yet withdrawable at the first state of that step.

A key that has exited is not withdrawable, since a withdrawable key is not slashed.

A key that has not exited has a withdrawable epoch at or after its exit, which is later. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.newly_slashed_unwithdrawable {g m n
  : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (caps : CapOrder preset) (toM : Run config checks g m)
    (step : Step config checks m n) (early : n.fork < .glamsterdam) {i : ℕ} {old new : Validator}
    (foundOld : m.state.validators.data[i]? = some old)
    (foundNew : n.state.validators.data[i]? = some new)
    (clean : old.slashed = false) (marked : new.slashed = true) :
    (getCurrentEpoch m.state).toNat < old.withdrawableEpoch.toNat := by
  by_cases exited : old.exitEpoch ≤ getCurrentEpoch m.state
  · exact UInt64.lt_iff_toNat_lt.mp
      ((Run.nil.snoc step).newly_slashed_initial_exited_unwithdrawable caps.activation
        caps.compounding early i old new foundOld foundNew clean marked exited)
  · have ordered := UInt64.le_iff_toNat_le.mp
      ((Run.invariant genesis.invariant toM).exitsOrdered old (Array.mem_of_getElem? foundOld))
    have before := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp exited)
    omega

/-- A key slashed at C and not slashed at the start of a deposit event is not withdrawable there.

The key is not slashed at the step's start, and the run from there ends with it slashed.

At the step that slashes it, the key is slashable, so it is not yet withdrawable.

Until then its withdrawable epoch is the one it has at the event's start, or its exit is far off. -/
private theorem slashed_deposit_held (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {u w : ForkedBeaconState preset} (ok : advanceSlotAcross config checks u = .ok w)
    (contained : tailC.Contains (Step.slot ok)) {es : List (BalanceEvent preset)}
    (replayedEs : (Step.slot ok : Step config checks u w).balanceEvents = .ok es)
    {e : BalanceEvent preset} (inStep : e ∈ es) (dep : e.source = .deposits)
    (ordered : ExitsOrdered e.before.state) (life : RegistryLifecycle e.before.state counted)
    {i : ℕ} (slashedC : ∃ b, counted.validators.data[i]? = some b ∧ b.slashed = true)
    {a : Validator} (found : e.before.state.validators.data[i]? = some a)
    (clean : a.slashed = false) :
    (getCurrentEpoch e.before.state).toNat < a.withdrawableEpoch.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨pre, post, rfl⟩ := Run.contains_split tailC (Step.slot ok) contained
  have earlyW : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have fuluU : .fusaka ≤ u.fork := Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)
  have toU := (toFin.append fromFin).append pre
  obtain ⟨-, wdKept, -, size, persist, sameEpoch⟩ := Internal.Run.events_kept toU h.genesis
    (Run.nil.snoc (Step.slot ok)) fuluU earlyW ok (.last .nil _) replayedEs e inStep dep
  obtain ⟨au, foundU⟩ : ∃ au, u.state.validators.data[i]? = some au :=
    ⟨_, Array.getElem?_eq_getElem (lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 size)⟩
  have cleanU : au.slashed = false := by
    cases flag : au.slashed
    · rfl
    · obtain ⟨x, read, marked⟩ := persist i au foundU flag
      obtain rfl := Option.some.inj (read.symm.trans found)
      simp [clean] at marked
  obtain ⟨m, n, preR, step, postR, -, notM, isN⟩ := Run.split_at_flip
    ((Run.nil.snoc (Step.slot ok)).append post)
    (fun z => ∃ b, z.state.validators.data[i]? = some b ∧ b.slashed = true)
    (by
      rintro ⟨b, read, marked⟩
      obtain rfl := Option.some.inj (foundU.symm.trans read)
      simp [cleanU] at marked) slashedC
  have toM := toU.append preR
  obtain ⟨bn, foundN, slashedN⟩ := isN
  obtain ⟨bm, foundM⟩ : ∃ bm, m.state.validators.data[i]? = some bm := by
    by_cases inside : i < m.state.validators.data.size
    · exact ⟨_, Array.getElem?_eq_getElem inside⟩
    · have := Internal.fresh_unslashed toM step h.genesis (Nat.le_of_not_lt inside) foundN
      simp [this] at slashedN
  have cleanM : bm.slashed = false := by
    cases flag : bm.slashed
    · rfl
    · exact absurd ⟨bm, foundM, flag⟩ notM
  have earlyN : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps postR.chainSteps) h.early
  have lateM : (getCurrentEpoch m.state).toNat < bm.withdrawableEpoch.toNat :=
    Internal.newly_slashed_unwithdrawable h.genesis h.caps toM step earlyN foundM foundN cleanM
      slashedN
  have epochs : (getCurrentEpoch u.state).toNat ≤ (getCurrentEpoch m.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps preR.chainSteps)
  have sameNat := congrArg UInt64.toNat sameEpoch
  by_cases unset : au.exitEpoch = FAR_FUTURE_EPOCH
  · have bound := UInt64.le_iff_toNat_le.mp (ordered a (Array.mem_of_getElem? found))
    have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots e.before.state
    by_cases assigned : a.exitEpoch = FAR_FUTURE_EPOCH
    · rw [assigned] at bound
      omega
    · obtain ⟨wc, readC, bC⟩ := slashedC
      obtain ⟨later, readL, lifeL⟩ := life.validators i a found
      obtain rfl : later = wc := Option.some.inj (readL.symm.trans readC)
      have exitC := congrArg UInt64.toNat (lifeL.exitEpoch assigned)
      obtain ⟨charge, member, -, charged⟩ := Run.departure_charge_of_assigned
        ((Run.nil.snoc (Step.slot ok)).append post) i au later foundU readC unset
        (by rw [lifeL.exitEpoch assigned]; exact assigned)
      have late := DirectSafety.Run.departureCharges_epoch_ge_start
        ((Run.nil.snoc (Step.slot ok)).append post) (Nat.le_trans (by decide) fuluU) h.early charge
        member
      omega
  · have keptM := Internal.kept_run toU h.genesis fuluU preR
      (Nat.lt_of_le_of_lt step.chainStep.fork_le earlyN)
    obtain ⟨le1, moved1⟩ := wdKept i au a foundU found unset
    obtain ⟨le2, moved2⟩ := keptM.withdrawable i au bm foundU foundM unset
    have e1 := UInt64.le_iff_toNat_le.mp le1
    have e2 := UInt64.le_iff_toNat_le.mp le2
    have eq1 : a.withdrawableEpoch = au.withdrawableEpoch := moved1.resolve_left (by simp [clean])
    have eq2 : bm.withdrawableEpoch = au.withdrawableEpoch := moved2.resolve_left (by simp [cleanM])
    have := congrArg UInt64.toNat eq1
    have := congrArg UInt64.toNat eq2
    omega

/-- The deposits credited to keys active at C's end, and to keys slashed there, fit the churn.

A key that exits after C's epoch is not withdrawable at any deposit event of C's run.

Its exit epoch is constant once set, and the exit epoch bounds the withdrawable epoch.

A key slashed at C counts only the deposits of events that do not hold it slashed.

An event that raises no balance credits nothing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.deposits_active_le (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (S P : Finset ValidatorIndex) (apart : Disjoint S P)
    (active : ∀ v ∈ S, ∃ w, counted.validators.data[v.toNat]? = some w ∧
      (getCurrentEpoch counted).toNat < w.exitEpoch.toNat)
    (slashedC : ∀ v ∈ P, ∃ b, counted.validators.data[v.toNat]? = some b ∧ b.slashed = true) :
    3 * (∑ v ∈ S, (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat
      highC
      tailC) + ∑ v ∈ P, Internal.depPre eventsC v.toNat) ≤ (pinTerms config pulled anc fin).queueDep
        := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have located := (Internal.run_located tailC (Nat.le_trans (by decide) h.fulu) h.early highC
    replayedC).1
  refine deposits_scan_le h tailC highC endEpochC replayedC S P fun e member dep => ?_
  rcases located e member dep with unconditional | ⟨u, w, ok, es, contained, replayedEs, inStep, -⟩
  · have zero (i : ℕ) : Internal.keyCredit i e = 0 := by
      have := unconditional i
      simp only [Internal.keyCredit]
      omega
    simp [zero]
  have forkLe := ((toFin.append fromFin).withdrawnConsolidationCredit_eq_zero tailC h.genesis
    h.early (Internal.Setting.delay h) replayedC e member).2.2
  obtain ⟨-, life, life', ordered, matched, -, epoch⟩ := replay_event_provenance
    (toFin.append fromFin) tailC h.genesis h.early highC endEpochC _ replayedC e member
  have union := deposit_each_le e
    (S ∪ P.filter fun v => ¬ slashedFlagAt e.before.state v.toNat = some true) dep
    (Nat.le_trans (Nat.le_trans (by decide) h.fulu) forkLe) matched fun v inUnion a found => ?_
  · rwa [Finset.sum_union (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) apart)]
      at union
  rcases Finset.mem_union.mp inUnion with inS | inP
  · obtain ⟨wC, foundC, late⟩ := active v inS
    obtain ⟨u, foundU, lifeU⟩ := (life.trans life').validators v.toNat a found
    obtain rfl : u = wC := Option.some.inj (foundU.symm.trans foundC)
    have epoch' : (getCurrentEpoch e.before.state).toNat ≤ (getCurrentEpoch counted).toNat := epoch
    have bound := UInt64.le_iff_toNat_le.mp (ordered a (Array.mem_of_getElem? found))
    have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots e.before.state
    by_cases unset : a.exitEpoch = FAR_FUTURE_EPOCH
    · rw [unset] at bound
      omega
    · have same := congrArg UInt64.toNat (lifeU.exitEpoch unset)
      omega
  · obtain ⟨inP, clean⟩ := Finset.mem_filter.mp inP
    simp only [slashedFlagAt, found, Option.map_some, Option.some.injEq,
      Bool.not_eq_true] at clean
    exact slashed_deposit_held h tailC ok contained replayedEs inStep dep ordered
      (life.trans life') (slashedC v inP) found clean

/-- The deposit budget covers the deposits applied to voters on R's branch at weight three. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_deposits (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    3 * (∑ v ∈ V, Internal.credDepR events v.toNat) ≤ (pinTerms config pulled anc fin).queueDep :=
      by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have within := BeaconState.registryWithinLimit_of_lt h.early pulled
  -- The keys of `V` are active at R's epoch, so no deposit event credits a withdrawable one.
  have recent : ∀ i ∈ V.image UInt64.toNat, ∃ w, pulled.validators.data[i]? = some w ∧
      (isActiveValidator w (getCurrentEpoch pulled) = true ∨
        isActiveValidator w (getPreviousEpoch pulled) = true) := by
    intro i hi
    obtain ⟨v, member, rfl⟩ := Finset.mem_image.mp hi
    have listed : v ∈ getActiveValidatorIndices pulled (getCurrentEpoch pulled) := by
      simpa [activeVoters] using (h.voting v member).1
    obtain ⟨u, found, active⟩ := (mem_getActiveValidatorIndices within).mp listed
    exact ⟨u, found, .inl active⟩
  refine bud_deposits_of h tail high endEpoch replayed fun e member deposit => ?_
  have forkLe := ((toFin.append fromFin).withdrawnConsolidationCredit_eq_zero tail h.genesis h.early
    (Internal.Setting.delay h) replayed e member).2.2
  have credited := Run.deposit_credit_le_funding (toFin.append fromFin) tail h.genesis h.early
    h.twoSlots high endEpoch replayed (V.image UInt64.toNat) recent e member deposit
    (Nat.le_trans electra forkLe)
  rw [Finset.sum_image fun _ _ _ _ same => UInt64.toNat_inj.mp same] at credited
  exact credited

/-- A step with a key that has no exit at its start and one at its end charges that key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_charges_of_exits {m n :
  ForkedBeaconState preset}
    (step : Step config checks m n) {i : ℕ} {u w : Validator}
    (foundM : m.state.validators.data[i]? = some u)
    (foundN : n.state.validators.data[i]? = some w) (unset : u.exitEpoch = FAR_FUTURE_EPOCH)
    (assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    step.departureCharges.any (·.index == i) = true := by
  obtain ⟨d, dMember, dIndex, -⟩ :=
    (Run.nil.snoc step).departure_charge_of_assigned i u w foundM foundN unset assigned
  exact List.any_eq_true.mpr
    ⟨d, by simpa [Run.departureCharges] using dMember, by simpa using dIndex⟩

/-- Two charges of a run at one position are the same charge. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.charge_unique {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    {c d : DepartureCharge} (hc : c ∈ tail.departureCharges) (hd : d ∈ tail.departureCharges)
    (same : c.index = d.index) : c = d :=
  List.inj_on_of_nodup_map (DirectSafety.departureCharges_run_indices tail) hc hd same

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The slashing credits of C's run are paid for each key by its envelope or its charge.

A key of the split's registry is paid by the envelope on its effective balance.

A key beyond it is paid by the charge that its exit leaves. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashing_charge (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (env cr : ℕ → ℕ)
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i ≤ env i)
    (created : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, split.validators.data.size ≤ i →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ cr i) :
    (eventsC.map fun e => if e.source = .slashings then e.creditLimit else 0).sum ≤
      ∑ i ∈ (Finset.range counted.validators.data.size).filter (fun i =>
          (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
            (counted.validators.data[i]?.map (·.slashed)).getD false = true),
        (if i < split.validators.data.size then
          env i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else cr i) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  refine slashing_credits_le (shared.append fromFin) tailC h.genesis h.early h.caps.compounding
    highC endEpochC _ _ ?_ replayedC
  intro a b step member i inside flag
  obtain ⟨pre, post, -, -, -⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have sameFork : a.fork = fork :=
    Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at flag
  obtain ⟨unslashedA, slashedB⟩ := flag
  have insideCounted : i < counted.validators.data.size :=
    Nat.lt_of_lt_of_le (Finset.mem_range.mp inside) post.registryLifecycle.size_le
  have unslashedSplit : (split.validators.data[i]?.map (·.slashed)).getD false = false := by
    cases found : split.validators.data[i]? with
    | none => rfl
    | some w =>
      simp [Internal.unslashed_of_run pre found (fun u read => by simpa [read] using unslashedA)]
  have slashedCounted : (counted.validators.data[i]?.map (·.slashed)).getD false = true := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at slashedB
    | some w =>
      have marked : w.slashed = true := by simpa [found] using slashedB
      obtain ⟨u, read, kept⟩ := post.slashedPersistence i w found marked
      simp [read, kept]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr insideCounted, unslashedSplit,
    slashedCounted⟩, ?_⟩
  by_cases registered : i < split.validators.data.size
  · simp only [registered, ↓reduceIte, sameFork]
    exact Nat.div_le_div_right (registry step member i registered
      (by simp [unslashedA, slashedB]))
  · simp only [registered, ↓reduceIte, sameFork]
    exact created step member i (Nat.le_of_not_lt registered)
      (by simp [unslashedA, slashedB])

/-- The amount of the departure charge of a key on a run, or 0.

The charge reads the effective balance before the step that assigns the exit. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.chargeAmt {x y : ForkedBeaconState
  preset} (tail : Run config checks x y) (i : ℕ) :
    ℕ :=
  ((tail.departureCharges.find? fun c => c.index == i).map (·.amount)).getD 0

/-- A charge that meets a test, and is the only one that does, is the first that does. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.find_charge {l : List
  DepartureCharge} {p : DepartureCharge → Bool}
    {c : DepartureCharge} (member : c ∈ l) (hp : p c = true)
    (unique : ∀ d ∈ l, p d = true → d = c) : l.find? p = some c := by
  obtain ⟨d, chosen⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨c, member, hp⟩)
  obtain rfl := unique d (List.mem_of_find?_eq_some chosen) (List.find?_some chosen)
  exact chosen

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that a step slashes with its exit unset is charged its effective balance before the step.

The slashing assigns its exit, so the step records a departure charge of that amount.

The charge of the run at the key is that one. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slash_exit_charge (h : Setting
  config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (old new : Validator) (foundA : a.state.validators.data[i]? = some old)
    (foundB : b.state.validators.data[i]? = some new) (unset : old.exitEpoch = FAR_FUTURE_EPOCH)
    (slashed : new.slashed = true) :
    effectiveAt a i ≤ Internal.chargeAmt tailC i := by
  classical
  unfold Internal.chargeAmt
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨pre, post, cut, -, -⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have assigned : new.exitEpoch ≠ FAR_FUTURE_EPOCH :=
    run_slashed_exit_assigned (((shared.append fromFin).append pre).snoc step) h.genesis
      h.caps.activation h.caps.compounding bEarly (Internal.Setting.delay h) i new foundB slashed
  have inStep : (⟨i, new.exitEpoch.toNat, old.effectiveBalance.toNat⟩ : DepartureCharge) ∈
      step.departureCharges := by
    apply List.mem_filterMap.mpr
    refine ⟨(old, i), ?_, ?_⟩
    · simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using foundA
    · simp [foundB, unset, assigned]
  have inRun : (⟨i, new.exitEpoch.toNat, old.effectiveBalance.toNat⟩ : DepartureCharge) ∈
      tailC.departureCharges := by
    rw [cut, Run.departureCharges_append]
    simp [Run.departureCharges, inStep]
  rw [Internal.find_charge inRun (by simp)
    (fun d inD hd => Internal.charge_unique tailC inD inRun (by simpa using hd))]
  simp [effectiveAt, foundA]

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key beyond R's registry is charged the amount of its exit and what it gains after it.

An exit that a step assigns by the slashing is the charge of that step.

An earlier exit adds its gains, bands and credits, which `extra` bounds. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_charge (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (extra : ℕ → ℕ)
    (earlier : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ (i : ℕ), split.validators.data.size ≤ i → ∀ (old : Validator),
        a.state.validators.data[i]? = some old → old.exitEpoch ≠ FAR_FUTURE_EPOCH →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + extra i)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : split.validators.data.size ≤ i)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    effectiveAt a i ≤ Internal.chargeAmt tailC i + extra i := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at flag
  obtain ⟨-, slashedB⟩ := flag
  cases foundA : a.state.validators.data[i]? with
  | none => simp [effectiveAt, foundA]
  | some old =>
    by_cases unset : old.exitEpoch = FAR_FUTURE_EPOCH
    · cases foundB : b.state.validators.data[i]? with
      | none => simp [foundB] at slashedB
      | some new =>
        have marked : new.slashed = true := by simpa [foundB] using slashedB
        exact (Internal.slash_exit_charge h fromFin tailC step member i old new foundA foundB unset
          marked).trans (Nat.le_add_right _ _)
    · exact earlier step member i created old foundA unset

/-- The keys whose exit is charged within the run's epochs pay at most the window of the queues.

For such a key the charge due by the end of the run is its full departure charge. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.charge_amounts_le_queueWindow
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (S : Finset ValidatorIndex)
    (charged : ∀ v ∈ S, ∃ c ∈ tailC.departureCharges,
      c.index = v.toNat ∧ c.epoch ≤ (getCurrentEpoch counted).toNat) :
    ∑ v ∈ S, Internal.chargeAmt tailC v.toNat ≤ (pinTerms config pulled anc fin).queueWindow := by
  classical
  have same : ∀ v ∈ S, Internal.chargeAmt tailC v.toNat = Internal.exitQ tailC v.toNat := by
    intro v member
    obtain ⟨c, inRun, index, epoch⟩ := charged v member
    have unique : ∀ d ∈ tailC.departureCharges, d.index = v.toNat → d = c := fun d inD same =>
      Internal.charge_unique tailC inD inRun (same.trans index.symm)
    unfold Internal.chargeAmt Internal.exitQ
    rw [Internal.find_charge inRun (by simp [index]) (fun d inD hd => unique d inD (by simpa using
      hd)),
      Internal.find_charge inRun (by simp [index, epoch])
        (fun d inD hd => unique d inD (by simp at hd; exact hd.1))]
  rw [Finset.sum_congr rfl same]
  refine (sum_exitQ_le tailC ((getCurrentEpoch counted).toNat - 1 + 1)
    (by simp only; omega) S).trans ?_
  exact charges_le_queueWindow h tailC

/-- Either a run has no counted charge of a key and `exitQ` is zero.

Or `exitQ` is the amount of a counted charge of the key.

The counted charges are those whose exit epoch is at most the run's last epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exitQ_cases {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (v : ℕ) :
    ((∀ c ∈ tail.departureCharges, c.index = v → ¬ c.epoch ≤ (getCurrentEpoch y.state).toNat) ∧
      Internal.exitQ tail v = 0) ∨
    ∃ c ∈ tail.departureCharges, c.index = v ∧ c.epoch ≤ (getCurrentEpoch y.state).toNat ∧
      Internal.exitQ tail v = c.amount := by
  cases found : tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat) with
  | none =>
    refine .inl ⟨fun c mem idx le => ?_, by simp [Internal.exitQ, found]⟩
    have := List.find?_eq_none.mp found c mem
    simp [idx, le] at this
  | some c =>
    have both := List.find?_some found
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at both
    exact .inr ⟨c, List.mem_of_find?_eq_some found, both.1, both.2, by simp [Internal.exitQ, found]⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A charge of a run is the charge of the stop at its position, on the run after a prefix.

The stop is the state before the step that assigns the exit, and the charge reads its balance. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.stop_of_charge {x s y :
  ForkedBeaconState preset} (fromX : Run config checks x s)
    (tail : Run config checks s y) {c0 : DepartureCharge} (member : c0 ∈ tail.departureCharges)
    {i : ℕ} (index : c0.index = i) :
    ∃ stop : Stop (fromX.append tail) i, stop.charge = some c0 := by
  subst index
  have inTail : c0 ∈ (fromX.append tail).departureCharges := by
    rw [Run.departureCharges_append]
    exact List.mem_append_right _ member
  obtain ⟨stop⟩ := Stop.exists (fromX.append tail) c0.index
  obtain ⟨c, chosen⟩ : ∃ c, stop.charge = some c := by
    cases hc : stop.charge with
    | none =>
      have selected := stop.selected
      rw [hc] at selected
      exact absurd rfl (selected.2 c0 inTail)
    | some c => exact ⟨c, rfl⟩
  have selected := stop.selected
  rw [chosen] at selected
  have cEq : c = c0 := Internal.charge_unique _ selected.1 inTail selected.2.1
  subst cEq
  exact ⟨stop, chosen⟩

/-- The rise scan records exactly those positions that the run charges. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.riseScan_fst {x : ForkedBeaconState
  preset} (v high : ℕ)
    {y : ForkedBeaconState preset} (tail : Run config checks x y) :
    (Internal.riseScan (config := config) (checks := checks) v high tail).1 = true ↔
      ∃ c ∈ tail.departureCharges, c.index = v := by
  induction tail with
  | nil => simp [Internal.riseScan, Run.departureCharges]
  | snoc pre step ih =>
    simp only [Internal.riseScan, Run.departureCharges, Bool.or_eq_true, ih, List.any_eq_true,
      List.mem_append, beq_iff_eq]
    constructor
    · rintro (⟨c, member, same⟩ | ⟨c, member, same⟩)
      · exact ⟨c, .inl member, same⟩
      · exact ⟨c, .inr member, same⟩
    · rintro ⟨c, member | member, same⟩
      · exact .inl ⟨c, member, same⟩
      · exact .inr ⟨c, member, same⟩

/-- The charge adds one upward band to the rise recorded after it. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.riseQ_eq_of_seen {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high i : ℕ) (seen : (Internal.riseScan i high tail).1 = true) :
    Internal.riseQ tail high i = preset.upwardBand + (Internal.riseScan i high tail).2 := by
  simp only [Internal.riseQ, seen, ↓reduceIte]

/-- A key with no charge on the run has no rise after its exit. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.riseQ_eq_zero {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) (none : ∀ c ∈ tail.departureCharges, c.index ≠ v) : Internal.riseQ tail high v = 0
      := by
  have unseen : (Internal.riseScan (config := config) (checks := checks) v high tail).1 ≠ true :=
    fun seen =>
    let ⟨c, member, same⟩ := (Internal.riseScan_fst v high tail).mp seen
    none c member same
  simp [Internal.riseQ, unseen]

/-- A key with no charge on a run has no charge amount. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.chargeAmt_eq_zero {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    {i : ℕ} (none : ¬ ∃ c ∈ tail.departureCharges, c.index = i) : Internal.chargeAmt tail i = 0 :=
      by
  unfold Internal.chargeAmt
  rw [List.find?_eq_none.mpr fun c member same => none ⟨c, member, by simpa using same⟩]
  rfl

/-- A key of `K5` that has a charge on the run exits by the run's last epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.charge_epoch_le_of_K5 (h : Setting
  config checks g split fin pulled anc counted V)
    {x : ForkedBeaconState preset} (tail : Run config checks x ⟨fork, counted⟩)
    {v : ValidatorIndex} (member : v ∈ Internal.K5 counted V) :
    ∀ c ∈ tail.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat := by
  intro c charged same
  obtain ⟨w, found, assigned, epoch⟩ := Run.departure_charge_exit tail c charged
  obtain ⟨u, foundU, activeBefore, notNow⟩ := Internal.K5_previous_only h member
  rw [same] at found
  have equal : u = w := Option.some.inj (foundU.symm.trans found)
  subst equal
  have previous := getPreviousEpoch_toNat counted
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeBefore
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not] at notNow
  have low := UInt64.le_iff_toNat_le.mp activeBefore.1
  rw [← epoch]
  rcases notNow with notLow | notHigh
  · exact absurd (UInt64.le_iff_toNat_le.mpr (by omega)) notLow
  · have : ¬ (getCurrentEpoch counted).toNat < u.exitEpoch.toNat :=
      fun lt => notHigh (UInt64.lt_iff_toNat_lt.mpr lt)
    omega

end Terms
end PinDrift
end EthLib.Consensus.Models.Network

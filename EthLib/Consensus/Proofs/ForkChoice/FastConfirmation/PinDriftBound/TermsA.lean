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
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.Prefix

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
private theorem cV_le_of (h : Setting config checks g split fin pulled anc counted V)
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
private theorem key_floorR_from (h : Setting config checks g split fin pulled anc counted V)
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
private theorem parameters_of_fusaka {fork : Fork} (fusaka : .fusaka ≤ fork)
    (early : fork < .glamsterdam) :
    EthLib.Consensus.parameters preset fork = EthLib.Consensus.parameters preset .fusaka := by
  cases fork <;> first
    | rfl
    | exact absurd fusaka (by decide)
    | exact absurd early (by decide)

/-- The floor debit of a replay is its penalties plus its sync debits. -/
private theorem floorPenaltyDebit_sum (i : ℕ) (events : List (BalanceEvent preset)) :
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
  have splitDebit := floorPenaltyDebit_sum i.toNat before
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

The guards of the floor trace are `floor_guards`, from the setting's guard at the finalized block.

Nothing in the statement needs the key to be slashed, so it holds for a key that stays unslashed.

A step may assign the key's exit within the window, if its withdrawable epoch is beyond the window.

No upgrade runs from Fulu, so no step records a crossing. -/
private theorem slashed_floor (h : Setting config checks g split fin pulled anc counted V)
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
  rw [balance, debt, floorPenaltyDebit_sum] at floor
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

The guards are `floor_guards`, with the exit guard `retained` of the segment.

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
private theorem segment_potential (h : Setting config checks g split fin pulled anc counted V)
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

`segment_potential` keeps the form without the slash for a key that is unslashed at the end.

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
    rw [same, parameters_of_fusaka h.fulu h.early]
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

The potential floor is `segment_potential`, read at the end of each prefix from the finalized block.

The guards are `floor_guards`, with the exit guard `retained` and the pass rate `pass`.

The step `arith` is the arithmetic that fits the closed form of the potential floor to `floor`.

It holds for each epoch count up to C's.

It also holds for each debit that is at most the key's sync and partial debits over the run. -/
private theorem cfloor_balance (h : Setting config checks g split fin pulled anc counted V)
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
  obtain ⟨D, split, closed⟩ := segment_potential h near i clean Run.nil r1 r2 val initial
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

The potential floor is `segment_potential_slash`.

It is read at the end of each prefix, from the finalized block.

The step `arithS` fits its closed form to `floor`, and `loss` is the slash's share.

`cfloor_balance` has the key unslashed at the end of the run and the closed form of one epoch less.

That form is stronger than this one, so `cfloor_balance` is not a case of it. -/
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
private theorem cfloor_origin (h : Setting config checks g split fin pulled anc counted V)
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

The balance of the key at every prefix end is above `floor`, as `endpointFloor` says.

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

The balance of the key at every prefix end is above `floor`, by `cfloor_balance`.

The effective balance of the key at the end of a prefix is then at least a least value.

That value is the least of its effective balance and its cap at the finalized block.

And of `floor` rounded down to an increment. -/
private theorem cfloor_endpoint (h : Setting config checks g split fin pulled anc counted V)
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
    (fun r1 r2 whole => cfloor_balance h e wholeRun near replayed i val initial clean retained
      slack ρn ρd floor start pass arith r1 r2 whole) rp rest cut

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at a state of C's run is above a least value, for a slashed key.

The balance of the key at every prefix end is above `floor`, less `loss`, by `cfloor_balance_slash`.

The least value is that of `cfloor_endpoint`, with `floor - loss` for `floor`. -/
private theorem cfloor_endpoint_slash (h : Setting config checks g split fin pulled anc counted V)
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

It falls by what `fall` charges, in `X`: the leak and the gain over the depth, and the partials.

The hypothesis `margin` fits the closed form of the potential floor to the floor of the fall.

The hypothesis `stay` keeps the effective balance at its finalized value if the test holds.

It is `floorC_stay`, for a key with no sync debits. -/
private theorem floorC_at (h : Setting config checks g split fin pulled anc counted V)
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
  have eff := cfloor_endpoint h counted (fromFin.append tailC) h.near replayed i val initial clean
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
private theorem rate_of_guard
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
private theorem rise_arith {inc band capFor high finEB start eR eC Bc capHigh S U : Nat}
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

`Run.effective_floor_pair` bounds the balance at every state by `creditBound`, given the right `E`.

`E` is at least the effective balances that the bound allows.

Then the update of the effective balances reads that bound as its ceiling. -/
private theorem key_credit_ceiling {n y : ForkedBeaconState preset}
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
private theorem passRate_le_leakAt (h : Setting config checks g split fin pulled anc counted V)
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
private theorem finalized_le_current {g : ForkedBeaconState preset}
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
    UInt64.le_iff_toNat_le.mp (finalized_le_current h)⟩
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
    have finCur := UInt64.le_iff_toNat_le.mp (finalized_le_current h)
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

/-- The keys that join at R's next epoch are charged their rise in `joinRise`. -/
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

/-- `exitingBands` is two bands for each key that `exitingB` marks and for each queue key. -/
private theorem exitingBands_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitingBands =
      2 * ((((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).exitingB i = true).card +
        (pinTerms config state ancestor finalizedState).queueKeys)) * preset.upwardBand := by
  dsimp only [pinTerms]
  simp only [decide_eq_true_eq]

/-- At most as many keys as the positions that `exitingB` marks are marked. -/
private theorem card_exitingB_le (config : Config)
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
private theorem two_bands_le_exitingBands (config : Config)
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
  have inA := card_exitingB_le config pulled anc fin A fun v hv => (Finset.mem_filter.mp hv).2
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
private theorem exit_charged (h : Setting config checks g split fin pulled anc counted V)
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
private theorem K5_charged (h : Setting config checks g split fin pulled anc counted V)
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
  refine exit_charged h tailC foundU assignedC (Nat.le_of_eq exitC.2) unslashedC
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

/-- A key of `K5` without a departure charge on C's run is one whose exit R reads.

It is the contrapositive of `K5_charged`. -/
private theorem K5_exiting_of_not_charged
    (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ Internal.K5 counted V) (none : ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      :
    (pinTerms config pulled anc fin).exitingB v.toNat = true := by
  by_contra flag
  exact none (K5_charged h tailC member (by simpa using flag))

/-- The stake of the keys whose exit R reads, against `exiting`.

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
      · exact K5_exiting_of_not_charged h tailC (Finset.mem_filter.mp member).1
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

/-- Before Gloas, `queueWindow` is the depth's exit and consolidation churn and the two carries. -/
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
  have notGloas : ¬ .glamsterdam ≤ fork' := Nat.not_le_of_lt early
  obtain ⟨total, read⟩ : ∃ t, getTotalActiveBalance s = .ok t := by
    cases first : getTotalActiveBalance s with
    | error e =>
      simp [exitChurnLimit, notGloas, getActivationExitChurnLimit, getBalanceChurnLimit, first,
        bind, Except.bind] at computed
    | ok t => exact ⟨t, rfl⟩
  exact (Apriori.Internal.exit_rate_le_churn early read computed).trans
    (Apriori.Internal.exit_churn_mono (band total read))

/-- A state with a total of at most `wide` has a consolidation churn limit of at most the pin's.

The pin reads it at `wide`. -/
private theorem consRate_le {fork' : Fork} {s : BeaconState preset fork'}
    (early : fork' < .glamsterdam) {rate : Gwei} (wide : ℕ)
    (band : ∀ t : Gwei, getTotalActiveBalance s = .ok t → t.toNat ≤ wide)
    (computed : getConsolidationChurnLimit config s = .ok rate) :
    rate.toNat ≤ Apriori.consolidationChurn preset config wide := by
  have notGloas : ¬ .glamsterdam ≤ fork' := Nat.not_le_of_lt early
  obtain ⟨total, read⟩ : ∃ t, getTotalActiveBalance s = .ok t := by
    cases first : getTotalActiveBalance s with
    | error e =>
      simp [getConsolidationChurnLimit, notGloas, getBalanceChurnLimit, first, bind,
        Except.bind] at computed
    | ok t => exact ⟨t, rfl⟩
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
private theorem card_big_charges_le (h : Setting config checks g split fin pulled anc counted V)
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

/-- `queueDep` is three times the deposit churn of each epoch of the window, and the carry. -/
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
private theorem deposits_active_le (h : Setting config checks g split fin pulled anc counted V)
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

/-- The deposits applied on R's branch to V keys, at weight 3, against `queueDep`. -/
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

/-- A step with a key that has no exit at its start and one at its end charges that key.

It is the converse of `charge_exits`. -/
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

For such a key `chargeAmt` is the `exitQ` of the run. -/
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

/-- A run has a charge at a position exactly when `riseScan` has seen one. -/
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
private theorem charge_epoch_le_of_K5 (h : Setting config checks g split fin pulled anc counted V)
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

/-- The quarter of any total has a base reward per increment, if any total has one.

The factor times the increment fits in a `UInt64` for every total, and the quarter is positive. -/
private theorem quarter_base_ok (facts : PinPresetFacts preset) {total perIncrement : Gwei}
    (perOk : getBaseRewardPerIncrement preset total = .ok perIncrement) (T : Gwei) :
    ∃ pq, getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq := by
  have size := facts.incrementSize
  have positive : 0 < (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei).toNat := by
    split
    · rename_i big
      simp only [UInt64.toNat_div]
      show 0 < T.toNat / 4
      omega
    · simp only [UInt64.toNat_div]
      show 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat / 5
      omega
  generalize (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
    else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei) = q at positive ⊢
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at perOk
  obtain ⟨scaled, scaledOk, -⟩ := perOk
  have root : integerSquareroot q ≠ 0 := fun zero => by
    have value := toNat_integerSquareroot q
    rw [zero] at value
    have := Nat.sqrt_pos.mpr positive
    simp only [UInt64.toNat_zero] at value
    omega
  refine ⟨scaled / integerSquareroot q, ?_⟩
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff]
  exact ⟨scaled, scaledOk, divChecked_ok_iff.mpr ⟨root, by rw [UInt64.toNat_div]⟩⟩

/-- The pin has a rate `P` that bounds the reward rate at every state of a run from `fin`.

The rate is the reserve's base reward per increment, or zero if the reward read fails.

At the maximum effective balance this rate gives the reserve's flag gain bound. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.pin_rate_exists (h : Setting config
  checks g split fin pulled anc counted V) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ≤
          (pinTerms config pulled anc fin).gainRateMax ∧
      ∀ {m : BeaconState preset fork} (_toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩),
        (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
        ∀ total perIncrement : Gwei, getTotalActiveBalance m = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat *
              ((∑ i ∈ (getActiveValidatorIndices m (getPreviousEpoch m)).toFinset,
                effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
                  preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  have gainMax : (pinTerms config pulled anc fin).gainRateMax =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := rfl
  by_cases anyOk : ∃ total perIncrement : Gwei,
      getBaseRewardPerIncrement preset total = .ok perIncrement
  · obtain ⟨total, perIncrement, perOk⟩ := anyOk
    obtain ⟨pq, pqOk⟩ :=
      quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
    refine ⟨pq.toNat, by rw [pqOk]; rfl, ?_, fun toM inside =>
      rate_of_guard h toM inside (Or.inl rfl) pqOk⟩
    rw [gainMax, pqOk]
    simp only [Except.toOption, Option.getD_some, le_refl]
  · refine ⟨0, ?_, ?_, fun _ _ total perIncrement _ perOk =>
      absurd ⟨total, perIncrement, perOk⟩ anyOk⟩
    · cases hr : getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5) with
      | error e => rfl
      | ok p => exact absurd ⟨_, p, hr⟩ anyOk
    · simp

/-- The pin's rate bounds the reward rate at each state of a prefix of C's tail.

The prefix ends at most one epoch after the call, and its states are of the fork of the setting. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_rate_forked (h : Setting config
  checks g split fin pulled anc counted V) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      ∀ a : ForkedBeaconState preset, Run config checks ⟨fork, split⟩ a → a.fork ≤ fork →
      (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ total perIncrement : Gwei, getTotalActiveBalance a.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices a.state
          (getPreviousEpoch a.state)).toFinset, effectiveAt a j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨P, hP, -, rateAll⟩ := Internal.pin_rate_exists h
  obtain ⟨fromFin⟩ := h.fromFin
  refine ⟨P, hP, fun a run forkLe near total perIncrement totalOk perOk => ?_⟩
  obtain ⟨af, as⟩ := a
  have sameFork : af = fork := Internal.fork_eq_of_run run Run.nil forkLe
  subst sameFork
  simp only at near totalOk perOk ⊢
  exact rateAll (fromFin.append run) (by omega) total perIncrement totalOk perOk

/-- The pin's rate bounds the reward rate at every state of a prefix of C's tail.

The prefix ends at most one epoch after the call.

Each state of its balance path is the end of a run from the finalized block.

So the guard applies. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_rate_pre (h : Setting config
  checks g split fin pulled anc counted V)
    {a : BeaconState preset fork} (pre : Run config checks ⟨fork, split⟩ ⟨fork, a⟩)
    (near : (getCurrentEpoch a).toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      ∀ z ∈ pre.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨P, hP, rate⟩ := Internal.key_rate_forked h
  refine ⟨P, hP, fun z member total perIncrement totalOk perOk => ?_⟩
  obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint pre Run.nil
    (show (⟨fork, a⟩ : ForkedBeaconState preset).fork ≤
      (⟨fork, split⟩ : ForkedBeaconState preset).fork from Nat.le_refl _) member
  have order : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch a).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
  exact rate z r1 (fork_le_of_chainSteps r2.chainSteps) (by omega) total perIncrement totalOk
    perOk

/-- The depth times the reward rate for each increment stays below an eleventh of an increment.

It follows from the second test of the low rate at an aligned bound.

Its units are the gwei of the reward, scaled by the weight denominator. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.rate_per_increment (I WD F P e0 D :
  ℕ) (hI : 0 < I) (hWD : 0 < WD)
    (alignedE : e0 % I = 0) (rateLow : 11 * D * (e0 / I * P * F / WD + 1) ≤ e0) :
    11 * D * (P * F) < WD * I := by
  rcases Nat.eq_zero_or_pos D with zero | pos
  · subst zero
    simpa using Nat.mul_pos hWD hI
  · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero alignedE
    have e : e0 / I = m := by rw [hm, Nat.mul_div_cancel_left _ hI]
    rw [e] at rateLow
    have big : 11 ≤ e0 := Nat.le_trans (by
      have := Nat.mul_le_mul (show 11 ≤ 11 * D by omega)
        (Nat.le_add_left 1 (m * P * F / WD))
      simpa using this) rateLow
    have mPos : 0 < m := Nat.pos_of_ne_zero (fun z => by rw [z] at hm; omega)
    have a : m * P * F < WD * (m * P * F / WD + 1) := Nat.lt_mul_div_succ _ hWD
    have b := Nat.mul_lt_mul_of_pos_left a (show 0 < 11 * D by omega)
    have d := Nat.mul_le_mul_left WD rateLow
    have f : (11 * D * (P * F)) * m < (WD * I) * m := by
      calc (11 * D * (P * F)) * m = 11 * D * (m * P * F) := by ring
        _ < 11 * D * (WD * (m * P * F / WD + 1)) := b
        _ = WD * (11 * D * (m * P * F / WD + 1)) := by ring
        _ ≤ WD * e0 := d
        _ = (WD * I) * m := by rw [hm]; ring
    exact Nat.lt_of_mul_lt_mul_right f

/-- The base reward per increment is at least four.

The root of a quarter total is below `2 ^ 31`.

And `rewardScale` makes the scaled factor at least `2 ^ 35`.

Below the small total the root is at most a fifth of an increment, which the factor covers.

The read succeeds, since the quarter total is positive and `fits` bounds the scaled factor. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.four_le_perIncrement (h : Setting
  config checks g split fin pulled anc counted V) :
    4 ≤ (pinTerms config pulled anc fin).perIncrement := by
  have definition : (pinTerms config pulled anc fin).perIncrement =
      ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat := rfl
  obtain ⟨q, hq⟩ : ∃ q : Gwei, q = (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5) := ⟨_, rfl⟩
  rw [← hq] at definition
  have small : q.toNat < 2 ^ 62 ∨ 5 * q.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [hq]
    split_ifs
    · left
      have : ((getTotalActiveBalance pulled).toOption.getD 0).toNat < 2 ^ 64 :=
        ((getTotalActiveBalance pulled).toOption.getD 0).toNat_lt
      rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
    · right
      rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
  have room := h.facts.rewardScale
  have reward := (Internal.PinPresetFacts.reward h.facts)
  have positive : 0 < q.toNat := by
    have size := h.facts.incrementSize
    rw [hq]
    split_ifs
    · rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
    · rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
  obtain ⟨per, computed⟩ :=
    DirectSafety.Apriori.Internal.perIncrement_exists positive h.facts.fits
  rw [computed] at definition
  simp only [Except.toOption, Option.getD_some] at definition
  have formula := toNat_getBaseRewardPerIncrement computed
  have rootPos : 0 < q.toNat.sqrt := Nat.sqrt_pos.mpr positive
  have rootSmall : 4 * q.toNat.sqrt ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat := by
    rcases small with low | tiny
    · have : q.toNat.sqrt < 2 ^ 31 := Nat.sqrt_lt'.mpr (by norm_num at low ⊢; omega)
      omega
    · have : q.toNat.sqrt ≤ q.toNat := Nat.sqrt_le_self _
      have : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat :=
        Nat.le_mul_of_pos_right _ reward
      omega
  have four : 4 ≤ per.toNat := by
    rw [formula]
    exact (Nat.le_div_iff_mul_le rootPos).mpr rootSmall
  rw [definition]
  exact four

/-- The gain on a positive number of increments is below an eleventh of them.

The rate for each increment is the one that `rate_per_increment` bounds. -/
private theorem gain_lt (I WD F P D k : ℕ) (hk : 0 < k)
    (key : 11 * D * (P * F) < WD * I) : 11 * (D * (k * P * F / WD)) < I * k := by
  have fl : WD * (k * P * F / WD) ≤ k * P * F := Nat.mul_div_le _ _
  have h1 : WD * (11 * (D * (k * P * F / WD))) < WD * (I * k) :=
    calc WD * (11 * (D * (k * P * F / WD))) = 11 * D * (WD * (k * P * F / WD)) := by ring
      _ ≤ 11 * D * (k * P * F) := Nat.mul_le_mul_left _ fl
      _ = k * (11 * D * (P * F)) := by ring
      _ < k * (WD * I) := Nat.mul_lt_mul_of_pos_left key hk
      _ = WD * (I * k) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

/-- The gain on a credit rounded up to an increment is at most an eleventh of the credit.

The credit is a whole number of increments, so its rounding up is itself. -/
private theorem gain_credit_le (I WD F P D C : ℕ) (hI : 0 < I)
    (alignedC : C % I = 0) (key : 11 * D * (P * F) < WD * I) :
    11 * (D * ((C + I - 1) / I * P * F / WD)) ≤ C := by
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero alignedC
  subst hu
  rw [show (I * u + I - 1) / I = u from smul_ceilDiv (β := Nat) hI u]
  rcases Nat.eq_zero_or_pos u with zero | pos
  · subst zero
    simp
  · exact (gain_lt I WD F P D u pos key).le

/-- The gain at the stake `e0 + C` over `k` epochs splits into two parts.

They are the gain on the credits and the gain at the base stake `e0`.

The floor costs one unit per epoch. -/
private theorem gain_split_flat (I WD F P e0 C k depth : ℕ) (hI : 0 < I) (hk : k ≤ depth)
    (alignedE : e0 % I = 0) (alignedC : C % I = 0) :
    k * ((e0 + C) / I * P * F / WD) ≤
      depth * ((C + I - 1) / I * P * F / WD) + (depth * (e0 / I * P * F / WD) + depth) := by
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero alignedE
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero alignedC
  rw [← Nat.mul_add, Nat.mul_div_cancel_left _ hI, Nat.mul_div_cancel_left _ hI,
    show (I * b + I - 1) / I = b from smul_ceilDiv (β := Nat) hI b]
  have floor := Nat.add_div_le_div_add_div_add_one (a * P * F) (b * P * F) WD
  have split : (a + b) * P * F = a * P * F + b * P * F := by ring
  rw [split]
  calc k * ((a * P * F + b * P * F) / WD)
      ≤ depth * ((a * P * F + b * P * F) / WD) := Nat.mul_le_mul_right _ hk
    _ ≤ depth * (a * P * F / WD + b * P * F / WD + 1) := Nat.mul_le_mul_left _ floor
    _ = depth * (b * P * F / WD) + (depth * (a * P * F / WD) + depth) := by ring

/-- The gain of one key's flows is at most the linear rate of the flows.

It drops the floor of the increments and the floor of the rate. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.gain_lin (I WD FP D Z : ℕ) :
    10 * (I * WD) * (D * (11 * Z / (10 * I) * FP / WD)) ≤ 11 * D * FP * Z := by
  have floorLe : WD * (11 * Z / (10 * I) * FP / WD) ≤ 11 * Z / (10 * I) * FP :=
    Nat.mul_div_le _ _
  have increments : 10 * I * (11 * Z / (10 * I)) ≤ 11 * Z := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  calc 10 * (I * WD) * (D * (11 * Z / (10 * I) * FP / WD))
      = 10 * I * D * (WD * (11 * Z / (10 * I) * FP / WD)) := by ring
    _ ≤ 10 * I * D * (11 * Z / (10 * I) * FP) := Nat.mul_le_mul_left _ floorLe
    _ = D * FP * (10 * I * (11 * Z / (10 * I))) := by ring
    _ ≤ D * FP * (11 * Z) := Nat.mul_le_mul_left _ increments
    _ = 11 * D * FP * Z := by ring

/-- The gain on whole increments of a stake, at eleven tenths, is at most a tenth of the stake.

The rate for each increment is the one that `rate_per_increment` bounds. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.gain_tenth (I WD F P D Zr : ℕ)
    (key : 11 * D * (P * F) < WD * I) :
    D * (11 * Zr / (10 * I) * P * F / WD) ≤ Zr / 10 := by
  have lin := Internal.gain_lin I WD (P * F) D Zr
  rw [Nat.mul_assoc (11 * Zr / (10 * I)) P F]
  generalize D * (11 * Zr / (10 * I) * (P * F) / WD) = G at lin ⊢
  have pos : 0 < I * WD := by
    have := Nat.lt_of_le_of_lt (Nat.zero_le _) key
    rwa [Nat.mul_comm] at this
  have rate : 11 * D * (P * F) * Zr ≤ WD * I * Zr := Nat.mul_le_mul_right Zr key.le
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  refine Nat.le_of_mul_le_mul_left ?_ pos
  calc I * WD * (G * 10) = 10 * (I * WD) * G := by ring
    _ ≤ 11 * D * (P * F) * Zr := lin
    _ ≤ WD * I * Zr := rate
    _ = I * WD * Zr := by ring

/-- The gain at the base stake, with its tenth, is within `rise`'s gain slack. -/
private theorem base_absorb (D Df q : ℕ) (hDf : D ≤ Df) :
    D * q + D + (D * q + D) / 10 ≤ Df * ((11 * q + 9) / 10 + 3) := by
  have step : 11 * q ≤ 10 * ((11 * q + 9) / 10) := by omega
  have scaled := Nat.mul_le_mul_left D step
  have left : D * (11 * q) = 11 * (D * q) := by ring
  have right : D * (10 * ((11 * q + 9) / 10)) = 10 * (D * ((11 * q + 9) / 10)) := by ring
  have widen := Nat.mul_le_mul_right ((11 * q + 9) / 10 + 3) hDf
  have expand : D * ((11 * q + 9) / 10 + 3) = D * ((11 * q + 9) / 10) + 3 * D := by ring
  omega

/-- The gain of a key's flows and of the base stake is at most its flow gain, a unit and the base.

The joint floor of the flows and the base stake splits by kind with one step.

With no flow there is no step. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_gain_split (I WD F P D Dt Df q
  Zk Z' : ℕ)
    (key : 11 * D * (P * F) < WD * I) (hDt : D ≤ Dt) (hDf : D ≤ Df) (hZ : Zk ≤ Z') :
    D * (11 * (Zk + (D * q + D)) / (10 * I) * P * F / WD) + (D * q + D) ≤
      Dt * (11 * Z' / (10 * I) * P * F / WD) +
        (if 0 < Z' then Dt * (P * F / WD + 2) else 0) + Df * ((11 * q + 9) / 10 + 3) := by
  have tenth := Internal.gain_tenth I WD F P D (D * q + D) key
  have absorb := base_absorb D Df q hDf
  have monoGain : D * (11 * Zk / (10 * I) * P * F / WD) ≤
      Dt * (11 * Z' / (10 * I) * P * F / WD) :=
    Nat.mul_le_mul hDt (Nat.div_le_div_right (Nat.mul_le_mul_right F (Nat.mul_le_mul_right P
      (Nat.div_le_div_right (Nat.mul_le_mul_left 11 hZ)))))
  rcases Nat.eq_zero_or_pos Zk with zero | pos
  · subst zero
    simp only [Nat.zero_add]
    split_ifs <;> omega
  · have posZ : 0 < Z' := Nat.lt_of_lt_of_le pos hZ
    have joint : 11 * (Zk + (D * q + D)) / (10 * I) ≤
        11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1 := by
      have := Nat.add_div_le_div_add_div_add_one (11 * Zk) (11 * (D * q + D)) (10 * I)
      rwa [← Nat.mul_add] at this
    have step : D * (11 * (Zk + (D * q + D)) / (10 * I) * P * F / WD) ≤
        D * ((11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1) * P * F / WD) :=
      Nat.mul_le_mul_left D (Nat.div_le_div_right (Nat.mul_le_mul_right F
        (Nat.mul_le_mul_right P joint)))
    have split : (11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1) * P * F =
        11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F + P * F := by ring
    have floors : (11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F + P * F) /
        WD ≤ 11 * Zk / (10 * I) * P * F / WD + 11 * (D * q + D) / (10 * I) * P * F / WD +
          P * F / WD + 2 := by
      have one := Nat.add_div_le_div_add_div_add_one
        (11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F) (P * F) WD
      have two := Nat.add_div_le_div_add_div_add_one (11 * Zk / (10 * I) * P * F)
        (11 * (D * q + D) / (10 * I) * P * F) WD
      omega
    rw [split] at step
    have wide := Nat.mul_le_mul_left D floors
    have expand : ∀ A B C : ℕ, D * (A + B + C + 2) = D * A + D * B + D * C + 2 * D :=
      fun A B C => by ring
    rw [expand] at wide
    have unit : D * (P * F / WD + 2) ≤ Dt * (P * F / WD + 2) := Nat.mul_le_mul_right _ hDt
    have unitSplit : D * (P * F / WD + 2) = D * (P * F / WD) + 2 * D := by ring
    simp only [posZ, ↓reduceIte]
    omega

/-- The closure test of the credit ceiling with the credits rounded down to increments.

The stake above `e0` is the credits, the slack `W` and the gain at the base stake.

The gain on the rounded credits is at most an eleventh of them.

Rounding down leaves less than an increment of that stake unrounded.

The increment of the bound covers it. -/
private theorem ceiling_closed_floor (I WD F P e0 D Cr Cr' S W C q : ℕ)
    (hq : q = e0 / I * P * F / WD) (hI : 0 < I) (key : 11 * D * (P * F) < WD * I)
    (hC : C = I * (11 * (Cr' + W + D * q + D) / (10 * I))) (start : S + Cr ≤ e0 + Cr' + W) :
    S + Cr + (D * ((C + I - 1) / I * P * F / WD) + (D * q + D)) < e0 + C + I := by
  subst hq
  have alignedC : C % I = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  have credit := gain_credit_le I WD F P D C hI alignedC key
  have div := Nat.div_add_mod (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D)) (10 * I)
  have lt := Nat.mod_lt (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D)) (show 0 < 10 * I by omega)
  have times : 10 * I * (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D) / (10 * I)) = 10 * C := by
    rw [hC]
    ring
  omega

/-- The arithmetic of the credit ceiling, for any run.

The bound `e0` on the effective balance, with the credits rounded down to increments, is closed.

The gain of any number of epochs up to the depth is at most the gain at the depth.

That gain is a tenth of the credits, the slack and the gain at the base stake. -/
private theorem ceiling_arith (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (P depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    (e0 + C) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) <
        e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
      (∀ k, k ≤ depth → k * ((e0 + C) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ≤
        Internal.gainOn preset depth P C + (depth * q + depth)) ∧
      Internal.gainOn preset depth P C = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * Internal.gainOn preset depth P C ≤ Cr' + W + depth * q + depth := by
  have closed := ceiling_closed_floor preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat F P e0 depth Cr Cr' S W C q hq incPos key hC start
  have alignedC : C % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  have credit := gain_credit_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat F P depth C incPos alignedC key
  have rounded := Nat.mul_div_le (11 * (Cr' + W + depth * q + depth))
    (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
  have times : 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) =
        10 * C := by
    rw [hC]
    ring
  subst hF
  have alignedE : (e0 + C) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero alignedE0)
      (Nat.dvd_of_mod_eq_zero alignedC))
  refine ⟨alignedE, closed, fun k within => ?_, ?_, ?_⟩
  · have split := gain_split_flat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 C k depth
      incPos within alignedE0 alignedC
    rw [← hq] at split
    exact split
  · unfold Internal.gainOn
    let I := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let u := 11 * (Cr' + W + depth * q + depth) / (10 * I)
    have quotient : (I * u + I - 1) / I = u := smul_ceilDiv (β := Nat) incPos u
    rw [hC, quotient]
  · unfold Internal.gainOn
    omega

/-- A key's balance along a run is at most a stake bound, its credits and the gain at the bound.

The bound `e0` on the effective balance, with the credits rounded down to increments, is closed.

The stake above `e0` is the credits, the slack `W` and the gain at the base stake.

The rate premise is that of the low regime, at the depth of the call.

The gain on the rounded credits is at most a tenth of that stake. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.c_ceiling_abstract {n y :
  ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P capHigh : ℕ)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ capHigh)
    (capCeil : ∀ z ∈ post.balancePath, PinTerms.capAt z i ≤ capHigh)
    (rate : ∀ z ∈ post.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt n i) capHigh ≤ S)
    (startEff : effectiveAt n i ≤ e0 + C)
    (credits : Internal.netScan i high post +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post) ≤ Cr)
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    ∃ gc, gc = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ Cr' + W + depth * q + depth ∧
      (∀ z ∈ post.balancePath, min (actualBalanceAt z i) capHigh ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      effectiveAt y i ≤ e0 + C := by
  obtain ⟨alignedE, closed, splitAll, hform, hten⟩ := ceiling_arith incPos P depth Cr Cr' e0 C S W F
    q hF hq alignedE0 hC key start
  subst hF
  have split := splitAll _ epochs
  have bound : Internal.creditBound post i high (e0 + C) P capHigh ≤
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) := by
    unfold Internal.creditBound
    exact le_trans (le_of_eq (by ring)) (Nat.add_le_add (Nat.add_le_add startBal credits) split)
  have fixpoint : max (effectiveAt n i) (min capHigh
      (Internal.creditBound post i high (e0 + C) P capHigh -
        Internal.creditBound post i high (e0 + C) P capHigh %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le startEff (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt bound closed)))
  obtain ⟨-, -, third, fourth⟩ := Internal.Run.effective_floor_pair post early fulu i inside 0 0
    capHigh high (e0 + C) P
  have balances := fourth alignedCap startCap capCeil (fun z member => .inr (rate z member))
    endEpoch fixpoint
  refine ⟨Internal.gainOn preset depth P C, hform, hten,
    fun z member => Nat.le_trans (balances z member) bound, ?_⟩
  · refine Nat.le_trans (third _ alignedCap startCap balances capCeil).1 ?_
    rw [Nat.min_comm]
    exact fixpoint

/-- A key's balance along a run that makes it compound has the ceiling of a run with one cap.

The run splits at the step that makes the key compound.

Before the step the balance counts up to `lo`, and after it up to `hi`.

The ceiling is that of `c_ceiling_abstract`, with the credits of the step added.

The step leaves its balance within the smaller of its balance before it and `lo`, plus its credits.

So the balance after the step is at most the ceiling before it, plus the credits of the step.

Both parts take the same closed bound `e0 + C`, and their epochs add up to those of the run. -/
private theorem c_ceiling_abstract_flip {x m n y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m n) (post : Run config checks n y)
    (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (high P lo hi : ℕ)
    (alignedLo : lo % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (alignedHi : hi % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0) (loLe : lo ≤ hi)
    (startCap : effectiveAt x i ≤ lo)
    (capsPre : ∀ z ∈ pre.balancePath, PinTerms.capAt z i ≤ lo)
    (capsPost : ∀ z ∈ post.balancePath, PinTerms.capAt z i ≤ hi)
    (rate : ∀ z, z ∈ pre.balancePath ∨ z ∈ post.balancePath → ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt x i) lo ≤ S)
    (startEff : effectiveAt x i ≤ e0 + C)
    (junction : actualBalanceAt n i ≤ min (actualBalanceAt m i) lo +
      Internal.stepCredit (fun _ => true) (fun _ => true) i step)
    (keepEff : effectiveAt n i = effectiveAt m i)
    (credits : Internal.netScan i high pre + (Internal.creditScan (fun _ => false)
        (fun s => decide (s ≠ .rewards)) i high pre) +
      Internal.stepCredit (fun _ => true) (fun _ => true) i step + Internal.netScan i high post +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post) ≤ Cr)
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    ∃ gc, gc = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ Cr' + W + depth * q + depth ∧
      (∀ z ∈ pre.balancePath, min (actualBalanceAt z i) lo ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      (∀ z ∈ post.balancePath, min (actualBalanceAt z i) hi ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      effectiveAt y i ≤ e0 + C := by
  obtain ⟨alignedE, closed, splitAll, hform, hten⟩ := ceiling_arith incPos P depth Cr Cr' e0 C S W F
    q hF hq alignedE0 hC key start
  subst hF
  have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
  have epochPre := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have epochPost := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have forkM : m.fork < .glamsterdam := Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps) early
  have fuluN : .fusaka ≤ n.fork :=
    Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
  have insideN : i < n.state.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps (pre.snoc step).chainSteps)
  have split := splitAll ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat +
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat)) (by omega)
  rw [Nat.add_mul] at split
  have boundPre : Internal.creditBound pre i high (e0 + C) P lo ≤
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) := by
    unfold Internal.creditBound
    omega
  have fixPre : max (effectiveAt x i) (min lo (Internal.creditBound pre i high (e0 + C) P lo -
      Internal.creditBound pre i high (e0 + C) P lo %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le startEff (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt boundPre closed)))
  obtain ⟨-, -, thirdPre, fourthPre⟩ := Internal.Run.effective_floor_pair pre
    forkM fulu i inside 0 0 lo high (e0 + C) P
  have balPre := fourthPre alignedLo startCap capsPre
    (fun z member => .inr (rate z (.inl member))) (by omega) fixPre
  obtain ⟨front, atLast⟩ := Run.balancePath_last pre
  have mPre : min (actualBalanceAt m i) lo ≤
      Internal.creditBound pre i high (e0 + C) P lo :=
    balPre m (by rw [atLast]; simp)
  have effM : effectiveAt m i ≤ e0 + C := by
    refine Nat.le_trans (thirdPre _ alignedLo startCap balPre capsPre).1 ?_
    rw [Nat.min_comm]
    exact fixPre
  have effLo : effectiveAt m i ≤ lo := by
    have := (thirdPre _ alignedLo startCap balPre capsPre).1
    omega
  have boundPost : Internal.creditBound post i high (e0 + C) P hi ≤
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) := by
    unfold Internal.creditBound at mPre ⊢
    omega
  have fixPost : max (effectiveAt n i) (min hi (Internal.creditBound post i high (e0 + C) P hi -
      Internal.creditBound post i high (e0 + C) P hi %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le (keepEff ▸ effM) (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt boundPost closed)))
  obtain ⟨-, -, thirdPost, fourthPost⟩ := Internal.Run.effective_floor_pair post early fuluN i
    insideN 0 0 hi high (e0 + C) P
  have balPost := fourthPost alignedHi (by omega) capsPost
    (fun z member => .inr (rate z (.inr member))) endEpoch fixPost
  refine ⟨Internal.gainOn preset depth P C, hform, hten,
    fun z member => Nat.le_trans (balPre z member) boundPre,
    fun z member => Nat.le_trans (balPost z member) boundPost, ?_⟩
  refine Nat.le_trans (thirdPost _ alignedHi (by omega) balPost capsPost).1 ?_
  rw [Nat.min_comm]
  exact fixPost

open DirectSafety.Apriori.Internal in
/-- The cap that `rise` reads: the key's own cap when its gain is low, else the largest. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capFor_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ) :
    (pinTerms config state ancestor finalizedState).capFor i =
      if (decide ((pinTerms config state ancestor finalizedState).depthFin *
            ((11 * (pinTerms config state ancestor finalizedState).gainRate i + 9) / 10 + 3) <
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) &&
          decide (11 * (pinTerms config state ancestor finalizedState).depth *
              ((pinTerms config state ancestor finalizedState).gainRate i + 1) ≤
            (pinTerms config state ancestor finalizedState).ebUp i)) = true then
        PinTerms.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := rfl

/-- The cap that `rise` reads is at least the key's own cap. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capAt_le_capFor (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ)
    (capMax : PinTerms.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    PinTerms.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i ≤
      (pinTerms config state ancestor finalizedState).capFor i := by
  rw [Internal.capFor_eq]
  split
  · exact Nat.le_refl _
  · exact capMax

/-- The rise of a key on its kept arm is the least of its cap, its rounded top and its headroom.

The rounded top adds the downward band to `high`.

The headroom starts from the finalized balance.

The rise is that less the effective balance at R. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.rise_kept (config : Config) (pulled
  anc fin : BeaconState preset fork) (i : ℕ)
    {H : ℕ} (hH : H = (pinTerms config pulled anc fin).high i)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    (pinTerms config pulled anc fin).rise i =
      min ((pinTerms config pulled anc fin).capFor i)
        (min (H + preset.downwardBand - (H + preset.downwardBand) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          (max (balanceAt fin i) (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
        balanceAt pulled i := by
  have unfold : (pinTerms config pulled anc fin).rise i =
      if (pinTerms config pulled anc fin).keptArm i = true then
        min ((pinTerms config pulled anc fin).capFor i)
          (min (H + preset.downwardBand - (H + preset.downwardBand) %
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
            (max (balanceAt fin i) (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
          balanceAt pulled i
      else (pinTerms config pulled anc fin).capFor i - balanceAt pulled i := by
    rw [hH]
    rfl
  rw [unfold]
  split
  · rfl
  · exact absurd kept ‹_›

/-- A key on its kept arm has an effective balance within its rise, the flows and their slack.

The key's effective balance stays at that of R, ends at its start, or is within the ceiling.

The ceiling is within `high` and the flows, and the slack is paid when there are flows.

It starts from any state: `start` bounds the effective balance there.

A key that ends at its start has `start` within the cap and within the rounded top of `H`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.rise_close (config : Config)
  (pulled anc fin : BeaconState preset fork) (i : ℕ)
    {H : ℕ} (hH : H = (pinTerms config pulled anc fin).high i)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm i = true)
    {eC Bc S U start capHigh : ℕ}
    (alignedC : eC % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startLe : start ≤ max (balanceAt fin i)
      ((H + S) - (H + S) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (stay : eC = balanceAt pulled i ∨
      (eC ≤ start ∧ start ≤ (pinTerms config pulled anc fin).capFor i + S + U ∧
        start ≤ (H + preset.downwardBand) -
          (H + preset.downwardBand) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat + S + U) ∨
      (eC ≤ Bc + preset.downwardBand ∧
        eC ≤ max start (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh)))
    (capped : eC ≤ (pinTerms config pulled anc fin).capFor i + S + U)
    (ceiling : Bc ≤ H + S)
    (slack : S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
      (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) :
    eC ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i + S + U := by
  rw [Internal.rise_kept config pulled anc fin i hH kept]
  have arith := rise_arith (finEB := max (balanceAt fin i)
      (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (capFor := (pinTerms config pulled anc fin).capFor i) incPos
    stay (Nat.le_trans startLe (max_le_max (Nat.le_max_left _ _) (Nat.le_refl _))) alignedC
    capped ceiling slack
  rwa [max_assoc, max_self] at arith

/-- The bound `ebUp` on a key's effective balance is its largest balance or its rounded top.

The top adds the leak at the cap, the net partials and a band to the balance at R.

It reads the partials through `dueAmount`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.ebUp_eq (config : Config) (pulled
  anc fin : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i t : ℕ)
    (ht : t = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (pinTerms config pulled anc fin).leakAt
          (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i +
      (PinTerms.dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
        PinTerms.dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1)) +
      preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) :
    (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  subst ht
  simp only [pinTerms, PinTerms.dueAmount, electra, ↓reduceDIte]
  rfl

/-- The least and the greatest of two whole numbers of increments are such numbers too. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.min_max_aligned {inc a b : ℕ} (ha :
  a % inc = 0) (hb : b % inc = 0) :
    min a b % inc = 0 ∧ max a b % inc = 0 :=
  ⟨by rcases min_choice a b with e | e <;> rw [e] <;> assumption,
    by rcases max_choice a b with e | e <;> rw [e] <;> assumption⟩

/-- A number rounded down to an increment is a whole number of increments. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.round_aligned (inc x : ℕ) : (x - x
  % inc) % inc = 0 :=
  Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

/-- The effective balances of a key at R and at the finalized state are aligned. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.balances_aligned (h : Setting
  config checks g split fin pulled anc counted V)
    (i : ℕ) : balanceAt pulled i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
      balanceAt fin i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  exact ⟨DirectSafety.Apriori.Internal.FloorTrace.effective_aligned
    (shared.append (fromFin.append toPulled)) h.genesis h.aligned i,
    DirectSafety.Apriori.Internal.FloorTrace.effective_aligned shared h.genesis h.aligned i⟩

/-- The aligned effective balances make the bound `ebUp` of a key a whole number of increments. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.ebUp_aligned (h : Setting config
  checks g split fin pulled anc counted V) (i : ℕ) :
    (pinTerms config pulled anc fin).ebUp i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨a1, a2⟩ := Internal.balances_aligned h i
  obtain ⟨t, ht⟩ : ∃ t, (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, Internal.ebUp_eq config pulled anc fin electra i _ rfl⟩
  have capAligned : PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    cases found : pulled.validators.data[i]? with
    | none => simp [PinTerms.capAt, found]
    | some w =>
      exact Internal.capAt_aligned h.aligned (z := (⟨fork, pulled⟩ : ForkedBeaconState preset))
        electra found
  rw [ht]
  exact (Internal.min_max_aligned (Internal.min_max_aligned a1 a2).2
    (Internal.min_max_aligned capAligned (Internal.round_aligned _ t)).1).2

/-- A call's cutoff is within the withdrawal delay of the finalized state. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.window_short (h : Setting config
  checks g split fin pulled anc counted V) :
    (getCurrentEpoch pulled).toNat + 1 <
      (getCurrentEpoch fin).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  have shallow := h.shallow
  omega

/-- The due amounts of a key are those of the entries that name it and are due, in two filters. -/
private theorem dueAmount_eq (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (v : ValidatorIndex) (cutoff : ℕ) :
    PinTerms.dueAmount state electra v.toNat cutoff =
      ((((state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum := by
  unfold PinTerms.dueAmount
  simp only [List.filter_filter]
  congr 3
  funext entry
  simp [Bool.decide_and, UInt64.toNat_inj, Bool.and_comm]

/-- The leak of the pin does not fall as the effective balance rises. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.leakAt_mono (config : Config)
  (pulled anc fin : BeaconState preset fork) {a b : ℕ}
    (i : ℕ) (le : a ≤ b) :
    (pinTerms config pulled anc fin).leakAt a i ≤ (pinTerms config pulled anc fin).leakAt b i := by
  unfold pinTerms
  dsimp only
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right le)))
    (Nat.div_le_div_right (Nat.mul_le_mul_right _ le))

/-- The leak of the pin at the finalized state's score, spelled out.

The score is the key's inactivity score at the finalized state, or zero before Altair. -/
private theorem leakAt_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (eb i : ℕ) :
    (pinTerms config pulled anc fin).leakAt eb i =
      2 * (eb / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config pulled anc fin).perIncrement) +
      eb * ((if altair : .altair ≤ fork then
          (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
        (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  unfold pinTerms
  rfl

/-- A key's inactivity score at the finalized state is at most the largest score there. -/
private theorem score_le_scoreMax (fin : BeaconState preset fork) (i : ℕ) :
    (if altair : .altair ≤ fork then
        (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) ≤
      (if altair : .altair ≤ fork then
        ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) := by
  split
  · rename_i altair
    cases found : (fin.inactivityScores altair).data[i]? with
    | none => simp
    | some x =>
      have mem : x.toNat ∈ (fin.inactivityScores altair).data.toList.map (·.toNat) :=
        List.mem_map_of_mem (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
      rw [List.foldl_max_eq_max (List.ne_nil_of_mem mem)]
      exact le_max_of_le_right (List.le_max_of_mem mem)
  · exact Nat.le_refl _

/-- Raising the balance by whole increments raises the leak by an amount in those increments.

The amount is the leak of the increments at the key's per-increment reward and the largest score.

It is rounded up once. -/
private theorem leakAt_add_le (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (i eb m : ℕ) :
    (pinTerms config pulled anc fin).leakAt (eb + preset.EFFECTIVE_BALANCE_INCREMENT.toNat * m) i ≤
      (pinTerms config pulled anc fin).leakAt eb i +
        2 * ((pinTerms config pulled anc fin).perIncrement * m) +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * m *
          ((pinTerms config pulled anc fin).scoreMaxFin +
            (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) + 1) := by
  have scoreMax : (pinTerms config pulled anc fin).scoreMaxFin = (if altair : .altair ≤ fork then
      ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) := by
    unfold pinTerms
    rfl
  rw [leakAt_eq, leakAt_eq, scoreMax]
  have score := score_le_scoreMax fin i
  generalize (if altair : .altair ≤ fork then
    (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) = S at score ⊢
  generalize (if altair : .altair ≤ fork then
    ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) = M at score ⊢
  generalize (pinTerms config pulled anc fin).perIncrement = P
  generalize (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat = B
  generalize config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = Q
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = inc at incPos ⊢
  have quotient : (eb + inc * m) / inc = eb / inc + m := by
    rw [Nat.add_mul_div_left _ _ incPos]
  have rounded : (eb + inc * m) * (S + B) / Q ≤ eb * (S + B) / Q + inc * m * (S + B) / Q + 1 := by
    rw [Nat.add_mul]
    exact Nat.add_div_le_div_add_div_add_one _ _ _
  have larger : inc * m * (S + B) / Q ≤ inc * m * (M + B) / Q :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right score _))
  have step : 2 * ((eb / inc + m) * P) = 2 * (eb / inc * P) + 2 * (P * m) := by ring
  rw [quotient, step]
  generalize eb / inc * P = x at *
  generalize (eb + inc * m) * (S + B) / Q = u at *
  generalize eb * (S + B) / Q = v at *
  generalize inc * m * (S + B) / Q = w at *
  generalize inc * m * (M + B) / Q = z at *
  omega

/-- The leak that a rise above `ebUp` by `a` increments of debits and `s` of a penalty induces.

The debits cost the leak of their increments at the key's reward, and the penalty one increment.

A debited key pays one more for the rounding, which the reward of an increment covers. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.inducedR_le (config : Config)
  (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) (i a s : ℕ) (slack : s ≤ 1)
    (envelope : ∀ z ∈ tail.balancePath, effectiveAt z i ≤
      (pinTerms config pulled anc fin).ebUp i +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (a + s)) :
    Internal.inducedR (pinTerms config pulled anc fin) tail i ≤
      (pinTerms config pulled anc fin).depthFin *
          (3 * (pinTerms config pulled anc fin).perIncrement * a +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a *
              ((pinTerms config pulled anc fin).scoreMaxFin +
                (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)) +
        s * (pinTerms config pulled anc fin).slashLeak := by
  have fold : ∀ (l : List ℕ) (b c : ℕ), b ≤ c → (∀ x ∈ l, x ≤ c) → l.foldl max b ≤ c := by
    intro l
    induction l with
    | nil => exact fun _ _ le _ => le
    | cons x xs ih =>
      exact fun b c le all => ih _ c (max_le le (all x List.mem_cons_self))
        fun y m => all y (List.mem_cons_of_mem _ m)
  have mono := Internal.leakAt_mono config pulled anc fin i (fold _ 0 _ (Nat.zero_le _) fun v member
    => by
    obtain ⟨z, inPath, rfl⟩ := List.mem_map.mp member
    exact envelope z inPath)
  have first := leakAt_add_le config pulled anc fin incPos i
    ((pinTerms config pulled anc fin).ebUp i) a
  have second := leakAt_add_le config pulled anc fin incPos i
    ((pinTerms config pulled anc fin).ebUp i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a) s
  have rate : (pinTerms config pulled anc fin).perIncrement * a ≥ 1 ∨ a = 0 := by
    rcases Nat.eq_zero_or_pos a with zero | pos
    · exact .inr zero
    · exact .inl (Nat.mul_pos perPos pos)
  rw [Nat.mul_add, ← Nat.add_assoc] at mono
  by_cases withdrawn : (pinTerms config pulled anc fin).withdrawnRB i = true
  · rw [Internal.inducedR_of_withdrawn _ tail i withdrawn]
    exact Nat.zero_le _
  rw [Internal.inducedR_of_not_withdrawn _ tail i (by simpa using withdrawn)]
  have leakEq : (pinTerms config pulled anc fin).slashLeak =
      (pinTerms config pulled anc fin).depthFin *
        (2 * (pinTerms config pulled anc fin).perIncrement +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
              ((pinTerms config pulled anc fin).scoreMaxFin +
                (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
            (config.INACTIVITY_SCORE_BIAS.toNat *
              (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) + 1) := rfl
  rw [leakEq, Nat.mul_left_comm s, ← Nat.mul_add]
  refine Nat.mul_le_mul_left _ ?_
  have three : 3 * (pinTerms config pulled anc fin).perIncrement * a =
      3 * ((pinTerms config pulled anc fin).perIncrement * a) := by ring
  have n1 := Nat.zero_le (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
  have n2 := Nat.zero_le (preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp slack with rfl | rfl <;>
    rcases rate with rate | rfl <;>
    simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
      Nat.zero_div] at mono first second three n1 ⊢ <;>
    omega

/-- A key's cap does not fall along a run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cap_le_cap_of_run (caps : CapOrder
  preset) {z y : ForkedBeaconState preset}
    (post : Run config checks z y) (early : y.fork < .glamsterdam) (i : ℕ) :
    PinTerms.capAt z i ≤ PinTerms.capAt y i := by
  unfold PinTerms.capAt
  cases found : z.state.validators.data[i]? with
  | none => simp
  | some w =>
    obtain ⟨w', found', mono⟩ := post.validatorCap_mono caps.activation caps.compounding early i
      w found
    simp only [found', Option.map_some, Option.getD_some]
    exact UInt64.le_iff_toNat_le.mp mono

/-- A key's effective balance at the end of a run from genesis is at most its cap there.

The cap is the one at that state. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.effective_le_cap_at {g z :
  ForkedBeaconState preset}
    (shared : Run config checks g z)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : z.fork < .glamsterdam) (i : ℕ) : effectiveAt z i ≤ PinTerms.capAt z i := by
  cases found : z.state.validators.data[i]? with
  | none => simp [effectiveAt, found]
  | some w =>
    have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared genesis caps
      early found
    simpa [PinTerms.capAt, found] using capped

/-- On R's branch a key's effective balance is at most its cap at R. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.effective_le_cap_pulled (h :
  Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, z⟩)
    (post : Run config checks ⟨fork, z⟩ ⟨fork, pulled⟩) (i : ℕ) :
    effectiveAt (⟨fork, z⟩ : ForkedBeaconState preset) i ≤
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
  obtain ⟨shared⟩ := h.toFin
  exact Nat.le_trans (Internal.effective_le_cap_at (shared.append toZ) h.genesis h.caps h.early i)
    (Internal.cap_le_cap_of_run h.caps post h.early i)

/-- Each state of the balance path of a run on the way to R has an effective balance within R's cap.

The run starts at a state that the finalized block's state reaches, and R follows its end. -/
private theorem path_le_cap_pulled (h : Setting config checks g split fin pulled anc counted V)
    {zs : BeaconState preset fork} {m : ForkedBeaconState preset}
    (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩) (rp : Run config checks ⟨fork, zs⟩ m)
    (rest : Run config checks m ⟨fork, pulled⟩) (i : ℕ) :
    ∀ z ∈ rp.balancePath,
      effectiveAt z i ≤ PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
  intro z member
  obtain ⟨q1, q2, -⟩ := Internal.balancePath_endpoint rp rest (Nat.le_refl _) member
  obtain ⟨zf, zs'⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run q1 q2 (Nat.le_refl _)).symm
  subst same
  exact Internal.effective_le_cap_pulled h (toZ.append q1) q2 i

/-- A state of the balance path of a run between two states of one fork is a state of that fork.

It is the end of a run from the start and the start of a run to the end. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.balancePath_state {a b :
  BeaconState preset fork}
    (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩) {z : ForkedBeaconState preset}
    (member : z ∈ r.balancePath) :
    ∃ zs : BeaconState preset fork, z = ⟨fork, zs⟩ ∧
      Nonempty (Run config checks ⟨fork, a⟩ ⟨fork, zs⟩) ∧
      Nonempty (Run config checks ⟨fork, zs⟩ ⟨fork, b⟩) := by
  obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint r
    (Run.nil : Run config checks ⟨fork, b⟩ ⟨fork, b⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  exact ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩

/-- The cap of a key in the registry is the activation balance, or the largest balance.

Both are a whole number of increments, and the cap is too. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capAt_kind (h : Setting config
  checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (i : ℕ) (within : i < z.validators.data.size) :
    (PinTerms.capAt (⟨fork, z⟩ : ForkedBeaconState preset) i =
        preset.MIN_ACTIVATION_BALANCE.toNat ∨
      PinTerms.capAt (⟨fork, z⟩ : ForkedBeaconState preset) i =
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) ∧
    preset.MIN_ACTIVATION_BALANCE.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨w, found⟩ : ∃ w, z.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem within⟩
  obtain ⟨aMin, aMax⟩ := Internal.cap_values_aligned h.aligned
  refine ⟨?_, aMin, aMax⟩
  rw [Internal.capAt_of_found (z := (⟨fork, z⟩ : ForkedBeaconState preset)) electra found]
  split
  · exact .inr rfl
  · exact .inl rfl

/-- The states of the parts of a run cut at a step are states of the run. -/
private theorem flip_path_mem {x m n y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    {tail : Run config checks x y} (cut : (pre.snoc step).append post = tail) :
    (∀ z ∈ pre.balancePath, z ∈ tail.balancePath) ∧
      ∀ z ∈ post.balancePath, z ∈ tail.balancePath := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [cut] at path
  obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
  refine ⟨fun z member => by rw [path]; simp [Run.balancePath, member], fun z member => ?_⟩
  rw [headPost] at member
  rw [path]
  rcases List.mem_cons.mp member with rfl | inRest
  · simp [Run.balancePath, List.mem_of_mem_getLast? (Step.balancePath_ends step).2]
  · simp [headPost, inRest]

/-- A state of a run cut at a block step is a state of one of the parts. -/
private theorem flip_path_cover {x m n y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    (notSlot : ∀ ok, step ≠ Step.slot ok) {tail : Run config checks x y}
    (cut : (pre.snoc step).append post = tail) :
    ∀ z ∈ tail.balancePath, z ∈ pre.balancePath ∨ z ∈ post.balancePath := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [cut] at path
  have block : step.balancePath = [m, n] := by
    cases step with
    | slot ok => exact absurd rfl (notSlot ok)
    | block => rfl
  obtain ⟨front, atLast⟩ := Run.balancePath_last pre
  obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
  intro z member
  rw [path] at member
  simp only [Run.balancePath, block, headPost, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.tail_cons] at member
  rcases member with (inPre | rfl | rfl) | inRest
  · exact .inl inPre
  · exact .inl (by rw [atLast]; simp)
  · exact .inr (by rw [headPost]; exact List.mem_cons_self)
  · exact .inr (by rw [headPost]; exact List.mem_cons_of_mem _ inRest)

/-- The effective balance of a key along a run is bounded by its capped balance.

The cap of the key may rise once, at a step that makes it compound.

The cap of a key in the registry is the activation balance, or the largest balance if it compounds.

The balance counts up to the cap, so a ceiling on it holds before and after the rise. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.effective_ceiling_flip (h : Setting
  config checks g split fin pulled anc counted V)
    {x y : BeaconState preset fork} (tail : Run config checks ⟨fork, x⟩ ⟨fork, y⟩)
    (invariant : Invariant x) (i : ℕ) (inside : i < x.validators.data.size)
    (ceil capHigh : ℕ)
    (capped : ∀ z ∈ tail.balancePath, effectiveAt z i ≤ PinTerms.capAt z i)
    (capCeil : ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh)
    (balanceCeil : ∀ z ∈ tail.balancePath,
      min (actualBalanceAt z i) (PinTerms.capAt z i) ≤ ceil) :
    effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i ≤
        max (effectiveAt (⟨fork, x⟩ : ForkedBeaconState preset) i)
          (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
      ((getCurrentEpoch y).toNat ≤ (getCurrentEpoch x).toNat →
        effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i =
          effectiveAt (⟨fork, x⟩ : ForkedBeaconState preset) i) ∧
      ((getCurrentEpoch x).toNat < (getCurrentEpoch y).toNat →
        effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i ≤ ceil + preset.downwardBand) ∧
      (getCurrentEpoch x).toNat ≤ (getCurrentEpoch y).toNat := by
  have capOrder := h.caps
  have minMax := UInt64.le_iff_toNat_le.mp capOrder.compounding
  obtain ⟨-, alignedMin, alignedMax⟩ := Internal.capAt_kind h i inside
  -- a run of constant cap `c0`, below `capHigh`, is the constant-cap case
  have seg : ∀ {a b : BeaconState preset fork}
      (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩) (c0 : ℕ),
      c0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → c0 ≤ capHigh →
      i < a.validators.data.size →
      effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i ≤ c0 →
      (∀ z ∈ r.balancePath, PinTerms.capAt z i = c0) →
      (∀ z ∈ r.balancePath, min (actualBalanceAt z i) (PinTerms.capAt z i) ≤ ceil) →
      effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i)
            (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
        ((getCurrentEpoch b).toNat ≤ (getCurrentEpoch a).toNat →
          effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i =
            effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i) ∧
        ((getCurrentEpoch a).toNat < (getCurrentEpoch b).toNat →
          effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤ ceil + preset.downwardBand) ∧
        (getCurrentEpoch a).toNat ≤ (getCurrentEpoch b).toNat := by
    intro a b r c0 aligned le insideA start cap bal
    obtain ⟨p1, p2, p3, p4⟩ := Internal.Run.effective_ceiling_of_balance_ceiling r h.early h.fulu
      i insideA ceil c0 aligned start
      (fun z member => by rw [← cap z member]; exact bal z member)
      (fun z member => (cap z member).le)
    exact ⟨le_trans p1 (max_le_max le_rfl (min_le_min le_rfl le)), p2, p3, p4⟩
  -- the cap of a key in the registry is one of two values
  have kind := fun (z : BeaconState preset fork) (within : i < z.validators.data.size) =>
    (Internal.capAt_kind h i within).1
  obtain ⟨rest, atHead⟩ := Run.balancePath_head tail
  have headMem : (⟨fork, x⟩ : ForkedBeaconState preset) ∈ tail.balancePath := by
    rw [atHead]
    exact List.mem_cons_self
  obtain ⟨last, atLast⟩ := Run.balancePath_last tail
  have lastMem : (⟨fork, y⟩ : ForkedBeaconState preset) ∈ tail.balancePath := by
    rw [atLast]
    simp
  -- a run that ends with the activation cap has the activation cap throughout
  have lowRun : ∀ {a b : BeaconState preset fork} (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩),
      i < a.validators.data.size →
      PinTerms.capAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
        preset.MIN_ACTIVATION_BALANCE.toNat →
      ∀ z ∈ r.balancePath,
        PinTerms.capAt z i = preset.MIN_ACTIVATION_BALANCE.toNat :=
    fun r within atEnd z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩ := Internal.balancePath_state r member
      have hi := Internal.cap_le_cap_of_run h.caps r2 h.early i
      rcases kind zs (Nat.lt_of_lt_of_le within (registryGrows_of_chainSteps r1.chainSteps)) with
        low | high
      · exact low
      · omega
  -- a run that starts above the activation cap has the largest cap throughout
  have highRun : ∀ {a b : BeaconState preset fork} (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩),
      i < a.validators.data.size →
      preset.MIN_ACTIVATION_BALANCE.toNat <
        PinTerms.capAt (⟨fork, a⟩ : ForkedBeaconState preset) i →
      ∀ z ∈ r.balancePath,
        PinTerms.capAt z i = preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
    fun r within atStart z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩ := Internal.balancePath_state r member
      have lo := Internal.cap_le_cap_of_run h.caps r1 h.early i
      rcases kind zs (Nat.lt_of_lt_of_le within (registryGrows_of_chainSteps r1.chainSteps)) with
        low | high
      · omega
      · exact high
  by_cases compoundsEnd : preset.MIN_ACTIVATION_BALANCE.toNat <
      PinTerms.capAt (⟨fork, y⟩ : ForkedBeaconState preset) i
  · by_cases compoundsStart : preset.MIN_ACTIVATION_BALANCE.toNat <
        PinTerms.capAt (⟨fork, x⟩ : ForkedBeaconState preset) i
    · -- the cap is the largest balance along the whole run
      have all := highRun tail inside compoundsStart
      have atX := all _ headMem
      exact seg tail _ alignedMax (by have := capCeil _ headMem; omega) inside
        (by have := capped _ headMem; omega) all balanceCeil
    · -- the cap is the activation balance until the step that makes the key compound
      obtain ⟨m, n, pre, step, post, cut, flatM, largeN, -, sameEpoch⟩ :=
        Internal.Run.flip_split tail h.early h.fulu invariant i
          (by omega) compoundsEnd
      obtain ⟨mf, ms⟩ := m
      obtain ⟨nf, ns⟩ := n
      have sameM : fork = mf :=
        (Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
      have sameN : fork = nf := (Internal.fork_eq_of_run (pre.snoc step) post (Nat.le_refl _)).symm
      subst sameM sameN
      have insideM : i < ms.validators.data.size :=
        Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)
      have insideN : i < ns.validators.data.size :=
        Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps (pre.snoc step).chainSteps)
      obtain ⟨preMem, postMem⟩ := flip_path_mem pre step post cut
      obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
      have nMem := postMem (⟨fork, ns⟩ : ForkedBeaconState preset)
        (by rw [headPost]; exact List.mem_cons_self)
      have capsPre := lowRun pre inside flatM
      have capsPost := highRun post insideN largeN
      have atX := kind x inside
      have atY := kind y (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tail.chainSteps))
      have capX := capCeil _ headMem
      have capY := capCeil _ lastMem
      have effX := capped _ headMem
      have effN := capped _ nMem
      have capN := capsPost _ (by
        rw [headPost]
        exact List.mem_cons_self)
      have first := seg pre _ alignedMin (by omega) inside (by omega) capsPre
        (fun z member => balanceCeil z (preMem z member))
      have second := seg post _ alignedMax (by omega) insideN (by omega) capsPost
        (fun z member => balanceCeil z (postMem z member))
      have epochN : getCurrentEpoch ns = getCurrentEpoch ms :=
        UInt64.toNat_inj.mp (sameEpoch inside)
      have keep := step_same_epoch_effective step (Nat.lt_of_le_of_lt
        (fork_le_of_chainSteps post.chainSteps) h.early) epochN i insideM
      have epochs : (getCurrentEpoch ns).toNat = (getCurrentEpoch ms).toNat := sameEpoch inside
      obtain ⟨f1, f2, f3, f4⟩ := first
      obtain ⟨s1, s2, s3, s4⟩ := second
      refine ⟨by omega, fun back => ?_, fun before => ?_, by omega⟩
      · have e1 := f2 (by omega)
        have e2 := s2 (by omega)
        omega
      · by_cases later : (getCurrentEpoch ns).toNat < (getCurrentEpoch y).toNat
        · exact s3 later
        · have e1 := f3 (by omega)
          have e2 := s2 (by omega)
          omega
  · -- the cap is the activation balance along the whole run
    have all := lowRun tail inside (Nat.le_of_not_lt compoundsEnd)
    have atX := all _ headMem
    exact seg tail _ alignedMin (by have := capCeil _ headMem; omega) inside
      (by have := capped _ headMem; omega) all balanceCeil

/-- The cap along the balance path of a run is at most the cap at its end. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capCeil_path {c e :
  ForkedBeaconState preset} (tail : Run config checks c e)
    (caps : CapOrder preset) (early : e.fork < .glamsterdam) (back : e.fork ≤ c.fork) (i : ℕ) :
    ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ PinTerms.capAt e i := by
  intro z member
  obtain ⟨-, r2, -⟩ := Internal.balancePath_endpoint tail (Run.nil : Run config checks e e) back
    member
  exact Internal.cap_le_cap_of_run caps r2 early i

/-- The effective balance of a key is at most its cap at each state of a run from a state `c`.

The run from the finalized state reaches `c` first, and `c` holds the key. -/
private theorem effective_le_cap_run (h : Setting config checks g split fin pulled anc counted V)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) {y : BeaconState preset fork}
    (r : Run config checks ⟨fork, split⟩ ⟨fork, y⟩) (i : ℕ) :
    ∀ z ∈ (fromC.append r).balancePath, effectiveAt z i ≤ PinTerms.capAt z i := fun z member => by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨zs, rfl, ⟨r1⟩, -⟩ := Internal.balancePath_state (fromC.append r) member
  exact Internal.effective_le_cap_at (shared.append (toC.append r1)) h.genesis h.caps h.early i

/-- A key's effective balance at a state of C's run is that at `c`, or within the ceiling.

The run of C starts at a state `c` of the shared segment, which holds the key, and ends at `e`.

The cap of the key may rise once on the run, and the balance counts up to its cap at each state.

The effective balance at `e` is that at `c` if `e` is no later than `c`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_stay_to (h : Setting config
  checks g split fin pulled anc counted V)
    {c e : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, e⟩) (i : ℕ)
    (inside : i < c.validators.data.size) (Bc : ℕ)
    (balanceC : ∀ z ∈ (fromC.append tailC).balancePath,
      min (actualBalanceAt z i) (PinTerms.capAt z i) ≤ Bc) :
    ((getCurrentEpoch e).toNat ≤ (getCurrentEpoch c).toNat ∧
        effectiveAt (⟨fork, e⟩ : ForkedBeaconState preset) i =
          effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i) ∨
      ((getCurrentEpoch c).toNat < (getCurrentEpoch e).toNat ∧
        effectiveAt (⟨fork, e⟩ : ForkedBeaconState preset) i ≤ Bc + preset.downwardBand ∧
        effectiveAt (⟨fork, e⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i)
            (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
              (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i))) := by
  obtain ⟨shared⟩ := h.toFin
  have invariant : Invariant c := Run.invariant h.genesis.invariant (shared.append toC)
  obtain ⟨c1, c2, c3, -⟩ := Internal.effective_ceiling_flip h (fromC.append tailC) invariant i
    inside Bc
    (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i)
    (effective_le_cap_run h toC fromC tailC i)
    (Internal.capCeil_path (fromC.append tailC) h.caps h.early (Nat.le_refl _) i) balanceC
  by_cases flat : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch c).toNat
  · exact .inl ⟨flat, c2 flat⟩
  · exact .inr ⟨by omega, c3 (by omega), c1⟩

open DirectSafety.Apriori.Internal in
/-- A key's balance on C's branch is at most R's balance, its debits, its credits and the gains.

The gain is small enough to use the key's effective balance envelope to bound its rewards.

The credits are `Cr`, which covers C's net credits `credits`, and the sync debits of R's.

`flipCover` makes `Cr` cover all of C's gross credits, when the cap rises on C's run.

The gain is at most a tenth of the credits, sync debits, slack and base gain. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.c_ceiling (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {e : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, e⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch e).toNat ≤ highC + 1)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (v : ValidatorIndex) (inside : v.toNat < split.validators.data.size)
    {events eventsF eventsC : List (BalanceEvent preset)} (W : ℕ)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) (Cr : ℕ)
    (credits : Internal.netScan v.toNat highC tailC +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC tailC) ≤
        Cr)
    (flipCover : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat ∧ preset.MIN_ACTIVATION_BALANCE.toNat <
          PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) v.toNat →
      Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
        (eventsC.map (Internal.syncCredit v.toNat)).sum ≤ Cr)
    (startEff : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum + W) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (floorR : min (actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (Internal.syncDebit v.toNat)).sum + W)
    (debits : (events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1)))
    (rateLow : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRate v.toNat + 1) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat) :
    ∃ gc, gc = min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (11 * ((Cr +
            (events.map (Internal.syncDebit v.toNat)).sum + (eventsF.map (Internal.syncDebit
              v.toNat)).sum) + W +
          min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate v.toNat +
          min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ (Cr +
            (events.map (Internal.syncDebit v.toNat)).sum + (eventsF.map (Internal.syncDebit
              v.toNat)).sum) + W +
        min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).gainRate v.toNat +
        min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) ∧
      ∀ z ∈ tailC.balancePath, min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤
        min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
          (events.map (Internal.syncDebit v.toNat)).sum + W)
          (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) +
          Cr +
          (gc + (min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate v.toNat +
            min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat))) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  have top : min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) +
        preset.downwardBand) ≤ (pinTerms config pulled anc fin).ebUp v.toNat := by
    have key : ∀ T : ℕ, T ≤ (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) -
        (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun T => by
      rw [← Nat.mul_div_self_eq_mod_sub_self]
      exact le_smul_ceilDiv (β := Nat) incPos
    rw [Internal.ebUp_eq config pulled anc fin electra v.toNat _ rfl]
    exact le_trans (min_le_min le_rfl (key _)) (le_max_right _ _)
  obtain ⟨i, hi⟩ : ∃ i, i = v.toNat := ⟨_, rfl⟩
  rw [← hi] at inside startEff floorR debits rateLow top credits flipCover ⊢
  obtain ⟨capI, hcap0⟩ : ∃ capI, capI =
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := ⟨_, rfl⟩
  rw [← hcap0] at debits top
  obtain ⟨pd, hpd⟩ : ∃ pd,
      pd = PinTerms.dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
      PinTerms.dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1) := ⟨_, rfl⟩
  rw [← hpd] at debits top
  obtain ⟨Dp, hDp⟩ : ∃ Dp, Dp =
      (events.map (penaltyDebit i)).sum + (events.map (floorPartialDebit v)).sum := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds, Ds = (events.map (Internal.syncDebit i)).sum := ⟨_, rfl⟩
  obtain ⟨DsF, hDsF⟩ : ∃ DsF, DsF = (eventsF.map (Internal.syncDebit i)).sum := ⟨_, rfl⟩
  rw [← hDp] at floorR debits ⊢
  rw [← hDs] at floorR startEff ⊢
  rw [← hDsF] at startEff ⊢
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  obtain ⟨Df, hDf⟩ : ∃ Df, Df =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := ⟨_, rfl⟩
  rw [← hDf] at debits top
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth Df := ⟨_, rfl⟩
  rw [← hDf, ← hD]
  obtain ⟨e0, he0⟩ : ∃ e0, e0 = (pinTerms config pulled anc fin).ebUp i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate i := ⟨_, rfl⟩
  rw [← he0] at top startEff rateLow
  rw [← hq] at rateLow ⊢
  have hq' : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
    rw [hq, he0, hP]
    rfl
  obtain ⟨C, hC⟩ : ∃ C, C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr + Ds + DsF + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, rfl⟩
  have startEff' : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ e0 + C := by
    refine Nat.le_trans startEff (Nat.add_le_add_left ?_ _)
    rw [hC]
    refine Nat.mul_le_mul_left _ ?_
    have le := Nat.div_le_div_right (c := 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      (show 10 * (DsF + Ds + W) ≤ 11 * (Cr + Ds + DsF + W + D * q + D) by omega)
    rwa [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 10)] at le
  have alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [he0]
    exact Internal.ebUp_aligned h i
  obtain ⟨P', hP', rateAll⟩ := Internal.key_rate_pre h tailC near
  rw [hP'.trans hP.symm] at rateAll
  have hDle : D ≤ (pinTerms config pulled anc fin).depth := hD ▸ min_le_left _ _
  have epochs : (getCurrentEpoch e).toNat - (getCurrentEpoch split).toNat ≤ D := by
    rw [hD]
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have sizeC : i < e.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tailC.chainSteps)
  have capSC := Internal.cap_le_cap_of_run h.caps tailC h.early i
  have capSP : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ capI :=
    hcap0 ▸ Internal.cap_le_cap_of_run h.caps toPulled h.early i
  have capCeil := Internal.capCeil_path tailC h.caps h.early (Nat.le_refl _) i
  have effS := Internal.effective_le_cap_at (shared.append fromFin) h.genesis h.caps h.early i
  have minMax := UInt64.le_iff_toNat_le.mp h.caps.compounding
  obtain ⟨kindS, aMin, aMax⟩ := Internal.capAt_kind h i inside
  obtain ⟨kindC, -, -⟩ := Internal.capAt_kind h i sizeC
  obtain ⟨wC, foundC⟩ : ∃ w, e.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem sizeC⟩
  have alignedC := Internal.capAt_aligned h.aligned (z := (⟨fork, e⟩ : ForkedBeaconState preset))
    electra foundC
  have startKey : 11 * D * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Internal.rate_per_increment preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 D incPos (by decide) alignedE0
      (by
        rw [← hq']
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 hDle)) rateLow)
  by_cases flipped : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤
      preset.MIN_ACTIVATION_BALANCE.toNat ∧ preset.MIN_ACTIVATION_BALANCE.toNat <
        PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i
  · -- the cap rises on C's branch, so the run splits at the step that makes the key compound
    have cover := flipCover flipped
    have invariantS := Run.invariant h.genesis.invariant (shared.append fromFin)
    obtain ⟨m, n, pre, step, post, cut, flatM, largeN, -, sameEpoch⟩ :=
      Internal.Run.flip_split tailC h.early h.fulu invariantS i flipped.1 flipped.2
    obtain ⟨mf, ms⟩ := m
    have sameM : fork = mf :=
      (Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
    subst sameM
    have insideM : i < ms.validators.data.size :=
      Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)
    obtain ⟨preMem, postMem⟩ := flip_path_mem pre step post cut
    have notSlot := Internal.step_flip_not_slot step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)) i insideM
      (Nat.not_lt.mpr flatM) largeN
    have junction := Internal.step_flip_min step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps))
      (Run.invariant invariantS pre) i (Nat.not_lt.mpr flatM) largeN
    have capMin : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i =
        preset.MIN_ACTIVATION_BALANCE.toNat := by omega
    clear kindS kindC
    have capsPre : ∀ z ∈ pre.balancePath, PinTerms.capAt z i ≤
        preset.MIN_ACTIVATION_BALANCE.toNat := fun z member => by
      obtain ⟨zs, rfl, -, ⟨r2⟩⟩ := Internal.balancePath_state pre member
      exact Nat.le_trans (Internal.cap_le_cap_of_run h.caps r2 h.early i) flatM
    have epochM : (getCurrentEpoch ms).toNat ≤ highC + 1 := by
      have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
        ((Run.nil.snoc step).append post).chainSteps)
      simp only at this
      omega
    have fc := Internal.flip_credits_le_sources (shared.append fromFin) h.genesis pre step post
      notSlot
      h.early electra i highC epochM (by rw [cut]; exact replayedC)
    rw [cut] at fc
    have minLe : preset.MIN_ACTIVATION_BALANCE.toNat ≤ capI := capMin ▸ capSP
    obtain ⟨gc, hform, hgc, bPre, bPost, -⟩ := c_ceiling_abstract_flip pre step post h.early
      h.fulu i inside highC P preset.MIN_ACTIVATION_BALANCE.toNat
      (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i) aMin alignedC
      (by omega) (by omega) capsPre (fun z member => capCeil z (postMem z member))
      (fun z member => rateAll z (member.elim (preMem z) (postMem z))) endEpochC incPos D Cr
      (Cr + Ds + DsF) e0 C
      (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
        preset.MIN_ACTIVATION_BALANCE.toNat) W
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq' alignedE0 hC epochs
      (le_min (by rw [← capMin]; exact floorR) (min_le_right _ _)) startEff' junction
      (step_same_epoch_effective step
        (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
        (UInt64.toNat_inj.mp (sameEpoch inside)) i insideM)
      (by omega) startKey (by omega)
    refine ⟨gc, hform, hgc, fun z member => ?_⟩
    rcases flip_path_cover pre step post notSlot cut z member with inPre | inPost
    · have := bPre z inPre
      have := capsPre z inPre
      rw [capMin]
      omega
    · have := bPost z inPost
      have := capCeil z member
      rw [capMin]
      omega
  · -- the cap of C's branch is the cap at the split throughout
    have same : PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i =
        PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i := by
      rcases kindS with s1 | s1 <;> rcases kindC with f | f <;> omega
    clear kindS kindC
    obtain ⟨gc, hform, hgc, bound, -⟩ := Internal.c_ceiling_abstract tailC h.early h.fulu i inside
      highC P
      (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i) alignedC
      (by omega) capCeil rateAll endEpochC incPos D Cr (Cr + Ds + DsF) e0 C
      (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
        (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i)) W
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq' alignedE0 hC epochs
      (le_min (by rw [same]; exact floorR) (by rw [same]; exact min_le_right _ _)) startEff'
      credits startKey (by omega)
    refine ⟨gc, hform, hgc, fun z member => ?_⟩
    have := bound z member
    have := capCeil z member
    omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The debits of a key on R's branch that the pin charges at the top: its passes and its partials.

The passes cost at most the leak at `M` for each epoch from the finalized state's.

The bound `M` is at least the key's effective balance at each state of the run to R.

The partials paid are at most those queued at the finalized state less those still queued at R. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.debits_le_top (h : Setting config
  checks g split fin pulled anc counted V)
    {s : BeaconState preset fork} (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, s⟩)
    (tail : Run config checks ⟨fork, s⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (inside : v.toNat < s.validators.data.size) (M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, s⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), tail = pre.append post →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M) :
    (events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt M v.toNat +
        (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1)) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have passes : (events.map (penaltyDebit v.toNat)).sum ≤
      ((getCurrentEpoch pulled).toNat - (getCurrentEpoch s).toNat) *
        (pinTerms config pulled anc fin).leakAt M v.toNat :=
    Internal.Run.passDebit_le tail h.early altair high endEpoch inside
    ((pinTerms config pulled anc fin).leakAt M v.toNat)
    (fun {z} pre post cut before totals => by
      obtain ⟨T, perIncrement, totalOk, perOk⟩ := totals
      obtain ⟨zf, zs⟩ := z
      have same : zf = fork := Internal.fork_eq_of_run pre post (Nat.le_refl _)
      subst same
      have startE : (getCurrentEpoch zs).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
        simp only at before
        omega
      obtain ⟨pq, pqOk⟩ :=
        quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
      exact (passRate_le_leakAt h (fromFin.append pre) startE totalOk pqOk v.toNat).trans
        (Internal.leakAt_mono config pulled anc fin v.toNat (below pre post cut)))
    replayed
  have epochs : (getCurrentEpoch pulled).toNat - (getCurrentEpoch s).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
    have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    simp only at this
    omega
  have whole := Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  have net := Internal.Run.partialDebit_net (fromFin.append tail) electra h.early high
    ((getCurrentEpoch pulled).toNat + 1) (Nat.le_succ _) (Internal.window_short h) v whole
  simp only [List.map_append, List.sum_append] at net
  have part : (events.map (floorPartialDebit v)).sum +
      PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1) ≤
        PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) := by
    rw [dueAmount_eq, dueAmount_eq]
    omega
  have := Nat.mul_le_mul_right ((pinTerms config pulled anc fin).leakAt M v.toNat) epochs
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a key at a state of R's run from the finalized state has a ceiling.

The balance counts up to the key's cap at that state.

The ceiling is R's balance, the leak at `M` over the window and the net partials.

It adds the sync debits of the two runs and the slack `W`.

The floor of the state gives it, with the debits of the run after the state.

The bound `M` is at least the key's effective balance at each state of the run. -/
private theorem prefix_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (W M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append post = fromFin.append tail →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M)
    {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) (cut : r1.append r2 = fromFin.append tail)
    (inside : v.toNat < zs.validators.data.size)
    (floorAt : ∀ {evs : List (BalanceEvent preset)}, r2.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).leakAt M v.toNat +
          (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1) -
            PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1))) +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
          v.toNat)).sum + W) := by
  have whole := Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  obtain ⟨e1, ok1⟩ := r1.balanceEvents_ok h.early high
  obtain ⟨e2, ok2⟩ := r2.balanceEvents_ok h.early high
  have app := Apriori.Internal.balanceEvents_append r1 r2 high ok1 ok2
  rw [cut, whole] at app
  have eq : eventsF ++ events = e1 ++ e2 := Except.ok.inj app
  have floor := floorAt ok2
  have debit := Internal.debits_le_top h r1 r2 high endEpoch ok1 ok2 v inside M
    (fun pre post same => below (r1.append pre) post
      (by rw [← Run.append_assoc, ← same]; exact cut))
  have sums : (e2.map (Internal.syncDebit v.toNat)).sum ≤
      (eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit v.toNat)).sum
        := by
    have := congrArg (fun L => (L.map (Internal.syncDebit v.toNat)).sum) eq
    simp only [List.map_append, List.sum_append] at this
    omega
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- `prefix_ceiling` at each state of the balance path of the run from a state `c` to R.

The state `c` is on the shared segment, and the floor holds at each state after it. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.path_ceiling (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (W M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append post = fromFin.append tail →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size)
    (floorAt : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (after : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append after = fromC.append tail →
      ∀ {evs : List (BalanceEvent preset)}, after.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    ∀ z ∈ (fromC.append tail).balancePath,
      min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
              (pinTerms config pulled anc fin).leakAt M v.toNat +
            (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
                ((getCurrentEpoch pulled).toNat + 1) -
              PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
                ((getCurrentEpoch pulled).toNat + 1))) +
          ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum + W) := by
  intro z member
  obtain ⟨r1, r2, cutZ'⟩ := Internal.balancePath_endpoint (fromC.append tail)
    (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  have cutZ : (toC.append r1).append r2 = fromFin.append tail := by
    rw [← Run.append_assoc]
    exact (congrArg toC.append cutZ').trans (by
      show toC.append (fromC.append tail) = fromFin.append tail
      rw [← cutC, Run.append_assoc])
  exact prefix_ceiling h fromFin tail high endEpoch replayedF replayed v W M below (toC.append r1)
    r2 cutZ (Nat.le_trans inside (registryGrows_of_chainSteps r1.chainSteps)) (floorAt r1 r2 cutZ')

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at each state of R's run from a state `c` is bounded.

The run from `c` is the rest of the run from the finalized state to R's, cut at `c`.

The finalized state is `c` for a key of the finalized registry.

A key that R's run creates has its first state `c` after the split.

At `c` the effective balance is within `ebUp` and the finalized one, or within its balance floor.

After `c` it is within `ebUp` and the whole increments of its sync debits and `W`.

`floorAt` bounds the balance at each state by R's balance and debits, which gives the ceiling. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.prefix_envelope (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (rest : Run config checks ⟨fork, c⟩ ⟨fork, pulled⟩)
    (cutC : toC.append rest = fromFin.append tail)
    (inside : v.toNat < c.validators.data.size) (W : ℕ)
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (floorAt : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (after : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append after = rest →
      ∀ {evs : List (BalanceEvent preset)}, after.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    ∀ z ∈ rest.balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum + W) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  obtain ⟨shared⟩ := h.toFin
  -- the top of `ebUp`, `A`, and the balance ceiling, `B`, which adds the sync debits and `W` to it
  obtain ⟨A, hA⟩ : ∃ A, A = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) :=
      ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = A +
      ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
        v.toNat)).sum + W) :=
    ⟨_, rfl⟩
  -- the balance ceiling at each state of that run
  have ceiling : ∀ {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), r1.append r2 = rest →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤ B := by
    intro zs r1 r2 cut
    have := prefix_ceiling h fromFin tail high endEpoch replayedF replayed v W
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (fun pre post _ => Internal.effective_le_cap_pulled h pre post v.toNat) (toC.append r1) r2
      (by rw [← Run.append_assoc, cut, cutC])
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps r1.chainSteps))
      (fun {evs} ev => floorAt r1 r2 cut ev)
    omega
  intro z member
  obtain ⟨r1, r2, cutZ⟩ := Internal.balancePath_endpoint rest
    (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  -- every state of the run to `zs` is the end of a run from `c` to R's
  have atPath : ∀ z' ∈ r1.balancePath, ∃ (zs' : BeaconState preset fork)
      (s1 : Run config checks ⟨fork, c⟩ ⟨fork, zs'⟩)
      (s2 : Run config checks ⟨fork, zs'⟩ ⟨fork, pulled⟩),
      z' = ⟨fork, zs'⟩ ∧ s1.append s2 = rest := by
    intro z' member'
    obtain ⟨s1, s2, cutS⟩ := Internal.balancePath_endpoint r1 r2 (Nat.le_refl _) member'
    obtain ⟨zf', zs'⟩ := z'
    have same' : fork = zf' := (Internal.fork_eq_of_run s1 s2 (Nat.le_refl _)).symm
    subst same'
    exact ⟨zs', s1, s2, rfl, cutS.trans cutZ⟩
  have bound := Internal.effective_ceiling_flip h r1
    (Run.invariant h.genesis.invariant (shared.append toC)) v.toNat inside B
    (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact Internal.effective_le_cap_at (shared.append (toC.append s1)) h.genesis h.caps h.early
        v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact Internal.cap_le_cap_of_run h.caps s2 h.early v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact ceiling s1 s2 cut)
  obtain ⟨origin, -⟩ := bound
  -- a start within the floor of the balance at `c` is within the floor of the balance ceiling
  have startLe : effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        min (B - B % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) := by
    rcases start with ⟨within, -⟩ | floorC
    · exact Or.inl within
    · refine Or.inr (Nat.le_min.mpr ⟨?_, ?_⟩)
      · have atC := ceiling (Run.nil : Run config checks ⟨fork, c⟩ ⟨fork, c⟩) rest
          (Run.nil_append _)
        have capped := Internal.effective_le_cap_at (shared.append toC) h.genesis h.caps h.early
          v.toNat
        have aligned := FloorTrace.effective_aligned (shared.append toC) h.genesis h.aligned v.toNat
        have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (show effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ B by omega)
        omega
      · have capped := Internal.effective_le_cap_at (shared.append toC) h.genesis h.caps h.early
          v.toNat
        have rise := Internal.cap_le_cap_of_run h.caps rest h.early v.toNat
        omega
  -- the envelope `ebUp` and the rounding
  obtain ⟨t, ht⟩ :
      ∃ t, t = A + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := ⟨_, rfl⟩
  have up := Internal.ebUp_eq config pulled anc fin electra v.toNat t (by omega)
  have floorRound := rounded_add_floor_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat A
    ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit v.toNat)).sum
      + W) incPos
  have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (show A + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 ≤ t by omega)
  have upper : min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat := by
    rw [up]
    exact Nat.le_max_right _ _
  rw [← hB] at floorRound
  omega

/-- A cap at a state of the Electra forks is at most the largest cap. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capAt_le_capMax {z :
  ForkedBeaconState preset} (caps : CapOrder preset)
    (electra : .pectra ≤ z.fork) (i : ℕ) :
    PinTerms.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
  cases found : z.state.validators.data[i]? with
  | none => simp [PinTerms.capAt, found]
  | some w =>
    have compounding := UInt64.le_iff_toNat_le.mp caps.compounding
    rw [Internal.capAt_of_found electra found]
    split <;> omega

/-- A key with an assigned exit epoch is inactive at every epoch from the exit on, along a run.

The run keeps an assigned exit epoch. -/
private theorem inactive_from_exit {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {i : ℕ} {v : Validator} (found : x.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) {e : Epoch} (reached : v.exitEpoch ≤ e) :
    isActiveAt y.state e i = false := by
  obtain ⟨later, foundLater, kept⟩ := tail.registryLifecycle.validators i v found
  have inactive : isActiveValidator later e = false := by
    unfold isActiveValidator
    simp
    exact fun _ => by rw [kept.exitEpoch assigned]; exact reached
  simp [isActiveAt, foundLater, inactive]

/-- A key that exited before the finalized epoch stays within its finalized balance and credits.

The key is idle from the finalized block on.

Its exit is kept, and the previous epoch of each later state is at or past it.

An idle key earns no epoch reward, so the credit ceiling of the run needs no rate.

The ceiling on the balance is the finalized balance and the credits of the run.

Rounding adds the whole increments that cover the credits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exited_ceiling (h : Setting config
  checks g split fin pulled anc counted V)
    {a : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, a⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch a).toNat ≤ high + 1) (i : ℕ) {w : Validator}
    (found : fin.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat) (Cr : ℕ)
    (credits : Internal.netScan i high run +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high run) ≤ Cr) :
    effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i ≤
      max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        ((actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  have incPos := h.bands.1
  have inside : i < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨shared⟩ := h.toFin
  have alignedMax := (Internal.cap_values_aligned h.aligned).2
  have startCap := Internal.effectiveAt_le_capMax shared h.genesis h.caps h.early i
  have capCeil : ∀ z ∈ run.balancePath,
      PinTerms.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := fun z member => by
    obtain ⟨r1, -, -⟩ := Internal.balancePath_endpoint run
      (Run.nil : Run config checks ⟨fork, a⟩ ⟨fork, a⟩) (Nat.le_refl _) member
    exact Internal.capAt_le_capMax h.caps (Nat.le_trans (Nat.le_trans (by decide) h.fulu)
      (fork_le_of_chainSteps r1.chainSteps)) i
  have notFar : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  have idle : ∀ z ∈ run.balancePath,
      i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) := by
    intro z member active
    obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint run
      (Run.nil : Run config checks ⟨fork, a⟩ ⟨fork, a⟩) (Nat.le_refl _) member
    obtain ⟨zf, zs⟩ := z
    have within := BeaconState.registryWithinLimit_of_lt
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early) zs
    have index : i.toUInt64.toNat = i := toNat_toUInt64_of_lt within
      (Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 r1.registryLifecycle.size_le)
    have previous := getPreviousEpoch_toNat zs
    have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r1.chainSteps)
    simp only at epochs
    have inactive := inactive_from_exit r1 found notFar (e := getPreviousEpoch zs)
      (UInt64.le_iff_toNat_le.mpr (by omega))
    obtain ⟨v, foundV, isActive⟩ := (mem_getActiveValidatorIndices within).mp active
    rw [index] at foundV
    have := isActiveAt_eq_true_iff.mpr ⟨v, foundV, isActive⟩
    rw [inactive] at this
    exact Bool.false_ne_true this
  obtain ⟨cb, hcb⟩ : ∃ cb, cb = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat + (Internal.netScan i high run +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high run)) := ⟨_,
          rfl⟩
  have cbE : ∀ E, Internal.creditBound run i high E 0
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat = cb := fun E => by
    rw [hcb]
    unfold Internal.creditBound
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_div, Nat.add_zero]
    omega
  obtain ⟨E, hE⟩ : ∃ E, E = max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
      (min preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        (cb - cb % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := ⟨_, rfl⟩
  have ceiling := key_credit_ceiling run h.early h.fulu i inside high 0 E alignedMax startCap
    capCeil (fun z member => .inl (idle z member)) endEpoch
    (by rw [cbE]; exact le_of_eq hE.symm)
  rw [cbE] at ceiling
  have mono := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (show cb ≤ actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i + Cr by
      have := Nat.min_le_left (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      omega)
  have split := rounded_add_ceil_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i) Cr incPos
  exact Nat.le_trans ceiling (max_le_max (Nat.le_refl _)
    (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans mono split)))

/-- A step that charges a key has it without an exit at its start and with one at its end. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.charge_exits {m n :
  ForkedBeaconState preset} (step : Step config checks m n)
    {v : ℕ} (charged : step.departureCharges.any (·.index == v) = true) :
    ∃ u w, m.state.validators.data[v]? = some u ∧ n.state.validators.data[v]? = some w ∧
      (∀ u', m.state.validators.data[v]? = some u' → u'.exitEpoch = FAR_FUTURE_EPOCH) ∧
      w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨c, member, same⟩ := List.any_eq_true.mp charged
  obtain ⟨⟨u, j⟩, found, picked⟩ := List.mem_filterMap.mp member
  have found : m.state.validators.data[j]? = some u := by
    simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using found
  dsimp only at picked
  split at picked
  · cases picked
  · rename_i w located
    split at picked
    · rename_i assigned
      cases Option.some.inj picked
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at assigned
      have : j = v := by simpa using same
      subst this
      refine ⟨u, w, found, located, ?_, assigned.2⟩
      intro u' read
      obtain rfl := Option.some.inj (found.symm.trans read)
      exact assigned.1
    · cases picked

/-- A step that charges a key has it in the registry at its start. -/
private theorem charge_inside {m n : ForkedBeaconState preset} (step : Step config checks m n)
    {v : ℕ} (charged : step.departureCharges.any (·.index == v) = true) :
    v < m.state.validators.data.size :=
  let ⟨_, _, found, _⟩ := Internal.charge_exits step charged
  (Array.getElem?_eq_some_iff.mp found).1

/-- The epoch rewards of a key over a run are at most the rate for each epoch of the run.

The steps from the key's departure charge on count, and the key is in the registry from then.

So the bound is needed for a step only when the key is in the registry at its start. -/
private theorem riseScan_snd_le (v high R : ℕ) {x : ForkedBeaconState preset}
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (bound : ∀ {m n : ForkedBeaconState preset} (step : Step config checks m n),
      tail.Contains step → v < m.state.validators.data.size →
        Internal.epochRewards v step ≤
          ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) * R) :
    (Internal.riseScan (config := config) (checks := checks) v high tail).2 ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * R := by
  induction tail with
  | nil => simp [Internal.riseScan]
  | @snoc m n pre step ih =>
    have prior := ih fun inner member inside => bound inner (.earlier member step) inside
    have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have mn := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step : Run config checks m n).chainSteps)
    simp only [Internal.riseScan]
    split
    · rename_i cond
      have inside : v < m.state.validators.data.size := by
        rcases cond.1 with seen | charged
        · obtain ⟨c, member, same⟩ := (Internal.riseScan_fst v high pre).mp seen
          obtain ⟨w, found, -, -⟩ := pre.departure_charge_exit c member
          rw [same] at found
          exact (Array.getElem?_eq_some_iff.mp found).1
        · exact charge_inside step charged
      have one := bound step (.last pre step) inside
      have split : (getCurrentEpoch n.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
            ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) := by omega
      rw [split, Nat.add_mul]
      omega
    · exact prior.trans (Nat.mul_le_mul_right _ (by omega))

/-- The rise of a charged key on C's branch is one band and the depth's gains at the largest rate.

The gains are the epoch rewards of the key after its exit starts, over the epochs of the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.riseQ_le (h : Setting config checks
  g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC v : ℕ) :
    Internal.riseQ tailC highC v ≤ preset.upwardBand + (pinTerms config pulled anc fin).depth *
      (pinTerms config pulled anc fin).gainRateMax := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  unfold Internal.riseQ
  split
  swap
  · exact Nat.zero_le _
  obtain ⟨P, -, gainLe, rateAll⟩ := Internal.pin_rate_exists h
  have scan := riseScan_snd_le (config := config) (checks := checks) v highC
    (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) tailC
    (fun {m n} step member inside => by
      obtain ⟨pre, post, _, mEarly, mEpoch⟩ :=
        DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
      have same := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
      obtain ⟨mf, ms⟩ := m
      obtain rfl : mf = fork := same
      have nEarly : n.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
      exact Internal.epochRewards_le step altair nEarly v (Or.inl inside)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
        (.inr (Internal.effectiveAt_le_capMax (shared.append (fromFin.append pre)) h.genesis
          h.caps mEarly v))
        (.inr (rateAll (fromFin.append pre) (by simp only at mEpoch ⊢; omega))))
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have epochs : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (pinTerms config pulled anc fin).depth := by omega
  calc _ ≤ preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) :=
        Nat.add_le_add_left (scan.trans (Nat.mul_le_mul_right _ epochs)) _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ gainLe) _

/-- A low key is in the registry. -/
private theorem lowB_found (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ} (low : (pinTerms config state ancestor finalizedState).lowB i = true) :
    ∃ w, state.validators.data[i]? = some w := by
  refine Internal.validator_of_flag (f := fun v =>
    decide (ancestor.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat) &&
      decide (v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat)) (.inl ?_)
  exact (of_decide_eq_true low).1

/-- A key is low if it is activated, not withdrawable at R, and its low bound is below the floor. -/
private theorem lowB_intro (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ}
    (first : ((state.validators.data[i]?).any fun v =>
      decide (ancestor.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat) &&
        decide (v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat)) = true)
    (low : (pinTerms config state ancestor finalizedState).lowEB i <
      (pinTerms config state ancestor finalizedState).newKeyFloor) :
    (pinTerms config state ancestor finalizedState).lowB i = true :=
  decide_eq_true ⟨first, low⟩

/-- A key whose exit starts on a run is activated at the start of the step that starts it.

The hypothesis `site` is the split of the run at the step that assigns the charged exit.

The activation comes from `ChainStep.exit_assigned_activated` at that step. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.charge_activated {x y :
  ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (tail : Run config checks x y) (charge : DepartureCharge)
    (site : ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧
          v.exitEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat) :
    ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧ v.exitEpoch = FAR_FUTURE_EPOCH ∧
          w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.activationEpoch ≤ getCurrentEpoch a.state ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat := by
  obtain ⟨a, b, pre, step, post, split, v, w, found, later, unset, set, amount, epoch⟩ := site
  exact ⟨a, b, pre, step, post, split, v, w, found, later, unset, set,
    step.chainStep.exit_assigned_activated
      (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps))
      found later unset set, amount, epoch⟩

/-- A charged key activated at the finalized state, and by R's epoch at C, is active at R.

Its activation at R is that of C: an assigned activation does not change.

It is not withdrawable by the finalized epoch at R, since then it would be exited on both branches.

This is the argument of `slashed_waits` for any key.

The split fixes its exit and withdrawable epochs. -/
private theorem activated_key_at_pulled (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (v : ValidatorIndex)
    (activatedBy : ∀ c, counted.validators.data[v.toNat]? = some c →
      c.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat) {w : Validator}
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (found : fin.validators.data[v.toNat]? = some w)
    (activated : w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ((pulled.validators.data[v.toNat]?).any fun u =>
      decide (anc.finalizedCheckpoint.epoch.toNat < u.withdrawableEpoch.toNat) &&
        decide (u.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat)) = true := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have near := h.near
  -- the key at the split, at R and at C, with the activation of the finalized state
  obtain ⟨x, foundSplit, lifeFin⟩ := fromFin.registryLifecycle.validators v.toNat w found
  obtain ⟨u, foundPulled, lifeSplit⟩ := toPulled.registryLifecycle.validators v.toNat x foundSplit
  have actSplit : x.activationEpoch = w.activationEpoch := lifeFin.activationEpoch activated
  have actPulled : u.activationEpoch = w.activationEpoch :=
    (lifeSplit.activationEpoch (actSplit ▸ activated)).trans actSplit
  obtain ⟨c, foundCounted, lifeAll⟩ :=
    (fromFin.append tailC).registryLifecycle.validators v.toNat w found
  have actCounted : c.activationEpoch = w.activationEpoch := lifeAll.activationEpoch activated
  have atPulled : u.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by
    rw [actPulled, ← actCounted]
    exact activatedBy c foundCounted
  -- the key is not withdrawable by the finalized epoch at R, since it has a charge on C's run
  have settled : anc.finalizedCheckpoint.epoch.toNat < u.withdrawableEpoch.toNat := by
    by_contra not
    obtain ⟨d, member, index⟩ := charged
    exact Internal.no_charge_of_settled h tailC
      (Array.getElem?_eq_some_iff.mp foundSplit).1 foundPulled (by omega) d member index
  simp [foundPulled, settled, atPulled]

section LowBound

open DirectSafety.Apriori DirectSafety.Apriori.Internal

/-- The penalties of one key in one step fit a rate read at the start of the step. -/
private theorem step_passDebit_le {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (startEpoch : (getCurrentEpoch m.state).toNat ≤ high + 1) {v : ℕ}
    (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : (getCurrentEpoch m.state).toNat < (getCurrentEpoch n.state).toNat →
      (∃ total perIncrement, getTotalActiveBalance m.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      Internal.passPenaltyRate config m v ≤ pen)
    {evs : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok evs) :
    (evs.map (penaltyDebit v)).sum ≤ pen := by
  have run : (Run.nil.snoc step : Run config checks m n).balanceEvents high = .ok evs := by
    simp [Run.balanceEvents, startEpoch, replayed, bind, Except.bind, pure, Except.pure]
  have bound := Internal.segment_passDebit_le_guarded (Run.nil.snoc step : Run config checks m n)
    early
    altair high endEpoch
    (fun {u w} step' member => by
      cases member with
      | last => rfl
      | earlier inner _ => cases inner)
    inside pen
    (fun {z} pre ok split before total => by
      injection split with middle _ _ _
      subst middle
      exact rate before total) run
  refine bound.trans ?_
  split <;> simp

/-- A rate that is linear in the effective balance bounds the two terms of a leak.

It bounds the leak of an aligned balance, and the leak of any balance an increment above, less one.
-/
private theorem leak_linear (inc pi score depth bias quotient : ℕ) (incPos : 0 < inc) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧
      (∀ eb : ℕ, inc ∣ eb →
        2 * (eb / inc * pi) + eb * (score + depth * bias) / (bias * quotient) ≤ ρn * eb / ρd) ∧
      ∀ x : ℕ, ρn * x ≤ ρd * (2 * ((x + inc) / inc * pi) +
        (x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by
  have under : ∀ x : ℕ, x ≤ inc * ((x + inc) / inc) := fun x => by
    rw [Nat.add_div_right _ incPos]
    exact (Nat.lt_mul_div_succ x incPos).le
  by_cases zero : bias * quotient = 0
  · refine ⟨2 * pi, inc, incPos, fun eb aligned => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := aligned
      simp only [zero, Nat.div_zero, Nat.add_zero]
      rw [Nat.mul_div_cancel_left _ incPos, show 2 * pi * (inc * u) = inc * (2 * pi * u) by ring,
        Nat.mul_div_cancel_left _ incPos]
      ring_nf
      exact le_refl _
    · simp only [zero, Nat.div_zero, Nat.add_zero]
      calc 2 * pi * x ≤ 2 * pi * (inc * ((x + inc) / inc)) := Nat.mul_le_mul_left _ (under x)
        _ = inc * (2 * ((x + inc) / inc * pi)) := by ring
        _ ≤ inc * (2 * ((x + inc) / inc * pi) + 1) := Nat.mul_le_mul_left _ (by omega)
  · have positive : 0 < bias * quotient := Nat.pos_of_ne_zero zero
    refine ⟨2 * pi * (bias * quotient) + (score + depth * bias) * inc, inc * (bias * quotient),
      Nat.mul_pos incPos positive, fun eb aligned => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := aligned
      have lhs : 2 * (inc * u / inc * pi) + inc * u * (score + depth * bias) / (bias * quotient) =
          2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
        rw [Nat.mul_div_cancel_left _ incPos]
        congr 2
        ring
      have rhs : (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) /
          (inc * (bias * quotient)) =
          2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
        rw [show (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) =
          inc * ((bias * quotient) * (2 * (u * pi)) + (score + depth * bias) * inc * u) by ring,
          Nat.mul_div_mul_left _ _ incPos, Nat.mul_add_div positive]
      rw [lhs, rhs]
    · have first := Nat.mul_le_mul_left (bias * quotient * (2 * pi)) (under x)
      have second : (score + depth * bias) * x ≤
          bias * quotient * ((x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by
        have := Nat.lt_mul_div_succ ((x + inc) * (score + depth * bias)) positive
        have mono : (score + depth * bias) * x ≤ (x + inc) * (score + depth * bias) :=
          calc (score + depth * bias) * x = x * (score + depth * bias) := Nat.mul_comm _ _
            _ ≤ (x + inc) * (score + depth * bias) :=
              Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        omega
      have third := Nat.mul_le_mul_left inc second
      calc (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * x
          = bias * quotient * (2 * pi) * x + inc * ((score + depth * bias) * x) := by ring
        _ ≤ bias * quotient * (2 * pi) * (inc * ((x + inc) / inc)) +
            inc * (bias * quotient *
              ((x + inc) * (score + depth * bias) / (bias * quotient) + 1)) :=
          Nat.add_le_add first third
        _ = inc * (bias * quotient) * (2 * ((x + inc) / inc * pi) +
            (x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by ring

/-- The pass premise of the potential floor, from a rate that is linear in aligned balances. -/
private theorem pass_of_leak (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (i : ValidatorIndex) (initial : ∃ val, fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = whole → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨val, initial⟩ := initial
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  intro m n pre step post cut evs ok
  have same := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  have startE : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
    simp only at this
    omega
  have endE : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    simp only at this
    omega
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have mSize := registryGrows_of_chainSteps pre.chainSteps
  obtain ⟨mf, ms⟩ := m
  obtain rfl : mf = fork := same
  have inside : i.toNat < ms.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp initial).1 mSize
  refine step_passDebit_le step nEarly altair (getCurrentEpoch pulled).toNat endE startE inside
    (ρn * effectiveAt ⟨mf, ms⟩ i.toNat / ρd) (fun _ total => ?_) ok
  obtain ⟨T, perIncrement, totalOk, perOk⟩ := total
  obtain ⟨pq, pqOk⟩ :=
    quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
  have rate := passRate_le_leakAt h pre startE totalOk pqOk i.toNat
  exact rate.trans (leaky _ (Nat.dvd_of_mod_eq_zero
    (FloorTrace.effective_aligned (shared.append pre) h.genesis h.aligned i.toNat)))

/-- The floor of the potential, in naturals.

It is the closed form less the debits, the band and the carried shortfall. -/
private def potentialFloor (ρn ρd K X band slack cost : ℕ) : ℕ :=
  ((ρd - ρn * K) * (X + band) - ρn * slack) / ρd - (band + cost)

/-- The queued partials of the key at the finalized state that are due by the call's cutoff.

They are at most the key's `partialsDue`. -/
private theorem partials_le_due (electra : .pectra ≤ fork) (v : ValidatorIndex) :
    ((((fin.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
            (·.amount.toNat)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  rw [← dueAmount_eq fin electra v]
  refine le_trans ?_ (le_max_left (_ : ℕ) _)
  dsimp only
  simp only [PinTerms.dueAmount, electra, ↓reduceDIte]
  exact le_rfl

/-- The partials paid to a key over a run from the finalized state are at most those due.

The run ends by the call's cutoff, which is within the withdrawal delay of the finalized state. -/
private theorem run_partials_le_due (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (v : ValidatorIndex)
    {events : List (BalanceEvent preset)}
    (replayed : whole.balanceEvents (getCurrentEpoch pulled).toNat = .ok events) :
    (events.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  exact (Internal.Run.partialDebit_le whole electra h.early (getCurrentEpoch pulled).toNat
    ((getCurrentEpoch pulled).toNat + 1) near (Internal.window_short h) v replayed).trans
    (partials_le_due electra v)

/-- The effective balance of a key at a state of the run from the finalized state, before its exit.

It is at least the least of its effective balance and cap at the finalized state.

It is also at least the floor of its potential, rounded down to an increment.

The floor loses the shortfall of the balance below the stored effective balance.

It also loses the debits, which are the sync debits of the run and the partials due. -/
private theorem exitQ_at (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    {sd : ForkedBeaconState preset} (pre : Run config checks ⟨fork, fin⟩ sd)
    (post : Run config checks sd ⟨fork, counted⟩)
    (cut : pre.append post = fromFin.append tailC)
    (v : ValidatorIndex) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (far : ∀ w, sd.state.validators.data[v.toNat]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (Internal.syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (Internal.syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      effectiveAt sd v.toNat := by
  have nearC := h.near
  have same := Internal.fork_eq_of_run pre post (Nat.le_refl _)
  obtain ⟨sf, se⟩ := sd
  obtain rfl : fork = sf := same.symm
  have toCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  simp only at toCounted
  have near : (getCurrentEpoch se).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix pre post
    (getCurrentEpoch pulled).toNat events (by rw [cut]; exact replayed)
  have clean : ∀ w, se.validators.data[v.toNat]? = some w → w.slashed = false := by
    obtain ⟨shared⟩ := h.toFin
    intro w found
    by_contra slashed
    exact run_slashed_exit_assigned (shared.append pre) h.genesis h.caps.activation
      h.caps.compounding h.early (Internal.Setting.delay h) v.toNat w found (by simpa using slashed)
        (far w found)
  have retained : ∀ {m n : ForkedBeaconState preset} (b : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (a : Run config checks n ⟨fork, se⟩),
      (b.snoc step).append a = pre → ∀ w, n.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat := by
    intro m n b step a cut' w found
    obtain ⟨last, located, kept⟩ := a.registryLifecycle.validators v.toNat w found
    by_cases e : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [e]
      exact .inl (getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled)
    · exact absurd ((kept.exitEpoch e).symm.trans (far last located)) e
  have syncLe : (before.map (Internal.syncDebit v.toNat)).sum ≤ (events.map (Internal.syncDebit
    v.toNat)).sum :=
    (isPrefix.sublist.map (Internal.syncDebit v.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
  have partialLe : (before.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat :=
    run_partials_le_due h pre near v beforeOk
  have final := cfloor_endpoint h se pre near beforeOk v val initial clean retained
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) ρn ρd
    (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat)
      preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      ((before.map (Internal.syncDebit v.toNat)).sum + (before.map (floorPartialDebit v)).sum))
    (by omega)
    (pass_of_leak h pre near v ⟨val, initial⟩ ρn ρd leaky)
    (fun a D k hk hD closed => by
      have mono : ρd - ρn * ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat) ≤
          ρd - ρn * k :=
        Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (hk.trans (Nat.sub_le_sub_right toCounted _))) _
      have step2 := (Nat.mul_le_mul_right _ mono).trans closed
      have step3 := Nat.div_le_of_le_mul (Nat.sub_le_of_le_add step2)
      unfold potentialFloor
      omega)
    pre Run.nil rfl
  refine le_trans (min_le_min le_rfl (min_le_min le_rfl (rounded_mono _ ?_))) final
  unfold potentialFloor
  omega

/-- The charge of a key on C's run is its effective balance at a state where its exit is unset.

The state is the stop of the charge.

The runs to it and from it make C's run from the finalized block. -/
private theorem exit_stop (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (v : ℕ)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v →
      c.epoch ≤ (getCurrentEpoch counted).toNat) :
    ∃ (sd : ForkedBeaconState preset) (pre : Run config checks ⟨fork, fin⟩ sd)
        (post : Run config checks sd ⟨fork, counted⟩),
      pre.append post = fromFin.append tailC ∧
      (∀ w, sd.state.validators.data[v]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH) ∧
      Internal.exitQ tailC v = effectiveAt sd v := by
  classical
  obtain ⟨c0, member0, index0, -, amount0⟩ : ∃ c ∈ tailC.departureCharges,
      c.index = v ∧ c.epoch ≤ (getCurrentEpoch counted).toNat ∧ Internal.exitQ tailC v = c.amount :=
        by
    obtain ⟨c, mem, idx⟩ := charged
    rcases Internal.exitQ_cases tailC v with ⟨none, -⟩ | found
    · exact absurd (epochLe c mem idx) (none c mem idx)
    · exact found
  obtain ⟨stop, chosen⟩ := Internal.stop_of_charge fromFin tailC member0 index0
  have selected := stop.selected
  rw [chosen] at selected
  obtain ⟨-, -, amount, next, assignedStep, rest, split', charged', vv, w, atStop, atNext,
    unset, assigned, epoch⟩ := selected
  refine ⟨stop.state, stop.pre, stop.post, stop.split, fun w' found => ?_, by rw [amount0, amount]⟩
  have same := Option.some.inj (found.symm.trans atStop)
  subst same
  exact unset

/-- The key's effective balance at its exit call, from the potential floor of the run to the call.

The key is activated at the finalized state, charged on the run from the split, and exits by C. -/
private theorem exitQ_potential (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (Internal.syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (Internal.syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      Internal.exitQ tailC v.toNat := by
  obtain ⟨sd, pre, post, cut, far, amount⟩ := exit_stop fromFin tailC v.toNat charged epochLe
  rw [amount]
  exact exitQ_at h fromFin tailC replayed pre post cut v val initial far ρn ρd leaky

/-- The leak of an aligned effective balance is at most a rate times it.

The rate times any balance is at most the leak an increment above, plus one. -/
private theorem leak_rate (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (v : ℕ) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧
      (∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
        (pinTerms config pulled anc fin).leakAt eb v ≤ ρn * eb / ρd) ∧
      ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
        (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v + 1) := by
  obtain ⟨ρn, ρd, positive, bound, above⟩ := leak_linear preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat
    (if altair : .altair ≤ fork then
      (((fin.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    config.INACTIVITY_SCORE_BIAS.toNat
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat incPos
  exact ⟨ρn, ρd, positive, fun eb aligned => bound eb aligned, fun x => above x⟩

/-- The rate times the epochs and the base is at most the leak for each epoch, plus one.

The leak is read an increment above the base. -/
private theorem rate_cost (ρn ρd K L Y : ℕ) (first : ρn * Y ≤ ρd * (L + 1)) :
    ρn * K * Y ≤ ρd * (K * (L + 1)) :=
  calc ρn * K * Y = K * (ρn * Y) := by ring
    _ ≤ K * (ρd * (L + 1)) := Nat.mul_le_mul_left _ first
    _ = ρd * (K * (L + 1)) := by ring

/-- The leak at a base, for each epoch of the depth, covers the base's share of the closed form.

The rate bounds the base by the leak an increment above it, plus one.

The closed form takes the rate for each epoch from the base, and its rest is the base's share. -/
private theorem rate_step (ρn ρd K L Y : ℕ) (first : ρn * Y ≤ ρd * (L + 1)) :
    ρd * Y ≤ (ρd - ρn * K) * Y + ρd * (K * (L + 1)) := by
  have rate := rate_cost ρn ρd K L Y first
  have cover : ρd ≤ (ρd - ρn * K) + ρn * K := by omega
  calc ρd * Y ≤ ((ρd - ρn * K) + ρn * K) * Y := Nat.mul_le_mul_right _ cover
    _ = (ρd - ρn * K) * Y + ρn * K * Y := by ring
    _ ≤ (ρd - ρn * K) * Y + ρd * (K * (L + 1)) := Nat.add_le_add_left rate _

/-- The arithmetic of the low bound of an existing key.

The potential floor, rounded down to an increment, is at least the bound less the sync debits.

`L1` and `L2` are the leaks an increment above the base and above the shortfall.

The rate bounds the base and the shortfall by them, plus one each.

`R` is the bound before its drop, and it is at most the base less the partials due. -/
private theorem low_arith (inc band ρn ρd K depth X s R pd sync L1 L2 E0 cap : ℕ)
    (positive : 0 < ρd) (incPos : 0 < inc)
    (first : ρn * X ≤ ρd * (L1 + 1)) (second : ρn * s ≤ ρd * (L2 + 1)) (epochs : K ≤ depth)
    (baseLe : R ≤ X - pd) (effLe : R ≤ E0) (capLe : E0 ≤ cap) :
    R - ((L2 + 1) + depth * (L1 + 1) + band + inc) ≤
      min E0 (min cap
        (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) -
          (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd))) % inc)) + sync := by
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ epochs
  suffices rounded : R - ((L2 + 1) + depth * (L1 + 1) + band + inc) ≤
      (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) -
        (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd))) % inc) + sync by
    omega
  generalize hF : ((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) = F
  have modLt := Nat.mod_lt F incPos
  have modLe := Nat.mod_le F inc
  by_cases big : ρd ≤ ρn * K
  · -- the closed form is vacuous, and the leak already covers the base
    have zero : ρd - ρn * K = 0 := Nat.sub_eq_zero_of_le big
    rw [zero, Nat.zero_mul, Nat.zero_sub, Nat.zero_div, Nat.zero_sub] at hF
    have step := rate_step ρn ρd K L1 X first
    rw [zero, Nat.zero_mul, Nat.zero_add] at step
    have base := Nat.le_of_mul_le_mul_left step positive
    omega
  · have step := rate_step ρn ρd K L1 X first
    have mono : (ρd - ρn * K) * X ≤ (ρd - ρn * K) * (X + band) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have bound := Nat.lt_mul_div_succ
      ((ρd - ρn * K) * (X + band) - ρn * s) positive
    have total : ρd * (X + band) ≤ ((ρd - ρn * K) * (X + band) - ρn * s) + ρn * s +
        ρd * (K * (L1 + 1)) + ρd * band := by
      have split : ρd * (X + band) = ρd * X + ρd * band := by ring
      omega
    have lt : ρd * (X + band) < ρd * (((ρd - ρn * K) * (X + band) - ρn * s) / ρd + 1 +
        (L2 + 1) + K * (L1 + 1) + band) := by
      calc ρd * (X + band) ≤ _ := total
        _ < ρd * (((ρd - ρn * K) * (X + band) - ρn * s) / ρd + 1) + ρd * (L2 + 1) +
              ρd * (K * (L1 + 1)) + ρd * band := by omega
        _ = _ := by ring
    have cancel := Nat.lt_of_mul_lt_mul_left lt
    generalize ((ρd - ρn * K) * (X + band) - ρn * s) / ρd = W at cancel hF
    omega

/-- The low bound of an existing key, against the `lowEB` and `drop` of the reserve.

The key is activated at the finalized state, charged on the run from the split, and exits by C.

The bound is its effective balance at the call, less its sync debits.

The form of `drop` carries the shortfall of the balance below the stored effective balance once.

It carries the leak at the base for each epoch of the depth. -/
private theorem existing_low_explicit
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    min (min (min (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
          (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) -
        (pinTerms config pulled anc fin).partialsDue v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat -
      (((pinTerms config pulled anc fin).leakAt
          (balanceAt fin v.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      Internal.exitQ tailC v.toNat + (events.map (Internal.syncDebit v.toNat)).sum := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin h.bands.1 v.toNat
  have potential := exitQ_potential h fromFin tailC replayed v epochLe val initial charged ρn ρd
    leaky
  have finEB : balanceAt fin v.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat := rfl
  have capped : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared h.genesis h.caps h.early
      initial
  have toCounted := UInt64.le_iff_toNat_le.mp h.later
  have nearC := h.near
  have arith := low_arith preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand ρn ρd
    ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (min (min (min (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
          (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) -
        (pinTerms config pulled anc fin).partialsDue v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat)
    ((pinTerms config pulled anc fin).partialsDue v.toNat) (events.map (Internal.syncDebit
      v.toNat)).sum
    ((pinTerms config pulled anc fin).leakAt
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat)
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (withdrawalMaxEffectiveBalance preset fork val).toNat positive h.bands.1 (above _) (above _)
    (by omega) (by omega) (by omega) capped
  simp only [potentialFloor] at potential
  exact le_trans arith (Nat.add_le_add_right potential _)

/-- The relaxed closed form, read at `a + X / M`, is the unslashed one with one more pass.

`Y` stands for `max finEB base0`.

`X` is the argument of `flagged`'s slashing loss. -/
private theorem bridge (ρn ρd M k B0 DOWN slack a D X Y inc : Nat) (hM : 2 ≤ M)
    (closed : (M - 1) * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) ≤
      M * (ρd * (a + D + DOWN) + ρn * slack) + ρd * (DOWN + slack))
    (hB : B0 + slack ≤ Y) (hX : Y + inc ≤ X) (hinc : M + 2 * DOWN ≤ inc + 1) :
    (ρd - ρn * (k + 1)) * (B0 + DOWN) ≤ ρd * (a + X / M + D + DOWN) + ρn * slack := by
  have hMpos : 0 < M := by omega
  have hq : X < M * (X / M + 1) := by
    have := Nat.lt_mul_div_succ X hMpos
    simpa [Nat.mul_comm] using this
  have hV : ρd - ρn * (k + 1) ≤ ρd := Nat.sub_le _ _
  have hP : (ρd - ρn * (k + 1)) * (B0 + DOWN) ≤ ρd * (B0 + DOWN) :=
    Nat.mul_le_mul_right _ hV
  have hsplit : M * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) =
      (M - 1) * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) +
        (ρd - ρn * (k + 1)) * (B0 + DOWN) := by
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp [Nat.add_mul]
  have hfit : B0 + 2 * DOWN + slack ≤ M * (X / M) := by
    have : M * (X / M + 1) = M * (X / M) + M := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hρ : ρd * (B0 + 2 * DOWN + slack) ≤ ρd * (M * (X / M)) := Nat.mul_le_mul_left _ hfit
  have hlhs : M * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) ≤
      M * (ρd * (a + D + DOWN) + ρn * slack) + ρd * (M * (X / M)) := by
    have e1 : ρd * (B0 + 2 * DOWN + slack) = ρd * (B0 + DOWN) + ρd * (DOWN + slack) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  have hrhs : M * (ρd * (a + X / M + D + DOWN) + ρn * slack) =
      M * (ρd * (a + D + DOWN) + ρn * slack) + ρd * (M * (X / M)) := by
    have e2 : ρd * (a + X / M + D + DOWN) = ρd * (a + D + DOWN) + ρd * (X / M) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [e2, Nat.add_right_comm (ρd * (a + D + DOWN)), Nat.mul_add, Nat.mul_add,
      Nat.mul_left_comm M ρd (X / M)]
  exact Nat.le_of_mul_le_mul_left (by omega) hMpos

/-- The arithmetic of the margin of the floor of a key on C's run.

The closed form of the potential floor, less the sync debits, is at least the base less the fall.

The fall holds the leak at the base and the band for each epoch of the depth, and the carry.

`L1` and `L2` are the leaks an increment above the base with the band and above the shortfall.

The rate bounds the base with the band and the shortfall by them, plus one each. -/
private theorem margin_arith (ρn ρd K depth B band s L1 L2 pd sync D a X : ℕ)
    (positive : 0 < ρd) (first : ρn * (B + band) ≤ ρd * (L1 + 1))
    (second : ρn * s ≤ ρd * (L2 + 1)) (epochs : K ≤ depth)
    (fall : (L2 + 1) + depth * (L1 + 1) + pd ≤ X) (debit : D ≤ sync + pd)
    (closed : (ρd - ρn * K) * (B + band) ≤ ρd * (a + D + band) + ρn * s) :
    B - X - sync ≤ a := by
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ epochs
  have step := rate_step ρn ρd K L1 (B + band) first
  have spread : ρd * (a + D + band + (L2 + 1) + K * (L1 + 1)) =
      ρd * (a + D + band) + ρd * (L2 + 1) + ρd * (K * (L1 + 1)) := by ring
  have total : ρd * (B + band) ≤ ρd * (a + D + band + (L2 + 1) + K * (L1 + 1)) := by omega
  have cancel := Nat.le_of_mul_le_mul_left total positive
  omega

/-- The arithmetic of the stay of the effective balance of a key on C's run.

The key has no sync debits, and the test of its floor holds.

An effective balance above the finalized one is at least an increment above it.

A segment of the run from a state with that effective balance ends at a balance of at least M.

Here `M` is the finalized effective balance.

The segment loses the rate of the leak for each epoch and the partials due.

The rate bounds the base with the band by the leak, and the test bounds the fall by the band.

A quarter of an increment bounds the band, as the preset requires. -/
private theorem stay_arith (ρn ρd K k depth inc band B M Bw X pd D bal L1 L2 : ℕ)
    (positive : 0 < ρd) (incPos : 0 < inc) (quarter : 4 * band ≤ inc) (big : inc ≤ M)
    (testB : M ≤ B + band) (fallX : X ≤ band) (first : ρn * (B + band) ≤ ρd * (L1 + 1))
    (fall : (L2 + 1) + depth * (L1 + 1) + pd ≤ X) (epochs : k ≤ K) (depthK : K ≤ depth)
    (start : M + inc ≤ Bw) (debit : D ≤ pd)
    (closed : (ρd - ρn * k) * (Bw + band) ≤ ρd * (bal + D + band)) : M ≤ bal := by
  have cost := rate_cost ρn ρd K L1 (B + band) first
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ depthK
  have rate : ρn * K * (B + band) + ρd * pd ≤ ρd * X := by
    have fits : ρd * (K * (L1 + 1) + pd) ≤ ρd * X := Nat.mul_le_mul_left ρd (by omega)
    rw [Nat.mul_add] at fits
    omega
  have yPos : 0 < B + band := by omega
  have bound : ρn * K * (B + band) ≤ ρd * (B + band) :=
    calc ρn * K * (B + band) ≤ ρd * X := by omega
      _ ≤ ρd * band := Nat.mul_le_mul_left _ fallX
      _ ≤ ρd * (B + band) := Nat.mul_le_mul_left _ (by omega)
  have under : ρn * K ≤ ρd := Nat.le_of_mul_le_mul_right bound yPos
  have fewer : ρn * k ≤ ρd := Nat.le_trans (Nat.mul_le_mul_left ρn epochs) under
  have mono : (ρd - ρn * k) * (M + inc + band) ≤ (ρd - ρn * k) * (Bw + band) :=
    Nat.mul_le_mul_left _ (by omega)
  have split : ρd * (M + inc + band) =
      (ρd - ρn * k) * (M + inc + band) + ρn * k * (M + inc + band) :=
    calc ρd * (M + inc + band) = ((ρd - ρn * k) + ρn * k) * (M + inc + band) := by
          rw [Nat.sub_add_cancel fewer]
      _ = _ := by ring
  have loss : ρn * k * (M + inc + band) ≤ 3 * (ρn * K * (B + band)) :=
    calc ρn * k * (M + inc + band) ≤ ρn * K * (M + inc + band) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ρn epochs)
      _ ≤ ρn * K * (3 * (B + band)) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (ρn * K * (B + band)) := by ring
  have left : ρd * (M + inc + band + 3 * pd) = ρd * (M + inc + band) + 3 * (ρd * pd) := by ring
  have right : ρd * (bal + D + band + 3 * X) = ρd * (bal + D + band) + 3 * (ρd * X) := by ring
  have total : ρd * (M + inc + band + 3 * pd) ≤ ρd * (bal + D + band + 3 * X) := by omega
  have cancel := Nat.le_of_mul_le_mul_left total positive
  omega

/-- The margin of the floor of a key on C's run, from a rate of its leak.

The rate is `leak_rate`'s for the key.

The balance of the key from the finalized block is above the closed form of the potential floor.

The closed form reads the rate that `leak_rate` gives and the shortfall of the balance.

It also reads the debits of the run, which are its sync debits and its partials.

The partials are at most those due.

`low` is the base less `X`.

`X` is at least the fall.

The fall is the carry, the leak for each epoch of the depth, and the partials due.

The leak is read at the base with the band. -/
private theorem floorC_margin (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X) :
    ∃ slack : ℕ,
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
        low - (events.map (Internal.syncDebit i.toNat)).sum ≤ a := by
  have nearC := h.near
  have partialLe := run_partials_le_due h (fromFin.append tailC) nearC i replayed
  refine ⟨effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
    actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat, by omega,
    pass_of_leak h (fromFin.append tailC) nearC i ⟨val, initial⟩ ρn ρd leaky,
    fun a D k hk hD closed => ?_⟩
  rw [← hbase0] at closed
  have bound := margin_arith ρn ρd k
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) base0
    preset.downwardBand
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).partialsDue i.toNat)
    (events.map (Internal.syncDebit i.toNat)).sum D a X
    positive (above _) (above _) (by omega) fall (by omega) closed
  omega

/-- The arithmetic of the margin of the floor of a slashed key on C's run.

It is `floorC_margin` for the closed form after a slash with the fork's quotient.

The fall reads the leak at the base, and the band is a term of `X`, as `lowEB`'s drop reads them.

`Xs` is the effective balance that the slash is read at.

It is at least the finalized one and an increment.

`bridge` turns the closed form into the one at the balance and the slash's share `Xs / M`.

Then `margin_arith` at one more epoch gives the bound. -/
private theorem floorC_margin_slash (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low Xs : ℕ)
    (hXs : max (balanceAt fin i.toNat) base0 + preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ Xs)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        preset.downwardBand + (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X) :
    ∃ slack : ℕ,
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
        ((EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) *
        ((ρd - ρn * (k + 1)) *
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat + preset.downwardBand)) ≤
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
            (ρd * (a + D + preset.downwardBand) + ρn * slack) +
            ρd * (preset.downwardBand + slack) →
        low - (events.map (Internal.syncDebit i.toNat)).sum ≤ a + Xs /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
  have nearC := h.near
  have partialLe := run_partials_le_due h (fromFin.append tailC) nearC i replayed
  have fusaka := parameters_of_fusaka (preset := preset) h.fulu h.early
  have two := h.facts.quotient
  have slashFact := h.facts.slash
  have quarter := h.facts.quarterBand
  rw [← fusaka] at two slashFact
  refine ⟨effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
    actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat, by omega,
    pass_of_leak h (fromFin.append tailC) nearC i ⟨val, initial⟩ ρn ρd leaky,
    fun a D k hk hD closed => ?_⟩
  rw [← hbase0] at closed
  have finEq : balanceAt fin i.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := rfl
  have bridged := bridge ρn ρd
    (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat k base0
    preset.downwardBand
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    a D Xs (max (balanceAt fin i.toNat) base0) preset.EFFECTIVE_BALANCE_INCREMENT.toNat two
    closed (by rw [hbase0, finEq]; omega) hXs (by omega)
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  simp only at finSplit
  have epochs : k + 1 ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
    omega
  have mono : (ρd - ρn * (k + 1)) * (base0 + 0) ≤
      (ρd - ρn * (k + 1)) * (base0 + preset.downwardBand) :=
    Nat.mul_le_mul_left _ (by omega)
  have closed0 : (ρd - ρn * (k + 1)) * (base0 + 0) ≤ ρd * ((a + Xs /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat +
        preset.downwardBand) + D + 0) + ρn * (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset)
        i.toNat - actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat) := by
    refine mono.trans (bridged.trans (le_of_eq ?_))
    congr 2
    omega
  have bound := margin_arith ρn ρd (k + 1)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) base0 0
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (base0 + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).partialsDue i.toNat)
    (events.map (Internal.syncDebit i.toNat)).sum D
    (a + Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat +
      preset.downwardBand) (X - preset.downwardBand)
    positive (by simpa using above base0) (above _) epochs (by omega) (by omega) closed0
  have downLe : preset.downwardBand ≤ X := by omega
  rw [hlow]
  exact (fun (B X S q a dn : ℕ) (le : dn ≤ X) (b : B - (X - dn) - S ≤ a + q + dn) =>
    show B - X - S ≤ a + q by omega) _ _ _ _ _ _ downLe bound

/-- The drop of `lowEB` and the fall `X` of the margin leave the rounded floor above `lowEB`.

The drop has the increment where the fall has the partials due.

A key whose bound is zero needs no floor. -/
private theorem slash_low_arith (R pd dropV X base0 m sy G r inc A P dn : ℕ)
    (hX : X = A + P + dn + pd) (hD : dropV = A + P + dn + inc)
    (hR : 0 < R → R + pd ≤ base0) (hG : base0 - X - sy - m = G) (hr : r < inc) :
    R - dropV - m - sy ≤ G - r := by
  omega

/-- The effective balance of a key at C is above its `lowEB`, less the slash's share.

The sync debits of the key are added to it.

The key is unslashed at the finalized block, and it may be slashed at C.

The share is read at the effective balance that `flagged` reads the slashing's loss at.

The drop in `lowEB` holds the band and an increment, which cover the rounding of the floor. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.lowEB_slashed (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (unslashed : val.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat)) :
    (pinTerms config pulled anc fin).lowEB i.toNat -
        max ((pinTerms config pulled anc fin).ebUp i.toNat)
          (max (balanceAt fin i.toNat) ((pinTerms config pulled anc fin).base0 i.toNat) +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
      balanceAt counted i.toNat + (events.map (Internal.syncDebit i.toNat)).sum := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have incPos := h.bands.1
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin incPos i.toNat
  have capped : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared h.genesis h.caps h.early
      initial
  have finEq : balanceAt fin i.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := rfl
  have base0Eq := Internal.base0_of_found config pulled anc fin initial
  have dropEq := Internal.drop_of_found config pulled anc fin initial
  obtain ⟨X, hX⟩ : ∃ X, X = ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            ((pinTerms config pulled anc fin).base0 i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        preset.downwardBand + (pinTerms config pulled anc fin).partialsDue i.toNat := ⟨_, rfl⟩
  obtain ⟨Xs, hXsEq⟩ : ∃ Xs, Xs = max ((pinTerms config pulled anc fin).ebUp i.toNat)
      (max (balanceAt fin i.toNat) ((pinTerms config pulled anc fin).base0 i.toNat) +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := ⟨_, rfl⟩
  obtain ⟨slack, start, pass, arithS⟩ := floorC_margin_slash h fromFin tailC replayed i val initial
    ρn ρd positive leaky above ((pinTerms config pulled anc fin).base0 i.toNat) X
    ((pinTerms config pulled anc fin).base0 i.toNat - X) Xs
    (by rw [hXsEq]; exact Nat.le_max_right _ _) base0Eq rfl (by omega)
  have endpoint := cfloor_endpoint_slash h counted (fromFin.append tailC) h.near replayed i val
    initial unslashed retained slack ρn ρd
    ((pinTerms config pulled anc fin).base0 i.toNat - X -
      (events.map (Internal.syncDebit i.toNat)).sum)
    (Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) start pass
    arithS (fromFin.append tailC) (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) rfl
  have actEq : ((fin.balances.data[i.toNat]?).map (·.toNat)).getD 0 =
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := rfl
  rw [Internal.lowEB_unfold, actEq]
  have effC : balanceAt counted i.toNat =
      effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i.toNat := rfl
  rw [effC, ← hXsEq]
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = min (min (balanceAt pulled i.toNat) (balanceAt fin i.toNat))
      (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat) := ⟨_, rfl⟩
  rw [← hm1]
  have m1Eff : m1 ≤ balanceAt fin i.toNat := by
    rw [hm1]
    exact Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  have m1Act : m1 ≤ actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := by
    rw [hm1]
    exact Nat.min_le_right _ _
  obtain ⟨R, hR⟩ : ∃ R, R = min (m1 - (pinTerms config pulled anc fin).partialsDue i.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat := ⟨_, rfl⟩
  rw [← hR]
  have hRle : R ≤ m1 - (pinTerms config pulled anc fin).partialsDue i.toNat := by
    rw [hR]
    exact Nat.min_le_left _ _
  have capped' : balanceAt fin i.toNat ≤ (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    rw [finEq]
    exact capped
  have baseLe : 0 < R → R + (pinTerms config pulled anc fin).partialsDue i.toNat ≤
      (pinTerms config pulled anc fin).base0 i.toNat := fun positive => by
    rw [base0Eq]
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have underM : R ≤ m1 := Nat.le_trans hRle (Nat.sub_le _ _)
  generalize hG : (pinTerms config pulled anc fin).base0 i.toNat - X -
    (events.map (Internal.syncDebit i.toNat)).sum - Xs /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = G at endpoint
  have modLt := Nat.mod_lt G incPos
  generalize G % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = r at endpoint modLt
  rw [← finEq] at endpoint
  have bounded : R - (pinTerms config pulled anc fin).drop i.toNat -
      Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        (events.map (Internal.syncDebit i.toNat)).sum ≤ G - r :=
    slash_low_arith _ _ _ _ _ _ _ _ _ _ _ _ _ hX dropEq baseLe hG modLt
  have atMin : R - (pinTerms config pulled anc fin).drop i.toNat -
      Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        (events.map (Internal.syncDebit i.toNat)).sum ≤
      min (balanceAt fin i.toNat) (min (withdrawalMaxEffectiveBalance preset fork val).toNat
        (G - r)) :=
    Nat.le_min.mpr ⟨Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _)
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans underM m1Eff))),
      Nat.le_min.mpr ⟨Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _)
        (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans underM (Nat.le_trans m1Eff capped')))),
        bounded⟩⟩
  omega

/-- The effective balance of a key on C's run stays at its finalized value when the test holds.

The key has no sync debits on the run, and the test of its floor holds.

A downward update fires only at a step whose balance after it is at least the finalized balance. -/
private theorem floorC_stay (h : Setting config checks g split fin pulled anc counted V)
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
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low finEB : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (hfin : finEB = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X)
    (sync : (events.map (Internal.syncDebit i.toNat)).sum = 0)
    (test : max finEB base0 ≤ low + preset.downwardBand)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC) :
    finEB ≤ effectiveAt z i.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  have incPos := h.bands.1
  have alignedFin := FloorTrace.effective_aligned toFin h.genesis h.aligned i.toNat
  have aligned : finEB % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hfin]
    exact alignedFin
  by_cases small : finEB < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  · have zero : finEB = 0 := by rw [← Nat.mod_eq_of_lt small]; exact aligned
    omega
  have big : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ finEB := Nat.le_of_not_lt small
  have quarter := h.facts.quarterBand
  have fallX : X ≤ preset.downwardBand := by omega
  have testB : finEB ≤ base0 + preset.downwardBand := by omega
  have first := above (base0 + preset.downwardBand)
  have partialLe := run_partials_le_due h (fromFin.append tailC) h.near i replayed
  obtain ⟨slack, start, pass, arith⟩ := floorC_margin h fromFin tailC replayed i val initial ρn ρd
    positive leaky above base0 X low hbase0 hlow fall
  have floorAt : ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, counted⟩), r1.append r2 = fromFin.append tailC →
      low - (events.map (Internal.syncDebit i.toNat)).sum ≤ actualBalanceAt p i.toNat :=
    fun r1 r2 whole => cfloor_balance h counted (fromFin.append tailC) h.near replayed i val
      initial clean retained slack ρn ρd (low - (events.map (Internal.syncDebit i.toNat)).sum) start
        pass
      arith r1 r2 whole
  have forkEnd : ∀ {p : ForkedBeaconState preset} (r2 : Run config checks p ⟨fork, counted⟩),
      p.fork < .glamsterdam := fun r2 =>
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  have inside : i.toNat < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp initial).1
  have cappedFin : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax toFin h.genesis h.caps h.early
      initial
  rw [hfin]
  refine (Internal.Run.effective_floor_pair rp (forkEnd rest) h.fulu i.toNat inside 0 0 0 0 0
    0).2.1 alignedFin ?_ ?_
  · intro m n before step after cut' below
    have nSame := Internal.fork_eq_of_run (before.snoc step) (after.append rest) (Nat.le_refl _)
    have mSame := Internal.fork_eq_of_run before ((Run.nil.snoc step).append (after.append rest))
      (Nat.le_refl _)
    obtain ⟨mF, mS⟩ := m
    obtain ⟨nF, nS⟩ := n
    obtain rfl : fork = nF := nSame.symm
    obtain rfl : fork = mF := mSame.symm
    have eqn : (before.snoc step).append (after.append rest) = fromFin.append tailC := by
      rw [Run.append_assoc, cut', cut]
    have atN := floorAt (before.snoc step) (after.append rest) eqn
    by_cases down : effectiveAt (⟨fork, mS⟩ : ForkedBeaconState preset) i.toNat ≤ finEB
    · omega
    have alignedM := FloorTrace.effective_aligned (toFin.append before) h.genesis h.aligned i.toNat
    have gap := add_le_of_lt_of_aligned alignedM aligned (by omega)
    have origin := cfloor_origin h counted (fromFin.append tailC) h.near replayed i val initial
      clean retained before ((Run.nil.snoc step).append (after.append rest))
      (by rw [Run.append_assoc]; exact eqn)
    rcases origin with same | ⟨w, pre, post, hpre, hm, hle, -⟩
    · omega
    have wSame := Internal.fork_eq_of_run pre post (Nat.le_refl _)
    obtain ⟨wF, wS⟩ := w
    obtain rfl : fork = wF := wSame.symm
    obtain ⟨valW, initialW, -⟩ := pre.registryLifecycle.validators i.toNat val initial
    have hwhole : (pre.append (post.snoc step)).append (after.append rest) =
        fromFin.append tailC := by
      show ((pre.append post).snoc step).append (after.append rest) = _
      rw [hpre]
      exact eqn
    have lift : ∀ {m' n' : ForkedBeaconState preset} (before' : Run config checks ⟨fork, wS⟩ m')
        (step' : Step config checks m' n') (after' : Run config checks n' ⟨fork, nS⟩),
        (before'.snoc step').append after' = post.snoc step →
        ((pre.append before').snoc step').append (after'.append (after.append rest)) =
          fromFin.append tailC := by
      intro m' n' before' step' after' cut''
      have shift : ((pre.append before').snoc step').append after' =
          pre.append ((before'.snoc step').append after') :=
        (Run.append_assoc pre (before'.snoc step') after').symm
      rw [Run.append_assoc, shift, cut'']
      exact hwhole
    obtain ⟨segEv, segOk⟩ := Run.balanceEvents_ok (post.snoc step) h.early
      (getCurrentEpoch pulled).toNat
    obtain ⟨preEv, preOk⟩ := Run.balanceEvents_ok pre h.early (getCurrentEpoch pulled).toNat
    obtain ⟨D, split, closed⟩ := segment_potential h h.near i clean pre (post.snoc step)
      (after.append rest) valW initialW
      (fun before' step' after' cut'' w found => retained (pre.append before') step'
        (after'.append (after.append rest)) (lift before' step' after' cut'') w found)
      0 ρn ρd (by omega)
      (fun before' step' after' cut'' evs ok => pass (pre.append before') step'
        (after'.append (after.append rest)) (lift before' step' after' cut'') evs ok)
      segOk
    have app := balanceEvents_append pre (post.snoc step) (getCurrentEpoch pulled).toNat preOk
      segOk
    obtain ⟨b, hb, isPrefix⟩ := Run.balanceEvents_prefix (pre.append (post.snoc step))
      (after.append rest) (getCurrentEpoch pulled).toNat events (by rw [hwhole]; exact replayed)
    have sameEv : b = preEv ++ segEv := Except.ok.inj (hb.symm.trans app)
    have sub : segEv.Sublist events := by
      rw [sameEv] at isPrefix
      exact (List.sublist_append_right _ _).trans isPrefix.sublist
    have syncLe : (segEv.map (Internal.syncDebit i.toNat)).sum ≤ (events.map (Internal.syncDebit
      i.toNat)).sum :=
      (sub.map (Internal.syncDebit i.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
    have partialSeg : (segEv.map (floorPartialDebit i)).sum ≤
        (events.map (floorPartialDebit i)).sum :=
      (sub.map (floorPartialDebit i)).sum_le_sum fun _ _ => Nat.zero_le _
    have splitDebit := floorPenaltyDebit_sum i.toNat segEv
    have cappedW : effectiveAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat ≤
        (withdrawalMaxEffectiveBalance preset fork valW).toNat :=
      DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax (toFin.append pre) h.genesis
        h.caps h.early initialW
    have preEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have restEpoch := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (after.append rest).chainSteps)
    simp only at preEpoch restEpoch
    have kept := stay_arith ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      ((getCurrentEpoch nS).toNat - (getCurrentEpoch wS).toNat)
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand base0 finEB
      (min (actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat)
        (withdrawalMaxEffectiveBalance preset fork valW).toNat) X
      ((pinTerms config pulled anc fin).partialsDue i.toNat)
      D (actualBalanceAt (⟨fork, nS⟩ : ForkedBeaconState preset) i.toNat)
      ((pinTerms config pulled anc fin).leakAt
        (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
      ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
      positive incPos h.facts.quarterBand big testB fallX first fall (by omega)
      (by have := h.near; omega) (by omega) (by omega) (by simpa using closed)
    omega
  · intro p member
    obtain ⟨r1, r2, -⟩ : ∃ (r1 : Run config checks ⟨fork, fin⟩ p)
        (r2 : Run config checks p ⟨fork, counted⟩), r1.append r2 = rp.append rest := by
      obtain ⟨r1, r2, whole⟩ := Internal.balancePath_endpoint rp rest (Nat.le_refl _) member
      exact ⟨r1, r2, whole⟩
    obtain ⟨w, found, mono⟩ := r1.validatorCap_mono h.caps.activation h.caps.compounding
      (forkEnd r2) i.toNat val initial
    have := UInt64.le_iff_toNat_le.mp mono
    simp only [PinTerms.capAt, found, Option.map_some, Option.getD_some]
    exact cappedFin.trans this

/-- A key whose exit comes late stays out of its withdrawal along a run from the finalized block.

Its exit epoch is constant from the state where it is set.

The withdrawable epoch is the delay after it, so it is after the horizon `high` of the call.

A key with no exit has the withdrawable epoch that no epoch reaches, since it exits no later. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.retained_of_exit (h : Setting
  config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {e : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (high : ℕ) (highLe : high ≤ (getCurrentEpoch pulled).toNat) (i : ValidatorIndex)
    {wE : Validator} (foundE : e.validators.data[i.toNat]? = some wE)
    (late : high + 1 < wE.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = fromFin.append tail → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      (high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          high + 1 < u.withdrawableEpoch.toNat) := by
  obtain ⟨toFin⟩ := h.toFin
  intro m n before step after cut w found
  refine .inr fun u foundU => ?_
  have holds := Run.invariant (Genesis.invariant h.genesis) (toFin.append before)
  obtain ⟨last, located, kept⟩ := ((Run.nil.snoc step).append after).registryLifecycle.validators
    i.toNat u foundU
  by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
  · have ordered := holds.exitsOrdered u (Array.mem_of_getElem? foundU)
    rw [unset] at ordered
    have := UInt64.le_iff_toNat_le.mp ordered
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
    omega
  · have same := congrArg UInt64.toNat (kept.exitEpoch unset)
    have lastEq : last = wE := Option.some.inj (located.symm.trans foundE)
    have delayed := (toFin.append before).exit_withdrawable_delay h.genesis i.toNat u foundU unset
    subst lastEq
    omega

/-- A key whose exit at R is at or before the finalized epoch has that exit at the finalized state.

A key absent from the finalized registry was created after it, and its exit is assigned after it.

An exit assigned after the finalized state is at least the seed lookahead past its epoch.

An exit assigned before it is kept along the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exit_kept_of_le_fin (h : Setting
  config checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat) :
    ∃ u, fin.validators.data[i]? = some u ∧ u.exitEpoch = w.exitEpoch := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  have late : ∀ c ∈ (fromFin.append toPulled).departureCharges,
      (getCurrentEpoch fin).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
    DirectSafety.Run.departureCharges_epoch_ge_start (fromFin.append toPulled)
      (Nat.le_trans (by decide) h.fulu) h.early
  cases foundFin : fin.validators.data[i]? with
  | none =>
    obtain ⟨charge, member, -, epoch⟩ := Internal.Run.charge_of_exit (fromFin.append toPulled)
      (Nat.le_trans (by decide) h.fulu) h.early i (fun v hv => nomatch hv.symm.trans foundFin) w
      foundPulled assigned
    have := late charge member
    omega
  | some u =>
    refine ⟨u, rfl, ?_⟩
    by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨charge, member, -, epoch⟩ := (fromFin.append toPulled).departure_charge_of_assigned
        i u w foundFin foundPulled unset assigned
      have := late charge member
      omega
    · obtain ⟨last, located, kept⟩ :=
        (fromFin.append toPulled).registryLifecycle.validators i u foundFin
      have lastEq : last = w := Option.some.inj (located.symm.trans foundPulled)
      rw [← lastEq]
      exact (kept.exitEpoch unset).symm

/-- The events of C's run from the finalized block are those of its two parts.

They are read at R's epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.V_events (h : Setting config checks
  g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat =
      .ok (eventsF ++ eventsC) := by
  have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have nearC := h.near
  refine balanceEvents_append fromFin tailC _ ?_ ?_
  · rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := high) (by simp only; omega)
      (by simp only; omega)]
    exact replayedF
  · rw [balanceEvents_eq_of_endpoint_le tailC (localHigh := highC) (by simp only; omega)
      (by simp only; omega)]
    exact replayedC

/-- The sync debits of a key over two runs are at most those that `cV_le` charges. -/
private theorem V_sync_le (eventsF eventsC : List (BalanceEvent preset)) (v : ℕ) :
    ((eventsF ++ eventsC).map (Internal.syncDebit v)).sum ≤
      (eventsF.map (Internal.syncDebit v)).sum + Internal.syncF eventsC v := by
  have := Internal.sum_syncDebit_eq eventsC v
  unfold Internal.syncF
  rw [List.map_append, List.sum_append]
  omega

/-- A key falls by at least its effective balance at R, less any bound of its floor.

A key that is not in the finalized registry has the floor zero. -/
private theorem fall_floor (h : Setting config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) (X : ℕ)
    (bound : fin.validators.data[v.toNat]? = none ∨
      (pinTerms config pulled anc fin).floorC v.toNat ≤ X) :
    (Internal.eR pulled v : ℤ) ≤ ((pinTerms config pulled anc fin).fall v.toNat : ℤ) + X := by
  have fallEq := Internal.fall_eq config pulled anc fin v.toNat
  simp only [h.shallow, ↓reduceIte] at fallEq
  have eRdef : Internal.eR pulled v = balanceAt pulled v.toNat := rfl
  rcases bound with none | le
  · obtain ⟨low, base, shape⟩ : ∃ low base : ℕ, (pinTerms config pulled anc fin).floorC v.toNat =
        if max (balanceAt fin v.toNat) base ≤ low + preset.downwardBand then balanceAt fin v.toNat
        else min (balanceAt fin v.toNat) (low - low % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :=
      ⟨_, _, rfl⟩
    have zero : balanceAt fin v.toNat = 0 := by simp [balanceAt, none]
    have : (pinTerms config pulled anc fin).floorC v.toNat = 0 := by
      rw [shape]
      split
      · exact zero
      · rw [zero]
        exact Nat.zero_min _
    omega
  · omega

/-- C's floor of a key is below its effective balance at each state of C's run, with its debits.

The debits are the key's sync debits over the run and their rounding band.

The key is in the finalized registry, unslashed at C's end, and kept out of withdrawal. -/
private theorem V_floor (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (val : Validator) (initial : fin.validators.data[v.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC) :
    (pinTerms config pulled anc fin).floorC v.toNat ≤ effectiveAt z v.toNat +
      (events.map (Internal.syncDebit v.toNat)).sum + Internal.bandR events v.toNat := by
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin h.bands.1 v.toNat
  obtain ⟨base0, hbase0def⟩ : ∃ b, b = (pinTerms config pulled anc fin).base0 v.toNat := ⟨_, rfl⟩
  have hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    hbase0def.trans (Internal.base0_of_found config pulled anc fin initial)
  obtain ⟨X, hX⟩ : ∃ X, X = ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        ((pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat +
            (pinTerms config pulled anc fin).gainRate v.toNat + 1) +
      (pinTerms config pulled anc fin).partialsDue v.toNat := ⟨_, rfl⟩
  have hfall : ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        ((pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      (pinTerms config pulled anc fin).partialsDue v.toNat ≤ X := by
    rw [hX]
    have := Nat.mul_le_mul_left ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
      (show (pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1 ≤
        (pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat +
            (pinTerms config pulled anc fin).gainRate v.toNat + 1 by omega)
    omega
  have hfloorC : (pinTerms config pulled anc fin).floorC v.toNat =
      if max (balanceAt fin v.toNat) base0 ≤ (base0 - X) + preset.downwardBand
      then balanceAt fin v.toNat
      else min (balanceAt fin v.toNat)
        ((base0 - X) - (base0 - X) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    rw [hX, hbase0def]
    rfl
  have hfin : balanceAt fin v.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat := rfl
  obtain ⟨slack, margin⟩ := floorC_margin h fromFin tailC replayed v val initial ρn ρd positive
    leaky above base0 X (base0 - X) hbase0 rfl hfall
  exact floorC_at h fromFin tailC replayed v val initial clean retained base0 X (base0 - X)
    (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).floorC v.toNat) hbase0 rfl hfin
    hfloorC rp rest cut ⟨slack, ρn, ρd, margin⟩
    (fun test sync => floorC_stay h fromFin tailC replayed v val initial clean retained
      ρn ρd positive leaky above base0 X (base0 - X) (balanceAt fin v.toNat)
      hbase0 rfl hfin hfall sync test rp rest cut)

/-- A V key that is active in C falls by at most `fall` and what C's floor leaves out.

C's floor is below the key's effective balance at C's end, plus its sync debits and their band.

The fall is the key's effective balance at R, less that floor, within the delay. -/
private theorem V_active (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ v ∈ V, v ∈ Internal.AC counted → (Internal.eR pulled v : ℤ) - Internal.eC counted v ≤
      ((pinTerms config pulled anc fin).fall v.toNat : ℤ) +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
          Internal.bandR (eventsF ++ eventsC) v.toNat := by
  intro v member act
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have delay := (Internal.Setting.delay h)
  obtain ⟨wC, foundC, isActive⟩ := Internal.active_of_activeVoters h.early (s := counted) act
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActive
  have exitAfter := UInt64.lt_iff_toNat_lt.mp isActive.2
  have clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
    intro w found
    rw [foundC] at found
    cases found
    simpa [slashedFlagAt, foundC] using (h.voting v member).2
  have sync := V_sync_le eventsF eventsC v.toNat
  have := fall_floor h v (balanceAt counted v.toNat + ((eventsF.map (Internal.syncDebit
    v.toNat)).sum +
      Internal.syncF eventsC v.toNat) + Internal.bandR (eventsF ++ eventsC) v.toNat) (by
    cases initial : fin.validators.data[v.toNat]? with
    | none => exact .inl rfl
    | some val =>
      have floor := V_floor h fromFin tailC
        (Internal.V_events h fromFin tailC high highC endEpoch endEpochC replayedF replayedC) v val
          initial
        clean (Internal.retained_of_exit h fromFin tailC _ (Nat.le_refl _) v foundC (by omega))
          (fromFin.append tailC)
        Run.nil rfl
      exact .inr (by
        have : effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat =
          balanceAt counted v.toNat := rfl
        omega))
  have eCdef : Internal.eC counted v = balanceAt counted v.toNat := rfl
  omega

/-- A V key that left C's active set is charged by its exit, its late activation or its floor.

Its activation is at most R's epoch.

If that is within the seed lookahead of the split, the two branches agree on its activity there.

Then C's record exits it by C's epoch, which R reads as exiting or C charges.

Otherwise R activated it after finalizing the split, and R reads it as late.

R's registry may hold a key that C's does not, since the registries differ by position.

Then `h.voting` holds with the unslashed flag read as false.

Such a key activates late at R, so it is in the second case. -/
private theorem V_left (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ v ∈ Internal.VN counted V, (Internal.eR pulled v : ℤ) ≤
      ((pinTerms config pulled anc fin).fall v.toNat +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
        Internal.bandR (eventsF ++ eventsC) v.toNat + Internal.exitQ tailC v.toNat +
        (if (pinTerms config pulled anc fin).exitingB v.toNat = true then Internal.eR pulled v else
          0) +
        (if (pinTerms config pulled anc fin).lateB v.toNat = true then Internal.eR pulled v
          else 0) : ℕ) := by
  intro v hv
  obtain ⟨member, notAC⟩ := Finset.mem_filter.mp hv
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨w, foundW, activeWb⟩ := Internal.active_of_activeVoters h.early (h.voting v member).1
  have activeW := activeWb
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt] at activeW
  have farEpoch := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have nearC := h.near
  by_cases early : w.activationEpoch.toNat ≤
      (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat
  · -- the key's activity at its activation epoch is shared, so C holds it
    have atAct : isActiveAt counted w.activationEpoch v.toNat = true := by
      rw [← Internal.activity_shared h (e := w.activationEpoch) early v.toNat]
      exact isActiveAt_eq_true_iff.mpr ⟨w, foundW, by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
        omega⟩
    obtain ⟨u, foundU, activeU⟩ := isActiveAt_eq_true_iff.mp atAct
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt] at activeU
    have exited : u.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
      by_contra later
      apply notAC
      simpa [Internal.AC, activeVoters] using mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨u, foundU, by
          simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
            UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
          omega⟩)
    have assigned : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at exited
      omega
    have unslashed : u.slashed = false := by
      simpa [slashedFlagAt, foundU] using (h.voting v member).2
    by_cases ex : (pinTerms config pulled anc fin).exitingB v.toNat = true
    · simp only [ex, ↓reduceIte]
      omega
    · obtain ⟨c, mem, idx⟩ := exit_charged h tailC foundU assigned exited unslashed
        (fun w' found _ => by
          obtain rfl : w' = w := Option.some.inj (found.symm.trans foundW)
          exact .inr (isActiveAt_eq_true_iff.mpr ⟨w', foundW, activeWb⟩))
        (by simpa using ex)
      have exitOf : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
          u.exitEpoch.toNat = c.epoch := by
        intro c' mem' idx'
        obtain ⟨x, found, -, epoch⟩ := Run.departure_charge_exit tailC c' mem'
        rw [idx'] at found
        obtain rfl : x = u := Option.some.inj (found.symm.trans foundU)
        exact epoch
      have startC := DirectSafety.Run.departureCharges_epoch_ge_start tailC
        (Nat.le_trans (by decide) h.fulu) h.early c mem
      simp only at startC
      have exitC := exitOf c mem idx
      have shallow := h.shallow
      have finOrder := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
      simp only at finOrder
      obtain ⟨sd, pre, post, cut, far, amount⟩ := exit_stop fromFin tailC v.toNat ⟨c, mem, idx⟩
        (fun c' mem' idx' => by have := exitOf c' mem' idx'; omega)
      have sync := V_sync_le eventsF eventsC v.toNat
      have clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
        intro w found
        rw [foundU] at found
        cases found
        exact unslashed
      have := fall_floor h v (Internal.exitQ tailC v.toNat + ((eventsF.map (Internal.syncDebit
        v.toNat)).sum +
          Internal.syncF eventsC v.toNat) + Internal.bandR (eventsF ++ eventsC) v.toNat) (by
        cases initial : fin.validators.data[v.toNat]? with
        | none => exact .inl rfl
        | some val =>
          have floor := V_floor h fromFin tailC
            (Internal.V_events h fromFin tailC high highC endEpoch endEpochC replayedF replayedC) v
              val
            initial clean
            (Internal.retained_of_exit h fromFin tailC _ (Nat.le_refl _) v foundU (by omega)) pre
              post cut
          exact .inr (by omega))
      omega
  · -- R activated the key after finalizing the split, so it reads the key as late
    have farAct : w.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at activeW
      omega
    have eligible := Run.eligibility_le_finalized ((toFin.append fromFin).append toPulled)
      h.genesis v.toNat w foundW farAct
    have finCur := UInt64.le_iff_toNat_le.mp (finalized_le_current h)
    have late := (Internal.lateB_iff config pulled anc fin v.toNat).mpr ⟨w, foundW, by
      have := UInt64.le_iff_toNat_le.mp eligible
      simp only at this
      omega, by omega⟩
    simp only [late, ↓reduceIte]
    omega

/-- The fall of the V keys, and the stake of the V keys that left C's active set. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cV_le (h : Setting config checks g
  split fin pulled anc counted V) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1) (events : List (BalanceEvent preset))
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    Internal.cV1 pulled counted V + Internal.cV2 pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ V, (Internal.syncD eventsF v.toNat + (Internal.syncF events v.toNat + Internal.syncF
          eventsC v.toNat))) +
        (∑ v ∈ V, Internal.credDepR events v.toNat) +
        (∑ v ∈ V, Internal.consAmt events v.toNat) + preset.upwardBand * Internal.dueAt fin high V +
        (∑ v ∈ (Internal.VN counted V), Internal.exitQ tailC v.toNat) +
        (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).exitingB v.toNat =
          true,
          Internal.eR pulled v) +
        (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
          Internal.eR pulled v) : ℕ) := by
  have base := cV_le_of h tailC
    (V_active h fromFin tailC high highC endEpoch endEpochC replayedF replayedC)
    (V_left h fromFin tailC high highC endEpoch endEpochC replayedF replayedC)
  have sync : ∑ v ∈ V, ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC
    v.toNat) ≤
      ∑ v ∈ V, (Internal.syncD eventsF v.toNat + (Internal.syncF events v.toNat + Internal.syncF
        eventsC v.toNat)) :=
    Finset.sum_le_sum fun v _ => by unfold Internal.syncD; omega
  refine le_trans base (Int.ofNat_le.mpr ?_)
  simp only [Internal.syncD, Finset.sum_add_distrib] at sync ⊢
  omega

end LowBound

/-- The low bound of an existing key is covered by its exit charge and its sync debits.

The key is activated at the finalized state, charged on the run, and exits by C.

The charge is its effective balance at the exit call.

The bound reads the floor of its balance from the finalized state.

The penalties are covered by `drop` and the partials by `partialsDue`.

The hysteresis is covered by the activation balance. -/
private theorem existing_low_le_charge (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    (pinTerms config pulled anc fin).lowEB v.toNat ≤
      Internal.exitQ tailC v.toNat + (events.map (Internal.syncDebit v.toNat)).sum := by
  have bound := existing_low_explicit h fromFin tailC replayed v epochLe val initial charged
  have drop : (pinTerms config pulled anc fin).drop v.toNat =
      ((pinTerms config pulled anc fin).leakAt
          (balanceAt fin v.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [Internal.drop_of_found config pulled anc fin initial, Internal.base0_of_found config pulled
      anc fin initial]
    rfl
  rw [Internal.lowEB_unfold, drop]
  exact bound

/-- The low and new-key floors are ordered: `newKeyFloor` is `newKeySlack` above `exitFloor`. -/
private theorem exitFloor_add_slack (h : Setting config checks g split fin pulled anc counted V) :
    (pinTerms config pulled anc fin).exitFloor + (pinTerms config pulled anc fin).newKeySlack =
      (pinTerms config pulled anc fin).newKeyFloor := by
  have newKey := h.facts.newKey fork
  have size := h.facts.incrementSize
  have floorEq : (pinTerms config pulled anc fin).newKeyFloor =
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat := rfl
  have exitEq : (pinTerms config pulled anc fin).exitFloor =
      max 1 (min (config.EJECTION_BALANCE.toNat - preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
        (pinTerms config pulled anc fin).newKeyFloor) := rfl
  have slack : (pinTerms config pulled anc fin).newKeySlack =
      (pinTerms config pulled anc fin).newKeyFloor -
        (pinTerms config pulled anc fin).exitFloor := rfl
  omega

/-- A key that is not yet activated at the finalized state and has a small charge loses seats.

The key is missing at the finalized state, or its activation there is unassigned.

It activates on the run from the finalized state.

So it keeps at least `newKeyFloor` of effective balance less its sync debits.

This is `Run.new_key_effective_floor`.

A small charge is below `exitFloor`, so the debits exceed `newKeySlack`.

It has no partial withdrawals queued, since a request needs an active key. -/
private theorem pending_key_claim (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (small : Internal.exitQ tailC v.toNat < (pinTerms config pulled anc fin).exitFloor)
    (fresh : fin.validators.data[v.toNat]? = none ∨
      ∃ w, fin.validators.data[v.toNat]? = some w ∧ w.activationEpoch = FAR_FUTURE_EPOCH) :
    (pinTerms config pulled anc fin).newKeySlack < (events.map (Internal.syncDebit v.toNat)).sum :=
      by
  -- The charge splits C's run at the step that exits the key.
  --
  -- The key is activated there, by `charge_activated`.
  --
  -- The key is active at that state, so the floor of a new key reads its effective balance.
  --
  -- That balance is the charge, and the floor adds the key's sync debits and partial payments.
  --
  -- The partial payments are none, since no queued entry names the key at the finalized state.
  --
  -- An entry queued later is not due in the window.
  classical
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨c, cMember, cIndex⟩ := charged
  obtain ⟨a, b, pre, step, post, split', vv, w, found, foundB, unset, set, activated, amount,
    epoch⟩ := Internal.charge_activated (x := ⟨fork, split⟩) electra tailC c
    (tailC.departure_charge_site c cMember)
  rw [cIndex] at found foundB
  -- the charge counts, so `exitQ` is its amount
  have exitQEq : Internal.exitQ tailC v.toNat = c.amount := by
    rcases Internal.exitQ_cases tailC v.toNat with ⟨none, -⟩ | ⟨d, dMember, dIndex, -, dQ⟩
    · exact absurd (epochLe c cMember cIndex) (none c cMember cIndex)
    · rw [dQ, Internal.charge_unique tailC dMember cMember (dIndex.trans cIndex.symm)]
  -- the run from the finalized state to the exit step, and its events, a prefix of the replay
  have shape : fromFin.append ((pre.snoc step).append post) =
      (fromFin.append pre).append ((Run.nil.snoc step).append post) := by
    rw [pre.snoc_append_eq, Run.append_assoc]
  rw [← split', shape] at replayed
  obtain ⟨prior, priorOk, isPrefix⟩ := Run.balanceEvents_prefix (fromFin.append pre)
    ((Run.nil.snoc step).append post) (getCurrentEpoch pulled).toNat events replayed
  have aEpoch : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch counted).toNat :=
    UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
  have aInside : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := h.near
    omega
  have aEarly : a.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
      h.early
  have finite : (getCurrentEpoch a.state).toNat < FAR_FUTURE_EPOCH.toNat := by
    have ne := getCurrentEpoch_ne_farFuture h.twoSlots a.state
    have := (getCurrentEpoch a.state).toNat_lt
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have : (getCurrentEpoch a.state).toNat ≠ FAR_FUTURE_EPOCH.toNat := fun eq =>
      ne (UInt64.toNat_inj.mp eq)
    omega
  have active : isActiveAt a.state (getCurrentEpoch a.state) v.toNat = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨vv, found, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨activated, by rw [unset]; exact UInt64.lt_iff_toNat_lt.mpr finite⟩
  have pending : ∀ u, fin.validators.data[v.toNat]? = some u →
      (getCurrentEpoch (⟨fork, fin⟩ : ForkedBeaconState preset).state).toNat + 1 <
        u.activationEpoch.toNat := by
    intro u foundFin
    rcases fresh with none | ⟨u', foundFin', far⟩
    · rw [none] at foundFin
      cases foundFin
    · obtain rfl := Option.some.inj (foundFin.symm.trans foundFin')
      rw [far]
      exact getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
  have floor := Internal.Run.new_key_effective_floor toFin h.genesis h.parameters h.caps h.aligned
    h.twoSlots electra h.fulu (getCurrentEpoch pulled).toNat h.guard (fromFin.append pre) aEarly
    aInside h.window (Internal.Setting.delay h) h.bands h.facts v.toNat pending active priorOk
  -- no queued partial withdrawal names the key at the finalized state, which has no activation
  have genesisPartials : Internal.AssignedPartials g.state := by
    obtain ⟨_, _, _, initialized⟩ := h.genesis
    have before := (initializeBeaconStateFromEth1_ok initialized).1
    intro fork
    exact (Nat.not_le_of_lt before (Nat.le_trans (by decide) fork)).elim
  have finPartials : Internal.AssignedPartials fin :=
    (Internal.CapStep.run toFin h.caps.activation h.caps.compounding h.early).2.1 genesisPartials
  have noEntry : ((((fin.pendingPartialWithdrawals electra).data.toList.filter
      fun entry => decide (entry.validatorIndex = v)).filter
        (fun entry => entry.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
          (·.amount.toNat)).sum = 0 := by
    have none : (fin.pendingPartialWithdrawals electra).data.toList.filter
        (fun entry => decide (entry.validatorIndex = v)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro entry member same
      obtain ⟨u, foundU, assignedU⟩ := finPartials electra entry member
      rw [of_decide_eq_true same] at foundU
      rcases fresh with absent | ⟨u', foundU', far⟩
      · rw [absent] at foundU
        cases foundU
      · obtain rfl := Option.some.inj (foundU.symm.trans foundU')
        exact assignedU far
    rw [none]
    rfl
  have debits := Internal.Run.partialDebit_le (fromFin.append pre) electra aEarly
    (getCurrentEpoch pulled).toNat ((getCurrentEpoch pulled).toNat + 1) aInside
    (Internal.window_short h) v priorOk
  have toUInt : v.toNat.toUInt64 = v := by simp
  have partials : (prior.map (DirectSafety.Apriori.Internal.floorPartialDebit
      v.toNat.toUInt64)).sum = 0 := by
    rw [toUInt]
    exact Nat.le_zero.mp (noEntry ▸ debits)
  have order := exitFloor_add_slack h
  have floorEq : (pinTerms config pulled anc fin).newKeyFloor =
      2 * preset.MAX_EFFECTIVE_BALANCE.toNat / 3 -
        preset.MAX_EFFECTIVE_BALANCE.toNat /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        preset.downwardBand - preset.EFFECTIVE_BALANCE_INCREMENT.toNat := rfl
  rw [parameters_of_fusaka h.fulu h.early] at floorEq
  have effective : effectiveAt a v.toNat = c.amount := by
    simp only [effectiveAt, found, Option.map_some, Option.getD_some]
    exact amount.symm
  have prefixSum : (prior.map (Internal.syncDebit v.toNat)).sum ≤ (events.map (Internal.syncDebit
    v.toNat)).sum := by
    obtain ⟨rest, rfl⟩ := isPrefix
    simp only [List.map_append, List.sum_append]
    omega
  omega

/-- A key of `K5` that is not exiting at the call and has a small charge is low or loses seats.

A small charge is below `exitFloor`.

The key is then a low key, or its sync debits from the finalized state exceed `newKeySlack`.

The debits are those of the replay of the run from the finalized state to C's state.

A key that is not activated at the finalized state loses seats, by `pending_key_claim`.

An activated key is active and not withdrawable at R, by `activated_key_at_pulled`.

Its low bound is covered by its charge and its debits, by `existing_low_le_charge`. -/
private theorem small_charge_claim (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (activatedBy : ∀ c, counted.validators.data[v.toNat]? = some c →
      c.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (small : Internal.exitQ tailC v.toNat < (pinTerms config pulled anc fin).exitFloor) :
    (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (Internal.syncDebit v.toNat)).sum
        := by
  classical
  by_cases fresh : fin.validators.data[v.toNat]? = none ∨
      ∃ w, fin.validators.data[v.toNat]? = some w ∧ w.activationEpoch = FAR_FUTURE_EPOCH
  · exact .inr (pending_key_claim h fromFin tailC replayed v epochLe charged small fresh)
  obtain ⟨absent, notFar⟩ := not_or.mp fresh
  obtain ⟨w, found⟩ := Option.ne_none_iff_exists'.mp absent
  have activated : w.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far => notFar ⟨w, found, far⟩
  by_cases rich : (pinTerms config pulled anc fin).newKeySlack <
      (events.map (Internal.syncDebit v.toNat)).sum
  · exact .inr rich
  refine .inl (lowB_intro config pulled anc fin
    (activated_key_at_pulled h tailC v activatedBy charged found activated) ?_)
  have floor := existing_low_le_charge h fromFin tailC replayed v epochLe w found charged
  have order := exitFloor_add_slack h
  omega

/-- The total active balance at each step of a run from the finalized state is bounded.

It is at most three halves of the pulled total.

The run ends at most one epoch after the pulled epoch.

This is `total_band_of_guard` at the states of the steps of the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.step_band_of_guard (h : Setting
  config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (r : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {pulledTotal : Gwei} (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      r.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  intro u w step member T read
  obtain ⟨pre, post, _, _, _⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have wEarly : w.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have wEpoch : (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch e).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  exact Internal.total_band_of_guard shared h.genesis h.parameters h.caps h.aligned h.twoSlots
    electra
    h.guard (fromFin.append toPulled) h.early (Nat.le_succ _) (pre.snoc step) wEarly
    (by omega) pulledOk read

/-- The sync debits of any keys over a run from the finalized block fit the window's envelope.

The run ends within one epoch of R's, and its events are read at R's epoch.

The seats of the window debit at most its slots' envelopes, one for each epoch to the run's end. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncDebits_window_le (h : Setting
  config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)}
    (replayed : run.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, (events.map (Internal.syncDebit v.toNat)).sum ≤
      ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      run.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat :=
    Internal.step_band_of_guard h run within pulledOk
  have debits := (Internal.Run.syncDebits_le run h.fulu h.early (getCurrentEpoch pulled).toNat
    replayed pulledTotal.toNat band (S.image fun v : ValidatorIndex => v.toNat)).1
  rw [Finset.sum_image fun _ _ _ _ same => UInt64.toNat_inj.mp same] at debits
  rwa [pulledOk]

/-- The keys whose sync debits from the finalized state exceed `newKeySlack` are at most the seats.

The sync debits of any keys over the run from the finalized state to C's state fit one envelope.

The envelope is for each seat and slot of the window.

A key over the slack has at least one more than the slack.

So the keys number at most the debits over the slack. -/
private theorem card_seat_keys_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (B : Finset ValidatorIndex)
    (seats : ∀ v ∈ B, (pinTerms config pulled anc fin).newKeySlack <
      (events.map (Internal.syncDebit v.toNat)).sum) :
    B.card ≤ (pinTerms config pulled anc fin).newKeySeats := by
  classical
  have debits := Internal.syncDebits_window_le h (fromFin.append tailC) h.near replayed B
  have each : B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) ≤
      ∑ v ∈ B, (events.map (Internal.syncDebit v.toNat)).sum := by
    have := Finset.card_nsmul_le_sum B
      (fun v : ValidatorIndex => (events.map (Internal.syncDebit v.toNat)).sum)
      ((pinTerms config pulled anc fin).newKeySlack + 1) fun v member => seats v member
    simpa [smul_eq_mul] using this
  have seatsEq : (pinTerms config pulled anc fin).newKeySeats =
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat /
            max 1 (pinTerms config pulled anc fin).newKeySlack := rfl
  rw [seatsEq, Nat.le_div_iff_mul_le (lt_max_of_lt_left Nat.one_pos)]
  have epochs : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by have := h.near; omega
  have window := Nat.mul_le_mul_right
    (PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat)
    (Nat.mul_le_mul_right preset.SYNC_COMMITTEE_SIZE.toNat
      (Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat epochs))
  have unit : max 1 (pinTerms config pulled anc fin).newKeySlack ≤
      (pinTerms config pulled anc fin).newKeySlack + 1 := by omega
  calc B.card * max 1 (pinTerms config pulled anc fin).newKeySlack
      ≤ B.card * ((pinTerms config pulled anc fin).newKeySlack + 1) := Nat.mul_le_mul_left _ unit
    _ ≤ _ := each
    _ ≤ _ := debits
    _ ≤ _ := by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using window

/-- The keys that C's branch charges are few, if each is activated by R's epoch and exits by C.

A key is charged if the run has a departure charge at its position.

`card_big_charges_le` counts the charges of at least `exitFloor`.

`small_charge_claim` counts the small ones, and reads no exit flag of R.

They are at most the keys that `queueKeys` counts.

Those are the keys with a large charge, the low keys and the keys that lose seats. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.charged_count_of (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (S : Finset ValidatorIndex)
    (keys : ∀ v ∈ S, (∀ c, counted.validators.data[v.toNat]? = some c →
        c.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat) ∧
      (∀ c ∈ tailC.departureCharges, c.index = v.toNat →
        c.epoch ≤ (getCurrentEpoch counted).toNat) ∧
      ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    S.card ≤ (pinTerms config pulled anc fin).queueKeys := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨events, replayed⟩ := (fromFin.append tailC).balanceEvents_ok h.early
    (getCurrentEpoch pulled).toNat
  have big := card_big_charges_le h tailC S
  set small := S.filter fun v => ¬ (pinTerms config pulled anc fin).exitFloor ≤
    Internal.exitQ tailC v.toNat with hSmall
  have claim : ∀ v ∈ small, (pinTerms config pulled anc fin).lowB v.toNat = true ∨
      (pinTerms config pulled anc fin).newKeySlack < (events.map (Internal.syncDebit v.toNat)).sum
        := by
    intro v member
    obtain ⟨inS, notBig⟩ := Finset.mem_filter.mp member
    obtain ⟨activatedBy, epochLe, charged⟩ := keys v inS
    exact small_charge_claim h fromFin tailC replayed v activatedBy epochLe charged
      (Nat.lt_of_not_ge notBig)
  have seats := card_seat_keys_le h fromFin tailC replayed
    (small.filter fun v => ¬ (pinTerms config pulled anc fin).lowB v.toNat = true) (by
      intro v member
      obtain ⟨inSmall, notLow⟩ := Finset.mem_filter.mp member
      exact (claim v inSmall).resolve_left notLow)
  have lows : (small.filter fun v => (pinTerms config pulled anc fin).lowB v.toNat = true).card ≤
      (pinTerms config pulled anc fin).lowKeys := by
    rw [Internal.lowKeys_eq]
    have count := voters_sum_le (voters := small.filter fun v =>
        (pinTerms config pulled anc fin).lowB v.toNat = true)
      (positions := (pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).lowB i = true) (fun _ => 1) (fun v member => by
      have low := (Finset.mem_filter.mp member).2
      obtain ⟨w, found⟩ := lowB_found config pulled anc fin low
      exact Internal.mem_positions_filter config pulled anc fin found low)
    simpa using count
  have coverSmall : small ⊆
      (small.filter fun v => (pinTerms config pulled anc fin).lowB v.toNat = true) ∪
        (small.filter fun v => ¬ (pinTerms config pulled anc fin).lowB v.toNat = true) := by
    intro v member
    by_cases low : (pinTerms config pulled anc fin).lowB v.toNat = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member, low⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member, low⟩)
  have coverS : S ⊆ (S.filter fun v => (pinTerms config pulled anc fin).exitFloor ≤
      Internal.exitQ tailC v.toNat) ∪ small := by
    intro v member
    by_cases large : (pinTerms config pulled anc fin).exitFloor ≤ Internal.exitQ tailC v.toNat
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨member, large⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨member, large⟩)
  have splitS := (Finset.card_le_card coverS).trans (Finset.card_union_le _ _)
  have splitSmall := (Finset.card_le_card coverSmall).trans (Finset.card_union_le _ _)
  rw [Internal.queueKeys_unfold]
  omega

/-- The keys of `K5` that C's branch charges are few.

Each is activated by R's epoch, since it is active in the epoch before C's. -/
private theorem charged_count (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    ((Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat).card ≤
      (pinTerms config pulled anc fin).queueKeys := by
  refine Internal.charged_count_of h tailC _ fun v member => ?_
  obtain ⟨inK5, charged⟩ := Finset.mem_filter.mp member
  refine ⟨fun c foundC => ?_, charge_epoch_le_of_K5 h tailC inK5, charged⟩
  obtain ⟨u, foundU, activeBefore, -⟩ := Internal.K5_previous_only h inK5
  obtain rfl : u = c := Option.some.inj (foundU.symm.trans foundC)
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeBefore
  have low := UInt64.le_iff_toNat_le.mp activeBefore.1
  have previous := getPreviousEpoch_toNat counted
  have near := h.near
  omega

/-- K5 bands: the two bands beyond `credits`' one of each credited K5 key, weight 3.

Split by `exitingB`: the keys whose exit R reads and those the queues let exit on C. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_exitingBands (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    2 * (∑ v ∈ (Internal.K5 counted V), Internal.bandC tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).exitingBands :=
  two_bands_le_exitingBands config pulled anc fin counted V tailC highC
    (fun _ member flag _ => K5_charged h tailC member flag) (charged_count h tailC)

/-- K5 (`queueRise`): the rise of keys after their exit starts on C's branch.

Every key of `K5` with a departure charge counts, since `charged_count` bounds all of them. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_queueRise (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    3 * (∑ v ∈ (Internal.K5 counted V) with ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        Internal.riseQ tailC highC v.toNat) ≤
      (pinTerms config pulled anc fin).queueRise := by
  classical
  rw [Internal.queueRise_unfold]
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  have later := UInt64.le_iff_toNat_le.mp h.later
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · simp only [tight, ↓reduceIte]
    have tightLe : (pinTerms config pulled anc fin).depth ≤ 1 + preset.MAX_SEED_LOOKAHEAD.toNat :=
      of_decide_eq_true tight
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    rw [depthEq] at tightLe
    have none : ∀ v ∈ (Internal.K5 counted V).filter
        (fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat),
        Internal.riseQ tailC highC v.toNat = 0 := by
      intro v member
      apply Internal.riseQ_eq_zero
      intro c charged same
      have inside := charge_epoch_le_of_K5 h tailC (Finset.mem_filter.mp member).1 c
        charged same
      have far : (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
        DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c charged
      omega
    rw [Finset.sum_eq_zero none]
    simp
  · simp only [tight, Bool.false_eq_true, ↓reduceIte]
    have sumEq := Finset.sum_filter_ne_zero
      (s := (Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      (f := fun v : ValidatorIndex => Internal.riseQ tailC highC v.toNat)
    have each := Finset.sum_le_card_nsmul
      (((Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
        v.toNat).filter
          fun v => Internal.riseQ tailC highC v.toNat ≠ 0)
      (fun v : ValidatorIndex => Internal.riseQ tailC highC v.toNat)
      (preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).gainRateMax)
      fun v _ => Internal.riseQ_le h tailC highC v.toNat
    have count := (Finset.card_le_card (Finset.filter_subset
      (fun v : ValidatorIndex => Internal.riseQ tailC highC v.toNat ≠ 0)
      ((Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index =
        v.toNat))).trans
      (charged_count h tailC)
    rw [smul_eq_mul] at each
    rw [← sumEq]
    calc _ ≤ 3 * ((((Internal.K5 counted V).filter fun v =>
            ∃ c ∈ tailC.departureCharges, c.index = v.toNat).filter
          fun v => Internal.riseQ tailC highC v.toNat ≠ 0).card *
        (preset.upwardBand + (pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).gainRateMax)) := Nat.mul_le_mul_left _ each
      _ ≤ _ := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ count)

/-- K5 (`exitingRise`): the keys whose exit R reads.

The keys of `K5` are those without a departure charge on C's run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_exitingRise (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (∑ v ∈ (Internal.K5 counted V) with ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat,
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).exitingB v.toNat =
        true,
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).exitingRise := by
  classical
  have exitingRise : (pinTerms config pulled anc fin).exitingRise =
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).exitingB i = true,
        (pinTerms config pulled anc fin).rise i := by
    simp only [pinTerms, decide_eq_true_eq]
  have apart : Disjoint
      ((Internal.K5 counted V).filter fun v => ¬ ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
      ((Internal.K6 pulled counted).filter fun v =>
        (pinTerms config pulled anc fin).exitingB v.toNat = true) := by
    refine Finset.disjoint_left.mpr fun v first second => ?_
    have active := (Finset.mem_filter.mp (Finset.mem_filter.mp second).1).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp first).1).2.1 active
  rw [← Finset.sum_union apart, exitingRise]
  refine voters_sum_le (pinTerms config pulled anc fin).rise fun v selected => ?_
  have exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true := by
    rcases Finset.mem_union.mp selected with chosen | chosen
    · exact K5_exiting_of_not_charged h tailC (Finset.mem_filter.mp chosen).1
        (Finset.mem_filter.mp chosen).2
    · exact (Finset.mem_filter.mp chosen).2
  have found : ∃ w, pulled.validators.data[v.toNat]? = some w := by
    obtain ⟨-, -, read⟩ := (by simpa only [pinTerms, decide_eq_true_eq] using exiting :
      _ ∧ _ ∧ ((pulled.validators.data[v.toNat]?).map fun w =>
        decide (w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).getD false = true)
    exact Internal.validator_of_flag (.inr read)
  obtain ⟨w, found⟩ := found
  exact Internal.mem_positions_filter config pulled anc fin found exiting

/-- The credits of a set of keys in one event are at most the event's credit limit. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_keyCredit_le_creditLimit (S :
  Finset ValidatorIndex) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) : ∑ v ∈ S, Internal.keyCredit v.toNat e ≤ e.creditLimit :=
      by
  refine Nat.le_trans ?_ bounded
  unfold Internal.keyCredit
  have inj : Set.InjOn (fun v : ValidatorIndex => v.toNat) S := fun a _ b _ same =>
    UInt64.toNat_inj.mp same
  rw [← Finset.sum_image (f := fun i => actualBalanceAt e.after i - actualBalanceAt e.before i)
    inj]
  exact Internal.keys_credits_le _ e

/-- The block credits of one epoch, against the pin's rate on the pulled total.

The rewards of the epoch are at most `54 / 448` of the rate on each active set.

Each active set is at most the total, which is within three halves of the pulled total. -/
private theorem propN_arith {inc c pi pq a b total T : ℕ} (incPos : 0 < inc)
    (credits : c * 448 ≤ 54 * pi * (a + b)) (prev : pi * a ≤ pq * (total / inc))
    (curr : pi * b ≤ pq * (total / inc)) (band : 2 * total ≤ 3 * T) :
    c * 896 ≤ 324 * (pq * (T / inc)) + 216 * pq := by
  have h1 := Nat.div_mul_le_self total inc
  have h2 := Nat.lt_mul_div_succ T incPos
  have K2 : 2 * (total / inc) ≤ 3 * (T / inc) + 2 := by
    have : 2 * (total / inc) * inc < (3 * (T / inc) + 3) * inc := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have e : c * 448 ≤ 54 * (2 * (pq * (total / inc))) := by
    calc c * 448 ≤ 54 * pi * (a + b) := credits
      _ = 54 * (pi * a + pi * b) := by ring
      _ ≤ _ := by omega
  calc c * 896 = 2 * (c * 448) := by ring
    _ ≤ 2 * (54 * (2 * (pq * (total / inc)))) := by omega
    _ = 108 * (pq * (2 * (total / inc))) := by ring
    _ ≤ 108 * (pq * (3 * (T / inc) + 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ K2)
    _ = 324 * (pq * (T / inc)) + 216 * pq := by ring

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The reward rate and the total at the start of a run in `fin`'s epoch or later are bounded.

The state is reached from `fin`, or it precedes `fin` in its epoch and reads what `fin` reads. -/
private theorem start_rates (h : Setting config checks g split fin pulled anc counted V)
    {m : BeaconState preset fork}
    (within : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, m⟩) ∨
      ∃ _ : Run config checks ⟨fork, m⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch m)
    {pq : Gwei} (pqOk : getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq)
    {T : Gwei} (pulledOk : getTotalActiveBalance pulled = .ok T)
    {total perIncrement : Gwei} (totalOk : getTotalActiveBalance m = .ok total)
    (per : getBaseRewardPerIncrement preset total = .ok perIncrement) :
    perIncrement.toNat * ((∑ i ∈ (getActiveValidatorIndices m (getPreviousEpoch m)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      pq.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
    perIncrement.toNat * ((∑ i ∈ (getActiveValidatorIndices m (getCurrentEpoch m)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      pq.toNat * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
    2 * total.toNat ≤ 3 * T.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rcases link with toMne | ⟨back, same⟩
  · obtain ⟨toM⟩ := toMne
    exact ⟨rate_of_guard h toM within (Or.inl rfl) pqOk total perIncrement totalOk per,
      rate_of_guard h toM within (Or.inr rfl) pqOk total perIncrement totalOk per,
      Internal.total_band_of_guard toFin h.genesis h.parameters h.caps h.aligned h.twoSlots electra
        h.guard (fromFin.append toPulled) h.early (Nat.le_succ _) toM h.early within pulledOk
        totalOk⟩
  · have current := activeStake_eq_of_same_epoch back h.early same (getCurrentEpoch m)
      (UInt64.le_refl _)
    have previous := activeStake_eq_of_same_epoch back h.early same (getPreviousEpoch m)
      (getPreviousEpoch_le _)
    have previousSame : getPreviousEpoch fin = getPreviousEpoch m := by
      simp only [getPreviousEpoch, same]
    obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok totalOk)
    change total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (∑ i ∈ (getActiveValidatorIndices m (getCurrentEpoch m)).toFinset,
        effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) at value
    obtain ⟨atFin, atFinOk, atFinValue⟩ := totalActive_exists (s := fin) h.early (by
      rw [same, current]
      exact Nat.lt_of_le_of_lt (by rw [value]; exact le_max_right _ _) total.toNat_lt)
    simp only [same] at atFinValue
    have amounts : atFin = total := UInt64.toNat_inj.mp (by rw [atFinValue, current, value])
    subst amounts
    have inside : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
      rw [same]
      exact within
    have first := rate_of_guard h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) inside
      (Or.inl rfl) pqOk atFin perIncrement atFinOk per
    have second := rate_of_guard h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) inside
      (Or.inr rfl) pqOk atFin perIncrement atFinOk per
    refine ⟨?_, ?_, Internal.total_band_of_guard toFin h.genesis h.parameters h.caps h.aligned
      h.twoSlots electra h.guard (fromFin.append toPulled) h.early (Nat.le_succ _)
      (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) h.early inside pulledOk atFinOk⟩
    · rw [previousSame, previous] at first
      exact first
    · rw [same, current] at second
      exact second

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The proposer credits of a set of keys over a run inside one epoch of C's branch are bounded.

The bound is the pin's rate on the pulled total, with `896` times the credits on the left.

The block steps of the run credit at most `54 / 448` of the rate on the active increments.

A run with no reads of the rate credits nothing. -/
private theorem propN_epoch_le (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) (S : Finset ValidatorIndex) {T : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok T) {m : BeaconState preset fork}
    (toM : Run config checks g ⟨fork, m⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, m⟩) ∨
      ∃ _ : Run config checks ⟨fork, m⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch m)
    {u : ForkedBeaconState preset}
    (inner : Run config checks ⟨fork, m⟩ u) (rest : Run config checks u ⟨fork, counted⟩)
    (same : getCurrentEpoch u.state = getCurrentEpoch m) :
    (∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      inner)) * 896 ≤
      324 * ((pinTerms config pulled anc fin).perIncrement *
        (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have uFork : u.fork = fork := Internal.fork_eq_of_run inner rest (Nat.le_refl _)
  have uEarly : u.fork < .glamsterdam := by rw [uFork]; exact h.early
  have within : (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (inner.append rest).chainSteps)) h.near
  obtain ⟨events, replayed, bounded⟩ :=
    Run.balanceEvents_bounded toM inner h.genesis uEarly highC
  have scan : ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false)
    v.toNat highC
      inner) ≤ sourceCredits .rewards events := by
    have := Internal.creditScan_sum_le S UInt64.toNat (fun s => decide (s = .rewards)) (fun _ =>
      false) highC
      (fun e => e.creditLimit) inner replayed fun e member _ =>
        Internal.sum_keyCredit_le_creditLimit S e (bounded e member).1
    simpa [sourceCredits] using this
  obtain ⟨reads, data⟩ := epoch_credits_data inner (by exact electra) uEarly same highC replayed
  rcases reads with ⟨total, perIncrement, totalOk, per⟩ | ⟨quiet, -⟩
  swap
  · rw [quiet] at scan
    simp [Nat.le_zero.mp scan]
  obtain ⟨credits, -⟩ := data total perIncrement totalOk per
  obtain ⟨pq, pqOk⟩ := quarter_base_ok h.facts per ((getTotalActiveBalance pulled).toOption.getD 0)
  obtain ⟨prev, curr, band⟩ := start_rates h within link pqOk pulledOk totalOk per
  have rate : (pinTerms config pulled anc fin).perIncrement = pq.toNat := by
    show ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat = pq.toNat
    rw [pqOk]
    rfl
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  rw [rate]
  exact Nat.le_trans (Nat.mul_le_mul_right 896 scan)
    (propN_arith incPos credits prev curr band)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The proposer credits of a set of keys over a one-epoch segment of C's branch are bounded.

The segment may follow a run `head` of its own epoch, whose credits it adds to.

The bound is the pin's rate on the pulled total, with `896` times the credits on the left.

The slot that ends the segment adds no block credit.

So the segment fits as its run before that slot does. -/
private theorem propN_segment_le (h : Setting config checks g split fin pulled anc counted V)
    (highC : ℕ) (S : Finset ValidatorIndex) {T : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok T) {s0 : BeaconState preset fork}
    {m n : ForkedBeaconState preset} (toS : Run config checks g ⟨fork, s0⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, s0⟩) ∨
      ∃ _ : Run config checks ⟨fork, s0⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch s0)
    (head : Run config checks ⟨fork, s0⟩ m) (mid : Run config checks m n)
    (rest : Run config checks n ⟨fork, counted⟩)
    (sameStart : getCurrentEpoch m.state = getCurrentEpoch s0)
    (starts : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      mid.Contains step → getCurrentEpoch u.state = getCurrentEpoch m.state) :
    ((∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat highC
      head)) + ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false)
        v.toNat
        highC mid)) * 896 ≤
      324 * ((pinTerms config pulled anc fin).perIncrement *
        (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement := by
  have mFork : m.fork = fork := Internal.fork_eq_of_run head (mid.append rest) (Nat.le_refl _)
  obtain ⟨mf, ms⟩ := m
  obtain rfl : mf = fork := mFork
  rcases DirectSafety.Apriori.Internal.segment_slot_cases mid starts with same |
    ⟨u, inner, boundary, rfl, uEpoch, -⟩
  · have whole := propN_epoch_le h highC S pulledOk toS link (head.append mid) rest
      (same.trans sameStart)
    simp only [Internal.creditScan_append, Finset.sum_add_distrib] at whole
    exact whole
  · have whole := propN_epoch_le h highC S pulledOk toS link (head.append inner)
      ((Run.nil.snoc (Step.slot boundary)).append rest) (uEpoch.trans sameStart)
    simp only [Internal.creditScan_append, Finset.sum_add_distrib] at whole
    refine Nat.le_trans (Nat.mul_le_mul_right 896 (Nat.add_le_add_left
      (Finset.sum_le_sum fun v _ => ?_) _)) whole
    rw [Internal.creditScan_snoc]
    split <;> simp [Internal.stepCredit]

/-- The whole increments of aligned stakes are at most those of larger stakes on a larger set. -/
private theorem stake_le_base {α : Type} {inc pq : ℕ} {P : Finset ℕ} {f : ℕ → ℕ} {A : Finset α}
    {g : α → ℕ} (e : ℕ → ℕ) (incPos : 0 < inc) (inj : Set.InjOn g A)
    (inside : ∀ a ∈ A, g a ∈ P) (le : ∀ a ∈ A, e (g a) ≤ f (g a)) (dvd : ∀ j, inc ∣ e j) :
    pq * ((∑ a ∈ A, e (g a)) / inc) ≤ ∑ j ∈ P, f j / inc * pq := by
  rw [← Finset.sum_image (f := e) inj]
  have exact : ∑ j ∈ A.image g, e j = inc * ∑ j ∈ A.image g, e j / inc := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (Nat.mul_div_cancel' (dvd j)).symm
  rw [exact, Nat.mul_div_cancel_left _ incPos, Finset.mul_sum]
  refine Nat.le_trans (Finset.sum_le_sum fun j member => ?_)
    (Finset.sum_le_sum_of_subset (f := fun j => f j / inc * pq) fun j member => ?_)
  · obtain ⟨a, inA, rfl⟩ := Finset.mem_image.mp member
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right (le a inA))
  · obtain ⟨a, inA, rfl⟩ := Finset.mem_image.mp member
    exact inside a inA

/-- The epoch bound of the pin's rate on the pulled total is at most the proposer credit.

The proposer base pays the bound, and `attesterExcess` pays one more increment's rate. -/
private theorem credit_arith {inc pi E T P A : ℕ} (incPos : 0 < inc) (hT : T = max inc E)
    (hP : pi * (E / inc) ≤ P) (hA : 1 ≤ A) :
    (324 * (pi * (T / inc)) + 216 * pi) / 896 ≤ P + A * pi := by
  have one : T / inc ≤ E / inc + 1 := by
    rw [hT]
    rcases le_total inc E with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h, Nat.div_self incPos]; exact Nat.le_add_left _ _
  have mul : pi * (T / inc) ≤ pi * (E / inc) + pi := by
    calc pi * (T / inc) ≤ pi * (E / inc + 1) := Nat.mul_le_mul_left _ one
      _ = _ := by ring
  have A1 : pi ≤ A * pi := Nat.le_mul_of_pos_left _ hA
  refine Nat.div_le_of_le_mul ?_
  nlinarith

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- C's proposer credits to any set of keys, with the sync part of the bound, are bounded.

The credits start at a state `b` of the split's epoch, so they include the run `pre` from `b`.

The bound is the proposer credit of each epoch of the window.

The credits of each epoch are cut over the blocks, and the split's epoch is cut once from `b`.

So the flag rewards of its epoch pass are not read. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.proposer_rewards_le (h : Setting
  config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (S : Finset ValidatorIndex) :
    (∑ v ∈ S, Internal.propN (pre.append tailC) highC v.toNat) +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit := by
  obtain ⟨T, pulledOk⟩ := h.pulledTotal
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  obtain ⟨B, hB⟩ : ∃ B, B = (324 * ((pinTerms config pulled anc fin).perIncrement *
      (T.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) +
        216 * (pinTerms config pulled anc fin).perIncrement) / 896 := ⟨_, rfl⟩
  -- the credits of `pre` are those of one epoch run, so they fit one epoch's bound
  obtain ⟨P, hP⟩ : ∃ P, P = ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards))
    (fun _ => false) v.toNat highC pre) := ⟨_, rfl⟩
  have first : P ≤ B := by
    have one := propN_segment_le h highC S pulledOk toB link pre
      (Run.nil : Run config checks ⟨fork, split⟩ ⟨fork, split⟩) tailC sameEpoch
      (fun step member => by cases member)
    rw [hB, hP]
    refine (Nat.le_div_iff_mul_le (by norm_num)).mpr (Nat.le_trans ?_ one)
    simp only [Internal.creditScan_nil, Finset.sum_const_zero, Nat.add_zero]
    exact Nat.le_refl _
  have cut := run_cuts_of_additive tailC h.early (fun _ => True)
    (fun r => ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false)
      v.toNat highC
      r)) (fun i => if i = 0 then B - P else B)
    (fun pre post _ => by simp only [Internal.creditScan_append, Finset.sum_add_distrib])
    (fun _ _ _ _ => trivial)
    (fun {m n} toM mid rest starts _ => by
      obtain ⟨mf, ms⟩ := m
      obtain rfl : fork = mf := (Internal.fork_eq_of_run toM (mid.append rest) (Nat.le_refl _)).symm
      by_cases e : getCurrentEpoch ms = getCurrentEpoch split
      · -- the segment is in the split's epoch, so it adds to the credits of `pre`
        have index : ix (⟨fork, split⟩ : ForkedBeaconState preset) ⟨fork, ms⟩ = 0 := by
          simp only [ix, e]
          omega
        simp only [index, ↓reduceIte]
        have one := propN_segment_le h highC S pulledOk toB link (pre.append toM) mid rest
          (by simpa only [sameEpoch] using e) starts
        have again : P ≤ ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ =>
          false)
            v.toNat highC (pre.append toM)) := by
          rw [hP]
          exact Finset.sum_le_sum fun v _ => by
            rw [Internal.creditScan_append]
            exact Nat.le_add_right _ _
        have bound : P + ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ =>
          false)
            v.toNat highC mid) ≤ B := by
          rw [hB]
          exact (Nat.le_div_iff_mul_le (by norm_num)).mpr
            (Nat.le_trans (Nat.mul_le_mul_right 896 (Nat.add_le_add_right again _)) one)
        omega
      · have later : getCurrentEpoch split < getCurrentEpoch ms :=
          UInt64.lt_of_le_of_ne (currentEpoch_le_of_chainSteps toM.chainSteps) (Ne.symm e)
        have index : ix (⟨fork, split⟩ : ForkedBeaconState preset) ⟨fork, ms⟩ ≠ 0 := by
          have := UInt64.lt_iff_toNat_lt.mp later
          simp only [ix]
          omega
        simp only [index, ↓reduceIte]
        rw [hB]
        have one := propN_segment_le h highC S pulledOk ((toFin.append fromFin).append toM)
          (Or.inl ⟨fromFin.append toM⟩) (Run.nil : Run config checks ⟨fork, ms⟩ ⟨fork, ms⟩) mid
          rest rfl starts
        simp only [Internal.creditScan_nil, Finset.sum_const_zero, Nat.zero_add] at one
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr one)
    (ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1) (fun step member => steps_before_end tailC step member)
  have total : ∀ t : ℕ, ((List.range (t + 1)).map
      (fun i => if i = 0 then B - P else B)).sum + P ≤ (t + 1) * B := by
    intro t
    induction t with
    | zero => simp only [List.range_one, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        ↓reduceIte, Nat.add_zero, Nat.zero_add]; omega
    | succ t ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.succ_ne_zero t, ↓reduceIte] at ih ⊢
      have : (t + 1 + 1) * B = (t + 1) * B + B := by ring
      omega
  have joined : ∑ v ∈ S, Internal.propN (pre.append tailC) highC v.toNat =
      P + ∑ v ∈ S, (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v.toNat
        highC
        tailC) := by
    rw [hP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Internal.creditScan_append _ _ _ _ pre tailC
  have depth : ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1 ≤ (pinTerms config pulled anc fin).depth := by
    have fin' := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have near := h.near
    show _ ≤ (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat
    simp only [ix]
    omega
  have credit : B + (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).proposerCredit := by
    obtain ⟨-, -, value⟩ := getTotalBalance_ok_iff_stake.mp (getTotalActiveBalance_ok pulledOk)
    rw [hB]
    simp only [pinTerms]
    refine Nat.add_le_add_right (credit_arith incPos value ?_ ?_) _
    · refine stake_le_base (g := UInt64.toNat) (fun j => balanceAt pulled j) incPos
        (fun a _ b _ same => UInt64.toNat_inj.mp same) (fun a member => ?_)
        (fun a _ => Nat.le_trans (Nat.le_add_right _ _) (le_max_left _ _)) fun j =>
          Nat.dvd_of_mod_eq_zero (FloorTrace.effective_aligned
            (toFin.append (fromFin.append toPulled)) h.genesis h.aligned j)
      obtain ⟨w, found, active⟩ := (mem_getActiveValidatorIndices
        (pulled.validators.bound h.early)).mp (List.mem_toFinset.mp member)
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
      have exit := UInt64.lt_iff_toNat_lt.mp active.2
      have fin' := UInt64.le_iff_toNat_le.mp h.finalized
      have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
      exact Internal.mem_positions_filter config pulled anc fin found (by simp [found]; omega)
    · have slots := h.twoSlots
      have two : 2 ≤ (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := by
        have := UInt64.le_iff_toNat_le.mp h.finalized
        have := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
        omega
      -- The first of the credited keys' slots is one of the terms of `attesterExcess`.
      iterate 4 refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      refine Nat.le_trans ?_ (Nat.le_add_left _ _)
      iterate 3 refine Nat.le_trans ?_ (Nat.le_add_right _ _)
      exact Nat.le_trans (by decide) (Nat.mul_le_mul two slots)
  calc _ ≤ (ix ⟨fork, split⟩ ⟨fork, counted⟩ + 1) * B +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer :=
      Nat.add_le_add_right (by
        rw [joined]
        have := total (ix ⟨fork, split⟩ ⟨fork, counted⟩)
        omega) _
    _ ≤ (pinTerms config pulled anc fin).depth * B +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ depth) _
    _ ≤ _ := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ credit

/-- The sources of the due entries of X's queue that name a target in `T`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.dueList (X : BeaconState preset fork)
  (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : List Validator :=
  (((X.pendingConsolidations electra).data.toList.filter fun c =>
      decide (c.targetIndex ∈ T)).filterMap fun c =>
    X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
      !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)

/-- `dueAt` counts `dueList`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.dueAt_eq (X : BeaconState preset
  fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : Internal.dueAt X high T = (Internal.dueList X electra high
      T).length := by
  unfold Internal.dueAt Internal.dueList
  simp only [electra, ↓reduceDIte]

/-- The caps of the due entries of two disjoint sets of targets add up. -/
private theorem dueList_sum_union (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (disjoint : Disjoint A B) (f : Validator → ℕ) :
    ((Internal.dueList X electra high (A ∪ B)).map f).sum =
      ((Internal.dueList X electra high A).map f).sum + ((Internal.dueList X electra high B).map
        f).sum := by
  -- Each entry adds the value of its source when the source passes the test, else nothing.
  have perEntry : ∀ (M : List PendingConsolidation)
      (look : PendingConsolidation → Option Validator) (ok : Validator → Bool),
      (((M.filterMap look).filter ok).map f).sum =
        (M.map fun c => (((look c).filter ok).map f).getD 0).sum := by
    intro M look ok
    induction M with
    | nil => rfl
    | cons c M ih =>
      cases found : look c with
      | none => simp [found, ih]
      | some w => by_cases keep : ok w = true <;> simp [found, keep, ih, Option.filter]
  unfold Internal.dueList
  rw [perEntry, perEntry, perEntry]
  have := Internal.sum_filter_or (X.pendingConsolidations electra).data.toList
    (fun c => decide (c.targetIndex ∈ A)) (fun c => decide (c.targetIndex ∈ B))
    (by
      rintro c ⟨ha, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      exact Finset.disjoint_left.mp disjoint ha hb)
    (fun c => ((((X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
      !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map f).getD 0))
  simpa [Finset.mem_union, Bool.decide_or] using this

/-- The due entries of two disjoint sets of targets number as many as those of their union. -/
private theorem dueList_length_union (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (disjoint : Disjoint A B) :
    (Internal.dueList X electra high (A ∪ B)).length =
      (Internal.dueList X electra high A).length + (Internal.dueList X electra high B).length := by
  have := dueList_sum_union X electra high disjoint (fun _ => 1)
  simpa using this

/-- A later horizon keeps at least the stake of an earlier one. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.dueList_sum_mono (X : BeaconState
  preset fork) (electra : .pectra ≤ fork)
    {high high' : ℕ} (later : high ≤ high') (T : Finset ValidatorIndex) (f : Validator → ℕ) :
    ((Internal.dueList X electra high T).map f).sum ≤ ((Internal.dueList X electra high' T).map
      f).sum := by
  unfold Internal.dueList
  have sub : List.Sublist
      ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter
        (fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)))
      ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter
        (fun v => !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high' + 1))) := by
    refine List.monotone_filter_right _ fun b hb => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨hb.1, by omega⟩
  exact (sub.map f).sum_le_sum fun _ _ => Nat.zero_le _

/-- A later horizon keeps at least the entries of an earlier one. -/
private theorem dueList_length_mono (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    {high high' : ℕ} (later : high ≤ high') (T : Finset ValidatorIndex) :
    (Internal.dueList X electra high T).length ≤ (Internal.dueList X electra high' T).length := by
  simpa using Internal.dueList_sum_mono X electra later T fun _ => 1

/-- More targets keep at least the entries of fewer. -/
private theorem dueList_length_subset (X : BeaconState preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) {A B : Finset ValidatorIndex} (sub : A ⊆ B) :
    (Internal.dueList X electra high A).length ≤ (Internal.dueList X electra high B).length := by
  unfold Internal.dueList
  refine (((List.monotone_filter_right _ fun c hc => ?_).filterMap _).filter _).length_le
  simp only [decide_eq_true_eq] at hc ⊢
  exact sub hc

/-- The due entries of any targets have at most the stake of all entries read at that horizon. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.dueList_sum_le_all (X : BeaconState
  preset fork) (electra : .pectra ≤ fork)
    (high : ℕ) (T : Finset ValidatorIndex) (f : Validator → ℕ) :
    ((Internal.dueList X electra high T).map f).sum ≤
      ((((((X.pendingConsolidations electra).data.toList.filterMap fun c =>
        X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).map f)).sum) := by
  unfold Internal.dueList
  refine (List.Sublist.map f ?_).sum_le_sum fun _ _ => Nat.zero_le _
  exact (List.filter_sublist.filterMap _).filter _

/-- A whistleblower's share of an amount is at most the amount.

The quotient is at least thirty, so a share of `33/300` of the amount, rounded up, fits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.wShare_le (facts : PinPresetFacts
  preset) (x : ℕ) : Internal.wShare preset fork x ≤ x := by
  have quotient := facts.whistleblower fork
  unfold Internal.wShare
  generalize (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = W at *
  have pos : 0 < 10 * W := by omega
  refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul pos).mpr ?_)
  have big : 33 * x ≤ 10 * W * x := Nat.mul_le_mul_right _ (by omega)
  have two : (x + 1) * (10 * W) = 10 * W * x + 10 * W := by ring
  show 33 * x + 10 * W - 1 < (x + 1) * (10 * W)
  omega

/-- The due entries of a set of targets are those of its keys.

Each entry names one target. -/
private theorem dueAt_sum (X : BeaconState preset fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) : ∑ v ∈ T, Internal.dueAt X high {v} = Internal.dueAt X high T := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Internal.dueAt_eq X electra high]
    simp [Internal.dueList]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Internal.dueAt_eq X electra high, Internal.dueAt_eq X electra
      high,
      Internal.dueAt_eq X electra high, show insert a s = {a} ∪ s from rfl,
      dueList_length_union X electra high (Finset.disjoint_singleton_left.mpr ha)]

/-- The band of a key is its upward band for each due entry that names it, and these add over keys.

The due entries of a set of targets are the due entries of its keys. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bandX_sum (X : BeaconState preset
  fork) (electra : .pectra ≤ fork) (high : ℕ)
    (T : Finset ValidatorIndex) :
    ∑ v ∈ T, Internal.bandX X high v.toNat = preset.upwardBand * Internal.dueAt X high T := by
  classical
  have single (v : ValidatorIndex) :
      Internal.bandX X high v.toNat = preset.upwardBand * Internal.dueAt X high {v} := by
    simp [Internal.bandX]
  simp only [single]
  rw [← Finset.mul_sum, dueAt_sum X electra high T]

/-- The classes `K4`, `K5` and `K6` share no key with each other or with `V`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.classes_disjoint (h : Setting
  config checks g split fin pulled anc counted V) :
    Disjoint (Internal.K4 pulled counted V) (Internal.K5 counted V) ∧
    Disjoint (Internal.K4 pulled counted V) (Internal.K6 pulled counted) ∧
    Disjoint (Internal.K5 counted V) (Internal.K6 pulled counted) ∧
    Disjoint V (Internal.K4 pulled counted V) ∧ Disjoint V (Internal.K5 counted V) ∧
    Disjoint V (Internal.K6 pulled counted) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine Finset.disjoint_left.mpr fun v a b => ?_
  · simp only [Internal.K4, Internal.K5, Finset.mem_filter] at a b
    exact b.2.1 a.1
  · simp only [Internal.K4, Internal.K6, Finset.mem_filter] at a b
    exact b.2.2 a.2.1
  · simp only [Internal.K5, Internal.K6, Finset.mem_filter] at a b
    exact a.2.1 b.1
  · simp only [Internal.K4, Finset.mem_filter] at b
    exact b.2.2.2 a
  · simp only [Internal.K5, Finset.mem_filter] at b
    exact b.2.2 a
  · simp only [Internal.K6, Finset.mem_filter] at b
    exact b.2.2 (h.voting v a).1

/-- A key of `K4`, `K5` or `K6` is in C's quorum. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.classes_mem_Q {v : ValidatorIndex}
    (member : v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted)
      : v ∈ Internal.Q counted := by
  simp only [Finset.mem_union] at member
  rcases member with (h4 | h5) | h6
  · simp only [Internal.K4, Finset.mem_filter] at h4
    exact h4.2.2.1
  · simp only [Internal.K5, Finset.mem_filter] at h5
    exact h5.1
  · simp only [Internal.K6, Finset.mem_filter] at h6
    exact h6.2.1

/-- A key of `K4`, `K5` or `K6` is in C's quorum, so it is unslashed at C. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.classes_unslashed {v :
  ValidatorIndex}
    (member : v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted)
      :
    slashedFlagAt counted v.toNat ≠ some true := by
  have inQ := Internal.classes_mem_Q member
  intro slashed
  simp only [Internal.Q, quorumVoters, Finset.mem_filter] at inQ
  have unslashed := inQ.2
  unfold slashedFlagAt at slashed
  rw [slashed] at unslashed
  simp at unslashed

/-- The keys slashed at C and not at the split are in no class of C's quorum, and not in `V`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sc_disjoint (h : Setting config
  checks g split fin pulled anc counted V) :
    Disjoint (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted)
      (Internal.SC pulled counted split) ∧
    Disjoint V (Internal.SC pulled counted split) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hk hs
    simp only [Internal.SC, Finset.mem_filter] at hs
    exact Internal.classes_unslashed hk hs.2.1
  · rw [Finset.disjoint_left]
    intro v hv hs
    simp only [Internal.SC, Finset.mem_filter] at hs
    have unslashed := (h.voting v hv).2
    rw [hs.2.1] at unslashed
    simp at unslashed

/-- The keys created after the split's registry and slashed at C are in no other class.

They are slashed at C, so they are not in C's quorum or in `V`.

They are absent at the split, so they are not in `SC`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cs_disjoint (h : Setting config
  checks g split fin pulled anc counted V) :
    Disjoint (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted ∪
      Internal.SC pulled counted split)
      (Internal.CS counted split) ∧ Disjoint V (Internal.CS counted split) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro v hk hc
    simp only [Internal.CS, Finset.mem_filter] at hc
    rcases Finset.mem_union.mp hk with quorum | created
    · exact Internal.classes_unslashed quorum hc.2.2
    · simp only [Internal.SC, Finset.mem_filter] at created
      have absent : slashedFlagAt split v.toNat = none := by
        simp only [slashedFlagAt, Option.map_eq_none_iff]
        exact Array.getElem?_eq_none hc.2.1
      rw [absent] at created
      cases created.2.2
  · rw [Finset.disjoint_left]
    intro v hv hc
    simp only [Internal.CS, Finset.mem_filter] at hc
    have unslashed := (h.voting v hv).2
    rw [hc.2.2] at unslashed
    simp at unslashed

/-- A key that a run credits.

A block step credits it, or a pending-deposit pass does. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditedKey {x y : ForkedBeaconState
  preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) : Bool :=
  decide (0 < Internal.grossScan v.toNat high tail +
    (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high tail))

/-- `creditUnits` is `unitGain` for the credited-key slots and for two more of each exiting key.

The same holds for each queue key.

The slots are at least the proposers, the seats and the deposit recipients of the window.

They also hold the seat units of R's branch and the shared segment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditUnits_eq (config : Config)
  (pulled anc fin : BeaconState preset fork) :
    ∃ N : ℕ, (pinTerms config pulled anc fin).creditUnits =
        (N + 2 * (((pinTerms config pulled anc fin).positions.filter fun i =>
          (pinTerms config pulled anc fin).exitingB i = true).card +
            (pinTerms config pulled anc fin).queueKeys)) *
          (pinTerms config pulled anc fin).unitGain ∧
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
            ((pinTerms config pulled anc fin).depthFin /
              max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2)) *
          preset.SYNC_COMMITTEE_SIZE.toNat ≤ N := by
  dsimp only [pinTerms]
  simp only [decide_eq_true_eq]
  exact ⟨_, rfl, by omega⟩

/-- The keys that a sync aggregate debits on the shared segment or R's branch fit the seat units.

The seat units are the seats of the committees of the periods that the two runs touch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.debit_keys_le (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high : ℕ)
    {events eventsF : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF) (A B : Finset ValidatorIndex)
    (debitsF : ∀ v ∈ A, 0 < Internal.syncD eventsF v.toNat) (debitsR : ∀ v ∈ B, 0 < Internal.syncD
      events v.toNat) :
    (A ∪ B).card ≤ ((pinTerms config pulled anc fin).depth /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((pinTerms config pulled anc fin).depthFin /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2)) *
      preset.SYNC_COMMITTEE_SIZE.toNat := by
  classical
  obtain ⟨eventsC, replayedC⟩ := tailC.balanceEvents_ok h.early high
  have inj : Function.Injective fun v : ValidatorIndex => v.toNat := fun a b same =>
    UInt64.toNat_inj.mp same
  have union := Internal.seat_union_card h fromFin tail tailC high high replayed replayedF replayedC
    (Nat.le_trans (by decide) h.fulu) (A.image fun v => v.toNat) (B.image fun v => v.toNat)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      have := debitsF v hv
      simp only [Internal.syncD, List.map_append, List.sum_append] at this ⊢
      omega)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact debitsR v hv)
  rw [← Finset.image_union, Finset.card_image_of_injective _ inj] at union
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have periods := Nat.add_div_le_div_add_div_add_one
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) (getCurrentEpoch fin).toNat
    (max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
  have shift : ((getCurrentEpoch pulled).toNat + 1) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat ≤ ((getCurrentEpoch pulled).toNat + 2) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := Nat.div_le_div_right (by omega)
  rw [Nat.sub_add_cancel (by omega)] at periods
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have depthFinEq : (pinTerms config pulled anc fin).depthFin =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := rfl
  refine union.trans ?_
  have nonneg := Nat.zero_le (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) /
    max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
  rw [depthEq, depthFinEq, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The credited keys of a set fit the credited-key slots of the window.

The slots are the proposers, the seats and the deposit recipients of the window.

They are the keys of C's run, which `credited_keys_le` counts by the slots of its epochs. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credited_slots_le (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (T : Finset ValidatorIndex) (inside : ∀ v ∈ T, v.toNat < counted.validators.data.size) :
    (T.filter fun v => Internal.creditedKey tailC highC v = true).card ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  have fit : (T.filter fun v => Internal.creditedKey tailC highC v = true).card ≤
      ((Finset.range counted.validators.data.size).filter fun i =>
        0 < Internal.grossScan i highC tailC +
          (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC
            tailC)).card := by
    refine Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat) (fun v hv => ?_)
      (fun a _ b _ same => UInt64.toNat_inj.mp same)
    obtain ⟨member, flag⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (inside v member), of_decide_eq_true flag⟩
  have credited := Internal.credited_keys_le h tailC highC
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  -- The slots of the run's epochs are at most those of the window.
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have monotone := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
  simp only at monotone
  have wide : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat + 1 ≤
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := by omega
  have periods := Nat.add_div_le_div_add_div_add_one
    ((getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat)
    (getCurrentEpoch split).toNat (max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
  rw [Nat.sub_add_cancel monotone] at periods
  have periodsLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    (show (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat by omega)
  have monotoneLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) monotone
  have first := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) wide
  have second := Nat.mul_le_mul_left preset.SYNC_COMMITTEE_SIZE.toNat
    (show (getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 ≤
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2 by omega)
  have bound : ((getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat + 1) *
      (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) ≤
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) *
          preset.SLOTS_PER_EPOCH.toNat +
        (((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat :=
    (Nat.add_le_add first second).trans_eq (by ring)
  rw [depthEq]
  omega

/-- The credited keys of `K4`, `K5`, `K6`, `SC` and `CS` fit the credited-key slots of the window.

The slots are the proposers, the seats and the deposit recipients of the window.

A credited key of `CS` is a credited key of C's run, in C's registry, as the others are. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credited_classes_le (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    ((Internal.K4 pulled counted V).filter fun v => Internal.creditedKey tailC highC v = true).card
      +
      ((Internal.K5 counted V).filter fun v => Internal.creditedKey tailC highC v = true).card +
      ((Internal.K6 pulled counted).filter fun v => Internal.creditedKey tailC highC v = true).card
        +
      ((Internal.SC pulled counted split).filter fun v => Internal.creditedKey tailC highC v =
        true).card +
      ((Internal.CS counted split).filter fun v => Internal.creditedKey tailC highC v = true).card ≤
    (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
      ((pinTerms config pulled anc fin).depth /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
          preset.SYNC_COMMITTEE_SIZE.toNat +
      (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  obtain ⟨dCS, -⟩ := Internal.cs_disjoint h
  set C4 := (Internal.K4 pulled counted V).filter fun v => Internal.creditedKey tailC highC v = true
  set C5 := (Internal.K5 counted V).filter fun v => Internal.creditedKey tailC highC v = true
  set C6 := (Internal.K6 pulled counted).filter fun v => Internal.creditedKey tailC highC v = true
  set Csc := (Internal.SC pulled counted split).filter fun v => Internal.creditedKey tailC highC v =
    true
  set Ccs := (Internal.CS counted split).filter fun v => Internal.creditedKey tailC highC v = true
  -- The five classes are apart, and each key of them is in C's registry.
  have apart : Disjoint (C4 ∪ C6) C5 :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_filter_filter d45,
      (Finset.disjoint_filter_filter d56).symm⟩
  have apartSC : Disjoint (C4 ∪ C6 ∪ C5) Csc :=
    Finset.disjoint_of_subset_left (u := Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
      Internal.K6 pulled counted)
      (fun v hv => by
        simp only [C4, C5, C6, Finset.mem_union, Finset.mem_filter] at hv
        simp only [Finset.mem_union]
        tauto)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSC)
  have apartCS : Disjoint (C4 ∪ C6 ∪ C5 ∪ Csc) Ccs :=
    Finset.disjoint_of_subset_left (u := Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
      Internal.K6 pulled counted ∪
      Internal.SC pulled counted split)
      (fun v hv => by
        simp only [C4, C5, C6, Csc, Finset.mem_union, Finset.mem_filter] at hv
        simp only [Finset.mem_union]
        tauto)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dCS)
  have card5 : (C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs).card =
      C4.card + C6.card + C5.card + Csc.card + Ccs.card := by
    rw [Finset.card_union_of_disjoint apartCS, Finset.card_union_of_disjoint apartSC,
      Finset.card_union_of_disjoint apart,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter d46)]
  have inCounted : ∀ v ∈ Internal.K4 pulled counted V ∪ Internal.K6 pulled counted ∪ Internal.K5
    counted V,
      v.toNat < counted.validators.data.size := by
    intro v hv
    simp only [Finset.mem_union] at hv
    rcases hv with (h4 | h6) | h5
    · obtain ⟨w, found, -⟩ := Internal.active_of_activeVoters h.early (Finset.mem_filter.mp h4).1
      exact (Array.getElem?_eq_some_iff.mp found).1
    · obtain ⟨w, found, -⟩ := Internal.active_of_activeVoters h.early (Finset.mem_filter.mp h6).1
      exact (Array.getElem?_eq_some_iff.mp found).1
    · have listed := (Finset.mem_filter.mp h5).1
      simp only [Internal.Q, quorumVoters, Finset.mem_filter, List.mem_toFinset,
        List.mem_append] at listed
      rcases listed.1 with now | before
      · exact lt_size_of_mem_getActiveValidatorIndices now
      · exact lt_size_of_mem_getActiveValidatorIndices before
  have flagIn : ∀ v : ValidatorIndex, slashedFlagAt counted v.toNat = some true →
      v.toNat < counted.validators.data.size := by
    intro v flag
    simp only [slashedFlagAt, Option.map_eq_some_iff] at flag
    obtain ⟨w, found, -⟩ := flag
    exact (Array.getElem?_eq_some_iff.mp found).1
  have inSC : ∀ v ∈ Internal.SC pulled counted split, v.toNat < counted.validators.data.size :=
    fun v hv => flagIn v (Finset.mem_filter.mp hv).2.1
  have inCS : ∀ v ∈ Internal.CS counted split, v.toNat < counted.validators.data.size :=
    fun v hv => flagIn v (Finset.mem_filter.mp hv).2.2
  have flags : ∀ v ∈ C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs, Internal.creditedKey tailC highC v = true := by
    intro v member
    simp only [C4, C5, C6, Csc, Ccs, Finset.mem_union, Finset.mem_filter] at member
    tauto
  have inside : ∀ v ∈ C4 ∪ C6 ∪ C5 ∪ Csc ∪ Ccs, v.toNat < counted.validators.data.size := by
    intro v member
    have classed : v ∈ Internal.K4 pulled counted V ∪ Internal.K6 pulled counted ∪ Internal.K5
      counted V ∨
        v ∈ Internal.SC pulled counted split ∨ v ∈ Internal.CS counted split := by
      simp only [C4, C5, C6, Csc, Ccs, Finset.mem_union, Finset.mem_filter] at member ⊢
      tauto
    rcases classed with held | held | held
    · exact inCounted v held
    · exact inSC v held
    · exact inCS v held
  have slots := Internal.credited_slots_le h tailC highC _ inside
  rw [Finset.filter_true_of_mem flags, card5] at slots
  omega

/-- The rounding slacks of a set of keys are the upward band for each credited key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.band_sum {x y : ForkedBeaconState
  preset} (tail : Run config checks x y)
    (high : ℕ) (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.bandC tail high v.toNat =
      preset.upwardBand * (S.filter fun v => Internal.creditedKey tail high v = true).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Internal.bandC Internal.creditedKey
  by_cases credited : 0 < Internal.grossScan v.toNat high tail +
    (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat high tail) <;>
    simp [credited]

/-- The credits that a scan reads for a key are at most the credits of its source's events.

The sources of the scan, block and slot, are those that `p` selects. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.scan_le_events (blockP slotP :
  BalanceSource → Bool) (p : BalanceSource → Prop)
    [DecidablePred p] (selects : ∀ s, (blockP s = true ∨ slotP s = true) ↔ p s)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) (high : ℕ)
    (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    (Internal.creditScan blockP slotP v.toNat high tail) ≤
      ((events.filter fun e => p e.source).map (Internal.keyCredit v.toNat)).sum := by
  have scan := Internal.creditScan_sum_le {v} UInt64.toNat blockP slotP high (Internal.keyCredit
    v.toNat) tail
    replayed fun e _ _ => by simp
  simp only [Finset.sum_singleton] at scan
  refine scan.trans (le_of_eq ?_)
  simp only [selects]
  rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source) (Internal.keyCredit v.toNat)
    (fun _ => 0)]
  simp

/-- The credits of a key on C's branch are its proposer credits and deposits, up to consolidations.

The consolidations are those of the replayed events. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.credit_parts_le {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    Internal.credC tail high v.toNat ≤ Internal.credN tail high v.toNat + Internal.consAmt events
      v.toNat ∧
    Internal.propC tail high v.toNat ≤ Internal.propN tail high v.toNat + Internal.consAmt events
      v.toNat := by
  have cons := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp) tail high v
    replayed
  have c := Internal.credC_split tail high v.toNat
  have p := Internal.propC_split tail high v.toNat
  exact ⟨by unfold Internal.consAmt; omega, by unfold Internal.consAmt; omega⟩

/-- K5 (`exitingCredits` with `credits`): C's proposer credits to K5 keys, weight 3.

`bud_consolidations` charges the consolidation amounts, so they are added to the bound.

The `syncProposer` part of the bound is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `exitingCredits`.

The compounding of the credits, an exact tenth of the keys' total, is in the bound.

The two further bands of each credited K5 key are in `bud_exitingBands`.

The run `pre` starts at the split's epoch, so its credits are proposer credits only.

Consolidations and deposits credit at epoch processing, so none falls inside `pre`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_exitingCredits (h : Setting
  config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * (2 * ((∑ v ∈ (Internal.K5 counted V), Internal.propN pre highC v.toNat) +
        ∑ v ∈ (Internal.K5 counted V), Internal.propC tailC highC v.toNat)) +
      2 * ((∑ v ∈ (Internal.K5 counted V), Internal.propN pre highC v.toNat) +
        ∑ v ∈ (Internal.K5 counted V), Internal.propN tailC highC v.toNat) +
        22 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).exitingCredits +
        20 * (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat) := by
  -- The proposer credits fit the pin's per-epoch bound, and their consolidation part is `consAmt`.
  have rewards := Internal.proposer_rewards_le h toB link pre sameEpoch tailC highC (Internal.K5
    counted V)
  simp only [Internal.propN_append, Finset.sum_add_distrib] at rewards
  have parts : ∑ v ∈ (Internal.K5 counted V), Internal.propC tailC highC v.toNat ≤
      ∑ v ∈ (Internal.K5 counted V), Internal.propN tailC highC v.toNat +
        ∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => (Internal.credit_parts_le tailC highC v replayedC).2
  have exiting : (pinTerms config pulled anc fin).exitingCredits =
      (22 * ((pinTerms config pulled anc fin).depth *
        (pinTerms config pulled anc fin).proposerCredit) + 9) / 10 := rfl
  rw [exiting]
  omega

/-- `credits` holds the proposer credit, the deposit queue and the credited-key slots.

`queueDep` is the same queue, three times. -/
private theorem credits_budget (config : Config) (pulled anc fin : BeaconState preset fork) :
    ∃ carry churn wb ck : ℕ, (pinTerms config pulled anc fin).queueDep = 3 * (churn + carry) ∧
      (pinTerms config pulled anc fin).credits =
        (11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).proposerCredit + carry + churn + wb) + 9) / 10 +
          ck * preset.upwardBand ∧
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤
        ck := by
  dsimp only [pinTerms]
  exact ⟨_, _, _, _, rfl, rfl, Nat.le_add_right _ _⟩

/-- The deposits of the classes fit the deposit queue at weight three.

The keys slashed at C, `SC` and `CS`, count the deposits of events that do not hold them slashed.

The classes of C's quorum are apart from them. -/
private theorem deposits_union_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * ((∑ v ∈ Internal.K4 pulled counted V ∪ Internal.K6 pulled counted,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
          tailC)) +
      (∑ v ∈ Internal.SC pulled counted split ∪ Internal.CS counted split, Internal.depPre eventsC
        v.toNat)) ≤
      (pinTerms config pulled anc fin).queueDep := by
  have quorum : Internal.K4 pulled counted V ∪ Internal.K6 pulled counted ⊆
      Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted := fun v
        member => by
    simp only [Finset.mem_union] at member ⊢
    tauto
  refine deposits_active_le h tailC highC endEpochC replayedC _ _ ?_ (fun v member => ?_)
    fun v member => ?_
  · rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_of_subset_left quorum (Internal.sc_disjoint h).1,
      Finset.disjoint_of_subset_left (fun v m => Finset.mem_union_left _ (quorum m))
        (Internal.cs_disjoint h).1⟩
  · have countedActive : v ∈ Internal.AC counted := by
      rcases Finset.mem_union.mp member with m | m
      · exact (Finset.mem_filter.mp m).1
      · exact (Finset.mem_filter.mp m).1
    obtain ⟨w, found, active⟩ := Internal.active_of_activeVoters h.early countedActive
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
    exact ⟨w, found, active.2⟩
  · have flag : slashedFlagAt counted v.toNat = some true := by
      rcases Finset.mem_union.mp member with m | m
      · exact (Finset.mem_filter.mp m).2.1
      · exact (Finset.mem_filter.mp m).2.2
    simpa [slashedFlagAt, Option.map_eq_some_iff] using flag

/-- The credits bound, from the proposer rewards, the deposits and the credited keys of its classes.

The consolidation amounts are charged by `bud_consolidations`, and the sync part by `bud_sync`.

The deposits of a key slashed at C count only those before its slashing, in its share.

`rewards` is the proposer credits of the five classes and the sync part against `proposerCredit`.

`deposits` is the deposits of the classes against the deposit queue, at weight three.

`cards` is the credited keys of the classes against the credited-key slots. -/
private theorem bud_credits_of (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (rewards : (∑ v ∈ Internal.K4 pulled counted V, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ Internal.K5 counted V, Internal.propN pre highC v.toNat) +
      (∑ v ∈ Internal.K5 counted V, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre highC v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC highC v.toNat) +
      (∑ v ∈ Internal.CS counted split, Internal.propN tailC highC v.toNat) +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit)
    (deposits : 3 * ((∑ v ∈ Internal.K4 pulled counted V ∪ Internal.K6 pulled counted,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC
          tailC)) +
      (∑ v ∈ Internal.SC pulled counted split ∪ Internal.CS counted split, Internal.depPre eventsC
        v.toNat)) ≤
      (pinTerms config pulled anc fin).queueDep)
    (cards : ((Internal.K4 pulled counted V).filter fun v => Internal.creditedKey tailC highC v =
      true).card +
      ((Internal.K5 counted V).filter fun v => Internal.creditedKey tailC highC v = true).card +
      ((Internal.K6 pulled counted).filter fun v => Internal.creditedKey tailC highC v = true).card
        +
      ((Internal.SC pulled counted split).filter fun v => Internal.creditedKey tailC highC v =
        true).card +
      ((Internal.CS counted split).filter fun v => Internal.creditedKey tailC highC v = true).card ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) :
    10 * ((∑ v ∈ (Internal.K4 pulled counted V), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V), Internal.propN pre highC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V), Internal.propC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K4 pulled counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC
        highC v.toNat) +
        ∑ v ∈ Internal.SC pulled counted split, Internal.depPre eventsC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre highC
        v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ Internal.CS counted split, Internal.propN tailC highC
        v.toNat) +
        ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC v.toNat) +
      (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat)) +
      ((∑ v ∈ (Internal.K4 pulled counted V), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (Internal.K6 pulled counted), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (Internal.K5 counted V), Internal.propN pre highC v.toNat) +
        (∑ v ∈ (Internal.K5 counted V), Internal.propN tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat)) := by
  classical
  obtain ⟨carry, churn, wb, ck, queue, credits, slots⟩ := credits_budget config pulled anc fin
  obtain ⟨-, d46, -, -, -, -⟩ := Internal.classes_disjoint h
  have dSCCS : Disjoint (Internal.SC pulled counted split) (Internal.CS counted split) :=
    Finset.disjoint_of_subset_left Finset.subset_union_right (Internal.cs_disjoint h).1
  have parts (S : Finset ValidatorIndex) := fun v (_ : v ∈ S) => Internal.credit_parts_le tailC
    highC v
    replayedC
  have sumLe (S : Finset ValidatorIndex) (f g : ValidatorIndex → ℕ)
      (le : ∀ v ∈ S, f v ≤ g v) : ∑ v ∈ S, f v ≤ ∑ v ∈ S, g v := Finset.sum_le_sum le
  have c4 := sumLe (Internal.K4 pulled counted V) _ (fun v => Internal.credN tailC highC v.toNat +
    Internal.consAmt eventsC v.toNat) fun v m => (parts _ v m).1
  have c6 := sumLe (Internal.K6 pulled counted) _ (fun v => Internal.credN tailC highC v.toNat +
    Internal.consAmt eventsC v.toNat) fun v m => (parts _ v m).1
  have c5 := sumLe (Internal.K5 counted V) _ (fun v => Internal.propN tailC highC v.toNat +
    Internal.consAmt eventsC v.toNat) fun v m => (parts _ v m).2
  simp only [Finset.sum_add_distrib] at c4 c6 c5
  have e4 : ∑ v ∈ Internal.K4 pulled counted V, Internal.credN tailC highC v.toNat =
      (∑ v ∈ Internal.K4 pulled counted V, Internal.propN tailC highC v.toNat) + ∑ v ∈ Internal.K4
        pulled counted V,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
          := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Internal.credN_split tailC highC v.toNat
  have e6 : ∑ v ∈ Internal.K6 pulled counted, Internal.credN tailC highC v.toNat =
      (∑ v ∈ Internal.K6 pulled counted, Internal.propN tailC highC v.toNat) + ∑ v ∈ Internal.K6
        pulled counted,
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
          := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => Internal.credN_split tailC highC v.toNat
  rw [Finset.sum_union d46, Finset.sum_union dSCCS] at deposits
  have w1 := Internal.wShare_le (fork := fork) h.facts ((∑ v ∈ Internal.SC pulled counted split,
    Internal.propN tailC highC v.toNat) + ∑ v ∈ Internal.SC pulled counted split, Internal.depPre
      eventsC v.toNat)
  have w3 := Internal.wShare_le (fork := fork) h.facts (∑ v ∈ Internal.SC pulled counted split,
    Internal.propN pre highC v.toNat)
  have w2 := Internal.wShare_le (fork := fork) h.facts ((∑ v ∈ Internal.CS counted split,
    Internal.propN tailC highC v.toNat) + ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC
      v.toNat)
  have bands : (∑ v ∈ Internal.K4 pulled counted V, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ Internal.K5 counted V, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat) ≤ ck * preset.upwardBand
        := by
    simp only [Internal.band_sum, ← Nat.mul_add]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (cards.trans slots)
  omega

/-- C's non-attestation credits to keys counted once.

The consolidation amounts are not here either: `bud_consolidations` charges them.

The `syncProposer` part of `credits` is not here: `bud_sync` uses it.

The bound is scaled by ten, to take the eleven tenths and the rounding of `credits`.

The compounding of the credits, an exact tenth of the keys' total, is in the bound.

The rounding slacks of the credited keys of `K4` and `K5` are paid by `creditedKeys`.

`K5` also reads the proposer credits of `pre`, the run to the split from the start of its epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_credits (h : Setting config
  checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (link : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, b⟩) ∨
      ∃ _ : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, getCurrentEpoch fin = getCurrentEpoch b)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    10 * ((∑ v ∈ (Internal.K4 pulled counted V), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.credC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V), Internal.propN pre highC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V), Internal.propC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K4 pulled counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K5 counted V), Internal.bandC tailC highC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC
        highC v.toNat) +
        ∑ v ∈ Internal.SC pulled counted split, Internal.depPre eventsC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre highC
        v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
      Internal.wShare preset fork ((∑ v ∈ Internal.CS counted split, Internal.propN tailC highC
        v.toNat) +
        ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC v.toNat) +
      (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat)) +
      ((∑ v ∈ (Internal.K4 pulled counted V), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (Internal.K6 pulled counted), Internal.credN tailC highC v.toNat) +
        (∑ v ∈ (Internal.K5 counted V), Internal.propN pre highC v.toNat) +
        (∑ v ∈ (Internal.K5 counted V), Internal.propN tailC highC v.toNat)) +
        11 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) ≤
      10 * (pinTerms config pulled anc fin).credits +
        10 * ((∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
          (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat)) :=
  bud_credits_of h pre tailC highC replayedC
    (by
      obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
      have := Internal.proposer_rewards_le h toB link pre sameEpoch tailC highC
        (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
        Internal.K6 pulled counted ∪ Internal.SC pulled counted split ∪ Internal.CS counted split)
      simp only [Internal.propN_append, Finset.sum_add_distrib] at this
      simp only [Finset.sum_union (Internal.cs_disjoint h).1, Finset.sum_union (Internal.sc_disjoint
        h).1,
        Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d46, d56⟩),
        Finset.sum_union d45] at this
      omega)
    (deposits_union_le h tailC highC endEpochC replayedC) (Internal.credited_classes_le h tailC
      highC)

/-- The keys of `K5` are at most the keys that R reads as exiting and the queue keys.

A key of `K5` is read as exiting at R, or has a departure charge on C's run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.card_K5_le (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) :
    (Internal.K5 counted V).card ≤ ((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
      (pinTerms config pulled anc fin).queueKeys := by
  classical
  set A := (Internal.K5 counted V).filter fun v =>
    (pinTerms config pulled anc fin).exitingB v.toNat = true
  set B := (Internal.K5 counted V).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat
  have cover : Internal.K5 counted V ⊆ A ∪ B := by
    intro v inK5
    by_cases exiting : (pinTerms config pulled anc fin).exitingB v.toNat = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inK5, exiting⟩)
    · have flag : (pinTerms config pulled anc fin).exitingB v.toNat = false := by
        simpa using exiting
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨inK5, K5_charged h tailC inK5 flag⟩)
  have exitingLe := card_exitingB_le config pulled anc fin A fun v hv =>
    (Finset.mem_filter.mp hv).2
  have chargedLe := charged_count h tailC
  exact (Finset.card_le_card cover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add exitingLe chargedLe))

/-- The events of the sources of consolidations and deposits are at most those of each source. -/
private theorem sum_filter_cons_dep_le (events : List (BalanceEvent preset))
    (f : BalanceEvent preset → ℕ) :
    ((events.filter fun e => decide (e.source = .consolidations ∨ e.source = .deposits)).map
        f).sum ≤
      ((events.filter fun e => decide (e.source = .deposits)).map f).sum +
        ((events.filter fun e => decide (e.source = .consolidations)).map f).sum := by
  have same : (fun e : BalanceEvent preset =>
      decide (e.source = .consolidations ∨ e.source = .deposits)) =
        fun e => decide (e.source = .deposits) || decide (e.source = .consolidations) := by
    funext e
    cases e.source <;> decide
  rw [same]
  have apart : ∀ s : BalanceSource, ¬ (decide (s = .deposits) = true ∧
      decide (s = .consolidations) = true) := fun s h => by
    simp at h
    exact absurd (h.1.symm.trans h.2) (by decide)
  exact (Internal.sum_filter_or events (fun e => decide (e.source = .deposits))
    (fun e => decide (e.source = .consolidations)) (fun e => apart e.source) f).le

/-- A slot step raises the balance of a key that is idle in the previous epoch by its credits.

The credits are those of deposits and consolidations.

The epoch rewards of such a key are 0, and the slot has no sync events. -/
private theorem slot_idle_step {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (ok : advanceSlotAcross config checks m = .ok n) (early : n.fork < .glamsterdam)
    (electra : .pectra ≤ m.fork) (v : ℕ)
    (known : v < m.state.validators.data.size ∨ BalancesMatch m.state)
    (idle : v.toUInt64 ∉ getActiveValidatorIndices m.state (getPreviousEpoch m.state)) :
    actualBalanceAt n v ≤ actualBalanceAt m v +
      Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) v
        (Step.slot ok : Step config checks m n) +
      Internal.stepCredit (fun _ => false) (fun s => decide (s = .consolidations)) v
        (Step.slot ok : Step config checks m n) := by
  have altair : .altair ≤ m.fork := Nat.le_trans (by decide) electra
  obtain ⟨events, replayed⟩ := (Step.slot ok : Step config checks m n).balanceEvents_ok early
  have base := Internal.step_balance_le (Step.slot ok : Step config checks m n) early v
  have rewards := Internal.epochRewards_le (Step.slot ok : Step config checks m n) altair early v
    known 0 0 (.inl idle) (.inl idle)
  have rewardsZero : Internal.epochRewards v (Step.slot ok : Step config checks m n) = 0 := by
    simpa using rewards
  have sources := Internal.step_credit_le_sources shared genesis (Step.slot ok : Step config checks
    m n)
    early electra v replayed
  have noSync := Internal.slot_noSync electra ok early replayed
  have syncZero : (events.map (Internal.syncCredit v)).sum = 0 :=
    List.sum_eq_zero fun x member => by
      obtain ⟨e, mem, rfl⟩ := List.mem_map.mp member
      simp [Internal.syncCredit, noSync e mem]
  have split := sum_filter_cons_dep_le events (Internal.keyCredit v)
  simp only [Internal.stepCredit, Internal.stepNet, replayed, Except.toOption, Option.getD_some,
    syncZero] at base sources ⊢
  simp only [List.filter_false, List.map_nil, List.sum_nil] at sources
  omega

/-- A block step gives no gross credit to a key that is not active and holds no seat.

A key that is not active at the epoch of the step is not its proposer.

A key whose activation is too late for a committee to sample it holds no seat. -/
private theorem block_idle_step {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (covers : preset.MIN_SEED_LOOKAHEAD.toNat + 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) (v : ℕ)
    (notActive : ∀ w, s.validators.data[v]? = some w →
      isActiveValidator w (getCurrentEpoch s) = false)
    (notSeated : ∀ w, t.validators.data[v]? = some w → w.activationEpoch = FAR_FUTURE_EPOCH ∨
      (getCurrentEpoch t).toNat + 1 < w.activationEpoch.toNat) :
    Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
      false) v
      (Step.block engine signed due ok) = 0 := by
  obtain ⟨K, -, proposer, keys⟩ := Internal.block_step_gross_keys genesis apart shared fulu early
    (engine := engine) (signed := signed) (due := due) (ok := ok)
  by_contra nonzero
  rcases keys v (Nat.pos_of_ne_zero nonzero) with member | ⟨altair, w, found, seat⟩
  · obtain ⟨p, read, same⟩ := proposer v member
    have active := (Run.lookaheadActive covers genesis shared early).proposer_active fulu read
    rw [same] at active
    obtain ⟨w, found, isActive⟩ := isActiveAt_eq_true_iff.mp active
    rw [notActive w found] at isActive
    exact Bool.false_ne_true isActive
  · have run := shared.snoc (Step.block engine signed due ok)
    obtain ⟨j, w', found', keyed, assigned, late⟩ :=
      (run.syncCommittee_activation_bounded genesis altair).1 w.pubkey seat
    obtain rfl := (run.pubkeysDistinct genesis).index_eq found found' keyed.symm
    obtain rfl := Option.some.inj (found.symm.trans found')
    rcases notSeated w found with far | later
    · exact assigned far
    · have bound : w.activationEpoch.toNat ≤ (getCurrentEpoch t).toNat + 1 := late
      omega

/-- A key that is idle along a prefix of C's run has a balance at most its credits there.

The key is two epochs from its activation at the end of the run.

It is absent at the start.

No block step gives it a gross credit, since it is neither a proposer nor on a seat.

A slot step credits it the credits of deposits and consolidations, since it is idle. -/
private theorem key_idle_walk (h : Setting config checks g split fin pulled anc counted V)
    {z : ForkedBeaconState preset} (v : ℕ) (small : v < 2 ^ 64) (highC : ℕ)
    (zEarly : z.fork < .glamsterdam)
    (zHigh : (getCurrentEpoch z.state).toNat ≤ highC + 1)
    (ahead : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v]? = some w → w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch m.state).toNat + 1 < w.activationEpoch.toNat)
    (start : actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v = 0) :
    ∀ {m : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ m),
      Run config checks m z → Internal.grossScan v highC pre = 0 ∧ actualBalanceAt m v ≤
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v highC pre) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v highC pre)
          := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- The key is not active at any epoch up to the current one, at a state of the rest of the run.
  have inactive : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v]? = some w → ∀ e : Epoch,
        e.toNat ≤ (getCurrentEpoch m.state).toNat → isActiveValidator w e = false := by
    intro m run w found e le
    by_contra active
    simp only [Bool.not_eq_false, isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
      at active
    have lowEpoch := UInt64.le_iff_toNat_le.mp active.1
    have highEpoch := UInt64.lt_iff_toNat_lt.mp active.2
    have exitBound := w.exitEpoch.toNat_lt
    by_cases assigned : w.activationEpoch = FAR_FUTURE_EPOCH
    · rw [assigned] at lowEpoch
      have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
    · have := ahead m run w found assigned
      omega
  intro m pre
  induction pre with
  | nil =>
    intro _
    rw [start]
    exact ⟨rfl, Nat.zero_le _⟩
  | @snoc middle last pre step ih =>
    intro post
    have shared : Run config checks g middle := (toFin.append fromFin).append pre
    have afterStep : Run config checks middle z := (Run.nil.snoc step).append post
    have middleZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps afterStep.chainSteps)
    have middleFork := fork_le_of_chainSteps afterStep.chainSteps
    have lastFork := fork_le_of_chainSteps post.chainSteps
    have selected : (getCurrentEpoch middle.state).toNat ≤ highC + 1 := by omega
    rw [Internal.grossScan_snoc, Internal.creditScan_snoc, Internal.creditScan_snoc]
    simp only [selected, ↓reduceIte]
    obtain ⟨noGross, before⟩ := ih afterStep
    have lastEarly : last.fork < .glamsterdam := Nat.lt_of_le_of_lt lastFork zEarly
    cases step with
    | block engine signed due ok =>
      have gross := Internal.block_balance_le_gross (engine := engine) (signed := signed) (due :=
        due)
        (ok := ok) shared h.genesis lastEarly
        (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) v
      have zero := block_idle_step (engine := engine) (signed := signed) (due := due) (ok := ok)
        h.genesis h.parameters.lookahead h.facts.covers shared
        (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)) lastEarly v
        (fun w found => inactive _ afterStep w found _ (Nat.le_refl _))
        (fun w found => by
          by_cases assigned : w.activationEpoch = FAR_FUTURE_EPOCH
          · exact .inl assigned
          · exact .inr (ahead _ post w found assigned))
      exact ⟨by omega, by omega⟩
    | slot ok =>
      have middleElectra : .pectra ≤ middle.fork :=
        Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
      have middleEarly : middle.fork < .glamsterdam := Nat.lt_of_le_of_lt middleFork zEarly
      have known : v < middle.state.validators.data.size ∨ BalancesMatch middle.state := by
        by_cases inside : v < middle.state.validators.data.size
        · exact .inl inside
        · exact .inr (Run.invariant (Genesis.invariant h.genesis) shared).balancesMatch
      have idle : v.toUInt64 ∉ getActiveValidatorIndices middle.state
          (getPreviousEpoch middle.state) := by
        intro active
        obtain ⟨w, found, isActive⟩ :=
          (mem_getActiveValidatorIndices (middle.state.validators.bound middleEarly)).mp active
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small] at found
        have previous := getPreviousEpoch_toNat middle.state
        rw [inactive middle afterStep w found _ (by omega)] at isActive
        exact Bool.false_ne_true isActive
      have noCredit : Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s =
        .sync))
          (fun _ => false) v (Step.slot ok : Step config checks middle last) = 0 := by
        simp [Internal.stepCredit]
      have step := slot_idle_step shared h.genesis ok lastEarly middleElectra v known idle
      exact ⟨by omega, by omega⟩

/-- An active validator's activation is before the far-future epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.activation_ne_far_of_active {w :
  Validator} {e : Epoch}
    (active : isActiveValidator w e = true) : w.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  have low := UInt64.le_iff_toNat_le.mp (activationLe_of_active active)
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  have high := UInt64.lt_iff_toNat_lt.mp active.2
  have bound := w.exitEpoch.toNat_lt
  intro far
  rw [far] at low
  have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  omega

/-- A voter that is active at a state has its activation assigned and reached. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.activated_of_activeVoters (early :
  fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ activeVoters s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧ w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
      w.activationEpoch ≤ getCurrentEpoch s := by
  obtain ⟨w, found, active⟩ := Internal.active_of_activeVoters early member
  exact ⟨w, found, Internal.activation_ne_far_of_active active, activationLe_of_active active⟩

/-- A voter of the quorum has its activation assigned and reached.

The quorum holds the keys that are active at the current or the previous epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.activated_of_quorum (early : fork <
  .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ Internal.Q s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧ w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧
      w.activationEpoch ≤ getCurrentEpoch s := by
  have listed := (Finset.mem_filter.mp (member : v ∈ quorumVoters s)).1
  rw [List.mem_toFinset, List.mem_append] at listed
  rcases listed with now | before
  · exact Internal.activated_of_activeVoters early (by simpa [activeVoters] using now)
  · obtain ⟨w, found, active⟩ :=
      (mem_getActiveValidatorIndices (s.validators.bound early)).mp before
    exact ⟨w, found, Internal.activation_ne_far_of_active active,
      UInt64.le_trans (activationLe_of_active active) (getPreviousEpoch_le s)⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C activates has its activation before its exit. -/
private theorem activated_ordered (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted) :
    ∀ vy, counted.validators.data[v.toNat]? = some vy →
      vy.activationEpoch.toNat < vy.exitEpoch.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨w, foundC, neFar, -⟩ := activated
  intro vy found
  obtain rfl := Option.some.inj (found.symm.trans foundC)
  have farToNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have bound := vy.activationEpoch.toNat_lt
  have notFar : vy.activationEpoch.toNat ≠ 2 ^ 64 - 1 := fun same =>
    neFar (UInt64.toNat_inj.mp (by rw [same]; rfl))
  by_cases exit : vy.exitEpoch = FAR_FUTURE_EPOCH
  · rw [exit]
    omega
  · have gap := (toFin.append (fromFin.append tailC)).exit_activation_gap h.genesis v.toNat vy
      found exit
    omega

/-- A key activated by C and absent at the split holds the activation reserve at a state of C's run.

The run from the split reaches that state first, and then C.

The key is activated by C, before it exits, and absent at the split.

At that state its balance is at least `MAX_EFFECTIVE_BALANCE`.

Its effective balance is within the downward band of its balance, and at least that.

The key is idle before that state, so its balance is at most the credits that the scans count. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_start (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ z)
      (post : Run config checks z ⟨fork, counted⟩), tailC = pre.append post ∧
      z.fork < .glamsterdam ∧ z.fork ≤ fork ∧
      (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch counted).toNat ∧
      v.toNat < z.state.validators.data.size ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ actualBalanceAt z v.toNat ∧
      effectiveAt z v.toNat ≤ actualBalanceAt z v.toNat + preset.downwardBand ∧
      preset.MAX_EFFECTIVE_BALANCE.toNat ≤ effectiveAt z v.toNat ∧
      actualBalanceAt z v.toNat ≤ Internal.grossScan v.toNat highC pre +
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC pre) +
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v.toNat highC
          pre) ∧ Internal.grossScan v.toNat highC pre = 0 ∧
      ∀ p ∈ pre.balancePath, ∀ w : Validator, p.state.validators.data[v.toNat]? = some w →
        w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch p.state).toNat + 1 < w.activationEpoch.toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- The key is activated at C, before its exit, and absent at the split.
  obtain ⟨w, foundC, neFar, lowC⟩ := activated
  have ordered := activated_ordered h fromFin tailC ⟨w, foundC, neFar, lowC⟩
  have splitAbsent : split.validators.data[v.toNat]? = none :=
    Array.getElem?_eq_none absent
  have pending : ∀ u, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[v.toNat]? =
      some u → (getCurrentEpoch (⟨fork, split⟩ : ForkedBeaconState preset).state).toNat + 1 <
        u.activationEpoch.toNat := fun u found => by
    simp only [splitAbsent] at found
    cases found
  obtain ⟨z, pre, post, v0, vy, splitEq, found0, foundY, sameAct, actEq, actLe⟩ :=
    Internal.Run.start_state tailC h.window v.toNat pending ⟨w, foundC, neFar, lowC⟩ ordered
  obtain rfl := Option.some.inj (foundY.symm.trans foundC)
  have actNeFar : v0.activationEpoch ≠ FAR_FUTURE_EPOCH := fun same =>
    neFar (sameAct.symm.trans same)
  have zFork : z.fork ≤ fork := fork_le_of_chainSteps post.chainSteps
  have zEarly : z.fork < .glamsterdam := Nat.lt_of_le_of_lt zFork h.early
  have actZ : (getCurrentEpoch z.state).toNat + 2 = v0.activationEpoch.toNat := by
    rw [sameAct]
    exact actEq
  -- At that state the key holds the activation reserve, which is positive.
  obtain ⟨-, funded, hysteresis, reserve⟩ :=
    Internal.Run.funded_at_start shared h.genesis h.caps h.aligned electra pre zEarly v.toNat found0
      actNeFar actZ
  have zCounted : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch counted).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  -- The key has no balance at the start, and no credit scan counts a step before that state.
  have startZero : actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat = 0 := by
    have matched : split.balances.data.size = split.validators.data.size :=
      (Run.invariant (Genesis.invariant h.genesis) shared).balancesMatch
    simp only [actualBalanceAt, Array.getElem?_eq_none (show
      split.balances.data.size ≤ v.toNat by omega), Option.map_none,
      Option.getD_none]
  -- the key is not yet active at a state before the one that schedules it
  have ahead : ∀ m : ForkedBeaconState preset, Run config checks m z → ∀ w : Validator,
      m.state.validators.data[v.toNat]? = some w → w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch m.state).toNat + 1 < w.activationEpoch.toNat :=
    fun m run w found assigned => by
      obtain ⟨later, foundLater, life⟩ := run.registryLifecycle.validators v.toNat w found
      have same : later = v0 := Option.some.inj (foundLater.symm.trans found0)
      subst same
      have act := life.activationEpoch assigned
      have mZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps run.chainSteps)
      rw [← act]
      omega
  obtain ⟨noGross, walk⟩ := key_idle_walk h v.toNat v.toNat_lt highC zEarly (by omega) ahead
    startZero pre Run.nil
  refine ⟨z, pre, post, splitEq, zEarly, zFork, zCounted,
    (Array.getElem?_eq_some_iff.mp found0).1, funded, hysteresis, reserve, by omega, noGross,
    fun p member => ?_⟩
  obtain ⟨-, r2, -⟩ := Internal.balancePath_endpoint pre (Run.nil : Run config checks z z) zFork
    member
  exact ahead p r2

/-- The activation reserve is positive. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.maxEffectiveBalance_pos
    (h : Setting config checks g split fin pulled anc counted V) :
    0 < preset.MAX_EFFECTIVE_BALANCE.toNat := by
  have newKey := h.facts.newKey .fusaka
  have size := h.facts.incrementSize
  by_contra zero
  have none : preset.MAX_EFFECTIVE_BALANCE.toNat = 0 := by omega
  rw [none] at newKey
  simp only [Nat.mul_zero, Nat.zero_div, Nat.zero_sub, Nat.le_zero] at newKey
  omega

/-- The consolidation credits of a run after the shared segment fit the due entries.

The keys of a set are credited at most the caps of the due entries of X's queue that name them.

The run from X to the end is the shared segment and then the run from the split.

The horizon is within the withdrawal delay of X, as `shallow` says. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cons_due_bound (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {z : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, z⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch z).toNat ≤ high + 1)
    (highLe : high ≤ (getCurrentEpoch pulled).toNat)
    {events eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events) (T : Finset ValidatorIndex) :
    ∑ v ∈ T, Internal.consAmt (eventsF ++ events) v.toNat ≤
      ((Internal.dueList fin (Nat.le_trans (by decide) h.fulu) high T).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
  classical
  have shallow := h.shallow
  obtain ⟨shared⟩ := h.toFin
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have bound := Internal.Run.consolidation_credits_le_X_targets (config := config)
    (checks := checks) shared h.genesis h.caps (fromFin.append tail)
    (Nat.le_trans (by decide) h.fulu) h.early high
    (Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed) endEpoch
    (by simp only; omega) (by omega) (T.image UInt64.toNat)
  have injective : Function.Injective UInt64.toNat := fun _ _ same => UInt64.toNat_inj.mp same
  simp only [injective.mem_finset_image] at bound
  rw [← Finset.sum_image (f := fun i => Internal.consAmt (eventsF ++ events) i)
    (fun _ _ _ _ e => UInt64.toNat_inj.mp e)]
  exact bound

/-- The keys that a consolidation of X's queue credits on C's run are at most its due entries.

Each such key is the target of a due entry, and each entry names one target. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cons_keys_le (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    {eventsF eventsC : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents highC = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) (T : Finset ValidatorIndex)
    (credited : ∀ v ∈ T, 0 < Internal.consAmt eventsC v.toNat) :
    T.card ≤ (pinTerms config pulled anc fin).consolidationsXCount := by
  classical
  have shallow := h.shallow
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have each (v : ValidatorIndex) (hv : v ∈ T) : 1 ≤ Internal.dueAt fin highC {v} := by
    have bound := Internal.cons_due_bound h fromFin tailC highC endEpochC highLe replayedF replayedC
      {v}
    rw [Internal.dueAt_eq fin electra highC]
    by_contra none
    have empty : Internal.dueList fin electra highC {v} = [] := List.length_eq_zero_iff.mp (by
      omega)
    simp only [Finset.sum_singleton, empty, List.map_nil, List.sum_nil] at bound
    have positive := credited v hv
    unfold Internal.consAmt at positive bound
    simp only [List.filter_append, List.map_append, List.sum_append] at bound
    omega
  calc T.card = ∑ v ∈ T, 1 := by simp
    _ ≤ ∑ v ∈ T, Internal.dueAt fin highC {v} := Finset.sum_le_sum each
    _ = Internal.dueAt fin highC T := dueAt_sum fin electra highC T
    _ ≤ (Internal.dueList fin electra (getCurrentEpoch pulled).toNat T).length := by
      rw [Internal.dueAt_eq fin electra highC]
      exact dueList_length_mono fin electra highLe T
    _ ≤ _ := by
      unfold pinTerms
      dsimp only
      simp only [shallow, electra, ↓reduceIte, ↓reduceDIte]
      simpa using Internal.dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat T fun _ =>
        1

/-- `consolidationsX` is the sum of the caps of the sources in X's queue that are due.

It is zero beyond the withdrawal delay, so the setting's `shallow` selects the entries. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.consolidationsX_eq (h : Setting
  config checks g split fin pulled anc counted V)
    (electra : .pectra ≤ fork) :
    (pinTerms config pulled anc fin).consolidationsX =
      (((((fin.pendingConsolidations electra).data.toList.filterMap fun c =>
        fin.validators.data[c.sourceIndex.toNat]?).filter fun v =>
          !v.slashed &&
            decide (v.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
            fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)).sum := by
  have shallow := h.shallow
  unfold pinTerms
  dsimp only
  simp only [shallow, electra, ↓reduceIte, ↓reduceDIte]

/-- The caps are whole increments, so `consolidationsX` is too. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.consolidationsX_aligned
    (h : Setting config checks g split fin pulled anc counted V) :
    (pinTerms config pulled anc fin).consolidationsX % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
      0 := by
  rw [Internal.consolidationsX_eq h (Nat.le_trans (by decide) h.fulu)]
  apply Nat.mod_eq_zero_of_dvd
  refine List.dvd_sum fun x hx => ?_
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  have := congrArg UInt64.toNat (withdrawalMaxEffectiveBalance_aligned (fork := fork) h.aligned v)
  exact Nat.dvd_of_mod_eq_zero (by simpa [UInt64.toNat_mod] using this)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key with no due consolidation entry takes no consolidation credit on C's run or before it.

The horizon of the due entries is cut to R's epoch, which C's replay does not read. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.consAmt_zero (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    {ending : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch ending).toNat ≤ highC + 1)
    (near : (getCurrentEpoch ending).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (none : Internal.dueAt fin highC {v} = 0) :
    Internal.consAmt eventsF v.toNat + Internal.consAmt eventsC v.toNat = 0 := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have later := UInt64.le_iff_toNat_le.mp h.later
  have ahead : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch ending).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
  obtain ⟨hc, hhc⟩ : ∃ hc, hc = min highC (getCurrentEpoch pulled).toNat := ⟨_, rfl⟩
  rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := hc) (by simp only; omega)
    (by simp only; omega)] at replayedF
  rw [balanceEvents_eq_of_endpoint_le tailC (localHigh := hc) (by simp only; omega)
    (by simp only; omega)] at replayedC
  have bound := Internal.cons_due_bound h fromFin tailC hc (by omega) (by omega) replayedF replayedC
    {v}
  have empty : Internal.dueList fin electra hc {v} = [] := List.length_eq_zero_iff.mp (by
    have := dueList_length_mono fin electra (show hc ≤ highC by omega) {v}
    rw [Internal.dueAt_eq fin electra highC] at none
    omega)
  simp only [Finset.sum_singleton, empty, List.map_nil, List.sum_nil] at bound
  unfold Internal.consAmt at bound ⊢
  simp only [List.filter_append, List.map_append, List.sum_append] at bound
  omega

/-- The caps of a list of validators are at least the maximum effective balance each. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cap_floor_sum (h : Setting config
  checks g split fin pulled anc counted V)
    (l : List Validator) :
    preset.MAX_EFFECTIVE_BALANCE.toNat * l.length ≤
      (l.map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
  have := List.length_nsmul_le_sum
    (l.map fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    preset.MAX_EFFECTIVE_BALANCE.toNat (by
      simp only [List.mem_map]
      rintro _ ⟨v, -, rfl⟩
      exact UInt64.le_iff_toNat_le.mp
        (Internal.minimum_cap h.caps.activation h.caps.compounding v))
  simpa [smul_eq_mul, Nat.mul_comm] using this

/-- A sum over a subset can be extended by zero to use the ambient set's pointwise bounds. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_eq_U {M : Type*} [AddCommMonoid
  M] {S W : Finset ValidatorIndex}
    (sub : S ⊆ W) (f : ValidatorIndex → M) :
    ∑ v ∈ S, f v = ∑ v ∈ W, if v ∈ S then f v else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr sub]

/-- The consolidation credits of C's branch, charged to `consolidationsX`.

The run from the finalized block's state X to C's state has the run from the split as its tail.

`Run.consolidation_credits_le_X_targets` bounds the credits to a set of targets.

The bound is the caps at X of the due entries of X's queue that name them.

It is over the whole run from X.

The run to R's state bounds the credits to V the same way.

The sets `V`, `K4`, `K5` and `K6` are disjoint.

So the sum over their union is at most the caps of X's queue: `consolidationsX`.

This holds as `high ≤` the epoch of the call and X is within the withdrawal delay.

The keys of `SC` are slashed at C, so they are not in `K4`, `K5`, `K6` or `V`.

Their credits join those of `K4`, `K5` and `K6` in the bound.

The keys of `CS` are created after R's registry and slashed at C.

So they are in none of those sets either.

Their credits join the bound with the same share and bands.

A whistleblower's share of the amounts of `SC` and `CS` is at most the amounts.

A due entry that names one of them adds its band.

A key of `V` or `K5` weighs three, and the others one.

Each applied entry also adds one upward band to its target's rise.

So the left side has `upwardBand` for each due entry of X's queue.

An entry is charged its cap at X, which is at least `MAX_EFFECTIVE_BALANCE`.

So three bands are at most three tenths of it.

The bound `3.3 · X ≤ (33 · X + 9) / 10` is the charge of `consolidationsX` in `pinReserve`.

Deeper than the withdrawal delay `consolidationsX` is 0, so the setting's `shallow` is used here. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_consolidations_base
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat) :
    (((∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, Internal.consAmt events v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ Internal.CS counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
          Internal.consAmt eventsF v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.bandX fin high
          v.toNat)) +
      preset.upwardBand * (Internal.dueAt fin highC (Internal.K4 pulled counted V) +
        Internal.dueAt fin highC (Internal.K6 pulled counted) + 3 * Internal.dueAt fin highC
          (Internal.K5 counted V) +
        3 * Internal.dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10) ∧
      (∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
        3 * (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
  classical
  have shallow := h.shallow
  have early := h.early
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  obtain ⟨eventsFin, replayedFin⟩ := fromFin.balanceEvents_ok early highC
  have sameF : eventsFin = eventsF := by
    have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
    simp only at splitC
    have same := DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin
      (high := highC) (localHigh := high)
      (by simp only; omega) (by simp only; omega)
    rw [same, replayedF] at replayedFin
    exact (Except.ok.inj replayedFin).symm
  subst sameF
  obtain ⟨Kall, hKall⟩ : ∃ K : Finset ValidatorIndex,
      K = Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted ∪
        Internal.SC pulled counted split ∪
        Internal.CS counted split := ⟨_, rfl⟩
  have boundC := Internal.cons_due_bound h fromFin tailC highC endEpochC highLe replayedFin
    replayedC Kall
  have boundR := Internal.cons_due_bound h fromFin tail high endEpoch highLeR replayedF replayed V
  -- The shared segment's amounts of the keys of `SC` that exited before the finalized epoch.
  set S' := (Internal.SC pulled counted split).filter fun v =>
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true with hS'
  have subS : S' ⊆ Kall := fun v hv => by
    rw [hKall]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
  have amountC : (∑ v ∈ Kall, Internal.consAmt eventsC v.toNat) + (∑ v ∈ S', Internal.consAmt
    eventsFin v.toNat) ≤
      ((Internal.dueList fin electra highC Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    rw [Internal.sum_eq_U subS, ← Finset.sum_add_distrib]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundC
    simp only [Internal.consAmt, List.filter_append, List.map_append, List.sum_append]
    split_ifs <;> omega
  have amountR : (∑ v ∈ V, Internal.consAmt events v.toNat) ≤
      ((Internal.dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum := by
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) boundR
    simp only [Internal.consAmt, List.filter_append, List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  -- The target sets are disjoint.
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  have d456 : Disjoint (Internal.K4 pulled counted V ∪ Internal.K5 counted V) (Internal.K6 pulled
    counted) :=
    Finset.disjoint_union_left.mpr ⟨d46, d56⟩
  obtain ⟨dS, dVS⟩ := Internal.sc_disjoint h
  obtain ⟨dC, dVC⟩ := Internal.cs_disjoint h
  have dKV : Disjoint Kall V := by
    rw [hKall, Finset.disjoint_left]
    intro v hk hv
    simp only [Finset.mem_union] at hk
    rcases hk with (((h4 | h5) | h6) | hS) | hC
    · simp only [Internal.K4, Finset.mem_filter] at h4
      exact h4.2.2.2 hv
    · simp only [Internal.K5, Finset.mem_filter] at h5
      exact h5.2.2 hv
    · simp only [Internal.K6, Finset.mem_filter] at h6
      exact h6.2.2 (h.voting v hv).1
    · exact Finset.disjoint_left.mp dVS hv hS
    · exact Finset.disjoint_left.mp dVC hv hC
  -- The amounts and the entries split over the three sets of C's keys.
  have splitAmount : (∑ v ∈ Kall, Internal.consAmt eventsC v.toNat) =
      (∑ v ∈ Internal.K4 pulled counted V, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ Internal.K5 counted V, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ Internal.K6 pulled counted, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt eventsC v.toNat) +
        (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC v.toNat) := by
    rw [hKall, Finset.sum_union dC, Finset.sum_union dS, Finset.sum_union d456,
      Finset.sum_union d45]
  have splitEntries (H : ℕ) : (Internal.dueList fin electra H Kall).length =
      (Internal.dueList fin electra H (Internal.K4 pulled counted V)).length +
        (Internal.dueList fin electra H (Internal.K5 counted V)).length +
        (Internal.dueList fin electra H (Internal.K6 pulled counted)).length +
        (Internal.dueList fin electra H (Internal.SC pulled counted split)).length +
        (Internal.dueList fin electra H (Internal.CS counted split)).length := by
    rw [hKall, dueList_length_union fin electra H dC, dueList_length_union fin electra H dS,
      dueList_length_union fin electra H d456, dueList_length_union fin electra H d45]
  -- The caps of the due entries are at least `MAX_EFFECTIVE_BALANCE` each.
  have floorC := Internal.cap_floor_sum h (Internal.dueList fin electra (getCurrentEpoch
    pulled).toNat Kall)
  have floorR := Internal.cap_floor_sum h (Internal.dueList fin electra high V)
  -- Both runs charge entries of X's queue, at most those that `consolidationsX` counts.
  have total : ((Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum +
      ((Internal.dueList fin electra high V).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum ≤
      (pinTerms config pulled anc fin).consolidationsX := by
    have hcX := Internal.consolidationsX_eq h electra
    have laterR := Internal.dueList_sum_mono fin electra highLeR V
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have union := dueList_sum_union fin electra (getCurrentEpoch pulled).toNat dKV
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    have all := Internal.dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat (Kall ∪ V)
      (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
    rw [hcX]
    omega
  have laterC := Internal.dueList_sum_mono fin electra highLe Kall
    (fun v => (withdrawalMaxEffectiveBalance preset fork v).toNat)
  -- Whole, the due caps of C's keys fit `consolidationsX`, so the weighted amounts fit three of it.
  have whole : (∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat) ≤
      3 * (pinTerms config pulled anc fin).consolidationsX := by
    omega
  refine ⟨?_, whole⟩
  have bandLen : (Internal.dueList fin electra highC (Internal.SC pulled counted split)).length +
      (Internal.dueList fin electra highC (Internal.CS counted split)).length +
      (Internal.dueList fin electra highC (Internal.K4 pulled counted V)).length +
      (Internal.dueList fin electra highC (Internal.K6 pulled counted)).length +
      3 * (Internal.dueList fin electra highC (Internal.K5 counted V)).length +
      (Internal.dueList fin electra high S').length ≤
        3 * (Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).length := by
    have union := splitEntries (getCurrentEpoch pulled).toNat
    have m4 := dueList_length_mono fin electra highLe (Internal.K4 pulled counted V)
    have m5 := dueList_length_mono fin electra highLe (Internal.K5 counted V)
    have m6 := dueList_length_mono fin electra highLe (Internal.K6 pulled counted)
    have mS := dueList_length_mono fin electra highLe (Internal.SC pulled counted split)
    have mC := dueList_length_mono fin electra highLe (Internal.CS counted split)
    have mF := (dueList_length_mono fin electra highLeR S').trans
      (dueList_length_subset fin electra (getCurrentEpoch pulled).toNat
        (Finset.filter_subset _ _ : S' ⊆ Internal.SC pulled counted split))
    omega
  have shareF := Internal.wShare_le (fork := fork) h.facts (∑ v ∈ S', Internal.consAmt eventsFin
    v.toNat)
  have shareS := Internal.wShare_le (fork := fork) h.facts
    (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt eventsC v.toNat)
  have shareC := Internal.wShare_le (fork := fork) h.facts
    (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC v.toNat)
  rw [Internal.bandX_sum fin electra highC (Internal.SC pulled counted split),
    Internal.bandX_sum fin electra highC (Internal.CS counted split), Internal.bandX_sum fin electra
      high S']
  rw [Internal.dueAt_eq fin electra highC, Internal.dueAt_eq fin electra highC, Internal.dueAt_eq
    fin electra highC,
    Internal.dueAt_eq fin electra highC, Internal.dueAt_eq fin electra highC, Internal.dueAt_eq fin
      electra high,
    Internal.dueAt_eq fin electra high]
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  generalize (Internal.dueList fin electra highC (Internal.K4 pulled counted V)).length = d4 at *
  generalize (Internal.dueList fin electra highC (Internal.K5 counted V)).length = d5 at *
  generalize (Internal.dueList fin electra highC (Internal.K6 pulled counted)).length = d6 at *
  generalize (Internal.dueList fin electra highC (Internal.SC pulled counted split)).length = dS' at
    *
  generalize (Internal.dueList fin electra highC (Internal.CS counted split)).length = dC' at *
  generalize (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt eventsC v.toNat) = aS at *
  generalize Internal.wShare preset fork aS = wS at *
  generalize (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC v.toNat) = aC at *
  generalize Internal.wShare preset fork aC = wC at *
  generalize (Internal.dueList fin electra high S').length = dF at *
  generalize (∑ v ∈ S', Internal.consAmt eventsFin v.toNat) = aF at *
  generalize Internal.wShare preset fork aF = wF at *
  generalize (Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).length = dK at *
  generalize (Internal.dueList fin electra high V).length = dV at *
  generalize ((Internal.dueList fin electra highC Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK' at *
  generalize ((Internal.dueList fin electra (getCurrentEpoch pulled).toNat Kall).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PK at *
  generalize ((Internal.dueList fin electra high V).map fun v =>
    (withdrawalMaxEffectiveBalance preset fork v).toNat).sum = PV at *
  generalize (pinTerms config pulled anc fin).consolidationsX = cX at *
  have bandsK : preset.upwardBand * dS' + preset.upwardBand * dC' +
      preset.upwardBand * (d4 + d6 + 3 * d5 + 3 * dV) + preset.upwardBand * dF ≤
        3 * (preset.upwardBand * (dK + dV)) := by
    have : dS' + dC' + (d4 + d6 + 3 * d5 + 3 * dV) + dF ≤ 3 * (dK + dV) := by omega
    calc preset.upwardBand * dS' + preset.upwardBand * dC' +
          preset.upwardBand * (d4 + d6 + 3 * d5 + 3 * dV) + preset.upwardBand * dF
        = preset.upwardBand * (dS' + dC' + (d4 + d6 + 3 * d5 + 3 * dV) + dF) := by ring
      _ ≤ preset.upwardBand * (3 * (dK + dV)) := Nat.mul_le_mul_left _ this
      _ = 3 * (preset.upwardBand * (dK + dV)) := by ring
  have bandsM : 10 * (preset.upwardBand * (dK + dV)) ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV := by
    calc 10 * (preset.upwardBand * (dK + dV))
        = (10 * preset.upwardBand) * (dK + dV) := by ring
      _ ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * (dK + dV) := Nat.mul_le_mul_right _ h.facts.band
      _ = preset.MAX_EFFECTIVE_BALANCE.toNat * dK + preset.MAX_EFFECTIVE_BALANCE.toNat * dV :=
        Nat.mul_add _ _ _
  omega

/-- The consolidation credits of the third window, with the shares of `CS` and the shared segment.

The shared segment's shares are those of the keys of `SC` that exited before the finalized epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_consolidations (h : Setting
  config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat) :
    ((∑ v ∈ (Internal.K4 pulled counted V), Internal.consAmt eventsC v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ (Internal.K5 counted V), Internal.consAmt eventsC v.toNat) +
      3 * (∑ v ∈ V, Internal.consAmt events v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC
        v.toNat) +
      (∑ v ∈ Internal.CS counted split, Internal.bandX fin highC v.toNat) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
          Internal.consAmt eventsF v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.bandX fin high
          v.toNat)) +
      preset.upwardBand * (Internal.dueAt fin highC (Internal.K4 pulled counted V) +
        Internal.dueAt fin highC (Internal.K6 pulled counted) + 3 * Internal.dueAt fin highC
          (Internal.K5 counted V) +
        3 * Internal.dueAt fin high V) ≤
        (33 * (pinTerms config pulled anc fin).consolidationsX + 9) / 10 := by
  exact (Internal.bud_consolidations_base h fromFin tail high endEpoch replayed replayedF highLeR
    tailC highC
    endEpochC replayedC highLe).1

/-- The keys of `K6` whose exit started on R's branch after the split. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_exitedR :
    (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).exitedRB v.toNat =
      true,
      (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤
        (pinTerms config pulled anc fin).exitedR := by
  rw [Internal.exitedR_eq]
  refine voters_sum_le (fun i => balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
    fun v hv => ?_
  have flag := (Finset.mem_filter.mp hv).2
  obtain ⟨w, found⟩ := Internal.validator_of_flag (state := pulled) (i := v.toNat) (Or.inl flag)
  exact Internal.mem_positions_filter config pulled anc fin found flag

/-- Three sets with disjoint keys: the weights one, three and one are at most three. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.weighted_le {A B C : Finset
  ValidatorIndex} (f : ValidatorIndex → ℕ)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C) :
    ∑ v ∈ A, f v + 3 * ∑ v ∈ B, f v + ∑ v ∈ C, f v ≤ 3 * ∑ v ∈ A ∪ B ∪ C, f v := by
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨ac, bc⟩), Finset.sum_union ab]
  omega

/-- `slashedRB` reads the slashed flag and the withdrawable epoch of the key's record. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashedRB_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ) :
    (pinTerms config state ancestor finalizedState).slashedRB i =
      decide ((((state.validators.data[i]?).map (·.slashed)).getD false = true) ∧
        ((state.validators.data[i]?).any fun v => decide (
          ancestor.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
            v.withdrawableEpoch.toNat)) = true) := rfl

/-- A key that the pin counts as slashed on this branch holds a position of the registry. -/
private theorem slashedRB_lt (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ} (h : (pinTerms config state ancestor finalizedState).slashedRB i = true) :
    i < state.validators.data.size := by
  by_contra out
  have none : state.validators.data[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt out)
  rw [Internal.slashedRB_eq] at h
  simp [none] at h

/-- A slashed key counts in `slashedRB` when its withdrawable epoch is late enough.

That epoch must be a slashing vector past the finalized epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashedRB_of_withdrawable (config :
  Config)
    (state ancestor finalizedState : BeaconState preset fork) {i : ℕ} {w : Validator}
    (found : state.validators.data[i]? = some w) (slashed : w.slashed = true)
    (late : ancestor.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      w.withdrawableEpoch.toNat) :
    (pinTerms config state ancestor finalizedState).slashedRB i = true := by
  rw [Internal.slashedRB_eq]
  simpa [found, slashed] using late

/-- A key unslashed at the split and slashed at R counts in `slashedRB`.

R slashes it after the split, so its withdrawable epoch is a slashing vector past the split's. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashedRB_of_newly_slashed
    (h : Setting config checks g split fin pulled anc counted V) {i : ℕ} {s w : Validator}
    (foundS : split.validators.data[i]? = some s)
    (foundP : pulled.validators.data[i]? = some w) (cleanS : s.slashed = false)
    (slashedP : w.slashed = true) :
    (pinTerms config pulled anc fin).slashedRB i = true := by
  obtain ⟨tail⟩ := h.toPulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have delayed : (getCurrentEpoch split).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      w.withdrawableEpoch.toNat := (tail.newly_slashed_withdrawableEpoch h.caps.activation
    h.caps.compounding h.early (Internal.Setting.delay h) i s w foundS foundP cleanS slashedP).2
  exact Internal.slashedRB_of_withdrawable config pulled anc fin foundP slashedP (by omega)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The exit of a counted voter of the finalized registry is late at R.

The voter is not active at `counted` since an exit before the finalized epoch is excluded.

Its exit at R is then at least the finalized epoch, so it is late for the whole run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.voter_late (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (v : ValidatorIndex) (voter : v ∈ Internal.Q counted) :
    ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  classical
  intro wP foundP
  obtain ⟨tailC⟩ := h.toCounted
  have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inQ := voter
  simp only [Internal.Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inQ
  obtain ⟨listed, -⟩ := inQ
  obtain ⟨uC, foundC, activeC⟩ : ∃ uC, counted.validators.data[v.toNat]? = some uC ∧
      (isActiveValidator uC (getCurrentEpoch counted) = true ∨
        isActiveValidator uC (getPreviousEpoch counted) = true) := by
    rcases listed with now | before
    · obtain ⟨u, foundU, act⟩ := (mem_getActiveValidatorIndices within).mp now
      exact ⟨u, foundU, .inl act⟩
    · obtain ⟨u, foundU, act⟩ := (mem_getActiveValidatorIndices within).mp before
      exact ⟨u, foundU, .inr act⟩
  -- the voter's exit at R is not before the finalized epoch, so it is late for the whole run
  have short := Internal.window_short h
  by_cases exitedFin : wP.exitEpoch.toNat < (getCurrentEpoch fin).toNat
  · exfalso
    obtain ⟨uF', foundF', sameExit⟩ := Internal.exit_kept_of_le_fin h foundP (Nat.le_of_lt
      exitedFin)
    have exitNat : uF'.exitEpoch.toNat = wP.exitEpoch.toNat := congrArg UInt64.toNat sameExit
    have assigned : uF'.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      have far1 := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
      have far2 := congrArg UInt64.toNat far
      omega
    have previous := getPreviousEpoch_toNat counted
    have idle : ∀ e : Epoch, uF'.exitEpoch ≤ e → isActiveValidator uC e = false :=
      fun e reached => by
        have inactive := inactive_from_exit (fromFin.append tailC) foundF' assigned reached
        cases act : isActiveValidator uC e
        · rfl
        · exact absurd (inactive.symm.trans (isActiveAt_eq_true_iff.mpr ⟨uC, foundC, act⟩))
            Bool.false_ne_true
    rcases activeC with act | act
    · rw [idle (getCurrentEpoch counted) (UInt64.le_iff_toNat_le.mpr (by omega))] at act
      exact Bool.false_ne_true act
    · rw [idle (getPreviousEpoch counted) (UInt64.le_iff_toNat_le.mpr (by omega))] at act
      exact Bool.false_ne_true act
  · omega

/-- A key whose exit at R is at or after the finalized epoch is late for the whole run.

The call's cutoff is within the withdrawal delay of the finalized epoch.

`voter_late` gives the same for a counted voter. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.late_of_exitAfterFin (h : Setting
  config checks g split fin pulled anc counted V)
    (i : ℕ) (exitAfterFin : ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch fin).toNat ≤ w.exitEpoch.toNat) :
    ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  intro w found
  have after := exitAfterFin w found
  have short := Internal.window_short h
  omega

/-- A counted voter is unslashed at the split.

It is unslashed at `counted`, and a slashing stays. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.voter_unslashed (h : Setting config
  checks g split fin pulled anc counted V)
    (v : ValidatorIndex) (voter : v ∈ Internal.Q counted) :
    (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false := by
  classical
  obtain ⟨tailC⟩ := h.toCounted
  have within := BeaconState.registryWithinLimit_of_lt h.early counted
  have inQ := voter
  simp only [Internal.Q, quorumVoters, Finset.mem_filter, List.mem_toFinset, List.mem_append] at inQ
  obtain ⟨listed, unslashedC⟩ := inQ
  obtain ⟨uC, foundC⟩ : ∃ uC, counted.validators.data[v.toNat]? = some uC := by
    rcases listed with now | before
    · obtain ⟨u, foundU, -⟩ := (mem_getActiveValidatorIndices within).mp now
      exact ⟨u, foundU⟩
    · obtain ⟨u, foundU, -⟩ := (mem_getActiveValidatorIndices within).mp before
      exact ⟨u, foundU⟩
  have cleanC : uC.slashed = false := by simpa [foundC] using unslashedC
  cases foundS : split.validators.data[v.toNat]? with
  | none => rfl
  | some uS =>
    simp [Internal.unslashed_of_run tailC foundS (fun u read => by
      rw [foundC] at read
      cases read
      exact cleanC)]

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key slashed at R after a state of its run, where it is unslashed, is withdrawable late.

It is withdrawable a slashings vector after that state.

The state is at or after the finalized epoch, so the pin counts the slashing. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashed_withdrawable_of_clean
    (h : Setting config checks g split fin pulled anc counted V) {d : BeaconState preset fork}
    (run : Run config checks ⟨fork, d⟩ ⟨fork, pulled⟩) (v : ValidatorIndex)
    (clean : ∀ u, d.validators.data[v.toNat]? = some u → u.slashed = false)
    (inside : v.toNat < d.validators.data.size)
    (finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch d) :
    ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
      anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat := by
  intro wP foundP slashedP
  obtain ⟨uD, foundD⟩ : ∃ uD, d.validators.data[v.toNat]? = some uD :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have newly := (run.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
    h.early (Internal.Setting.delay h) v.toNat uD wP foundD foundP (clean uD foundD) slashedP).2
  have newly' : (getCurrentEpoch d).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      wP.withdrawableEpoch.toNat := newly
  have finalizedNat := UInt64.le_iff_toNat_le.mp finalized
  omega

/-- Under the guard, the window from the finalized epoch through R's horizon is under half a vector.

It is the short window of the guard, read at R's horizon. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.depthFin_lt_half (h : Setting
  config checks g split fin pulled anc counted V) :
    (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat <
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, short, _⟩ := id h.guard
  change (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat + 2 <
    preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 at short
  omega

/-- A step that slashes a key stays in its epoch.

A slot step keeps each slashed flag, and a block keeps the slot. -/
private theorem step_slash_epoch {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (fulu : .fusaka ≤ m.fork) (i : ℕ)
    (clean : (slashedFlagAt m.state i).getD false = false)
    (slashed : (slashedFlagAt n.state i).getD false = true) :
    (getCurrentEpoch n.state).toNat = (getCurrentEpoch m.state).toNat := by
  cases step with
  | slot ok =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp ok
    obtain rfl := DirectSafety.Apriori.Internal.processUpgrades_eq_of_window upgraded fulu early
    have same := slashedFlagAt_advanceSlot advancedOk i
    rw [clean] at same
    exact absurd (same.symm.trans slashed) Bool.false_ne_true
  | @block f s t engine signed due ok =>
    obtain ⟨-, processed, -⟩ := applySignedBlock_ok ok
    have slot := (frame_processBlock processed).slot
    simp only [getCurrentEpoch, slot]

/-- A state before the last step of a run leads to the first state of that step. -/
private theorem prefix_leads {x m n : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) {m1 n1 : ForkedBeaconState preset}
    (before : Run config checks x m1) (step1 : Step config checks m1 n1)
    (after : Run config checks n1 n) (cut : (before.snoc step1).append after = pre.snoc step) :
    Nonempty (Run config checks m1 m) := by
  cases after with
  | nil =>
    obtain ⟨rfl, -, -⟩ := Run.snoc.inj cut
    exact ⟨Run.nil⟩
  | snoc rest step2 =>
    obtain ⟨rfl, -, -⟩ := Run.snoc.inj cut
    exact ⟨(Run.nil.snoc step1).append rest⟩

/-- A key unslashed at `c` and slashed at a later state is withdrawable a vector past `fin`.

The key is slashed after `c`, so its withdrawable epoch is the slashings vector past that epoch.

The finalized epoch is at most the epoch of `c`. -/
private theorem slashed_withdrawable_vector
    (h : Setting config checks g split fin pulled anc counted V) (v : ValidatorIndex)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (inside : v.toNat < c.validators.data.size)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    {a : ForkedBeaconState preset} (run : Run config checks ⟨fork, c⟩ a)
    (low : a.fork < .glamsterdam) (u : Validator)
    (foundU : a.state.validators.data[v.toNat]? = some u) (flag : u.slashed = true) :
    (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      u.withdrawableEpoch.toNat := by
  obtain ⟨uB, foundB⟩ : ∃ uB, c.validators.data[v.toNat]? = some uB :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  have lower := (run.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
    low (Internal.Setting.delay h) v.toNat uB u foundB foundU (clean uB foundB) flag).2
  simp only at finC lower
  omega

/-- A key unslashed at `c` and slashed at a later state is withdrawable beyond R's horizon.

The guard keeps the window from the finalized epoch through R's horizon under half a vector. -/
private theorem slashed_beyond_horizon
    (h : Setting config checks g split fin pulled anc counted V) (v : ValidatorIndex)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (inside : v.toNat < c.validators.data.size)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    {a : ForkedBeaconState preset} (run : Run config checks ⟨fork, c⟩ a)
    (low : a.fork < .glamsterdam) (u : Validator)
    (foundU : a.state.validators.data[v.toNat]? = some u) (flag : u.slashed = true) :
    (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat := by
  have := slashed_withdrawable_vector h v toC inside clean run low u foundU flag
  have half := Internal.depthFin_lt_half h
  omega

/-- A key unslashed at R that R does not hold withdrawable has a late exit.

Its withdrawable epoch is its exit plus the delay, or both are unset. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.late_of_withdrawable (h : Setting
  config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (i : ℕ) (w : Validator)
    (found : pulled.validators.data[i]? = some w) (clean : w.slashed = false)
    (beyond : (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) :
    (getCurrentEpoch pulled).toNat + 1 <
      w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  obtain ⟨shared⟩ := h.toFin
  have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  rcases Run.withdrawable_eq_exit_delay (shared.append (fromFin.append tail)) h.genesis i w found
    clean with ⟨exitFar, withdrawFar⟩ | eq
  · have := congrArg UInt64.toNat exitFar
    have farEq : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  · omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key slashed at R, from a state of R's run, across the step that slashes it.

The key is unslashed at `c`, and the pin counts it as slashed on R's branch.

The run from the state splits at the step that slashes the key.

Before the step the key is unslashed, and its withdrawable epoch is beyond the epoch of that step.

After it the key is slashed, so its withdrawable epoch is beyond R's horizon.

The floor is R's balance, the run's debits, and the one slack of the slashing that `slashW` holds.

A key slashed at the state needs no step, and takes `slashed_floor` from that state. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slash_floor_across (h : Setting
  config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩) (inside : v.toNat < c.validators.data.size)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    (wP : Validator) (foundP : pulled.validators.data[v.toNat]? = some wP)
    (slashedP : wP.slashed = true)
    (rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true)
    {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
    (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩)
    {evs : List (BalanceEvent preset)}
    (ev : rest.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum +
          Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨uB, foundB⟩ : ∃ uB, c.validators.data[v.toNat]? = some uB :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have cleanB : uB.slashed = false := clean uB foundB
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  obtain ⟨val, foundZ⟩ : ∃ val, zs.validators.data[v.toNat]? = some val :=
    ⟨_, Array.getElem?_eq_getElem
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))⟩
  -- the cap of the voter at the state is the cap that the floor reads
  have atZ : PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinTerms.capAt, foundZ]
  have topDiv : PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat /
      (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
      Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
    have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat =
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
      simp [Internal.slashW, rb]
    rw [hW, parameters_of_fusaka h.fulu h.early]
    exact Nat.div_le_div_right (Internal.capAt_le_capMax h.caps electra v.toNat)
  -- the floor of a slashed key from a state to R
  have slashedTail : ∀ {a : BeaconState preset fork}
      (runA : Run config checks ⟨fork, c⟩ ⟨fork, a⟩)
      (restA : Run config checks ⟨fork, a⟩ ⟨fork, pulled⟩) {evsA : List (BalanceEvent preset)},
      restA.balanceEvents (getCurrentEpoch pulled).toNat = .ok evsA → ∀ ua : Validator,
      a.validators.data[v.toNat]? = some ua → ua.slashed = true →
      min (actualBalanceAt (⟨fork, a⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, a⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evsA.map (penaltyDebit v.toNat)).sum + (evsA.map (Internal.syncDebit v.toNat)).sum +
          (evsA.map (floorPartialDebit v)).sum := by
    intro a runA restA evsA evA ua foundA flagA
    have floor := slashed_floor h (toC.append runA) (e := pulled) (Nat.le_succ _) restA
      (getCurrentEpoch pulled).toNat (Nat.le_succ _) evA v ua foundA
      (fun flag => slashed_withdrawable_vector h v toC inside clean runA h.early ua foundA flag)
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (path_le_cap_pulled h (toC.append runA) restA .nil v.toNat)
      (fun before step after _ _ _ => .inr fun u foundU => by
        obtain ⟨w', foundW', flagW'⟩ := before.slashedPersistence v.toNat ua foundA flagA
        have same := Option.some.inj (foundW'.symm.trans foundU)
        have low := Nat.lt_of_le_of_lt
          (fork_le_of_chainSteps ((Run.nil.snoc step).append after).chainSteps) h.early
        exact slashed_beyond_horizon h v toC inside clean (runA.append before) low u foundU
          (same ▸ flagW'))
    have capEq : PinTerms.capAt (⟨fork, a⟩ : ForkedBeaconState preset) v.toNat =
        (withdrawalMaxEffectiveBalance preset fork ua).toNat := by
      simp [PinTerms.capAt, foundA]
    rw [ite_eq_left flagA] at floor
    omega
  by_cases startSlashed : val.slashed = true
  · -- the key is slashed already at the state
    have := slashedTail pre rest ev val foundZ startSlashed
    omega
  · have cleanZ : val.slashed = false := by simpa using startSlashed
    -- the run splits at the step that slashes the key
    obtain ⟨m, n, pre', step, post, split', notYet, arrived⟩ := Run.split_at_flip rest
      (fun z => ∃ w, z.state.validators.data[v.toNat]? = some w ∧ w.slashed = true)
      (fun hx => by
        obtain ⟨w, found, flag⟩ := hx
        have found' : zs.validators.data[v.toNat]? = some w := found
        rw [foundZ] at found'
        cases found'
        simp [cleanZ] at flag)
      ⟨wP, foundP, slashedP⟩
    subst split'
    have forkM : m.fork = fork :=
      Internal.fork_eq_of_run pre' ((Run.nil.snoc step).append post) (Nat.le_refl _)
    have forkN : n.fork = fork := Internal.fork_eq_of_run (pre'.snoc step) post (Nat.le_refl _)
    obtain ⟨mf, mS⟩ := m
    obtain ⟨nf, nS⟩ := n
    have forkM' : fork = mf := forkM.symm
    have forkN' : fork = nf := forkN.symm
    subst forkM'
    subst forkN'
    obtain ⟨valM, foundM⟩ : ∃ valM, mS.validators.data[v.toNat]? = some valM :=
      ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le
        (Array.getElem?_eq_some_iff.mp foundZ).1 (registryGrows_of_chainSteps pre'.chainSteps))⟩
    have cleanM : valM.slashed = false := by
      by_contra flag
      exact notYet ⟨valM, foundM, by simpa using flag⟩
    obtain ⟨valN, foundN, slashedN⟩ := arrived
    have flagM : (slashedFlagAt mS v.toNat).getD false = false := by
      simp [slashedFlagAt, foundM, cleanM]
    have flagN : (slashedFlagAt nS v.toNat).getD false = true := by
      simp [slashedFlagAt, foundN, slashedN]
    -- the slashing step is a block, so it stays in its epoch
    have sameEpoch : (getCurrentEpoch nS).toNat = (getCurrentEpoch mS).toNat :=
      step_slash_epoch step h.early h.fulu v.toNat flagM flagN
    have nearN : (getCurrentEpoch nS).toNat ≤ (getCurrentEpoch pulled).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    -- the key is not yet withdrawable when the step slashes it
    have slashable : (getCurrentEpoch mS).toNat < valM.withdrawableEpoch.toNat :=
      Internal.newly_slashed_unwithdrawable h.genesis h.caps (shared.append (toC.append (pre.append
        pre')))
        step h.early foundM foundN cleanM slashedN
    -- before the step the key is withdrawable beyond the epoch of the step
    have wide : ∀ {m1 : ForkedBeaconState preset} (toM1 : Run config checks ⟨fork, c⟩ m1)
        (toM : Run config checks m1 ⟨fork, mS⟩) (u : Validator),
        m1.state.validators.data[v.toNat]? = some u →
        (getCurrentEpoch mS).toNat - 1 + 1 < u.withdrawableEpoch.toNat := by
      intro m1 toM1 toM u foundU
      have low : m1.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps toM.chainSteps) h.early
      have reach : (getCurrentEpoch mS).toNat ≤ (getCurrentEpoch pulled).toNat := by omega
      by_cases flag : u.slashed = true
      · have := slashed_beyond_horizon h v toC inside clean toM1 low u foundU flag
        omega
      · have clean : u.slashed = false := by simpa using flag
        have farBound := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
        rcases (shared.append (toC.append toM1)).withdrawable_eq_exit_delay h.genesis v.toNat u
          foundU clean with ⟨-, far⟩ | eqW
        · rw [far]
          omega
        · by_cases assigned : u.exitEpoch = FAR_FUTURE_EPOCH
          · rw [assigned] at eqW
            omega
          · obtain ⟨mm, foundMM, life⟩ := toM.registryLifecycle.validators v.toNat u foundU
            have mmEq : mm = valM := Option.some.inj (foundMM.symm.trans foundM)
            have exM : valM.exitEpoch = u.exitEpoch := by
              rw [← mmEq]
              exact life.exitEpoch assigned
            rcases (shared.append (toC.append (pre.append pre'))).withdrawable_eq_exit_delay
              h.genesis v.toNat valM foundM cleanM with ⟨farM, -⟩ | exactM
            · exact absurd (exM.symm.trans farM) assigned
            · have lower := (shared.append (toC.append toM1)).exit_withdrawable_delay h.genesis
                v.toNat u foundU assigned
              have gap := (shared.append (toC.append toM1)).exit_activation_gap h.genesis
                v.toNat u foundU assigned
              have delayPos := (Internal.Setting.delay h)
              rw [exM] at exactM
              omega
    -- the floor of the run up to the slashed state
    obtain ⟨evs1, ok1⟩ := (pre'.snoc step).balanceEvents_ok h.early
      ((getCurrentEpoch mS).toNat - 1)
    obtain ⟨evs2, ok2⟩ := post.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
    have ok1' : (pre'.snoc step).balanceEvents (getCurrentEpoch pulled).toNat = .ok evs1 := by
      rw [balanceEvents_eq_of_endpoint_le (pre'.snoc step)
        (localHigh := (getCurrentEpoch mS).toNat - 1) (by simp only; omega)
        (by simp only; omega)]
      exact ok1
    have evEq : evs = evs1 ++ evs2 :=
      Except.ok.inj (ev.symm.trans (balanceEvents_append (pre'.snoc step) post _ ok1' ok2))
    have floor1 := slashed_floor h (toC.append pre) (e := nS) (by omega) (pre'.snoc step)
      ((getCurrentEpoch mS).toNat - 1) (by omega) ok1 v val foundZ
      (fun flag => absurd flag startSlashed)
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (path_le_cap_pulled h (toC.append pre) (pre'.snoc step) post v.toNat)
      (fun before step1 after1 cutB _ _ => .inr fun u foundU => by
        obtain ⟨toM⟩ := prefix_leads pre' step before step1 after1 cutB
        exact wide (pre.append before) toM u foundU)
    rw [ite_eq_right startSlashed] at floor1
    have floor2 := slashedTail (pre.append (pre'.snoc step)) post ok2 valN foundN slashedN
    have capMono := Internal.cap_le_cap_of_run h.caps (pre'.snoc step) h.early v.toNat
    rw [atZ] at capMono
    rw [evEq]
    simp only [List.map_append, List.sum_append] at floor1 floor2 ⊢
    rw [atZ]
    omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key unslashed at `c` at each state of R's run from `c`.

The run from `c` is the rest of the run from the finalized state to R's, cut at `c`.

The floor starts from the smaller of the voter's balance there and its cap there.

The cap there is the cap at R if it is frozen, and less if the voter switches to compounding on R.

It is R's balance, the debits of the rest of R's run, and the slack of a slashing on R.

A voter unslashed at R takes it from `key_floorR_from`.

A voter slashed at R takes it from `slashed_floor`, with the slack that `slashW` holds.

The key is unslashed at `c`.

A key slashed on R is withdrawable after the finalized epoch by a vector, by `slashedLate`.

The pin counts it, so `slashW` holds the slack.

The exit of the key at R is late for the whole run.

`voter_late` and `late_of_exitAfterFin` give that for a finalized key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.voter_floorAt (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (v : ValidatorIndex)
    {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (rest : Run config checks ⟨fork, c⟩ ⟨fork, pulled⟩)
    (cutC : toC.append rest = fromFin.append tail)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    (slashedLate : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
      anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat)
    (inside : v.toNat < c.validators.data.size)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
    (after : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append after = rest →
    ∀ {evs : List (BalanceEvent preset)},
    after.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum +
          Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
  classical
  have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  -- the key's records at the four states
  have sizeC := registryGrows_of_chainSteps rest.chainSteps
  obtain ⟨uB, foundB⟩ : ∃ uB, c.validators.data[v.toNat]? = some uB :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨wP, foundP⟩ : ∃ wP, pulled.validators.data[v.toNat]? = some wP :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside sizeC)⟩
  -- a record that is unslashed is the unslashed record at its index
  have only : ∀ {s : BeaconState preset fork} {u : Validator},
      s.validators.data[v.toNat]? = some u → u.slashed = false →
      ∀ w, s.validators.data[v.toNat]? = some w → w.slashed = false :=
    fun fu cu w fw => by
      rw [fu] at fw
      cases fw
      exact cu
  have cleanB : uB.slashed = false := clean uB foundB
  have finC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toC.chainSteps)
  intro zs pre after cut' evs ev
  have cut : (toC.append pre).append after = fromFin.append tail := by
    rw [← Run.append_assoc, cut', cutC]
  obtain ⟨val, foundZ⟩ : ∃ val, zs.validators.data[v.toNat]? = some val :=
    ⟨_, Array.getElem?_eq_getElem
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps))⟩
  -- the cap of the voter at the state is the cap that the floor reads
  have atZ : PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinTerms.capAt, foundZ]
  by_cases slashedP : wP.slashed = true
  · -- slashed on R after the split: the pin counts it, and `slashW` holds its slack
    have rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true :=
      Internal.slashedRB_of_withdrawable config pulled anc fin foundP slashedP
        (slashedLate wP foundP slashedP)
    exact Internal.slash_floor_across h v toC inside (fun u fu => only foundB cleanB u fu) wP foundP
      slashedP rb pre after ev
  · have cleanP : wP.slashed = false := by simpa using slashedP
    have lateP := late wP foundP cleanP
    have cleanZ : val.slashed = false := Internal.unslashed_of_run after foundZ (only foundP cleanP)
    have retainedZ : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, zs⟩ m)
        (step : Step config checks m n) (later : Run config checks n ⟨fork, pulled⟩),
        (before.snoc step).append later = after → ∀ w,
        n.state.validators.data[v.toNat]? = some w →
        ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
          ∀ u, m.state.validators.data[v.toNat]? = some u →
            (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) :=
      fun before step later cutB w foundW =>
        Internal.retained_of_exit h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_refl _) v
          foundP
          lateP ((toC.append pre).append before) step later
          (by
            rw [← cut, ← cutB]
            exact (Run.append_assoc (toC.append pre) (before.snoc step) later).symm)
          w foundW
    have floor := key_floorR_from h (toC.append pre) after (getCurrentEpoch pulled).toNat
      (Nat.le_succ _) ev v
      val foundZ cleanZ
      (fun w fw => by
        rw [← Option.some.inj (foundP.symm.trans fw)]
        exact cleanP)
      retainedZ
    rw [atZ]
    omega

/-- The effective balance of a key at the finalized state is at most `ebUp`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.effective_fin_le_ebUp (h : Setting
  config checks g split fin pulled anc counted V)
    (i : ℕ) :
    effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i ≤
      (pinTerms config pulled anc fin).ebUp i := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rw [Internal.ebUp_eq config pulled anc fin electra i _ rfl]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The floor of a key slashed at the finalized state, from a state of a run to R.

The key keeps its withdrawable epoch along every run, once it is slashed.

Its withdrawable epoch at R is the slashings vector past the finalized epoch, and past R's horizon.

So `slashed_floor` takes the floor of each state, with no slashing slack. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slash_floor_from_slashed
    (h : Setting config checks g split fin pulled anc counted V) (v : ValidatorIndex)
    (inFin : v.toNat < fin.validators.data.size)
    (slashedFin : ∀ u, fin.validators.data[v.toNat]? = some u → u.slashed = true)
    (wP : Validator) (foundP : pulled.validators.data[v.toNat]? = some wP)
    (frozen : (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      wP.withdrawableEpoch.toNat)
    (late : (getCurrentEpoch pulled).toNat + 1 < wP.withdrawableEpoch.toNat)
    {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) {evs : List (BalanceEvent preset)}
    (ev : r2.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
        (evs.map (floorPartialDebit v)).sum := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨uF, foundF⟩ : ∃ uF, fin.validators.data[v.toNat]? = some uF :=
    ⟨_, Array.getElem?_eq_getElem inFin⟩
  obtain ⟨val, foundZ, slashedZ⟩ := r1.slashedPersistence v.toNat uF foundF (slashedFin uF foundF)
  have assigned : val.exitEpoch ≠ FAR_FUTURE_EPOCH :=
    run_slashed_exit_assigned (shared.append r1) h.genesis h.caps.activation
      h.caps.compounding h.early (Internal.Setting.delay h) v.toNat val foundZ slashedZ
  have kept := r2.slashed_withdrawable_eq h.caps.activation h.caps.compounding h.early
    v.toNat val wP foundZ foundP slashedZ assigned
  have capEq : PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat =
      (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    simp [PinTerms.capAt, foundZ]
  have floor := slashed_floor h r1 (e := pulled) (Nat.le_succ _) r2
    (getCurrentEpoch pulled).toNat (Nat.le_succ _) ev v val foundZ
    (fun _ => by
      have := frozen
      rw [kept.2] at this
      exact this)
    (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (path_le_cap_pulled h r1 r2 .nil v.toNat)
    (fun before step after _ _ _ => .inr fun u foundU => by
      have low := Nat.lt_of_le_of_lt
        (fork_le_of_chainSteps ((Run.nil.snoc step).append after).chainSteps) h.early
      have keptU := before.slashed_withdrawable_eq h.caps.activation h.caps.compounding low
        v.toNat val u foundZ foundU slashedZ assigned
      have lateW := late
      rw [kept.2] at lateW
      rw [keptU.2]
      exact lateW)
  rw [ite_eq_left slashedZ] at floor
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a finalized key slashed at the split stays in its envelope on R's run.

A key unslashed at the finalized state is slashed on the shared segment or on R's run.

It takes its floor from `slash_floor_across` at the finalized state.

A key slashed at the finalized state keeps its withdrawable epoch along every run.

Its withdrawable epoch at R is the slashings vector past the finalized epoch, and past R's horizon.

So `slashed_floor` takes its floor from each state, with no slashing slack.

`prefix_envelope` turns the floor into the bound on the effective balance. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.kc_envelope (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (inFin : v.toNat < fin.validators.data.size)
    (slashedSplit : ∃ u, split.validators.data[v.toNat]? = some u ∧ u.slashed = true)
    (rb : (pinTerms config pulled anc fin).slashedRB v.toNat = true)
    (frozen : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) :
    ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨uF, foundF⟩ : ∃ uF, fin.validators.data[v.toNat]? = some uF :=
    ⟨_, Array.getElem?_eq_getElem inFin⟩
  obtain ⟨uS, foundS, flagS⟩ := slashedSplit
  obtain ⟨wP, foundP, slashedP⟩ := toPulled.slashedPersistence v.toNat uS foundS flagS
  have floorAt : ∀ {zs : BeaconState preset fork}
      (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (rest : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩),
      pre.append rest = fromFin.append tail → ∀ {evs : List (BalanceEvent preset)},
      rest.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
    intro zs pre rest _ evs ev
    by_cases cleanF : uF.slashed = false
    · exact Internal.slash_floor_across h v Run.nil inFin (fun u fu => by
        rw [← Option.some.inj (foundF.symm.trans fu)]
        exact cleanF) wP foundP slashedP rb pre rest ev
    · -- slashed at the finalized state, so slashed at every state of the run
      have slashedF : uF.slashed = true := by simpa using cleanF
      have := Internal.slash_floor_from_slashed h v inFin (fun u fu => by
        rw [← Option.some.inj (foundF.symm.trans fu)]
        exact slashedF) wP foundP (frozen wP foundP) (late wP foundP) pre rest ev
      omega
  exact Internal.prefix_envelope h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
    replayedF
    replayed v Run.nil (fromFin.append tail) (Run.nil_append (fromFin.append tail)) inFin
    (Internal.slashW (pinTerms config pulled anc fin) v.toNat)
    (Or.inl ⟨Internal.effective_fin_le_ebUp h v.toNat, Nat.le_refl _⟩) floorAt

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key unslashed at `c` at each state of R's run from `c`.

The run from `c` is the rest of the run from the finalized state to R's, cut at `c`.

It is within `ebUp` and a few increments, if it starts within `ebUp`.

It may start within the floor of its balance at `c` instead.

The increments are the whole ones of its sync debits and its slashing slack.

The floor of each state of that run is `voter_floorAt`.

`prefix_envelope` turns it into the bound on the effective balance. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.envelope_of_voter (h : Setting
  config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (rest : Run config checks ⟨fork, c⟩ ⟨fork, pulled⟩)
    (cutC : toC.append rest = fromFin.append tail)
    (clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false)
    (slashedLate : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
      anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat)
    (inside : v.toNat < c.validators.data.size)
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ z ∈ rest.balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
              Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  exact Internal.prefix_envelope h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
    replayedF
    replayed v toC rest cutC inside (Internal.slashW (pinTerms config pulled anc fin) v.toNat) start
    (Internal.voter_floorAt h fromFin tail v toC rest cutC clean slashedLate inside late)

/-- The keys of a set that the pin counts as slashed on this branch are at most `slashedR`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashedRB_card_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (W : Finset ValidatorIndex) :
    (W.filter fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat =
      true).card ≤ (pinTerms config state ancestor finalizedState).slashedR := by
  classical
  rw [Internal.slashedR_eq]
  refine Finset.card_le_card_of_injOn UInt64.toNat (fun v member => ?_)
    (fun a _ b _ same => UInt64.toNat_inj.mp same)
  obtain ⟨_, flag⟩ := Finset.mem_filter.mp member
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (slashedRB_lt config state ancestor
    finalizedState flag), flag⟩

/-- The keys slashed on this branch after the finalized epoch cost one increment each, once. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashR_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    (W : Finset ValidatorIndex) :
    ∑ v ∈ W, Internal.slashR (pinTerms config state ancestor finalizedState) v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config state ancestor finalizedState).slashedR := by
  classical
  have sum : ∑ v ∈ W, Internal.slashR (pinTerms config state ancestor finalizedState) v.toNat =
      ∑ v ∈ W.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
        = true), preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [Finset.sum_filter]
    rfl
  rw [sum, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Internal.slashedRB_card_le config state ancestor finalizedState W)

/-- A key that exited by the epoch of a run's start is inactive at the end of the run.

The run keeps an assigned exit epoch, and the epoch of its end is not before that of its start. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.inactive_of_exited (twoSlots : 2 ≤
  preset.SLOTS_PER_EPOCH.toNat)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) {i : ℕ} {v : Validator}
    (found : x.state.validators.data[i]? = some v)
    (exited : v.exitEpoch.toNat ≤ (getCurrentEpoch x.state).toNat) :
    isActiveAt y.state (getCurrentEpoch y.state) i = false := by
  have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    intro same
    rw [same] at exited
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have bound := (getCurrentEpoch x.state).toNat_lt_size
    simp only [UInt64.size] at bound
    exact getCurrentEpoch_ne_farFuture twoSlots x.state (UInt64.toNat_inj.mp (by omega))
  have forward := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  exact inactive_from_exit tail found assigned
    (UInt64.le_iff_toNat_le.mpr (Nat.le_trans exited forward))

/-- No block of a run from the finalized state has as proposer a key that exited by that state.

The key's exit is already assigned at the finalized state, so it is inactive on the whole run.

A proposer is active, which the lookahead of the run gives. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exited_not_proposer (h : Setting
  config checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)
    (u : ForkedBeaconState preset) (run : Run config checks ⟨fork, fin⟩ u) (p : ValidatorIndex) :
    u.fork < .glamsterdam → getBeaconProposerIndex u.state = .ok p → p.toNat ≠ i := by
  intro early proposer same
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨w0, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h foundPulled exited
  have inactive := Internal.inactive_of_exited h.twoSlots run foundFin (by rw [kept]; exact exited)
  have look := Run.lookaheadActive h.facts.covers h.genesis (toFin.append run) early
  have active := look.proposer_active
    (Nat.le_trans h.fulu (fork_le_of_chainSteps run.chainSteps)) proposer
  rw [same, inactive] at active
  exact Bool.false_ne_true active

/-- A scan over sources that the gross credits hold is at most the gross credits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.scan_le_gross {x y :
  ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) (p : BalanceSource → Bool)
    (inside : ∀ s, p s = true → s = .rewards ∨ s = .slashings ∨ s = .sync) :
    (Internal.creditScan p (fun _ => false) v high tail) ≤ Internal.grossScan v high tail := by
  have split := Internal.creditScan_or (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync))
    (fun _ => false) p (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync) && !p s)
    (fun _ => false) (fun _ => false)
    (fun s => by
      by_cases hp : p s = true
      · simp [hp, inside s hp]
      · simp [hp])
    (fun _ => rfl) (fun s ⟨first, second⟩ => by simp [first] at second)
    (fun s h => by simp at h) v high tail
  unfold Internal.grossScan
  omega

/-- A key with a sync credit over a run's replayed events has a gross credit on the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncCr_gross {x y :
  ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (tailC : Run config checks x y) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ℕ) (positive : 0 < Internal.syncCr eventsC v) : 0 < Internal.grossScan v highC tailC := by
  obtain ⟨-, sync⟩ := Internal.creditScan_bounds (∅ : Finset ValidatorIndex) UInt64.toNat
    (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) highC
    (fun _ => 0) tailC replayedC (fun e _ _ => by simp)
  have bound := sync (fun s => decide (s = .sync)) (Or.inl fun s covered => by
      simp only [decide_eq_true_eq] at covered ⊢
      exact Or.inr (Or.inr covered))
    (Or.inr fun ok _ fork early replayed i =>
      (Internal.sum_map_sync _ (Internal.keyCredit i)).symm.trans
        (Internal.slot_syncDebit_zero fork ok early replayed i).2) electra early v
  have conv : Internal.syncCr eventsC v = ((eventsC.filter (·.source = .sync)).map
    (Internal.keyCredit v)).sum :=
    Internal.sum_map_sync _ (Internal.keyCredit v)
  unfold Internal.grossScan
  rw [conv] at positive
  omega

/-- A key with a sync credit over the events of the shared segment has a gross credit on a run.

The run is the shared segment followed by a tail from the split. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncCr_gross_shared (h : Setting
  config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, z⟩) (high : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (v : ℕ) (positive : 0 < Internal.syncCr eventsF v) :
    0 < Internal.grossScan v high (fromFin.append tailC) := by
  have shared := Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early fromFin high
    replayedF v
    positive
  have split := Internal.creditScan_append (fun s => decide (s = .rewards ∨ s = .slashings ∨ s =
    .sync))
    (fun _ => false) v high fromFin tailC
  unfold Internal.grossScan at shared ⊢
  omega

/-- The rounding bands of a set of keys are the band for each key with a sync debit. -/
private theorem sum_bandR (events : List (BalanceEvent preset)) (T : Finset ValidatorIndex) :
    ∑ v ∈ T, Internal.bandR events v.toNat =
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        (T.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum).card := by
  classical
  simp only [Internal.bandR_eq]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The keys of `SC` that C's run charges to depart.

A key charged in the split's epoch reads the balance before the credits of `pre` that follow it.

A key charged later holds those credits in its charge, so reading them is an overpayment.

The overpayment fits the one application of `cut_whistle` over these keys and those of `K5`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.scCharged (pulled counted split :
  BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tailC : Run config checks x y) : Finset ValidatorIndex :=
  (Internal.SC pulled counted split).filter fun v => ∃ c ∈ tailC.departureCharges, c.index = v.toNat

/-- The keys of R's registry that are slashed at the split and that R's call reads as slashed.

They are the keys that the shared run slashes in its last epoch, and some before it.

The withdrawable epoch at R is a slashing vector past the finalized state's epoch.

The anchor's finalized epoch can lag that of the finalized state.

So this leaves out a key slashed before the finalized state's epoch.

Its correlation penalty can fall in the window.

None is in `SC`, which holds keys that are unslashed at the split.

None is in C's quorum, since a flag set at the split persists to C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cutKeys (config : Config) (pulled anc
  fin split : BeaconState preset fork) :
    Finset ValidatorIndex :=
  ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter fun v =>
    ((split.validators.data[v.toNat]?).map (·.slashed)).getD false = true ∧
      (pinTerms config pulled anc fin).slashedRB v.toNat = true ∧
      ((pulled.validators.data[v.toNat]?).any fun w =>
        decide ((getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)) = true

/-- A key that exited by the finalized epoch is exited at R's record. -/
private theorem exited_of_exitBeforeFin {v : ValidatorIndex}
    (exit : (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) :
    ∃ w, pulled.validators.data[v.toNat]? = some w ∧
      w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat := by
  have flag : ((pulled.validators.data[v.toNat]?).any fun w =>
      decide (w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = true := exit
  cases found0 : pulled.validators.data[v.toNat]? with
  | none => simp [found0] at flag
  | some w0 =>
    simp [found0] at flag
    exact ⟨w0, rfl, flag⟩

/-- A key that C's run charges to depart has not exited by the finalized epoch.

Its exit is assigned at the finalized state, so it is assigned at the start of C's run.

The charge is of a step that starts with the exit unassigned. -/
private theorem scCharged_not_exited (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {v : ValidatorIndex}
    (member : v ∈ Internal.scCharged pulled counted split tailC) :
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat ≠ true := by
  intro exit
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨-, c, cMember, cIndex⟩ := Finset.mem_filter.mp member
  obtain ⟨w, foundPulled, exited⟩ := exited_of_exitBeforeFin exit
  obtain ⟨u, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h foundPulled exited
  have assigned : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat (kept.symm.trans far)
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  obtain ⟨at_split, foundSplit, life⟩ := fromFin.registryLifecycle.validators v.toNat u foundFin
  have keptSplit := life.exitEpoch assigned
  obtain ⟨a, b, front, step, post, site, vv, w2, found, foundB, unset, set, amount, epoch⟩ :=
    tailC.departure_charge_site c cMember
  rw [cIndex] at found foundB
  obtain ⟨at_a, foundA, lifeA⟩ := front.registryLifecycle.validators v.toNat at_split foundSplit
  have same : at_a = vv := Option.some.inj (foundA.symm.trans found)
  have assignedSplit : at_split.exitEpoch ≠ FAR_FUTURE_EPOCH := by
    rw [keptSplit]
    exact assigned
  have keptA := lifeA.exitEpoch assignedSplit
  rw [same] at keptA
  exact assignedSplit (by rw [← keptA]; exact unset)

/-- A key with a proposer, whistleblower or sync credit on a run has a gross credit. -/
private theorem credit_gross {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (early : y.fork < .glamsterdam) (r : Run config checks x y) (highC : ℕ)
    {eventsP : List (BalanceEvent preset)} (replayedP : r.balanceEvents highC = .ok eventsP)
    (v : ℕ) (positive : 0 < Internal.propN r highC v + Internal.whistC r highC v + Internal.syncCr
      eventsP v) :
    0 < Internal.grossScan v highC r := by
  have prop := Internal.scan_le_gross r highC v (fun s => decide (s = .rewards))
    fun s h => by simp at h; simp [h]
  have whist := Internal.scan_le_gross r highC v (fun s => decide (s = .slashings))
    fun s h => by simp at h; simp [h]
  by_cases sync : 0 < Internal.syncCr eventsP v
  · exact Internal.syncCr_gross electra early r highC replayedP v sync
  · unfold Internal.propN Internal.whistC at positive
    omega

/-- A key credited on `pre` is a proposer of its epoch, or holds a seat of the split's committee.

The run `pre` is inside one epoch, from the start `b` of the split's epoch.

At most one block of `pre` is proposed in each of the epoch's slots. -/
private theorem pre_credit_seat (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b) (highC : ℕ) :
    ∃ B : Finset ℕ, B.card ≤ preset.SLOTS_PER_EPOCH.toNat ∧
      ∀ i, 0 < Internal.grossScan i highC pre → i ∈ B ∨ ∃ w, split.validators.data[i]? = some w ∧
        w.pubkey ∈
          (split.currentSyncCommittee (Nat.le_trans (by decide) h.fulu)).value.pubkeys.toList := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have samePeriod : (getCurrentEpoch split).toNat /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch b).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
    rw [sameEpoch]
  obtain ⟨B, D, cardB, -, gross, -, -, -⟩ := Internal.credited_piece h.genesis
    h.parameters.lookahead toB
    pre h.fulu altair h.early (Internal.Setting.delay h) highC samePeriod
  refine ⟨B, ?_, fun i pos => ?_⟩
  · -- the blocks of `pre` are at most one in each slot of the epoch
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := h.twoSlots; omega
    have count : pre.blockCount ≤
        ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch b).toNat) *
          preset.SLOTS_PER_EPOCH.toNat := pre.blockCount_le_epochs positive
    have one : (getCurrentEpoch split).toNat + 1 - (getCurrentEpoch b).toNat = 1 := by
      rw [sameEpoch]
      omega
    rw [one, Nat.one_mul] at count
    exact cardB.trans count
  · rcases gross i pos with inB | ⟨w, found, mem⟩
    · exact .inl inB
    · refine .inr ⟨w, found, ?_⟩
      rw [pre.currentSyncCommittee_eq_of_same_period h.early samePeriod altair altair]
      exact mem

/-- The rounding of an increment's reward is at most a third of a band, from quotient thirty. -/
private theorem whistle_round_le (inc W down : ℕ) (quotient : 30 ≤ W) (large : 3600 ≤ inc) :
    3 * ((inc + W - 1) / W) ≤ inc + down - 1 := by
  have le := Nat.div_mul_le_self (inc + W - 1) W
  generalize (inc + W - 1) / W = c at le ⊢
  rcases c with _ | k
  · omega
  · rw [Nat.succ_mul] at le
    have := Nat.mul_le_mul_left k quotient
    omega

/-- The bands of the classes and of the charged and cut keys fit the seats and slots, as numbers. -/
private theorem bands_arith (UP β cc SPE seats nV n4 n5 n6 nS nE nQ nB nU nK : ℕ)
    (bandUp : UP ≤ 2 * β) (ceil : 3 * cc ≤ β)
    (linear : 3 * nV + n4 + 3 * n5 + n6 + 3 * nU + nK ≤ 3 * seats) (subS : nS ≤ nU)
    (subEQ : nE + nQ ≤ nU) (cardB : nB ≤ SPE) :
    3 * (β * nV) + β * n4 + 3 * (β * n5) + β * n6 + β * nS + UP * nE + UP * (nB + nQ) +
        3 * (cc * nK) ≤ 3 * (β * (seats + SPE)) := by
  have scaled := Nat.mul_le_mul_left β linear
  have bandS := Nat.mul_le_mul_left β subS
  have bandEQ : UP * (nE + nQ) ≤ 2 * β * nU := Nat.mul_le_mul bandUp subEQ
  have bandB : UP * nB ≤ 2 * β * SPE := Nat.mul_le_mul bandUp cardB
  have bandK : 3 * cc * nK ≤ β * nK := Nat.mul_le_mul_right nK ceil
  nlinarith

/-- The cut keys are in no class of `bud_sync`.

A cut key is slashed at the split, and the flag persists to C.

So it is not in `V` or a quorum class, and it is not in `SC`, which is unslashed at the split.

It is in the split's registry, so it is not in `CS`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cut_disjoint (h : Setting config
  checks g split fin pulled anc counted V) :
    Disjoint (Internal.cutKeys config pulled anc fin split) (V ∪ Internal.K4 pulled counted V ∪
      Internal.K5 counted V ∪
      Internal.K6 pulled counted ∪ Internal.SC pulled counted split ∪ Internal.CS counted split) :=
        by
  rw [Finset.disjoint_left]
  intro v cut member
  simp only [Internal.cutKeys, Finset.mem_filter] at cut
  obtain ⟨w, found, marked⟩ : ∃ w, split.validators.data[v.toNat]? = some w ∧ w.slashed = true := by
    cases hw : split.validators.data[v.toNat]? <;> simp_all
  obtain ⟨toCounted⟩ := h.toCounted
  obtain ⟨u, foundC, markedC⟩ := toCounted.slashedPersistence v.toNat w found marked
  have atCounted : slashedFlagAt counted v.toNat = some true := by
    simp [slashedFlagAt, foundC, markedC]
  simp only [Finset.mem_union] at member
  rcases member with ((((inV | in4) | in5) | in6) | inSC) | inCS
  · have unslashed := (h.voting v inV).2
    simp [atCounted] at unslashed
  · exact Internal.classes_unslashed (Finset.mem_union_left _ (Finset.mem_union_left _ in4))
      atCounted
  · exact Internal.classes_unslashed (pulled := pulled)
      (Finset.mem_union_left _ (Finset.mem_union_right _ in5)) atCounted
  · exact Internal.classes_unslashed (V := V) (Finset.mem_union_right _ in6) atCounted
  · simp only [Internal.SC, Finset.mem_filter] at inSC
    have fresh := inSC.2.2
    simp [slashedFlagAt, found, marked] at fresh
  · simp only [Internal.CS, Finset.mem_filter] at inCS
    have := (Array.getElem?_eq_some_iff.mp found).1
    omega

/-- The bands of the classes, of the charged `SC` keys and of the cut keys fit the seats and slots.

The keys of `scCharged` with a credit on `pre` also pay an upward band.

A key that proposed in `pre` pays it from a slot of the epoch.

The bound adds the slots of an epoch to the seats.

The run `pre` starts at a state of the split's epoch, so its proposers fill the slots of one epoch.

Any other key holds a seat, by its sync credit, and pays it from the spare of its seat.

A cut key with a sync debit holds a seat and pays the rounding of an increment's reward there.

C's run is read at `highC`, and the shared segment and R's run at `high`.

The end epochs of R and of C are at most `high + 1` and `highC + 1`, as in `bud_branchR`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bands_seats (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    {events eventsF eventsC eventsP : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (replayedP : pre.balanceEvents highC = .ok eventsP) :
    3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ Internal.K4 pulled counted V, Internal.bandR (eventsF ++ events) v.toNat) +
        3 * (∑ v ∈ Internal.K5 counted V, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ Internal.K6 pulled counted, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ Internal.SC pulled counted split, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ Internal.SC pulled counted split,
          if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
            (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) +
        (∑ v ∈ Internal.scCharged pulled counted split tailC,
          if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
            Internal.syncCr eventsP v.toNat then
            preset.upwardBand else 0) +
        3 * (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) ≤
      3 * ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
        (preset.SYNC_COMMITTEE_SIZE.toNat *
          (((getCurrentEpoch pulled).toNat + 1) /
              max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
          ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) +
          preset.SLOTS_PER_EPOCH.toNat)) := by
  classical
  obtain ⟨d45, d46, d56, d4v, d5v, d6v⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, dSV⟩ := Internal.sc_disjoint h
  have cutApart := Internal.cut_disjoint h
  have dKV : Disjoint (Internal.cutKeys config pulled anc fin split) V :=
    Finset.disjoint_of_subset_right (fun v hv => by simp [Finset.mem_union, hv]) cutApart
  have dKK : Disjoint (Internal.cutKeys config pulled anc fin split)
      (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted) :=
    Finset.disjoint_of_subset_right (fun v hv => by
      simp only [Finset.mem_union] at hv ⊢
      tauto) cutApart
  have dKS : Disjoint (Internal.cutKeys config pulled anc fin split) (Internal.SC pulled counted
    split) :=
    Finset.disjoint_of_subset_right (fun v hv => by simp [Finset.mem_union, hv]) cutApart
  obtain ⟨B, cardB, creditB⟩ := pre_credit_seat h toB pre sameEpoch highC
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have altairF : .altair ≤ fork := Nat.le_trans (by decide) electra
  have whistleblower := h.facts.whistleblower fork
  -- the charged keys of `SC` that were credited on `pre`
  set fP := (Internal.scCharged pulled counted split tailC).filter fun v =>
    0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
      eventsP v.toNat with hfP
  have sumP : (∑ v ∈ Internal.scCharged pulled counted split tailC,
      if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat + Internal.syncCr
        eventsP v.toNat then
        preset.upwardBand else 0) = preset.upwardBand * fP.card := by
    rw [hfP, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases credit : 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
      Internal.syncCr eventsP v.toNat <;> simp [credit]
  set fB := fP.filter fun v => v.toNat ∈ B with hfB
  set fQ := fP.filter fun v => v.toNat ∉ B with hfQ
  have splitP : fB.card + fQ.card = fP.card :=
    Finset.card_filter_add_card_filter_not (s := fP) (fun v : ValidatorIndex => v.toNat ∈ B)
  have cardFB : fB.card ≤ B.card :=
    Finset.card_le_card_of_injOn (fun v : ValidatorIndex => v.toNat)
      (fun v hv => (Finset.mem_filter.mp hv).2)
      (fun a _ b _ same => UInt64.toNat_inj.mp same)
  -- a charged key credited on `pre`, and not a proposer there, holds a seat of the split
  have seatQ : ∀ v ∈ fQ, ∃ w, split.validators.data[v.toNat]? = some w ∧
      w.pubkey ∈ (split.currentSyncCommittee altairF).value.pubkeys.toList := by
    intro v hv
    obtain ⟨hvP, notB⟩ := Finset.mem_filter.mp hv
    obtain ⟨-, credit⟩ := Finset.mem_filter.mp hvP
    have gross := credit_gross electra h.early pre highC replayedP v.toNat credit
    rcases creditB v.toNat gross with inB | seat
    · exact absurd inB notB
    · exact seat
  have subQ : fQ ⊆ Internal.SC pulled counted split := fun v hv =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).1
  -- the cut keys with a sync debit
  set fK := (Internal.cutKeys config pulled anc fin split).filter fun v =>
    0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat with hfK
  have sumK : (∑ v ∈ Internal.cutKeys config pulled anc fin split,
      if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) =
      ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) * fK.card := by
    rw [hfK, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases debit : 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat <;> simp
      [debit]
  -- the rounding of an increment's reward at the whistleblower quotient is a third of a band
  have ceil : 3 * ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 := by
    have rounding := h.facts.rounding
    have vector := h.facts.vector
    exact whistle_round_le _ _ _ whistleblower (by omega)
  -- the upward band of a shared credit is paid by each exited key of `SC` with such a credit
  set fE := (Internal.SC pulled counted split).filter fun v =>
    (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
      0 < Internal.syncCr eventsF v.toNat with hfE
  have sumE : (∑ v ∈ Internal.SC pulled counted split,
      if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
        (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) =
      preset.upwardBand * fE.card := by
    rw [hfE, Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases exit : (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true <;>
      by_cases credit : 0 < Internal.syncCr eventsF v.toNat <;> simp [exit, credit]
  rw [sum_bandR, sum_bandR, sum_bandR, sum_bandR, sum_bandR, sumE, sumP, sumK]
  have upward := h.facts.upward
  have rounding := h.facts.rounding
  have vector := h.facts.vector
  have bandUp : preset.upwardBand ≤
      2 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) := by omega
  generalize preset.upwardBand = UP at bandUp ⊢
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 = β at bandUp ceil ⊢
  generalize ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) = cc at ceil ⊢
  generalize preset.SLOTS_PER_EPOCH.toNat = SPE at cardB ⊢
  generalize hSeats : preset.SYNC_COMMITTEE_SIZE.toNat *
    (((getCurrentEpoch pulled).toNat + 1) / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
    ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) = seats
  set fV := V.filter fun v => 0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum with
    hfV
  set f4 := (Internal.K4 pulled counted V).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hf4
  set f5 := (Internal.K5 counted V).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hf5
  set f6 := (Internal.K6 pulled counted).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hf6
  set fS := (Internal.SC pulled counted split).filter fun v =>
    0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum with hfS
  set U := fS ∪ fE ∪ fQ with hU
  have subU : U ⊆ Internal.SC pulled counted split :=
    Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) subQ
  -- the charged keys of `SC` are not exited by the finalized state
  have dEQ : Disjoint fE fQ := Finset.disjoint_left.mpr fun v hE hQ =>
    scCharged_not_exited h tailC
      (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1 (Finset.mem_filter.mp hE).2.1
  have dKf : Disjoint fV fK := dKV.symm.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have dK456 : Disjoint (f4 ∪ f5 ∪ f6) fK := dKK.symm.mono
    (Finset.union_subset_union (Finset.union_subset_union (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)) (Finset.filter_subset _ _)
  have dKU : Disjoint U fK := dKS.symm.mono subU (Finset.filter_subset _ _)
  have dSK : Disjoint (f4 ∪ f5 ∪ f6) U := dSC.mono
    (Finset.union_subset_union (Finset.union_subset_union (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)) (Finset.filter_subset _ _)) subU
  have dSf : Disjoint fV U := dSV.mono (Finset.filter_subset _ _) subU
  have d45' : Disjoint f4 f5 := d45.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d46' : Disjoint f4 f6 := d46.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d56' : Disjoint f5 f6 := d56.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d4f : Disjoint fV f4 := d4v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d5f : Disjoint fV f5 := d5v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have d6f : Disjoint fV f6 := d6v.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have inj : Function.Injective fun v : ValidatorIndex => v.toNat := fun a b same =>
    UInt64.toNat_inj.mp same
  -- A key debited on the shared segment is debited on C's run, and any other on R's tail.
  --
  -- A key that exited by the finalized epoch and has a shared credit holds a seat of C's run.
  obtain ⟨everyone, hEveryone⟩ : ∃ everyone, everyone = fV ∪ (f4 ∪ f5 ∪ f6 ∪ U ∪ fK) :=
    ⟨_, rfl⟩
  have replayedFC : fromFin.balanceEvents highC = .ok eventsF := by
    have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have laterNat := UInt64.le_iff_toNat_le.mp h.later
    rw [← DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin (high := high)
      (localHigh := highC) (by simp only; omega) (by simp only; omega)]
    exact replayedF
  have union := Internal.seat_union_card h fromFin tail tailC high highC replayed replayedFC
    replayedC
    altairF
    ((everyone.filter fun v =>
      0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
        ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
          0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ).image fun v => v.toNat)
    ((everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum).image
      fun v => v.toNat)
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      rcases (Finset.mem_filter.mp hv).2 with debit | ⟨exit, credit⟩ | seat
      · exact .inl debit
      · obtain ⟨w, found, exited⟩ := exited_of_exitBeforeFin exit
        exact .inr (.inl ⟨Internal.syncCr_gross_shared h fromFin tailC highC replayedFC v.toNat
          credit,
          fun u run p early proposer => Internal.exited_not_proposer h found exited u run p early
            proposer⟩)
      · exact .inr (.inr (seatQ v seat)))
    (fun i hi => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hv).2)
  rw [hSeats] at union
  have cover : (everyone.image fun v => v.toNat) ⊆
      ((everyone.filter fun v =>
        0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
            0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ).image fun v => v.toNat) ∪
      ((everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum).image
        fun v => v.toNat) := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    -- a key debited over both runs is debited on one of them
    have debited : 0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum →
        0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          0 < (events.map (Internal.syncDebit v.toNat)).sum := fun pos => by
      simp only [List.map_append, List.sum_append] at pos ⊢
      omega
    have inEv : v ∈ everyone := hv
    have viaF : 0 < ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum →
        v ∈ everyone.filter (fun v =>
          0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
            0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ) ∨
        v ∈ everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum := fun pos =>
      (debited pos).elim
        (fun d => .inl (Finset.mem_filter.mpr ⟨inEv, .inl d⟩))
        (fun d => .inr (Finset.mem_filter.mpr ⟨inEv, d⟩))
    have viaK : 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat →
        v ∈ everyone.filter (fun v =>
          0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
          ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
            0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ) ∨
        v ∈ everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum := fun pos =>
      viaF (by simp only [Internal.syncD, List.map_append, List.sum_append] at pos ⊢; omega)
    have inV : v ∈ everyone.filter (fun v =>
        0 < ((eventsF ++ eventsC).map (Internal.syncDebit v.toNat)).sum ∨
        ((pinTerms config pulled anc fin).exitBeforeFin v.toNat = true ∧
          0 < Internal.syncCr eventsF v.toNat) ∨ v ∈ fQ) ∨
        v ∈ everyone.filter fun v => 0 < (events.map (Internal.syncDebit v.toNat)).sum := by
      have split : v ∈ fV ∪ (f4 ∪ f5 ∪ f6 ∪ U ∪ fK) := hEveryone ▸ hv
      rcases Finset.mem_union.mp split with member | member
      · exact .inl (Finset.mem_filter.mpr ⟨inEv, .inl (Finset.mem_filter.mp member).2⟩)
      · rcases Finset.mem_union.mp member with member | member
        · rcases Finset.mem_union.mp member with member | member
          · rcases Finset.mem_union.mp member with member | member
            · rcases Finset.mem_union.mp member with member | member
              · exact viaF (Finset.mem_filter.mp member).2
              · exact viaF (Finset.mem_filter.mp member).2
            · exact viaF (Finset.mem_filter.mp member).2
          · rcases Finset.mem_union.mp member with member | member
            · rcases Finset.mem_union.mp member with member | member
              · exact viaF (Finset.mem_filter.mp member).2
              · exact .inl (Finset.mem_filter.mpr
                  ⟨inEv, .inr (.inl (Finset.mem_filter.mp member).2)⟩)
            · exact .inl (Finset.mem_filter.mpr ⟨inEv, .inr (.inr member)⟩)
        · exact viaK (Finset.mem_filter.mp member).2
    rcases inV with c | r
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, c, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, r, rfl⟩)
  have union' := (Finset.card_le_card cover).trans union
  have dEQU : Disjoint (f4 ∪ f5 ∪ f6 ∪ U) fK := Finset.disjoint_union_left.mpr ⟨dK456, dKU⟩
  have disjoint : Disjoint fV (f4 ∪ f5 ∪ f6 ∪ U ∪ fK) := by
    rw [Finset.disjoint_union_right, Finset.disjoint_union_right, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    exact ⟨⟨⟨⟨d4f, d5f⟩, d6f⟩, dSf⟩, dKf⟩
  rw [hEveryone, Finset.card_image_of_injective _ inj, Finset.card_union_of_disjoint disjoint,
    Finset.card_union_of_disjoint dEQU, Finset.card_union_of_disjoint dSK,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d46', d56'⟩),
    Finset.card_union_of_disjoint d45'] at union'
  have subS : fS.card ≤ U.card :=
    Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
  have subEQ : fE.card + fQ.card ≤ U.card := by
    rw [← Finset.card_union_of_disjoint dEQ]
    exact Finset.card_le_card (Finset.union_subset
      (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right)
  have linear : 3 * fV.card + f4.card + 3 * f5.card + f6.card + 3 * U.card + fK.card ≤
      3 * seats := by
    omega
  have key := bands_arith UP β cc SPE seats fV.card f4.card f5.card f6.card fS.card fE.card
    fQ.card fB.card U.card fK.card bandUp ceil linear subS subEQ (cardFB.trans cardB)
  rw [← splitP]
  linarith

/-- The flag reward of one increment is at most the reward of one increment. -/
private theorem flagRate_le (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).flagRate ≤
      (pinTerms config state ancestor finalizedState).perIncrement := by
  show _ * _ / _ ≤ _
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum ≤ WEIGHT_DENOMINATOR.toNat := by
    decide
  exact (Nat.div_le_div_right (Nat.mul_le_mul_left _ weights)).trans
    (Nat.mul_div_cancel _ (by decide : 0 < WEIGHT_DENOMINATOR.toNat)).le

/-- The rewards of the keys of a set that a test marks fit a quotient.

The quotient is of the sum over the positions that meet a stronger test.

Each reward is a quotient of the key's value.

A sum of quotients is at most the quotient of the sum. -/
private theorem floor_aux {A : Finset ValidatorIndex} {S : Finset ℕ} {P : ℕ → Prop}
    [DecidablePred P] {c q : ℕ} (f : ℕ → ℕ) (rb : ℕ → Bool)
    (inside : ∀ v ∈ A, rb v.toNat = true → v.toNat ∈ S ∧ P v.toNat) :
    ∑ v ∈ A.filter (fun v => rb v.toNat = true), f v.toNat / q ≤
      (∑ i ∈ S.filter P, f i + c) / q :=
  le_trans (DirectSafety.Apriori.Internal.sum_div_le (A.filter fun v => rb v.toNat = true)
    (fun v : ValidatorIndex => f v.toNat) q)
    (Nat.div_le_div_right (Nat.le_trans (voters_sum_le f fun v hv =>
      Finset.mem_filter.mpr (inside v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2))
      (Nat.le_add_right _ _)))

/-- `branchR` is a whistleblower charge and the slashed, proposer and rounding charges.

The slashed, proposer and rounding charges have weight three.

So has the whistleblower charge `Wh`.

The slashed charge covers the flag gain of two windows and the leak of one increment.

The remainder `W` holds those and the unit gain.

`Wh` pays the whistleblower reward of any set of keys that R's call reads as slashed on its branch.

Each reward is at the key's effective balance and rise, or at its balance at the finalized state. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.branchR_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    ∃ Wh W : ℕ, (pinTerms config state ancestor finalizedState).branchR =
      3 * (Wh + W + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (pinTerms config state ancestor finalizedState).slashedR +
        (pinTerms config state ancestor finalizedState).depth *
          (pinTerms config state ancestor finalizedState).proposerCredit +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
          ((pinTerms config state ancestor finalizedState).depth * preset.SLOTS_PER_EPOCH.toNat +
            (pinTerms config state ancestor finalizedState).depth *
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat *
              (((getCurrentEpoch state).toNat + 1) /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
                (getCurrentEpoch finalizedState).toNat /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
                (pinTerms config state ancestor finalizedState).depth /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat))) ∧
      (pinTerms config state ancestor finalizedState).slashedR *
          (2 * (pinTerms config state ancestor finalizedState).depthFin *
            (pinTerms config state ancestor finalizedState).flagRate) +
        (pinTerms config state ancestor finalizedState).slashedR *
          (pinTerms config state ancestor finalizedState).slashLeak +
        (pinTerms config state ancestor finalizedState).unitGain *
          (pinTerms config state ancestor finalizedState).slashedR ≤ W ∧
      ∀ A : Finset ValidatorIndex,
        ∑ v ∈ A.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
          = true), max (balanceAt state v.toNat +
            (pinTerms config state ancestor finalizedState).rise v.toNat)
              (balanceAt finalizedState v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ Wh := by
  -- The slashed charge is an increment and the leak of the dropped balance; the leak joins `W`.
  have charge : ∀ d p a b Q f : ℕ, f ≤ p → a ≤ b →
      2 * d * f + d * (2 * p + a / Q + 1) ≤ d * (2 * (2 * p) + b / Q + 1) :=
    fun d p a b Q f le ab => by
      have floor := Nat.div_le_div_right (c := Q) ab
      calc 2 * d * f + d * (2 * p + a / Q + 1) = d * (2 * f + (2 * p + a / Q + 1)) := by ring
        _ ≤ d * (2 * (2 * p) + b / Q + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨W, D, U, split, gain, unit, floorW⟩ : ∃ W D U : ℕ,
      (pinTerms config state ancestor finalizedState).branchR =
      3 * (W + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + D) *
          (pinTerms config state ancestor finalizedState).slashedR +
        U * (pinTerms config state ancestor finalizedState).slashedR +
        (pinTerms config state ancestor finalizedState).depth *
          (pinTerms config state ancestor finalizedState).proposerCredit +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1) *
          ((pinTerms config state ancestor finalizedState).depth * preset.SLOTS_PER_EPOCH.toNat +
            (pinTerms config state ancestor finalizedState).depth *
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat *
              (((getCurrentEpoch state).toNat + 1) /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
                (getCurrentEpoch finalizedState).toNat /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
                (pinTerms config state ancestor finalizedState).depth /
                  max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat))) ∧
      2 * (pinTerms config state ancestor finalizedState).depthFin *
          (pinTerms config state ancestor finalizedState).flagRate +
        (pinTerms config state ancestor finalizedState).slashLeak ≤ D ∧
      U = (pinTerms config state ancestor finalizedState).unitGain ∧
      ∀ A : Finset ValidatorIndex,
        ∑ v ∈ A.filter (fun v => (pinTerms config state ancestor finalizedState).slashedRB v.toNat
          = true), max (balanceAt state v.toNat +
            (pinTerms config state ancestor finalizedState).rise v.toNat)
              (balanceAt finalizedState v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ W := by
    refine ⟨_, _, _, rfl, ?_, rfl, fun A => ?_⟩
    · exact charge _ _ _ _ _ _ (flagRate_le _ _ _ _)
        (by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by norm_num))
    · -- The reward of a key is read at its position among the keys slashed on this branch.
      refine floor_aux (A := A) (fun i => max (balanceAt state i +
        (pinTerms config state ancestor finalizedState).rise i) (balanceAt finalizedState i))
        (fun i => (pinTerms config state ancestor finalizedState).slashedRB i) fun v _ flag => ?_
      refine ⟨Finset.mem_range.mpr (slashedRB_lt config state ancestor finalizedState flag), ?_⟩
      rw [Internal.slashedRB_eq] at flag
      exact of_decide_eq_true flag
  subst unit
  refine ⟨W, D * (pinTerms config state ancestor finalizedState).slashedR +
    (pinTerms config state ancestor finalizedState).unitGain *
      (pinTerms config state ancestor finalizedState).slashedR, by rw [split]; ring, ?_, floorW⟩
  have step : (pinTerms config state ancestor finalizedState).slashedR *
      (2 * (pinTerms config state ancestor finalizedState).depthFin *
          (pinTerms config state ancestor finalizedState).flagRate +
        (pinTerms config state ancestor finalizedState).slashLeak) ≤
      D * (pinTerms config state ancestor finalizedState).slashedR :=
    (Nat.mul_comm _ _).le.trans (Nat.mul_le_mul_right _ gain)
  rw [Nat.mul_add] at step
  omega

/-- The sync part of the proposer credit is at most the proposer credit. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncProposer_le_credit (config :
  Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).syncProposer ≤
      (pinTerms config state ancestor finalizedState).proposerCredit :=
  Nat.le_add_left _ _

/-- The keys of `SC` that the rise term of `bud_whistle_of` charges.

They are not slashed at R, `exitedSlashable` does not count them, and they are active at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sc3a (config : Config) (pulled anc fin
  counted split : BeaconState preset fork) :
    Finset ValidatorIndex :=
  (Internal.SC pulled counted split).filter fun v =>
    (¬ (pinTerms config pulled anc fin).slashedRB v.toNat = true ∧
      ¬ PinTerms.exitedSlashable anc pulled v.toNat = true) ∧
    isActiveAt counted (getCurrentEpoch counted) v.toNat = true

/-- The cap that the keys of `K6` beyond R's registry take from `creditCap`.

At a high gain rate each takes the largest cap. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.capUse (config : Config) (pulled anc
  fin counted : BeaconState preset fork) : ℕ :=
  if (pinTerms config pulled anc fin).gainHigh = true then
    ((Internal.K6 pulled counted).filter fun v => pulled.validators.data.size ≤ v.toNat).card *
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else 0


end Terms
end PinDrift
end EthLib.Consensus.Models.Network

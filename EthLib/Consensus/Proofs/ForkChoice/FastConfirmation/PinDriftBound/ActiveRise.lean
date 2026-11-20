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
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.Whistleblower

/-! The pin reserve: credit ceilings, headroom and the active keys' rise. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety PinKeys
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- A key with a flow credit of `cred` or a whistleblower credit has a gross credit on C's run.

Or a consolidation credits it. -/
private theorem credit_gate {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high : ℕ) (v : ValidatorIndex) {cred : ℕ}
    (source : cred = Internal.credC tail high v.toNat ∨ cred = Internal.propC tail high v.toNat)
    (positive : 0 < cred + Internal.whistC tail high v.toNat) :
    Internal.creditedKey tail high v = true ∨
      0 < (Internal.creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v.toNat high tail) := by
  have prop : Internal.propN tail high v.toNat ≤ Internal.grossScan v.toNat high tail :=
    Internal.scan_le_gross tail high v.toNat _ fun s h => .inl (by simpa using h)
  have whist : Internal.whistC tail high v.toNat ≤ Internal.grossScan v.toNat high tail :=
    Internal.scan_le_gross tail high v.toNat _ fun s h => .inr (.inl (by simpa using h))
  have cn := Internal.credN_split tail high v.toNat
  have cc := Internal.credC_split tail high v.toNat
  have pc := Internal.propC_split tail high v.toNat
  by_cases cons : 0 < (Internal.creditScan (fun s => decide (s = .consolidations))
      (fun s => decide (s = .consolidations)) v.toNat high tail)
  · exact .inr cons
  · left
    simp only [Internal.creditedKey, decide_eq_true_eq]
    rcases source with rfl | rfl <;> omega

/-- A block step gives no reward or slashing credit to a key that is not its proposer. -/
private theorem block_proposer_credit_zero {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) (v : ℕ)
    (notProposer : ∀ p, getBeaconProposerIndex s = .ok p → p.toNat ≠ v)
    (blockP slotP : BalanceSource → Bool)
    (sources : ∀ x, blockP x = true → x = .rewards ∨ x = .slashings) :
    Internal.stepCredit blockP slotP v (Step.block engine signed due ok) = 0 := by
  obtain ⟨events, replayed⟩ := (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩).balanceEvents_ok early
  obtain ⟨K, -, proposer, keys⟩ := Internal.block_gross_keys genesis apart shared fulu early
    replayed
  simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some]
  refine List.sum_eq_zero fun c member => ?_
  obtain ⟨e, inEvents, rfl⟩ := List.mem_map.mp member
  obtain ⟨inList, selected⟩ := List.mem_filter.mp inEvents
  by_contra positive
  rcases keys e inList v (Nat.pos_of_ne_zero positive) with inK | ⟨isSync, -⟩
  · obtain ⟨p, read, same⟩ := proposer v inK
    exact notProposer p read same
  · rcases sources _ selected with rewards | slashings <;> simp_all

/-- The proposer and whistleblower credits of a key that exited by the finalized state are 0.

The key is inactive on the whole run from that state, so it proposes no block.

Its slashings and rewards credit only the proposer. -/
private theorem exited_proposer_credits_zero
    (h : Setting config checks g split fin pulled anc counted V) {u : ForkedBeaconState preset}
    (run : Run config checks ⟨fork, fin⟩ u) (early : u.fork < .glamsterdam) (high i : ℕ)
    {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat) :
    Internal.propN run high i = 0 ∧ Internal.whistC run high i = 0 := by
  obtain ⟨toFin⟩ := h.toFin
  have zero : ∀ (blockP : BalanceSource → Bool),
      (∀ x, blockP x = true → x = .rewards ∨ x = .slashings) →
      (Internal.creditScan blockP (fun _ => false) i high run) = 0 := fun blockP sources =>
    Internal.creditScan_eq_zero_of_steps blockP _ i high run fun {m n} step member => by
      cases step with
      | slot ok => simp [Internal.stepCredit]
      | @block f s t engine signed due ok =>
        obtain ⟨pre, -, -, mEarly, -⟩ :=
          DirectSafety.Apriori.Internal.Run.contains_step_facts member early
        exact block_proposer_credit_zero h.genesis h.parameters.lookahead (toFin.append pre)
          (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)) mEarly i
          (fun p read => Internal.exited_not_proposer h foundPulled exited _ pre p mEarly read)
            blockP _
          sources
  exact ⟨zero _ fun x hx => .inl (by simpa using hx),
    zero _ fun x hx => .inr (by simpa using hx)⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The ceiling of the effective balance of a key that exited before the finalized state.

It is read at a state that C's branch slashes the key from.

Its credits on the run from the finalized state are sync and consolidation credits.

Deposits, proposer credits and whistleblower credits are 0 for such a key. -/
private theorem exited_credit_ceiling
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (w : Validator) (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    ∃ Cr, Cr ≤ Internal.syncCr eventsF i + Internal.consAmt eventsF i + Internal.syncCr eventsC i +
      Internal.consAmt eventsC i ∧
      (0 < Cr → 0 < Internal.syncCr eventsF i ∨ 0 < Internal.syncCr eventsC i ∨
        0 < Internal.consAmt eventsF i + Internal.consAmt eventsC i) ∧
      effectiveAt a i ≤
        max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
          ((actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
              ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨pre, post, cut, aEarly, aEpoch⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨u, foundFin, sameExit⟩ := Internal.exit_kept_of_le_fin h foundPulled (by omega)
  have exitedFin : u.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat := by
    rw [sameExit]; exact exited
  have sameFork : a.fork = fork :=
    Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  obtain ⟨af, as⟩ := a
  simp only at sameFork aEarly aEpoch
  subst sameFork
  have epochA : (getCurrentEpoch as).toNat ≤ highC + 1 := by omega
  -- the replays of the shared segment, and of the run from the finalized state to `a`
  obtain ⟨eF, replayedF'⟩ := fromFin.balanceEvents_ok h.early highC
  obtain ⟨eP, replayedP⟩ := pre.balanceEvents_ok aEarly highC
  have sameF : eF = eventsF := by
    have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
    have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    simp only at splitC calledNat
    have same := balanceEvents_eq_of_endpoint_le fromFin (high := highC) (localHigh := high)
      (by simp only; omega) (by simp only; omega)
    rw [same, replayedF] at replayedF'
    exact (Except.ok.inj replayedF').symm
  subst sameF
  have wholeR := balanceEvents_append fromFin pre highC replayedF' replayedP
  have cred := Internal.credits_le_sources shared h.genesis (fromFin.append pre) aEarly electra i
    highC
    wholeR
  -- the key has no proposer, whistleblower or deposit credit on the run
  obtain ⟨propZero, whistZero⟩ := exited_proposer_credits_zero h (fromFin.append pre) aEarly highC
    i foundPulled (by omega)
  have insideFin : i < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp foundFin).1
  have inA : i < as.validators.data.size :=
    Nat.lt_of_lt_of_le insideFin (registryGrows_of_chainSteps (fromFin.append pre).chainSteps)
  obtain ⟨vA, foundA⟩ : ∃ vA, as.validators.data[i]? = some vA :=
    ⟨_, Array.getElem?_eq_getElem inA⟩
  obtain ⟨vB, foundB⟩ : ∃ vB, b.state.validators.data[i]? = some vB := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at flag
    | some vB => exact ⟨vB, rfl⟩
  obtain ⟨flagA, flagB⟩ := Bool.and_eq_true_iff.mp flag
  have cleanA : vA.slashed = false := by simpa [foundA] using flagA
  have slashedB : vB.slashed = true := by simpa [foundB] using flagB
  have unset : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  have kept := Internal.kept_run shared h.genesis h.fulu (fromFin.append pre) aEarly
  obtain ⟨vA', foundA', -⟩ := kept.life.validators i u foundFin
  obtain rfl := Option.some.inj (foundA'.symm.trans foundA)
  have constant : vA'.withdrawableEpoch = u.withdrawableEpoch :=
    (kept.withdrawable i u vA' foundFin foundA unset).2.resolve_left (by simp [cleanA])
  have lateA : (getCurrentEpoch as).toNat < vA'.withdrawableEpoch.toNat :=
    Internal.newly_slashed_unwithdrawable h.genesis h.caps (shared.append (fromFin.append pre))
      step (Nat.lt_of_le_of_lt
        (fork_le_of_chainSteps post.chainSteps) h.early) foundA foundB cleanA slashedB
  have exitLt := Internal.exitEpoch_toNat_lt_of_ne_far unset
  have deposits := Internal.Run.exiting_deposit_credit_zero shared h.genesis (fromFin.append pre)
    h.fulu aEarly highC wholeR i u foundFin exitLt (by rw [← constant]; exact lateA)
  have index : i.toUInt64.toNat = i := toNat_toUInt64_of_lt
    (BeaconState.registryWithinLimit_of_lt h.early fin) insideFin
  have depScan : (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC
      (fromFin.append pre)) = 0 := by
    have := Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits)) (· =
      .deposits)
      (by intro s; simp) (fromFin.append pre) highC i.toUInt64 wholeR
    rw [index] at this
    omega
  have consScan : (Internal.creditScan (fun s => decide (s = .consolidations))
      (fun s => decide (s = .consolidations)) i highC (fromFin.append pre)) ≤
        Internal.consAmt (eF ++ eP) i := by
    have := Internal.scan_le_events (fun s => decide (s = .consolidations))
      (fun s => decide (s = .consolidations))
      (· = .consolidations) (by intro s; simp) (fromFin.append pre) highC i.toUInt64 wholeR
    rw [index] at this
    exact this
  obtain ⟨gross, netLe, -⟩ := cred
  have hN := Internal.credN_split (fromFin.append pre) highC i
  have hC := Internal.credC_split (fromFin.append pre) highC i
  have ceiling := Internal.exited_ceiling h (fromFin.append pre) highC epochA i foundFin exitedFin
    (Internal.consAmt (eF ++ eP) i + Internal.syncCr (eF ++ eP) i) (by
      unfold Internal.syncCr
      omega)
  -- the prefix of C's replay that the run to `a` reads
  rw [cut] at replayedC
  obtain ⟨before, replayedB, prefixB⟩ := Run.balanceEvents_prefix (pre.snoc step) post highC eventsC
    replayedC
  obtain ⟨eP', replayedP', prefixP⟩ := Run.balanceEvents_prefix pre (Run.nil.snoc step) highC before
    replayedB
  rw [replayedP] at replayedP'
  obtain rfl := Except.ok.inj replayedP'
  obtain ⟨rest, restEq⟩ := prefixP.trans prefixB
  have sums : Internal.syncCr eventsC i = Internal.syncCr eP i + Internal.syncCr rest i ∧
      Internal.consAmt eventsC i = Internal.consAmt eP i + Internal.consAmt rest i := by
    subst restEq
    unfold Internal.syncCr Internal.consAmt
    simp only [List.map_append, List.sum_append, List.filter_append, and_self]
  have splitR : Internal.syncCr (eF ++ eP) i = Internal.syncCr eF i + Internal.syncCr eP i ∧
      Internal.consAmt (eF ++ eP) i = Internal.consAmt eF i + Internal.consAmt eP i := by
    unfold Internal.syncCr Internal.consAmt
    simp only [List.map_append, List.sum_append, List.filter_append, and_self]
  refine ⟨_, by omega, fun positive => by omega, ceiling⟩

/-- The early-exit test includes keys whose exit at R is due by the finalized epoch. -/
private theorem exitBeforeFin_of_exit (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat) :
    (pinTerms config pulled anc fin).exitBeforeFin i = true := by
  simp only [pinTerms]
  simp [foundPulled, exited]

/-- An early exit uses the effective or rounded balance at the finalized state. -/
private theorem bF_of_exit (config : Config) (pulled anc fin : BeaconState preset fork) (i : ℕ)
    (exit : (pinTerms config pulled anc fin).exitBeforeFin i = true) :
    (pinTerms config pulled anc fin).bF i =
      max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  simp only [pinTerms] at exit ⊢
  simp only [exit, ↓reduceIte]
  rfl

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of the split's registry that exited before the finalized state is bounded by `whistleEnv`.

Keys slashed on R's branch instead use the bound from the finalized state.

Its balance at a state of C's branch is its finalized balance and its credits since.

Those credits are sync and consolidation credits, which the slack holds with one rounding band. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.registry_exited
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (inside : i < split.validators.data.size)
    (exited : ∀ w, pulled.validators.data[i]? = some w →
      w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true)
    (slashed : ¬ (pinTerms config pulled anc fin).slashedRB i = true) :
    effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin i := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨w, foundPulled⟩ : ∃ w, pulled.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside
      (registryGrows_of_chainSteps toPulled.chainSteps))⟩
  have exitedW := exited w foundPulled
  have exit := exitBeforeFin_of_exit config pulled anc fin i foundPulled (by omega)
  obtain ⟨Cr, credits, positive, ceiling⟩ := exited_credit_ceiling h fromFin high endEpoch
    replayedF tailC highC endEpochC replayedC step member i w foundPulled exitedW flag
  have bF := bF_of_exit config pulled anc fin i exit
  have incPos := h.bands.1
  have up := h.bands.2
  -- the rounding of the credits up to whole increments costs less than one band
  have roundLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        Cr + (if 0 < Cr then preset.upwardBand else 0) := by
    by_cases zero : Cr = 0
    · subst zero
      simp [Nat.div_eq_of_lt (show preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 <
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat by omega)]
    · have := Nat.mul_div_le (Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      simp only [Nat.pos_of_ne_zero zero, ↓reduceIte]
      omega
  -- a credited key has a band: its sync credit on either segment, or a due consolidation entry
  have band : 0 < Cr → preset.upwardBand ≤ Internal.bandC tailC highC i + Internal.bandX fin highC i
    +
      (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) := by
    intro credited
    rcases positive credited with sharedSync | sync | cons
    · simp only [sharedSync, ↓reduceIte]
      omega
    · have gross := Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early tailC highC
        replayedC i sync
      unfold Internal.bandC
      split_ifs <;> omega
    · have index : i.toUInt64.toNat = i := toNat_toUInt64_of_lt
        (BeaconState.registryWithinLimit_of_lt h.early pulled)
        (Array.getElem?_eq_some_iff.mp foundPulled).1
      have replayedF' := Internal.replay_at_pulled pulled fromFin high endEpoch
          (Internal.Setting.called h)
        replayedF
      have due : 0 < Internal.dueAt fin highC {i.toUInt64} := by
        refine Nat.pos_of_ne_zero fun none => ?_
        have zero := Internal.consAmt_zero h fromFin replayedF' tailC highC endEpochC h.near
          replayedC
          i.toUInt64 none
        rw [index] at zero
        omega
      unfold Internal.bandX
      have ge := Nat.le_mul_of_pos_right preset.upwardBand due
      rw [Nat.toUInt64_eq] at due
      simp only [Nat.toUInt64_eq] at ge ⊢
      omega
  have main : effectiveAt a i ≤ (pinTerms config pulled anc fin).bF i +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    omega
  have pay : preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 +
      (11 * (Internal.syncCr eventsC i + Internal.consAmt eventsC i) + 9) / 10 + Internal.bandC
        tailC highC i +
      Internal.bandX fin highC i + (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0)
        := by
    split_ifs at roundLe band ⊢ <;> omega
  clear ceiling roundLe band positive credits bF
  unfold Internal.whistleEnv Internal.whistleSlack Internal.whistleSlackBase
  simp only [slashed, exit, ↓reduceIte, Bool.false_eq_true]
  split_ifs at pay ⊢ <;> omega

/-- A key with a flow credit is credited.

Or a consolidation of X, a seat debit or R's slashing takes it. -/
private theorem unit_gate (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (events eventsF : List (BalanceEvent preset)) (v : ValidatorIndex) {cred : ℕ}
    (source : cred = Internal.credC tailC highC v.toNat ∨ cred = Internal.propC tailC highC v.toNat)
    (positive : 0 < Internal.flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events
      eventsF
      v.toNat cred) :
    Internal.creditedKey tailC highC v = true ∨ 0 < Internal.consAmt eventsC v.toNat ∨
      0 < Internal.syncD eventsF v.toNat ∨ 0 < Internal.syncD events v.toNat ∨
      (pinTerms config pulled anc fin).slashedRB v.toNat = true := by
  unfold Internal.flowCredit at positive
  by_cases credit : 0 < cred + Internal.whistC tailC highC v.toNat
  · rcases credit_gate tailC highC v source credit with credited | consolidated
    · exact .inl credited
    · exact .inr (.inl (Nat.lt_of_lt_of_le consolidated
        (Internal.scan_le_events _ _ (· = .consolidations) (by intro s; simp) tailC highC v
          replayedC)))
  by_cases seat : 0 < Internal.syncCr eventsC v.toNat
  · left
    have := Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early tailC highC replayedC
      v.toNat seat
    simp only [Internal.creditedKey, decide_eq_true_eq]
    omega
  by_cases debitF : 0 < Internal.syncD eventsF v.toNat
  · exact .inr (.inr (.inl debitF))
  by_cases debitR : 0 < Internal.syncD events v.toNat
  · exact .inr (.inr (.inr (.inl debitR)))
  right; right; right; right
  have slash : 0 < Internal.slashW (pinTerms config pulled anc fin) v.toNat := by omega
  by_contra not
  simp [Internal.slashW, not] at slash

/-- The units of a set of keys are the unit for each key with a flow credit. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_unitK (t : PinTerms preset) {x
  y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ) (eventsC events eventsF : List (BalanceEvent preset))
    (S : Finset ValidatorIndex) (cred : ValidatorIndex → ℕ) :
    ∑ v ∈ S, Internal.unitK t tailC high eventsC events eventsF v.toNat (cred v) =
      t.unitGain * (S.filter fun v =>
        0 < Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cred v)).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Internal.unitK
  split <;> simp_all

/-- The reserve covers the rounding units of the counted keys at their respective weights.

A credited key uses one rounding unit, and a key with only seat activity uses a seat unit.

A key credited only by consolidation uses a unit for an entry in X's consolidation queue.

A key slashed only on R's branch uses a unit from that branch's slashing budget.

The keys of `SC` and `CS` hold the slots that the keys of `K4`, `K5` and `K6` leave.

The keys of `SC` alone fit the slots and the extra units at weight one. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_units (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ((∑ v ∈ (Internal.K4 pulled counted V),
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)
          +
      3 * (∑ v ∈ (Internal.K5 counted V),
          Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
            (Internal.propC tailC highC v.toNat)) +
      (∑ v ∈ (Internal.K6 pulled counted),
          Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat) +
      (∑ v ∈ Internal.SC pulled counted split,
          Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat) +
      (∑ v ∈ Internal.CS counted split,
          Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat) ≤
      (pinTerms config pulled anc fin).creditUnits +
        3 * (pinTerms config pulled anc fin).unitGain *
          (pinTerms config pulled anc fin).consolidationsXCount +
        3 * ((pinTerms config pulled anc fin).unitGain *
          (pinTerms config pulled anc fin).slashedR)) ∧
      ∑ v ∈ Internal.SC pulled counted split,
          Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
            ≤
        (pinTerms config pulled anc fin).creditUnits +
          (pinTerms config pulled anc fin).unitGain *
            ((pinTerms config pulled anc fin).consolidationsXCount +
              (pinTerms config pulled anc fin).slashedR) := by
  classical
  obtain ⟨N, units, slots⟩ := Internal.creditUnits_eq config pulled anc fin
  obtain ⟨d45, d46, d56, -⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  obtain ⟨dCS, -⟩ := Internal.cs_disjoint h
  have credited := Internal.credited_classes_le h tailC highC
  have five := Internal.card_K5_le h tailC
  -- The consolidation counts read the pulled epoch as their horizon.
  obtain ⟨eventsF', replayedF'⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  have replayedC' : tailC.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsC :=
    (DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le tailC
      (high := (getCurrentEpoch pulled).toNat) (localHigh := highC) h.near endEpochC).trans
      replayedC
  set G4 := (Internal.K4 pulled counted V).filter fun v => 0 < Internal.flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (Internal.credC tailC highC v.toNat)
  set G5 := (Internal.K5 counted V).filter fun v => 0 < Internal.flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (Internal.propC tailC highC v.toNat)
  set G6 := (Internal.K6 pulled counted).filter fun v => 0 < Internal.flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (Internal.credC tailC highC v.toNat)
  set Gsc := (Internal.SC pulled counted split).filter fun v => 0 < Internal.flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (Internal.credC tailC highC v.toNat)
  set Gcs := (Internal.CS counted split).filter fun v => 0 < Internal.flowCredit
    (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
    (Internal.credC tailC highC v.toNat)
  have s4 : ∑ v ∈ Internal.K4 pulled counted V,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * G4.card :=
    Internal.sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC
        v.toNat
  have s5 : ∑ v ∈ Internal.K5 counted V,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        (Internal.propC tailC highC v.toNat) =
        (pinTerms config pulled anc fin).unitGain * G5.card :=
    Internal.sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.propC tailC highC
        v.toNat
  have s6 : ∑ v ∈ Internal.K6 pulled counted,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * G6.card :=
    Internal.sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC
        v.toNat
  have ssc : ∑ v ∈ Internal.SC pulled counted split,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * Gsc.card :=
    Internal.sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC
        v.toNat
  have scs : ∑ v ∈ Internal.CS counted split,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * Gcs.card :=
    Internal.sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC
        v.toNat
  set All := Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted ∪
    Internal.SC pulled counted split ∪
    Internal.CS counted split
  set Co := All.filter fun v => 0 < Internal.consAmt eventsC v.toNat
  set A := All.filter fun v => 0 < Internal.syncD eventsF v.toNat
  set B := All.filter fun v => 0 < Internal.syncD events v.toNat
  set Sl := All.filter fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true
  set Cr4 := (Internal.K4 pulled counted V).filter fun v => Internal.creditedKey tailC highC v =
    true
  set Cr5 := (Internal.K5 counted V).filter fun v => Internal.creditedKey tailC highC v = true
  set Cr6 := (Internal.K6 pulled counted).filter fun v => Internal.creditedKey tailC highC v = true
  set Crsc := (Internal.SC pulled counted split).filter fun v => Internal.creditedKey tailC highC v
    = true
  set Crcs := (Internal.CS counted split).filter fun v => Internal.creditedKey tailC highC v = true
  -- A key with a unit is credited, or a consolidation, a seat debit or a slashing takes it.
  have route : ∀ (v : ValidatorIndex) (cred : ℕ), v ∈ All →
      (cred = Internal.credC tailC highC v.toNat ∨ cred = Internal.propC tailC highC v.toNat) →
      0 < Internal.flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
        v.toNat cred →
      Internal.creditedKey tailC highC v = true ∨ v ∈ Co ∪ (A ∪ B) ∪ Sl := by
    intro v cred inAll source positive
    rcases unit_gate h tailC highC replayedC events eventsF v source positive with
      credit | consolidated | debitF | debitR | slashed
    · exact .inl credit
    · exact .inr (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨inAll, consolidated⟩)))
    · exact .inr (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inAll, debitF⟩))))
    · exact .inr (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨inAll, debitR⟩))))
    · exact .inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨inAll, slashed⟩))
  have inAll : ∀ v, v ∈ Internal.K4 pulled counted V ∨ v ∈ Internal.K5 counted V ∨ v ∈ Internal.K6
    pulled counted ∨
      v ∈ Internal.SC pulled counted split ∨ v ∈ Internal.CS counted split → v ∈ All := fun v member
        => by
    simp only [All, Finset.mem_union]
    tauto
  have cover : G4 ∪ G5 ∪ G6 ∪ Gsc ∪ Gcs ⊆
      (Cr4 ∪ Cr5 ∪ Cr6 ∪ Crsc ∪ Crcs) ∪ (Co ∪ (A ∪ B) ∪ Sl) := by
    intro v member
    simp only [G4, G5, G6, Gsc, Gcs, Cr4, Cr5, Cr6, Crsc, Crcs, Finset.mem_union,
      Finset.mem_filter] at member ⊢
    rcases member with (((⟨i4, p4⟩ | ⟨i5, p5⟩) | ⟨i6, p6⟩) | ⟨isc, psc⟩) | ⟨ics, pcs⟩
    · rcases route v _ (inAll v (.inl i4)) (.inl rfl) p4 with c | r
      · exact .inl (.inl (.inl (.inl (.inl ⟨i4, c⟩))))
      · simp only [Finset.mem_union] at r
        exact .inr r
    · rcases route v _ (inAll v (.inr (.inl i5))) (.inr rfl) p5 with c | r
      · exact .inl (.inl (.inl (.inl (.inr ⟨i5, c⟩))))
      · simp only [Finset.mem_union] at r
        exact .inr r
    · rcases route v _ (inAll v (.inr (.inr (.inl i6)))) (.inl rfl) p6 with c | r
      · exact .inl (.inl (.inl (.inr ⟨i6, c⟩)))
      · simp only [Finset.mem_union] at r
        exact .inr r
    · rcases route v _ (inAll v (.inr (.inr (.inr (.inl isc))))) (.inl rfl) psc with c | r
      · exact .inl (.inl (.inr ⟨isc, c⟩))
      · simp only [Finset.mem_union] at r
        exact .inr r
    · rcases route v _ (inAll v (.inr (.inr (.inr (.inr ics))))) (.inl rfl) pcs with c | r
      · exact .inl (.inr ⟨ics, c⟩)
      · simp only [Finset.mem_union] at r
        exact .inr r
  have apart45 : Disjoint G4 G5 := Finset.disjoint_left.mpr fun v a b =>
    Finset.disjoint_left.mp d45 (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
  have apart456 : Disjoint (G4 ∪ G5) G6 := Finset.disjoint_left.mpr fun v a b => by
    rcases Finset.mem_union.mp a with a | a
    · exact Finset.disjoint_left.mp d46 (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
    · exact Finset.disjoint_left.mp d56 (Finset.mem_filter.mp a).1 (Finset.mem_filter.mp b).1
  have inK3 : ∀ v, v ∈ G4 ∪ G5 ∪ G6 → v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
    Internal.K6 pulled counted :=
    fun v hv => by
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mp hv).1)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mp hv).1
  have apartSC : Disjoint (G4 ∪ G5 ∪ G6) Gsc := Finset.disjoint_left.mpr fun v a b =>
    Finset.disjoint_left.mp dSC (inK3 v a) (Finset.mem_filter.mp b).1
  have apartCS : Disjoint (G4 ∪ G5 ∪ G6 ∪ Gsc) Gcs := Finset.disjoint_left.mpr fun v a b => by
    rcases Finset.mem_union.mp a with a | a
    · exact Finset.disjoint_left.mp dCS (Finset.mem_union_left _ (inK3 v a))
        (Finset.mem_filter.mp b).1
    · exact Finset.disjoint_left.mp dCS (Finset.mem_union_right _ (Finset.mem_filter.mp a).1)
        (Finset.mem_filter.mp b).1
  have total := Finset.card_le_card cover
  rw [Finset.card_union_of_disjoint apartCS, Finset.card_union_of_disjoint apartSC,
    Finset.card_union_of_disjoint apart456, Finset.card_union_of_disjoint apart45] at total
  have union1 := Finset.card_union_le (Cr4 ∪ Cr5 ∪ Cr6 ∪ Crsc ∪ Crcs) (Co ∪ (A ∪ B) ∪ Sl)
  have union2 := Finset.card_union_le (Cr4 ∪ Cr5 ∪ Cr6 ∪ Crsc) Crcs
  have union3 := Finset.card_union_le (Cr4 ∪ Cr5 ∪ Cr6) Crsc
  have union4 := Finset.card_union_le (Cr4 ∪ Cr5) Cr6
  have union5 := Finset.card_union_le Cr4 Cr5
  have union6 := Finset.card_union_le (Co ∪ (A ∪ B)) Sl
  have union7 := Finset.card_union_le Co (A ∪ B)
  -- The counts of the credited keys, the consolidations, the seat debits and the slashings.
  have consolidations := Internal.cons_keys_le h fromFin tailC (getCurrentEpoch pulled).toNat h.near
    (Nat.le_refl _) replayedF' replayedC' Co fun v hv => (Finset.mem_filter.mp hv).2
  have seats := Internal.debit_keys_le h fromFin tail tailC high replayed replayedF A B
    (fun v hv => (Finset.mem_filter.mp hv).2) fun v hv => (Finset.mem_filter.mp hv).2
  have slashed : Sl.card ≤ (pinTerms config pulled anc fin).slashedR :=
    Internal.slashedRB_card_le config pulled anc fin All
  have inFive : G5.card ≤ (Internal.K5 counted V).card := Finset.card_le_card (Finset.filter_subset
    _ _)
  have key : G4.card + G6.card + 3 * G5.card + Gsc.card + Gcs.card ≤ N +
      2 * ((((pinTerms config pulled anc fin).positions.filter fun i =>
        (pinTerms config pulled anc fin).exitingB i = true).card +
          (pinTerms config pulled anc fin).queueKeys)) +
      3 * (pinTerms config pulled anc fin).consolidationsXCount +
      3 * (pinTerms config pulled anc fin).slashedR := by
    omega
  -- The keys of `SC` alone take one slot each, and the other classes' slots are not weighed.
  have keySC : Gsc.card ≤ N + (pinTerms config pulled anc fin).consolidationsXCount +
      (pinTerms config pulled anc fin).slashedR := by
    omega
  refine ⟨?_, ?_⟩
  swap
  · rw [ssc, units]
    calc (pinTerms config pulled anc fin).unitGain * Gsc.card
        ≤ (pinTerms config pulled anc fin).unitGain * (N +
            (pinTerms config pulled anc fin).consolidationsXCount +
            (pinTerms config pulled anc fin).slashedR) := Nat.mul_le_mul_left _ keySC
      _ = (pinTerms config pulled anc fin).unitGain * N +
          (pinTerms config pulled anc fin).unitGain *
            ((pinTerms config pulled anc fin).consolidationsXCount +
              (pinTerms config pulled anc fin).slashedR) := by ring
      _ ≤ _ := by
        rw [Nat.add_mul, Nat.mul_comm (pinTerms config pulled anc fin).unitGain N]
        exact Nat.add_le_add (Nat.le_add_right _ _) (Nat.le_refl _)
  rw [s4, s5, s6, ssc, scs, units]
  calc (pinTerms config pulled anc fin).unitGain * G4.card +
        3 * ((pinTerms config pulled anc fin).unitGain * G5.card) +
        (pinTerms config pulled anc fin).unitGain * G6.card +
        (pinTerms config pulled anc fin).unitGain * Gsc.card +
        (pinTerms config pulled anc fin).unitGain * Gcs.card
      = (pinTerms config pulled anc fin).unitGain *
          (G4.card + G6.card + 3 * G5.card + Gsc.card + Gcs.card) := by ring
    _ ≤ (pinTerms config pulled anc fin).unitGain * (N +
        2 * ((((pinTerms config pulled anc fin).positions.filter fun i =>
          (pinTerms config pulled anc fin).exitingB i = true).card +
            (pinTerms config pulled anc fin).queueKeys)) +
        3 * (pinTerms config pulled anc fin).consolidationsXCount +
        3 * (pinTerms config pulled anc fin).slashedR) := Nat.mul_le_mul_left _ key
    _ = _ := by ring

/-- The arithmetic of the sync leak: the debited increments `A` of all keys fit `D` at `inc` each.

Three increments of a key fit two of the window's, since `D / (inc - 1)` bounds them.

The floors of the keys add up to at most the floor of their sum. -/
private theorem leak_arith (dF P X Q D inc A F S R SL Sig : ℕ) (hinc : 1 < inc)
    (debits : inc * A ≤ D) (floors : F ≤ inc * A * X / Q) (count : S ≤ R)
    (keys : Sig ≤ dF * (3 * P * A + F) + S * SL) :
    3 * Sig ≤ 3 * dF * (2 * P * (2 * D / (inc - 1) + 1) + 2 * D * X / Q + 1) + 3 * (R * SL) := by
  have within : A ≤ D / (inc - 1) := (Nat.le_div_iff_mul_le (by omega)).mpr
    (le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (by rw [Nat.mul_comm]; exact debits))
  have double := Nat.mul_div_le_mul_div_assoc 2 D (inc - 1)
  have three : 3 * P * A ≤ 2 * P * (2 * D / (inc - 1) + 1) :=
    calc 3 * P * A = P * (3 * A) := by ring
      _ ≤ P * (2 * (2 * D / (inc - 1) + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have rounded : F ≤ 2 * D * X / Q := floors.trans (Nat.div_le_div_right (by
    calc inc * A * X ≤ D * X := Nat.mul_le_mul_right _ debits
      _ ≤ 2 * D * X := Nat.mul_le_mul_right _ (by omega)))
  have := Nat.mul_le_mul_left dF (Nat.add_le_add_right (Nat.add_le_add three rounded) 1)
  have := Nat.mul_le_mul_right SL count
  nlinarith

/-- A key's penalty on R's branch is at most one increment, and only a slashed key has one. -/
private theorem slashW_le (h : Setting config checks g split fin pulled anc counted V) (i : ℕ) :
    Internal.slashW (pinTerms config pulled anc fin) i ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (if (pinTerms config pulled anc fin).slashedRB i = true then 1 else 0) := by
  unfold Internal.slashW
  split_ifs
  · rw [Nat.mul_one]
    exact (Nat.le_add_right _ _).trans h.facts.slashBand
  · exact Nat.zero_le _

/-- The leak induced by the sync debits of any keys fits `syncLeak` and the slashed keys' leak.

A key withdrawn by R's horizon induces no leak.

A key's induced leak is that of its debited increments and of its penalty's increment.

The keys that R slashed after the finalized epoch are at most `slashedR`. -/
private theorem syncLeak_of_envelope (h : Setting config checks g split fin pulled anc counted V)
    (perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (W : Finset ValidatorIndex)
    (envelope : ∀ v ∈ W, (∀ w, pulled.validators.data[v.toNat]? = some w →
        (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) →
      ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
              Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :
    3 * ∑ v ∈ W, Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat ≤
      (pinTerms config pulled anc fin).syncLeak +
        3 * ((pinTerms config pulled anc fin).slashedR *
          (pinTerms config pulled anc fin).slashLeak) := by
  classical
  have incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  -- the abbreviations of the pin's terms
  obtain ⟨a, ha⟩ : ∃ a : ValidatorIndex → ℕ, ∀ v, a v = (Internal.syncD eventsF v.toNat +
    Internal.syncD events v.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ValidatorIndex → ℕ, ∀ v, s v =
    if (pinTerms config pulled anc fin).slashedRB v.toNat = true then 1 else 0 := ⟨_, fun _ => rfl⟩
  have total := Finset.sum_le_sum fun v (member : v ∈ W) => by
    by_cases late : ∀ w, pulled.validators.data[v.toNat]? = some w →
        (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat
    · refine Internal.inducedR_le config pulled anc fin incPos perPos _ v.toNat (a v) (s v)
        (by rw [hs]; split_ifs <;> omega) fun z inPath =>
          (envelope v member late z inPath).trans ?_
      refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
      have within := slashW_le h v.toNat
      rw [← hs] at within
      calc _ ≤ (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat * s v) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
            Nat.div_le_div_right (Nat.add_le_add_left within _)
        _ = a v + s v := by
            rw [Nat.add_mul_div_left _ _ incPos, ha]
    · obtain ⟨w, found, notLate⟩ : ∃ w, pulled.validators.data[v.toNat]? = some w ∧
          w.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
        by_contra none
        exact late fun w found => by
          by_contra notLate
          exact none ⟨w, found, by omega⟩
      rw [Internal.inducedR_of_withdrawn _ _ _ (Internal.withdrawnRB_of_le config pulled anc fin
          found
        notLate)]
      exact Nat.zero_le _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at total
  have appended := DirectSafety.Apriori.Internal.balanceEvents_append fromFin tail _ replayedF
    replayed
  have epochs : (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch fin).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
  have hA := (show preset.EFFECTIVE_BALANCE_INCREMENT.toNat * ∑ v ∈ W, a v ≤
      ∑ v ∈ W, ((eventsF ++ events).map (Internal.syncDebit v.toNat)).sum by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [ha, List.map_append, List.sum_append]
    exact Nat.mul_div_le _ _).trans
    ((Internal.syncDebits_window_le h (fromFin.append tail) (Nat.le_succ _) appended W).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ epochs))))
  have hS : ∑ v ∈ W, s v ≤ (pinTerms config pulled anc fin).slashedR := by
    refine Nat.le_of_mul_le_mul_left (le_trans (le_of_eq ?_)
      (Internal.slashR_le config pulled anc fin W)) incPos
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by unfold Internal.slashR; rw [hs]; split_ifs <;> simp
  have floors := (DirectSafety.Apriori.Internal.sum_div_le W
    (fun v => preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a v *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat))
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)).trans
    (Nat.div_le_div_right (le_of_eq (by rw [← Finset.sum_mul, ← Finset.mul_sum])))
  have hc : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  exact leak_arith _ _ _ _ _ _ _ _ _ _ _ _ hc hA floors hS total

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A counted key's balance at C is at most its balance at R plus its rise and its flows.

It adds the rise of the key and the credits, flows and slacks that `rise` does not read.

The slacks are one increment for a slashing on R's branch.

They are one rounding step for a credit on C's branch.

They are one rounding step for a sync debit on R's branch or on its shared segment with C's.

The bound also includes compounding flows, one rounding unit and the induced leak.

The starting balance floor accounts for rounding down to an increment. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.keyCeiling (anc : BeaconState preset
  fork)
    (run : Run config checks ⟨fork, fin⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ) : Prop :=
  balanceAt counted i ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
    (Internal.credC tailC highC i +
      Internal.keyExtra (pinTerms config pulled anc fin) run tailC highC eventsC events eventsF i) +
    Internal.whistC tailC highC i + (Internal.syncF events i + Internal.syncF eventsC i) +
    Internal.slashR (pinTerms config pulled anc fin) i + Internal.bandC tailC highC i +
    Internal.bandR (eventsF ++ events) i + Internal.bandX fin highC i

/-- The gain of the flows `Z0` and a penalty `W` is within a tenth of `Z0`, rounded up, and a unit.

The gain of the flows alone is within a tenth of them, by `key`.

A penalty below an increment adds at most one increment to the floor of the flows' gain.

That increment gains at most one unit. -/
private theorem flow_gain_slack {I WD F P D Z0 W U : ℕ} (hI : 0 < I)
    (key : 11 * D * (P * F) < WD * I) (hW : 11 * W < 10 * I)
    (unit : D * (P * F / WD + 2) ≤ U) :
    D * (11 * (Z0 + W) / (10 * I) * P * F / WD) ≤ (Z0 + 9) / 10 + (if 0 < W then U else 0) := by
  have hWD : 0 < WD := by
    rcases Nat.eq_zero_or_pos WD with z | p
    · subst z
      simp at key
    · exact p
  have base : ∀ Z : ℕ, 10 * (D * (11 * Z / (10 * I) * P * F / WD)) ≤ Z := by
    intro Z
    obtain ⟨x, hx⟩ : ∃ x, x = 11 * Z / (10 * I) := ⟨_, rfl⟩
    rw [← hx]
    obtain ⟨q, hq⟩ : ∃ q, q = x * P * F / WD := ⟨_, rfl⟩
    rw [← hq]
    have h1 : WD * q ≤ x * P * F := by
      rw [hq]
      exact Nat.mul_div_le _ _
    have h2 : x * (10 * I) ≤ 11 * Z := by
      rw [hx]
      exact Nat.div_mul_le_self _ _
    have h3 : 11 * D * (P * F) + 1 ≤ WD * I := key
    have h4 : 11 * (D * q * WD) ≤ 11 * (D * (x * P * F)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have h5 : 11 * (D * (x * P * F)) * 10 ≤ WD * (x * (10 * I)) := by nlinarith
    have h6 : 11 * (10 * (D * q)) * WD ≤ 11 * Z * WD := by nlinarith
    exact Nat.le_of_mul_le_mul_right
      (Nat.le_of_mul_le_mul_left (by nlinarith) (by norm_num : 0 < 11)) hWD
  have g0 := base Z0
  by_cases w : 0 < W
  · simp only [w, ↓reduceIte]
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 = 11 * Z0 / (10 * I) := ⟨_, rfl⟩
    have hx : 11 * (Z0 + W) / (10 * I) ≤ x0 + 1 := by
      have : 11 * (Z0 + W) ≤ 11 * Z0 + 10 * I := by omega
      calc 11 * (Z0 + W) / (10 * I) ≤ (11 * Z0 + 10 * I) / (10 * I) :=
            Nat.div_le_div_right this
        _ = x0 + 1 := by rw [hx0, Nat.add_div_right _ (by omega)]
    have step : 11 * (Z0 + W) / (10 * I) * P * F / WD ≤ x0 * P * F / WD + P * F / WD + 1 := by
      calc 11 * (Z0 + W) / (10 * I) * P * F / WD ≤ (x0 + 1) * P * F / WD :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hx))
        _ = (x0 * P * F + P * F) / WD := by
            congr 1
            ring
        _ ≤ x0 * P * F / WD + P * F / WD + 1 := Nat.add_div_le_div_add_div_add_one _ _ _
    have g1 : D * (11 * (Z0 + W) / (10 * I) * P * F / WD) ≤
        D * (x0 * P * F / WD) + D * (P * F / WD + 2) := by
      calc D * (11 * (Z0 + W) / (10 * I) * P * F / WD)
          ≤ D * (x0 * P * F / WD + P * F / WD + 1) := Nat.mul_le_mul_left _ step
        _ ≤ D * (x0 * P * F / WD) + D * (P * F / WD + 2) := by
            rw [← Nat.mul_add]
            exact Nat.mul_le_mul_left _ (by omega)
    rw [← hx0] at g0
    omega
  · simp only [w, ↓reduceIte]
    have : W = 0 := by omega
    subst this
    simp only [Nat.add_zero]
    omega

/-- The explicit closing of a key at its slashing state is within `whistleEnv` and `whistleSlack`.

`pre` is C's run up to the state before the slashing, and `tailC` is the whole run.

The slashing's increment is `whistleEnv`'s when R's branch slashes the key.

`Cr` and the sync debits are credits of the slack.

The flows' gain is within a tenth of them, rounded up, with a unit for the penalty of R's slashing.

The key's bands and unit of the prefix are within those of the whole run. -/
private theorem whistle_of_close (h : Setting config checks g split fin pulled anc counted V)
    (t : PinTerms preset) (ht : t = pinTerms config pulled anc fin)
    {x y x' y' r r' : ForkedBeaconState preset}
    (pre : Run config checks x y) (tailC : Run config checks x' y')
    (rrun : Run config checks r r') (highC high : ℕ)
    (eventsC eventsPre eventsF events : List (BalanceEvent preset))
    (i Cr X : ℕ)
    (close : X ≤ balanceAt pulled i + t.rise i +
      (Internal.syncD eventsF i + Internal.syncD events i + Cr + Internal.inducedR t rrun i +
        Internal.flowK t pre highC eventsPre events eventsF i +
        Internal.unitK t pre highC eventsPre events eventsF i) +
      (Internal.bandC pre highC i + Internal.bandR (eventsF ++ events) i + Internal.bandX fin highC
        i + Internal.slashR t i))
    (hCr : Cr ≤ Internal.propN tailC highC i + Internal.depPre eventsC i + Internal.whistC tailC
      highC i +
      Internal.syncCr eventsC i + Internal.consAmt eventsC i)
    (hcredC : Internal.credC pre highC i ≤ Internal.credC tailC highC i)
    (hcredN : Internal.credC pre highC i ≤ Internal.propN tailC highC i + Internal.depPre eventsC i
      + Internal.consAmt eventsC i)
    (hwhist : Internal.whistC pre highC i ≤ Internal.whistC tailC highC i)
    (hsync : Internal.syncCr eventsPre i ≤ Internal.syncCr eventsC i)
    (hband : Internal.bandC pre highC i ≤ Internal.bandC tailC highC i)
    (kept : t.keptArm i = true) :
    X ≤ Internal.whistleEnv t pulled anc fin i +
      Internal.whistleSlack t tailC rrun highC high eventsC eventsF events fin i := by
  have incPos := h.bands.1
  have key : 11 * min t.depth t.depthFin * (t.perIncrement *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    subst ht
    exact Internal.key_of_kept h i _ (Nat.min_le_left _ _) kept
  have hunit : t.unitGain = t.depth * (t.perIncrement *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) := by
    subst ht
    rfl
  have hW : 11 * Internal.slashW t i < 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    subst ht
    have hWdb := Internal.slashW_add_downwardBand_le h i
    have := h.facts.bandLow
    omega
  have envLe : balanceAt pulled i + t.rise i + Internal.slashR t i ≤ Internal.whistleEnv t pulled
    anc fin i := by
    unfold Internal.whistleEnv Internal.slashR
    split_ifs <;> omega
  have fK : Internal.flowK t pre highC eventsPre events eventsF i =
      Internal.flowGain t pre highC eventsPre events eventsF i := by
    simp [Internal.flowK, kept]
  have gain := flow_gain_slack (I := preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (WD := WEIGHT_DENOMINATOR.toNat) (F := (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (P := t.perIncrement) (D := min t.depth t.depthFin)
    (Z0 := Internal.credC pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsPre i +
      Internal.syncD events i +
      Internal.syncD eventsF i) (W := Internal.slashW t i) (U := t.unitGain) incPos key hW
    (by rw [hunit]; exact Nat.mul_le_mul_right _ (min_le_left _ _))
  have gainEq : Internal.flowGain t pre highC eventsPre events eventsF i =
      min t.depth t.depthFin * (11 * (Internal.credC pre highC i + Internal.whistC pre highC i +
        Internal.syncCr eventsPre i + Internal.syncD events i + Internal.syncD eventsF i +
          Internal.slashW t i) /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * t.perIncrement *
            (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) := by
    unfold Internal.flowGain Internal.flowCredit
    rfl
  have unitLe : Internal.unitK t pre highC eventsPre events eventsF i ≤
      Internal.unitK t tailC highC eventsC events eventsF i := by
    unfold Internal.unitK Internal.flowCredit
    split_ifs with p q
    · exact Nat.le_refl _
    · omega
    · exact Nat.zero_le _
    · exact Nat.le_refl _
  unfold Internal.whistleSlack Internal.whistleSlackBase
  rw [fK, gainEq] at close
  omega

/-- The key that a step slashes is an index.

The events of C's run are those of its prefix first.

Each deposit of the prefix replay finds the key unslashed or gives it no credit. -/
private theorem prefix_prologue (h : Setting config checks g split fin pulled anc counted V)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)}
    (replayedC : ((pre.snoc step).append post).balanceEvents highC = .ok eventsC) (i : ℕ)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    ∃ v : ValidatorIndex, v.toNat = i ∧
      ∃ e1 t : List (BalanceEvent preset), pre.balanceEvents highC = .ok e1 ∧
        eventsC = e1 ++ t ∧ ∀ e ∈ e1, e.source = .deposits →
          Internal.keyCredit i e = 0 ∨ ¬ slashedFlagAt e.before.state i = some true := by
  have bEarly : b.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have aEarly : a.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le bEarly
  -- The key is in the registry at `b`, so its position is an index.
  have inside : i < b.state.validators.data.size := by
    cases found : b.state.validators.data[i]? with
    | none => simp [found] at flag
    | some _ => exact (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨v, rfl⟩ := Uint64.exists_toNat_eq
    (inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam bEarly b.state))
  rw [Run.snoc_append_eq] at replayedC
  obtain ⟨e1, replayed1, t, rfl⟩ := Run.balanceEvents_prefix pre _ highC _ replayedC
  exact ⟨v, rfl, e1, t, replayed1, rfl, Internal.prefix_deposits_clean h pre aEarly highC replayed1
      v
    (by simpa using (Bool.and_eq_true_iff.mp flag).1)⟩

/-- The credits of C's run before a key's slashing are within the credit terms of `whistleSlack`.

They are the key's block credits from rewards and its consolidation and deposit credits.

They are those up to the step.

The proposer credits are at most those of the whole run.

The deposit bound counts only deposits made before the key was slashed.

The consolidation credits are at most the total applied to the key. -/
private theorem credC_prefix_le (h : Setting config checks g split fin pulled anc counted V)
    {a b : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (step : Step config checks a b) (post : Run config checks b ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)}
    (replayedC : ((pre.snoc step).append post).balanceEvents highC = .ok eventsC) (i : ℕ)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    Internal.credC pre highC i ≤
      Internal.propN ((pre.snoc step).append post) highC i + Internal.depPre eventsC i +
        Internal.consAmt eventsC i := by
  obtain ⟨v, rfl, e1, t, replayed1, rfl, clean⟩ :=
    prefix_prologue h pre step post highC replayedC i flag
  have whole := pre.snoc_append_eq step post
  rw [whole] at replayedC ⊢
  have depPreOk := Internal.deposits_le_depPre e1 v.toNat clean
  have deps := Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits)) (· =
    .deposits)
    (by intro s; simp) pre highC v replayed1
  have consEvents := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp)
    (pre.append ((Run.nil.snoc step).append post)) highC v replayedC
  have propScan := Internal.creditScan_append (fun s => decide (s = .rewards)) (fun _ => false)
    v.toNat highC
    pre ((Run.nil.snoc step).append post)
  have consScan := Internal.creditScan_append (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) v.toNat highC pre ((Run.nil.snoc step).append post)
  have split1 := Internal.credC_split pre highC v.toNat
  have split2 := Internal.credN_split pre highC v.toNat
  have depMono : Internal.depPre e1 v.toNat ≤ Internal.depPre (e1 ++ t) v.toNat := by
    unfold Internal.depPre
    simp only [List.filter_append, List.map_append, List.sum_append]
    omega
  beta_reduce at deps consEvents
  unfold Internal.propN at split2 ⊢
  unfold Internal.consAmt
  omega

/-- The credits of a key over the run before a step are at most those over the whole run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.creditScan_prefix_le (blockP slotP
  : BalanceSource → Bool) (v high : ℕ)
    {x a b c : ForkedBeaconState preset} (pre : Run config checks x a)
    (step : Step config checks a b) (post : Run config checks b c) :
    (Internal.creditScan blockP slotP v high pre) ≤
      (Internal.creditScan blockP slotP v high ((pre.snoc step).append post)) := by
  rw [Internal.creditScan_append, Internal.creditScan_snoc]
  split <;> omega

/-- The credits, whistleblower credits and credit band of a prefix are within the whole run's. -/
private theorem prefix_credits_mono {a b : ForkedBeaconState preset}
    (pre : Run config checks ⟨fork, split⟩ a) (step : Step config checks a b)
    (post : Run config checks b ⟨fork, counted⟩) (highC i : ℕ) :
    Internal.credC pre highC i ≤ Internal.credC ((pre.snoc step).append post) highC i ∧
      Internal.whistC pre highC i ≤ Internal.whistC ((pre.snoc step).append post) highC i ∧
      Internal.bandC pre highC i ≤ Internal.bandC ((pre.snoc step).append post) highC i := by
  have gross := Internal.creditScan_prefix_le
    (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i highC pre step
    post
  have deposits := Internal.creditScan_prefix_le (fun _ => false) (fun s => decide (s = .deposits))
      i highC
    pre step post
  refine ⟨Internal.creditScan_prefix_le _ _ i highC pre step post,
    Internal.creditScan_prefix_le _ _ i highC pre step post, ?_⟩
  unfold Internal.bandC Internal.grossScan
  split_ifs <;> omega

/-- The sync credits of the events of a prefix of C's run are within those of the whole run.

The replay of the prefix at `highC` is a prefix of the replay of the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.syncCr_prefix_le {a b :
  ForkedBeaconState preset}
    (pre : Run config checks ⟨fork, split⟩ a) (step : Step config checks a b)
    (post : Run config checks b ⟨fork, counted⟩) (highC : ℕ)
    {eventsPre eventsC : List (BalanceEvent preset)}
    (replayedPre : pre.balanceEvents highC = .ok eventsPre)
    (replayedC : ((pre.snoc step).append post).balanceEvents highC = .ok eventsC) (i : ℕ) :
    Internal.syncCr eventsPre i ≤ Internal.syncCr eventsC i := by
  obtain ⟨eventsStep, replayedStep, prefixStep⟩ :=
    (pre.snoc step).balanceEvents_prefix post highC eventsC replayedC
  obtain ⟨events, replayed, prefixPre⟩ :=
    pre.balanceEvents_prefix (Run.nil.snoc step) highC eventsStep (by exact replayedStep)
  obtain rfl : events = eventsPre := Except.ok.inj (replayed.symm.trans replayedPre)
  obtain ⟨rest, restEq⟩ := prefixPre.trans prefixStep
  rw [← restEq]
  unfold Internal.syncCr
  simp [List.map_append, List.sum_append]

/-- A slashing penalty and the gain on it over the window fit below one increment.

The penalty leaves a downward band, which is at least a quarter of the increment.

The penalty alone gains the unit gain, as it is under ten elevenths of an increment.

The unit gain is a gain per increment over the window, and two more gwei for each epoch.

`key` bounds the gain per increment by an eleventh of an increment. -/
private theorem slash_gain_small {I db WD F P D W : ℕ} (hI : 0 < I)
    (key : 11 * D * (P * F) < WD * I) (band : I ≤ 4 * db) (slashBand : W + db ≤ I)
    (window : 88 * D ≤ 3 * I) :
    W + (D * (11 * W / (10 * I) * P * F / WD) +
      if 0 < W then D * (P * F / WD + 2) else 0) < I := by
  have zero : 11 * W / (10 * I) = 0 := Nat.div_eq_of_lt (by omega)
  have small : 11 * (D * (P * F / WD)) < I := by
    have h1 := Nat.mul_le_mul_left (11 * D) (Nat.mul_div_le (P * F) WD)
    have h2 : WD * (11 * (D * (P * F / WD))) < WD * I :=
      calc WD * (11 * (D * (P * F / WD))) = 11 * D * (WD * (P * F / WD)) := by ring
        _ ≤ 11 * D * (P * F) := h1
        _ < WD * I := key
    exact Nat.lt_of_mul_lt_mul_left h2
  rw [zero]
  split_ifs
  · rw [Nat.mul_add]
    simp only [Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.zero_add]
    omega
  · simp only [Nat.zero_mul, Nat.zero_div, Nat.mul_zero, Nat.zero_add]
    omega

/-- A key that the split holds, unslashed, is not withdrawable at R's next epoch.

An unslashed key has its withdrawable epoch at its exit plus the delay, or both unset.

Its exit is late at R, which `late` states.

A key that R slashes after the split has its withdrawable epoch a slashings vector past the split.

The window of the guard is under half a vector. -/
private theorem voter_not_withdrawn (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (v : ValidatorIndex)
    (unslashed : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (inSplit : v.toNat < split.validators.data.size) :
    (pinTerms config pulled anc fin).withdrawnRB v.toNat = false := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have sizeSplit := registryGrows_of_chainSteps tail.chainSteps
  obtain ⟨uS, foundS⟩ : ∃ uS, split.validators.data[v.toNat]? = some uS :=
    ⟨_, Array.getElem?_eq_getElem inSplit⟩
  obtain ⟨wP, foundP⟩ : ∃ wP, pulled.validators.data[v.toNat]? = some wP :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inSplit sizeSplit)⟩
  have cleanS : uS.slashed = false := by simpa [foundS] using unslashed
  have half := Internal.depthFin_lt_half h
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have far := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  have beyond : (getCurrentEpoch pulled).toNat + 1 < wP.withdrawableEpoch.toNat := by
    by_cases slashedP : wP.slashed = true
    · have newly := (tail.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
        h.early (Internal.Setting.delay h) v.toNat uS wP foundS foundP cleanS slashedP).2
      have newly' : (getCurrentEpoch split).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          wP.withdrawableEpoch.toNat := newly
      omega
    · have cleanP : wP.slashed = false := by simpa using slashedP
      have late := late wP foundP cleanP
      rcases Run.withdrawable_eq_exit_delay (shared.append (fromFin.append tail)) h.genesis
        v.toNat wP foundP cleanP with ⟨exitFar, withdrawFar⟩ | eq
      · have := congrArg UInt64.toNat withdrawFar
        omega
      · omega
  show ((pulled.validators.data[v.toNat]?).any fun w =>
    decide (w.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)) = false
  rw [foundP]
  simpa using beyond

/-- The credit stake of a key on a low rate, rounded down to increments, is paid by the slack.

The stake is its credits, the gain on them and the gain of its base stake.

On a low rate, the base gain is below an increment, so it rounds away.

With bands, an increment of slack pays what is left of the gain over the flows.

With none, there are no credits.

Then a slashing's penalty is below an increment, and the stake is below two.

A stake below two increments rounds to one at most, which the slashing's increment pays. -/
private theorem y_floor_le (I WD F P D Df q Cr Ds DsF W gc S U Fl : ℕ)
    (key : 11 * D * (P * F) < WD * I) (hDf : D ≤ Df)
    (lowG : Df * ((11 * q + 9) / 10 + 3) < I)
    (hform : gc = D * (11 * ((Cr + Ds + DsF) + W + D * q + D) / (10 * I) * P * F / WD))
    (cases : (I ≤ U + 1 ∧ Cr + Fl ≤ S ∧
        gc + (D * q + D) ≤ Fl + Df * ((11 * q + 9) / 10 + 3)) ∨
      (Cr = 0 ∧ Ds = 0 ∧ DsF = 0 ∧ W < I ∧ (0 < W → I ≤ S + U))) :
    Cr + (gc + (D * q + D)) - (Cr + (gc + (D * q + D))) % I ≤ S + U := by
  have hI : 0 < I := by
    rcases Nat.eq_zero_or_pos I with h | h
    · subst h; simp at key
    · exact h
  rcases cases with ⟨hU, hCr, hgc⟩ | ⟨hCr, hDs, hDsF, hW, hS⟩
  · refine le_trans (Nat.sub_le _ _) ?_
    omega
  · subst hCr hDs hDsF
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD
      have : gc = 0 := by rw [hform]; simp
      subst this
      simp
    · have hG : 10 * ((11 * q + 9) / 10) + 9 ≥ 11 * q + 9 := by omega
      have h1 : D * (11 * q + 30) ≤ 10 * (Df * ((11 * q + 9) / 10 + 3)) := by
        calc D * (11 * q + 30) ≤ Df * (11 * q + 30) := Nat.mul_le_mul_right _ hDf
          _ ≤ Df * (10 * ((11 * q + 9) / 10 + 3)) :=
            Nat.mul_le_mul_left _ (by omega)
          _ = 10 * (Df * ((11 * q + 9) / 10 + 3)) := by ring
      have hX : 11 * (D * q + D) < 10 * I := by
        have : 11 * (D * q + D) < D * (11 * q + 30) := by
          have : D * (11 * q + 30) = 11 * (D * q + D) + 19 * D := by ring
          omega
        omega
      rcases Nat.eq_zero_or_pos W with hW0 | hW0
      · subst hW0
        have zero : 11 * (0 + 0 + 0 + 0 + D * q + D) / (10 * I) = 0 :=
          Nat.div_eq_of_lt (by omega)
        have g0 : gc = 0 := by rw [hform, zero]; simp
        subst g0
        have : D * q + D < I := by omega
        simp only [Nat.zero_add]
        rw [Nat.mod_eq_of_lt this]
        omega
      · have quot : 11 * (0 + 0 + 0 + W + D * q + D) / (10 * I) ≤ 2 := by
          have : 11 * (0 + 0 + 0 + W + D * q + D) < 3 * (10 * I) := by omega
          have := (Nat.div_lt_iff_lt_mul (by omega)).2 this
          omega
        have gcle : gc ≤ D * (2 * P * F / WD) := by
          rw [hform]
          refine Nat.mul_le_mul_left _ (Nat.div_le_div_right ?_)
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ quot)
        have gclt : 11 * gc < 2 * I := by
          have h2 : D * (2 * P * F / WD) * WD ≤ D * (2 * P * F) := by
            calc D * (2 * P * F / WD) * WD = D * (WD * (2 * P * F / WD)) := by ring
              _ ≤ D * (2 * P * F) := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
          have h3 : WD * (11 * gc) < WD * (2 * I) := by
            calc WD * (11 * gc) ≤ WD * (11 * (D * (2 * P * F / WD))) := by
                  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ gcle)
              _ = 11 * (D * (2 * P * F / WD) * WD) := by ring
              _ ≤ 11 * (D * (2 * P * F)) := Nat.mul_le_mul_left _ h2
              _ = 2 * (11 * D * (P * F)) := by ring
              _ < 2 * (WD * I) := by omega
              _ = WD * (2 * I) := by ring
          exact Nat.lt_of_mul_lt_mul_left h3
        have hY : 0 + (gc + (D * q + D)) < 2 * I := by omega
        have hdiv : (0 + (gc + (D * q + D))) / I ≤ 1 := by
          have := (Nat.div_lt_iff_lt_mul hI).2 (by omega : 0 + (gc + (D * q + D)) < 2 * I)
          omega
        have hmod := Nat.div_add_mod (0 + (gc + (D * q + D))) I
        have : I * ((0 + (gc + (D * q + D))) / I) ≤ I * 1 := Nat.mul_le_mul_left _ hdiv
        have := hS hW0
        omega

/-- The closing of a key, with the credits `Cr` that it holds, gives `keyCeiling`.

`Cr` is at most the credits of C's run, and the sync credits are at most `syncF`. -/
private theorem keyCeiling_of_close (anc : BeaconState preset fork)
    {ending : BeaconState preset fork}
    (run : Run config checks ⟨fork, fin⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (highC : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (v Cr : ℕ)
    (close : balanceAt ending v ≤ balanceAt pulled v + (pinTerms config pulled anc fin).rise v +
      (Internal.syncD eventsF v + Internal.syncD events v + Cr + Internal.inducedR (pinTerms config
        pulled anc fin) run v +
        Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v) +
      (Internal.bandC tailC highC v + Internal.bandR (eventsF ++ events) v + Internal.bandX fin
        highC v +
        Internal.slashR (pinTerms config pulled anc fin) v))
    (creditsLe : Cr ≤ Internal.credC tailC highC v + Internal.whistC tailC highC v +
      (eventsC.map (Internal.syncCredit v)).sum) :
    Internal.keyCeiling anc run tailC highC eventsC events eventsF v := by
  have fSyncE : Internal.syncD events v ≤ Internal.syncF events v := by
    rw [Internal.syncF_eq]; unfold Internal.syncD; omega
  have fSyncC : (eventsC.map (Internal.syncCredit v)).sum ≤ Internal.syncF eventsC v := by
    rw [Internal.syncF_eq]; omega
  unfold Internal.keyCeiling Internal.keyExtra
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The rise of a key on the kept branch bounds its effective balance on C's branch, up to flows.

Its balance on C's branch is bounded by `Bc`, and the effective balance by `stay`.

`Bc` adds up R's balance and the leak at the largest effective balance.

It adds the debits and slack on R's runs, and the credits and gains of C's run.

The bound also accounts for flows between states and the bands that pay for rounding.

The cap enters only through `stay` and `cappedY`, which the cap arms prove.

The bound applies to any prefix of C's run.

The effective balance at any starting state must also satisfy the ceiling's starting bound.

The rise bound accounts for flows and rounding bands, apart from the credits on C's branch.

The effective balance at the endpoint is at most the applicable cap and the rounded stake.

A key off the low rate reads the largest cap. -/
private theorem key_close (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {ending : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (highC : ℕ)
    {eventsC events eventsF : List (BalanceEvent preset)} (v : ValidatorIndex)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true)
    (notWithdrawn : (pinTerms config pulled anc fin).withdrawnRB v.toNat = false) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (Df D q gc Cr M Bc capHigh : ℕ)
    (hDf : Df = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    (hD : D = min (pinTerms config pulled anc fin).depth Df)
    (hq : q = (pinTerms config pulled anc fin).gainRate v.toNat)
    (hM : M = ((fromFin.append tail).balancePath.map fun z => effectiveAt z v.toNat).foldl max 0)
    (hform : gc = D * (11 * ((Cr + (events.map (Internal.syncDebit v.toNat)).sum +
          (eventsF.map (Internal.syncDebit v.toNat)).sum) +
        Internal.slashW (pinTerms config pulled anc fin) v.toNat + D * q + D) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat))
    (hBc : Bc = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
          (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1) -
            PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1))) +
      ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
        v.toNat)).sum +
        Internal.slashW (pinTerms config pulled anc fin) v.toNat) + (Cr + (gc + (D * q + D))))
    (maxLe : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (start : ℕ)
    (startLe : ∀ S : ℕ, Bc ≤ (pinTerms config pulled anc fin).high v.toNat + S →
      start ≤ max (balanceAt fin v.toNat)
        (((pinTerms config pulled anc fin).high v.toNat + S) -
          ((pinTerms config pulled anc fin).high v.toNat + S) %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (stay : balanceAt ending v.toNat = balanceAt pulled v.toNat ∨
      (balanceAt ending v.toNat ≤ start ∧ ∀ S U : ℕ,
        Bc ≤ (pinTerms config pulled anc fin).high v.toNat + S →
        (S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
          (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) →
        start ≤ (pinTerms config pulled anc fin).capFor v.toNat + S + U ∧
          start ≤ ((pinTerms config pulled anc fin).high v.toNat +
            preset.downwardBand) - ((pinTerms config pulled anc fin).high v.toNat +
            preset.downwardBand) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat + S + U) ∨
      (balanceAt ending v.toNat ≤ Bc + preset.downwardBand ∧
        balanceAt ending v.toNat ≤ max start
          (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh)))
    (cappedY : Df * ((11 * q + 9) / 10 + 3) < preset.EFFECTIVE_BALANCE_INCREMENT.toNat →
      balanceAt ending v.toNat ≤ (pinTerms config pulled anc fin).capFor v.toNat +
        (Cr + (gc + (D * q + D)) - (Cr + (gc + (D * q + D))) %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (creditsLe : Cr ≤ Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
      (eventsC.map (Internal.syncCredit v.toNat)).sum)
    (noCredit : Internal.bandC tailC highC v.toNat = 0 → Internal.bandX fin highC v.toNat = 0 → Cr =
      0) :
    balanceAt ending v.toNat ≤ balanceAt pulled v.toNat +
      (pinTerms config pulled anc fin).rise v.toNat +
      (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat + Cr +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
        Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)
          +
      (Internal.bandC tailC highC v.toNat + Internal.bandR (eventsF ++ events) v.toNat +
        Internal.bandX fin highC v.toNat +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat) := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  -- the gain of the flows, and of the base stake, is the flow gain with a unit and the base gain
  have hDle : D ≤ (pinTerms config pulled anc fin).depth := hD ▸ min_le_left _ _
  obtain ⟨toFin⟩ := h.toFin
  have hperIncrement : (pinTerms config pulled anc fin).perIncrement = P := by
    rw [hP]
    rfl
  have key := Internal.key_of_kept h v.toNat D hDle kept
  rw [hperIncrement] at key
  have hunit : (pinTerms config pulled anc fin).unitGain =
      (pinTerms config pulled anc fin).depth * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat + 2) := by
    rw [← hperIncrement]
    rfl
  have hdf : (pinTerms config pulled anc fin).depthFin = Df := hDf.symm
  have hDF : D ≤ Df := hD ▸ min_le_right _ _
  obtain ⟨Zk, hZk⟩ : ∃ Zk, Zk = Cr + (events.map (Internal.syncDebit v.toNat)).sum +
      (eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.slashW (pinTerms config pulled anc
        fin) v.toNat :=
    ⟨_, rfl⟩
  have gcEq : gc = D * (11 * (Zk + (D * q + D)) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) := by
    rw [hform, hZk, Nat.add_assoc _ (D * q) D]
  have gainBound : gc + (D * q + D) ≤
      Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat +
        Df * ((11 * q + 9) / 10 + 3) := by
    have split := Internal.flow_gain_split preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D
      (min (pinTerms config pulled anc fin).depth (pinTerms config pulled anc fin).depthFin) Df q Zk
      (Internal.flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
        v.toNat)
      key (le_of_eq (by rw [hD, hdf])) hDF
      (by rw [hZk]; unfold Internal.flowCredit Internal.syncCr Internal.syncD; omega)
    unfold Internal.flowGain Internal.unitK
    rw [hunit, hperIncrement, gcEq]
    refine le_trans split (Nat.add_le_add_right (Nat.add_le_add_left ?_ _) _)
    split_ifs
    · exact Nat.mul_le_mul_right _ (min_le_left _ _)
    · exact Nat.le_refl _
  obtain ⟨Fl, hFl⟩ : ∃ Fl, Fl =
      Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
          :=
    ⟨_, rfl⟩
  -- R's rise covers the increase on C's branch apart from the flows and their rounding slack.
  obtain ⟨H, hH⟩ : ∃ H, H = (pinTerms config pulled anc fin).high v.toNat :=
    ⟨_, rfl⟩
  have induced : Df * (pinTerms config pulled anc fin).leakAt M v.toNat ≤
      Df * (pinTerms config pulled anc fin).leak v.toNat +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat := by
    rw [← hdf, hM]
    exact Internal.leakAt_foldl_le config pulled anc fin (fromFin.append tail) v.toNat notWithdrawn
  have hHeq : H = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      Df * ((11 * q + 9) / 10 + 3 + (pinTerms config pulled anc fin).leak v.toNat) +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) := by
    rw [hH, hq, hDf]
    exact Internal.high_eq config pulled anc fin electra v.toNat
  have gap : Bc ≤ H + (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
      Internal.slashW (pinTerms config pulled anc fin) v.toNat + Cr +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
      (Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat))
          := by
    unfold Internal.syncD
    rw [hBc, hHeq, Nat.mul_add (Df) _ _]
    omega
  -- the closing: R's rise, the flows, and the bands that pay the rounding
  have alignedC : balanceAt ending v.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    FloorTrace.effective_aligned (toFin.append (fromFin.append tailC)) h.genesis h.aligned v.toNat
  have atMax : balanceAt ending v.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
    Internal.effectiveAt_le_capMax (toFin.append (fromFin.append tailC)) h.genesis h.caps
      h.early
      v.toNat
  -- the cap that `capFor` reads is the largest one off the low rate, and otherwise `cappedY`'s
  have capped : ∀ S U : ℕ, ((preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∧ Cr + Fl ≤ S ∧
        gc + (D * q + D) ≤ Fl + Df * ((11 * q + 9) / 10 + 3)) ∨
      (Cr = 0 ∧ (events.map (Internal.syncDebit v.toNat)).sum = 0 ∧
        (eventsF.map (Internal.syncDebit v.toNat)).sum = 0 ∧
        Internal.slashW (pinTerms config pulled anc fin) v.toNat <
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        (0 < Internal.slashW (pinTerms config pulled anc fin) v.toNat →
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U))) →
      balanceAt ending v.toNat ≤
        (pinTerms config pulled anc fin).capFor v.toNat + S + U := by
    intro S U cases
    by_cases lowG : Df * ((11 * q + 9) / 10 + 3) < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    · have y := y_floor_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D Df q Cr
        (events.map (Internal.syncDebit v.toNat)).sum (eventsF.map (Internal.syncDebit v.toNat)).sum
        (Internal.slashW (pinTerms config pulled anc fin) v.toNat) gc S U Fl key hDF lowG hform
          cases
      have := cappedY lowG
      omega
    · have notLow : (pinTerms config pulled anc fin).capFor v.toNat =
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
        rw [Internal.capFor_eq]
        refine ite_eq_right_iff.mpr fun low => ?_
        simp only [Bool.and_eq_true, decide_eq_true_eq] at low
        have lt := low.1
        rw [hdf, ← hq] at lt
        exact absurd lt lowG
      omega
  have close : ∀ S U : ℕ, Bc ≤ H + S → (S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
      (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) → balanceAt ending v.toNat ≤
          (pinTerms config pulled anc fin).capFor v.toNat + S + U →
      balanceAt ending v.toNat ≤
        balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat + S + U :=
    fun S U ceiling slack cap => Internal.rise_close config pulled anc fin v.toNat hH h.bands.1 kept
      alignedC (by subst hH; exact startLe S ceiling)
      (stay.imp_right fun st => st.elim
        (fun ⟨atStart, bounds⟩ => Or.inl ⟨atStart, by subst hH; exact bounds S U ceiling slack⟩)
        Or.inr) cap ceiling slack
  have fK : Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
    v.toNat =
      Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        := by
    simp [Internal.flowK, kept]
  have hWdb := Internal.slashW_add_downwardBand_le h v.toNat
  have fW : Internal.slashW (pinTerms config pulled anc fin) v.toNat ≤
      Internal.slashR (pinTerms config pulled anc fin) v.toNat := by
    have := hWdb
    unfold Internal.slashW at this ⊢
    unfold Internal.slashR
    split_ifs at this ⊢ <;> omega
  have incPos : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  have bandsOne : 0 < Internal.bandC tailC highC v.toNat ∨ 0 < Internal.bandR (eventsF ++ events)
    v.toNat ∨
      0 < Internal.bandX fin highC v.toNat → preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        Internal.bandC tailC highC v.toNat + Internal.bandR (eventsF ++ events) v.toNat +
          Internal.bandX fin highC v.toNat + 1 := by
    have up := h.bands.2
    rintro (pos | pos | pos)
    · unfold Internal.bandC at pos ⊢
      split_ifs at pos ⊢ <;> omega
    · unfold Internal.bandR at pos ⊢
      split_ifs at pos ⊢ <;> omega
    · unfold Internal.bandX at pos ⊢
      have dpos : 0 < Internal.dueAt fin highC {UInt64.ofNat v.toNat} :=
        Nat.pos_of_ne_zero fun z => by rw [z, Nat.mul_zero] at pos; exact Nat.lt_irrefl _ pos
      have := Nat.le_mul_of_pos_right preset.upwardBand dpos
      omega
  by_cases bands : 0 < Internal.bandC tailC highC v.toNat ∨ 0 < Internal.bandR (eventsF ++ events)
    v.toNat ∨
      0 < Internal.bandX fin highC v.toNat
  · have := close _ (Internal.bandC tailC highC v.toNat + Internal.bandR (eventsF ++ events) v.toNat
    +
      Internal.bandX fin highC v.toNat + (Internal.slashR (pinTerms config pulled anc fin) v.toNat -
        Internal.slashW (pinTerms config pulled anc fin) v.toNat))
      gap
      (Or.inr (Or.inl (by have := bandsOne bands; omega)))
      (capped _ _ (Or.inl ⟨by have := bandsOne bands; omega, by omega, by omega⟩))
    omega
  · simp only [not_or, not_lt, Nat.le_zero] at bands
    obtain ⟨hbC, hbR, hbX⟩ := bands
    have up := h.bands.2
    have sD0 : (eventsF.map (Internal.syncDebit v.toNat)).sum +
        (events.map (Internal.syncDebit v.toNat)).sum = 0 := by
      have := Internal.bandR_eq (eventsF ++ events) v.toNat
      simp only [List.map_append, List.sum_append] at this
      split_ifs at this <;> omega
    have Cr0 : Cr = 0 := noCredit hbC hbX
    have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      have := h.facts.bandLow
      omega
    have M0 : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat := by
      have e := maxLe
      rw [Nat.div_eq_of_lt (show Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
        Internal.slashW (pinTerms config pulled anc fin) v.toNat <
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat
            by unfold Internal.syncD; omega), Nat.mul_zero, Nat.add_zero] at e
      exact e
    have ind0 : Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat = 0
      := by
      rw [Internal.inducedR_of_not_withdrawn _ _ _ notWithdrawn]
      rw [← hM, Nat.sub_eq_zero_of_le (Internal.leakAt_mono config pulled anc fin v.toNat M0),
        Nat.mul_zero]
    have hZkW : Zk = Internal.slashW (pinTerms config pulled anc fin) v.toNat := by
      rw [hZk]
      omega
    have gainNet := Internal.flow_gain_split preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D D Df q Zk Zk key
      (Nat.le_refl _) hDF (Nat.le_refl _)
    rw [hZkW] at gainNet
    obtain ⟨εn, hεn⟩ : ∃ εn, εn =
        D * (11 * Internal.slashW (pinTerms config pulled anc fin) v.toNat /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
        (if 0 < Internal.slashW (pinTerms config pulled anc fin) v.toNat then
          D * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2)
          else 0) := ⟨_, rfl⟩
    rw [← hεn] at gainNet
    have small := slash_gain_small h.bands.1 key h.facts.bandLow hWdb (by
      have := Internal.depthFin_lt_half h
      have := (Internal.PinPresetFacts.vectorSmall h.facts)
      omega)
    rw [← hεn] at small
    rw [hZkW] at gcEq
    have ceilII : Bc ≤ H + (Internal.slashW (pinTerms config pulled anc fin) v.toNat + εn) := by
      rw [hBc, hHeq, Nat.mul_add Df _ _]
      omega
    have εle : εn ≤ Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events
      eventsF
        v.toNat +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
          := by
      have hWle : Internal.slashW (pinTerms config pulled anc fin) v.toNat ≤
          Internal.flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat := by
        unfold Internal.flowCredit
        omega
      have hdf' : min (pinTerms config pulled anc fin).depth
          (pinTerms config pulled anc fin).depthFin = D := by rw [hdf, hD]
      unfold Internal.flowGain Internal.unitK
      rw [hdf', hperIncrement, hunit, hεn]
      refine Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.div_le_div_right
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right
          (Nat.mul_le_mul_left 11 hWle)))))) ?_
      split_ifs <;> first | exact Nat.zero_le _ | exact Nat.mul_le_mul_right _ hDle | omega
    have hsl : 0 < Internal.slashW (pinTerms config pulled anc fin) v.toNat →
        Internal.slashR (pinTerms config pulled anc fin) v.toNat =
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun pos => by
      unfold Internal.slashW at pos
      unfold Internal.slashR
      split_ifs at pos ⊢ <;> omega
    have slack : Internal.slashW (pinTerms config pulled anc fin) v.toNat + εn = 0 ∨
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat -
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) + 1 ∨
        (Internal.slashW (pinTerms config pulled anc fin) v.toNat + εn <
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            Internal.slashW (pinTerms config pulled anc fin) v.toNat + εn +
              (Internal.slashR (pinTerms config pulled anc fin) v.toNat -
                Internal.slashW (pinTerms config pulled anc fin) v.toNat)) := by
      by_cases w0 : Internal.slashW (pinTerms config pulled anc fin) v.toNat = 0
      · left
        rw [hεn, w0]
        simp
      · right
        right
        have sl := hsl (Nat.pos_of_ne_zero w0)
        exact ⟨small, by omega⟩
    have := close _ _ ceilII slack
      (capped _ _ (Or.inr ⟨Cr0, by omega, by omega, hW, fun pos => by have := hsl pos; omega⟩))
    omega

/-- A start is within the finalized balance or the rounded top.

It is within the finalized effective balance, or within the floor of the balance at it.

The floor start is within the balance ceiling.

It is aligned, so it is within the rounding of the ceiling. -/
private theorem start_le_round {inc fin e a cap H S : ℕ}
    (aligned : e % inc = 0) (capped : e ≤ cap) (ceiling : min a cap ≤ H + S)
    (start : e ≤ fin ∨ e ≤ a - a % inc) :
    e ≤ max fin ((H + S) - (H + S) % inc) := by
  rcases start with atFin | floorA
  · exact Nat.le_trans atFin (Nat.le_max_left _ _)
  · refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    exact Internal.aligned_le_round aligned capped ceiling floorA

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The closing of the rise for a key on its kept arm, from a start state `c`, at any end of C.

The key is in the registry at the state `c` of the shared segment, and unslashed at the split.

The run from the finalized state reaches `c` first, and the key is absent before it.

The caps along the runs are those of each state, so a switch to compounding on either run is read.

The credits `Cr` are all of C's, so they cover the cap's rise on C's run.

`late` is read only for a key that is unslashed at R.

At an end before R's epoch and no later than `c`, `shortStart` bounds the effective balance at `c`.

The replays are read at R's epoch. -/
private theorem key_core_frozen_from (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    {ending : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch ending).toNat ≤ highC + 1)
    (nearC : (getCurrentEpoch ending).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex)
    (unslashed : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size)
    (before : ∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p v.toNat = 0)
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (shortStart : (getCurrentEpoch ending).toNat < (getCurrentEpoch pulled).toNat →
      (getCurrentEpoch ending).toNat ≤ (getCurrentEpoch c).toNat → ∀ S U : ℕ,
      (S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
        (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) →
      min (actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat) ≤
        (pinTerms config pulled anc fin).high v.toNat + S →
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
          (pinTerms config pulled anc fin).capFor v.toNat + S + U ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
          ((pinTerms config pulled anc fin).high v.toNat + preset.downwardBand) -
            ((pinTerms config pulled anc fin).high v.toNat + preset.downwardBand) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat + S + U)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    balanceAt ending v.toNat ≤ balanceAt pulled v.toNat +
      (pinTerms config pulled anc fin).rise v.toNat +
      (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
        (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
          (eventsC.map (Internal.syncCredit v.toNat)).sum) +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
        Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat +
        Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat)
          +
      (Internal.bandC tailC highC v.toNat + Internal.bandR (eventsF ++ events) v.toNat +
        Internal.bandX fin highC v.toNat +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have sizeC := registryGrows_of_chainSteps fromC.chainSteps
  -- the floor of each state of R's run, and the largest effective balance on it
  obtain ⟨M, hM⟩ : ∃ M, M = ((fromFin.append tail).balancePath.map
      fun z => effectiveAt z v.toNat).foldl max 0 := ⟨_, rfl⟩
  -- the credit ceiling of C's run, from the floor and the debits of R's
  have splitSize : v.toNat < split.validators.data.size := Nat.lt_of_lt_of_le inside sizeC
  have debitsM := Internal.debits_le_top h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ
    _)
    replayedF replayed v splitSize M
    (fun pre post same => hM ▸ Internal.effective_le_foldl_max (fromFin.append tail) v.toNat
      (fromFin.append pre) post (by rw [← Run.append_assoc, ← same]))
  have debitsCap := Internal.debits_le_top h fromFin tail (getCurrentEpoch pulled).toNat
    (Nat.le_succ _)
    replayedF replayed v splitSize
    (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (fun pre post _ => Internal.effective_le_cap_pulled h (fromFin.append pre) post v.toNat)
  have splitOn {x : ForkedBeaconState preset} (pre : Run config checks x ⟨fork, split⟩) :
      (⟨fork, split⟩ : ForkedBeaconState preset) ∈ (pre.append tail).balancePath := by
    rw [Run.balancePath_append]
    exact List.mem_append_left _ (List.mem_of_mem_getLast? (Run.balancePath_ends pre).2)
  -- the envelope and the floor read the key's run from `c` to R's whole
  have cutRest : toC.append (fromC.append tail) = fromFin.append tail := by
    rw [Run.append_assoc, cutC]
  have cleanSplit : ∀ u, split.validators.data[v.toNat]? = some u → u.slashed = false :=
    fun u foundU => by
      obtain ⟨uS, foundS⟩ : ∃ uS, split.validators.data[v.toNat]? = some uS :=
        ⟨_, Array.getElem?_eq_getElem splitSize⟩
      rw [foundS] at foundU
      cases foundU
      simpa [foundS] using unslashed
  have clean : ∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false :=
    fun u foundU => Internal.unslashed_of_run fromC foundU cleanSplit
  have slashedLate := Internal.slashed_withdrawable_of_clean h tail v cleanSplit splitSize
    h.finalized
  have envAll := Internal.envelope_of_voter h fromFin tail replayedF replayed v toC (fromC.append
    tail)
    cutRest clean slashedLate inside start late
  have startEff := envAll (⟨fork, split⟩ : ForkedBeaconState preset) (splitOn fromC)
  have floorR : min (actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
      (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (Internal.syncDebit v.toNat)).sum + Internal.slashW (pinTerms config pulled anc
          fin) v.toNat := by
    have := Internal.voter_floorAt h fromFin tail v toC (fromC.append tail) cutRest clean
      slashedLate inside
      late fromC tail rfl replayed
    omega
  have rateLow := Internal.keptArm_eq v.toNat kept
  obtain ⟨P, hP⟩ : ∃ P, P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat := ⟨_, rfl⟩
  obtain ⟨credits, netLe, -⟩ := Internal.credits_le_sources (toFin.append fromFin) h.genesis tailC
    h.early electra v.toNat highC replayedC
  obtain ⟨Cr, hCr⟩ : ∃ Cr, Cr = Internal.credC tailC highC v.toNat + Internal.whistC tailC highC
    v.toNat +
    (eventsC.map (Internal.syncCredit v.toNat)).sum := ⟨_, rfl⟩
  obtain ⟨gc, hform, hgc, bound0⟩ := Internal.c_ceiling h fromFin tailC highC endEpochC nearC P hP v
    splitSize (Internal.slashW (pinTerms config pulled anc fin) v.toNat) replayedC Cr (by omega)
    (fun _ => hCr.symm.le) startEff floorR debitsCap rateLow
  have bound : ∀ z ∈ tailC.balancePath,
      min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (Internal.syncDebit v.toNat)).sum + Internal.slashW (pinTerms config pulled anc
          fin) v.toNat +
        Cr + (gc + (min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).gainRate v.toNat +
          min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat))) := by
    intro z member
    have := bound0 z member
    have := Nat.min_le_left
      (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (Internal.syncDebit v.toNat)).sum + Internal.slashW (pinTerms config pulled anc
          fin) v.toNat)
      (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
    omega
  -- the names of the parts of the ceilings
  obtain ⟨Df, hDf⟩ : ∃ Df, Df = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth Df := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate v.toNat := ⟨_, rfl⟩
  rw [← hDf, ← hD, ← hq] at hform hgc bound bound0
  rw [← hDf] at debitsM
  -- R's run has the ceiling on its balance, and C's run adds its credits and gains
  have onR : ∀ z ∈ (fromC.append tail).balancePath,
      min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
            (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
              PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1))) +
          ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) := by
    intro z member
    have := Internal.path_ceiling h fromFin tail (getCurrentEpoch pulled).toNat (Nat.le_succ _)
      replayedF
      replayed v (Internal.slashW (pinTerms config pulled anc fin) v.toNat) M
      (fun pre post cut => hM ▸ Internal.effective_le_foldl_max (fromFin.append tail) v.toNat pre
          post cut)
      toC fromC cutC inside
      (Internal.voter_floorAt h fromFin tail v toC (fromC.append tail) cutRest clean slashedLate
        inside
        late) z member
    rw [hDf]
    omega
  obtain ⟨Bc, hBc⟩ : ∃ Bc, Bc = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset)
        v.toNat + (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
          (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
            PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1))) +
      ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
        v.toNat)).sum +
        Internal.slashW (pinTerms config pulled anc fin) v.toNat) + (Cr + (gc + (D * q + D))) :=
    ⟨_, rfl⟩
  -- Before the split C shares R's path, so only the tail needs C's credit bounds.
  have onSharedOrTail {z : ForkedBeaconState preset}
      (member : z ∈ (fromC.append tailC).balancePath) :
      z ∈ (fromC.append tail).balancePath ∨ z ∈ tailC.balancePath := by
    rw [Run.balancePath_append] at member
    rcases List.mem_append.mp member with front | later
    · exact .inl (by rw [Run.balancePath_append]; exact List.mem_append_left _ front)
    · exact .inr (List.mem_of_mem_tail later)
  have onC : ∀ z ∈ (fromC.append tailC).balancePath,
      min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤ Bc := by
    intro z member
    rcases onSharedOrTail member with inR | later
    · have := onR z inR
      omega
    · have := bound z later
      omega
  have atC : min (actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat)
      (PinTerms.capAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat) ≤ Bc := by
    obtain ⟨rest, head⟩ := Run.balancePath_head (fromC.append tailC)
    exact onC _ (by rw [head]; exact List.mem_cons_self)
  have stay : balanceAt ending v.toNat = balanceAt pulled v.toNat ∨
      (balanceAt ending v.toNat ≤ effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ∧
        ∀ S U : ℕ, Bc ≤ (pinTerms config pulled anc fin).high v.toNat + S →
        (S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
          (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) →
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
            (pinTerms config pulled anc fin).capFor v.toNat + S + U ∧
          effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
            ((pinTerms config pulled anc fin).high v.toNat +
              preset.downwardBand) - ((pinTerms config pulled anc fin).high v.toNat +
              preset.downwardBand) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat + S + U) ∨
      (balanceAt ending v.toNat ≤ Bc + preset.downwardBand ∧
        balanceAt ending v.toNat ≤ max (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat)
          (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
            (PinTerms.capAt (⟨fork, ending⟩ : ForkedBeaconState preset) v.toNat))) := by
    rcases Internal.key_stay_to h toC fromC tailC v.toNat inside Bc onC with ⟨flat, same⟩ | ⟨-,
      near, top⟩
    · by_cases reached : (getCurrentEpoch pulled).toNat ≤ (getCurrentEpoch ending).toNat
      · rcases Internal.key_stay_to h toC fromC tail v.toNat inside _ onR with ⟨flatR, sameR⟩ | ⟨lt,
        -⟩
        · exact .inl (same.trans sameR.symm)
        · omega
      · exact .inr (.inl ⟨le_of_eq same, fun S U ceiling slack =>
        shortStart (by omega) flat S U slack (by omega)⟩)
    · exact .inr (.inr ⟨near, top⟩)
  have cappedLe : PinTerms.capAt (⟨fork, ending⟩ : ForkedBeaconState preset) v.toNat ≤
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat →
      balanceAt ending v.toNat ≤ (pinTerms config pulled anc fin).capFor v.toNat :=
    fun le => Nat.le_trans (Internal.effective_le_cap_at (toFin.append (toC.append (fromC.append
      tailC)))
      h.genesis h.caps h.early v.toNat)
      (Nat.le_trans le
        (Internal.capAt_le_capFor config pulled anc fin v.toNat (Internal.capAt_le_capMax h.caps
          electra v.toNat)))
  have maxLe : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    have mapped : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ∈
        (fromFin.append tail).balancePath.map fun z => effectiveAt z v.toNat :=
      List.mem_map.mpr ⟨_, splitOn fromFin, rfl⟩
    rw [hM, List.foldl_max_eq_max (List.ne_nil_of_mem mapped)]
    refine Nat.max_le.2 ⟨Nat.zero_le _, (List.max_le_iff (List.ne_nil_of_mem mapped)).2 ?_⟩
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    rw [← cutC, ← Run.append_assoc] at hz
    exact Internal.path_le_of_start toC (fromC.append tail) v.toNat _ before envAll z hz
  have noCredit : Internal.bandC tailC highC v.toNat = 0 → Internal.bandX fin highC v.toNat = 0 → Cr
    = 0 := by
    intro hbC hbX
    have up := h.bands.2
    have incPos : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      have := h.facts.incrementSize
      omega
    have scans : Internal.grossScan v.toNat highC tailC = 0 ∧
        (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
          =
          0 := by
      unfold Internal.bandC at hbC
      split_ifs at hbC <;> omega
    have hdue : Internal.dueAt fin highC {v} = 0 := by
      unfold Internal.bandX at hbX
      rw [UInt64.ofNat_toNat] at hbX
      rcases Nat.eq_zero_or_pos (Internal.dueAt fin highC {v}) with z | p
      · exact z
      · have := Nat.le_mul_of_pos_right preset.upwardBand p
        omega
    have c0 := Internal.consAmt_zero h fromFin replayedF tailC highC endEpochC nearC replayedC v
      hdue
    have consScan : (Internal.creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v.toNat highC tailC) ≤
          Internal.consAmt eventsC v.toNat :=
      Internal.scan_le_events _ _ (· = .consolidations) (by intro s; simp) tailC highC v replayedC
    have noOwn : ¬ 0 < Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat :=
      fun pos => by
      rcases credit_gate tailC highC v (Or.inl rfl) pos with credited | consolidated
      · simp only [Internal.creditedKey, decide_eq_true_eq] at credited
        omega
      · omega
    have noSeat : ¬ 0 < Internal.syncCr eventsC v.toNat := fun pos => by
      have := Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early tailC highC replayedC
        v.toNat pos
      omega
    unfold Internal.syncCr at noSeat
    omega
  have startLe : ∀ S : ℕ, Bc ≤ (pinTerms config pulled anc fin).high v.toNat + S →
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        max (balanceAt fin v.toNat)
          (((pinTerms config pulled anc fin).high v.toNat + S) -
            ((pinTerms config pulled anc fin).high v.toNat + S) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    intro S ceiling
    exact start_le_round
      (FloorTrace.effective_aligned (toFin.append toC) h.genesis h.aligned v.toNat)
      (Internal.effective_le_cap_at (toFin.append toC) h.genesis h.caps h.early v.toNat) (by omega)
      (start.imp_left And.right)
  -- on the headroom of C's cap, which R's cap may not reach, the cap adds to the rounded credits
  have cappedY : Df * ((11 * q + 9) / 10 + 3) < preset.EFFECTIVE_BALANCE_INCREMENT.toNat →
      balanceAt ending v.toNat ≤ (pinTerms config pulled anc fin).capFor v.toNat +
        (Cr + (gc + (D * q + D)) - (Cr + (gc + (D * q + D))) %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    intro lowGain
    by_cases le : PinTerms.capAt (⟨fork, ending⟩ : ForkedBeaconState preset) v.toNat ≤
        PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat
    · exact Nat.le_trans (cappedLe le) (Nat.le_add_right _ _)
    · have lowArm : (decide ((pinTerms config pulled anc fin).depthFin *
            ((11 * (pinTerms config pulled anc fin).gainRate v.toNat + 9) / 10 + 3) <
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) &&
          decide (11 * (pinTerms config pulled anc fin).depth *
            ((pinTerms config pulled anc fin).gainRate v.toNat + 1) ≤
              (pinTerms config pulled anc fin).ebUp v.toNat)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by rw [show (pinTerms config pulled anc fin).depthFin = Df from hDf.symm, ← hq]
                  exact lowGain, rateLow⟩
      have capFor : (pinTerms config pulled anc fin).capFor v.toNat =
          PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat := by
        rw [Internal.capFor_eq]
        simp only [lowArm, ↓reduceIte]
      have pulledSize : v.toNat < pulled.validators.data.size :=
        Nat.lt_of_lt_of_le splitSize (registryGrows_of_chainSteps tail.chainSteps)
      obtain ⟨wP, foundP⟩ : ∃ w, pulled.validators.data[v.toNat]? = some w :=
        ⟨_, Array.getElem?_eq_getElem pulledSize⟩
      have aligned := Internal.capAt_aligned h.aligned (z := (⟨fork, pulled⟩ : ForkedBeaconState
        preset))
        electra foundP
      have capSP := Internal.cap_le_cap_of_run h.caps tail h.early v.toNat
      have stay2 := Internal.key_stay_to h toC fromC tailC v.toNat inside
        (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (Cr + (gc + (D * q + D))))
        (fun z member => by
          rcases onSharedOrTail member with inR | later
          · have := Internal.capCeil_path (fromC.append tail) h.caps h.early (Nat.le_refl _) v.toNat
              z inR
            omega
          · have := bound0 z later
            have := Nat.min_le_right
              (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
                ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
                (events.map (Internal.syncDebit v.toNat)).sum +
                Internal.slashW (pinTerms config pulled anc fin) v.toNat)
              (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
            omega)
      have whole : (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (Cr + (gc + (D * q + D)))) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
          (Cr + (gc + (D * q + D))) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
        rw [Nat.add_mod, aligned, Nat.zero_add, Nat.mod_mod]
      have atC := Internal.effective_le_cap_at (toFin.append toC) h.genesis h.caps h.early v.toNat
      have atPulled := Internal.effective_le_cap_at (toFin.append (toC.append (fromC.append tail)))
        h.genesis
        h.caps h.early v.toNat
      have capCP := Internal.cap_le_cap_of_run h.caps (fromC.append tail) h.early v.toNat
      rw [capFor]
      rcases stay2 with ⟨-, same⟩ | ⟨-, -, atMost⟩
      · show effectiveAt (⟨fork, ending⟩ : ForkedBeaconState preset) v.toNat ≤ _
        omega
      · show effectiveAt (⟨fork, ending⟩ : ForkedBeaconState preset) v.toNat ≤ _
        omega
  have creditsLe : Cr ≤ Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
      (eventsC.map (Internal.syncCredit v.toNat)).sum := hCr.le
  rw [← hCr]
  exact key_close h tail fromFin tailC highC v kept
    (voter_not_withdrawn h fromFin tail v unslashed late
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps fromC.chainSteps)))
    P hP Df D q gc Cr M Bc _ hDf hD hq hM hform hBc
    maxLe (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat) startLe stay
    cappedY creditsLe noCredit

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The per-key core of the rise for a counted voter on its kept arm, from a start state `c`.

The key's cap may stay or move, from `c` to R and to C.

The bound is evaluated at the end of C's run.

C's run ends at or after R's epoch, so `shortStart` holds vacuously. -/
private theorem key_core_cap (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex)
    (unslashed : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size)
    (before : ∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p v.toNat = 0)
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    Internal.keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat :=
  keyCeiling_of_close anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat _
    (key_core_frozen_from h tail replayed fromFin replayedF tailC highC endEpochC h.near replayedC
      v unslashed (fun w fw _ => late w fw) toC fromC cutC inside before start
      (fun lt => absurd lt (by
        have := UInt64.le_iff_toNat_le.mp h.later
        omega)) kept)
    (Nat.le_refl _)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of the split's registry, unslashed at the split and kept, is bounded at its slashing.

The key is held at a state `c` of the shared segment.

The closing reads the cap of each state, so the cap is not read as frozen.

The step `a → b` of C's run slashes it, and `pre` is C's run up to `a`.

Its credits are those of the prefix, within the terms of `whistleSlack`.

The slashing's increment is `whistleEnv`'s.

An unslashed key at R is late for the whole run, which `late` states for the key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.registry_frozen (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : i < c.validators.data.size)
    (before : ∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p i = 0)
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤
        (pinTerms config pulled anc fin).ebUp i ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤ balanceAt fin i) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) i -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) i %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (unslashed : (split.validators.data[i]?.map (·.slashed)).getD false = false)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true)
    (late : ∀ w, pulled.validators.data[i]? = some w → w.slashed = false →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin i := by
  classical
  obtain ⟨pre, post, cut, aEarly, aEpoch⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  obtain ⟨af, as⟩ := a
  have sameFork : fork = af :=
    (Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
  subst sameFork
  -- a short end with the finalized start keeps its balance at `c`, within `whistleEnv`
  by_cases leftShort : ((getCurrentEpoch as).toNat < (getCurrentEpoch pulled).toNat ∧
      (getCurrentEpoch as).toNat ≤ (getCurrentEpoch c).toNat) ∧
      (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤
          (pinTerms config pulled anc fin).ebUp i ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤ balanceAt fin i)
  · have bound := Internal.short_in_fin h fromC tailC step member i inside leftShort.2.2
      (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin i) leftShort.1.2
    omega
  have near := h.near
  -- the replays are read at R's epoch
  obtain ⟨replayedF', replayed'⟩ :=
    Internal.replays_at_pulled tail high endEpoch replayed fromFin replayedF
  obtain ⟨eventsPre, replayedPre⟩ := pre.balanceEvents_ok aEarly highC
  subst cut
  -- the key as a validator index
  have sizeC : c.validators.data.size ≤ split.validators.data.size :=
    registryGrows_of_chainSteps fromC.chainSteps
  have sizeCounted : split.validators.data.size ≤ counted.validators.data.size :=
    registryGrows_of_chainSteps ((pre.snoc step).append post).chainSteps
  have aEpoch' : (getCurrentEpoch as).toNat ≤ (getCurrentEpoch counted).toNat := aEpoch
  obtain ⟨v, rfl⟩ := Uint64.exists_toNat_eq
    ((inside.trans_le (sizeC.trans sizeCounted)).trans
      (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted))
  have core := key_core_frozen_from h tail replayed' fromFin replayedF' pre highC
    (by omega) (by omega) replayedPre v unslashed late
    toC fromC cutC inside before start
    (fun lt le S U slack ceiling => by
      rcases start with ⟨within, atFin⟩ | floorC
      · exact absurd ⟨⟨lt, le⟩, within, atFin⟩ leftShort
      · obtain ⟨toFin⟩ := h.toFin
        have capped := Internal.effective_le_cap_at (toFin.append toC) h.genesis h.caps h.early
          v.toNat
        have capsLater := Internal.cap_le_cap_of_run h.caps (fromC.append tail) h.early v.toNat
        have forOf := Internal.capAt_le_capFor config pulled anc fin v.toNat
          (Internal.capAt_le_capMax h.caps (Nat.le_trans (by decide) h.fulu) v.toNat)
        exact ⟨by omega, Internal.short_start_floor h.bands.1
          (FloorTrace.effective_aligned (toFin.append toC) h.genesis h.aligned v.toNat) capped
          ceiling floorC slack⟩)
    kept
  have p1 := credC_prefix_le h pre step post highC replayedC v.toNat flag
  have p2 := prefix_credits_mono (counted := counted) pre step post highC v.toNat
  have p3 : (eventsPre.map (Internal.syncCredit v.toNat)).sum ≤ Internal.syncCr eventsC v.toNat :=
    Internal.syncCr_prefix_le pre step post highC replayedPre replayedC v.toNat
  exact whistle_of_close h _ rfl pre ((pre.snoc step).append post) (fromFin.append tail) highC high
    eventsC eventsPre eventsF events v.toNat
    (Internal.credC pre highC v.toNat + Internal.whistC pre highC v.toNat +
      (eventsPre.map (Internal.syncCredit v.toNat)).sum)
    (balanceAt as v.toNat) core (by omega) p2.1 p1 p2.2.1 p3 p2.2.2 kept

/-- At the finalized state there is no earlier balance path, and the effective balance fits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.finalized_start (h : Setting config
  checks g split fin pulled anc counted V)
    (i : ℕ) :
    (∀ p ∈ (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩).balancePath,
      p = ⟨fork, fin⟩ ∨ effectiveAt p i = 0) ∧
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i ≤
        (pinTerms config pulled anc fin).ebUp i ∧
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i ≤ balanceAt fin i) :=
  ⟨fun _ mem => Or.inl (by simpa [Run.balancePath] using mem),
    Internal.effective_fin_le_ebUp h i, Nat.le_refl _⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of the split's registry that is off the kept arm is bounded by the largest cap.

Its rise is its whole headroom, so the bound reads the largest cap at each step of C's branch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.registry_headroom (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (notKept : ¬ (pinTerms config pulled anc fin).keptArm i = true) (slack : ℕ) :
    effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i + slack
      := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨pre, -, -, aEarly, -⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have capped := Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre) h.genesis
    h.caps aEarly i
  have headroom := Internal.rise_of_notKept h i notKept
  unfold Internal.whistleEnv
  split_ifs <;> omega

/-- The per-key core of the rise for a key on the headroom arm.

Its rise is its whole headroom, to the largest cap.

The cap holds the balance on C's branch, whatever the replays read. -/
private theorem key_core_headroom (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (v : ValidatorIndex)
    (notKept : ¬ (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    Internal.keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  obtain ⟨shared⟩ := h.toFin
  have capped := Internal.effectiveAt_le_capMax (shared.append (fromFin.append tailC))
    h.genesis h.caps h.early v.toNat
  have headroom := Internal.rise_of_notKept h v.toNat notKept
  have countedLe : balanceAt counted v.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := capped
  unfold Internal.keyCeiling
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C's branch created beyond the split is bounded by its credits and their gains.

The key's stake is its credits on C's branch.

Its effective balance is within the ceiling of a created key.

Its flows hold the credits, and the key's gain over the depth of the window is the flow gain.

The premises are the rate of the ceiling at the depth of the window.

They are also the charge of the flow gain to the key.

The unit pays the joint floor, and the band is an upward band at least. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_key_ceiling (h : Setting
  config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat)
    (key : 11 * (min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (charged : (pinTerms config pulled anc fin).keptArm v.toNat = true ∨
      (v.toNat ∉ (pinTerms config pulled anc fin).positions ∧
        (pinTerms config pulled anc fin).gainHigh = false))
    (band : preset.upwardBand ≤ Internal.bandC tailC highC v.toNat + Internal.bandX fin highC
      v.toNat) :
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
  obtain ⟨z, pre, post, -, positive, -, bound⟩ := Internal.created_ceiling h tailC highC endEpochC
      replayedC
    activated absent (pinTerms config pulled anc fin).perIncrement rfl key
  set Z := Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
    Internal.syncCr eventsC v.toNat with hZ
  have atEnd : (⟨fork, counted⟩ : ForkedBeaconState preset) ∈ post.balancePath := by
    obtain ⟨front, eq⟩ := Run.balancePath_last post
    rw [eq]
    simp
  have ceiling := bound _ atEnd
  have effective : effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat =
      balanceAt counted v.toNat := rfl
  -- the flow gain is charged to the key
  have flowEq : Internal.flowK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
      v.toNat = Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events
        eventsF
        v.toNat := by
    unfold Internal.flowK
    rw [ite_eq_left charged]
  have credit : Z ≤ Internal.flowCredit (pinTerms config pulled anc fin) tailC highC eventsC events
    eventsF
      v.toNat := by
    unfold Internal.flowCredit
    omega
  have gain : min (pinTerms config pulled anc fin).depth
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
      (11 * Z / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
        (pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ≤
      Internal.flowGain (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        :=
    Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.div_le_div_right (Nat.mul_le_mul_left 11 credit)))))
  have unit : min (pinTerms config pulled anc fin).depth
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
      ((pinTerms config pulled anc fin).perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) ≤
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat :=
        by
    unfold Internal.unitK
    rw [ite_eq_left (Nat.lt_of_lt_of_le positive credit)]
    exact Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
  have below := (Internal.PinPresetFacts.below h.facts)
  have upward := h.bands.2
  have sync := Internal.syncF_eq eventsC v.toNat
  have credits : Internal.syncCr eventsC v.toNat = (eventsC.map (Internal.syncCredit v.toNat)).sum
    := rfl
  unfold Internal.keyExtra
  omega

/-- The exit of a key that the finalized state does not hold is not before the finalized epoch.

An exit up to the finalized epoch would be an exit of the finalized registry. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_exitAfterFin (h : Setting
  config checks g split fin pulled anc counted V)
    {i : ℕ} (created : fin.validators.data.size ≤ i) :
    ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch fin).toNat ≤ w.exitEpoch.toNat := by
  intro w found
  by_contra before
  obtain ⟨u, foundFin, -⟩ := Internal.exit_kept_of_le_fin h found (by omega)
  have := (Array.getElem?_eq_some_iff.mp foundFin).1
  omega

/-- The withdrawal delay outlasts the run for a key created after finalization. -/
private theorem created_late (h : Setting config checks g split fin pulled anc counted V)
    {v : ValidatorIndex} (created : fin.validators.data.size ≤ v.toNat) :
    ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 <
        w.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat :=
  fun w found => (Internal.window_short h).trans_le
    (Nat.add_le_add_right (Internal.created_exitAfterFin h created w found) _)

/-- The per-key core of the rise for a counted voter created after the finalized state.

The key is absent from the finalized registry, and its rise is on the kept arm.

A key created on C's branch after the split is bounded by its credits and their gains.

The kept arm bounds the key's gain rate, which is the rate that bound reads.

The replays are read at R's epoch. -/
private theorem key_core_created (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (voter : v ∈ Internal.Q counted)
    (created : fin.validators.data.size ≤ v.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm v.toNat = true) :
    Internal.keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  classical
  by_cases absent : split.validators.data.size ≤ v.toNat
  · have activated := Internal.activated_of_quorum h.early voter
    have core := Internal.created_key_ceiling (events := events) (eventsF := eventsF) h tail fromFin
        tailC
      highC endEpochC replayedC activated absent
      (Internal.key_of_kept h v.toNat _ (Nat.min_le_left _ _) kept) (Or.inl kept)
      (Internal.created_band h fromFin (getCurrentEpoch pulled).toNat (Nat.le_succ _) replayedF
          tailC highC
        endEpochC replayedC activated absent)
    unfold Internal.keyCeiling
    omega
  · -- the key is created on the shared segment, and its envelope starts at its first state
    have splitSize : v.toNat < split.validators.data.size := Nat.lt_of_not_le absent
    obtain ⟨c, toC, fromC, cutC, insideC, -, before, floorStart, -⟩ :=
      Internal.created_first_state h fromFin created splitSize
    exact key_core_cap h tail replayed fromFin replayedF tailC highC endEpochC replayedC v
      (Internal.voter_unslashed h v voter) (created_late h created) toC fromC cutC insideC before
      (Or.inr floorStart) kept

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The leak that the counted keys' sync debits on R's branch induce, at their weights.

The keys that are slashed at C and not at the split are counted too, at weight one.

The keys slashed at the split that R's call reads as slashed are counted at weight three.

They are the keys whose sync flows are charged to the reserve.

The bounds include the leak induced by one increment for each key slashed on R's branch.

That allowance is weighted three in the combined bound and one for the keys slashed on C alone. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_syncLeak (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF) :
    (∑ v ∈ (Internal.K4 pulled counted V), Internal.inducedR (pinTerms config pulled anc fin)
      (fromFin.append tail)
          v.toNat) +
      3 * (∑ v ∈ (Internal.K5 counted V), Internal.inducedR (pinTerms config pulled anc fin)
        (fromFin.append tail)
          v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.inducedR (pinTerms config pulled anc fin)
        (fromFin.append tail)
          v.toNat) +
      (∑ v ∈ (Internal.SC pulled counted split), Internal.inducedR (pinTerms config pulled anc fin)
          (fromFin.append tail) v.toNat) +
      3 * (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat) ≤
      (pinTerms config pulled anc fin).syncLeak +
        3 * ((pinTerms config pulled anc fin).slashedR *
          (pinTerms config pulled anc fin).slashLeak) ∧
    (∑ v ∈ (Internal.SC pulled counted split), Internal.inducedR (pinTerms config pulled anc fin)
        (fromFin.append tail) v.toNat) ≤
      (pinTerms config pulled anc fin).syncLeak +
        (pinTerms config pulled anc fin).slashedR *
          (pinTerms config pulled anc fin).slashLeak := by
  classical
  obtain ⟨tailC⟩ := h.toCounted
  -- the replays are read at R's epoch
  obtain ⟨replayedF', replayed'⟩ :=
    Internal.replays_at_pulled tail high endEpoch replayed fromFin replayedF
  have perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement := by
    have := Internal.four_le_perIncrement h
    omega
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  obtain ⟨dKS, -⟩ := Internal.sc_disjoint h
  -- the keys slashed at the split that R's call reads as slashed
  set Kc : Finset ValidatorIndex := Internal.cutKeys config pulled anc fin split with hKc
  have kcSlashed : ∀ v ∈ Kc, ∃ u, split.validators.data[v.toNat]? = some u ∧
      u.slashed = true := by
    intro v member
    have flag := (Finset.mem_filter.mp member).2.1
    cases found : split.validators.data[v.toNat]? with
    | none => simp [found] at flag
    | some u => exact ⟨u, rfl, by simpa [found] using flag⟩
  have dK : Disjoint (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted) Kc := by
    rw [Finset.disjoint_left]
    intro v member inKc
    obtain ⟨u, found, flag⟩ := kcSlashed v inKc
    obtain ⟨w, foundC, flagC⟩ := tailC.slashedPersistence v.toNat u found flag
    exact Internal.classes_unslashed member (by simp [slashedFlagAt, foundC, flagC])
  have dS : Disjoint (Internal.SC pulled counted split) Kc := by
    rw [Finset.disjoint_left]
    intro v member inKc
    obtain ⟨u, found, flag⟩ := kcSlashed v inKc
    simp only [Internal.SC, Finset.mem_filter] at member
    have flagS := member.2.2
    simp [slashedFlagAt, found, flag] at flagS
  -- a key slashed at the split that R reads as slashed withdraws a vector past `fin`
  have kcFrozen : ∀ v ∈ Kc, ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
        w.withdrawableEpoch.toNat := by
    intro v inKc w fw
    have frozen := (Finset.mem_filter.mp inKc).2.2.2
    simp only [fw, Option.any_some, decide_eq_true_eq] at frozen
    exact frozen
  have notKcUnslashed : ∀ v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6
    pulled counted ∪
      Internal.SC pulled counted split, (split.validators.data[v.toNat]?.map (·.slashed)).getD false
        =
        false := by
    intro v notKc
    rcases Finset.mem_union.mp notKc with counted' | member'
    · exact Internal.voter_unslashed h v (Internal.classes_mem_Q counted')
    · simp only [Internal.SC, Finset.mem_filter] at member'
      have flag := member'.2.2
      simp only [slashedFlagAt] at flag
      rw [flag]
      rfl
  have envelope : ∀ v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted ∪
      Internal.SC pulled counted split ∪ Kc, (∀ w, pulled.validators.data[v.toNat]? = some w →
        (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) →
      ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
              Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    intro v member late z inPath
    by_cases beyond : pulled.validators.data.size ≤ v.toNat
    · -- R's registry does not hold the key, so it has no effective balance on R's run
      obtain ⟨q1, q2, -⟩ := Internal.balancePath_endpoint (fromFin.append tail)
        (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) inPath
      obtain ⟨zf, zs⟩ := z
      have same : fork = zf := (Internal.fork_eq_of_run q1 q2 (Nat.le_refl _)).symm
      subst same
      have grows : zs.validators.data.size ≤ pulled.validators.data.size :=
        registryGrows_of_chainSteps q2.chainSteps
      have absent : zs.validators.data[v.toNat]? = none := Array.getElem?_eq_none (by omega)
      have zero : effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat = 0 := by
        simp [effectiveAt, absent]
      rw [zero]
      exact Nat.zero_le _
    · by_cases inFin : v.toNat < fin.validators.data.size
      · by_cases inKc : v ∈ Kc
        · exact Internal.kc_envelope h fromFin tail replayedF' replayed' v inFin (kcSlashed v inKc)
            (Finset.mem_filter.mp inKc).2.2.1 (kcFrozen v inKc) late z inPath
        · have notKc : v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
              Internal.K6 pulled counted ∪ Internal.SC pulled counted split :=
            (Finset.mem_union.mp member).resolve_right inKc
          have unslashed := notKcUnslashed v notKc
          have cleanSplit : ∀ u, split.validators.data[v.toNat]? = some u →
              u.slashed = false := fun u foundU => by
            rw [foundU] at unslashed
            simpa using unslashed
          exact Internal.envelope_of_clean_fin h fromFin tail replayedF' replayed' v (by omega)
            (fun u foundU => Internal.unslashed_of_run fromFin foundU cleanSplit)
            (fun splitSize => Internal.slashed_withdrawable_of_clean h tail v cleanSplit splitSize
              h.finalized) late z inPath
      · have createdV : fin.validators.data.size ≤ v.toNat := by omega
        have slashedLate : v.toNat < split.validators.data.size →
            ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
              anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
                w.withdrawableEpoch.toNat := by
          intro splitSize
          by_cases inKc : v ∈ Kc
          · intro w fw flag
            have rb := (Finset.mem_filter.mp inKc).2.2.1
            rw [Internal.slashedRB_eq] at rb
            simp only [fw, flag, Option.map_some, Option.getD_some, Option.any_some,
              decide_eq_true_eq, true_and] at rb
            exact rb
          · have notKc : v ∈ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
                Internal.K6 pulled counted ∪ Internal.SC pulled counted split :=
              (Finset.mem_union.mp member).resolve_right inKc
            have unslashed := notKcUnslashed v notKc
            exact Internal.slashed_withdrawable_of_clean h tail v (fun u foundU => by
              rw [foundU] at unslashed
              simpa using unslashed) splitSize h.finalized
        exact Internal.envelope_of_clean_fin h fromFin tail replayedF' replayed' v (by omega)
          (fun u foundU => by
            rw [Array.getElem?_eq_none createdV] at foundU
            contradiction) slashedLate late z inPath
  have whole := syncLeak_of_envelope h perPos fromFin tail replayedF' replayed'
    (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted ∪ Internal.SC
      pulled counted split ∪ Kc)
    envelope
  have scOnly := syncLeak_of_envelope h perPos fromFin tail replayedF' replayed'
    (Internal.SC pulled counted split)
    (fun v member => envelope v (Finset.mem_union_left _ (Finset.mem_union_right _ member)))
  have weights := Internal.weighted_le (fun v : ValidatorIndex =>
    Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat) d45 d46 d56
  beta_reduce at weights
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨dK, dS⟩), Finset.sum_union dKS] at whole
  refine ⟨?_, ?_⟩
  · change _ + _ + _ + _ + 3 * (∑ x ∈ Kc, Internal.inducedR (pinTerms config pulled anc fin)
      (fromFin.append tail) (UInt64.toNat x)) ≤ _
    omega
  · omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The per-key core of the rise.

A key of R's registry rises from R to C by at most its rise term.

It also rises by the credits and slacks that `rise` does not read.

The slacks are one increment for a slashing on R's branch.

They are one rounding step for a credit on C's branch or a sync debit on R's.

The bound also includes compounding flows, one rounding unit and the induced leak.

It includes the key's sync debits on the shared segment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_core (h : Setting config checks
  g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (i : ℕ) (inside : i < pulled.validators.data.size)
    (voter : (UInt64.ofNat i : ValidatorIndex) ∈ Internal.Q counted) :
    Internal.keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF i := by
  classical
  -- the replays are read at R's epoch
  obtain ⟨replayedF', replayed'⟩ :=
    Internal.replays_at_pulled tail high endEpoch replayed fromFin replayedF
  -- the key as a validator index
  have below := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early pulled)
  generalize hv : (UInt64.ofNat i : ValidatorIndex) = v at voter
  have hvi : v.toNat = i := by
    rw [← hv]
    exact UInt64.toNat_ofNat_of_lt' below
  subst hvi
  by_cases kept : (pinTerms config pulled anc fin).keptArm v.toNat = true
  · by_cases inFin : v.toNat < fin.validators.data.size
    · exact key_core_cap h tail replayed' fromFin replayedF' tailC highC endEpochC replayedC v
        (Internal.voter_unslashed h v voter)
        (Internal.voter_late h fromFin v voter) Run.nil fromFin (Run.nil_append fromFin) inFin
        (Internal.finalized_start h v.toNat).1 (.inl (Internal.finalized_start h v.toNat).2) kept
    · exact key_core_created h tail replayed' fromFin replayedF' tailC highC endEpochC replayedC
        v voter (Nat.le_of_not_lt inFin) kept
  · exact key_core_headroom h tail fromFin tailC highC v kept

/-- The rise of the other keys, which are active in both. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.cN_le (h : Setting config checks g
  split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    Internal.cN pulled counted V ≤
      ((∑ v ∈ (Internal.K4 pulled counted V), ((pinTerms config pulled anc fin).rise v.toNat +
      (Internal.credC tailC highC v.toNat +
          Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
            eventsC events eventsF v.toNat) + Internal.whistC tailC highC v.toNat +
      (Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat) +
      Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC v.toNat
        +
      Internal.bandR (eventsF ++ events) v.toNat + Internal.bandX fin highC v.toNat)) : ℕ) := by
  have early := h.early
  have term : ∀ v ∈ Internal.K4 pulled counted V, ((Internal.eC counted v : ℤ) - Internal.eR pulled
    v) ≤
      (((pinTerms config pulled anc fin).rise v.toNat +
        (Internal.credC tailC highC v.toNat +
            Internal.keyExtra (pinTerms config pulled anc fin) (fromFin.append tail) tailC highC
              eventsC events eventsF v.toNat) +
        Internal.whistC tailC highC v.toNat + (Internal.syncF events v.toNat + Internal.syncF
          eventsC v.toNat) +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandC tailC highC
          v.toNat +
        Internal.bandR (eventsF ++ events) v.toNat + Internal.bandX fin highC v.toNat : ℕ) : ℤ) :=
          by
    intro v member
    have active : v ∈ Internal.AR pulled := (Finset.mem_filter.mp member).2.1
    obtain ⟨w, found, -⟩ := Internal.active_of_activeVoters early (s := pulled) active
    have core := Internal.key_core h tail high endEpoch replayed fromFin replayedF tailC highC
        endEpochC
      replayedC v.toNat (Array.getElem?_eq_some_iff.mp found).1
      (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp member).2.2.1)
    simp only [Internal.eC, Internal.eR]
    push_cast
    unfold Internal.keyCeiling at core
    zify at core
    omega
  have eq : Internal.cN pulled counted V =
      ∑ v ∈ Internal.K4 pulled counted V, ((Internal.eC counted v : ℤ) - Internal.eR pulled v) := by
    unfold Internal.cN
    rw [← Finset.sum_filter]
    congr 1
    ext v
    simp only [Internal.K4]
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Internal.U, Internal.AC, Internal.AR, Internal.Q, Finset.mem_union]
    tauto
  rw [eq]
  refine le_trans (Finset.sum_le_sum term) (le_of_eq ?_)
  exact (Nat.cast_sum _ _).symm

end Terms

end PinDrift
end EthLib.Consensus.Models.Network

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
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.TermsA

/-! The pin reserve: shared supplies, whistleblower credits and rise. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety PinKeys
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-! ### The supplies of the header terms for the keys of `SC` and `CS`

Each one strengthens a claim on an entry of `pinReserve` that only the keys of the classes make.

The keys of `SC` and `CS` join that claim, and the entry is spent once. -/

/-- The rise of the current keys of K4 and of `SC` fits the rise of the current keys of R.

The keys of `SC` that the rise term of `bud_whistle_of` charges are not in K4.

Each of them is a key of R's registry. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_rise (h : Setting config checks
  g split fin pulled anc counted V) :
    (∑ v ∈ (Internal.K4 pulled counted V), (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        (pinTerms config pulled anc fin).current v.toNat = true,
          (pinTerms config pulled anc fin).rise v.toNat) ≤
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).current i = true,
          (pinTerms config pulled anc fin).rise i := by
  classical
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  have dis : Disjoint (Internal.K4 pulled counted V) ((Internal.sc3a config pulled anc fin counted
    split).filter
      fun v => (pinTerms config pulled anc fin).current v.toNat = true) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_left
          (Finset.subset_union_left.trans Finset.subset_union_left) dSC))
  rw [← Finset.sum_union dis]
  refine voters_sum_le (fun i => (pinTerms config pulled anc fin).rise i) fun v hv => ?_
  rcases Finset.mem_union.mp hv with member | member
  · simp only [Internal.K4, Finset.mem_filter] at member
    obtain ⟨w, found, active⟩ := Internal.active_of_activeVoters h.early (s := pulled) member.2.1
    exact Internal.mem_positions_filter config pulled anc fin found
      (isActiveAt_eq_true_iff.mpr ⟨w, found, active⟩)
  · obtain ⟨-, current⟩ := Finset.mem_filter.mp member
    obtain ⟨w, found, -⟩ := isActiveAt_eq_true_iff.mp
      (show isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true from current)
    exact Internal.mem_positions_filter config pulled anc fin found current

/-- The rise of the upcoming-only keys of K6 and of `SC` fits `joinRise`.

The keys of `SC` that the rise term of `bud_whistle_of` charges are not in K6.

Each of them is a key of R's registry. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_joinRise (h : Setting config
  checks g split fin pulled anc counted V) :
    (∑ v ∈ (Internal.K6 pulled counted) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).joinRise := by
  classical
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  have dis : Disjoint ((Internal.K6 pulled counted).filter fun v =>
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true)
      ((Internal.sc3a config pulled anc fin counted split).filter fun v =>
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_left (Finset.subset_union_right) dSC)))
  rw [← Finset.sum_union dis, Internal.joinRise_eq]
  refine voters_sum_le (fun i => (pinTerms config pulled anc fin).rise i) fun v hv => ?_
  have upcoming : isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
      isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true := by
    rcases Finset.mem_union.mp hv with member | member <;> exact (Finset.mem_filter.mp member).2
  obtain ⟨w, found, -⟩ := isActiveAt_eq_true_iff.mp upcoming.2
  exact Internal.mem_positions_filter config pulled anc fin found upcoming

/-- Late activations, weight 3 for V keys and for new keys, and for the keys of `SC`.

A key of `SC` outside the tight window pays its stake three times and its rise.

It also pays the reward of what its finalized balance exceeds them by, rounded up.

In the tight window `late` is 0, and the sum over `SC` is empty, since its guard is false. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_late (h : Setting config checks
  g split fin pulled anc counted V) :
    3 * (∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        Internal.eR pulled v) +
      (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat =
        true,
        (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).lateB v.toNat = true),
        (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) ≤
      (pinTerms config pulled anc fin).late := by
  classical
  obtain ⟨dSC, dSV⟩ := Internal.sc_disjoint h
  rw [Internal.late_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · rw [ite_eq_left tight]
    have baseTight : 3 * (∑ v ∈ (Internal.VN counted V) with
        (pinTerms config pulled anc fin).lateB v.toNat = true, Internal.eR pulled v) +
        (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat =
          true,
          (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤ 0 := by
      -- Tight: no key of VN or K6 is late.
      have fin_le := UInt64.le_iff_toNat_le.mp h.finalized
      have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
      have bound := (Internal.tight_iff config pulled anc fin).mp tight
      have near := h.near
      have lowerEpoch : (getCurrentEpoch pulled).toNat + 1 ≤
          anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat := by omega
      have none : ∀ v ∈ (Internal.VN counted V) ∪ (Internal.K6 pulled counted),
          (pinTerms config pulled anc fin).lateB v.toNat = false := by
        intro v hv
        by_contra late
        obtain ⟨w, found, -, beyond⟩ := (Internal.lateB_iff config pulled anc fin v.toNat).mp
          (by simpa using late)
        rcases Finset.mem_union.mp hv with hv | hv
        · obtain ⟨w', found', active⟩ := Internal.active_of_activeVoters h.early
            (h.voting v (Finset.mem_filter.mp hv).1).1
          rw [found] at found'
          cases found'
          simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
          have := UInt64.le_iff_toNat_le.mp active.1
          omega
        · have le := Internal.activation_le_of_active h (by omega) (Finset.mem_filter.mp hv).1 found
          omega
      have zeroA : ∑ v ∈ (Internal.VN counted V) with (pinTerms config pulled anc fin).lateB v.toNat
        = true,
          Internal.eR pulled v = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have := none v (Finset.mem_union_left _ (Finset.mem_filter.mp hv).1)
        simp [(Finset.mem_filter.mp hv).2] at this
      have zeroB : ∑ v ∈ (Internal.K6 pulled counted) with
          (pinTerms config pulled anc fin).lateB v.toNat = true,
            (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have := none v (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
        simp [(Finset.mem_filter.mp hv).2] at this
      rw [zeroA, zeroB]
    have empty : ∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).lateB v.toNat = true),
        (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have := (Finset.mem_filter.mp hv).2.1
      rw [tight] at this
      cases this
    omega
  · rw [ite_eq_right tight]
    set A := (Internal.VN counted V).filter fun v => (pinTerms config pulled anc fin).lateB v.toNat
      = true
      with hA
    set B := (Internal.K6 pulled counted).filter
      fun v => (pinTerms config pulled anc fin).lateB v.toNat = true with hB
    set C := (Internal.sc3a config pulled anc fin counted split).filter fun v =>
      (pinTerms config pulled anc fin).tight = false ∧
        (pinTerms config pulled anc fin).lateB v.toNat = true with hC
    have apartAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro v hv hk
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2.2
        (h.voting v (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1).1
    have apartAC : Disjoint A C :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
            (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSV)))
    have apartBC : Disjoint B C :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_left Finset.subset_union_right
            (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSC)))
    have growA : 3 * ∑ v ∈ A, Internal.eR pulled v ≤
        ∑ v ∈ A, (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ =>
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    have growB : ∑ v ∈ B, (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)
      ≤
        ∑ v ∈ B, (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) :=
      Finset.sum_le_sum fun v _ => Nat.le_add_right _ _
    have joined : ∑ v ∈ A, (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat
      +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) +
        ∑ v ∈ B, (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) +
        ∑ v ∈ C, (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) ≤
        ∑ i ∈ (pinTerms config pulled anc fin).positions.filter
          (fun i => (pinTerms config pulled anc fin).lateB i = true),
            (3 * balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
              3 * ((balanceAt fin i - balanceAt pulled i -
            (pinTerms config pulled anc fin).rise i +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) := by
      rw [← Finset.sum_union apartAB, ← Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨apartAC, apartBC⟩)]
      refine voters_sum_le (fun i => 3 * balanceAt pulled i +
        (pinTerms config pulled anc fin).rise i + 3 * ((balanceAt fin i - balanceAt pulled i -
            (pinTerms config pulled anc fin).rise i +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) fun v hv => ?_
      have flag : (pinTerms config pulled anc fin).lateB v.toNat = true := by
        rcases Finset.mem_union.mp hv with hv | hv
        · rcases Finset.mem_union.mp hv with hv | hv <;>
            exact (Finset.mem_filter.mp hv).2
        · exact (Finset.mem_filter.mp hv).2.2
      obtain ⟨w, found, -⟩ := (Internal.lateB_iff config pulled anc fin v.toNat).mp flag
      exact Internal.mem_positions_filter config pulled anc fin found flag
    omega

/-- K6 keys and `SC` keys of R's registry that are not yet eligible at R: their stake and rise.

A key of `SC` also pays the reward of what its finalized balance exceeds them by, rounded up.

In the tight window `pendingR` is 0, and the sum over `SC` is empty, since its guard is false. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_pendingR (h : Setting config
  checks g split fin pulled anc counted V) :
    (∑ v ∈ (Internal.K6 pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat =
      true,
      (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).pendingRB v.toNat = true),
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) ≤
      (pinTerms config pulled anc fin).pendingR := by
  classical
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  rw [Internal.pendingR_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · rw [ite_eq_left tight]
    have baseTight : (∑ v ∈ (Internal.K6 pulled counted) with
        (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤ 0 := by
      have fin_le := UInt64.le_iff_toNat_le.mp h.finalized
      have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
      have bound := (Internal.tight_iff config pulled anc fin).mp tight
      have near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := h.near
      apply Nat.le_of_eq
      apply Finset.sum_eq_zero
      intro v hv
      exfalso
      have hv' := Finset.mem_filter.mp hv
      obtain ⟨w, found, -, far⟩ := (Internal.pendingRB_iff config pulled anc fin v.toNat).mp hv'.2
      have le := Internal.activation_le_of_active h (by omega) (Finset.mem_filter.mp hv'.1).1 found
      have farNat : w.activationEpoch.toNat = 2 ^ 64 - 1 := by rw [far]; rfl
      have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots counted
      have farValue : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
    have empty : ∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).pendingRB v.toNat = true),
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      have := (Finset.mem_filter.mp hv).2.1
      rw [tight] at this
      cases this
    omega
  · rw [ite_eq_right tight]
    set K := (Internal.K6 pulled counted).filter
      fun v => (pinTerms config pulled anc fin).pendingRB v.toNat = true with hK
    set C := (Internal.sc3a config pulled anc fin counted split).filter fun v =>
      (pinTerms config pulled anc fin).tight = false ∧
        (pinTerms config pulled anc fin).pendingRB v.toNat = true with hC
    have apart : Disjoint K C :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_left Finset.subset_union_right
            (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSC)))
    have grow : ∑ v ∈ K, (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat) ≤
        ∑ v ∈ K, (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) :=
      Finset.sum_le_sum fun v _ => Nat.le_add_right _ _
    refine Nat.le_trans (Nat.add_le_add_right grow _) ?_
    rw [← Finset.sum_union apart]
    refine voters_sum_le (fun i => balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
      3 * ((balanceAt fin i - balanceAt pulled i -
            (pinTerms config pulled anc fin).rise i +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) fun v hv => ?_
    have flag : (pinTerms config pulled anc fin).pendingRB v.toNat = true := by
      rcases Finset.mem_union.mp hv with member | member
      · exact (Finset.mem_filter.mp member).2
      · exact (Finset.mem_filter.mp member).2.2
    obtain ⟨w, found, -⟩ := (Internal.pendingRB_iff config pulled anc fin v.toNat).mp flag
    exact Internal.mem_positions_filter config pulled anc fin found flag

/-- No key of the split's registry is slashed on C's branch and withdrawable at R.

Here withdrawable means by the finalized epoch.

Both records are unslashed before C's slashing, and the key is unslashed at R.

If the split has no exit for it, C's slashing assigns one, and a run never charges an exit twice.

Otherwise R's withdrawable epoch is the split's, so the key is retired at the split.

A retired key stays unslashed on C's run. -/
private theorem sc3a_unwithdrawn (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} {s w u : Validator} (foundS : split.validators.data[i]? = some s)
    (foundP : pulled.validators.data[i]? = some w)
    (foundC : counted.validators.data[i]? = some u)
    (cleanS : s.slashed = false) (slashedC : u.slashed = true) (cleanP : w.slashed = false)
    (settled : w.withdrawableEpoch.toNat ≤ anc.finalizedCheckpoint.epoch.toNat) : False := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨tailR⟩ := h.toPulled
  obtain ⟨tailC⟩ := h.toCounted
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  obtain ⟨uAssigned, -⟩ := tailC.newly_slashed_withdrawableEpoch h.caps.activation
    h.caps.compounding h.early (Internal.Setting.delay h) i s u foundS foundC cleanS slashedC
  by_cases unset : s.exitEpoch = FAR_FUTURE_EPOCH
  · obtain ⟨c, member, index, -⟩ := tailC.departure_charge_of_assigned i s u foundS foundC unset
      uAssigned
    exact Internal.no_charge_of_settled h tailC (Array.getElem?_eq_some_iff.mp foundS).1 foundP
      settled c
      member index
  · have kept := Internal.kept_run (rf.append rs) h.genesis h.fulu tailR h.early
    obtain ⟨-, moved⟩ := kept.withdrawable i s w foundS foundP unset
    have same := congrArg UInt64.toNat (moved.resolve_left (by simp [cleanP]))
    have ordered := UInt64.le_iff_toNat_le.mp
      ((Run.invariant (Genesis.invariant h.genesis) (rf.append rs)).exitsOrdered s
        (Array.mem_of_getElem? foundS))
    have exited : s.exitEpoch.toNat ≤ (getCurrentEpoch split).toNat := by omega
    have withdrawn : s.withdrawableEpoch.toNat ≤ (getCurrentEpoch split).toNat := by omega
    have clean := (Run.retired_validator tailC h.caps.activation h.caps.compounding h.early i s u
      foundS foundC (UInt64.le_iff_toNat_le.mpr exited) cleanS
      (UInt64.le_iff_toNat_le.mpr withdrawn)).1
    simp [slashedC] at clean

/-- A key of `sc3a` is active at R or at R's next epoch.

Outside the tight window it can instead be late or pending.

In the tight window C's epoch is in the shared window, so R activates the key by then.

Outside it, an exit by R's next epoch is a slashing on R's branch, which `slashedRB` counts.

Otherwise `exitedSlashable` counts the exit.

Or the key withdraws by the finalized epoch, which C's slashing excludes.

A key that exits after R's next epoch activates after it.

Its eligibility is then late or pending. -/
private theorem sc3a_class (h : Setting config checks g split fin pulled anc counted V)
    {v : ValidatorIndex} (member : v ∈ Internal.sc3a config pulled anc fin counted split) :
    isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true ∨
      isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true ∨
      ((pinTerms config pulled anc fin).tight = false ∧
        ((pinTerms config pulled anc fin).lateB v.toNat = true ∨
          (pinTerms config pulled anc fin).pendingRB v.toNat = true)) := by
  classical
  obtain ⟨memberSC, ⟨notRB, notX⟩, activeC⟩ := Finset.mem_filter.mp member
  obtain ⟨-, flagC, flagS⟩ := Finset.mem_filter.mp memberSC
  obtain ⟨u, foundU, slashedU⟩ : ∃ u, counted.validators.data[v.toNat]? = some u ∧
      u.slashed = true := by
    simpa [slashedFlagAt, Option.map_eq_some_iff] using flagC
  obtain ⟨s, foundS, cleanS⟩ : ∃ s, split.validators.data[v.toNat]? = some s ∧
      s.slashed = false := by
    simpa [slashedFlagAt, Option.map_eq_some_iff] using flagS
  obtain ⟨rp⟩ := h.toPulled
  obtain ⟨w, found⟩ : ∃ w, pulled.validators.data[v.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp foundS).1
      (registryGrows_of_chainSteps rp.chainSteps))⟩
  obtain ⟨finSplit, called, later, near, below, farNat, succNat, finCur⟩ := Internal.setting_epochs
    h
  have rActive : ∀ e : Epoch, isActiveAt pulled e v.toNat = true ↔
      (w.activationEpoch.toNat ≤ e.toNat ∧ e.toNat < w.exitEpoch.toNat) := by
    intro e
    simp [isActiveAt, found, isActiveValidator, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · -- In the tight window C's epoch is in the shared window, so R activates the key by then.
    have bound := (Internal.tight_iff config pulled anc fin).mp tight
    have shared := Internal.activity_shared h (e := getCurrentEpoch counted) (by omega) v.toNat
    have atR := shared.trans activeC
    by_cases same : (getCurrentEpoch counted).toNat = (getCurrentEpoch pulled).toNat
    · rw [UInt64.toNat_inj.mp same] at atR
      exact .inl atR
    · rw [show getCurrentEpoch counted = getCurrentEpoch pulled + 1 from
        UInt64.toNat_inj.mp (by rw [succNat]; omega)] at atR
      exact .inr (.inl atR)
  · have loose : (pinTerms config pulled anc fin).tight = false := by simpa using tight
    have bound : anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
        (getCurrentEpoch pulled).toNat + 1 := by
      have := mt (Internal.tight_iff config pulled anc fin).mpr tight
      omega
    by_cases aR : isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true
    · exact .inl aR
    by_cases aR1 : isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true
    · exact .inr (.inl aR1)
    refine .inr (.inr ⟨loose, ?_⟩)
    have notR1 := mt (rActive _).mpr aR1
    by_cases exited : w.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1
    · -- An exit by R's next epoch is held by a slashing, or by `exitedSlashable`.
      exfalso
      by_cases slashedW : w.slashed = true
      · exact notRB (Internal.slashedRB_of_newly_slashed h foundS found cleanS slashedW)
      · have cleanW : w.slashed = false := by simpa using slashedW
        have settled : w.withdrawableEpoch.toNat ≤ anc.finalizedCheckpoint.epoch.toNat := by
          by_contra late
          apply notX
          simp only [PinTerms.exitedSlashable, found, Option.map_some, Option.getD_some, cleanW,
            Option.any_some]
          simp
          omega
        exact sc3a_unwithdrawn h foundS found foundU cleanS slashedU cleanW settled
    · -- The key activates after R's next epoch.
      have afterA : (getCurrentEpoch pulled).toNat + 1 < w.activationEpoch.toNat := by
        by_contra early
        apply notR1
        rw [succNat]
        exact ⟨by omega, by omega⟩
      exact Internal.late_or_pending h found bound afterA

/-- The charged keys of `SC` are current, upcoming-only, late or pending, and each pays that entry.

A key of `SC` outside the tight window that is late or pending pays its stake and its rise there.

A key is active at R, or active at the next epoch only.

Otherwise its activation is past the delay, or its eligibility is past the epoch.

In the tight window the last two cases are empty. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sc_3a_split (h : Setting config
  checks g split fin pulled anc counted V) :
    ∑ v ∈ Internal.sc3a config pulled anc fin counted split,
        ((pinTerms config pulled anc fin).rise v.toNat +
          (if (pinTerms config pulled anc fin).tight = false ∧
              (pinTerms config pulled anc fin).lateB v.toNat = true then
            3 * balanceAt pulled v.toNat +
              3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
                (pinTerms config pulled anc fin).rise v.toNat +
                ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) else 0) +
          (if (pinTerms config pulled anc fin).tight = false ∧
              (pinTerms config pulled anc fin).pendingRB v.toNat = true then
            balanceAt pulled v.toNat +
              3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
                (pinTerms config pulled anc fin).rise v.toNat +
                ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) else 0)) ≤
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        (pinTerms config pulled anc fin).current v.toNat = true,
          (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).lateB v.toNat = true),
        (3 * Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) +
      (∑ v ∈ (Internal.sc3a config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).pendingRB v.toNat = true),
        (Internal.eR pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v member => ?_
  have cls := sc3a_class h member
  have current : (pinTerms config pulled anc fin).current v.toNat =
      isActiveAt pulled (getCurrentEpoch pulled) v.toNat := rfl
  rw [current]
  unfold Internal.eR
  have arith : ∀ (r b c : ℕ) (C U L P : Prop) [Decidable C] [Decidable U] [Decidable L]
      [Decidable P], (C ∨ U ∨ L ∨ P) →
      r + (if L then 3 * b + 3 * c else 0) + (if P then b + 3 * c else 0) ≤
        (if C then r else 0) + (if U then r else 0) + (if L then 3 * b + r + 3 * c else 0) +
          (if P then b + r + 3 * c else 0) := by
    intro r b c C U L P _ _ _ _ cover
    by_cases hC : C <;> by_cases hU : U <;> by_cases hL : L <;> by_cases hP : P <;>
      simp [hC, hU, hL, hP] at cover ⊢ <;> omega
  refine arith _ _ _ _ _ _ _ ?_
  by_cases hC : isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true
  · exact .inl hC
  · have hC' : isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false := by simpa using hC
    by_cases hU : isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true
    · exact .inr (.inl ⟨hC', hU⟩)
    · rcases cls with c | u | ⟨t, l | p⟩
      · exact absurd c hC
      · exact absurd u hU
      · exact .inr (.inr (.inl ⟨t, l⟩))
      · exact .inr (.inr (.inr ⟨t, p⟩))

/-- The whistleblower reward of the keys of `SC` that R slashes, at R's effective balance and rise.

Each key reads the quotient of its balance and rise, and the quotient of an increment rounded up.

`bud_branchR` pays it and `bud_whistle_of` charges it. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.scSlashedReward (config : Config)
    (pulled anc fin counted split : BeaconState preset fork) : ℕ :=
  ∑ v ∈ (Internal.SC pulled counted split).filter
      (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
    (max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
        (balanceAt fin v.toNat) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- A key off the kept arm rises by its whole headroom to the largest cap.

Within the withdrawal delay, the kept arm fails only at the gain test, which `lowRate` repeats.

So `capFor` reads the largest cap. -/
private theorem rise_of_notKept (h : Setting config checks g split fin pulled anc counted V) (i : ℕ)
    (notKept : ¬ (pinTerms config pulled anc fin).keptArm i = true) :
    (pinTerms config pulled anc fin).rise i =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat - balanceAt pulled i := by
  have shallow := h.shallow
  unfold pinTerms at notKept ⊢
  simp only at notKept ⊢
  rw [ite_eq_right notKept]
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at notKept
  rw [ite_eq_right]
  intro low
  exact notKept shallow (of_decide_eq_true (Bool.and_eq_true_iff.mp low).2)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that a run from the finalized state creates has a first state on the run.

At that state its effective balance is within the floor of its balance, and it is unslashed.

Before it the key is absent from the path, so its effective balance is zero.

A state of the run that lacks the key is no later than the first state.

A step that appends a key leaves it unassigned, so the first state is where the key is created. -/
private theorem created_first_state (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    {v : ValidatorIndex} (created : fin.validators.data.size ≤ v.toNat)
    (inside : v.toNat < e.validators.data.size) :
    ∃ (c : BeaconState preset fork) (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
      (fromC : Run config checks ⟨fork, c⟩ ⟨fork, e⟩), toC.append fromC = run ∧
      v.toNat < c.validators.data.size ∧
      (∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false) ∧
      (∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p v.toNat = 0) ∧
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
      ∀ (d : BeaconState preset fork) (toD : Run config checks ⟨fork, fin⟩ ⟨fork, d⟩)
        (restD : Run config checks ⟨fork, d⟩ ⟨fork, e⟩), toD.append restD = run →
        ¬ v.toNat < d.validators.data.size →
        (getCurrentEpoch d).toNat ≤ (getCurrentEpoch c).toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  -- the first state of the run that holds the key
  obtain ⟨m, n, pre0, step, post0, cutFlip, absentM, presentN⟩ := Run.split_at_flip run
    (fun s : ForkedBeaconState preset => v.toNat < s.state.validators.data.size)
    (by simpa using created) inside
  have forkN : fork = n.fork := (Internal.fork_eq_of_run (pre0.snoc step) post0 (Nat.le_refl
    _)).symm
  have electra : .pectra ≤ m.fork :=
    Nat.le_trans (Nat.le_trans (by decide) h.fulu) (fork_le_of_chainSteps pre0.chainSteps)
  obtain ⟨fork, ns⟩ := n
  subst forkN
  simp only at presentN
  have sizeM : ¬ v.toNat < m.state.validators.data.size := absentM
  obtain ⟨vn, foundN⟩ : ∃ vn, ns.validators.data[v.toNat]? = some vn :=
    ⟨_, Array.getElem?_eq_getElem presentN⟩
  -- a step that appends the key leaves it unassigned, so it is funded and unslashed there
  obtain ⟨far, -⟩ := Step.new_validators_unassigned step h.early electra v.toNat vn
    (Nat.le_of_not_lt sizeM) foundN
  have finite : getCurrentEpoch ns < FAR_FUTURE_EPOCH :=
    UInt64.lt_iff_toNat_lt.mpr (by
      have := getCurrentEpoch_succ_lt_farFuture h.twoSlots ns
      omega)
  obtain ⟨unassigned, -⟩ := EthLib.Consensus.Internal.run_eligible_balance
    (toFin.append (pre0.snoc step)) h.genesis h.caps.activation h.caps.compounding h.aligned
    h.early finite
  obtain ⟨⟨b, foundB, le⟩, -, clean⟩ := unassigned v.toNat vn foundN far
  -- the key is absent at each state of the path before the first state
  have before : ∀ p ∈ (pre0.snoc step).balancePath, p = ⟨fork, ns⟩ ∨ effectiveAt p v.toNat = 0 := by
    intro p member
    obtain ⟨r1, r2, cutP⟩ := Internal.balancePath_endpoint (pre0.snoc step)
      (Run.nil : Run config checks ⟨fork, ns⟩ ⟨fork, ns⟩) (Nat.le_refl _) member
    rcases Run.prefix_snoc r1 r2 pre0 step cutP with ⟨same, joined⟩ | ⟨r', cutR⟩
    · exact Or.inl same
    · refine Or.inr ?_
      have grows := registryGrows_of_chainSteps r'.chainSteps
      have absent : p.state.validators.data[v.toNat]? = none :=
        Array.getElem?_eq_none (by omega)
      simp [effectiveAt, absent]
  refine ⟨ns, pre0.snoc step, post0, cutFlip.symm, presentN, fun u found => ?_, before, ?_, ?_⟩
  · rw [foundN] at found
    cases found
    exact clean
  · -- the effective balance of a key within its balance is within the floor of the balance
    have aligned := FloorTrace.effective_aligned (toFin.append (pre0.snoc step)) h.genesis
      h.aligned v.toNat
    have within : effectiveAt (⟨fork, ns⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, ns⟩ : ForkedBeaconState preset) v.toNat := by
      simp only [effectiveAt, actualBalanceAt, foundN, foundB, Option.map_some, Option.getD_some]
      exact UInt64.le_iff_toNat_le.mp le
    have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat within
    rw [aligned] at rounded
    simpa using rounded
  · -- a state without the key is before the first state, since the registry only grows
    intro d toD restD cutD absentD
    rcases Run.prefix_total toD restD (pre0.snoc step) post0 cutD cutFlip.symm with
      ⟨r, -⟩ | ⟨r, -⟩
    · exact UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r.chainSteps)
    · exact absurd (Nat.lt_of_lt_of_le presentN (registryGrows_of_chainSteps r.chainSteps)) absentD

/-- A key's effective balance at a state of a run is at most the largest on the run's balance path.

The state is the end of a prefix of the run, so the path holds it. -/
private theorem effective_le_foldl_max {x y : ForkedBeaconState preset}
    (run : Run config checks x y) (i : ℕ) {m : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) (cut : pre.append post = run) :
    effectiveAt m i ≤ (run.balancePath.map fun z => effectiveAt z i).foldl max 0 := by
  obtain ⟨front, atEnd⟩ := Run.balancePath_last pre
  have path := Run.balancePath_append pre post
  rw [cut] at path
  have member : m ∈ run.balancePath := by
    rw [path, atEnd]
    simp
  have mapped : effectiveAt m i ∈ run.balancePath.map fun z => effectiveAt z i :=
    List.mem_map.mpr ⟨_, member, rfl⟩
  rw [List.foldl_max_eq_max (List.ne_nil_of_mem mapped)]
  exact Nat.le_trans (List.le_max_of_mem mapped) (Nat.le_max_right _ _)

/-- A key's slashing slack and the downward band fit an increment. -/
private theorem slashW_add_downwardBand_le
    (h : Setting config checks g split fin pulled anc counted V) (i : ℕ) :
    Internal.slashW (pinTerms config pulled anc fin) i + preset.downwardBand ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  unfold Internal.slashW; split <;> first | exact h.facts.slashBand | simpa using
    (Internal.PinPresetFacts.below h.facts).le

/-- A replay of a run that ends by R's epoch, read at R's epoch.

The horizon of the replay does not change the events of such a run. -/
private theorem replay_at_pulled (pulled : BeaconState preset fork)
    {u w : ForkedBeaconState preset} (run : Run config checks u w) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (ending : getCurrentEpoch w.state ≤ getCurrentEpoch pulled)
    {events : List (BalanceEvent preset)} (replayed : run.balanceEvents high = .ok events) :
    run.balanceEvents (getCurrentEpoch pulled).toNat = .ok events := by
  have endingNat := UInt64.le_iff_toNat_le.mp ending
  rw [DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le run (localHigh := high)
    (by omega) (by omega)]
  exact replayed

/-- The pin's `high` of a key, with its depth and its due partials read out. -/
private theorem high_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i : ℕ) :
    (pinTerms config pulled anc fin).high i =
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((11 * (pinTerms config pulled anc fin).gainRate i + 9) / 10 + 3 +
            (pinTerms config pulled anc fin).leak i) +
        (PinTerms.dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1)) := by
  dsimp only [pinTerms]
  simp only [electra, ↓reduceDIte]
  rfl

/-- The leak at a key's largest effective balance on a run is the pin's leak and its induced leak.

The key is not withdrawable at R's next epoch, so `inducedR` charges the difference. -/
private theorem leakAt_foldl_le (config : Config) (pulled anc fin : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (run : Run config checks x y) (i : ℕ)
    (notWithdrawn : (pinTerms config pulled anc fin).withdrawnRB i = false) :
    (pinTerms config pulled anc fin).depthFin * (pinTerms config pulled anc fin).leakAt
        ((run.balancePath.map fun z => effectiveAt z i).foldl max 0) i ≤
      (pinTerms config pulled anc fin).depthFin * (pinTerms config pulled anc fin).leak i +
        Internal.inducedR (pinTerms config pulled anc fin) run i := by
  rw [Internal.inducedR_of_not_withdrawn _ _ _ notWithdrawn, ← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by
    show _ ≤ (pinTerms config pulled anc fin).leakAt ((pinTerms config pulled anc fin).ebUp i) i + _
    omega)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a cut key at the split is bounded from an anchor state of R's run that holds it.

The key is slashed on R's branch.

`floor` is the floor of its balance from each state after the anchor.

The floors give a ceiling on its balance along the run.

The ceiling bounds its effective balance at the split, up to a downward band.

The slash and the band fit one increment.

With a sync debit the rounding of `H` adds a second increment.

Without one nothing is induced, since the effective balance stays within `ebUp`.

`pathEnv` holds that bound before the anchor.

`start` bounds the anchor by its balance when the anchor is no earlier than the split's epoch. -/
private theorem cut_balance_core (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex)
    (hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (insideC : v.toNat < c.validators.data.size)
    (floor : ∀ {zs : BeaconState preset fork} (_ : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) {evs : List (BalanceEvent preset)},
      r2.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + Internal.slashW (pinTerms config pulled anc fin)
            v.toNat)
    (start : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch c).toNat →
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat + preset.downwardBand)
    (startEnv : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (pathEnv : ∀ p ∈ toC.balancePath, p ≠ ⟨fork, c⟩ → effectiveAt p v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat)
    (notWithdrawn : (pinTerms config pulled anc fin).withdrawnRB v.toNat = false) :
    balanceAt split v.toNat ≤ balanceAt pulled v.toNat +
      (pinTerms config pulled anc fin).rise v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      (if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) +
      (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have capSplit : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat :=
    Internal.cap_le_cap_of_run h.caps toPulled h.early v.toNat
  -- the largest effective balance on R's run
  obtain ⟨M, hM⟩ : ∃ M, M = ((fromFin.append tail).balancePath.map
      fun z => effectiveAt z v.toNat).foldl max 0 := ⟨_, rfl⟩
  obtain ⟨Df, hDf⟩ : ∃ Df, Df = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat :=
    ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = Internal.slashW (pinTerms config pulled anc fin) v.toNat := ⟨_, rfl⟩
  -- the ceiling on the balance at each state of the run from the anchor
  obtain ⟨Bc, hBc⟩ : ∃ Bc, Bc = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset)
        v.toNat + (Df * (pinTerms config pulled anc fin).leakAt M v.toNat +
          (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
            PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1))) +
      ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
        v.toNat)).sum + W) :=
    ⟨_, rfl⟩
  have ceil : ∀ z ∈ fromC.balancePath,
      min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤ Bc := by
    intro z member
    have inFull : z ∈ (fromC.append tail).balancePath := by
      rw [Run.balancePath_append]
      exact List.mem_append_left _ member
    have := Internal.path_ceiling h fromFin tail high endEpoch replayedF replayed v W M
      (fun pre post cut => hM ▸ effective_le_foldl_max (fromFin.append tail) v.toNat pre post cut)
      toC fromC cutC insideC
      (fun {_} r1 r2 _ {evs} ev => by
        have ev' := replay_at_pulled pulled r2 high endEpoch (UInt64.le_refl _) ev
        rw [hWdef]
        exact floor r1 r2 ev') z inFull
    rw [hBc, hDf]
    omega
  have capped : ∀ z ∈ fromC.balancePath, effectiveAt z v.toNat ≤ PinTerms.capAt z v.toNat := by
    intro z member
    obtain ⟨zs, rfl, ⟨r1⟩, -⟩ := Internal.balancePath_state fromC member
    exact Internal.effective_le_cap_at (toFin.append (toC.append r1)) h.genesis h.caps h.early
      v.toNat
  have capCeil : ∀ z ∈ fromC.balancePath,
      PinTerms.capAt z v.toNat ≤ PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset)
        v.toNat := by
    intro z member
    obtain ⟨zs, rfl, -, ⟨r2⟩⟩ := Internal.balancePath_state fromC member
    exact Nat.le_trans (Internal.cap_le_cap_of_run h.caps r2 h.early v.toNat) capSplit
  obtain ⟨-, sameC, afterC, -⟩ := Internal.effective_ceiling_flip h fromC
    (Run.invariant h.genesis.invariant (toFin.append toC)) v.toNat insideC Bc
    (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) capped capCeil ceil
  -- the effective balance at the split is within a downward band of the ceiling
  have ebBound : balanceAt split v.toNat ≤ Bc + preset.downwardBand := by
    by_cases flat : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch c).toNat
    · have eq := sameC flat
      have startB := start flat
      have atC := ceil ⟨fork, c⟩ (by
        obtain ⟨front, atHead⟩ := Run.balancePath_head fromC
        rw [atHead]
        exact List.mem_cons_self)
      have capAtC := Internal.effective_le_cap_at (toFin.append toC) h.genesis h.caps h.early
        v.toNat
      change effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤ _
      omega
    · exact afterC (by omega)
  have hdf : (pinTerms config pulled anc fin).depthFin = Df := by rw [hDf]; rfl
  obtain ⟨H, hH⟩ : ∃ H, H = (pinTerms config pulled anc fin).high v.toNat :=
    ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate v.toNat := ⟨_, rfl⟩
  have hHeq : H = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      Df * ((11 * q + 9) / 10 + 3 + (pinTerms config pulled anc fin).leak v.toNat) +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) := by
    rw [hH, hq, hDf]
    exact high_eq config pulled anc fin electra v.toNat
  obtain ⟨ind, hind⟩ : ∃ ind, ind =
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat := ⟨_, rfl⟩
  have induced : Df * (pinTerms config pulled anc fin).leakAt M v.toNat ≤
      Df * (pinTerms config pulled anc fin).leak v.toNat + ind := by
    rw [hind, ← hdf, hM]
    exact leakAt_foldl_le config pulled anc fin (fromFin.append tail) v.toNat notWithdrawn
  have gap : Bc ≤ H + (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat + ind + W) :=
    by
    unfold Internal.syncD
    rw [hBc, hHeq, Nat.mul_add Df _ _]
    omega
  have alignedC : balanceAt split v.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    FloorTrace.effective_aligned (toFin.append fromFin) h.genesis h.aligned v.toNat
  have cappedC : balanceAt split v.toNat ≤
      (pinTerms config pulled anc fin).capFor v.toNat :=
    Nat.le_trans (Internal.effective_le_cap_pulled h fromFin tail v.toNat)
      (Internal.capAt_le_capFor config pulled anc fin v.toNat (Internal.capAt_le_capMax h.caps
        electra v.toNat))
  have incPos : 1 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.incrementSize
    omega
  have bandSlash : W + preset.downwardBand ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [hWdef]
    exact slashW_add_downwardBand_le h v.toNat
  obtain ⟨s, hs⟩ : ∃ s, s = Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat := ⟨_,
    rfl⟩
  rw [← hind, ← hs]
  by_cases kept : (pinTerms config pulled anc fin).keptArm v.toNat = true
  · rw [Internal.rise_kept config pulled anc fin v.toNat hH kept]
    have alignedLe : ∀ x, balanceAt split v.toNat ≤ x →
        balanceAt split v.toNat ≤ x - x % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun x le => by
      have := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat le
      rw [alignedC] at this
      simpa using this
    have maxH := Nat.le_max_right (balanceAt fin v.toNat)
      (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    have roundH := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (Nat.le_add_right H preset.downwardBand)
    by_cases sync : 0 < s
    · have bound : balanceAt split v.toNat ≤
          H + (s + ind + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
        omega
      have first := alignedLe _ bound
      have second := Internal.round_add_le (inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (x :=
        H)
        (S := s + ind + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
        (U := preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) (by omega)
        (Or.inr (Or.inl (by omega)))
      rw [ite_eq_left sync]
      omega
    · have s0 : s = 0 := by omega
      have sums : (eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
        v.toNat)).sum =
          0 := by
        unfold Internal.syncD at hs
        omega
      -- with no sync debit the effective balances stay within `ebUp`, so nothing is induced
      have env := Internal.prefix_envelope h fromFin tail high endEpoch replayedF replayed v toC
        (fromC.append tail) (by rw [Run.append_assoc, cutC]) insideC W startEnv
        (fun {zs} pre after cutR {evs} ev => by
          have ev' := replay_at_pulled pulled after high endEpoch (UInt64.le_refl _) ev
          rw [hWdef]
          exact floor pre after ev')
      have memberSplit : (⟨fork, split⟩ : ForkedBeaconState preset) ∈
          (fromFin.append tail).balancePath := by
        obtain ⟨front, atEnd⟩ := Run.balancePath_last fromFin
        rw [Run.balancePath_append, atEnd]
        simp
      have M0 : M ≤ (pinTerms config pulled anc fin).ebUp v.toNat := by
        have mapped : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ∈
            (fromFin.append tail).balancePath.map fun z => effectiveAt z v.toNat :=
          List.mem_map.mpr ⟨_, memberSplit, rfl⟩
        rw [hM, List.foldl_max_eq_max (List.ne_nil_of_mem mapped)]
        refine Nat.max_le.2 ⟨Nat.zero_le _, (List.max_le_iff (List.ne_nil_of_mem mapped)).2 ?_⟩
        intro x hx
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        have full : z ∈ (toC.append (fromC.append tail)).balancePath := by
          rw [Run.append_assoc, cutC]
          exact hz
        rw [Run.balancePath_append] at full
        rcases List.mem_append.mp full with front | later
        · by_cases atC : z = ⟨fork, c⟩
          · subst atC
            have e := env _ (by
              obtain ⟨rest, atHead⟩ := Run.balancePath_head (fromC.append tail)
              rw [atHead]
              exact List.mem_cons_self)
            rw [sums, Nat.div_eq_of_lt
              (by omega : 0 + W < preset.EFFECTIVE_BALANCE_INCREMENT.toNat),
              Nat.mul_zero, Nat.add_zero] at e
            exact e
          · exact pathEnv z front atC
        · have e := env z (List.mem_of_mem_tail later)
          rw [sums, Nat.div_eq_of_lt (by omega : 0 + W < preset.EFFECTIVE_BALANCE_INCREMENT.toNat),
            Nat.mul_zero, Nat.add_zero] at e
          exact e
      have ind0 : ind = 0 := by
        rw [hind, Internal.inducedR_of_not_withdrawn _ _ _ notWithdrawn]
        rw [← hM, Nat.sub_eq_zero_of_le (Internal.leakAt_mono config pulled anc fin v.toNat M0),
          Nat.mul_zero]
      have zeroMod : (balanceAt split v.toNat - preset.EFFECTIVE_BALANCE_INCREMENT.toNat) %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
        Nat.sub_mod_eq_zero_of_mod_eq (by rw [alignedC, Nat.mod_self])
      have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (show balanceAt split v.toNat - preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ H by omega)
      rw [zeroMod, Nat.sub_zero] at rounded
      rw [ite_eq_right (by omega : ¬ 0 < s)]
      omega
  · have headroom := rise_of_notKept h v.toNat kept
    have capped : balanceAt split v.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      Internal.effectiveAt_le_capMax (toFin.append fromFin) h.genesis h.caps h.early v.toNat
    have cappedR : balanceAt pulled v.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      Internal.effectiveAt_le_capMax (toFin.append (fromFin.append tail)) h.genesis h.caps
        h.early v.toNat
    omega

/-- A key that the shared run slashes is bounded by its finalized balance or by R's balance.

The bound by R's balance reads its rise, one increment and the debits and induced leak.

A second increment pays the rounding of the balance when it has a sync debit.

The balance at the split is the key's effective balance at the epoch start, up to the downward band.

A queued partial paid before the finalized state leaves the balance at the finalized one.

Otherwise R's tail takes its penalties and sync debits, and the leak that `rise` reads covers them.

The cut-key part of `bud_branchR`'s body reads the quotient of this bound.

It reads it for each key of `cut_whistle`'s set, and pays the rounding with the debits. -/
private theorem cut_balance_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (member : v ∈ Internal.cutKeys config pulled anc fin split) :
    balanceAt split v.toNat ≤ max (balanceAt fin v.toNat)
      (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) +
        (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
          Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat)) := by
  classical
  obtain ⟨-, flagS, rb, frozenFlag⟩ := Finset.mem_filter.mp member
  have rb' := rb
  rw [Internal.slashedRB_eq] at rb'
  obtain ⟨wP, foundP⟩ : ∃ wP, pulled.validators.data[v.toNat]? = some wP := by
    cases f : pulled.validators.data[v.toNat]? with
    | none => simp [f] at rb'
    | some w => exact ⟨w, rfl⟩
  have slashedP : wP.slashed = true := by simpa [foundP] using (of_decide_eq_true rb').1
  have frozen : (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
      wP.withdrawableEpoch.toNat := by
    simpa [foundP] using frozenFlag
  have half := Internal.depthFin_lt_half h
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have late : (getCurrentEpoch pulled).toNat + 1 < wP.withdrawableEpoch.toNat := by
    omega
  have notWithdrawn : (pinTerms config pulled anc fin).withdrawnRB v.toNat = false := by
    simp only [pinTerms, foundP, Option.any_some, decide_eq_false_iff_not]
    omega
  have hWdb := slashW_add_downwardBand_le h v.toNat
  have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.bandLow
    have := h.facts.incrementSize
    omega
  by_cases inFin : v.toNat < fin.validators.data.size
  · by_cases flat : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch fin).toNat
    · have sameE : getCurrentEpoch split = getCurrentEpoch fin :=
        UInt64.toNat_inj.mp (by omega)
      exact le_max_of_le_left
        (run_same_epoch_effective fromFin h.early sameE v.toNat inFin).le
    · refine le_max_of_le_right (cut_balance_core h fromFin tail high endEpoch replayedF replayed
        v hW (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) fromFin
        (Run.nil_append fromFin) inFin ?_ (fun hle => absurd hle flat)
        (Or.inl ⟨Internal.effective_fin_le_ebUp h v.toNat, Nat.le_refl _⟩)
        (fun p hp ne => by
          have : p = ⟨fork, fin⟩ := by simpa [Run.balancePath] using hp
          exact absurd this ne) notWithdrawn)
      obtain ⟨u, foundU⟩ : ∃ u, fin.validators.data[v.toNat]? = some u :=
        ⟨_, Array.getElem?_eq_getElem inFin⟩
      by_cases sl : u.slashed = true
      · intro r1 r2 evs ev
        have := Internal.slash_floor_from_slashed h v inFin
          (fun u' fu' => by
            rw [foundU] at fu'
            cases fu'
            exact sl) wP foundP frozen late r1 r2 ev
        omega
      · intro r1 r2 evs ev
        exact Internal.slash_floor_across h v (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩)
          inFin
          (fun u' fu' => by
            rw [foundU] at fu'
            cases fu'
            simpa using sl) wP foundP slashedP rb r1 r2 ev
  · -- a key created after the finalized state is anchored at the first state that holds it
    have first := created_first_state h fromFin (v := v) (by omega) (by
      cases f : split.validators.data[v.toNat]? with
      | none => simp [f] at flagS
      | some u => exact (Array.getElem?_eq_some_iff.mp f).1)
    obtain ⟨c, toC, fromC, cutC, insideC, clean, before, startEB, -⟩ := first
    have incPos := h.bands.1
    have remainder := Nat.mod_le (actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    refine le_max_of_le_right (cut_balance_core h fromFin tail high endEpoch replayedF replayed v hW
      toC fromC cutC insideC ?_ (fun _ => by omega) (Or.inr startEB)
      (fun p hp ne => by
        rcases before p hp with eq | zero
        · exact absurd eq ne
        · rw [zero]
          exact Nat.zero_le _) notWithdrawn)
    intro zs r1 r2 evs ev
    exact Internal.slash_floor_across h v toC insideC clean wP foundP slashedP rb r1 r2 ev

/-- A replay inside one epoch whose steps all start past the cutoff records no event.

The run starts at `b`, so each of its steps starts at the epoch of `b` or later.

No landed lemma states this, so `cut_whistle` reads it here, for a cutoff before that epoch. -/
private theorem balanceEvents_late {f : Fork} {b : BeaconState preset f}
    {y : ForkedBeaconState preset} (tail : Run config checks ⟨f, b⟩ y)
    (early : y.fork < .glamsterdam) (same : getCurrentEpoch y.state = getCurrentEpoch b)
    {high : ℕ} (late : high + 1 < (getCurrentEpoch b).toNat) :
    tail.balanceEvents high = .ok [] := by
  refine Run.induction_of_same_epoch (fun _ r => r.balanceEvents high = .ok []) rfl ?_ ?_ tail
    early same
  · intro _ s _ _ _ _ _ pre _ prior
    have started : (getCurrentEpoch b).toNat ≤ (getCurrentEpoch s).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have skipped : ¬ (getCurrentEpoch s).toNat ≤ high + 1 := by omega
    simp [Run.balanceEvents, prior, skipped, pure, Except.pure, bind, Except.bind]
  · intro middle _ _ _ pre _ _ _ _ prior
    have started : (getCurrentEpoch b).toNat ≤ (getCurrentEpoch middle.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have skipped : ¬ (getCurrentEpoch middle.state).toNat ≤ high + 1 := by omega
    simp [Run.balanceEvents, prior, skipped, pure, Except.pure, bind, Except.bind]

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The whistleblower credits of the shared run's last epoch fit the keys that it slashes.

The run `pre` goes from `b` to the split, inside the split's epoch.

A whistleblower credit lands in the proposer's block, so a key of any class can receive it.

Each key slashed along `pre` pays the quotient of its effective balance at the slashing.

That balance is the one at the split.

It changes only at an epoch update, and `pre` is in one epoch.

R's call reads each such key as slashed, since its withdrawable epoch is a slashing vector away.

The sum is over keys that `SC` leaves out, because they are slashed at the split. -/
private theorem cut_whistle (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b) (high : ℕ) (keys : Finset ℕ) :
    ∑ i ∈ keys, Internal.whistC pre high i ≤
      ∑ v ∈ ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter
          (fun v => ((b.validators.data[v.toNat]?).map (·.slashed)).getD false = false ∧
            ((split.validators.data[v.toNat]?).map (·.slashed)).getD false = true ∧
            (pinTerms config pulled anc fin).slashedRB v.toNat = true),
        balanceAt split v.toNat / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  obtain ⟨events, replayed, bounded⟩ := Run.balanceEvents_bounded toB pre h.genesis h.early high
  have scan := Internal.creditScan_sum_le keys id (fun s => decide (s = .slashings)) (fun _ =>
    false) high
    BalanceEvent.credits pre replayed fun e _ _ => by
      simpa [Internal.keyCredit] using Internal.keys_credits_le keys e
  have limits := Internal.slashing_credits_le_limits events fun e member => (bounded e member).1
  have slashings : (events.map fun e =>
      if decide (e.source = .slashings) = true ∨ false = true then e.credits else 0).sum =
      ((events.filter (·.source = .slashings)).map BalanceEvent.credits).sum := by
    simp only [decide_eq_true_eq, Bool.false_eq_true, or_false]
    rw [List.sum_map_ite (fun e : BalanceEvent preset => e.source = .slashings)
      BalanceEvent.credits (fun _ => 0)]
    simp
  refine (scan.trans (slashings.le.trans limits)).trans ?_
  by_cases late : high + 1 < (getCurrentEpoch b).toNat
  · rw [balanceEvents_late pre h.early sameEpoch late] at replayed
    cases replayed
    simp
  have endEpoch : (getCurrentEpoch split).toNat ≤ high + 1 := by rw [sameEpoch]; omega
  let P : ℕ → Prop := fun j => ((b.validators.data[j]?).map (·.slashed)).getD false = false ∧
    ((split.validators.data[j]?).map (·.slashed)).getD false = true ∧
    (pinTerms config pulled anc fin).slashedRB j = true
  let quotient := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  refine (slashing_credits_le toB pre h.genesis h.early h.caps.compounding high endEpoch
    (Finset.range pulled.validators.data.size)
    (fun j => if P j then balanceAt split j / quotient else 0) ?_ replayed).trans ?_
  · intro a a' step contained j inside flip
    obtain ⟨before, after, -⟩ := pre.contains_split step contained
    have rest := (Run.nil.snoc step).append after
    have sameFork : a.fork = fork := Internal.fork_eq_of_run before rest (Nat.le_refl _)
    have size := Nat.lt_of_lt_of_le (Finset.mem_range.mp inside)
      ((after.append toPulled).registryLifecycle.size_le)
    refine ⟨Finset.mem_range.mpr size, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at flip
    obtain ⟨unslashedA, slashedA'⟩ := flip
    rcases foundA : a.state.validators.data[j]? with _ | u
    · simp [effectiveAt, foundA]
    have clean : u.slashed = false := by simpa [foundA] using unslashedA
    obtain ⟨w, foundA', marked⟩ :
        ∃ w, a'.state.validators.data[j]? = some w ∧ w.slashed = true := by
      cases found : a'.state.validators.data[j]? with
      | none => simp [found] at slashedA'
      | some w => exact ⟨w, rfl, by simpa [found] using slashedA'⟩
    obtain ⟨_, foundS, markedS⟩ := after.slashedPersistence j w foundA' marked
    obtain ⟨wP, foundP, markedP⟩ := (after.append toPulled).slashedPersistence j w foundA' marked
    have startB : (getCurrentEpoch b).toNat ≤ (getCurrentEpoch a.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps before.chainSteps)
    have endS : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch split).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps rest.chainSteps)
    have epochB : (getCurrentEpoch b).toNat = (getCurrentEpoch split).toNat := by rw [sameEpoch]
    have withdrawable := ((rest.append toPulled).newly_slashed_withdrawableEpoch h.caps.activation
      h.caps.compounding h.early (Internal.Setting.delay h) j u wP foundA foundP clean markedP).2
    have p : P j := by
      refine ⟨?_, by simp [foundS, markedS], ?_⟩
      · cases foundB : b.validators.data[j]? with
        | none => rfl
        | some v =>
          simp [Internal.unslashed_of_run before foundB (fun z read => by simp_all)]
      · exact Internal.slashedRB_of_withdrawable config pulled anc fin foundP markedP (by omega)
    have sameEpochA : getCurrentEpoch split = getCurrentEpoch a.state :=
      UInt64.toNat_inj.mp (by omega)
    have kept := rest.effectiveKept_of_same_epoch h.early sameEpochA j
      (Array.getElem?_eq_some_iff.mp foundA).1
    have read : balanceAt split j = effectiveAt a j := kept
    simp only [p, ↓reduceIte, quotient, read, sameFork, le_refl]
  · rw [← Finset.sum_filter]
    have round (z : ℕ) (hz : z ∈ (Finset.range pulled.validators.data.size).filter P) :
        (UInt64.ofNat z).toNat = z := by
      have inside := Finset.mem_range.mp (Finset.mem_filter.mp hz).1
      exact UInt64.toNat_ofNat_of_lt'
        (inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early pulled))
    refine Finset.sum_le_sum_of_injOn UInt64.ofNat ?_ ?_ ?_ (fun _ _ _ => Nat.zero_le _)
    · intro x hx y hy same
      rw [← round x hx, ← round y hy, same]
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨inside, px⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, inside, rfl⟩, ?_⟩
      rw [round x hx]
      exact px
    · intro x hx
      rw [round x hx]

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- R1 from the count of its rounding bands.

The slash charges of the classes fit the slashed keys of `branchR`, with the weights of the classes.

The sync part of the proposer credit fits the proposer credit of each epoch.

The flag gain and the unit of each slashed key fit `W`, by `branchR_split`.

The bands of the classes fit the rounded keys of `branchR`, which is the hypothesis `bands`.

The seat holders of `SC` weigh one in `bands`, and take seat slots that no class claims. -/
private theorem bud_branchR_of (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {events eventsF eventsC eventsP : List (BalanceEvent preset)}
    (bands : 3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
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
        ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
          (pinTerms config pulled anc fin).depth *
            preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat +
          preset.SYNC_COMMITTEE_SIZE.toNat *
            (((getCurrentEpoch pulled).toNat + 1) /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
              (getCurrentEpoch fin).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
              (pinTerms config pulled anc fin).depth /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)))) :
    3 * ((pinTerms config pulled anc fin).slashedR *
        (2 * (pinTerms config pulled anc fin).depthFin *
          (pinTerms config pulled anc fin).flagRate)) +
      3 * ((pinTerms config pulled anc fin).slashedR *
        (pinTerms config pulled anc fin).slashLeak) +
      3 * ((pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR) +
      3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        (∑ v ∈ (Internal.K4 pulled counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * (∑ v ∈ (Internal.K5 counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        (∑ v ∈ (Internal.K6 pulled counted),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * Internal.scSlashedReward config pulled anc fin counted split +
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
                (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat else 0) +
        3 * (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          (max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
              (balanceAt fin v.toNat) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
          Internal.slashR (pinTerms config pulled anc fin) v.toNat)) ≤
      (pinTerms config pulled anc fin).branchR := by
  classical
  unfold Internal.scSlashedReward
  obtain ⟨Wh, W, hW, gainW, floorW⟩ := Internal.branchR_split config pulled anc fin
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  have slashes := Internal.weighted_le (A := Internal.K4 pulled counted V) (B := Internal.K5 counted
    V)
    (C := Internal.K6 pulled counted) (fun v => Internal.slashR (pinTerms config pulled anc fin)
      v.toNat) d45 d46
    d56
  -- A cut key is slashed at the split, so it is in no class and not in `SC`.
  have dCut : Disjoint (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted ∪
      Internal.SC pulled counted split) (Internal.cutKeys config pulled anc fin split) :=
    (Internal.cut_disjoint h).symm.mono_left fun v member => by
      simp only [Finset.mem_union] at member ⊢
      tauto
  -- Each cut key is read as slashed, so its slash charge is an increment.
  have cutRB : (Internal.cutKeys config pulled anc fin split).filter
      (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true) =
        Internal.cutKeys config pulled anc fin split :=
    Finset.filter_true_of_mem fun v cut => (Finset.mem_filter.mp cut).2.2.1
  -- A key of `SC` that R slashes takes an increment of `branchR`'s slashed keys.
  --
  -- A key of the classes takes one too, and the two sets are disjoint.
  have slashBound := Internal.slashR_le config pulled anc fin
    (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted ∪ Internal.SC
      pulled counted split ∪
      Internal.cutKeys config pulled anc fin split)
  rw [Finset.sum_union dCut, Finset.sum_union dSC] at slashBound
  have scFloor := floorW (Internal.SC pulled counted split ∪ Internal.cutKeys config pulled anc fin
    split)
  rw [Finset.filter_union, cutRB, Finset.sum_union (Finset.disjoint_of_subset_left
    (Finset.filter_subset _ _) (Finset.disjoint_union_left.mp dCut).2)] at scFloor
  have scReward : ∑ v ∈ (Internal.SC pulled counted split).filter
        (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
      (max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
          (balanceAt fin v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (∑ v ∈ (Internal.SC pulled counted split).filter
          (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
        max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
          (balanceAt fin v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        ∑ v ∈ Internal.SC pulled counted split, Internal.slashR (pinTerms config pulled anc fin)
          v.toNat := by
    have each : ∀ v ∈ (Internal.SC pulled counted split).filter
        (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
        max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
          (balanceAt fin v.toNat) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
              (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
        max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
          (balanceAt fin v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        Internal.slashR (pinTerms config pulled anc fin) v.toNat := fun v hv => by
      have flag := (Finset.mem_filter.mp hv).2
      rw [show Internal.slashR (pinTerms config pulled anc fin) v.toNat =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat by simp [Internal.slashR, flag]]
      exact Nat.add_le_add_left (ceil_div_le _ _) _
    refine (Finset.sum_le_sum each).trans ?_
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) _
  have credit := Nat.mul_le_mul_left (pinTerms config pulled anc fin).depth
    (Internal.syncProposer_le_credit config pulled anc fin)
  simp only [Finset.sum_add_distrib] at *
  rw [hW]
  omega

/-- R1 (branchR): R's credits to V keys since the split, weight 3.

The slashing of a key on R's branch is charged here for the keys of `K4` and `K5`.

So is a sync debit of R that `rise` omits.

The keys of `K4` weigh one, and those of `K5` weigh three.

The surplus of the slash charge pays `flow_split_of`'s slashed term.

`branchR` also holds the unit of each key slashed on R's branch.

R's credits leave out sync events, so `bud_sync` takes them.

The keys of `SC` that R slashes after the split also draw on `branchR`, at weight three.

The `whistleblowerR` term of `pinReserve` pays their reward on C's branch.

The seat holders of `SC` also weigh one, and take seat slots of `branchR` that no class claims.

A key of `K5` that receives a whistleblower credit on `pre` is read at the credits of `pre`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_branchR (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {eventsP : List (BalanceEvent preset)} (replayedP : pre.balanceEvents highC = .ok eventsP) :
    3 * ((pinTerms config pulled anc fin).slashedR *
        (2 * (pinTerms config pulled anc fin).depthFin *
          (pinTerms config pulled anc fin).flagRate)) +
      3 * ((pinTerms config pulled anc fin).slashedR *
        (pinTerms config pulled anc fin).slashLeak) +
      3 * ((pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR) +
      3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        (∑ v ∈ (Internal.K4 pulled counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * (∑ v ∈ (Internal.K5 counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * (∑ v ∈ (Internal.K5 counted V), Internal.whistC pre highC v.toNat) +
        3 * (∑ v ∈ Internal.scCharged pulled counted split tailC, Internal.whistC pre highC v.toNat)
          +
        (∑ v ∈ (Internal.K6 pulled counted),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * Internal.scSlashedReward config pulled anc fin counted split +
        (∑ v ∈ Internal.SC pulled counted split, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ Internal.SC pulled counted split,
          if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
            (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) +
        (∑ v ∈ Internal.scCharged pulled counted split tailC,
          if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
            Internal.syncCr eventsP v.toNat then
            preset.upwardBand else 0) ≤
      (pinTerms config pulled anc fin).branchR +
        -- The cut keys' sync debits and induced leak, paid by `bud_sync` and `bud_syncLeak`.
        3 * (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat)) := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  set q := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hq
  set inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat with hinc
  -- The bands of `bud_branchR_of` are the seats' bands, within the bound of `roundedKeys`.
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have seats := Internal.bands_seats h fromFin tail tailC high highC endEpoch endEpochC toB pre
    sameEpoch
    replayed replayedF replayedC replayedP
  have slots : preset.SLOTS_PER_EPOCH.toNat ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [← depthEq] at seats
  have of := bud_branchR_of h tailC highC pre (seats.trans (Nat.mul_le_mul_left 3
    (Nat.mul_le_mul_left _ ?bandsLe)))
  case bandsLe => omega
  -- One `cut_whistle` reads the credits of `pre` to the keys of `K5` and of `scCharged`.
  obtain ⟨dSC, -⟩ := Internal.sc_disjoint h
  have apart : Disjoint (Internal.K5 counted V) (Internal.scCharged pulled counted split tailC) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_left (fun v member => Finset.mem_union.mpr
        (.inl (Finset.mem_union.mpr (.inr member)))) dSC)
  have whistle := cut_whistle h toB pre sameEpoch highC
    ((Internal.K5 counted V ∪ Internal.scCharged pulled counted split tailC).image UInt64.toNat)
  rw [Finset.sum_image fun a _ b _ same => UInt64.toNat_inj.mp same,
    Finset.sum_union apart] at whistle
  -- Each key that `pre` slashes is a cut key, at most its reserve, increment, seat and debits.
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have each : ∀ v ∈ ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter
      (fun v => ((b.validators.data[v.toNat]?).map (·.slashed)).getD false = false ∧
        ((split.validators.data[v.toNat]?).map (·.slashed)).getD false = true ∧
        (pinTerms config pulled anc fin).slashedRB v.toNat = true),
      v ∈ Internal.cutKeys config pulled anc fin split ∧ balanceAt split v.toNat / q ≤
        (max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
            (balanceAt fin v.toNat) / q + Internal.slashR (pinTerms config pulled anc fin) v.toNat)
              +
          (if 0 < Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat then (inc + q - 1)
            / q else 0) +
          (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat) := by
    intro v member
    obtain ⟨inside, clean, marked, rb⟩ : v ∈ (Finset.range pulled.validators.data.size).image
        UInt64.ofNat ∧ _ ∧ _ ∧ _ := by simpa only [Finset.mem_filter, and_assoc] using member
    -- The step of `pre` that slashes the key starts from a record of it.
    let P : ForkedBeaconState preset → Prop := fun z =>
      ((z.state.validators.data[v.toNat]?).map (·.slashed)).getD false = true
    obtain ⟨m, n, before, step, after, -, notM, atN⟩ :=
      Run.split_at_flip pre P (by simp [P, clean]) marked
    have mFork : m.fork = fork := Internal.fork_eq_of_run before ((Run.nil.snoc step).append after)
      (Nat.le_refl _)
    have startB : (getCurrentEpoch b).toNat ≤ (getCurrentEpoch m.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps before.chainSteps)
    obtain ⟨w, foundN, slashedN⟩ : ∃ w, n.state.validators.data[v.toNat]? = some w ∧
        w.slashed = true := by
      cases found : n.state.validators.data[v.toNat]? with
      | none => simp [P, found] at atN
      | some w => exact ⟨w, rfl, by simpa [P, found] using atN⟩
    obtain ⟨u, foundM, unslashedM⟩ : ∃ u, m.state.validators.data[v.toNat]? = some u ∧
        u.slashed = false := by
      cases found : m.state.validators.data[v.toNat]? with
      | some u => exact ⟨u, rfl, by simpa [P, found] using notM⟩
      | none =>
        have finite : getCurrentEpoch m.state < FAR_FUTURE_EPOCH := by
          refine UInt64.lt_iff_le_and_ne.mpr ⟨UInt64.le_iff_toNat_le.mpr ?_,
            getCurrentEpoch_ne_farFuture h.twoSlots m.state⟩
          have := (getCurrentEpoch m.state).toNat_lt
          have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
          omega
        obtain ⟨_, recorded, -⟩ := step.slashed_activated
          (by rw [mFork]; exact Nat.le_trans (by decide) h.fulu)
          (Nat.lt_of_le_of_lt (fork_le_of_chainSteps after.chainSteps) h.early)
          h.caps.activation h.caps.compounding (Internal.Setting.delay h) finite v.toNat
          (fun u read => by simp [found] at read) (by simp [found, foundN, slashedN])
        simp [found] at recorded
    obtain ⟨wP, foundP, slashedP⟩ :=
      (after.append toPulled).slashedPersistence v.toNat w foundN slashedN
    have withdrawable := ((((Run.nil.snoc step).append after).append toPulled)
      |>.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding h.early
        (Internal.Setting.delay h)
        v.toNat u wP foundM foundP unslashedM slashedP).2
    have cut : v ∈ Internal.cutKeys config pulled anc fin split := by
      refine Finset.mem_filter.mpr ⟨inside, marked, rb, ?_⟩
      have key : (getCurrentEpoch fin).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          wP.withdrawableEpoch.toNat := by
        have same : (getCurrentEpoch split).toNat = (getCurrentEpoch b).toNat := by
          rw [sameEpoch]
        have late : (getCurrentEpoch m.state).toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
            wP.withdrawableEpoch.toNat := withdrawable
        omega
      simpa [foundP] using key
    refine ⟨cut, ?_⟩
    -- The balance at the split is within `cut_balance_le`'s bound, and the quotient splits.
    have bound := cut_balance_le h fromFin tail high endEpoch replayedF replayed v cut
    have unit : Internal.slashR (pinTerms config pulled anc fin) v.toNat = inc := by simp
      [Internal.slashR, rb, inc]
    rw [unit]
    rcases Nat.eq_zero_or_pos q with zero | positive
    · simp [zero]
    have lift (a c : ℕ) : (a + c) / q ≤ a + c / q := by
      have h2 := Nat.lt_mul_div_succ c positive
      rw [Nat.mul_succ] at h2
      have ha : a ≤ q * a := Nat.le_mul_of_pos_left a positive
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul positive, Nat.succ_mul, Nat.add_mul, Nat.mul_comm a q,
        Nat.mul_comm (c / q)]
      omega
    generalize balanceAt split v.toNat = x at bound ⊢
    generalize hP : balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat = p
      at bound ⊢
    generalize Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat = r
      at bound ⊢
    generalize Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat = d at bound ⊢
    generalize balanceAt fin v.toNat = f at bound ⊢
    by_cases debited : 0 < d
    · simp only [debited, ↓reduceIte] at bound ⊢
      have within : x ≤ max p f + ((inc + r) + inc) := by omega
      have one := (Nat.div_le_div_right (c := q) within).trans
        (floor_add_ceil_le _ _ q positive)
      have two := lift (inc + r) (inc + q - 1)
      rw [show inc + r + inc + q - 1 = inc + r + (inc + q - 1) by omega] at one
      omega
    · simp only [debited, ↓reduceIte] at bound ⊢
      have within : x ≤ max p f + (inc + r) := by omega
      have one := (Nat.div_le_div_right (c := q) within).trans
        (floor_add_ceil_le _ _ q positive)
      have two := lift (inc + r) (q - 1)
      have zero : (q - 1) / q = 0 := Nat.div_eq_of_lt (by omega)
      rw [show inc + r + q - 1 = inc + r + (q - 1) by omega] at one
      omega
  -- The keys that `pre` slashes fit the cut keys' reserves, increments, seats and debits.
  have cutSum := (Finset.sum_le_sum fun v member => (each v member).2).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (fun v member => (each v member).1)
      fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at cutSum
  simp only [hq, hinc] at cutSum whistle
  linarith

/-- The sync movement of a key is its sync credits plus its sync debits over the events. -/
private theorem syncF_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    Internal.syncF events v = (events.map (Internal.syncCredit v)).sum +
      (events.map (Internal.syncDebit v)).sum := by
  unfold Internal.syncF
  rw [← Internal.sum_syncDebit_eq events v]
  exact congrArg (· + ((events.map (Internal.syncDebit v)).sum)) (Internal.sum_map_sync events
    (Internal.keyCredit v)).symm

/-- The sync movement of keys on a run within a call's reach is within an envelope.

The run is the tail from the split, after `pre`, the shared run from the start of the split's epoch.

The envelope is the seats' one, read at the pulled state's total.

`shape` ties `pre` to the run from the finalized state, so each of its steps has a guarded total.

A step before the finalized state is in its epoch, where the active stake is the finalized one. -/
private theorem syncF_run_le (h : Setting config checks g split fin pulled anc counted V)
    (pulledTotal : Gwei) (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (shape : (∃ fromB : Run config checks ⟨fork, fin⟩ ⟨fork, b⟩, fromFin = fromB.append pre) ∨
      ∃ toFinB : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, pre = toFinB.append fromFin)
    {e : BeaconState preset fork} (t : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (highE : ℕ) {evs : List (BalanceEvent preset)}
    (replayed : (pre.append t).balanceEvents highE = .ok evs) (keys : Finset ℕ) :
    ∑ i ∈ keys, Internal.syncF evs i ≤
      ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch split).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          Internal.syncSeatEnvelope preset pulledTotal.toNat := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitB := congrArg UInt64.toNat sameEpoch
  have guarded : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      (fromFin.append t).Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := fun step member T read =>
    Internal.step_band_of_guard h (fromFin.append t) within pulledOk step member T read
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      (pre.append t).Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := by
    intro u w step member T read
    rcases (Run.contains_append _ _ _).mp member with inPre | inTail
    · rcases shape with ⟨fromB, rfl⟩ | ⟨toFinB, rfl⟩
      · exact guarded step ((Run.contains_append _ _ _).mpr (.inl
          ((Run.contains_append _ _ _).mpr (.inr inPre)))) T read
      · rcases (Run.contains_append _ _ _).mp inPre with before | inFin
        · -- a step before the finalized state shares its epoch, so its stake is the finalized one
          obtain ⟨front, back, -⟩ := toFinB.contains_split step before
          have startW : (getCurrentEpoch b).toNat ≤ (getCurrentEpoch w.state).toNat :=
            UInt64.le_iff_toNat_le.mp (UInt64.le_trans
              (currentEpoch_le_of_chainSteps front.chainSteps) step.chainStep.currentEpoch_le)
          have endW : (getCurrentEpoch w.state).toNat ≤ (getCurrentEpoch fin).toNat :=
            UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps back.chainSteps)
          have sameEp : getCurrentEpoch fin = getCurrentEpoch w.state :=
            UInt64.toNat_inj.mp (by omega)
          have wFork := Run.fork_eq_of_same_epoch back sameEp
          obtain ⟨wf, ws⟩ := w
          dsimp only at wFork sameEp read
          subst wFork
          have sums := DirectSafety.Apriori.Internal.activeStake_eq_of_same_epoch back h.early
            sameEp (getCurrentEpoch ws) (UInt64.le_refl _)
          have okW := getTotalActiveBalance_ok read
          obtain ⟨-, ltW, valW⟩ := getTotalBalance_ok_iff_stake.mp okW
          rw [← sameEp] at ltW valW
          have sameStake : stake (fun index => balanceAt fin index.toNat)
              (getActiveValidatorIndices fin (getCurrentEpoch fin)).toFinset =
              stake (fun index => balanceAt ws index.toNat)
                (getActiveValidatorIndices ws (getCurrentEpoch fin)).toFinset := by
            rw [← sameEp] at sums
            exact sums
          have checked : getActiveValidatorIndicesChecked fin (getCurrentEpoch fin) =
              .ok (getActiveValidatorIndices fin (getCurrentEpoch fin)) := by
            rw [getActiveValidatorIndicesChecked_eq_ok_iff]
            intro position inside _
            exact inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early fin)
          have okFin : getTotalActiveBalance fin = .ok T := by
            unfold getTotalActiveBalance
            rw [checked]
            exact getTotalBalance_ok_iff_stake.mpr
              ⟨fun i m => lt_size_of_mem_getActiveValidatorIndices m, sameStake ▸ ltW,
                by rw [valW, sameStake]⟩
          exact Internal.total_band_of_guard shared h.genesis h.parameters h.caps h.aligned
            h.twoSlots
            electra h.guard (fromFin.append toPulled) h.early (Nat.le_succ _)
            (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) h.early
            (by dsimp only; omega) pulledOk okFin
        · exact guarded step ((Run.contains_append _ _ _).mpr (.inl inFin)) T read
    · exact guarded step ((Run.contains_append _ _ _).mpr (.inr inTail)) T read
  have moves := (Internal.Run.syncDebits_le (pre.append t) h.fulu h.early highE replayed
    pulledTotal.toNat band keys).2.1
  refine (Finset.sum_le_sum fun i _ => (syncF_eq evs i).le).trans (moves.trans (le_of_eq ?_))
  dsimp only
  rw [sameEpoch]

/-- `syncProposer` is the proposer share of the sync envelope at R's total.

It is paid for each seat in each slot of an epoch. -/
private theorem syncProposer_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).syncProposer =
      preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
        (PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat *
          PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := rfl

/-- The reserve uses R's total active balance when the read succeeds. -/
private theorem getD_total_eq {pulledTotal : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    ((getTotalActiveBalance pulled).toOption.getD 0).toNat = pulledTotal.toNat := by
  rw [pulledOk]
  rfl

/-- The steps of a run from the split keep their total within the band of R's total. -/
private theorem step_band_of_tail (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {e : BeaconState preset fork}
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {pulledTotal : Gwei} (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      tail.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat := fun step member T read =>
  Internal.step_band_of_guard h (fromFin.append tail) within pulledOk step
    ((Run.contains_append _ _ _).mpr (.inr member)) T read

/-- The epochs of the shared segment and of R's run add up to the window from `fin`. -/
private theorem pin_epochs (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) :
    ((getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat) +
        ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  simp only at finSplit
  omega

/-- The sync seats, in the third window: the base bound with the shared segment's K debits.

It also holds the shares of `CS` and of the shared segment's exited keys of `SC`.

The shared segment's debits are one weighted sum over the disjoint classes.

`cutKeys` holds the keys slashed at the split that R's call reads as slashed, at the same weight.

`bud_branchR` rounds their rewards up, and the debits pay the rounding.

The sync credits of `pre` ride with R's tail, since `pre` and the tail are one run in the epoch.

`K5` weighs three, and `SC` once for the split-epoch charge case. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_sync (h : Setting config checks
  g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    (shape : (∃ fromB : Run config checks ⟨fork, fin⟩ ⟨fork, b⟩, fromFin = fromB.append pre) ∨
      ∃ toFinB : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, pre = toFinB.append fromFin)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {eventsP : List (BalanceEvent preset)} (replayedP : pre.balanceEvents high = .ok eventsP) :
    3 * ((∑ v ∈ V, (Internal.syncD eventsF v.toNat + (Internal.syncF events v.toNat + Internal.syncF
      eventsC v.toNat))) +
        (∑ v ∈ (Internal.K4 pulled counted V), Internal.syncD eventsF v.toNat) +
        (∑ v ∈ (Internal.K4 pulled counted V), (Internal.syncF events v.toNat + Internal.syncF
          eventsC v.toNat)) +
        (∑ v ∈ (Internal.K5 counted V), (Internal.syncD eventsF v.toNat + Internal.syncCr eventsP
          v.toNat)) +
        (∑ v ∈ (Internal.K5 counted V), (Internal.syncF events v.toNat + Internal.syncF eventsC
          v.toNat)) +
        (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat))) +
      (∑ v ∈ (Internal.K6 pulled counted), Internal.syncD eventsF v.toNat) +
      (∑ v ∈ (Internal.K6 pulled counted), (Internal.syncF events v.toNat + Internal.syncF eventsC
        v.toNat)) +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsC
        v.toNat) +
      Internal.wShare preset fork
        (∑ v ∈ Internal.SC pulled counted split, (Internal.syncD eventsF v.toNat + Internal.syncD
          events v.toNat)) +
      Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.syncCr eventsC v.toNat)
        +
      Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.syncCr eventsF
          v.toNat) +
      2 * ∑ v ∈ Internal.sc3a config pulled anc fin counted split, Internal.syncD eventsF v.toNat +
      (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsP v.toNat) ≤
        (pinTerms config pulled anc fin).syncSeats +
          6 * ((pinTerms config pulled anc fin).depth *
            (pinTerms config pulled anc fin).syncProposer) := by
  classical
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  -- the five sets are pairwise disjoint
  obtain ⟨d45, d46, d56, d1, d15, d16⟩ := Internal.classes_disjoint h
  obtain ⟨dS, dVS⟩ := Internal.sc_disjoint h
  obtain ⟨dCK, dCV⟩ := Internal.cs_disjoint h
  have d2 : Disjoint (V ∪ Internal.K4 pulled counted V) (Internal.K5 counted V) :=
    Finset.disjoint_union_left.mpr ⟨d15, d45⟩
  have d3 : Disjoint (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V) (Internal.K6 pulled
    counted) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d16, d46⟩, d56⟩
  have d4 : Disjoint (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted)
      (Internal.SC pulled counted split) := by
    rw [Finset.disjoint_left]
    intro v member slashed
    simp only [Finset.mem_union] at member
    rcases member with ((inV | in4) | in5) | in6
    · exact Finset.disjoint_left.mp dVS inV slashed
    · exact Finset.disjoint_left.mp dS (Finset.mem_union_left _ (Finset.mem_union_left _ in4))
        slashed
    · exact Finset.disjoint_left.mp dS (Finset.mem_union_left _ (Finset.mem_union_right _ in5))
        slashed
    · exact Finset.disjoint_left.mp dS (Finset.mem_union_right _ in6) slashed
  have dCS : Disjoint (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted ∪
      Internal.SC pulled counted split) (Internal.CS counted split) := by
    rw [Finset.disjoint_left]
    intro v member created
    simp only [Finset.mem_union] at member
    rcases member with (((inV | in4) | in5) | in6) | inSC
    · exact Finset.disjoint_left.mp dCV inV created
    · exact Finset.disjoint_left.mp dCK (by simp [in4]) created
    · exact Finset.disjoint_left.mp dCK (by simp [in5]) created
    · exact Finset.disjoint_left.mp dCK (by simp [in6]) created
    · exact Finset.disjoint_left.mp dCK (by simp [inSC]) created
  obtain ⟨U, hU⟩ : ∃ U : Finset ValidatorIndex,
      U = V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted ∪
        Internal.SC pulled counted split ∪
        Internal.CS counted split :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ValidatorIndex → ℕ, ∀ v, g v =
      Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat := ⟨_, fun _ => rfl⟩
  have sumU : ∑ v ∈ U, g v = ∑ v ∈ V, g v + ∑ v ∈ Internal.K4 pulled counted V, g v +
      ∑ v ∈ Internal.K5 counted V, g v + ∑ v ∈ Internal.K6 pulled counted, g v +
      ∑ v ∈ Internal.SC pulled counted split, g v + ∑ v ∈ Internal.CS counted split, g v := by
    rw [hU, Finset.sum_union dCS, Finset.sum_union d4, Finset.sum_union d3, Finset.sum_union d2,
      Finset.sum_union d1]
  -- the keys of SC that exited by the finalized epoch hold the shared credits, and the rest debits
  set EK := (Internal.SC pulled counted split).filter
    (fun v => (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) with hEK
  set NF := (Internal.SC pulled counted split).filter
    (fun v => ¬ (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) with hNF
  have dKN : Disjoint (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted) NF :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) d4
  have dKE : Disjoint (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted) EK :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) d4
  have dNE : Disjoint NF EK := Finset.disjoint_left.mpr fun v inN inE =>
    (Finset.mem_filter.mp inN).2 (Finset.mem_filter.mp inE).2
  have scSplit : ∑ v ∈ Internal.SC pulled counted split, Internal.syncD eventsF v.toNat =
      ∑ v ∈ EK, Internal.syncD eventsF v.toNat + ∑ v ∈ NF, Internal.syncD eventsF v.toNat :=
    (Finset.sum_filter_add_sum_filter_not _ _ fun v : ValidatorIndex => Internal.syncD eventsF
      v.toNat).symm
  have unionD : ∑ v ∈ V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
    counted ∪ NF,
      Internal.syncD eventsF v.toNat = ∑ v ∈ V, Internal.syncD eventsF v.toNat +
        ∑ v ∈ Internal.K4 pulled counted V, Internal.syncD eventsF v.toNat +
        ∑ v ∈ Internal.K5 counted V, Internal.syncD eventsF v.toNat + ∑ v ∈ Internal.K6 pulled
          counted, Internal.syncD eventsF v.toNat +
        ∑ v ∈ NF, Internal.syncD eventsF v.toNat := by
    rw [Finset.sum_union dKN, Finset.sum_union d3, Finset.sum_union d2, Finset.sum_union d1]
  have unionK : ∑ v ∈ EK, (Internal.syncCr eventsF v.toNat + Internal.syncD eventsF v.toNat) =
      ∑ v ∈ EK, Internal.syncCr eventsF v.toNat + ∑ v ∈ EK, Internal.syncD eventsF v.toNat :=
    Finset.sum_add_distrib
  -- each class is weighed at most three times its tail movement, and the shares at most their own
  have classV : ∑ v ∈ V, (Internal.syncD eventsF v.toNat + (Internal.syncF events v.toNat +
    Internal.syncF eventsC v.toNat)) =
      ∑ v ∈ V, Internal.syncD eventsF v.toNat + ∑ v ∈ V, g v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hg]
  have class4 : ∑ v ∈ Internal.K4 pulled counted V, (Internal.syncF events v.toNat + Internal.syncF
    eventsC v.toNat) ≤
      ∑ v ∈ Internal.K4 pulled counted V, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have class5 : ∑ v ∈ Internal.K5 counted V, (Internal.syncF events v.toNat + Internal.syncF eventsC
    v.toNat) ≤
      ∑ v ∈ Internal.K5 counted V, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have class6 : ∑ v ∈ Internal.K6 pulled counted, (Internal.syncF events v.toNat + Internal.syncF
    eventsC v.toNat) ≤
      ∑ v ∈ Internal.K6 pulled counted, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have credits : Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split,
    Internal.syncCr eventsC v.toNat) ≤
      ∑ v ∈ Internal.SC pulled counted split, Internal.syncF eventsC v.toNat :=
    (Internal.wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      unfold Internal.syncCr
      rw [syncF_eq]
      exact Nat.le_add_right _ _)
  have debits : Internal.wShare preset fork
      (∑ v ∈ Internal.SC pulled counted split, (Internal.syncD eventsF v.toNat + Internal.syncD
        events v.toNat)) ≤
      ∑ v ∈ Internal.SC pulled counted split, Internal.syncD eventsF v.toNat +
        ∑ v ∈ Internal.SC pulled counted split, Internal.syncF events v.toNat := by
    rw [← Finset.sum_add_distrib]
    exact (Internal.wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      unfold Internal.syncD
      rw [syncF_eq]
      omega)
  have creditsF : Internal.wShare preset fork (∑ v ∈ EK, Internal.syncCr eventsF v.toNat) ≤
      ∑ v ∈ EK, Internal.syncCr eventsF v.toNat := Internal.wShare_le h.facts _
  have creditsCS : Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.syncCr
    eventsC v.toNat) ≤
      ∑ v ∈ Internal.CS counted split, g v :=
    (Internal.wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      rw [hg]
      unfold Internal.syncCr
      rw [syncF_eq eventsC]
      omega)
  have shares : ∑ v ∈ Internal.SC pulled counted split, Internal.syncF eventsC v.toNat +
      ∑ v ∈ Internal.SC pulled counted split, Internal.syncF events v.toNat =
      ∑ v ∈ Internal.SC pulled counted split, g v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hg]; omega
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ v ∈ V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
    Internal.K6 pulled counted ∪ NF,
      Internal.syncD eventsF v.toNat + ∑ v ∈ EK, (Internal.syncCr eventsF v.toNat + Internal.syncD
        eventsF v.toNat) :=
    ⟨_, rfl⟩
  -- the keys that the rise term of `bud_whistle_of` charges are among the keys of `SC`
  have rise3a : ∑ v ∈ Internal.sc3a config pulled anc fin counted split, Internal.syncD eventsF
    v.toNat ≤
      ∑ v ∈ Internal.SC pulled counted split, Internal.syncD eventsF v.toNat :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- the terms of the statement beyond the old ones: the credits of `pre` and the cut keys' debits
  obtain ⟨extra, hextra⟩ : ∃ extra : ℕ, extra =
      3 * ∑ v ∈ Internal.K5 counted V, Internal.syncCr eventsP v.toNat +
      3 * ∑ v ∈ Internal.cutKeys config pulled anc fin split,
        (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat) +
      ∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsP v.toNat := ⟨_, rfl⟩
  have k5split : ∑ v ∈ Internal.K5 counted V, (Internal.syncD eventsF v.toNat + Internal.syncCr
    eventsP v.toNat) =
      ∑ v ∈ Internal.K5 counted V, Internal.syncD eventsF v.toNat + ∑ v ∈ Internal.K5 counted V,
        Internal.syncCr eventsP v.toNat :=
    Finset.sum_add_distrib
  have cutSplit : ∑ v ∈ Internal.cutKeys config pulled anc fin split,
        (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat) =
      ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD eventsF v.toNat +
        ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD events v.toNat :=
          Finset.sum_add_distrib
  refine le_trans (b := 3 * (∑ v ∈ U, g v + S) + extra) ?_ ?_
  · rw [sumU, hS]
    omega
  -- the shared segment moves the debited keys and the keys of EK by one envelope for each seat
  have cutAll := Internal.cut_disjoint h
  have cutU : Disjoint U (Internal.cutKeys config pulled anc fin split) := hU ▸ cutAll.symm
  have cutD : Disjoint (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6
    pulled counted ∪ NF)
      (Internal.cutKeys config pulled anc fin split) := by
    refine Finset.disjoint_of_subset_left ?_ cutU
    rw [hU]
    intro v member
    simp only [Finset.mem_union] at member ⊢
    rcases member with inK | inNF
    · exact .inl (.inl inK)
    · exact .inl (.inr (Finset.mem_filter.mp inNF).1)
  obtain ⟨PD, hPD⟩ : ∃ PD, PD = (V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪
    Internal.K6 pulled counted ∪
      NF ∪ Internal.cutKeys config pulled anc fin split).image fun v : ValidatorIndex => v.toNat :=
    ⟨_, rfl⟩
  obtain ⟨PK, hPK⟩ : ∃ PK, PK = EK.image fun v : ValidatorIndex => v.toNat := ⟨_, rfl⟩
  have dP : Disjoint PD PK := by
    have injective : Function.Injective fun v : ValidatorIndex => v.toNat :=
      fun a b same => UInt64.toNat_inj.mp same
    rw [hPD, hPK, Finset.disjoint_image injective]
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨dKE, dNE⟩, ?_⟩
    refine Finset.disjoint_of_subset_right (fun v inE => ?_) cutAll
    simp only [Finset.mem_union]
    exact .inl (.inr (Finset.mem_filter.mp inE).1)
  have posD := voters_sum_le
      (voters := V ∪ Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
        counted ∪ NF ∪
        Internal.cutKeys config pulled anc fin split) (positions := PD) (fun i => Internal.syncD
          eventsF i)
    fun v member => by rw [hPD]; exact Finset.mem_image_of_mem _ member
  have posK := voters_sum_le (voters := EK) (positions := PK)
      (fun i => Internal.syncCr eventsF i + Internal.syncD eventsF i)
    fun v member => by rw [hPK]; exact Finset.mem_image_of_mem _ member
  have band : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      fromFin.Contains step → ∀ T : Gwei, getTotalActiveBalance w.state = .ok T →
        2 * T.toNat ≤ 3 * pulledTotal.toNat :=
    Internal.step_band_of_guard h fromFin (by omega) pulledOk
  -- no block of the shared segment has a proposer among the keys of EK
  obtain ⟨toFin⟩ := h.toFin
  have apartK : ∀ {u w : ForkedBeaconState preset} (step : Step config checks u w),
      fromFin.Contains step → Internal.stepApart PK step := by
    intro u w step member
    cases step with
    | slot _ => trivial
    | @block f before after engine signed due ok =>
      obtain ⟨pre, post, -, -, -⟩ :=
        DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
      intro p found inK
      obtain ⟨v, inEK, same⟩ := Finset.mem_image.mp (hPK ▸ inK)
      -- v exits at R by the finalized epoch, so the finalized state has its record and exit
      obtain ⟨w0, foundPulled, exited⟩ : ∃ w0, pulled.validators.data[v.toNat]? = some w0 ∧
          w0.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat := by
        have flag : ((pulled.validators.data[v.toNat]?).any fun w =>
            decide (w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = true :=
          (Finset.mem_filter.mp inEK).2
        cases found0 : pulled.validators.data[v.toNat]? with
        | none => simp [found0] at flag
        | some w0 =>
          simp [found0] at flag
          exact ⟨w0, rfl, flag⟩
      obtain ⟨u0, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h foundPulled exited
      have inactive := Internal.inactive_of_exited h.twoSlots (pre.snoc (Step.block engine signed
        due ok))
        foundFin (by rw [kept]; exact exited)
      have look := Run.lookaheadActive h.facts.covers h.genesis
        (toFin.append (pre.snoc (Step.block engine signed due ok)))
        (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      have active := look.proposer_active (Nat.le_trans h.fulu
        (fork_le_of_chainSteps (pre.snoc (Step.block engine signed due ok)).chainSteps)) found
      rw [← same, inactive] at active
      exact Bool.false_ne_true active
  have sharedRun := (Internal.Run.syncDebits_le fromFin h.fulu h.early high replayedF
    pulledTotal.toNat band ∅).2.2 PD PK dP apartK
  unfold Internal.syncSeatMoves at sharedRun
  have sharedS : S + ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD eventsF
    v.toNat ≤
      ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset pulledTotal.toNat := by
    have whole := Finset.sum_union cutD (f := fun v : ValidatorIndex => Internal.syncD eventsF
      v.toNat)
    have both := (Nat.add_le_add posD posK).trans sharedRun
    dsimp only at whole both
    rw [hS]
    omega
  -- the tails move the keys of the classes and the cut keys by their seat bounds.
  --
  -- `pre` joins R's tail as one run, whose events are those of `pre` and then the tail's.
  have joined := DirectSafety.Apriori.Internal.balanceEvents_append pre tail high replayedP replayed
  have syncAppend : ∀ i, Internal.syncF (eventsP ++ events) i = Internal.syncF eventsP i +
    Internal.syncF events i := by
    intro i
    simp only [Internal.syncF, List.filter_append, List.map_append, List.sum_append]
    omega
  obtain ⟨G, hG⟩ : ∃ G : ValidatorIndex → ℕ, ∀ v, G v = Internal.syncF eventsP v.toNat + g v :=
    ⟨_, fun _ => rfl⟩
  have toPositions : ∑ v ∈ U ∪ Internal.cutKeys config pulled anc fin split, G v ≤
      ∑ i ∈ (U ∪ Internal.cutKeys config pulled anc fin split).image (fun v : ValidatorIndex =>
        v.toNat),
        (Internal.syncF (eventsP ++ events) i + Internal.syncF eventsC i) :=
    (Finset.sum_congr rfl fun v _ => by rw [hG, hg, syncAppend]; omega).le.trans
      (voters_sum_le (fun i => Internal.syncF (eventsP ++ events) i + Internal.syncF eventsC i)
        fun v member => Finset.mem_image_of_mem _ member)
  have first := syncF_run_le h pulledTotal pulledOk fromFin pre sameEpoch shape tail
    (Nat.le_succ _) high joined
    ((U ∪ Internal.cutKeys config pulled anc fin split).image fun v : ValidatorIndex => v.toNat)
  have second := syncF_run_le h pulledTotal pulledOk fromFin Run.nil rfl (.inl ⟨fromFin, rfl⟩) tailC
    near highC (by rw [Run.nil_append]; exact replayedC)
    ((U ∪ Internal.cutKeys config pulled anc fin split).image fun v : ValidatorIndex => v.toNat)
  generalize (U ∪ Internal.cutKeys config pulled anc fin split).image (fun v : ValidatorIndex =>
    v.toNat) =
    P at toPositions first second
  have splitP : ∑ i ∈ P, (Internal.syncF (eventsP ++ events) i + Internal.syncF eventsC i) =
      ∑ i ∈ P, Internal.syncF (eventsP ++ events) i + ∑ i ∈ P, Internal.syncF eventsC i :=
        Finset.sum_add_distrib
  have totalEq := getD_total_eq pulledOk
  have seats : (pinTerms config pulled anc fin).syncSeats =
      3 * (((pinTerms config pulled anc fin).depth +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat) := rfl
  have proposer := syncProposer_eq config pulled anc fin
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  rw [totalEq] at seats proposer
  rw [seats, proposer]
  unfold Internal.syncSeatEnvelope at first second
  generalize (pinTerms config pulled anc fin).depth = depth at depthEq ⊢
  generalize PinTerms.syncEnvelope preset pulledTotal.toNat = env at *
  generalize env * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) =
    share at *
  -- the epochs of the three runs fit the two depths
  have epochs : ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) +
      ((getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat) +
      ((getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat) ≤
      depth + ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) := by
    omega
  have firstDepth :
      (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth := by
    omega
  have secondDepth :
      (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth := by
    omega
  generalize (getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat = ef at *
  generalize (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat = e1 at *
  generalize (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat = e2 at *
  generalize (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat = d at *
  have scaleEnv := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) epochs
  have scaleShare := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)
    (show e1 + e2 ≤ depth + depth by omega)
  have positions : ∑ v ∈ U ∪ Internal.cutKeys config pulled anc fin split, G v + (S +
      ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD eventsF v.toNat) ≤
      (ef + e1 + e2) * (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) +
        (e1 + e2) *
          (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share) := by
    have tails : ∑ i ∈ P, (Internal.syncF (eventsP ++ events) i + Internal.syncF eventsC i) ≤
        e1 * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * (env + share) +
          e2 * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            (env + share) := by
      rw [splitP]
      exact Nat.add_le_add first second
    calc _ ≤ _ := Nat.add_le_add (toPositions.trans tails) sharedS
      _ = _ := by ring
  -- `extra` is paid by the same pools: `pre`'s credits and the cut keys' debits are in them
  have pay : 3 * (∑ v ∈ U, g v + S) + extra ≤
      3 * (∑ v ∈ U ∪ Internal.cutKeys config pulled anc fin split, G v +
        (S + ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD eventsF v.toNat)) :=
          by
    have whole := Finset.sum_union cutU (f := G)
    have splitU : ∑ v ∈ U, G v = ∑ v ∈ U, Internal.syncF eventsP v.toNat + ∑ v ∈ U, g v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => hG v
    have splitCut : ∑ v ∈ Internal.cutKeys config pulled anc fin split, G v =
        ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncF eventsP v.toNat +
          ∑ v ∈ Internal.cutKeys config pulled anc fin split, g v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => hG v
    have classesP : ∑ v ∈ U, Internal.syncF eventsP v.toNat = ∑ v ∈ V, Internal.syncF eventsP
      v.toNat +
        ∑ v ∈ Internal.K4 pulled counted V, Internal.syncF eventsP v.toNat +
        ∑ v ∈ Internal.K5 counted V, Internal.syncF eventsP v.toNat + ∑ v ∈ Internal.K6 pulled
          counted, Internal.syncF eventsP v.toNat +
        ∑ v ∈ Internal.SC pulled counted split, Internal.syncF eventsP v.toNat +
        ∑ v ∈ Internal.CS counted split, Internal.syncF eventsP v.toNat := by
      rw [hU, Finset.sum_union dCS, Finset.sum_union d4, Finset.sum_union d3, Finset.sum_union d2,
        Finset.sum_union d1]
    have credit (L : Finset ValidatorIndex) :
        ∑ v ∈ L, Internal.syncCr eventsP v.toNat ≤ ∑ v ∈ L, Internal.syncF eventsP v.toNat :=
      Finset.sum_le_sum fun v _ => by
        unfold Internal.syncCr
        rw [syncF_eq]
        exact Nat.le_add_right _ _
    have k5 := credit (Internal.K5 counted V)
    have sc := credit (Internal.SC pulled counted split)
    have cutTail : ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD events v.toNat
      ≤
        ∑ v ∈ Internal.cutKeys config pulled anc fin split, g v :=
      Finset.sum_le_sum fun v _ => by
        rw [hg]
        unfold Internal.syncD
        rw [syncF_eq]
        omega
    rw [hextra]
    omega
  calc 3 * (∑ v ∈ U, g v + S) + extra
      ≤ 3 * (∑ v ∈ U ∪ Internal.cutKeys config pulled anc fin split, G v +
          (S + ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD eventsF v.toNat))
            := pay
    _ ≤ 3 * ((ef + e1 + e2) *
          (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) +
        (e1 + e2) * (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)) :=
        Nat.mul_le_mul_left _ positions
    _ ≤ 3 * ((depth + d) *
          (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env) +
        (depth + depth) *
          (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add scaleEnv scaleShare)
    _ = _ := by ring

/-- The sync credits of any keys on C's branch are at most the seats' envelope and a share.

The share is the proposer's, and the bound weighs both at the depth, as `syncSeats` does. -/
private theorem syncCredits_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (eventsC.map (Internal.syncCredit i)).sum ≤
      (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  obtain ⟨fromFin⟩ := h.fromFin
  have run := syncF_run_le h pulledTotal pulledOk fromFin Run.nil rfl
    (.inl ⟨fromFin, rfl⟩) tailC near highC
    (by rw [Run.nil_append]; exact replayedC) keys
  have credits : ∑ i ∈ keys, (eventsC.map (Internal.syncCredit i)).sum ≤ ∑ i ∈ keys, Internal.syncF
    eventsC i :=
    Finset.sum_le_sum fun i _ => (Nat.le_add_right _ _).trans (syncF_eq eventsC i).ge
  have totalEq := getD_total_eq pulledOk
  have proposer := syncProposer_eq config pulled anc fin
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  rw [proposer, totalEq]
  unfold Internal.syncSeatEnvelope at run
  generalize (pinTerms config pulled anc fin).depth = depth at depthEq ⊢
  generalize PinTerms.syncEnvelope preset pulledTotal.toNat = env at *
  generalize env * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) =
    share at *
  have depthCounted : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤ depth :=
    by omega
  have bounded : ∑ i ∈ keys, Internal.syncF eventsC i ≤
      depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * env +
        depth * preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat * share := by
    refine run.trans ?_
    rw [Nat.mul_add]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ depthCounted)))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ depthCounted)))
  calc _ ≤ _ := credits.trans bounded
    _ = _ := by ring

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A run from a state after the split bounds a key's balance and effective balance by its credits.

The balance at the start, up to the cap bound, is at most `B`.

Then the balance up to the cap bound is at most `B`, the gains at the largest rate and the credits.

The effective balance at the end is at most that of the start, or that bound.

The cap bound is at least every cap along the run. -/
private theorem ceiling_run (h : Setting config checks g split fin pulled anc counted V)
    {c a : ForkedBeaconState preset} (toC : Run config checks ⟨fork, split⟩ c)
    (tail : Run config checks c a) (aEarly : a.fork < .glamsterdam) (aFork : a.fork ≤ fork)
    (i : ℕ) (inside : i < c.state.validators.data.size) (highC : ℕ)
    (endEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1)
    (near : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (capHigh : ℕ) (capLe : capHigh ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt c i ≤ capHigh) (B : ℕ)
    (startBal : min (actualBalanceAt c i) capHigh ≤ B)
    (capCeil : ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) :
    (∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ B +
      ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
        (pinTerms config pulled anc fin).gainRateMax +
      (Internal.netScan i highC tail +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail))) ∧
    effectiveAt a i ≤ max (effectiveAt c i) (B +
      ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
        (pinTerms config pulled anc fin).gainRateMax +
      (Internal.netScan i highC tail +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail))) := by
  classical
  obtain ⟨P, hP, gainLe, -⟩ := Internal.pin_rate_exists h
  obtain ⟨P', hP', rateAll⟩ := Internal.key_rate_forked h
  rw [hP'.trans hP.symm] at rateAll
  have cFork : fork ≤ c.fork := fork_le_of_chainSteps toC.chainSteps
  have rate : ∀ z ∈ tail.balancePath, i.toUInt64 ∉ getActiveValidatorIndices z.state
        (getPreviousEpoch z.state) ∨
      ∀ total perIncrement : Gwei, getTotalActiveBalance z.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
          (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    intro z member
    right
    obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint tail (Run.nil : Run config checks a a)
      (Nat.le_trans aFork cFork) member
    have order : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch a.state).toNat :=
      UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
    exact rateAll z (toC.append r1) (Nat.le_trans (fork_le_of_chainSteps r2.chainSteps) aFork)
      (by omega)
  obtain ⟨-, -, third, fourth⟩ := Internal.Run.effective_floor_pair tail aEarly
    (Nat.le_trans h.fulu cFork) i inside 0 0 capHigh highC
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
  have balances := fourth alignedCap startCap capCeil rate endEpoch
    (max_le (Nat.le_trans startCap capLe) (Nat.le_trans (Nat.min_le_left _ _) capLe))
  have ceiling := (third _ alignedCap startCap balances capCeil).1
  have gain := Nat.mul_le_mul_left ((getCurrentEpoch a.state).toNat -
    (getCurrentEpoch c.state).toNat) gainLe
  have credit : Internal.creditBound tail i highC preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
      capHigh ≤ B +
        ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
          (pinTerms config pulled anc fin).gainRateMax +
        (Internal.netScan i highC tail +
          (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail)) :=
            by
    unfold Internal.creditBound
    omega
  exact ⟨fun z member => Nat.le_trans (balances z member) credit,
    Nat.le_trans ceiling (max_le (Nat.le_max_left _ _) (Nat.le_trans (Nat.min_le_left _ _)
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans credit (Nat.le_max_right _ _)))))⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key beyond R's registry whose exit started on C's run rises at most by its credits and a band.

The exit is charged at the step that assigns it, with the effective balance before that step.

The band is the upward band at the epoch boundary before that step, where the key is active. -/
private theorem earlier_charge (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : split.validators.data.size ≤ i) (old : Validator)
    (foundA : a.state.validators.data[i]? = some old)
    (assigned : old.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    effectiveAt a i ≤ Internal.chargeAmt tailC i + (preset.upwardBand +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax +
      (Internal.credC tailC highC i + Internal.whistC tailC highC i + (eventsC.map
        (Internal.syncCredit i)).sum)) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨pre, post, cut, aEarly, aEpoch⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  have aFork : a.fork ≤ fork :=
    Nat.le_trans step.chainStep.fork_le (fork_le_of_chainSteps post.chainSteps)
  -- the key is absent at the split, so it has a charge on the run before `a`
  have unset : ∀ v, (⟨fork, split⟩ : ForkedBeaconState preset).state.validators.data[i]? =
      some v → v.exitEpoch = FAR_FUTURE_EPOCH := fun v found =>
    absurd (Array.getElem?_eq_some_iff.mp found).1 (by simp only; omega)
  obtain ⟨c0, c0Mem, c0Index, -⟩ :=
    Internal.Run.charge_of_exit pre electra aEarly i unset old foundA assigned
  obtain ⟨p, q, pre', step', post', cut', v, w, foundP, foundQ, unsetP, setQ, actP, amount, -⟩ :=
    Internal.charge_activated (x := ⟨fork, split⟩) electra pre c0 (pre.departure_charge_site c0
      c0Mem)
  rw [c0Index] at foundP foundQ
  have inTailC : c0 ∈ tailC.departureCharges := by
    rw [cut, Run.departureCharges_append]
    simp [Run.departureCharges, c0Mem]
  have chargeEq : Internal.chargeAmt tailC i = c0.amount := by
    unfold Internal.chargeAmt
    rw [Internal.find_charge inTailC (by simp [c0Index])
      (fun d inD hd => Internal.charge_unique tailC inD inTailC (by simpa [c0Index] using hd))]
    rfl
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps
      ((Run.nil.snoc step').append post' : Run config checks p a).chainSteps) aEarly
  -- the key is active at the start of the charge step
  have activeP : isActiveAt p.state (getCurrentEpoch p.state) i = true := by
    refine isActiveAt_eq_true_iff.mpr ⟨v, foundP, ?_⟩
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨actP, UInt64.lt_iff_toNat_lt.mpr ?_⟩
    rw [unsetP]
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots p.state
    omega
  have splitP : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch p.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre'.chainSteps)
  have pBound := (getCurrentEpoch p.state).toNat_lt
  -- so the run from the split crosses an epoch boundary before it
  have splitLt : (getCurrentEpoch split).toNat < (getCurrentEpoch p.state).toNat := by
    by_contra notLt
    have fixed : getCurrentEpoch p.state ≤ activityFixedEpoch split := by
      rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
      omega
    have keep := activeKept_of_chainSteps pre'.chainSteps (getCurrentEpoch p.state) fixed i
    have activeSplit : isActiveAt split (getCurrentEpoch p.state) i = true := by
      rw [← keep]
      exact activeP
    obtain ⟨u, foundU, -⟩ := isActiveAt_eq_true_iff.mp activeSplit
    have := (Array.getElem?_eq_some_iff.mp foundU).1
    omega
  obtain ⟨z, cc, pre0, ok, rest0, splitEq, hz, hcc⟩ := Run.cross_split pre'
    ((getCurrentEpoch p.state).toNat - 1)
    (by show (getCurrentEpoch split).toNat ≤ (getCurrentEpoch p.state).toNat - 1; omega)
    (by omega)
  subst splitEq
  have ccEarly : cc.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps rest0.chainSteps) pEarly
  have fuluZ : .fusaka ≤ z.fork :=
    Nat.le_trans h.fulu (fork_le_of_chainSteps pre0.chainSteps)
  have hyst : Hysteresis cc.state :=
    hysteresis_of_crossing_slot ok h.bands fuluZ ccEarly (by omega)
  -- the key is in the registry at the first state of the epoch of the charge
  have fixedC : getCurrentEpoch p.state ≤ activityFixedEpoch cc.state := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    omega
  have keepC := activeKept_of_chainSteps rest0.chainSteps (getCurrentEpoch p.state) fixedC i
  have activeC : isActiveAt cc.state (getCurrentEpoch p.state) i = true := by
    rw [← keepC]
    exact activeP
  obtain ⟨vc, foundC, -⟩ := isActiveAt_eq_true_iff.mp activeC
  have insideC : i < cc.state.validators.data.size := (Array.getElem?_eq_some_iff.mp foundC).1
  have effEq : effectiveAt cc i = c0.amount := by
    have same := run_same_epoch_effective rest0 pEarly
      (UInt64.toNat_inj.mp (by omega)) i insideC
    have atP : effectiveAt p i = c0.amount := by simp [effectiveAt, foundP, amount]
    omega
  -- the run from the start of the epoch to the key's state
  obtain ⟨tail2, h2⟩ : ∃ t : Run config checks cc a, t = (rest0.snoc step').append post' :=
    ⟨_, rfl⟩
  have whole : pre = (pre0.snoc (Step.slot ok)).append tail2 := by
    rw [← cut', h2, Run.append_assoc]
    rfl
  have aElectra : .pectra ≤ a.fork := Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)
  have capEnd := Internal.capAt_le_capMax h.caps aElectra i
  have toCC : Run config checks ⟨fork, split⟩ cc := pre0.snoc (Step.slot ok)
  have cFork : fork ≤ cc.fork := fork_le_of_chainSteps toCC.chainSteps
  have startEff : effectiveAt cc i ≤ PinTerms.capAt cc i :=
    Internal.effective_le_cap_at (shared.append (fromFin.append toCC)) h.genesis h.caps ccEarly i
  have capCC : PinTerms.capAt cc i ≤ PinTerms.capAt a i :=
    Internal.cap_le_cap_of_run h.caps tail2 aEarly i
  have alignedCap : PinTerms.capAt a i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    have := congrArg UInt64.toNat
      (withdrawalMaxEffectiveBalance_aligned (fork := a.fork) h.aligned old)
    simpa [PinTerms.capAt, foundA, UInt64.toNat_mod] using this
  have capCeil := Internal.capCeil_path tail2 h.caps aEarly (Nat.le_trans aFork cFork) i
  have aEpoch' : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch counted).toNat := aEpoch
  have nearC := h.near
  have near : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  have scans : Internal.netScan i highC tail2 +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail2) ≤
      Internal.netScan i highC tailC +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tailC) := by
    have eqC : tailC = (((pre0.snoc (Step.slot ok)).append tail2).snoc step).append post := by
      rw [cut, whole]
    rw [eqC]
    simp only [Internal.netScan_append, Internal.creditScan_append, Internal.netScan_snoc,
      Internal.creditScan_snoc]
    split_ifs <;> omega
  have sources := Internal.credits_le_sources (shared.append fromFin) h.genesis tailC h.early
    electra i highC
    replayedC
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have ccLow : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch cc.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps toCC.chainSteps)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  by_cases flipCase : ¬effectiveAt cc i < PinTerms.capAt cc i ∧
      PinTerms.capAt a i ≠ PinTerms.capAt cc i
  · -- the key switched to compounding after the epoch start, with its effective balance at the cap
    obtain ⟨notBelow, capNe⟩ := flipCase
    have electraC : .pectra ≤ cc.fork := Nat.le_trans electra cFork
    have capCCmin : PinTerms.capAt cc i = preset.MIN_ACTIVATION_BALANCE.toNat := by
      have eqn := Internal.capAt_of_found electraC foundC
      split at eqn <;> omega
    obtain ⟨s, s', pre1, step1, post1, eq1, capS, capS', balS', epochAt⟩ :=
      Internal.Run.flip_split tail2 aEarly (Nat.le_trans h.fulu cFork)
        ((shared.append (fromFin.append toCC)).invariant h.genesis.invariant) i (by omega)
        (by omega)
    have sFork : s.fork ≤ fork := Nat.le_trans step1.chainStep.fork_le
      (Nat.le_trans (fork_le_of_chainSteps post1.chainSteps) aFork)
    have s'Fork : s'.fork ≤ fork := Nat.le_trans (fork_le_of_chainSteps post1.chainSteps) aFork
    have sEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt sFork h.early
    have s'Early : s'.fork < .glamsterdam := Nat.lt_of_le_of_lt s'Fork h.early
    have insideS : i < s.state.validators.data.size :=
      Nat.lt_of_lt_of_le insideC pre1.registryLifecycle.size_le
    have insideS' : i < s'.state.validators.data.size := Nat.lt_of_lt_of_le insideS
      (Run.nil.snoc step1 : Run config checks s s').registryLifecycle.size_le
    have e1 := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre1.chainSteps)
    have e2 := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step1 : Run config checks s s').chainSteps)
    have e3 := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post1.chainSteps)
    -- the switch step is a block step, so it keeps the epoch and the effective balances
    have epochEq := epochAt insideC
    have effS' : effectiveAt s' i = effectiveAt s i :=
      run_same_epoch_effective (Run.nil.snoc step1 : Run config checks s s') s'Early
        (UInt64.toNat_inj.mp epochEq) i insideS
    have minLe : preset.MIN_ACTIVATION_BALANCE.toNat ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      UInt64.le_iff_toNat_le.mp h.caps.compounding
    have alignedMin : preset.MIN_ACTIVATION_BALANCE.toNat %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat h.aligned.2.1
    -- the run from the epoch start to the switch, at the activation balance as cap
    obtain ⟨-, ceil1⟩ := ceiling_run h toCC pre1 sEarly sFork i insideC highC (by omega)
      (by omega) preset.MIN_ACTIVATION_BALANCE.toNat minLe alignedMin (by omega)
      (effectiveAt cc i + preset.upwardBand) (by omega)
      (fun z member => Nat.le_trans
        (Internal.capCeil_path pre1 h.caps sEarly (Nat.le_trans sFork cFork) i z member) capS)
    -- the run from the switch to the key's state, at its cap
    obtain ⟨-, ceil2⟩ := ceiling_run h (toCC.append (pre1.snoc step1)) post1 aEarly aFork i
      insideS' highC (by omega) near (PinTerms.capAt a i) capEnd alignedCap
      (Nat.le_trans (Internal.effective_le_cap_at (shared.append (fromFin.append
        (toCC.append (pre1.snoc step1)))) h.genesis h.caps s'Early i)
        (Internal.cap_le_cap_of_run h.caps post1 aEarly i))
      (effectiveAt cc i + Internal.stepCredit (fun _ => true) (fun _ => true) i step1) (by omega)
      (Internal.capCeil_path post1 h.caps aEarly (Nat.le_trans aFork
        (fork_le_of_chainSteps (toCC.append (pre1.snoc step1)).chainSteps)) i)
    -- the credits of the three parts are at most the sources of C's run
    have notSlot := Internal.step_flip_not_slot step1 s'Early
      (Nat.le_trans (Nat.le_trans h.fulu cFork) (fork_le_of_chainSteps pre1.chainSteps)) i
      insideS (by omega) capS'
    obtain ⟨eT, replayedT⟩ := tail2.balanceEvents_ok aEarly highC
    have eqC' : tailC = (pre0.snoc (Step.slot ok)).append
        (tail2.append ((Run.nil.snoc step).append post)) := by
      rw [cut, whole, Run.append_assoc, Run.append_assoc]
      rfl
    have part : Internal.credC tail2 highC i + Internal.whistC tail2 highC i + (eT.map
      (Internal.syncCredit i)).sum ≤
        Internal.credC tailC highC i + Internal.whistC tailC highC i + (eventsC.map
          (Internal.syncCredit i)).sum := by
      obtain ⟨eP, replayedP⟩ := (pre0.snoc (Step.slot ok)).balanceEvents_ok ccEarly highC
      obtain ⟨eQ, replayedQ⟩ := ((Run.nil.snoc step).append post).balanceEvents_ok h.early highC
      have joinedC := balanceEvents_append (pre0.snoc (Step.slot ok))
        (tail2.append ((Run.nil.snoc step).append post)) highC replayedP
        (balanceEvents_append tail2 ((Run.nil.snoc step).append post) highC replayedT replayedQ)
      rw [eqC', joinedC] at replayedC
      obtain rfl := Except.ok.inj replayedC
      rw [eqC']
      unfold Internal.credC Internal.whistC
      simp only [Internal.creditScan_append, List.map_append, List.sum_append]
      omega
    have around := Internal.flip_credits_le_sources (shared.append (fromFin.append toCC)) h.genesis
      pre1
      step1 post1 notSlot aEarly (Nat.le_trans electra cFork) i highC (by omega)
      (by rw [eq1]; exact replayedT)
    rw [eq1] at around
    have epochs : (getCurrentEpoch s.state).toNat - (getCurrentEpoch cc.state).toNat +
        ((getCurrentEpoch a.state).toNat - (getCurrentEpoch s'.state).toNat) ≤
        (pinTerms config pulled anc fin).depth := by omega
    have gains := Nat.mul_le_mul_right (pinTerms config pulled anc fin).gainRateMax epochs
    rw [Nat.add_mul] at gains
    rw [chargeEq]
    omega
  · have startBal : min (actualBalanceAt cc i) (PinTerms.capAt a i) ≤
        effectiveAt cc i + preset.upwardBand := by
      by_cases below : effectiveAt cc i < PinTerms.capAt cc i
      · cases hb : cc.state.balances.data[i]? with
        | none => simp [actualBalanceAt, hb]
        | some bal =>
          have up := hyst.up i vc bal foundC hb (UInt64.lt_iff_toNat_lt.mpr
            (by simpa [effectiveAt, PinTerms.capAt, foundC] using below))
          have read : actualBalanceAt cc i = bal.toNat := by simp [actualBalanceAt, hb]
          have eff : effectiveAt cc i = vc.effectiveBalance.toNat := by simp [effectiveAt, foundC]
          omega
      · have same : PinTerms.capAt a i = PinTerms.capAt cc i := by
          by_contra ne
          exact flipCase ⟨below, ne⟩
        have := Nat.min_le_right (actualBalanceAt cc i) (PinTerms.capAt a i)
        omega
    obtain ⟨-, ceiling⟩ := ceiling_run h toCC tail2 aEarly aFork i insideC highC (by omega) near
      (PinTerms.capAt a i) capEnd alignedCap (Nat.le_trans startEff capCC)
      (effectiveAt cc i + preset.upwardBand) startBal capCeil
    have epochs : (getCurrentEpoch a.state).toNat - (getCurrentEpoch cc.state).toNat ≤
        (pinTerms config pulled anc fin).depth := by omega
    have gains := Nat.mul_le_mul_right (pinTerms config pulled anc fin).gainRateMax epochs
    rw [chargeEq]
    omega

/-- The whistleblower credits of a set of keys over a run fit the limits of its slashing events. -/
private theorem whistC_sum_le_limits {g m y : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (tail : Run config checks m y) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.whistC tail high v.toNat ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared tail genesis early high
  rw [replayed] at foundOk
  cases foundOk
  simpa [Internal.whistC] using Internal.creditScan_sum_le S UInt64.toNat (fun s => decide (s =
    .slashings))
    (fun _ => false) high (fun e => e.creditLimit) tail replayed fun e member _ =>
      Internal.sum_keyCredit_le_creditLimit S e (bounded e member).1

/-- The positions of the keys slashed on C's branch after the split.

They are unslashed at the split and slashed at C. -/
private def slashedOnC (split counted : BeaconState preset fork) : Finset ℕ :=
  (Finset.range counted.validators.data.size).filter fun i =>
    (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i]?.map (·.slashed)).getD false = true

/-- The bound on the effective balance of a key of R's registry that R's call reads.

It is the key's effective balance, its rise and one increment, if R's branch slashes it.

It is also at least the key's effective balance at the finalized state.

A prefix state of the finalized epoch can reach that balance.

`branchR` pays that bound for such a key, and its increment covers the drop of R's penalty.

A key that `exitedSlashable`, `late` or `pendingR` charges is read at its balance and rise, or `bF`.

It is also read at its effective balance at the finalized state.

It is read without `ebUp`, which can exceed them.

Otherwise it is also at least the key's bound `ebUp`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleEnv (t : PinTerms preset)
  (pulled anc fin : BeaconState preset fork) (i : ℕ) :
    ℕ :=
  if t.slashedRB i = true then
    max (balanceAt pulled i + t.rise i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (balanceAt fin i)
  else if PinTerms.exitedSlashable anc pulled i = true ∨
      (t.tight = false ∧ (t.lateB i = true ∨ t.pendingRB i = true)) then
    max (balanceAt pulled i + t.rise i) (max (t.bF i) (balanceAt fin i))
  else max (max (t.ebUp i) (balanceAt pulled i + t.rise i)) (t.bF i)

/-- A balance within the finalized effective balance is within `whistleEnv`, plus any slack.

The first two branches of `whistleEnv` hold the finalized effective balance.

The third holds `ebUp`, which is at least that. -/
private theorem short_end (h : Setting config checks g split fin pulled anc counted V) (i : ℕ)
    {X : ℕ} (hfin : X ≤ balanceAt fin i) (slack : ℕ) :
    X ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i + slack := by
  have up : balanceAt fin i ≤ (pinTerms config pulled anc fin).ebUp i :=
    Internal.effective_fin_le_ebUp h i
  unfold Internal.whistleEnv
  split_ifs <;> omega

/-- A state of C's run in the epoch of a state `c` has its effective balance within `whistleEnv`.

The run from `c` to it stays in one epoch.

So a key of the registry at `c` keeps its effective balance there.

If that balance at `c` is within the finalized one, `short_end` reads it, plus any slack.

The finalized state is the case `c = fin`. -/
private theorem short_in_fin (h : Setting config checks g split fin pulled anc counted V)
    {c : BeaconState preset fork}
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b)
    (member : tailC.Contains step) (i : ℕ) (inside : i < c.validators.data.size)
    (left : effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤ balanceAt fin i) (slack : ℕ)
    (sameEpoch : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch c).toNat) :
    effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i + slack
      := by
  obtain ⟨pre, post, -⟩ := tailC.contains_split step member
  have early : a.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
  have forward : (getCurrentEpoch c).toNat ≤ (getCurrentEpoch a.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps (fromC.append pre).chainSteps)
  have same : getCurrentEpoch a.state = getCurrentEpoch c :=
    UInt64.toNat_inj.mp (by omega)
  have kept := (fromC.append pre).effectiveKept_of_same_epoch early same i inside
  exact short_end h i (by rw [kept]; exact left) slack

/-- The credits that raise the effective balance of a key of R's registry on C's branch.

They are the key's credits at eleven tenths, rounded up, with the bands of credits and seat debits.

The credits hold the key's own whistleblower credits.

Its unit of gain and the leak that its sync debits induce on R's run come on top, unscaled.

`bud_whistle_of` pays them with the sets that it counts.

The seat debits are those of the two runs that R shares with C.

A key that exited before the finalized state also holds its credits on the shared segment.

A sync credit there has the band of its rounding. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleSlackBase (t : PinTerms preset)
  {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (rrun : Run config checks x' y') (highC high : ℕ)
    (eventsC eventsF events : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  (11 * (Internal.propN tail highC i + Internal.depPre eventsC i + Internal.whistC tail highC i +
    Internal.syncCr eventsC i +
    Internal.consAmt eventsC i + Internal.syncD eventsF i + Internal.syncD events i) + 9) / 10 +
      Internal.bandC tail highC i +
    Internal.bandX fin highC i + Internal.bandR (eventsF ++ events) i +
    Internal.unitK t tail highC eventsC events eventsF i + Internal.inducedR t rrun i +
  if t.exitBeforeFin i = true then
    (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX fin
      high i +
      (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0)
  else 0

/-- The credits of `whistleSlackBase`, and a second unit of gain for a key that R slashes.

The second unit pays the joint floor that R's slashing penalty can tip. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleSlack (t : PinTerms preset) {x y
  : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (rrun : Run config checks x' y') (highC high : ℕ)
    (eventsC eventsF events : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  Internal.whistleSlackBase t tail rrun highC high eventsC eventsF events fin i +
    (if 0 < Internal.slashW t i then t.unitGain else 0)

/-- What a created key's charge adds to the effective balance of the key at an earlier exit.

It is the band, the gains at the largest rate and the key's credits on C's branch. -/
private def whistleExtra (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : ℕ) (eventsC : List (BalanceEvent preset)) (i : ℕ) :
    ℕ :=
  preset.upwardBand + t.depth * t.gainRateMax +
    (Internal.credC tail high i + Internal.whistC tail high i + Internal.syncCr eventsC i)

/-- The bound on the effective balance at its slashing of a key of the split's registry.

A key that is not active at C and has a departure charge on C's branch is also read at its charge.

That reading is the charge, the key's rise after it, and the slack.

A charge in the split's own epoch reads the balance before the credits of `pre`.

So the key's proposer, whistleblower and sync credits over `pre` are read too.

The slashing starts the key's exit, or finds the exit that an earlier charge started. -/
private def whistleRead (t : PinTerms preset) (pulled anc counted : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {x' y' : ForkedBeaconState preset} (rrun : Run config checks x' y')
    {x'' y'' : ForkedBeaconState preset} (pre : Run config checks x'' y'') (highC high : ℕ)
    (eventsC eventsF events eventsP : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  if ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      (tail.departureCharges.any fun c => c.index == i) = true then
    min (Internal.whistleEnv t pulled anc fin i +
        Internal.whistleSlack t tail rrun highC high eventsC eventsF events fin i)
      (Internal.chargeAmt tail i + Internal.riseQ tail highC i + (Internal.propN pre highC i +
        Internal.whistC pre highC i +
        Internal.syncCr eventsP i) + Internal.whistleSlack t tail rrun highC high eventsC eventsF
          events fin i)
  else
    Internal.whistleEnv t pulled anc fin i + Internal.whistleSlack t tail rrun highC high eventsC
      eventsF events fin i

/-- The bound on the effective balance at its slashing of a key created after the split.

The key is active at C.

At a high gain rate it is the largest cap.

Otherwise it is the key's credits, their gains over the window, and a band. -/
private def createdCeil (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : ℕ) (eventsC : List (BalanceEvent preset)) (i : ℕ) :
    ℕ :=
  let credits := Internal.credC tail high i + Internal.whistC tail high i + Internal.syncCr eventsC
    i
  let rate := t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  if t.gainHigh = true then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else
    credits + t.depth * (11 * credits / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * rate /
      WEIGHT_DENOMINATOR.toNat) + t.depth * (rate / WEIGHT_DENOMINATOR.toNat + 2) +
        preset.downwardBand

/-- The gain of a created key's credits and base stake is at most the gain of its flows and a unit.

The key's base stake is credits, so it sits in the flows `Z`.

The flow of `Cr` and the slack `S - e0` compound at eleven tenths.

The floor holds the base gain `D * q` and `D`.

A key whose rate is low has `11 * D * q ≤ e0`, so its base gain is within a tenth of its stake.

The floors then lose one increment against the floor of the flows, which the unit pays. -/
private theorem created_gain_arith (I WD F P D e0 S Cr Z β : ℕ)
    (key : 11 * D * (P * F) < WD * I) (start : e0 ≤ S + β) (flows : Cr + S ≤ Z)
    (small : 11 * (β + D) < 10 * I) :
    D * (11 * (Cr + (S - e0) + D * (e0 / I * P * F / WD) + D) / (10 * I) * P * F / WD) +
        (D * (e0 / I * P * F / WD) + D) ≤
      D * (11 * Z / (10 * I) * P * F / WD) + D * (P * F / WD + 2) := by
  have hWD : 0 < WD := Nat.pos_of_ne_zero fun zero => by
    rw [zero] at key
    omega
  simp only [Nat.mul_assoc]
  obtain ⟨a, ha⟩ : ∃ a, a = P * F := ⟨_, rfl⟩
  rw [← ha] at key ⊢
  obtain ⟨N2, hN2⟩ : ∃ N2, N2 = e0 / I := ⟨_, rfl⟩
  rw [← hN2]
  obtain ⟨q, hq⟩ : ∃ q, q = N2 * a / WD := ⟨_, rfl⟩
  rw [← hq]
  -- the base gain is at most a eleventh of the stake
  have baseGain : 11 * (D * q) ≤ e0 := by
    have floor : q * WD ≤ N2 * a := by rw [hq]; exact Nat.div_mul_le_self _ _
    have step : 11 * D * q * WD ≤ WD * I * N2 := by
      calc 11 * D * q * WD = 11 * D * (q * WD) := by ring
        _ ≤ 11 * D * (N2 * a) := Nat.mul_le_mul_left _ floor
        _ = N2 * (11 * D * a) := by ring
        _ ≤ N2 * (WD * I) := Nat.mul_le_mul_left _ key.le
        _ = WD * I * N2 := by ring
    have cancel : 11 * D * q ≤ I * N2 := by
      refine Nat.le_of_mul_le_mul_right (c := WD) ?_ hWD
      calc 11 * D * q * WD ≤ WD * I * N2 := step
        _ = I * N2 * WD := by ring
    have rounded : I * N2 ≤ e0 := by rw [hN2]; exact Nat.mul_div_le _ _
    calc 11 * (D * q) = 11 * D * q := by ring
      _ ≤ e0 := Nat.le_trans cancel rounded
  obtain ⟨X, hX⟩ : ∃ X, X = Cr + (S - e0) + D * q + D := ⟨_, rfl⟩
  rw [← hX]
  have total : 11 * X + 10 * e0 ≤ 11 * Z + 11 * (β + D) := by omega
  -- the floors of the stake and of the credits add to one floor
  obtain ⟨N1, hN1⟩ : ∃ N1, N1 = 11 * X / (10 * I) := ⟨_, rfl⟩
  obtain ⟨N3, hN3⟩ : ∃ N3, N3 = 11 * Z / (10 * I) := ⟨_, rfl⟩
  rw [← hN1, ← hN3]
  have joint : N1 + N2 ≤ N3 + 1 := by
    have n2 : N2 = 10 * e0 / (10 * I) := by
      rw [hN2, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 10)]
    have add := Nat.div_add_div_le_add_div (x := 11 * X) (y := 10 * e0) (z := 10 * I)
    have mono := Nat.div_le_div_right (c := 10 * I) total
    have more := Nat.add_div_le_div_add_div_add_one (11 * Z) (11 * (β + D)) (10 * I)
    have none : 11 * (β + D) / (10 * I) = 0 := Nat.div_eq_of_lt small
    omega
  have gains : N1 * a / WD + N2 * a / WD ≤ N3 * a / WD + a / WD + 1 := by
    have add := Nat.div_add_div_le_add_div (x := N1 * a) (y := N2 * a) (z := WD)
    have mono : (N1 + N2) * a / WD ≤ (N3 + 1) * a / WD :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ joint)
    have more := Nat.add_div_le_div_add_div_add_one (N3 * a) a WD
    rw [Nat.add_mul] at mono
    rw [Nat.add_mul, Nat.one_mul] at mono
    omega
  have scaled := Nat.mul_le_mul_left D gains
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one] at scaled
  rw [← hq] at scaled
  rw [Nat.mul_add D (a / WD) 2]
  omega

/-- The deposits and consolidations that a run credits to a key are among its non-reward credits. -/
private theorem scan_deposits_consolidations_le (v high : ℕ) {x y : ForkedBeaconState preset}
    (run : Run config checks x y) :
    (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high run) +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v high run) ≤
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v high run) := by
  have named := Internal.creditScan_or (fun _ => false) (fun s => decide (s ≠ .rewards))
    (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits ∨ s = .consolidations))
    (fun s => decide (s ≠ .rewards ∧ s ≠ .deposits ∧ s ≠ .consolidations))
    (fun _ => rfl) (fun s => by cases s <;> decide) (fun _ => by simp)
    (fun s => by cases s <;> decide) v high run
  have pair := Internal.creditScan_or (fun _ => false)
    (fun s => decide (s = .deposits ∨ s = .consolidations)) (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits)) (fun s => decide (s = .consolidations))
    (fun _ => rfl) (fun s => by cases s <;> decide) (fun _ => by simp)
    (fun s => by cases s <;> decide) v high run
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key created on C's branch is at most its credits and their gains.

The run from the split reaches a state `z` where the key holds the activation reserve, and then C.

The bound holds at every state of C's run after `z`, and at C.

The key's base stake is credits, so one floor of the flows pays its gain.

The rate premise is that of the low regime: `key` reads it at the depth of the call. -/
private theorem created_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (key : 11 * (min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
      (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
        WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    let Z := Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
      Internal.syncCr eventsC v.toNat
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ z)
      (post : Run config checks z ⟨fork, counted⟩), tailC = pre.append post ∧ 0 < Z ∧
      (∀ p ∈ pre.balancePath, ∀ w : Validator, p.state.validators.data[v.toNat]? = some w →
        w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch p.state).toNat + 1 < w.activationEpoch.toNat) ∧
      ∀ p ∈ post.balancePath, effectiveAt p v.toNat ≤ Z +
        (min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          (11 * Z / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
            (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
        (min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) +
        preset.downwardBand := by
  classical
  intro Z
  obtain ⟨z, pre, post, splitEq, zEarly, zFork, zCounted, inside, funded, hysteresis, reserve,
    walk, -, ahead⟩ := Internal.created_start h tailC highC endEpochC
      activated absent
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have flows : Internal.grossScan v.toNat highC tailC +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC tailC) ≤
        Z :=
    (Internal.credits_le_sources shared h.genesis tailC h.early electra v.toNat highC replayedC).1
  have incPos := h.bands.1
  have alignedMax := (Internal.cap_values_aligned h.aligned).2
  have fuluZ : .fusaka ≤ z.fork := Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)
  have electraZ : .pectra ≤ z.fork := Nat.le_trans (by decide) fuluZ
  obtain ⟨P', hP', rate⟩ := Internal.key_rate_pre h tailC h.near
  obtain rfl : P = P' := hP.trans hP'.symm
  have inRun : ∀ p ∈ post.balancePath, p ∈ tailC.balancePath := fun p member => by
    obtain ⟨front, last⟩ := Run.balancePath_last pre
    obtain ⟨rest, head⟩ := Run.balancePath_head post
    rw [head] at member
    rw [splitEq, Run.balancePath_append, last, head]
    rcases List.mem_cons.mp member with rfl | later <;> simp [*]
  have backZ : (⟨fork, counted⟩ : ForkedBeaconState preset).fork ≤ z.fork := by
    have := fork_le_of_chainSteps pre.chainSteps
    exact this
  have capCeil : ∀ p ∈ post.balancePath, PinTerms.capAt p v.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := fun p member => by
    obtain ⟨r1, -, -⟩ := Internal.balancePath_endpoint post
      (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) backZ member
    exact Internal.capAt_le_capMax h.caps (Nat.le_trans electraZ (fork_le_of_chainSteps
      r1.chainSteps))
      v.toNat
  have splitZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) := ⟨_, rfl⟩
  rw [← hD] at key ⊢
  obtain ⟨e0, he0⟩ : ∃ e0, e0 = effectiveAt z v.toNat := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = actualBalanceAt z v.toNat := ⟨_, rfl⟩
  obtain ⟨Cr, hCr⟩ : ∃ Cr, Cr = Internal.netScan v.toNat highC post +
    (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC post) :=
    ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = S - e0 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, rfl⟩
  have alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [he0]
    exact FloorTrace.effective_aligned (shared.append pre) h.genesis h.aligned v.toNat
  have core := Internal.c_ceiling_abstract post h.early fuluZ v.toNat inside highC P
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat alignedMax
    (Internal.effectiveAt_le_capMax (shared.append pre) h.genesis h.caps zEarly v.toNat)
    capCeil
    (fun p member total perIncrement totalOk perOk =>
      rate p (inRun p member) total perIncrement totalOk perOk)
    endEpochC incPos D Cr Cr e0 C S W (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq
    alignedE0 hC (by simp only at splitZ ⊢; omega) (by rw [hS]; exact Nat.min_le_left _ _)
    (by omega) (le_of_eq hCr.symm) key (by omega)
  obtain ⟨gc, rfl, -, bound, -⟩ := core
  -- the credits, the base stake and the gains of the key
  have beforeZ : S ≤ Internal.grossScan v.toNat highC pre +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC pre) +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v.toNat highC
        pre) := by
    rw [hS]
    exact walk
  have splitScans := scan_deposits_consolidations_le v.toNat highC pre
  subst splitEq
  rw [Internal.grossScan_append, Internal.creditScan_append (fun _ => false) (fun s => decide (s ≠
    .rewards))
    v.toNat highC pre post] at flows
  obtain ⟨e2, ok2⟩ := post.balanceEvents_ok h.early highC
  have netLe := (Internal.credits_le_sources (shared.append pre) h.genesis post h.early electraZ
    v.toNat
    highC ok2).2.1
  have credited : Cr + S ≤ Z := by omega
  -- the key's rate is low against an increment, so the depth is small
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  have quarter := h.facts.quarterBand
  have four : 4 ≤ P := by
    rw [hP]
    exact Internal.four_le_perIncrement h
  have small : 11 * (preset.downwardBand + D) < 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [weights, denominator] at key
    have scaled := Nat.mul_le_mul_left D (show 4 * 54 ≤ P * 54 by omega)
    have regroup : 11 * D * (P * 54) = 11 * (D * (P * 54)) := by ring
    omega
  have arith := created_gain_arith preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D e0 S Cr Z
    preset.downwardBand key (by rw [he0, hS]; exact hysteresis) credited small
  rw [← hq, ← hW] at arith
  refine ⟨z, pre, post, rfl, ?_, ahead, fun p member => ?_⟩
  · have := Internal.maxEffectiveBalance_pos h
    omega
  obtain ⟨r1, r2, cut⟩ := Internal.balancePath_endpoint post
    (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) backZ member
  have prefixPath : ∀ z' ∈ r1.balancePath, z' ∈ post.balancePath := fun z' mem => by
    have joined : post.balancePath = r1.balancePath ++ r2.balancePath.tail := by
      rw [← Run.balancePath_append]
      exact congrArg Run.balancePath cut.symm
    rw [joined]
    exact List.mem_append_left _ mem
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  have ceiling := Internal.Run.effective_ceiling_of_balance_ceiling r1 pEarly fuluZ v.toNat
    inside
    (S + Cr + (D * (11 * (Cr + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
        (D * q + D)))
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat alignedMax
    (Internal.effectiveAt_le_capMax (shared.append pre) h.genesis h.caps zEarly v.toNat)
    (fun z' mem => bound z' (prefixPath z' mem)) (fun z' mem => capCeil z' (prefixPath z' mem))
  obtain ⟨-, same, third, ordered⟩ := ceiling
  by_cases crossed : (getCurrentEpoch z.state).toNat < (getCurrentEpoch p.state).toNat
  · have := third crossed
    omega
  · have stays := same (by omega)
    omega

/-- Off the high gain rate, the full window's weighted gain is below an increment. -/
private theorem wide_of_lowGain (h : Setting config checks g split fin pulled anc counted V)
    (lowGain : (pinTerms config pulled anc fin).gainHigh = false) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have low : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
    have notHigh : (!decide (11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)) = false := lowGain
    simpa using notHigh
  have gainMax : (pinTerms config pulled anc fin).gainRateMax =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := rfl
  exact Internal.rate_per_increment preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
    (pinTerms config pulled anc fin).perIncrement
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat (pinTerms config pulled anc fin).depth
    h.bands.1 (by decide) (Internal.cap_values_aligned h.aligned).2 (by rw [← gainMax]; exact low)

/-- Off the high gain rate, the depth of the window is small against the rate.

It is below an eleventh of an increment.

It is the rate premise of `created_ceiling` and `created_key_ceiling`. -/
private theorem key_of_lowGain (h : Setting config checks g split fin pulled anc counted V)
    (lowGain : (pinTerms config pulled anc fin).gainHigh = false) :
    11 * (min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (Nat.min_le_left _ _)))
    (wide_of_lowGain h lowGain)

/-- The kept arm's test bounds the gain at the full depth. -/
private theorem keptArm_eq (i : ℕ)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).gainRate i + 1) ≤
      (pinTerms config pulled anc fin).ebUp i := by
  simp only [pinTerms, Bool.and_eq_true, decide_eq_true_eq] at kept
  exact kept.2

/-- The kept arm bounds the gain per increment up to the full depth. -/
private theorem key_of_kept (h : Setting config checks g split fin pulled anc counted V)
    (i D : ℕ) (depth : D ≤ (pinTerms config pulled anc fin).depth)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    11 * D * ((pinTerms config pulled anc fin).perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  exact Internal.rate_per_increment _ _ _ _ _ _ h.bands.1 (by decide) (Internal.ebUp_aligned h i)
    (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 depth)) (keptArm_eq i kept))

/-- A key created after the split that is active at C has the bound `createdCeil` at its slashing.

Its credits since its creation are credits of C's branch, which `created_ceiling` reads.

The credits of the run are at most `credC`, `whistC` and the seat credits, so the bound reads them.

Off the high gain rate, `gainHigh` is false, which gives the rate premise of `created_ceiling`. -/
private theorem created_active (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : ¬ i < split.validators.data.size)
    (active : isActiveAt counted (getCurrentEpoch counted) i = true)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    effectiveAt a i ≤ createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨pre', post', cut', aEarly, -⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  by_cases high : (pinTerms config pulled anc fin).gainHigh = true
  · simp only [createdCeil, high, ↓reduceIte]
    exact Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre') h.genesis h.caps
      aEarly i
  have lowGain : (pinTerms config pulled anc fin).gainHigh = false := by simpa using high
  -- the key as a validator index
  obtain ⟨w, found, -⟩ := isActiveAt_eq_true_iff.mp active
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have below := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  obtain ⟨v, hvi⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  subst hvi
  have member_active : v ∈ activeVoters counted :=
    List.mem_toFinset.mpr (mem_getActiveValidatorIndices_of_isActiveAt active)
  have activated := Internal.activated_of_activeVoters h.early member_active
  have absent : split.validators.data.size ≤ v.toNat := Nat.le_of_not_lt created
  have key := key_of_lowGain h lowGain
  obtain ⟨z, pre, post, cut, positive, ahead, bound⟩ := created_ceiling h tailC highC endEpochC
    replayedC activated absent (pinTerms config pulled anc fin).perIncrement rfl key
  -- the state `a` is a state of the run, so it is before `z` or after it
  have inPath : a ∈ tailC.balancePath := by
    rw [cut', Run.balancePath_append]
    refine List.mem_append_left _ ?_
    simp only [Run.balancePath, List.mem_append]
    exact .inr (List.mem_of_mem_head? (Step.balancePath_ends step).1)
  have ends : a ∈ pre.balancePath ∨ a ∈ post.balancePath := by
    rw [cut, Run.balancePath_append] at inPath
    rcases List.mem_append.mp inPath with first | later
    · exact .inl first
    · exact .inr (List.mem_of_mem_tail later)
  rcases ends with before | after
  · -- a key that the step slashes was activated by the epoch of `a`, which `z` comes after
    have bEarly : b.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps post'.chainSteps) h.early
    have finite : getCurrentEpoch a.state < FAR_FUTURE_EPOCH :=
      UInt64.lt_iff_toNat_lt.mpr (by
        have := getCurrentEpoch_succ_lt_farFuture h.twoSlots a.state
        omega)
    obtain ⟨u, found, far, reached⟩ := Step.slashed_activated step
      (Nat.le_trans electra (fork_le_of_chainSteps pre'.chainSteps)) bEarly h.caps.activation
      h.caps.compounding (Internal.Setting.delay h) finite v.toNat
      (((shared.append fromFin).append pre').exit_activated h.genesis v.toNat) flag
    have := ahead a before u found far
    have := UInt64.le_iff_toNat_le.mp reached
    omega
  have ceiling := bound a after
  have minLe : min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) ≤
        (pinTerms config pulled anc fin).depth := Nat.min_le_left _ _
  simp only [createdCeil, lowGain, Bool.false_eq_true, ↓reduceIte]
  rw [Nat.mul_assoc (11 * _ / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))] at ceiling
  exact ceiling.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ minLe) _) (Nat.mul_le_mul_right _ minLe)) le_rfl)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The whistleblower credits of any set of keys on C's branch are at most the reward base.

The base is the slashing reward of each key slashed on that branch, read at its balance then.

A key of the split's registry is read at the bound `registry` gives for it.

If it is not active at C and has a charge there, it is also read at `registryCharge`.

`registry` is asked for each key that is unslashed at the split, at each step of C's branch.

A key slashed before the split has no term, since its credit on C's branch is zero.

A key of R's registry that is also slashed on R's branch is a term of the first sum.

A consumer that pays those terms by another budget splits that sum by the key's slashing on R.

A key created after the split is read at `createdCeil` if it is active at C.

If it has exited by C, it is read at its charge and credits.

A charge in the split's own epoch also reads the credits of `pre`, the run from that epoch's start.

`registryCharge` takes the facts that tie `pre` to the run, and this lemma does not use them. -/
private theorem whistle_core (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
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
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.whistC tailC highC v.toNat ≤
      (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
            (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      (∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true),
        min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      (∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true),
        min (Internal.chargeAmt tailC i +
            whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have limit := whistC_sum_le_limits (shared.append fromFin) h.genesis tailC h.early highC
    replayedC S
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ, ∀ i, E i =
      if (split.validators.data[i]?.map (·.slashed)).getD false = false then
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
            (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨cr, hcr⟩ : ∃ cr : ℕ → ℕ, ∀ i, cr i =
      if isActiveAt counted (getCurrentEpoch counted) i = true then
        min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
      else min (Internal.chargeAmt tailC i +
          whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := ⟨_, fun _ => rfl⟩
  -- the keys of R's registry are read at `registry`, or at the largest cap if slashed at the split
  have regE : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i ≤ E i := by
    intro a b step member i inside flag
    rw [hE i]
    obtain ⟨pre, -, -, aEarly, -⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
    have capped := Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre)
      h.genesis
      h.caps aEarly i
    by_cases unslashed : (split.validators.data[i]?.map (·.slashed)).getD false = false
    · simp only [unslashed]
      refine le_min ?_ capped
      simp only [whistleRead]
      split
      · rename_i cond
        exact le_min (registry step member i inside unslashed flag)
          (registryCharge step member i inside unslashed flag cond.2)
      · exact registry step member i inside unslashed flag
    · simp only [unslashed]
      exact capped
  -- the created keys are read at `createdCeil` while active at C, and at their charge after
  have createdE : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, split.validators.data.size ≤ i →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ cr i := by
    intro a b step member i created flag
    rw [hcr i]
    obtain ⟨pre, -, -, aEarly, -⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
    have capped := Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre)
      h.genesis
      h.caps aEarly i
    by_cases act : isActiveAt counted (getCurrentEpoch counted) i = true
    · simp only [act]
      exact Nat.div_le_div_right (le_min (created_active h tailC highC endEpochC replayedC step
        member i (Nat.not_lt.mpr created) act flag) capped)
    · simp only [act]
      exact Nat.div_le_div_right (le_min (Internal.created_charge h fromFin tailC
        (whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC)
        (fun step member i created old foundA assigned =>
          earlier_charge h tailC highC endEpochC replayedC step member i created old foundA
            assigned) step member i created flag) capped)
  have charged := Internal.slashing_charge h fromFin tailC highC endEpochC replayedC E cr regE
    createdE
  refine limit.trans (charged.trans (le_of_eq ?_))
  -- the sum over the slashed keys splits into the three kinds of key
  change ∑ i ∈ slashedOnC split counted, _ = _
  rw [← Finset.sum_filter_add_sum_filter_not (slashedOnC split counted)
    (fun i => i < split.validators.data.size)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)]
  rw [← add_assoc]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
    have unslashed := (Finset.mem_filter.mp inSlashed).2.1
    simp only [inside, ↓reduceIte, hE i, unslashed]
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inNew, act⟩ := Finset.mem_filter.mp member
    have outside := (Finset.mem_filter.mp inNew).2
    simp [outside, hcr i, act]
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inNew, act⟩ := Finset.mem_filter.mp member
    have outside := (Finset.mem_filter.mp inNew).2
    simp [outside, hcr i, act]

/-- The sum of a function of the positions over the images of the positions of a set is its sum. -/
private theorem sum_image_ofNat (T : Finset ℕ) (small : ∀ i ∈ T, i < 2 ^ 64) (f : ℕ → ℕ) :
    ∑ v ∈ T.image UInt64.ofNat, f v.toNat = ∑ i ∈ T, f i := by
  rw [Finset.sum_image fun a ha b hb same => by
    rw [← UInt64.toNat_ofNat_of_lt' (small a ha), ← UInt64.toNat_ofNat_of_lt' (small b hb), same]]
  exact Finset.sum_congr rfl fun i member => by rw [UInt64.toNat_ofNat_of_lt' (small i member)]

/-- A slashed flag at a position of the registry is the flag that `slashedOnC` reads. -/
private theorem slashedFlagAt_eq_some {s : BeaconState preset fork} {i : ℕ} {b : Bool} :
    slashedFlagAt s i = some b ↔
      i < s.validators.data.size ∧ (s.validators.data[i]?.map (·.slashed)).getD false = b := by
  constructor
  · intro flag
    have inside : i < s.validators.data.size := by
      by_contra out
      simp [slashedFlagAt, Array.getElem?_eq_none (Nat.le_of_not_lt out)] at flag
    refine ⟨inside, ?_⟩
    unfold slashedFlagAt at flag
    rw [flag]
    rfl
  · rintro ⟨inside, flag⟩
    simp only [slashedFlagAt, Array.getElem?_eq_getElem inside, Option.map_some] at flag ⊢
    simpa using flag

/-- The keys of `SC` are the keys of `slashedOnC` inside the split's registry, read at positions. -/
private theorem sum_SC_positions (h : Setting config checks g split fin pulled anc counted V)
    (f : ℕ → ℕ) :
    ∑ v ∈ Internal.SC pulled counted split, f v.toNat =
      ∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size), f i := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  have limit := BeaconState.validators_size_lt_of_lt_glamsterdam h.early pulled
  rw [← Finset.sum_image (f := f) (g := UInt64.toNat) fun a _ b _ same => UInt64.toNat_inj.mp same]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  constructor
  · intro mem
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp mem
    obtain ⟨-, hcs, hss⟩ := Finset.mem_filter.mp hv
    obtain ⟨hsplit, flagS⟩ := slashedFlagAt_eq_some.mp hss
    obtain ⟨hcount, flagC⟩ := slashedFlagAt_eq_some.mp hcs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcount, flagS, flagC⟩, hsplit⟩
  · intro mem
    obtain ⟨hmem, hin⟩ := Finset.mem_filter.mp mem
    obtain ⟨hrange, hsl, hcs⟩ := Finset.mem_filter.mp hmem
    have below := (Nat.lt_of_lt_of_le hin grows).trans limit
    refine Finset.mem_image.mpr ⟨UInt64.ofNat i, ?_, UInt64.toNat_ofNat_of_lt' below⟩
    rw [Internal.SC, Finset.mem_filter, UInt64.toNat_ofNat_of_lt' below]
    exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩,
      slashedFlagAt_eq_some.mpr ⟨Finset.mem_range.mp hrange, hcs⟩,
      slashedFlagAt_eq_some.mpr ⟨hin, hsl⟩⟩

/-- The keys of `CS` are the keys of `slashedOnC` beyond the split's registry, read at positions. -/
private theorem sum_CS_positions (h : Setting config checks g split fin pulled anc counted V)
    (f : ℕ → ℕ) :
    ∑ v ∈ Internal.CS counted split, f v.toNat =
      ∑ i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size), f i := by
  classical
  rw [← Finset.sum_image (f := f) (g := UInt64.toNat) fun a _ b _ same => UInt64.toNat_inj.mp same]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  constructor
  · intro mem
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp mem
    obtain ⟨-, hge, hcs⟩ := Finset.mem_filter.mp hv
    obtain ⟨hcount, flagC⟩ := slashedFlagAt_eq_some.mp hcs
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcount, ?_, flagC⟩,
      Nat.not_lt.mpr hge⟩
    simp [Array.getElem?_eq_none hge]
  · intro mem
    obtain ⟨hmem, hout⟩ := Finset.mem_filter.mp mem
    obtain ⟨hrange, hsl, hcs⟩ := Finset.mem_filter.mp hmem
    have below := (Finset.mem_range.mp hrange).trans
      (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
    refine Finset.mem_image.mpr ⟨UInt64.ofNat i, ?_, UInt64.toNat_ofNat_of_lt' below⟩
    rw [Internal.CS, Finset.mem_filter, UInt64.toNat_ofNat_of_lt' below]
    exact ⟨Finset.mem_image.mpr ⟨i, hrange, rfl⟩, Nat.not_lt.mp hout,
      slashedFlagAt_eq_some.mpr ⟨Finset.mem_range.mp hrange, hcs⟩⟩

/-- The keys of `SC` that satisfy a test at their positions are those positions of `slashedOnC`. -/
private theorem sum_SC_filter_positions (h : Setting config checks g split fin pulled anc counted V)
    (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) :
    ∑ v ∈ Internal.SC pulled counted split with p v.toNat, f v.toNat =
      ∑ i ∈ ((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter p,
        f i :=
  (Finset.sum_filter _ _).trans ((sum_SC_positions h (fun i => if p i then f i else 0)).trans
    (Finset.sum_filter _ _).symm)

/-- A key that C slashes after the split, and that R neither slashes nor exits, keeps its exit late.

The exit guard of its run from the finalized block holds along the run.

Its exit at C is after R's cutoff less the delay.

The exit is assigned on C's run, so it is a departure charge there, after the split.

Or it is assigned by the split, and then it is kept, and so it is R's exit.

R's exit is then after the cutoff.

Or R holds the key withdrawable by the finalized epoch, which `sc3a_unwithdrawn` excludes. -/
private theorem slashedC_retained (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (i : ValidatorIndex)
    (slashedC : i.toNat ∈ slashedOnC split counted)
    (inside : i.toNat < split.validators.data.size)
    (notR : ¬ (pinTerms config pulled anc fin).slashedRB i.toNat = true)
    (notExit : ¬ PinTerms.exitedSlashable anc pulled i.toNat = true) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) := by
  classical
  obtain ⟨hLt, hSplit, hCount⟩ : i.toNat < counted.validators.data.size ∧
      (split.validators.data[i.toNat]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i.toNat]?.map (·.slashed)).getD false = true := by
    simpa [slashedOnC] using slashedC
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨vS, foundS⟩ : ∃ v, split.validators.data[i.toNat]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨wC, foundC⟩ : ∃ w, counted.validators.data[i.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem hLt⟩
  have unslashedS : vS.slashed = false := by simpa [foundS] using hSplit
  have slashedAtC : wC.slashed = true := by simpa [foundC] using hCount
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  simp only at finSplit
  have shallow := h.shallow
  have slashC := tailC.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
    h.early (Internal.Setting.delay h) i.toNat vS wC foundS foundC unslashedS slashedAtC
  have late : (getCurrentEpoch pulled).toNat + 1 <
      wC.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    by_cases unset : vS.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨c, mem, -, epoch⟩ := Internal.Run.charge_of_exit tailC electra h.early i.toNat
        (fun v found => by
          rw [foundS] at found
          cases found
          exact unset) wC foundC slashC.1
      have start := Run.departureCharges_epoch_ge_start tailC electra h.early c mem
      simp only at start
      omega
    · obtain ⟨wL, foundL, kept⟩ := tailC.registryLifecycle.validators i.toNat vS foundS
      obtain rfl : wL = wC := Option.some.inj (foundL.symm.trans foundC)
      have exitC := congrArg UInt64.toNat (kept.exitEpoch unset)
      obtain ⟨wR, foundR, keptR⟩ := tail.registryLifecycle.validators i.toNat vS foundS
      have exitR := congrArg UInt64.toNat (keptR.exitEpoch unset)
      by_cases far : (getCurrentEpoch pulled).toNat + 1 < wR.exitEpoch.toNat
      · omega
      have unslashedR : wR.slashed = false := by
        by_contra marked
        exact notR (Internal.slashedRB_of_newly_slashed h foundS foundR unslashedS (by simpa using
          marked))
      exfalso
      refine sc3a_unwithdrawn h foundS foundR foundC unslashedS slashedAtC unslashedR ?_
      by_contra waiting
      have reached : wR.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
      have lt := Nat.lt_of_not_le waiting
      apply notExit
      simp [PinTerms.exitedSlashable, foundR, unslashedR, reached, lt]
  intro m n before step after cut w found
  exact Internal.retained_of_exit h fromFin tailC _ (Nat.le_refl _) i foundC late before step after
    cut w
    found

/-- A key that R holds withdrawable by the next epoch is a key with `withdrawnRB`. -/
private theorem withdrawnRB_of_le (config : Config) (pulled anc fin : BeaconState preset fork)
    {i : ℕ} {w : Validator} (found : pulled.validators.data[i]? = some w)
    (le : w.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    (pinTerms config pulled anc fin).withdrawnRB i = true := by
  simp only [pinTerms]
  simp [found, le]

/-- The deposit credits of some events are within `depPre` when each credited one is unslashed. -/
private theorem deposits_le_depPre (L : List (BalanceEvent preset)) (i : ℕ)
    (clean : ∀ e ∈ L, e.source = .deposits →
      Internal.keyCredit i e = 0 ∨ ¬ slashedFlagAt e.before.state i = some true) :
    ((L.filter fun e => e.source = .deposits).map (Internal.keyCredit i)).sum ≤ Internal.depPre L i
      := by
  induction L with
  | nil => simp [Internal.depPre]
  | cons e rest ih =>
    have tail := ih fun x member => clean x (List.mem_cons_of_mem _ member)
    unfold Internal.depPre at tail ⊢
    by_cases dep : e.source = .deposits
    · rcases clean e List.mem_cons_self dep with zero | unslashed
      · by_cases slashed : slashedFlagAt e.before.state i = some true <;>
          simp [dep, zero, slashed] <;> omega
      · simp [dep, unslashed]
        omega
    · simp [dep]
      omega

/-- Each deposit of a run's replay that credits a key finds it unslashed.

The run ends with the key unslashed.

A deposit event of a block credits no balance.

One of a slot step starts from a state that does not hold the key slashed.

A slashed key stays slashed up to the end of the run. -/
private theorem prefix_deposits_clean (h : Setting config checks g split fin pulled anc counted V)
    {a : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (aEarly : a.fork < .glamsterdam) (highC : ℕ) {e1 : List (BalanceEvent preset)}
    (replayed1 : pre.balanceEvents highC = .ok e1) (v : ValidatorIndex)
    (unslashedA : (a.state.validators.data[v.toNat]?.map (·.slashed)).getD false = false) :
    ∀ e ∈ e1, e.source = .deposits →
      Internal.keyCredit v.toNat e = 0 ∨ ¬ slashedFlagAt e.before.state v.toNat = some true := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  intro e member dep
  rcases (Internal.run_located pre electra aEarly highC replayed1).1 e member dep with
    unconditional | ⟨u, w, ok, es, contains, replayedEs, inEs, -⟩
  · have := unconditional v.toNat
    unfold Internal.keyCredit
    omega
  · right
    intro slashed
    obtain ⟨p1, p2, -⟩ := pre.contains_split (Step.slot ok) contains
    have wEarly : w.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps p2.chainSteps) aEarly
    have holds := Run.invariant h.genesis.invariant ((toFin.append fromFin).append p1)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, one, two, -⟩ :=
      (Step.balanceEvents_sites (Step.slot ok) wEarly holds h.caps.compounding replayedEs) e inEs
    obtain ⟨x, found, flagged⟩ : ∃ x, e.before.state.validators.data[v.toNat]? = some x ∧
        x.slashed = true := by
      unfold slashedFlagAt at slashed
      cases hx : e.before.state.validators.data[v.toNat]? <;> simp_all
    obtain ⟨y, foundA, flagA⟩ :=
      ((one.trans two).trans p2.slashedPersistence) v.toNat x found flagged
    simp [foundA, flagA] at unslashedA

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A bound along R's run from the first state of a key holds on the whole run.

Before the first state `c` the key is absent, so its effective balance is zero there. -/
private theorem path_le_of_start {a e : ForkedBeaconState preset} {c : BeaconState preset fork}
    (toC : Run config checks a ⟨fork, c⟩) (fromC : Run config checks ⟨fork, c⟩ e) (i X : ℕ)
    (before : ∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p i = 0)
    (after : ∀ z ∈ fromC.balancePath, effectiveAt z i ≤ X) :
    ∀ z ∈ (toC.append fromC).balancePath, effectiveAt z i ≤ X := by
  intro z member
  rw [Run.balancePath_append] at member
  rcases List.mem_append.mp member with front | later
  · rcases before z front with atC | zero
    · obtain ⟨rest, head⟩ := Run.balancePath_head fromC
      rw [atC]
      exact after _ (by rw [head]; exact List.mem_cons_self)
    · rw [zero]
      exact Nat.zero_le _
  · exact after z (List.mem_of_mem_tail later)

/-- No due entry names a key past the registry when the targets of the queue are inside it. -/
private theorem dueAt_eq_zero_of_targets (X : BeaconState preset fork) (high : ℕ)
    {v : ValidatorIndex}
    (inside : ∀ electra : .pectra ≤ fork, ∀ c ∈ (X.pendingConsolidations electra).data.toList,
      c.targetIndex.toNat < X.validators.data.size)
    (outside : X.validators.data.size ≤ v.toNat) : Internal.dueAt X high {v} = 0 := by
  unfold Internal.dueAt
  split
  · rename_i electra
    have none : (X.pendingConsolidations electra).data.toList.filter
        (fun c => decide (c.targetIndex ∈ ({v} : Finset ValidatorIndex))) = [] :=
      List.filter_eq_nil_iff.mpr fun c member => by
        have target := inside electra c member
        simp only [Finset.mem_singleton, decide_eq_true_eq]
        rintro rfl
        omega
    rw [none]
    rfl
  · rfl

/-- A key created after the split and activated by C has a deposit credit on C's run.

It holds the activation reserve at its start.

No gross block credit reaches it before its activation, so a deposit or a consolidation pays it.

A consolidation needs an entry of the finalized queue, whose target is inside that registry. -/
private theorem created_deposit (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
      := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  by_contra none
  have depZero := Nat.eq_zero_of_not_pos none
  have finGrows : fin.validators.data.size ≤ split.validators.data.size :=
    registryGrows_of_chainSteps fromFin.chainSteps
  obtain ⟨_, pre, post, splitEq, -, -, -, -, funded, -, -, walk, noGross, -⟩ :=
    Internal.created_start h tailC highC endEpochC activated absent
  have positive := Internal.maxEffectiveBalance_pos h
  have consScan : (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations))
    v.toNat
      highC tailC) ≤ Internal.consAmt eventsC v.toNat :=
    Internal.scan_le_events _ _ (· = .consolidations) (by intro s; simp) tailC highC v replayedC
  subst splitEq
  have depSplit := Internal.creditScan_append (fun _ => false) (fun s => decide (s = .deposits))
    v.toNat highC pre post
  have consSplit := Internal.creditScan_append (fun _ => false) (fun s => decide (s =
    .consolidations))
    v.toNat highC pre post
  have noCons := Internal.consAmt_zero h fromFin replayedF (pre.append post) highC endEpochC h.near
    replayedC v (dueAt_eq_zero_of_targets fin highC (toFin.pendingConsolidation_targets
      h.genesis h.early (Internal.Setting.delay h)) (by omega))
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C's branch holds beyond the split pays an upward band.

`created_deposit` gives it a deposit credit on C's run, so it has the credit band. -/
private theorem created_band (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    preset.upwardBand ≤ Internal.bandC tailC highC v.toNat + Internal.bandX fin highC v.toNat := by
  have replayedF' := replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called h)
    replayedF
  have deposit :=
    created_deposit h fromFin replayedF' tailC highC endEpochC replayedC activated absent
  have positive : 0 < Internal.grossScan v.toNat highC tailC +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
        := by
    omega
  have band : Internal.bandC tailC highC v.toNat = preset.upwardBand := by
    unfold Internal.bandC
    simp [positive]
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of `SC` that R neither slashes nor exits, and that is not active at C, is charged on C.

An exit unset at the split is set by the key's slashing on C's run, which charges it.

An exit set at the split belongs to a key activated by the split's epoch.

If R slashes the key, its withdrawal is a vector past the split, so `slashedRB` holds.

Otherwise its exit is after R's next epoch, or `exitedSlashable` counts it.

An exit after R's next epoch leaves the key active at C. -/
private theorem sc_inactive_charged (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {i : ℕ}
    (member : i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size))
    (notRB : ¬ (pinTerms config pulled anc fin).slashedRB i = true)
    (notES : ¬ PinTerms.exitedSlashable anc pulled i = true)
    (inactive : ¬ isActiveAt counted (getCurrentEpoch counted) i = true) :
    ∃ c ∈ tailC.departureCharges, c.index = i := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
  obtain ⟨-, unslashedS, slashedC⟩ := Finset.mem_filter.mp inSlashed
  obtain ⟨u, foundS⟩ : ∃ u, split.validators.data[i]? = some u :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have cleanU : u.slashed = false := by simpa [foundS] using unslashedS
  obtain ⟨wc, foundC, lifeC⟩ := tailC.registryLifecycle.validators i u foundS
  have markedC : wc.slashed = true := by simpa [foundC] using slashedC
  by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
  · have assigned : wc.exitEpoch ≠ FAR_FUTURE_EPOCH :=
      run_slashed_exit_assigned ((toFin.append fromFin).append tailC) h.genesis
        h.caps.activation h.caps.compounding h.early (Internal.Setting.delay h) i wc foundC markedC
    obtain ⟨c, inRun, index, -⟩ :=
      tailC.departure_charge_of_assigned i u wc foundS foundC unset assigned
    exact ⟨c, inRun, index⟩
  exfalso
  obtain ⟨w, foundP, lifeP⟩ := tail.registryLifecycle.validators i u foundS
  have exitP : w.exitEpoch = u.exitEpoch := lifeP.exitEpoch unset
  have exitC : wc.exitEpoch = u.exitEpoch := lifeC.exitEpoch unset
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have belowS := getCurrentEpoch_succ_lt_farFuture h.twoSlots split
  have activated : u.activationEpoch.toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp ((toFin.append fromFin).exit_activated h.genesis i u foundS unset)
  have actAssigned : u.activationEpoch ≠ FAR_FUTURE_EPOCH := fun same => by
    rw [same] at activated
    omega
  have actC : wc.activationEpoch = u.activationEpoch := lifeC.activationEpoch actAssigned
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  cases slashedP : w.slashed
  · by_cases early : u.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1
    · -- R keeps the key unslashed and exits it by its next epoch, so `exitedSlashable` counts it
      apply notES
      have delayS := (toFin.append fromFin).withdrawable_eq_exit_delay h.genesis i u foundS cleanU
      have delayP := ((toFin.append fromFin).append tail).withdrawable_eq_exit_delay h.genesis i w
        foundP slashedP
      have unassigned : u.exitEpoch.toNat ≠ 2 ^ 64 - 1 := fun same =>
        unset (UInt64.toNat_inj.mp (by rw [same, far]))
      have positive := (Internal.Setting.delay h)
      have openS : (getCurrentEpoch split).toNat < u.withdrawableEpoch.toNat := by
        by_cases exited : u.exitEpoch ≤ getCurrentEpoch split
        · exact UInt64.lt_iff_toNat_lt.mp (tailC.newly_slashed_initial_exited_unwithdrawable
            h.caps.activation h.caps.compounding h.early i u wc foundS foundC cleanU markedC exited)
        · have later := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp exited)
          rcases delayS with ⟨same, -⟩ | same
          · exact absurd same unset
          · omega
      have wdP : w.withdrawableEpoch.toNat = u.withdrawableEpoch.toNat := by
        rcases delayS with ⟨same, -⟩ | eqS
        · exact absurd same unset
        rcases delayP with ⟨same, -⟩ | eqP
        · exact absurd (exitP ▸ same) unset
        rw [eqS, eqP, exitP]
      unfold PinTerms.exitedSlashable
      simp only [foundP, Option.map_some, Option.getD_some, slashedP, Option.any_some, exitP,
        decide_eq_true_eq, true_and]
      omega
    · -- its exit is after R's next epoch, so it is active at C
      apply inactive
      have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
      refine isActiveAt_eq_true_iff.mpr ⟨wc, foundC, ?_⟩
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rw [actC]
        exact UInt64.le_iff_toNat_le.mpr (by simp only at splitC; omega)
      · rw [exitC]
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  · -- R slashes the key after the split, so its withdrawal is a vector past the split
    exact notRB (Internal.slashedRB_of_newly_slashed h foundS foundP cleanU slashedP)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key absent or unslashed at the finalized state is bounded from there or its creation.

A key already in the split's registry needs its slashing withdrawal bound.

A later key gets that bound from the state that first holds it. -/
private theorem envelope_of_clean_fin (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (inside : v.toNat < pulled.validators.data.size)
    (cleanFin : ∀ u, fin.validators.data[v.toNat]? = some u → u.slashed = false)
    (slashedLateSplit : v.toNat < split.validators.data.size →
      ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
        anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) :
    ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  intro z inPath
  by_cases inFin : v.toNat < fin.validators.data.size
  · have splitSize : v.toNat < split.validators.data.size :=
      Nat.lt_of_lt_of_le inFin (registryGrows_of_chainSteps fromFin.chainSteps)
    exact Internal.envelope_of_voter h fromFin tail replayedF replayed v
      (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) (fromFin.append tail)
      (Run.nil_append (fromFin.append tail)) cleanFin (slashedLateSplit splitSize) inFin
      (Or.inl ⟨Internal.effective_fin_le_ebUp h v.toNat, Nat.le_refl _⟩) (fun w fw clean' =>
        Internal.late_of_withdrawable h fromFin tail v.toNat w fw clean' (late w fw)) z inPath
  · obtain ⟨c, toC, fromC, cutC, insideC, clean, before, floorStart, firstAfter⟩ :=
      created_first_state h (fromFin.append tail) (by omega) inside
    have slashedLate : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
        anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      by_cases inSplit : v.toNat < split.validators.data.size
      · exact slashedLateSplit inSplit
      · have after := firstAfter split fromFin tail rfl inSplit
        have finalizedNat := UInt64.le_iff_toNat_le.mp h.finalized
        exact Internal.slashed_withdrawable_of_clean h fromC v clean insideC
          (UInt64.le_iff_toNat_le.mpr (by omega))
    have envC := Internal.envelope_of_voter h fromFin tail replayedF replayed v toC fromC cutC clean
      slashedLate insideC (Or.inr floorStart) (fun w fw clean' =>
        Internal.late_of_withdrawable h fromFin tail v.toNat w fw clean' (late w fw))
    rw [← cutC] at inPath
    exact path_le_of_start toC fromC v.toNat _ before envC z inPath

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The replays of the branch from `fin` to the split and of R's run, read at R's epoch.

Both runs end by R's epoch, so the horizon of the replay does not change their events. -/
private theorem replays_at_pulled
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF) :
    fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF ∧
      tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events :=
  ⟨replay_at_pulled pulled fromFin high endEpoch (currentEpoch_le_of_chainSteps tail.chainSteps)
      replayedF,
    replay_at_pulled pulled tail high endEpoch (UInt64.le_refl _) replayed⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of the split's registry, unslashed there, induces a leak on R's run only with a debit.

Its envelope on R's run is `ebUp` with its debits and its penalty in whole increments.

The penalty is below an increment.

So a key without a sync debit stays within `ebUp`, and induces no leak. -/
private theorem induced_debited (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {i : ℕ} (inside : i < split.validators.data.size)
    (unslashed : (split.validators.data[i]?.map (·.slashed)).getD false = false)
    (positive : 0 < Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i) :
    0 < Internal.syncD eventsF i + Internal.syncD events i := by
  obtain ⟨replayedF', replayed'⟩ :=
    replays_at_pulled tail high endEpoch replayed fromFin replayedF
  by_contra none
  have zero : Internal.syncD eventsF i + Internal.syncD events i = 0 := by omega
  by_cases late : ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat
  swap
  · obtain ⟨w, found, notLate⟩ : ∃ w, pulled.validators.data[i]? = some w ∧
        w.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
      by_contra no
      exact late fun w found => by
        by_contra notLate
        exact no ⟨w, found, by omega⟩
    rw [Internal.inducedR_of_withdrawn _ _ _ (withdrawnRB_of_le config pulled anc fin found
      notLate)]
      at positive
    exact Nat.lt_irrefl 0 positive
  have below := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split)
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  have cleanSplit : ∀ u, split.validators.data[v.toNat]? = some u → u.slashed = false :=
    fun u foundU => by
      rw [foundU] at unslashed
      simpa using unslashed
  have envelope := envelope_of_clean_fin h fromFin tail replayedF' replayed' v
    (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tail.chainSteps))
    (fun u foundU => Internal.unslashed_of_run fromFin foundU cleanSplit)
    (fun splitSize => Internal.slashed_withdrawable_of_clean h tail v cleanSplit splitSize
      h.finalized) late
  have hWdb := slashW_add_downwardBand_le h v.toNat
  have bandLow := h.facts.bandLow
  have incBig := h.facts.incrementSize
  have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by omega
  have perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement := by
    have := Internal.four_le_perIncrement h
    omega
  have bound := Internal.inducedR_le config pulled anc fin h.bands.1 perPos (fromFin.append tail)
    v.toNat
    0 0 (Nat.zero_le _) fun z inPath => by
      have within := envelope z inPath
      rw [zero, Nat.zero_add, Nat.div_eq_of_lt hW] at within
      simpa using within
  simp at bound
  omega

/-- The deposits of `depPre` are among the deposits of the events. -/
private theorem depPre_le_deposits (L : List (BalanceEvent preset)) (i : ℕ) :
    Internal.depPre L i ≤ ((L.filter fun e => e.source = .deposits).map (Internal.keyCredit i)).sum
      := by
  induction L with
  | nil => simp [Internal.depPre]
  | cons e rest ih =>
    unfold Internal.depPre at ih ⊢
    by_cases dep : e.source = .deposits
    · by_cases slashed : slashedFlagAt e.before.state i = some true <;>
        simp [dep, slashed] at ih ⊢ <;> omega
    · simp [dep] at ih ⊢
      omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key credited by a consolidation from the split, or on the shared segment, has a due entry.

The entry is in the queue of the finalized state, so the key has its band. -/
private theorem band_of_consolidation (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    {ending : BeaconState preset fork}
    (run : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch ending).toNat ≤ high + 1)
    (near : (getCurrentEpoch ending).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)} (replayed : run.balanceEvents high = .ok events)
    {i : ℕ} (small : i < 2 ^ 64) (credited : 0 < Internal.consAmt eventsF i + Internal.consAmt
      events i) :
    preset.upwardBand ≤ Internal.bandX fin high i := by
  by_contra low
  have none : Internal.dueAt fin high {(UInt64.ofNat i : ValidatorIndex)} = 0 := by
    unfold Internal.bandX at low
    by_contra pos
    exact low (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero pos))
  have zero := Internal.consAmt_zero h fromFin replayedF run high endEpoch near replayed _ none
  rw [UInt64.toNat_ofNat_of_lt' small] at zero
  omega

/-- Ten quotients times three ceilings of a slack are zero, or within thirty slacks and quotients.
-/
private theorem ceil_round (X Q : ℕ) (pos : 0 < Q) :
    10 * Q * (3 * ((X + Q - 1) / Q)) = 0 ∨
      (0 < X ∧ 10 * Q * (3 * ((X + Q - 1) / Q)) ≤ 30 * X + 30 * Q - 30) := by
  rcases Nat.eq_zero_or_pos X with rfl | positive
  · left
    rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)]
    simp
  · right
    refine ⟨positive, ?_⟩
    have floor := Nat.div_mul_le_self (X + Q - 1) Q
    have e : 10 * Q * (3 * ((X + Q - 1) / Q)) = 30 * ((X + Q - 1) / Q * Q) := by ring
    rw [e]
    omega

/-- Thirty-three of an amount is within ten quotients of its share. -/
private theorem share_ge (pos : 0 < (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
    (x : ℕ) :
    33 * x ≤ 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat *
      Internal.wShare preset fork x := by
  unfold Internal.wShare
  generalize (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = Q at pos ⊢
  exact le_smul_ceilDiv (β := Nat) (show 0 < 10 * Q by omega)

/-- A key's credits on C's run have their gross scan and their credit or consolidation band. -/
private theorem credit_band_bounds (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {i : ℕ} (small : i < 2 ^ 64) :
    Internal.propN tailC highC i ≤ Internal.grossScan i highC tailC ∧
      Internal.whistC tailC highC i ≤ Internal.grossScan i highC tailC ∧
      (Internal.syncCr eventsC i = 0 ∨ 0 < Internal.grossScan i highC tailC) ∧
      ((0 < Internal.grossScan i highC tailC + (Internal.creditScan (fun _ => false)
          (fun s => decide (s = .deposits)) i highC tailC) ∧
          Internal.bandC tailC highC i = preset.upwardBand) ∨
        (Internal.grossScan i highC tailC + (Internal.creditScan (fun _ => false)
          (fun s => decide (s = .deposits)) i highC tailC) = 0 ∧ Internal.bandC tailC highC i = 0))
            ∧
      (Internal.consAmt eventsC i = 0 ∨ preset.upwardBand ≤ Internal.bandX fin highC i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Internal.scan_le_gross tailC highC i (fun s => decide (s = .rewards))
      fun s h => by simp at h; simp [h]
  · exact Internal.scan_le_gross tailC highC i (fun s => decide (s = .slashings))
      fun s h => by simp at h; simp [h]
  · rcases Nat.eq_zero_or_pos (Internal.syncCr eventsC i) with none | positive
    · exact .inl none
    · exact .inr (Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early tailC highC
      replayedC i
        positive)
  · unfold Internal.bandC
    split_ifs <;> omega
  · rcases Nat.eq_zero_or_pos (Internal.consAmt eventsC i) with none | positive
    · exact .inl none
    · exact .inr (band_of_consolidation h fromFin replayedF tailC highC endEpochC h.near replayedC
        small (by omega))

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The rounding of one key of `SC` is within its shares and bands, at ten quotients.

The slack's credits pay at eleven tenths of three, the shares' rate.

Each source of the key's slack brings a band, which pays the rounding of its floor. -/
private theorem sc_key_round (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (eventsP : List (BalanceEvent preset)) (Q : ℕ)
    (hQ : Q = (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) {i : ℕ}
    (member : i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size)) :
    10 * Q * (3 * ((Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append
      tail) highC
        high eventsC eventsF events fin i +
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          + Q - 1) / Q)) ≤
      33 * Internal.propN tailC highC i + 33 * Internal.depPre eventsC i + 33 * Internal.syncCr
        eventsC i +
        33 * Internal.consAmt eventsC i + 33 * Internal.syncD eventsF i + 33 * Internal.syncD events
          i +
        30 * (Q * Internal.whistC tailC highC i) + 10 * (Q * Internal.bandC tailC highC i) +
        10 * (Q * Internal.bandX fin highC i) +
        33 * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.syncCr eventsF i else 0) +
        33 * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.consAmt eventsF i else 0) +
        10 * (Q * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.bandX fin high i else 0)) +
        10 * (Q * (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events
          eventsF i +
          Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
          Internal.bandR (eventsF ++ events) i +
          if (pinTerms config pulled anc fin).exitBeforeFin i = true then
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0)) +
        33 * Internal.propN pre highC i + 10 * (Q * Internal.syncCr eventsP i) +
        30 * (Q * (if ∃ c ∈ tailC.departureCharges, c.index = i then Internal.whistC pre highC i
          else 0)) +
        10 * (Q * (if ∃ c ∈ tailC.departureCharges, c.index = i then
          (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
            i then
            preset.upwardBand else 0) else 0)) := by
  have quotient : 30 ≤ Q := hQ ▸ h.facts.whistleblower fork
  have up := h.bands.2
  have incBig := h.facts.incrementSize
  have unit : 4 ≤ (pinTerms config pulled anc fin).unitGain := by
    have finalized := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have depth : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    have unitEq : (pinTerms config pulled anc fin).unitGain =
        (pinTerms config pulled anc fin).depth * ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) := rfl
    have product := Nat.mul_le_mul (show 2 ≤ (pinTerms config pulled anc fin).depth by omega)
      (Nat.le_add_left 2 ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat))
    omega
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
  obtain ⟨-, unslashedS, -⟩ := Finset.mem_filter.mp inSlashed
  have small := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split)
  have replayedF' := replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called h)
    replayedF
  -- the credits that the slack reads, and the bands that they bring
  obtain ⟨grossP, grossW, grossS, hbC, consBand⟩ :=
    credit_band_bounds h fromFin replayedF' tailC highC endEpochC replayedC small
  obtain ⟨-, credits⟩ := Internal.creditScan_bounds ∅ UInt64.toNat (fun _ => false)
    (fun s => decide (s = .deposits)) highC (fun _ => 0) tailC replayedC (fun e _ _ => by simp)
  have dep := credits (fun s => decide (s = .deposits))
    (Or.inr fun electra early replayed i => Internal.block_deposit_zero electra early
      replayed i)
    (Or.inl fun _ covered => covered) electra h.early i
  have deposits := (depPre_le_deposits eventsC i).trans dep
  have bandXZero : ∀ hh, Internal.bandX fin hh i = 0 ∨ preset.upwardBand ≤ Internal.bandX fin hh i
    := by
    intro hh
    unfold Internal.bandX
    rcases Nat.eq_zero_or_pos (Internal.dueAt fin hh {(UInt64.ofNat i : ValidatorIndex)}) with zero
      | pos
    · exact .inl (by rw [zero, Nat.mul_zero])
    · exact .inr (Nat.le_mul_of_pos_right _ pos)
  have hbX : (Internal.bandX fin highC i = 0 ∧ Internal.consAmt eventsC i = 0) ∨
      preset.upwardBand ≤ Internal.bandX fin highC i := by
    rcases bandXZero highC with zero | big
    · rcases consBand with none | big
      · exact .inl ⟨zero, none⟩
      · exact .inr big
    · exact .inr big
  have hbXh : (Internal.bandX fin high i = 0 ∧ Internal.consAmt eventsF i = 0) ∨
      preset.upwardBand ≤ Internal.bandX fin high i := by
    rcases bandXZero high with zero | big
    · rcases Nat.eq_zero_or_pos (Internal.consAmt eventsF i) with none | pos
      · exact .inl ⟨zero, none⟩
      · exact .inr (band_of_consolidation h fromFin replayedF' tail high endEpoch (by omega)
          replayed small (by omega))
    · exact .inr big
  have hbR : (Internal.syncD eventsF i + Internal.syncD events i = 0 ∧ Internal.bandR (eventsF ++
    events) i = 0 ∧
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i = 0) ∨
      Internal.bandR (eventsF ++ events) i =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 := by
    have induced : Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i = 0 ∨
        0 < Internal.syncD eventsF i + Internal.syncD events i := by
      rcases Nat.eq_zero_or_pos
          (Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i) with zero |
            pos
      · exact .inl zero
      · exact .inr (induced_debited h tail high endEpoch replayed fromFin replayedF inside
          unslashedS pos)
    rw [Internal.bandR_eq]
    simp only [List.map_append, List.sum_append]
    unfold Internal.syncD at induced ⊢
    split_ifs <;> omega
  have huK : (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i =
    0 ∧
        (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
          (pinTerms config pulled anc fin).unitGain else 0) = 0) ∨
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i =
        (pinTerms config pulled anc fin).unitGain := by
    unfold Internal.unitK Internal.flowCredit
    split_ifs <;> omega
  have hSW : (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0) ≤
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i := by
    unfold Internal.unitK Internal.flowCredit
    split_ifs <;> omega
  have huSF : (Internal.syncCr eventsF i = 0 ∧
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) = 0) ∨
      (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) = preset.upwardBand := by
    split_ifs <;> omega
  have hb5 : (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i =
    0 ∧
        (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
          then
          preset.upwardBand else 0) = 0) ∨
      (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
        then
        preset.upwardBand else 0) = preset.upwardBand := by
    split_ifs <;> omega
  -- the terms of a key that exited by the finalized state
  have hE : ((if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.syncCr eventsF i else 0) = Internal.syncCr eventsF i ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.consAmt eventsF i else 0) = Internal.consAmt eventsF i ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.bandX fin high i else 0) = Internal.bandX fin high i ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) =
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
            fin high i +
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) =
          (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
            fin high i +
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0)) ∨
      ((if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.syncCr eventsF i else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.consAmt eventsF i else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.bandX fin high i else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
            fin high i +
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) = 0) := by
    by_cases e : (pinTerms config pulled anc fin).exitBeforeFin i = true
    · left
      simp only [e, ↓reduceIte, and_self]
    · right
      simp only [e, Bool.false_eq_true, ↓reduceIte, and_self]
  -- the terms of a key not active at C that R neither slashes nor exits, which is charged
  have hD : ((if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          =
          Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i ∧
        (if ∃ c ∈ tailC.departureCharges, c.index = i then Internal.whistC pre highC i else 0) =
          Internal.whistC pre highC i ∧
        (if ∃ c ∈ tailC.departureCharges, c.index = i then
          (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
            i then
            preset.upwardBand else 0) else 0) =
          (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
            i then
            preset.upwardBand else 0)) ∨
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          = 0 := by
    by_cases d : ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true ∧
        ¬ isActiveAt counted (getCurrentEpoch counted) i = true
    · have charged := sc_inactive_charged h fromFin tail tailC member d.1 d.2.1 d.2.2
      exact .inl ⟨ite_eq_left d, ite_eq_left charged, ite_eq_left charged⟩
    · exact .inr (ite_eq_right d)
  -- the products by the quotient
  have pWT := Nat.mul_le_mul_right (Internal.whistC tailC highC i) (show 2 ≤ Q by omega)
  have pSP := Nat.mul_le_mul_right (Internal.syncCr eventsP i) (show 3 ≤ Q by omega)
  have pWP := Nat.mul_le_mul_right
    (if ∃ c ∈ tailC.departureCharges, c.index = i then Internal.whistC pre highC i else 0)
    (show 3 ≤ Q by omega)
  obtain ⟨SB, hSB⟩ : ∃ SB, SB = Internal.bandC tailC highC i + Internal.bandX fin highC i +
      (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
        Internal.bandR (eventsF ++ events) i +
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      (if (pinTerms config pulled anc fin).exitBeforeFin i = true then Internal.bandX fin high i
        else 0) +
      (if ∃ c ∈ tailC.departureCharges, c.index = i then
        (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
          then
          preset.upwardBand else 0) else 0) := ⟨_, rfl⟩
  have hQSB : Q * Internal.bandC tailC highC i + Q * Internal.bandX fin highC i +
      Q * (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
        Internal.bandR (eventsF ++ events) i +
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      Q * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        Internal.bandX fin high i else 0) +
      Q * (if ∃ c ∈ tailC.departureCharges, c.index = i then
        (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
          then
          preset.upwardBand else 0) else 0) = Q * SB := by
    rw [hSB]
    ring
  have pSB := Nat.mul_le_mul_right SB quotient
  -- the slack is zero, or it has a band of at least four
  have hc := ceil_round (Internal.whistleSlack (pinTerms config pulled anc fin) tailC
    (fromFin.append tail)
    highC high eventsC eventsF events fin i +
    (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true ∧
        ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
      Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0))
        Q (by omega)
  unfold Internal.whistleSlack Internal.whistleSlackBase at hc ⊢
  have big : (11 * (Internal.propN tailC highC i + Internal.depPre eventsC i + Internal.whistC tailC
    highC i +
        Internal.syncCr eventsC i + Internal.consAmt eventsC i + Internal.syncD eventsF i +
          Internal.syncD events i) + 9) / 10 +
      Internal.bandC tailC highC i + Internal.bandX fin highC i + Internal.bandR (eventsF ++ events)
        i +
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0) +
      (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
          fin high i +
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          = 0 ∨ 4 ≤ SB := by
    omega
  rcases big with zero | four
  · omega
  · have pFour := Nat.mul_le_mul_left Q four
    omega

/-- The slack and the rounding of the rewards of the keys of `SC` are paid by their shares.

A key of the split's registry is read at its bound and the slack that `registry` adds.

A key that exits on C's branch is read at its charge and its rise after it.

The slashing credits of the slack are the keys' own.

The left side of `bud_whistle_of` gives them up.

The unit, the induced leak and the bands of the slack are paid unscaled.

Its credits are paid by the shares, with a tenth for their gains.

Each credited key has an upward band, which pays the rounding of its floor. -/
private theorem whistle_slack_sc (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork}
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩) (eventsP : List (BalanceEvent preset)) :
    3 * (∑ i ∈ ((slashedOnC split counted).filter (fun i => i < split.validators.data.size)),
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      3 * (∑ i ∈ ((slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter
          (fun i => (pinTerms config pulled anc fin).slashedRB i = true),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        ∑ i ∈ ((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
          (fun i => PinTerms.exitedSlashable anc pulled i = true),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        ∑ i ∈ ((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
            (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
              ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
            (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).filter
            (fun i => ¬ ((pinTerms config pulled anc fin).tight = false ∧
              ((pinTerms config pulled anc fin).lateB i = true ∨
                (pinTerms config pulled anc fin).pendingRB i = true))),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        ∑ i ∈ ((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
            (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
              ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
            (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).filter
            (fun i => (pinTerms config pulled anc fin).tight = false ∧
              ((pinTerms config pulled anc fin).lateB i = true ∨
                (pinTerms config pulled anc fin).pendingRB i = true)),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        3 * (∑ i ∈ (((slashedOnC split counted).filter
            (fun i => i < split.validators.data.size)).filter
            (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
              ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
            (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true),
          (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        3 * (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
          Internal.whistC tailC highC i) +
        (Internal.wShare preset fork ((∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC
          highC v.toNat) +
            ∑ v ∈ Internal.SC pulled counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr
            eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt
            eventsC v.toNat) +
          Internal.wShare preset fork
            (∑ v ∈ Internal.SC pulled counted split, (Internal.syncD eventsF v.toNat +
              Internal.syncD events v.toNat)) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandX fin highC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.syncCr eventsF
              v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              Internal.consAmt eventsF v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              Internal.bandX fin high v.toNat) : ℕ) +
        (∑ v ∈ Internal.SC pulled counted split,
          (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat +
            if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
              (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) : ℕ) +
        Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre
          highC v.toNat) +
        (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsP v.toNat) +
        3 * (∑ v ∈ Internal.scCharged pulled counted split tailC, Internal.whistC pre highC v.toNat)
          +
        (∑ v ∈ Internal.scCharged pulled counted split tailC,
          if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
            Internal.syncCr eventsP v.toNat then
            preset.upwardBand else 0) := by
  have quotient := h.facts.whistleblower fork
  have pos : 0 < (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by omega
  -- each key is read at its group's bound, with the ceiling of its slack
  obtain ⟨base, hbase⟩ : ∃ base : ℕ → ℕ, ∀ i, base i =
      if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
      else Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℕ, ∀ i, X i =
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC
        eventsF events fin i +
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          := ⟨_, fun _ => rfl⟩
  have floorKey : ∀ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      3 * (min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      3 * base i + 3 * ((X i + (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
    intro i member
    rw [hbase, hX]
    by_cases hD : ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true ∧
        ¬ isActiveAt counted (getCurrentEpoch counted) i = true
    · -- the key is charged, and read at its charge
      obtain ⟨c, inRun, index⟩ := sc_inactive_charged h fromFin tail tailC member hD.1 hD.2.1 hD.2.2
      have any : (tailC.departureCharges.any fun c => c.index == i) = true :=
        List.any_eq_true.mpr ⟨c, inRun, by simp [index]⟩
      have read : whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i ≤
          (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) +
            (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail)
              highC high
              eventsC eventsF events fin i +
              (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
                i)) := by
        unfold whistleRead
        rw [ite_eq_left ⟨hD.2.2, any⟩]
        exact (min_le_right _ _).trans (by omega)
      rw [ite_eq_left hD, ite_eq_left hD]
      have down := Nat.div_le_div_right
        (c := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
        ((min_le_left _ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat).trans read)
      have split := floor_add_ceil_le (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i)
        (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
          high
          eventsC eventsF events fin i +
          (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i)) _
            pos
      omega
    · -- the key is read at its bound and its slack
      have read : whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i ≤
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i := by
        unfold whistleRead
        split
        · exact min_le_left _ _
        · exact le_rfl
      rw [ite_eq_right hD, ite_eq_right hD, Nat.add_zero]
      have down := Nat.div_le_div_right
        (c := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
        ((min_le_left _ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat).trans read)
      have split := floor_add_ceil_le (Internal.whistleEnv (pinTerms config pulled anc fin) pulled
        anc fin i)
        (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
          high
          eventsC eventsF events fin i) _ pos
      omega
  have floors := Finset.sum_le_sum floorKey
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at floors
  -- the bounds of the keys are the sums of the groups
  have apart : ∀ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      (pinTerms config pulled anc fin).slashedRB i = true →
        ¬ PinTerms.exitedSlashable anc pulled i = true := by
    intro i _ rb es
    rw [Internal.slashedRB_eq] at rb
    unfold PinTerms.exitedSlashable at es
    cases f : pulled.validators.data[i]? with
    | none => simp [f] at rb
    | some w => simp [f] at rb es; simp [rb.1] at es
  have splitThree : ∀ (S : Finset ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q],
      (∀ i ∈ S, p i → ¬ q i) → ∀ f : ℕ → ℕ, ∑ i ∈ S, f i = ∑ i ∈ S.filter p, f i +
        ∑ i ∈ S.filter q, f i + ∑ i ∈ S.filter (fun i => ¬ p i ∧ ¬ q i), f i := by
    intro S p q _ _ disjoint f
    rw [← Finset.sum_filter_add_sum_filter_not S p, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => ¬ p i)) q, Finset.filter_filter,
      Finset.filter_filter]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, -, hq⟩
      exact ⟨hi, hq⟩
    · rintro ⟨hi, hq⟩
      exact ⟨hi, fun hp => disjoint i hi hp hq, hq⟩
  have three := splitThree
    ((slashedOnC split counted).filter (fun i => i < split.validators.data.size))
    (fun i => (pinTerms config pulled anc fin).slashedRB i = true)
    (fun i => PinTerms.exitedSlashable anc pulled i = true) apart base
  have g1 : ∑ i ∈ ((slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => (pinTerms config pulled anc fin).slashedRB i = true), base i =
      ∑ i ∈ ((slashedOnC split counted).filter
        (fun i => i < split.validators.data.size)).filter
          (fun i => (pinTerms config pulled anc fin).slashedRB i = true),
        Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun i m => by
      rw [hbase, ite_eq_right fun hD => hD.1 (Finset.mem_filter.mp m).2]
  have g2 : ∑ i ∈ ((slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => PinTerms.exitedSlashable anc pulled i = true), base i =
      ∑ i ∈ ((slashedOnC split counted).filter
        (fun i => i < split.validators.data.size)).filter
          (fun i => PinTerms.exitedSlashable anc pulled i = true),
        Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun i m => by
      rw [hbase, ite_eq_right fun hD => hD.2.1 (Finset.mem_filter.mp m).2]
  have y := (Finset.sum_filter_add_sum_filter_not (((slashedOnC split counted).filter
    (fun i => i < split.validators.data.size)).filter
      (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true) base).symm
  have g3 := Finset.sum_congr rfl fun i (m : i ∈ (((slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
      (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)) => show base i =
        Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat by
      rw [hbase, ite_eq_right fun hD => hD.2.2 (Finset.mem_filter.mp m).2]
  have g4 := Finset.sum_congr rfl fun i (m : i ∈ (((slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
      (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true)) => show base i =
        (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat by
      obtain ⟨inY, inactive⟩ := Finset.mem_filter.mp m
      obtain ⟨-, both⟩ := Finset.mem_filter.mp inY
      rw [hbase, ite_eq_left ⟨both.1, both.2, inactive⟩]
  have g5 := (Finset.sum_filter_add_sum_filter_not ((((slashedOnC split counted).filter
    (fun i => i < split.validators.data.size)).filter
      (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
      (fun i => isActiveAt counted (getCurrentEpoch counted) i = true))
    (fun i => (pinTerms config pulled anc fin).tight = false ∧
      ((pinTerms config pulled anc fin).lateB i = true ∨
        (pinTerms config pulled anc fin).pendingRB i = true))
    (fun i => Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)).symm
  have part := congrArg
    (fun x => 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat * (3 * x))
    ((three.trans (by rw [g1, g2, y, g3, g4, g5])) : _ = _)
  -- the rounding of the keys is within the shares and bands
  have rounds := Finset.sum_le_sum fun i (m : i ∈ (slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)) => by
    have one := sc_key_round h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
      replayedC pre eventsP _ rfl m
    rw [← hX i] at one
    exact one
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at rounds
  -- the sums over `SC` are sums over the positions
  have fEBF (f : ℕ → ℕ) : ∑ v ∈ Internal.SC pulled counted split with
      (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, f v.toNat =
      ∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then f i else 0 :=
    (sum_SC_filter_positions h (fun i => (pinTerms config pulled anc fin).exitBeforeFin i = true)
      f).trans (Finset.sum_filter _ _)
  have fCharged (f : ℕ → ℕ) : ∑ v ∈ Internal.scCharged pulled counted split tailC, f v.toNat =
      ∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        if ∃ c ∈ tailC.departureCharges, c.index = i then f i else 0 :=
    (sum_SC_filter_positions h (fun i => ∃ c ∈ tailC.departureCharges, c.index = i) f).trans
      (Finset.sum_filter _ _)
  rw [fEBF (fun i => Internal.syncCr eventsF i), fEBF (fun i => Internal.consAmt eventsF i),
    fEBF (fun i => Internal.bandX fin high i), fCharged (fun i => Internal.whistC pre highC i),
    fCharged (fun i => if 0 < Internal.propN pre highC i + Internal.whistC pre highC i +
      Internal.syncCr eventsP i then
      preset.upwardBand else 0),
    sum_SC_positions h (fun i => Internal.propN tailC highC i),
    sum_SC_positions h (fun i => Internal.depPre eventsC i),
    sum_SC_positions h (fun i => Internal.syncCr eventsC i), sum_SC_positions h (fun i =>
      Internal.consAmt eventsC i),
    sum_SC_positions h (fun i => Internal.syncD eventsF i + Internal.syncD events i),
    sum_SC_positions h (fun i => Internal.bandC tailC highC i),
    sum_SC_positions h (fun i => Internal.bandX fin highC i),
    sum_SC_positions h (fun i => Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC
      events
      eventsF i + Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      Internal.bandR (eventsF ++ events) i + if (pinTerms config pulled anc fin).exitBeforeFin i =
        true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0),
    sum_SC_positions h (fun i => Internal.propN pre highC i), sum_SC_positions h (fun i =>
      Internal.syncCr eventsP i)]
  simp only [Finset.sum_add_distrib]
  refine Nat.le_of_mul_le_mul_left
    (c := 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ?_ (by omega)
  have scaled := Nat.mul_le_mul_left
    (10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) floors
  have s1 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.propN tailC highC i +
    ∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.depPre eventsC i)
  have s2 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.syncCr eventsC i)
  have s3 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.consAmt eventsC i)
  have s4 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.syncD eventsF i +
    ∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.syncD events i)
  have s5 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then Internal.syncCr eventsF i else
        0)
  have s6 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then Internal.consAmt eventsF i
        else 0)
  have s7 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.propN pre highC i)
  linarith

/-- The largest representable epoch is reserved for keys without an assigned exit. -/
private theorem exitEpoch_toNat_lt_of_ne_far {epoch : Epoch} (assigned : epoch ≠ FAR_FUTURE_EPOCH) :
    epoch.toNat < 2 ^ 64 - 1 := by
  have bound := epoch.toNat_lt
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have ne := mt UInt64.toNat_inj.mp assigned
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C's run creates and slashes is credited its proposer credits and consolidations.

It is also credited its deposits before its exit.

The run charges the key at the step that sets its exit, and its deposits stop there.

The key is unslashed before that step, since a slashed key has its exit set.

The consolidation credits that the run scans are among those of its events. -/
private theorem created_credC_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {i : ℕ} (created : ¬ i < split.validators.data.size)
    (slashedC : (counted.validators.data[i]?.map (·.slashed)).getD false = true) :
    Internal.credC tailC highC i ≤ Internal.propN tailC highC i + Internal.depPre eventsC i +
      Internal.consAmt eventsC i := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨wc, foundC⟩ : ∃ wc, counted.validators.data[i]? = some wc := by
    cases f : counted.validators.data[i]? with
    | none => simp [f] at slashedC
    | some w => exact ⟨w, rfl⟩
  have markedC : wc.slashed = true := by simpa [foundC] using slashedC
  have assignedC := run_slashed_exit_assigned ((shared.append fromFin).append tailC) h.genesis
    h.caps.activation h.caps.compounding h.early (Internal.Setting.delay h) i wc foundC markedC
  obtain ⟨c, inRun, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early i
    (fun v found => absurd (Array.getElem?_eq_some_iff.mp found).1 created) wc foundC assignedC
  have late := DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c inRun
  simp only at late
  obtain ⟨a, b, pre, step, post, site, u, w, foundA, foundB, unset, set, -, epochW⟩ :=
    tailC.departure_charge_site c inRun
  rw [index] at foundA foundB
  subst site
  have aFork : a.fork = fork :=
    Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  have aEarly : a.fork < .glamsterdam := by rw [aFork]; exact h.early
  have aFulu : .fusaka ≤ a.fork := by rw [aFork]; exact h.fulu
  have aEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      ((Run.nil.snoc step).append post).chainSteps)) endEpochC
  -- the key is unslashed at the step that sets its exit
  have cleanA : u.slashed = false := by
    cases s : u.slashed
    · rfl
    · exact absurd unset (run_slashed_exit_assigned ((shared.append fromFin).append pre)
        h.genesis h.caps.activation h.caps.compounding aEarly (Internal.Setting.delay h) i u foundA
          s)
  -- the events of C's run are those before the step and those from it
  obtain ⟨e1, replayed1⟩ := pre.balanceEvents_ok aEarly highC
  obtain ⟨eS, replayedS⟩ := ((Run.nil.snoc step).append post).balanceEvents_ok h.early highC
  have whole := balanceEvents_append pre ((Run.nil.snoc step).append post) highC replayed1
    replayedS
  rw [← pre.snoc_append_eq step post, replayedC] at whole
  obtain rfl := Except.ok.inj whole
  have insideC := (Array.getElem?_eq_some_iff.mp foundC).1
  have below := insideC.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  have insideA := (Array.getElem?_eq_some_iff.mp foundA).1
  -- from the step on, the key is exited and not withdrawable through C
  have exited := exitEpoch_toNat_lt_of_ne_far set
  have held : (getCurrentEpoch counted).toNat < w.withdrawableEpoch.toNat := by
    have delay := (((shared.append fromFin).append pre).snoc step).exit_withdrawable_delay
      h.genesis v.toNat w foundB set
    have shallow := h.shallow
    have near := h.near
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    simp only at finSplit
    omega
  have zeroS := Internal.Run.charge_deposit_credit_zero (shared.append (fromFin.append pre))
    h.genesis step post aFulu h.early highC aEpoch replayedS v.toNat insideA w foundB exited held
  have cleanPre := prefix_deposits_clean h pre aEarly highC replayed1 v (by simp [foundA, cleanA])
  have depFirst := deposits_le_depPre e1 v.toNat cleanPre
  have scanPre := Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits))
    (· = .deposits) (by intro s; simp) pre highC v replayed1
  have scanRest := Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits))
    (· = .deposits) (by intro s; simp) ((Run.nil.snoc step).append post) highC v replayedS
  have consAll := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp)
    ((pre.snoc step).append post) highC v replayedC
  have depSplit := Internal.creditScan_append (fun _ => false) (fun s => decide (s = .deposits))
    v.toNat
    highC pre ((Run.nil.snoc step).append post)
  rw [← pre.snoc_append_eq step post] at depSplit
  have depMono : Internal.depPre e1 v.toNat ≤ Internal.depPre (e1 ++ eS) v.toNat := by
    unfold Internal.depPre
    simp only [List.filter_append, List.map_append, List.sum_append]
    omega
  beta_reduce at scanPre scanRest consAll
  rw [Internal.credC_split, Internal.credN_split]
  unfold Internal.consAmt
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The reward of one key of `CS` is within its charge, its shares and its bands, at ten quotients.

A key active at C is read at `createdCeil`, and one that has exited at its charge and credits.

The credits of a slashed created key are its proposer credits, deposits and consolidations. -/
private theorem cs_key_round (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (Q : ℕ) (hQ : Q = (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) {i : ℕ}
    (member : i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)) :
    10 * Q * (if isActiveAt counted (getCurrentEpoch counted) i = true then
        3 * (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q)
      else 3 * (min (Internal.chargeAmt tailC i + whistleExtra (pinTerms config pulled anc fin)
        tailC highC
          eventsC i) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q)) ≤
      10 * Q * (if isActiveAt counted (getCurrentEpoch counted) i = true then 0
        else 3 * ((Internal.chargeAmt tailC i + preset.upwardBand + (pinTerms config pulled anc
          fin).depth *
          (pinTerms config pulled anc fin).gainRateMax) / Q)) +
        33 * Internal.propN tailC highC i + 33 * Internal.depPre eventsC i + 33 * Internal.syncCr
          eventsC i +
        33 * Internal.consAmt eventsC i + 30 * (Q * Internal.whistC tailC highC i) +
        10 * (Q * Internal.bandC tailC highC i) + 10 * (Q * Internal.bandX fin highC i) +
        10 * (Q * (if isActiveAt counted (getCurrentEpoch counted) i = true then
          (if (pinTerms config pulled anc fin).gainHigh = true then
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
          else (pinTerms config pulled anc fin).unitGain) else 0)) := by
  obtain ⟨fromFin⟩ := h.fromFin
  have quotient : 30 ≤ Q := hQ ▸ h.facts.whistleblower fork
  have pos : 0 < Q := by omega
  have up := h.bands.2
  have incBig := h.facts.incrementSize
  have below := (Internal.PinPresetFacts.below h.facts)
  obtain ⟨inSlashed, created⟩ := Finset.mem_filter.mp member
  obtain ⟨-, -, slashedC⟩ := Finset.mem_filter.mp inSlashed
  have insideC : i < counted.validators.data.size := by
    cases f : counted.validators.data[i]? with
    | none => simp [f] at slashedC
    | some w => exact (Array.getElem?_eq_some_iff.mp f).1
  have small := insideC.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  obtain ⟨eventsF, replayedF⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  -- the credits of the key and their bands
  have cred := created_credC_le h tailC highC endEpochC replayedC created slashedC
  obtain ⟨grossP, grossW, grossS, hbC, hbX⟩ :=
    credit_band_bounds h fromFin replayedF tailC highC endEpochC replayedC small
  have splitC := Internal.credC_split tailC highC i
  have splitN := Internal.credN_split tailC highC i
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' small⟩
  have consScan := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp) tailC highC v
    replayedC
  beta_reduce at consScan
  have consEq : Internal.consAmt eventsC v.toNat =
      ((eventsC.filter fun e => e.source = .consolidations).map (Internal.keyCredit v.toNat)).sum :=
        rfl
  have pWT := Nat.mul_le_mul_right (Internal.whistC tailC highC v.toNat) (show 2 ≤ Q by omega)
  have pC := Nat.mul_le_mul_right (Internal.bandC tailC highC v.toNat) quotient
  have pX := Nat.mul_le_mul_right (Internal.bandX fin highC v.toNat) quotient
  by_cases active : isActiveAt counted (getCurrentEpoch counted) v.toNat = true
  · rw [ite_eq_left active, ite_eq_left active, ite_eq_left active]
    -- a key active at C has the band of its creation
    obtain ⟨wv, foundV, activeV⟩ := isActiveAt_eq_true_iff.mp active
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at activeV
    have finiteC := getCurrentEpoch_succ_lt_farFuture h.twoSlots counted
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
        w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted :=
      ⟨wv, foundV, fun far => by
        have := UInt64.le_iff_toNat_le.mp activeV.1
        rw [far] at this
        omega, activeV.1⟩
    have band := created_band h fromFin (getCurrentEpoch pulled).toNat (by omega) replayedF tailC
      highC endEpochC replayedC activated (by omega)
    have floorMin := Nat.div_mul_le_self
      (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC v.toNat)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) Q
    have minLe := min_le_left (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC
      v.toNat) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    have minMax := min_le_right (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC
      v.toNat) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    have e : 10 * Q * (3 * (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC
        v.toNat) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q)) =
        30 * (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC v.toNat)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q * Q) := by ring
    rw [e]
    by_cases high : (pinTerms config pulled anc fin).gainHigh = true
    · rw [ite_eq_left high]
      have pM := Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        (show 3 ≤ Q by omega)
      omega
    · rw [ite_eq_right high]
      have lowGain : (pinTerms config pulled anc fin).gainHigh = false := by simpa using high
      -- off the high rate, the gains of the credits are within a tenth of them
      have wide := wide_of_lowGain h lowGain
      have tenth := Internal.gain_tenth preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        WEIGHT_DENOMINATOR.toNat
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum (pinTerms config pulled anc fin).perIncrement
        (pinTerms config pulled anc fin).depth (Internal.credC tailC highC v.toNat +
          Internal.whistC tailC highC v.toNat + Internal.syncCr eventsC v.toNat) wide
      rw [Nat.mul_assoc (11 * (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC
        v.toNat +
          Internal.syncCr eventsC v.toNat) /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))] at tenth
      have ceilEq : createdCeil (pinTerms config pulled anc fin) tailC highC eventsC v.toNat =
          Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
            eventsC v.toNat +
            (pinTerms config pulled anc fin).depth *
              (11 * (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
                  Internal.syncCr eventsC v.toNat) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
                    *
                ((pinTerms config pulled anc fin).perIncrement *
                  (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) / WEIGHT_DENOMINATOR.toNat) +
            (pinTerms config pulled anc fin).depth *
              ((pinTerms config pulled anc fin).perIncrement *
                (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) +
            preset.downwardBand := by
        unfold createdCeil
        simp only [lowGain, Bool.false_eq_true, ↓reduceIte]
      have unitEq : (pinTerms config pulled anc fin).unitGain =
          (pinTerms config pulled anc fin).depth *
            ((pinTerms config pulled anc fin).perIncrement *
              (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) := rfl
      have pU := Nat.mul_le_mul_right (pinTerms config pulled anc fin).unitGain
        (show 3 ≤ Q by omega)
      omega
  · rw [ite_eq_right active, ite_eq_right active, ite_eq_right active]
    -- a key that has exited is read at its charge and its credits
    have extra : Internal.chargeAmt tailC v.toNat + whistleExtra (pinTerms config pulled anc fin)
      tailC
        highC eventsC v.toNat = (Internal.chargeAmt tailC v.toNat + preset.upwardBand +
          (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) +
        (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
          eventsC v.toNat) := by
      unfold whistleExtra
      omega
    have mn := Nat.div_le_div_right (c := Q)
      ((min_le_left _ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat).trans (le_of_eq extra))
    have fl := floor_add_ceil_le (Internal.chargeAmt tailC v.toNat + preset.upwardBand +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax)
      (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
        eventsC v.toNat) Q pos
    have mul := Nat.mul_le_mul_left (10 * Q) (Nat.mul_le_mul_left 3 (mn.trans fl))
    have dist : 10 * Q * (3 * ((Internal.chargeAmt tailC v.toNat + preset.upwardBand +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) / Q +
        (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
          eventsC v.toNat + Q - 1) /
          Q)) =
        10 * Q * (3 * ((Internal.chargeAmt tailC v.toNat + preset.upwardBand +
          (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) /
            Q)) +
        10 * Q * (3 * ((Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
          Internal.syncCr eventsC v.toNat + Q - 1) / Q)) := by ring
    have hc := ceil_round (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat
      +
      Internal.syncCr eventsC v.toNat) Q pos
    -- credits bring a band of at least four
    have big : Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
      Internal.syncCr eventsC v.toNat = 0 ∨
        preset.upwardBand ≤ Internal.bandC tailC highC v.toNat + Internal.bandX fin highC v.toNat :=
          by
      omega
    rcases big with zero | four
    · omega
    · have pB := Nat.mul_le_mul_left Q four
      have pUp := Nat.mul_le_mul_left Q (show 4 ≤ preset.upwardBand by omega)
      rw [Nat.mul_add] at pB
      omega

/-- The slack and the rounding of the rewards of the keys of `CS` are paid by their shares.

A created key that has exited is read at its charge and its credits.

A created key active at C is read at `createdCeil`.

Its credits are paid by the shares, with a tenth for their gains.

Its unit, or its largest cap at a high rate, is paid for each active key.

Each credited key has an upward band, which pays the rounding of its floor.

The credits of a slashed created key are its proposer credits.

They are also its deposits before the slashing and its consolidations. -/
private theorem whistle_slack_cs (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * (∑ i ∈ (((slashedOnC split counted).filter (fun i => ¬ i <
        split.validators.data.size)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i
        = true)), min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      3 * (∑ i ∈ (((slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter (fun i => ¬ isActiveAt counted (getCurrentEpoch
          counted) i = true)), min (Internal.chargeAmt tailC i + whistleExtra (pinTerms config
            pulled anc
          fin) tailC highC eventsC i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      3 * (∑ i ∈ (((slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter (fun i => ¬ isActiveAt counted (getCurrentEpoch
          counted) i = true)), (Internal.chargeAmt tailC i + preset.upwardBand + (pinTerms config
            pulled anc
          fin).depth * (pinTerms config pulled anc fin).gainRateMax) / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        3 * (∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)),
            Internal.whistC tailC highC i) +
        (Internal.wShare preset fork ((∑ v ∈ Internal.CS counted split, Internal.propN tailC highC
          v.toNat) +
            ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.syncCr eventsC
            v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC
            v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandX fin highC v.toNat) : ℕ) +
        ((Internal.CS counted split).filter fun v => isActiveAt counted (getCurrentEpoch counted)
          v.toNat =
          true).card * (if (pinTerms config pulled anc fin).gainHigh = true then
              preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
            else (pinTerms config pulled anc fin).unitGain) := by
  have quotient := h.facts.whistleblower fork
  have pos : 0 < (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by omega
  -- each key of `CS` is within its charge, its shares and its bands
  have rounds := Finset.sum_le_sum fun i (m : i ∈ (slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)) =>
    cs_key_round h tailC highC endEpochC replayedC _ rfl m
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at rounds
  -- the two groups of the created keys are the keys active at C and the others
  have active (f g : ℕ → ℕ) : ∑ i ∈ (slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size),
        (if isActiveAt counted (getCurrentEpoch counted) i = true then f i else g i) =
      ∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => isActiveAt counted (getCurrentEpoch counted) i = true), f i +
      ∑ i ∈ ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true), g i :=
    Finset.sum_ite _ _
  simp only [active, Finset.sum_const_zero, Nat.zero_add, Nat.add_zero] at rounds
  simp only [← Finset.mul_sum] at rounds
  -- the units of the keys active at C are those of the active keys of `CS`
  have cap := sum_CS_positions h (fun i => if isActiveAt counted (getCurrentEpoch counted) i = true
    then 1 else 0)
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, Nat.mul_one, Nat.mul_one] at cap
  have units : ∑ i ∈ ((slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => isActiveAt counted (getCurrentEpoch counted) i = true),
        (if (pinTerms config pulled anc fin).gainHigh = true then
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        else (pinTerms config pulled anc fin).unitGain) =
      ((Internal.CS counted split).filter fun v => isActiveAt counted (getCurrentEpoch counted)
        v.toNat =
        true).card * (if (pinTerms config pulled anc fin).gainHigh = true then
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        else (pinTerms config pulled anc fin).unitGain) := by
    rw [Finset.sum_const, smul_eq_mul, cap]
  rw [units] at rounds
  rw [sum_CS_positions h (fun i => Internal.propN tailC highC i), sum_CS_positions h (fun i =>
      Internal.depPre eventsC i), sum_CS_positions h (fun i => Internal.syncCr eventsC i),
    sum_CS_positions h (fun i => Internal.consAmt eventsC i), sum_CS_positions h (fun i =>
      Internal.bandC tailC highC i), sum_CS_positions h (fun i => Internal.bandX fin highC i)]
  refine Nat.le_of_mul_le_mul_left (c := 10 *
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ?_ (by omega)
  have s1 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.propN tailC highC i +
    ∑ i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.depPre eventsC i)
  have s2 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.syncCr eventsC i)
  have s3 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.consAmt eventsC i)
  linarith

/-- A charge on C's run of a key not active at C is due by C's epoch.

It is also due after the split's epoch and the seed lookahead, as every charge of the run is.

The key is activated at the step that starts its exit, so it is inactive at C only by its exit.

That step is a seed lookahead before the charge's epoch, so the activation is by R's epoch. -/
private theorem charge_due (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {i : ℕ}
    (inactive : ¬ isActiveAt counted (getCurrentEpoch counted) i = true)
    {c : DepartureCharge} (member : c ∈ tailC.departureCharges) (index : c.index = i) :
    (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch ∧
      c.epoch ≤ (getCurrentEpoch counted).toNat ∧
      ∀ wC, counted.validators.data[i]? = some wC →
        wC.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨stop, chosen⟩ := Internal.stop_of_charge fromFin tailC member index
  have selected := stop.selected
  rw [chosen] at selected
  obtain ⟨-, -, -, next, step, remaining, -, inStep, v, w, atStop, atNext, unset, assigned, -⟩ :=
    selected
  have stopElectra : .pectra ≤ stop.state.fork :=
    Nat.le_trans electra (fork_le_of_chainSteps stop.pre.chainSteps)
  have activated := step.chainStep.exit_assigned_activated stopElectra atStop atNext unset assigned
  have activatedNat := UInt64.le_iff_toNat_le.mp activated
  have toCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps stop.post.chainSteps)
  simp only at toCounted
  have stepLow := DirectSafety.Run.departureCharges_epoch_ge_start (Run.nil.snoc step) stopElectra
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps remaining.chainSteps) h.early) c
    (by simpa [Run.departureCharges] using inStep)
  obtain ⟨last, located, kept⟩ := stop.post.registryLifecycle.validators i v atStop
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots stop.state.state
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have sameActivation := kept.activationEpoch (fun same => by
    rw [same] at activatedNat
    omega)
  obtain ⟨wC, foundC, -, epochC⟩ := Run.departure_charge_exit tailC c member
  rw [index] at foundC
  obtain rfl : last = wC := Option.some.inj (located.symm.trans foundC)
  have notActive : isActiveValidator last (getCurrentEpoch counted) = false := by
    cases now : isActiveValidator last (getCurrentEpoch counted)
    · rfl
    · exact absurd (isActiveAt_eq_true_iff.mpr ⟨last, located, now⟩) inactive
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not] at notActive
  have due : c.epoch ≤ (getCurrentEpoch counted).toNat := by
    rw [← epochC]
    rcases notActive with late | exited
    · exact absurd (UInt64.le_iff_toNat_le.mpr (by rw [sameActivation]; omega)) late
    · exact Nat.le_of_not_lt fun lt => exited (UInt64.lt_iff_toNat_lt.mpr lt)
  refine ⟨DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c member, due,
    fun wC' found => ?_⟩
  obtain rfl : wC' = last := Option.some.inj (found.symm.trans located)
  have near := h.near
  have lookahead : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := h.window
  rw [sameActivation]
  omega

/-- Positions charged on C's run that are not active at C pay at most the window, and are few.

Each such position holds a validator at C, so it is a validator index.

Its charge is due by C's epoch, and it is activated by R's epoch, so `charged_count_of` counts it.
-/
private theorem charged_window (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (T : Finset ℕ)
    (keys : ∀ i ∈ T, ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      ∃ c ∈ tailC.departureCharges, c.index = i) :
    ∑ i ∈ T, Internal.chargeAmt tailC i ≤ (pinTerms config pulled anc fin).queueWindow ∧
      T.card ≤ (pinTerms config pulled anc fin).queueKeys := by
  classical
  have small : ∀ i ∈ T, i < 2 ^ 64 := by
    intro i member
    obtain ⟨-, c, inRun, index⟩ := keys i member
    obtain ⟨w, found, -⟩ := Run.departure_charge_exit tailC c inRun
    rw [index] at found
    exact (Array.getElem?_eq_some_iff.mp found).1.trans
      (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  have injective : Set.InjOn (fun i => (UInt64.ofNat i : ValidatorIndex)) T :=
    fun a ha b hb same => by
      have := congrArg UInt64.toNat same
      rwa [UInt64.toNat_ofNat_of_lt' (small a ha), UInt64.toNat_ofNat_of_lt' (small b hb)] at this
  have back : ∀ v ∈ T.image (fun i => (UInt64.ofNat i : ValidatorIndex)), v.toNat ∈ T ∧
      ¬ isActiveAt counted (getCurrentEpoch counted) v.toNat = true ∧
      ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
    intro v member
    obtain ⟨i, inT, rfl⟩ := Finset.mem_image.mp member
    rw [UInt64.toNat_ofNat_of_lt' (small i inT)]
    exact ⟨inT, keys i inT⟩
  have image : ∑ v ∈ T.image (fun i => (UInt64.ofNat i : ValidatorIndex)),
      Internal.chargeAmt tailC v.toNat = ∑ i ∈ T, Internal.chargeAmt tailC i :=
    sum_image_ofNat T small (Internal.chargeAmt tailC)
  refine ⟨image ▸ Internal.charge_amounts_le_queueWindow h tailC _ fun v member => ?_, ?_⟩
  · obtain ⟨-, inactive, c, inRun, index⟩ := back v member
    exact ⟨c, inRun, index, (charge_due h tailC inactive inRun index).2.1⟩
  · rw [← Finset.card_image_of_injOn injective]
    refine Internal.charged_count_of h tailC _ fun v member => ?_
    obtain ⟨-, inactive, c, inRun, index⟩ := back v member
    exact ⟨(charge_due h tailC inactive inRun index).2.2,
      fun d dRun dIndex => (charge_due h tailC inactive dRun dIndex).2.1, c, inRun, index⟩

/-- The keys that R exits are paid by `reserveW`, with the queue window of the created ones.

A key of the split's registry that is not slashed at R is a term of `exitedSlashable`.

It exits by R's next epoch.

It is read at its balance and rise, or at its finalized balance.

A key of the split's registry that is none of those, and not active at C, is not slashed at R.

Its exit was assigned on C's branch.

It pays its charge and its rise after it, from the window.

A created key that has exited by C pays its charge from the window.

Each key that `queueKeys` counts adds its band and the gains of the largest rate. -/
private theorem whistle_exited (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    3 * (∑ i ∈ (((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
        (fun i => PinTerms.exitedSlashable anc pulled i = true)),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
            / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      3 * (∑ i ∈ ((((slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB
          i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => ¬ isActiveAt
          counted
          (getCurrentEpoch counted) i = true)), (Internal.chargeAmt tailC i + Internal.riseQ tailC
            highC i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      3 * (∑ i ∈ (((slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter (fun i => ¬ isActiveAt counted (getCurrentEpoch
          counted) i = true)), (Internal.chargeAmt tailC i + preset.upwardBand + (pinTerms config
            pulled anc
          fin).depth * (pinTerms config pulled anc fin).gainRateMax) / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (pinTerms config pulled anc fin).reserveW := by
  classical
  set G := preset.upwardBand + (pinTerms config pulled anc fin).depth *
    (pinTerms config pulled anc fin).gainRateMax with hG
  set W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hW
  set S1 := ((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
    (fun i => PinTerms.exitedSlashable anc pulled i = true) with hS1
  set S2 := (((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
    (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
      ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
    (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true) with hS2
  set S3 := ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
    (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true) with hS3
  set P := (pinTerms config pulled anc fin).positions.filter
    (PinTerms.exitedSlashable anc pulled · = true)
  have reserveEq : (pinTerms config pulled anc fin).reserveW =
      3 * (∑ i ∈ P, max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
          (max ((pinTerms config pulled anc fin).bF i) (balanceAt fin i)) +
        (if (pinTerms config pulled anc fin).tight = true then 0 else
          (pinTerms config pulled anc fin).queueWindow +
            (pinTerms config pulled anc fin).queueKeys * G)) / W := rfl
  -- the keys that `exitedSlashable` marks are its terms
  have group1 : ∑ i ∈ S1, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i ≤
      ∑ i ∈ P, max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (max ((pinTerms config pulled anc fin).bF i) (balanceAt fin i)) := by
    have term : ∀ i ∈ S1, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i =
        max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
          (max ((pinTerms config pulled anc fin).bF i) (balanceAt fin i)) := by
      intro i member
      have marked := of_decide_eq_true (Finset.mem_filter.mp member).2
      have notRB : ¬ (pinTerms config pulled anc fin).slashedRB i = true := by
        rw [Internal.slashedRB_eq]
        simp only [decide_eq_true_eq, not_and]
        intro slashed
        rw [marked.1] at slashed
        exact absurd slashed Bool.false_ne_true
      rw [Internal.whistleEnv, ite_eq_right_of_eq_false _ _ (eq_false notRB),
        ite_eq_left_of_eq_true _ _ (eq_true (Or.inl (Finset.mem_filter.mp member).2))]
    rw [Finset.sum_congr rfl term]
    refine Finset.sum_le_sum_of_subset fun i member => ?_
    have marked := of_decide_eq_true (Finset.mem_filter.mp member).2
    obtain ⟨w, found⟩ := Internal.validator_of_flag (state := pulled) (Or.inl marked.2.2)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
        (Finset.mem_filter.mp member).2⟩
  -- the keys charged on C's run, of the split's registry or created on it
  have createdCharged : ∀ i ∈ S3, ∃ c ∈ tailC.departureCharges, c.index = i := by
    intro i member
    obtain ⟨⟨slashedC, created⟩, -⟩ := Finset.mem_filter.mp member |>.imp_left Finset.mem_filter.mp
    obtain ⟨-, flags⟩ := Finset.mem_filter.mp slashedC
    have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
    cases foundC : counted.validators.data[i]? with
    | none => simp [foundC] at flags
    | some w =>
      have marked : w.slashed = true := by simpa [foundC] using flags.2
      have assigned := (Internal.CapStep.run tailC h.caps.activation h.caps.compounding
        h.early).1.appended (Internal.Setting.delay h) i w (Nat.le_of_not_lt created) foundC marked
      obtain ⟨c, inRun, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early i
        (fun v found => absurd (Array.getElem?_eq_some_iff.mp found).1 created) w foundC assigned
      exact ⟨c, inRun, index⟩
  set T2 := S2.filter fun i => ∃ c ∈ tailC.departureCharges, c.index = i with hT2
  have dropUncharged : ∑ i ∈ S2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) =
      ∑ i ∈ T2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) := by
    rw [hT2, Finset.sum_filter (p := fun i => ∃ c ∈ tailC.departureCharges, c.index = i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with charged
    · rfl
    · rw [Internal.chargeAmt_eq_zero tailC charged,
        Internal.riseQ_eq_zero tailC highC i fun c member same => charged ⟨c, member, same⟩]
      rfl
  have inT : ∀ i ∈ T2 ∪ S3, ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      ∃ c ∈ tailC.departureCharges, c.index = i := by
    intro i member
    rcases Finset.mem_union.mp member with inT2 | inS3
    · obtain ⟨inS2, charged⟩ := Finset.mem_filter.mp inT2
      exact ⟨(Finset.mem_filter.mp inS2).2, charged⟩
    · exact ⟨(Finset.mem_filter.mp inS3).2, createdCharged i inS3⟩
  have apart : Disjoint T2 S3 := by
    refine Finset.disjoint_left.mpr fun i one two => ?_
    have small := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_filter.mp one).1).1).1).2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp two).1).2 small
  have queued : ∑ i ∈ T2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) +
      ∑ i ∈ S3, (Internal.chargeAmt tailC i + preset.upwardBand +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) ≤
      (if (pinTerms config pulled anc fin).tight = true then 0 else
        (pinTerms config pulled anc fin).queueWindow +
          (pinTerms config pulled anc fin).queueKeys * G) := by
    by_cases tight : (pinTerms config pulled anc fin).tight = true
    · -- tight: no charge of the run is due by C's epoch
      have empty : T2 ∪ S3 = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun i member => ?_
        obtain ⟨inactive, c, inRun, index⟩ := inT i member
        have bounds := charge_due h tailC inactive inRun index
        have depthBound := (Internal.tight_iff config pulled anc fin).mp tight
        have finalized := UInt64.le_iff_toNat_le.mp h.finalized
        have near := h.near
        omega
      have none2 : T2 = ∅ := Finset.subset_empty.mp (empty ▸ Finset.subset_union_left)
      have none3 : S3 = ∅ := Finset.subset_empty.mp (empty ▸ Finset.subset_union_right)
      simp [none2, none3, tight]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false tight)]
      have rises : ∀ i ∈ T2, Internal.riseQ tailC highC i ≤ G := fun i _ => by
        rw [hG]
        exact Internal.riseQ_le h tailC highC i
      obtain ⟨window, count⟩ := charged_window h tailC (T2 ∪ S3) inT
      rw [Finset.sum_union apart] at window
      rw [Finset.card_union_of_disjoint apart] at count
      have riseSum : ∑ i ∈ T2, Internal.riseQ tailC highC i ≤ T2.card * G := by
        simpa using Finset.sum_le_card_nsmul T2 _ G rises
      have rewrite3 : ∑ i ∈ S3, (Internal.chargeAmt tailC i + preset.upwardBand +
          (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) =
          ∑ i ∈ S3, Internal.chargeAmt tailC i + S3.card * G := by
        rw [hG, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          smul_eq_mul, smul_eq_mul]
        ring
      rw [Finset.sum_add_distrib, rewrite3]
      have times := Nat.mul_le_mul_right G count
      rw [Nat.add_mul] at times
      omega
  have floors := DirectSafety.Apriori.Internal.sum_div_le S1
    (Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin) W
  have floors2 := DirectSafety.Apriori.Internal.sum_div_le S2
    (fun i => Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) W
  have floors3 := DirectSafety.Apriori.Internal.sum_div_le S3
    (fun i => Internal.chargeAmt tailC i + preset.upwardBand +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) W
  rw [reserveEq]
  generalize ∑ i ∈ S1, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i = a
    at floors group1
  generalize ∑ i ∈ S2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) = b
    at floors2 dropUncharged
  generalize ∑ i ∈ S3, (Internal.chargeAmt tailC i + preset.upwardBand +
    (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) = c
    at floors3 queued
  have total : 3 * (a / W) + 3 * (b / W) + 3 * (c / W) ≤ 3 * (a + b + c) / W := by
    calc 3 * (a / W) + 3 * (b / W) + 3 * (c / W) = 3 * (a / W + b / W + c / W) := by ring
      _ ≤ 3 * ((a + b + c) / W) := Nat.mul_le_mul_left 3
          ((Nat.add_le_add Nat.div_add_div_le_add_div (Nat.le_refl _)).trans
            Nat.div_add_div_le_add_div)
      _ ≤ 3 * (a + b + c) / W := Nat.mul_div_le_mul_div_assoc 3 (a + b + c) W
  refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 3 floors)
    (Nat.mul_le_mul_left 3 floors2)) (Nat.mul_le_mul_left 3 floors3)) (total.trans ?_)
  exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 (by omega))

/-- A key active at C has no exit by the finalized epoch at R, so its `bF` is zero.

Such an exit is already set at the finalized state, which would leave the key inactive at C. -/
private theorem bF_zero_of_active (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} (active : isActiveAt counted (getCurrentEpoch counted) i = true) :
    (pinTerms config pulled anc fin).bF i = 0 := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨tailC⟩ := h.toCounted
  have stays : (pinTerms config pulled anc fin).exitBeforeFin i = false := by
    show (pulled.validators.data[i]?).any
      (fun v => decide (v.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = false
    cases found : pulled.validators.data[i]? with
    | none => rfl
    | some w =>
      simp only [Option.any_some, decide_eq_false_iff_not]
      intro exited
      obtain ⟨w0, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h found exited
      have inactive := Internal.inactive_of_exited h.twoSlots (fromFin.append tailC) foundFin
        (by rw [kept]; exact exited)
      simp only at inactive
      rw [inactive] at active
      exact Bool.false_ne_true active
  show (if (pinTerms config pulled anc fin).exitBeforeFin i = true then _ else 0) = 0
  rw [stays]
  rfl

/-- Three rewards at a bound above an aligned bound cost at most the excess more.

The excess is zero or an increment, since both bounds are whole numbers of increments.

An excess below an increment could raise the quotient's floor by one.

Three rewards weigh that more than the excess itself. -/
private theorem floor_excess {E V r Q inc : ℕ} (quotient : 30 ≤ Q) (big : 4 ≤ inc)
    (alignedE : E % inc = 0) (alignedV : V % inc = 0) (within : V ≤ E + r) :
    3 * (max E V / Q) ≤ 3 * (E / Q) + r := by
  by_cases le : V ≤ E
  · rw [max_eq_left le]
    omega
  · have lt : E < V := Nat.lt_of_not_le le
    rw [max_eq_right lt.le]
    have gap := add_le_of_lt_of_aligned alignedV alignedE lt
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le lt.le
    have sum : (E + x) / Q ≤ E / Q + x / Q + 1 := by
      rw [Nat.add_div (by omega)]
      split_ifs <;> omega
    have small : x / Q ≤ x / 30 := Nat.div_le_div_left quotient (by norm_num)
    omega

/-- The balance of a key at R with its rise is a whole number of increments. -/
private theorem eR_rise_aligned (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} (within : i < pulled.validators.data.size) :
    (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  obtain ⟨kind, alignedMin, alignedMax⟩ := Internal.capAt_kind h i within
  obtain ⟨alignedR, alignedFin⟩ := Internal.balances_aligned h i
  have fill : ∀ X : ℕ, X % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (balanceAt pulled i + (X - balanceAt pulled i)) %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := fun X aligned => by
    rcases le_total (balanceAt pulled i) X with le | le
    · rw [Nat.add_sub_of_le le]
      exact aligned
    · rw [Nat.sub_eq_zero_of_le le, Nat.add_zero]
      exact alignedR
  by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
  · have capAligned : (pinTerms config pulled anc fin).capFor i %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
      rw [Internal.capFor_eq]
      split
      · rcases kind with e | e <;> rw [e] <;> assumption
      · exact alignedMax
    rw [Internal.rise_kept config pulled anc fin i rfl kept]
    exact fill _ (Internal.min_max_aligned capAligned (Internal.min_max_aligned
      (Internal.round_aligned _ _)
      (Internal.min_max_aligned alignedFin (Internal.round_aligned _ _)).2).1).1
  · rw [rise_of_notKept h i kept]
    exact fill _ alignedMax

/-- A key that `whistle_free` pays is slashable at R, as `flagged` reads the term.

It is in R's registry and unslashed there.

It is activated by R's next epoch.

It is not yet withdrawable at the finalized epoch.

A key outside these cases is a term of `slashedRB`, `lateB` or `pendingRB`.

`sc3a_unwithdrawn` excludes a key that is withdrawable by the finalized epoch. -/
private theorem free_slashable (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} (inside : i < split.validators.data.size) (below : i < 2 ^ 64)
    (unslashedS : (split.validators.data[i]?.map (·.slashed)).getD false = false)
    (slashedC : (counted.validators.data[i]?.map (·.slashed)).getD false = true)
    (notSlashedR : ¬ (pinTerms config pulled anc fin).slashedRB i = true)
    (active : isActiveAt counted (getCurrentEpoch counted) i = true)
    (notLate : ¬ ((pinTerms config pulled anc fin).tight = false ∧
      ((pinTerms config pulled anc fin).lateB i = true ∨
        (pinTerms config pulled anc fin).pendingRB i = true))) :
    ∃ w, pulled.validators.data[i]? = some w ∧ w.slashed = false ∧
      w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 ∧
      anc.finalizedCheckpoint.epoch.toNat < w.withdrawableEpoch.toNat := by
  classical
  obtain ⟨rp⟩ := h.toPulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have near := h.near
  have roundTrip : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' below
  have oldFound := Array.getElem?_eq_getElem inside
  have oldUnslashed : split.validators.data[i].slashed = false := by
    simpa [oldFound] using unslashedS
  obtain ⟨w, foundR, lifeSplit⟩ := rp.registryLifecycle.validators i _ oldFound
  have unslashedR : w.slashed = false := by
    by_contra slashed
    exact notSlashedR (Internal.slashedRB_of_newly_slashed h oldFound foundR oldUnslashed
      (by simpa using slashed))
  have activated : w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    by_contra late
    by_cases tight : (pinTerms config pulled anc fin).tight = true
    · have bound := (Internal.tight_iff config pulled anc fin).mp tight
      have memberAC : (UInt64.ofNat i : ValidatorIndex) ∈ Internal.AC counted := by
        simpa [Internal.AC, activeVoters] using mem_getActiveValidatorIndices_of_isActiveAt
          (by rw [roundTrip]; exact active)
      have le := Internal.activation_le_of_active h (by omega) memberAC (by rw [roundTrip]; exact
        foundR)
      omega
    · have loose : (pinTerms config pulled anc fin).tight = false := by simpa using tight
      have deep := mt (Internal.tight_iff config pulled anc fin).mpr tight
      exact notLate ⟨loose, Internal.late_or_pending h foundR (by omega) (by omega)⟩
  have settled : anc.finalizedCheckpoint.epoch.toNat < w.withdrawableEpoch.toNat := by
    by_contra waited
    cases foundC : counted.validators.data[i]? with
    | none => simp [foundC] at slashedC
    | some u =>
      simp only [foundC, Option.map_some, Option.getD_some] at slashedC
      exact sc3a_unwithdrawn h oldFound foundR foundC oldUnslashed slashedC unslashedR
        (by omega)
  exact ⟨w, foundR, unslashedR, activated, settled⟩

/-- A key that `whistle_free` pays is paid by `flagged` or by its stake at C and its seat debits.

Its bound is `ebUp` or its balance and rise.

The excess over `ebUp` is at most its `rise`.

If the floor test fails, `flagged` pays the reward at `ebUp`.

Otherwise `lowEB_slashed` bounds the reward by the key's balance at C.

It also adds the key's seat debits on both runs. -/
private theorem free_key (h : Setting config checks g split fin pulled anc counted V)
    (high : ℕ) (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (inside : v.toNat < split.validators.data.size)
    (unslashedS : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    (slashedC : (counted.validators.data[v.toNat]?.map (·.slashed)).getD false = true)
    (notSlashedR : ¬ (pinTerms config pulled anc fin).slashedRB v.toNat = true)
    (notExited : ¬ PinTerms.exitedSlashable anc pulled v.toNat = true)
    (active : isActiveAt counted (getCurrentEpoch counted) v.toNat = true)
    (notLate : ¬ ((pinTerms config pulled anc fin).tight = false ∧
      ((pinTerms config pulled anc fin).lateB v.toNat = true ∨
        (pinTerms config pulled anc fin).pendingRB v.toNat = true)))
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat)) :
    3 * (Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin v.toNat / (parameters
      preset
        fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (if 2 * ((pinTerms config pulled anc fin).lowEB v.toNat - max
          ((pinTerms config pulled anc fin).ebUp v.toNat)
          (max (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).base0 v.toNat) +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
              fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
          3 * ((pinTerms config pulled anc fin).ebUp v.toNat / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) then
        3 * ((pinTerms config pulled anc fin).ebUp v.toNat / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) else 0) +
      (((pinTerms config pulled anc fin).rise v.toNat + 2 * balanceAt counted v.toNat) +
        2 * Internal.syncD eventsF v.toNat + 2 * Internal.syncD eventsC v.toNat) := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have below : v.toNat < 2 ^ 64 := v.toNat_lt
  obtain ⟨w, foundR, -, -, -⟩ := free_slashable h inside below unslashedS slashedC notSlashedR
    active notLate
  have bound := bF_zero_of_active h active
  -- the bound of the key is `ebUp` or its balance and rise
  have env : Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin v.toNat =
      max ((pinTerms config pulled anc fin).ebUp v.toNat)
        (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) := by
    unfold Internal.whistleEnv
    rw [ite_eq_right_of_eq_false _ _ (eq_false notSlashedR),
      ite_eq_right_of_eq_false _ _ (eq_false (not_or.mpr ⟨notExited, notLate⟩)), bound]
    exact max_zero _
  have excess := floor_excess (r := (pinTerms config pulled anc fin).rise v.toNat)
    (h.facts.whistleblower fork) (by have := h.facts.incrementSize; omega)
    (Internal.ebUp_aligned h v.toNat) (eR_rise_aligned h (Array.getElem?_eq_some_iff.mp foundR).1)
    (by
      obtain ⟨t, ht⟩ : ∃ t, (pinTerms config pulled anc fin).ebUp v.toNat =
          max (max (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
            (min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
              (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
        ⟨_, Internal.ebUp_eq config pulled anc fin electra v.toNat _ rfl⟩
      have := le_trans (le_max_left _ _) (le_max_left _ _) |>.trans ht.ge
      omega)
  rw [env]
  split_ifs with flag
  · omega
  · have floorLe : (pinTerms config pulled anc fin).lowEB v.toNat - max
        ((pinTerms config pulled anc fin).ebUp v.toNat)
        (max (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).base0 v.toNat) +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
            fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
        balanceAt counted v.toNat + Internal.syncD eventsF v.toNat + Internal.syncD eventsC v.toNat
          := by
      cases foundFin : fin.validators.data[v.toNat]? with
      | none =>
        have zero : balanceAt fin v.toNat = 0 := by simp [balanceAt, foundFin]
        have : (pinTerms config pulled anc fin).lowEB v.toNat = 0 := by
          rw [Internal.lowEB_unfold, zero]
          simp
        rw [this, Nat.zero_sub]
        exact Nat.zero_le _
      | some val =>
        have unslashedFin : val.slashed = false := by
          by_contra slashed
          obtain ⟨now, nowFound, nowSlashed⟩ := fromFin.slashedPersistence v.toNat val foundFin
            (by simpa using slashed)
          simp [nowFound, nowSlashed] at unslashedS
        have events := Internal.V_events h fromFin tailC high highC endEpoch endEpochC replayedF
          replayedC
        have := Internal.lowEB_slashed h fromFin tailC events v val foundFin unslashedFin retained
        simp only [List.map_append, List.sum_append] at this
        unfold Internal.syncD
        omega
    omega

/-- The stake at C of keys active at C and outside its quorum is paid twice by `cK7`. -/
private theorem free_k7 (T : Finset ValidatorIndex)
    (member : ∀ v ∈ T, v ∈ Internal.AC counted ∧ v ∉ Internal.Q counted) :
    ((2 * ∑ v ∈ T, balanceAt counted v.toNat : ℕ) : ℤ) ≤ -Internal.cK7 pulled counted := by
  classical
  let term : ValidatorIndex → ℤ := fun v => if v ∈ Internal.AC counted ∧ v ∉ Internal.Q counted then
    ((2 * Internal.eC counted v : ℕ) : ℤ) + (if v ∈ Internal.AR pulled then (Internal.eR pulled v :
      ℤ) else 0) else 0
  have negK7 : -Internal.cK7 pulled counted = ∑ v ∈ Internal.U pulled counted, term v := by
    unfold Internal.cK7
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [term]
    split_ifs <;> push_cast <;> ring
  have onT : ∀ v ∈ T, ((2 * balanceAt counted v.toNat : ℕ) : ℤ) ≤ term v := fun v hv => by
    have inside := member v hv
    simp only [term, inside.1, inside.2, not_false_eq_true, and_self, ↓reduceIte]
    split_ifs <;> simp [Internal.eC]
  rw [negK7, Finset.mul_sum, Nat.cast_sum]
  exact (Finset.sum_le_sum onT).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun v hv => Finset.mem_union.mpr (.inl (Finset.mem_union.mpr (.inr (member v hv).1))))
    fun v _ _ => by simp only [term]; split_ifs <;> positivity)

/-- The whistleblower rewards of C's other slashed keys are paid from their own stake.

These are the keys of the split's registry that C slashes and leaves active.

R neither slashes them nor exits them.

Outside the tight window, R does not count them in `late` or `pendingR`.

They are active at both branches.

A slashable key whose floor does not cover its reward is flagged, and `flagged` pays it at `ebUp`.

The others pay from their stake at C and its seat debits, by `cK7`.

The seat debits of C's branch are paid by `seatShortfall`.

The seat debits of the shared segment are the last term, which `bud_sync` pays.

The excess of the bound over `ebUp` is the key's own `rise`. -/
private theorem whistle_free (h : Setting config checks g split fin pulled anc counted V)
    (high : ℕ) (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ((3 * (∑ i ∈ (((((slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i
        = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt
        counted
        (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms config pulled anc
        fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
        pulled anc fin).pendingRB i = true)))),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
            / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) : ℕ) : ℤ) ≤
      -Internal.cK7 pulled counted - Internal.cS pulled counted V + (pinTerms config pulled anc
        fin).flagged +
          (pinTerms config pulled anc fin).seatShortfall +
        ((∑ i ∈ (((((slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc
            fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun
            i =>
            isActiveAt counted (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms
            config pulled anc fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true
            ∨ (pinTerms config pulled anc fin).pendingRB i = true)))), (pinTerms config pulled anc
            fin).rise i + 2 * ∑ i ∈ (((((slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc
            fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun
            i =>
            isActiveAt counted (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms
            config pulled anc fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true
            ∨ (pinTerms config pulled anc fin).pendingRB i = true)))),
            Internal.syncD eventsF i : ℕ) : ℤ) := by
  classical
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  set FW : Finset ℕ := (((((slashedOnC split counted).filter (fun i => i <
    split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i
    = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt counted
    (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms config pulled anc
    fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
    pulled anc fin).pendingRB i = true)))) with hFW
  have facts : ∀ i ∈ FW, i < split.validators.data.size ∧ i < 2 ^ 64 ∧
      (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i]?.map (·.slashed)).getD false = true ∧
      ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
      ¬ PinTerms.exitedSlashable anc pulled i = true ∧
      isActiveAt counted (getCurrentEpoch counted) i = true ∧
      ¬ ((pinTerms config pulled anc fin).tight = false ∧
        ((pinTerms config pulled anc fin).lateB i = true ∨
          (pinTerms config pulled anc fin).pendingRB i = true)) := by
    intro i hi
    simp only [hFW, slashedOnC, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨⟨⟨⟨count, unslashed, slashedC⟩, inside⟩, notSlashed, notExited⟩, active⟩, notLate⟩ :=
      hi
    exact ⟨inside, count.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted),
      unslashed, slashedC, notSlashed, notExited, active, notLate⟩
  have retained : ∀ v : ValidatorIndex, v.toNat ∈ FW →
      ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) :=
    fun v member => by
      obtain ⟨tail⟩ := h.toPulled
      obtain ⟨⟨⟨⟨onC, inside⟩, notR, notExit⟩, -⟩, -⟩ := by
        simpa only [hFW, Finset.mem_filter] using member
      exact slashedC_retained h fromFin tail tailC v onC inside notR notExit
  -- each key is paid by `flagged`, its stake at C, its seat debits and its rise
  have key := fun i (member : i ∈ FW) => by
    obtain ⟨inside, below, unslashed, slashedC, notSlashed, notExited, active, notLate⟩ :=
      facts i member
    have roundTrip : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' below
    have paid := free_key h high endEpoch fromFin replayedF tailC highC endEpochC replayedC
      (UInt64.ofNat i) (by simpa only [roundTrip] using inside)
      (by simpa only [roundTrip] using unslashed) (by simpa only [roundTrip] using slashedC)
      (by simpa only [roundTrip] using notSlashed)
      (by simpa only [roundTrip] using notExited) (by simpa only [roundTrip] using active)
      (by simpa only [roundTrip] using notLate)
      (retained _ (by simpa only [roundTrip] using member))
    simpa only [roundTrip] using paid
  have summed := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at summed
  -- `flagged` pays the keys that fail the floor test
  have flagSum : ∑ i ∈ FW, (if 2 * ((pinTerms config pulled anc fin).lowEB i - max
      ((pinTerms config pulled anc fin).ebUp i)
      (max (balanceAt fin i) ((pinTerms config pulled anc fin).base0 i) +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
          fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
      3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
        fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) then
      3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
        fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) else 0) ≤
      (pinTerms config pulled anc fin).flagged := by
    have flaggedEq : (pinTerms config pulled anc fin).flagged =
        ∑ i ∈ (Finset.range pulled.validators.data.size).filter (fun i =>
          ((pulled.validators.data[i]?.map (·.slashed)).getD false = false ∧
            (pulled.validators.data[i]?).any (fun v =>
              decide (v.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1) &&
                decide (anc.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat)) = true) ∧
          2 * ((pinTerms config pulled anc fin).lowEB i - max
            ((pinTerms config pulled anc fin).ebUp i)
            (max (balanceAt fin i) ((pinTerms config pulled anc fin).base0 i) +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
                fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
          3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)),
          3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := rfl
    rw [flaggedEq, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset fun i member => ?_
    obtain ⟨inFW, flag⟩ := Finset.mem_filter.mp member
    obtain ⟨inside, below, unslashed, slashedC, notSlashed, notExited, active, notLate⟩ :=
      facts i inFW
    obtain ⟨w, found, unslashedR, activated, settled⟩ := free_slashable h inside below unslashed
      slashedC notSlashed active notLate
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
      ⟨by simp [found, unslashedR], ?_⟩, flag⟩
    simp [found, activated, settled]
  -- `seatShortfall` pays the seat debits of C's run
  have seats : 2 * ∑ i ∈ FW, Internal.syncD eventsC i ≤ (pinTerms config pulled anc
    fin).seatShortfall := by
    have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
    have debits := (Internal.Run.syncDebits_le tailC h.fulu h.early highC replayedC
      pulledTotal.toNat (step_band_of_tail h fromFin tailC h.near pulledOk) FW).1
    have totalEq := getD_total_eq pulledOk
    have seatEq : (pinTerms config pulled anc fin).seatShortfall =
        2 * ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat * PinTerms.syncEnvelope preset
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat) := rfl
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    have epochs : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤
        (pinTerms config pulled anc fin).depth := by
      have := h.near
      omega
    rw [seatEq, totalEq]
    exact Nat.mul_le_mul_left 2 (debits.trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ epochs))))
  -- `cK7` pays twice the stake at C of the keys, which are active at C and slashed there
  have k7 : ((2 * ∑ i ∈ FW, balanceAt counted i : ℕ) : ℤ) ≤ -Internal.cK7 pulled counted := by
    have toSC := sum_SC_filter_positions h (fun i => ((¬ (pinTerms config pulled anc
      fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true) ∧
      isActiveAt counted (getCurrentEpoch counted) i = true) ∧ ¬ ((pinTerms config pulled anc
      fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
      pulled anc fin).pendingRB i = true))) (fun i => balanceAt counted i)
    have sameFW : ∑ i ∈ FW, balanceAt counted i = ∑ i ∈ ((slashedOnC split counted).filter
        (fun i => i < split.validators.data.size)).filter (fun i => ((¬ (pinTerms config pulled
          anc fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true) ∧
          isActiveAt counted (getCurrentEpoch counted) i = true) ∧ ¬ ((pinTerms config pulled anc
          fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
          pulled anc fin).pendingRB i = true))), balanceAt counted i := by
      rw [hFW]
      simp only [Finset.filter_filter]
      exact Finset.sum_congr (Finset.filter_congr fun x _ => by tauto) fun _ _ => rfl
    rw [sameFW, ← toSC]
    refine free_k7 _ fun v member => ?_
    obtain ⟨inSC, ⟨⟨-, active⟩, -⟩⟩ := Finset.mem_filter.mp member
    refine ⟨by simpa [Internal.AC, activeVoters] using
      mem_getActiveValidatorIndices_of_isActiveAt active, ?_⟩
    intro quorum
    have flag := (Finset.mem_filter.mp inSC).2.1
    simp only [Internal.Q, quorumVoters, Finset.mem_filter] at quorum
    unfold slashedFlagAt at flag
    have := quorum.2
    rw [flag] at this
    simp at this
  have rest : 0 ≤ -Internal.cS pulled counted V := by
    unfold Internal.cS
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> simp
  have nat : 3 * ∑ i ∈ FW, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (pinTerms config pulled anc fin).flagged +
      (∑ i ∈ FW, (pinTerms config pulled anc fin).rise i + 2 * ∑ i ∈ FW, balanceAt counted i +
        2 * ∑ i ∈ FW, Internal.syncD eventsF i + 2 * ∑ i ∈ FW, Internal.syncD eventsC i) := by
    omega
  push_cast at k7 ⊢
  have seatsZ : (2 * ∑ i ∈ FW, Internal.syncD eventsC i : ℤ) ≤
      (pinTerms config pulled anc fin).seatShortfall := by exact_mod_cast seats
  have natZ := (Int.ofNat_le.mpr nat)
  push_cast at natZ
  linarith

/-- The rise and seat debit of an active key, with its late or pending charge. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleActiveRow (config : Config)
  (pulled anc fin : BeaconState preset fork)
    (i seatDebit : ℕ) : ℕ :=
  let terms := pinTerms config pulled anc fin
  let W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let excess := (balanceAt fin i - balanceAt pulled i - terms.rise i + (W - 1)) / W
  terms.rise i + 2 * seatDebit +
    (if terms.tight = false ∧ terms.lateB i = true then 3 * balanceAt pulled i + 3 * excess
      else 0) +
    (if terms.tight = false ∧ terms.pendingRB i = true then balanceAt pulled i + 3 * excess
      else 0)

/-- A key of the split's registry that only C activates pays from its row of R.

At R it is in `late` or in `pendingR`, which only `cJ_le`'s keys of `K6` claim.

It needs no floor.

Its effective part is that row's, three times for `late`, and its rise is the single claim.

Its finalized balance can exceed its balance and rise at R.

The row's reward of that excess, rounded up, pays the rest. -/
private theorem whistle_late (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ i ∈ (((((slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i
        = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt
        counted
        (getCurrentEpoch counted) i = true)).filter (fun i => ((pinTerms config pulled anc
        fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
        pulled anc fin).pendingRB i = true)))),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
            / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      ∑ i ∈ (((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)).filter (fun i => ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms
          config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc fin).pendingRB i =
          true)))), Internal.whistleActiveRow config pulled anc fin i 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i member => ?_
  simp only [Finset.mem_filter] at member
  obtain ⟨⟨⟨-, notRB⟩, active⟩, late⟩ := member
  -- the key is active at C, so its `bF` is zero
  have noExit := bF_zero_of_active h active
  rw [Internal.whistleEnv, ite_eq_right_of_eq_false _ _ (eq_false notRB.1),
    ite_eq_left_of_eq_true _ _ (eq_true (Or.inr late)), noExit, max_eq_right (Nat.zero_le _)]
  have quotient := h.facts.whistleblower fork
  -- the larger of the two balances is the balance and rise at R, and the excess over them
  have floor : max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (balanceAt fin i) / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (balanceAt fin i - balanceAt pulled i - (pinTerms config pulled anc fin).rise i +
          ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    have split := floor_add_ceil_le (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
      (balanceAt fin i - (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat (by omega)
    have whole : max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (balanceAt fin i) = balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
          (balanceAt fin i - (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)) := by
      rw [Nat.max_def]
      split_ifs <;> omega
    have excess : balanceAt fin i - (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) +
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1 =
        balanceAt fin i - balanceAt pulled i - (pinTerms config pulled anc fin).rise i +
          ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) := by
      omega
    rw [whole]
    rw [excess] at split
    exact split
  have three : 3 * ((balanceAt pulled i + (pinTerms config pulled anc fin).rise i) /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      balanceAt pulled i + (pinTerms config pulled anc fin).rise i :=
    (Nat.mul_le_mul_right _ (by omega)).trans (Nat.mul_div_le _ _)
  simp only [Internal.whistleActiveRow]
  split_ifs
  · omega
  · omega
  · omega
  · rename_i notLate notPending
    rcases late.2 with lateKey | pendingKey
    · exact absurd ⟨late.1, lateKey⟩ notLate
    · exact absurd ⟨late.1, pendingKey⟩ notPending

/-- W from the keys' payers.

The slashed keys' rewards are paid by the shares, `reserveW`, `flagged`, `cK7` and `cS`.

The seat debits, the keys' own `rise` and R's slashing of the key pay the rest.

`registry` is the bound of the keys of the split's registry on each step of C's branch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_whistle_of (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
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
    3 * ((∑ v ∈ (Internal.K4 pulled counted V), (Internal.whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (Internal.K5 counted V), (Internal.whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (Internal.K6 pulled counted), (Internal.whistC tailC highC v.toNat : ℤ))) ≤
      -Internal.cK7 pulled counted - Internal.cS pulled counted V + (pinTerms config pulled anc
        fin).reserveW +
        (pinTerms config pulled anc fin).flagged + (pinTerms config pulled anc fin).seatShortfall +
        ((Internal.wShare preset fork ((∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC
          highC v.toNat) +
            ∑ v ∈ Internal.SC pulled counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr
            eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt
            eventsC v.toNat) +
          Internal.wShare preset fork
            (∑ v ∈ Internal.SC pulled counted split, (Internal.syncD eventsF v.toNat +
              Internal.syncD events v.toNat)) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandX fin highC v.toNat) +
          Internal.wShare preset fork ((∑ v ∈ Internal.CS counted split, Internal.propN tailC highC
            v.toNat) +
            ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.syncCr eventsC
            v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC
            v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandX fin highC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.syncCr eventsF
              v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              Internal.consAmt eventsF v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.bandX fin high
              v.toNat) :
            ℕ) : ℤ) +
        ((∑ v ∈ Internal.SC pulled counted split, (Internal.unitK (pinTerms config pulled anc fin)
          tailC highC eventsC
            events eventsF v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
              Internal.bandR (eventsF
                ++ events) v.toNat +
            if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
              (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) : ℕ) :
                ℤ) +
        ((Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre
          highC v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsP v.toNat) +
          3 * (∑ v ∈ Internal.scCharged pulled counted split tailC, Internal.whistC pre highC
            v.toNat) +
          (∑ v ∈ Internal.scCharged pulled counted split tailC,
            if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
              Internal.syncCr eventsP v.toNat then
              preset.upwardBand else 0) : ℕ) : ℤ) +
        ((∑ v ∈ Internal.SC pulled counted split with (¬ (pinTerms config pulled anc fin).slashedRB
          v.toNat =
            true ∧
          ¬ PinTerms.exitedSlashable anc pulled v.toNat = true) ∧
          isActiveAt counted (getCurrentEpoch counted) v.toNat = true,
          Internal.whistleActiveRow config pulled anc fin v.toNat (Internal.syncD eventsF v.toNat) :
            ℕ) : ℤ) +
        ((3 * ∑ v ∈ Internal.SC pulled counted split with (pinTerms config pulled anc fin).slashedRB
          v.toNat
            = true,
          ((max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
            (balanceAt fin v.toNat)) / (parameters
              preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + (parameters preset
                fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) / (parameters preset
                fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) : ℕ) : ℤ) +
        (((Internal.CS counted split).filter fun v => isActiveAt counted (getCurrentEpoch counted)
          v.toNat =
          true).card * (if (pinTerms config pulled anc fin).gainHigh = true then
              preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
            else (pinTerms config pulled anc fin).unitGain) : ℕ) := by
  classical
  have quotient := h.facts.whistleblower fork
  -- the whistleblower credits of the classes and of `CS` are bounded by the reward base
  have core := whistle_core h fromFin tail high tailC highC endEpochC replayedC pre registry
    registryCharge ((Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
      counted) ∪ Internal.SC pulled counted
      split ∪ Internal.CS counted split)
  obtain ⟨dK, -⟩ := Internal.cs_disjoint h
  obtain ⟨dS, -⟩ := Internal.sc_disjoint h
  obtain ⟨d45, d46, d56, -⟩ := Internal.classes_disjoint h
  rw [Finset.sum_union dK, Finset.sum_union dS,
    Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d46, d56⟩), Finset.sum_union d45,
    sum_CS_positions h (fun i => Internal.whistC tailC highC i),
    sum_SC_positions h (fun i => Internal.whistC tailC highC i)] at core
  -- the part of the reward base that each payer takes
  have sc := whistle_slack_sc h tail high endEpoch replayed fromFin replayedF tailC highC
    endEpochC replayedC pre eventsP
  have cs := whistle_slack_cs h tailC highC endEpochC replayedC
  have whistSplit := (Finset.sum_filter_add_sum_filter_not (slashedOnC split counted)
    (fun i => i < split.validators.data.size) (fun i => Internal.whistC tailC highC i)).symm
  have exited := whistle_exited h tailC highC
  have free := whistle_free h high endEpoch fromFin replayedF tailC highC endEpochC replayedC
  -- the keys that R slashes pay `branchR`'s claim
  have slashedKeys : 3 * ∑ i ∈ (((slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter (fun i => (pinTerms config pulled anc fin).slashedRB i =
      true)), Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i / (parameters
        preset
      fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      3 * ∑ v ∈ Internal.SC pulled counted split with (pinTerms config pulled anc fin).slashedRB
        v.toNat =
          true,
        ((max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
            (balanceAt fin v.toNat)) / (parameters
            preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + (parameters preset
              fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) / (parameters preset
              fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
    rw [sum_SC_filter_positions h (fun i => (pinTerms config pulled anc fin).slashedRB i = true)
      (fun i => (max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
          (balanceAt fin i)) / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)]
    refine Nat.mul_le_mul_left 3 (Finset.sum_le_sum fun i member => ?_)
    have slashedR : (pinTerms config pulled anc fin).slashedRB i = true := (Finset.mem_filter.mp
        member).2
    simp only [slashedR, Internal.whistleEnv, ite_true]
    exact (Nat.div_le_div_right (by omega : max (balanceAt pulled i +
      (pinTerms config pulled anc fin).rise i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      (balanceAt fin i) ≤ max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
      (balanceAt fin i) + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)).trans
      (floor_add_ceil_le (max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (balanceAt fin i)) preset.EFFECTIVE_BALANCE_INCREMENT.toNat (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat (by omega))
  -- the keys that C leaves active, read at their rise, their rows and their seat debits
  have activeKeys : ∑ v ∈ Internal.SC pulled counted split with (¬ (pinTerms config pulled anc
    fin).slashedRB
      v.toNat = true ∧
        ¬ PinTerms.exitedSlashable anc pulled v.toNat = true) ∧
        isActiveAt counted (getCurrentEpoch counted) v.toNat = true,
        Internal.whistleActiveRow config pulled anc fin v.toNat (Internal.syncD eventsF v.toNat) =
      ∑ i ∈ ((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)), Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i) := by
    rw [sum_SC_filter_positions h (fun i => (¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
      ¬ PinTerms.exitedSlashable anc pulled i = true) ∧ isActiveAt counted (getCurrentEpoch
      counted) i =
          true)
      (fun i => Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i))]
    simp only [Finset.filter_filter, and_assoc]
  have late := whistle_late h
  have partition := Finset.sum_filter_add_sum_filter_not ((((slashedOnC split counted).filter (fun i
      => i < split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc
      fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i =>
      isActiveAt
      counted (getCurrentEpoch counted) i = true)) (fun i => ((pinTerms config pulled anc fin).tight
      = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc
      fin).pendingRB i = true)))
    (fun i => Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i))
  have freeKeys : ∑ i ∈ (((((slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i =
      true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt counted
      (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms config pulled anc
      fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
      pulled anc fin).pendingRB i = true)))), (pinTerms config pulled anc fin).rise i + 2 * ∑ i ∈
      (((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter (fun i
      => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc
      pulled i =
      true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).filter (fun i
      => ¬ ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB
      i = true ∨ (pinTerms config pulled anc fin).pendingRB i = true)))), Internal.syncD eventsF i ≤
      ∑ i ∈ (((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)).filter (fun i => ¬ ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms
          config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc fin).pendingRB i =
          true)))), Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i) :=
            by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by simp only [Internal.whistleActiveRow]; split_ifs <;> omega
  have lateKeys : ∑ i ∈ (((((slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i =
      true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt counted
      (getCurrentEpoch counted) i = true)).filter (fun i => ((pinTerms config pulled anc fin).tight
      = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc
      fin).pendingRB i = true)))), Internal.whistleActiveRow config pulled anc fin i 0 ≤
      ∑ i ∈ (((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)).filter (fun i => ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms
          config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc fin).pendingRB i =
          true)))), Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i) :=
    Finset.sum_le_sum fun i _ => by simp only [Internal.whistleActiveRow]; split_ifs <;> omega
  have wSplit := (Finset.sum_filter_add_sum_filter_not (slashedOnC split counted)
    (fun i => i < split.validators.data.size) (fun i => Internal.whistC tailC highC i)).symm
  zify at core sc cs whistSplit exited free late slashedKeys activeKeys partition
  zify at freeKeys lateKeys wSplit ⊢
  linarith

/-- Glue: V keys are current at R, and distinct keys have distinct positions. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_fall (h : Setting config checks
  g split fin pulled anc counted V) :
    (∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) ≤
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).current i = true,
        (pinTerms config pulled anc fin).fall i := by
  have within := BeaconState.registryWithinLimit_of_lt h.early pulled
  refine voters_sum_le (pinTerms config pulled anc fin).fall fun v voter => ?_
  have listed : v ∈ getActiveValidatorIndices pulled (getCurrentEpoch pulled) := by
    simpa [activeVoters] using (h.voting v voter).1
  obtain ⟨validator, found, active⟩ := (mem_getActiveValidatorIndices within).mp listed
  exact Internal.mem_positions_filter config pulled anc fin found
    (isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩)

/-- The quorum reserve covers the stake that joins the active set. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_joining : (pinTerms config
  pulled anc fin).joining ≤
    (pinTerms config pulled anc fin).quorum := by
  dsimp only [pinTerms, quorumReserve]
  exact (show ∀ a b c : ℕ, a ≤ 2 * (a + b) + 3 * c by intros; omega) _ _ _

/-- The weighted gains of the flows fit `creditLow`, the slashed term and the credits themselves.

The gains are bounded linearly, at the rate `11 * D * FP / (I * WD)` of a unit of flow.

The credit part pays at a rate below one, so it costs at most itself.

The other parts round down their increments once, and `f` at least two covers the rounding.

The consolidations are a whole number `m` of increments, and the slashed keys are at most `n`. -/
private theorem flow_close (I WD FP D D2 m OC Wr Wc Wo Ws n df L : ℕ)
    (hI : 0 < I) (hWD : 0 < WD) (key : 0 < L → 11 * D * FP < WD * I) (f2 : 0 < L → 2 ≤ FP / WD)
    (hD : D ≤ df) (hDD : D ≤ D2) (hc : Wc ≤ 3 * (I * m)) (ho : Wo ≤ OC) (hs : Ws ≤ 3 * (I * n))
    (lin : 10 * (I * WD) * L ≤ 11 * D * FP * (Wr + Wc + Wo + Ws)) :
    10 * L ≤ 10 * ((33 * D2 * (m * FP / WD) + 11 * D2 * ((OC / I) * FP / WD) +
      30 * D2 * (FP / WD + 1) + 9) / 10 + 3 * (n * (2 * df * (FP / WD)))) + Wr := by
  rcases Nat.eq_zero_or_pos L with zero | pos
  · subst zero; simp
  have key := key pos
  have f2 := f2 pos
  generalize hf : FP / WD = f at f2 ⊢
  generalize hcg : m * FP / WD = cg
  generalize hog : OC / I * FP / WD = og
  have cG : m * FP ≤ WD * (cg + 1) := by
    have := Nat.lt_mul_div_succ (m * FP) hWD; rw [hcg] at this; exact this.le
  have oG : OC / I * FP ≤ WD * (og + 1) := by
    have := Nat.lt_mul_div_succ (OC / I * FP) hWD; rw [hog] at this; exact this.le
  have fG : FP ≤ WD * (f + 1) := by
    have := Nat.lt_mul_div_succ FP hWD; rw [hf] at this; exact this.le
  have ocLt : OC < I * (OC / I + 1) := by
    have := Nat.lt_mul_div_succ OC hI; exact this
  -- the credit part pays at the rate below one
  have rate : 11 * D * FP * Wr ≤ I * WD * Wr := by
    have := Nat.mul_le_mul_right Wr key.le; linarith
  have consB : 11 * D * FP * Wc ≤ I * WD * (33 * D * (cg + 1)) := by
    calc 11 * D * FP * Wc ≤ 11 * D * FP * (3 * (I * m)) := Nat.mul_le_mul_left _ hc
      _ = 33 * D * I * (m * FP) := by ring
      _ ≤ 33 * D * I * (WD * (cg + 1)) := Nat.mul_le_mul_left _ cG
      _ = I * WD * (33 * D * (cg + 1)) := by ring
  have otherB : 11 * D * FP * Wo ≤ I * WD * (11 * D * (og + f + 2)) := by
    have step1 : FP * OC ≤ FP * (I * (OC / I)) + FP * I := by
      have := Nat.mul_le_mul_left FP ocLt.le
      calc FP * OC ≤ FP * (I * (OC / I + 1)) := this
        _ = FP * (I * (OC / I)) + FP * I := by ring
    have step2 : FP * (I * (OC / I)) ≤ I * (WD * (og + 1)) := by
      calc FP * (I * (OC / I)) = I * (OC / I * FP) := by ring
        _ ≤ I * (WD * (og + 1)) := Nat.mul_le_mul_left _ oG
    have step3 : FP * I ≤ I * (WD * (f + 1)) := by
      calc FP * I = I * FP := by ring
        _ ≤ I * (WD * (f + 1)) := Nat.mul_le_mul_left _ fG
    calc 11 * D * FP * Wo ≤ 11 * D * (FP * OC) := by
          calc 11 * D * FP * Wo = 11 * D * (FP * Wo) := by ring
            _ ≤ 11 * D * (FP * OC) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ho)
      _ ≤ 11 * D * (I * (WD * (og + 1)) + I * (WD * (f + 1))) := by
          refine Nat.mul_le_mul_left _ ?_
          omega
      _ = I * WD * (11 * D * (og + f + 2)) := by ring
  have slashB : 11 * D * FP * Ws ≤ I * WD * (33 * D * n * (f + 1)) := by
    calc 11 * D * FP * Ws ≤ 11 * D * FP * (3 * (I * n)) := Nat.mul_le_mul_left _ hs
      _ = 33 * D * n * I * FP := by ring
      _ ≤ 33 * D * n * I * (WD * (f + 1)) := Nat.mul_le_mul_left _ fG
      _ = I * WD * (33 * D * n * (f + 1)) := by ring
  have total : 10 * (I * WD) * L ≤ I * WD * (Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) +
      33 * D * n * (f + 1)) := by
    calc 10 * (I * WD) * L ≤ 11 * D * FP * (Wr + Wc + Wo + Ws) := lin
      _ = 11 * D * FP * Wr + 11 * D * FP * Wc + 11 * D * FP * Wo + 11 * D * FP * Ws := by ring
      _ ≤ _ := by nlinarith [rate, consB, otherB, slashB]
  have cancel : 10 * L ≤ Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) + 33 * D * n * (f + 1) := by
    have hq : 0 < I * WD := Nat.mul_pos hI hWD
    have : I * WD * (10 * L) ≤ I * WD * (Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) +
      33 * D * n * (f + 1)) := by linarith
    exact Nat.le_of_mul_le_mul_left this hq
  have t1 : 25 * D ≤ 19 * (D * f) := by nlinarith
  have t2 : 33 * D * n * (f + 1) ≤ 60 * (n * (df * f)) := by
    have a : D * n * f ≤ n * (df * f) := by
      calc D * n * f = n * (D * f) := by ring
        _ ≤ n * (df * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD)
    have b : D * n * 2 ≤ n * (df * f) := by
      calc D * n * 2 ≤ n * (df * 2) := by
            have := Nat.mul_le_mul_left n (Nat.mul_le_mul_right 2 hD); linarith
        _ ≤ n * (df * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ f2)
    have e : 33 * D * n * (f + 1) = 33 * (D * n * f) + 33 * (D * n) := by ring
    have hN := Nat.zero_le (n * (df * f))
    linarith
  have rnd : 33 * D2 * cg + 11 * D2 * og + 30 * D2 * (f + 1) ≤
      10 * ((33 * D2 * cg + 11 * D2 * og + 30 * D2 * (f + 1) + 9) / 10) := by omega
  have m1 : D * cg ≤ D2 * cg := Nat.mul_le_mul_right _ hDD
  have m2 : D * og ≤ D2 * og := Nat.mul_le_mul_right _ hDD
  have m3 : D * f ≤ D2 * f := Nat.mul_le_mul_right _ hDD
  have e1 : 33 * D * (cg + 1) = 33 * D * cg + 33 * D := by ring
  have e2 : 11 * D * (og + f + 2) = 11 * D * og + 11 * (D * f) + 22 * D := by ring
  have e3 : 30 * D2 * (f + 1) = 30 * (D2 * f) + 30 * D2 := by ring
  have e4 : 3 * (n * (2 * df * f)) = 6 * (n * (df * f)) := by ring
  rw [e3] at rnd
  rw [e3, e4]
  linarith

/-- The gains of the counted keys, at their weights, are at most the linear rate of their flows.

The credits of each class are read through the function `cA`, `cB` or `cC` of the key. -/
private theorem flow_lin (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (A B C : Finset ValidatorIndex)
    (cA cB cC : ℕ → ℕ) :
    10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
        ((∑ v ∈ A, Internal.flowK t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
          3 * (∑ v ∈ B, Internal.flowK t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
          (∑ v ∈ C, Internal.flowK t tailC high eventsC events eventsF v.toNat (cC v.toNat))) ≤
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
        ((∑ v ∈ A, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
          3 * (∑ v ∈ B, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cB
            v.toNat)) +
          (∑ v ∈ C, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cC v.toNat)))
            := by
  have each (i c : ℕ) :
      10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
        Internal.flowK t tailC high eventsC events eventsF i c ≤
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
        Internal.flowCredit t tailC high eventsC events eventsF i c := by
    have lin := Internal.gain_lin preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
      (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) (min t.depth t.depthFin)
      (Internal.flowCredit t tailC high eventsC events eventsF i c)
    unfold Internal.flowK
    split_ifs
    · unfold Internal.flowGain
      rwa [Nat.mul_assoc (11 * Internal.flowCredit t tailC high eventsC events eventsF i c /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))]
    · simp
  have sum (S : Finset ValidatorIndex) (cS : ℕ → ℕ) :
      10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
          (∑ v ∈ S, Internal.flowK t tailC high eventsC events eventsF v.toNat (cS v.toNat)) ≤
        11 * min t.depth t.depthFin *
            (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
          (∑ v ∈ S, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cS v.toNat)) :=
            by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => each v.toNat (cS v.toNat)
  have a := sum A cA
  have b := sum B cB
  have c := sum C cC
  nlinarith [a, b, c]

/-- The initial slashing penalties of a key set on R's branch are at most `slashedR` increments.

The penalty is at most the increment that `slashR` charges, by `slashBand`. -/
private theorem flow_slash (h : Setting config checks g split fin pulled anc counted V)
    (W : Finset ValidatorIndex) :
    ∑ v ∈ W, Internal.slashW (pinTerms config pulled anc fin) v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).slashedR := by
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) (Internal.slashR_le config pulled anc fin W)
  unfold Internal.slashW Internal.slashR
  split_ifs
  · have := h.facts.slashBand
    exact le_trans (Nat.le_add_right _ _) this
  · exact le_rfl

/-- The sync flows of any keys fit the sync part of `otherCredits`.

The flows are C's credits and the debits of R's run and of the shared segment.

The debits of the shared segment and of R's run take the epochs from the finalized block to the end.

C's credits take the seats' envelope and the proposer's share, as `syncCredits_le` bounds them. -/
private theorem flow_sync (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (Internal.syncCr eventsC i + Internal.syncD events i + Internal.syncD eventsF i) ≤
      ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have totalEq := getD_total_eq pulledOk
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have credits := syncCredits_le h tailC highC replayedC keys
  have shared := (Internal.Run.syncDebits_le fromFin h.fulu h.early high replayedF
    pulledTotal.toNat (Internal.step_band_of_guard h fromFin (by omega) pulledOk) keys).1
  have own := (Internal.Run.syncDebits_le tail h.fulu h.early high replayed pulledTotal.toNat
    (step_band_of_tail h fromFin tail (Nat.le_succ _) pulledOk) keys).1
  have epochs := pin_epochs h fromFin
  rw [totalEq]
  simp only [Finset.sum_add_distrib]
  unfold Internal.syncCr Internal.syncD
  have scaled := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
      PinTerms.syncEnvelope preset pulledTotal.toNat) (le_of_eq epochs)
  rw [totalEq] at credits
  nlinarith [credits, shared, own, scaled]

/-- Some counted key has a positive flow gain when the weighted gains are positive. -/
private theorem flow_pos (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (A B C : Finset ValidatorIndex)
    (cA cB cC : ℕ → ℕ)
    (pos : 0 < (∑ v ∈ A, Internal.flowK t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
      3 * (∑ v ∈ B, Internal.flowK t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
      (∑ v ∈ C, Internal.flowK t tailC high eventsC events eventsF v.toNat (cC v.toNat))) :
    ∃ i c, 0 < Internal.flowK t tailC high eventsC events eventsF i c := by
  by_contra none
  have zero : ∀ i c, Internal.flowK t tailC high eventsC events eventsF i c = 0 := fun i c =>
    Nat.eq_zero_of_not_pos fun p => none ⟨i, c, p⟩
  simp only [zero, Finset.sum_const_zero] at pos
  omega

/-- A key with a positive flow gain is on a kept arm or beyond R's registry in the low regime.

Either way its rate per increment is below an eleventh, so the credit part pays below its worth. -/
private theorem flow_key (h : Setting config checks g split fin pulled anc counted V)
    {x y : ForkedBeaconState preset} (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i c : ℕ)
    (pos : 0 < Internal.flowK (pinTerms config pulled anc fin) tailC high eventsC events eventsF i
      c) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have arm : (pinTerms config pulled anc fin).keptArm i = true ∨
      (i ∉ (pinTerms config pulled anc fin).positions ∧
        (pinTerms config pulled anc fin).gainHigh = false) := by
    by_contra none
    unfold Internal.flowK at pos
    rw [ite_eq_right_iff.mpr (fun c => absurd c none)] at pos
    exact Nat.lt_irrefl 0 pos
  rcases arm with kept | ⟨-, low⟩
  · exact key_of_kept h i _ (Nat.le_refl _) kept
  · exact wide_of_lowGain h low

/-- The rate of one increment, at the pin's base reward, is at least two.

The base reward per increment is at least four, by `four_le_perIncrement`. -/
private theorem flow_rate (h : Setting config checks g split fin pulled anc counted V) :
    2 ≤ (pinTerms config pulled anc fin).perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
  have four := Internal.four_le_perIncrement h
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  omega

/-- The bound `ebUp` of a key of the registry is at least one increment.

Its top holds the leak of the cap over the window.

That leak is positive since the cap is an increment or more and the rate is at least four. -/
private theorem inc_le_ebUp (h : Setting config checks g split fin pulled anc counted V) {i : ℕ}
    (inside : i < pulled.validators.data.size) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ (pinTerms config pulled anc fin).ebUp i := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  have four := Internal.four_le_perIncrement h
  obtain ⟨fromFin⟩ := h.fromFin
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have incMeb : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
    have newKey := h.facts.newKey fork
    have := ((newKey.trans (Nat.sub_le _ _)).trans (Nat.sub_le _ _)).trans (Nat.sub_le _ _)
    omega
  have capLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
    unfold PinTerms.capAt
    simp only [Array.getElem?_eq_getElem inside, Option.map_some, Option.getD_some]
    exact Nat.le_trans incMeb (UInt64.le_iff_toNat_le.mp
      (Internal.minimum_cap h.caps.activation h.caps.compounding _))
  have floor : ∀ T : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T →
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T - T % preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    fun T le => by
      have parts := Nat.div_add_mod T preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      have one : 1 ≤ T / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
        (Nat.le_div_iff_mul_le incPos).2 (by omega)
      have whole : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            (T / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by nlinarith
      omega
  have leak : 2 * (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).perIncrement) ≤
        (pinTerms config pulled anc fin).leakAt
          (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i :=
    Nat.le_add_right _ _
  have capOne : 1 ≤ PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := (Nat.le_div_iff_mul_le incPos).2 (by omega)
  have leakPos : 1 ≤ (pinTerms config pulled anc fin).leakAt
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i := by
    have := Nat.mul_le_mul capOne four
    omega
  have window : 1 ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
  have product := Nat.mul_le_mul window leakPos
  rw [Internal.ebUp_eq config pulled anc fin electra i _ rfl]
  refine le_max_of_le_right (le_min capLe (floor _ ?_))
  omega

/-- The bound that the core reads for a key of R's registry is at most its bound and its slack. -/
private theorem whistleRead_le (t : PinTerms preset) (pulled anc counted : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {x' y' : ForkedBeaconState preset} (rrun : Run config checks x' y')
    {x'' y'' : ForkedBeaconState preset} (pre : Run config checks x'' y'') (highC high : ℕ)
    (eventsC eventsF events eventsP : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) :
    whistleRead t pulled anc counted tail rrun pre highC high eventsC eventsF events eventsP fin
        i ≤
      Internal.whistleEnv t pulled anc fin i +
        Internal.whistleSlack t tail rrun highC high eventsC eventsF events fin i := by
  unfold whistleRead
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- A key of R's registry is read at most twice the largest of its bounds by `whistleEnv`.

The increment that a key slashed on R's branch adds is at most its bound `ebUp`.

Every other branch reads at most the key's balance and rise, or `bF`, or its bound `ebUp`. -/
private theorem whistleEnv_le (t : PinTerms preset) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) (inc : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ t.ebUp i)
    (finLe : balanceAt fin i ≤ t.ebUp i) :
    Internal.whistleEnv t pulled anc fin i ≤
      2 * max (max (t.ebUp i) (balanceAt pulled i + t.rise i)) (t.bF i) := by
  unfold Internal.whistleEnv
  split_ifs <;> omega

/-- The keys of R's registry are read at twice the largest bounds that `otherCredits` pays. -/
private theorem whistleEnv_sum_le (h : Setting config checks g split fin pulled anc counted V)
    (T : Finset ℕ) (inside : ∀ i ∈ T, i < pulled.validators.data.size) :
    ∑ i ∈ T, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i ≤
      2 * ∑ i ∈ (pinTerms config pulled anc fin).positions,
        max (max ((pinTerms config pulled anc fin).ebUp i)
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
          ((pinTerms config pulled anc fin).bF i) := by
  calc ∑ i ∈ T, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
      ≤ ∑ i ∈ T, 2 * max (max ((pinTerms config pulled anc fin).ebUp i)
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
          ((pinTerms config pulled anc fin).bF i) :=
        Finset.sum_le_sum fun i member =>
          whistleEnv_le _ _ _ _ i (inc_le_ebUp h (inside i member))
            (Internal.effective_fin_le_ebUp h i)
    _ = 2 * ∑ i ∈ T, max (max ((pinTerms config pulled anc fin).ebUp i)
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
          ((pinTerms config pulled anc fin).bF i) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset fun i member =>
        Finset.mem_range.mpr (inside i member))

/-- The sync flows of any keys on the three runs fit the sync part of the credit total.

C's credits take the seats' envelope and the proposer's share.

The shared segment's credits and debits of a seat are at most its reward with the proposer's share.

R's debits take the envelope.

So the segment from the finalized state takes the share too. -/
private theorem sync_flows_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (highF : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents highF = .ok eventsF)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (Internal.syncCr eventsC i + Internal.syncCr eventsF i + Internal.syncD eventsF i +
      Internal.syncD events i) ≤
      ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
            (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have totalEq := getD_total_eq pulledOk
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have credits := syncCredits_le h tailC highC replayedC keys
  have pair := (Internal.Run.syncDebits_le fromFin h.fulu h.early highF replayedF
    pulledTotal.toNat (Internal.step_band_of_guard h fromFin (by omega) pulledOk) keys).2.1
  have own := (Internal.Run.syncDebits_le tail h.fulu h.early high replayed pulledTotal.toNat
    (step_band_of_tail h fromFin tail (Nat.le_succ _) pulledOk) keys).1
  have epochs := pin_epochs h fromFin
  have proposer := syncProposer_eq config pulled anc fin
  rw [proposer] at credits ⊢
  rw [totalEq] at credits ⊢
  unfold Internal.syncSeatEnvelope at pair
  rw [← epochs]
  simp only [Finset.sum_add_distrib] at pair ⊢
  unfold Internal.syncCr Internal.syncD
  generalize PinTerms.syncEnvelope preset pulledTotal.toNat = env at *
  generalize env * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) =
    share at *
  generalize (pinTerms config pulled anc fin).depth = depth at *
  generalize (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat = n2 at *
  generalize (getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat = n1 at *
  nlinarith [credits, pair, own, Nat.zero_le (n2 * (preset.SLOTS_PER_EPOCH.toNat *
    preset.SYNC_COMMITTEE_SIZE.toNat * share))]

/-- The consolidation credits and bands of any keys, on C's run and the shared segment, fit caps.

Both runs charge entries of the finalized state's queue, which `cons_due_bound` bounds by caps.

A due entry's cap is at least ten bands, so the bands of both runs are at most a fifth of the caps.

The caps are at most `consolidationsX`, as `bud_consolidations_base` reads them. -/
private theorem cons_slack_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (high : ℕ) (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat) (T : Finset ValidatorIndex) :
    (∑ v ∈ T, (Internal.consAmt eventsC v.toNat + Internal.consAmt eventsF v.toNat)) ≤
        (pinTerms config pulled anc fin).consolidationsX ∧
      10 * ((∑ v ∈ T, Internal.bandX fin highC v.toNat) + ∑ v ∈ T, Internal.bandX fin high v.toNat)
        ≤
        2 * (pinTerms config pulled anc fin).consolidationsX := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  obtain ⟨eventsFin, replayedFin⟩ := fromFin.balanceEvents_ok h.early highC
  have sameF : eventsFin = eventsF := by
    have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
    simp only at splitC
    have same := DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin
      (high := highC) (localHigh := high) (by simp only; omega) (by simp only; omega)
    rw [same, replayedF] at replayedFin
    exact (Except.ok.inj replayedFin).symm
  rw [sameF] at replayedFin
  have boundC := Internal.cons_due_bound h fromFin tailC highC endEpochC highLe replayedFin
    replayedC T
  have caps : ∀ H, H ≤ (getCurrentEpoch pulled).toNat →
      ((Internal.dueList fin electra H T).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum ≤
          (pinTerms config pulled anc fin).consolidationsX := fun H later =>
    (Internal.dueList_sum_mono fin electra later T fun v =>
      (withdrawalMaxEffectiveBalance preset fork v).toNat).trans
        ((Internal.dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat T fun v =>
          (withdrawalMaxEffectiveBalance preset fork v).toNat).trans
            (le_of_eq (Internal.consolidationsX_eq h electra).symm))
  have bands : ∀ H, H ≤ (getCurrentEpoch pulled).toNat →
      10 * ∑ v ∈ T, Internal.bandX fin H v.toNat ≤ (pinTerms config pulled anc fin).consolidationsX
        :=
    fun H later => by
      rw [Internal.bandX_sum fin electra H T, Internal.dueAt_eq fin electra H T]
      calc 10 * (preset.upwardBand * (Internal.dueList fin electra H T).length)
          = (10 * preset.upwardBand) * (Internal.dueList fin electra H T).length := by ring
        _ ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * (Internal.dueList fin electra H T).length :=
          Nat.mul_le_mul_right _ h.facts.band
        _ ≤ _ := Internal.cap_floor_sum h _
        _ ≤ _ := caps H later
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun v _ => ?_) (boundC.trans (caps highC highLe))
    simp only [Internal.consAmt, List.filter_append, List.map_append, List.sum_append]
    omega
  · have first := bands highC highLe
    have second := bands high highLeR
    omega

/-- The rounding slacks of any keys credited on C's run fit the credited-key slots of the window. -/
private theorem band_credited_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (T : Finset ValidatorIndex) (inside : ∀ v ∈ T, v.toNat < counted.validators.data.size) :
    ∑ v ∈ T, Internal.bandC tailC highC v.toNat ≤ preset.upwardBand *
      ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) := by
  rw [Internal.band_sum]
  exact Nat.mul_le_mul_left _ (Internal.credited_slots_le h tailC highC T inside)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The credits that the registry keys without a deposit gain on C's branch fit the credit total.

Each credit is rounded to at most its double, so the keys pay twice their credits.

Their whistleblower credits stay as they are, for the base to bound.

The proposer credits, the sync flows and the consolidations fit the credit total of `otherCredits`.

The bands of the consolidation targets are at most a fifth of the consolidation total.

The bands of the credited keys are the upward band for each slot of the window.

`SB` is the bands of the keys that hold a seat on the shared segment or on R's run.

`SU` is the units and the induced leak of the keys. -/
private theorem slack_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (T : Finset ℕ) (inside : ∀ i ∈ T, i < split.validators.data.size)
    (quiet : ∀ i ∈ T, Internal.depPre eventsC i = 0) (SB SU : ℕ)
    (seat : ∑ i ∈ T, (Internal.bandR (eventsF ++ events) i +
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) ≤ SB)
    (units : ∑ i ∈ T, (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events
      eventsF i +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0)) ≤ SU) :
    ∑ i ∈ T, Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail)
      highC high
        eventsC eventsF events fin i ≤
      2 * ((11 * ((pinTerms config pulled anc fin).consolidationsX +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit +
        (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).syncProposer) + 9) / 10) +
      2 * ∑ i ∈ T, Internal.whistC tailC highC i +
      preset.upwardBand * ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
      SB + SU := by
  classical
  have grows : split.validators.data.size ≤ counted.validators.data.size := by
    have := registryGrows_of_chainSteps tailC.chainSteps
    exact this
  have within := BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted
  have small : ∀ i ∈ T, i < 2 ^ 64 := fun i member =>
    Nat.lt_trans (Nat.lt_of_lt_of_le (inside i member) grows) within
  have conv := sum_image_ofNat T small
  -- each credit is rounded to at most its double
  have pointwise : ∀ i ∈ T, Internal.whistleSlack (pinTerms config pulled anc fin) tailC
      (fromFin.append tail) highC high eventsC eventsF events fin i ≤
      2 * (Internal.propN tailC highC i + Internal.whistC tailC highC i +
        (Internal.syncCr eventsC i + Internal.syncCr eventsF i + Internal.syncD eventsF i +
          Internal.syncD events i) +
        (Internal.consAmt eventsC i + Internal.consAmt eventsF i)) +
      Internal.bandC tailC highC i + Internal.bandX fin highC i + Internal.bandX fin high i +
      (Internal.bandR (eventsF ++ events) i +
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
        (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
          (pinTerms config pulled anc fin).unitGain else 0)) := by
    intro i member
    have dep := quiet i member
    unfold Internal.whistleSlack Internal.whistleSlackBase
    rw [dep]
    split_ifs <;> omega
  have total := Finset.sum_le_sum pointwise
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  simp only [Finset.sum_add_distrib] at seat units
  -- the sums of the credits
  obtain ⟨toFin⟩ := h.toFin
  have prop := Internal.proposer_rewards_le h (toFin.append fromFin) (.inl ⟨fromFin⟩) Run.nil rfl
    tailC highC
    (T.image UInt64.ofNat)
  rw [Run.nil_append] at prop
  have c1 := conv fun i => Internal.propN tailC highC i
  beta_reduce at c1
  rw [c1] at prop
  have sync := sync_flows_le h fromFin high replayedF tail high replayed tailC highC replayedC T
  simp only [Finset.sum_add_distrib] at sync
  obtain ⟨consSum, consBand⟩ := cons_slack_le h fromFin high endEpoch replayedF highLeR tailC highC
    endEpochC replayedC highLe (T.image UInt64.ofNat)
  have c2 := conv fun i => Internal.consAmt eventsC i + Internal.consAmt eventsF i
  have c3 := conv fun i => Internal.bandX fin highC i
  have c4 := conv fun i => Internal.bandX fin high i
  beta_reduce at c2 c3 c4
  rw [c2] at consSum
  rw [c3, c4] at consBand
  simp only [Finset.sum_add_distrib] at consSum
  have bands := band_credited_le h tailC highC (T.image UInt64.ofNat) (by
    intro v member
    obtain ⟨i, mem, rfl⟩ := Finset.mem_image.mp member
    rw [UInt64.toNat_ofNat_of_lt' (small i mem)]
    exact Nat.lt_of_lt_of_le (inside i mem) grows)
  have c5 := conv fun i => Internal.bandC tailC highC i
  beta_reduce at c5
  rw [c5] at bands
  have credits : (∑ i ∈ T, Internal.propN tailC highC i) + (∑ i ∈ T, Internal.syncCr eventsC i) +
      (∑ i ∈ T, Internal.syncCr eventsF i) + (∑ i ∈ T, Internal.syncD eventsF i) + (∑ i ∈ T,
        Internal.syncD events i) ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit +
        (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).syncProposer := by
    nlinarith [prop, sync]
  omega

/-- The keys of a set that hold a deposit scan on C's run are at most the deposit recipients.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits.

C's run has at most the epochs from the finalized state. -/
private theorem deposit_scan_card_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) (T : Finset ℕ)
    (positive : ∀ i ∈ T,
      0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC)) :
    T.card ≤ (pinTerms config pulled anc fin).depthFin *
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have low : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch counted).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have near := h.near
  have periodLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
  have periods : (getCurrentEpoch counted).toNat /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
          (getCurrentEpoch split).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by omega
  obtain ⟨B, S, D, cardB, cardS, cardD, hBS, hD, hSD⟩ := Internal.credited_pieces h.genesis
    h.parameters.lookahead (y := ⟨fork, counted⟩) h.early (Internal.Setting.delay h) highC
    ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tailC h.fulu periods
  have inD : T ⊆ D := fun i member => hD i (positive i member)
  refine (Finset.card_le_card inD).trans (cardD.trans ?_)
  have epochs : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (pinTerms config pulled anc fin).depthFin := by
    show _ ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat
    omega
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ epochs

/-- The deposited keys of R's registry and the created keys that C slashes fit the recipients.

A key that a deposit credits before its slashing has a positive deposit scan.

`created` is that scan for the keys created on C's branch and slashed there. -/
private theorem whist_count (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (created : ∀ i ∈ (slashedOnC split counted).filter
        (fun i => ¬ i < split.validators.data.size),
      0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC)) :
    ((((slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter
            (fun i => 0 < Internal.depPre eventsC i)).card +
        (((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).card +
        (((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true)).card) ≤
      (pinTerms config pulled anc fin).depthFin *
        preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  have apart : Disjoint
      (((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
        (fun i => 0 < Internal.depPre eventsC i))
      ((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)) :=
    Finset.disjoint_left.mpr fun i registry beyond =>
      (Finset.mem_filter.mp beyond).2 (Finset.mem_filter.mp (Finset.mem_filter.mp registry).1).2
  have all := deposit_scan_card_le h tailC highC
    ((((slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
        (fun i => 0 < Internal.depPre eventsC i)) ∪
      (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    fun i member => by
      rcases Finset.mem_union.mp member with deposited | beyond
      · exact Internal.depPre_pos_scan h tailC highC endEpochC replayedC i
          (Finset.mem_filter.mp deposited).2
      · exact created i beyond
  rw [Finset.card_union_of_disjoint apart] at all
  have split2 := Finset.card_filter_add_card_filter_not
    (s := (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The whistleblower credits of any keys are at most the whistleblower base of `otherCredits`.

The base is `Sx`, the credit total `Y` and the band total `Ck` of `otherCredits`.

A key that received a deposit on C's branch, or was created there, is read at the largest cap.

`count` bounds those keys by the deposit recipients of the window, so `Y` pays them.

`slack` is the credits that the other keys of R's registry gain on C's branch.

It holds their whistleblower credits twice, because their rounding is at most their double.

Those credits are within the base too, so the bound divides by the quotient less two. -/
private theorem flow_whist_of (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
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
    (Sx Y Ck : ℕ)
    (hSx : Sx = ∑ i ∈ (pinTerms config pulled anc fin).positions,
      max (max ((pinTerms config pulled anc fin).ebUp i)
        (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
        ((pinTerms config pulled anc fin).bF i))
    (count : ((((slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter
            (fun i => 0 < Internal.depPre eventsC i)).card +
        (((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).card +
        (((slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true)).card) ≤
      (pinTerms config pulled anc fin).depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat)
    (slack : (∑ i ∈ ((slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter (fun i => ¬ 0 < Internal.depPre eventsC
            i),
        Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
          high
          eventsC eventsF events fin i) +
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
        ((pinTerms config pulled anc fin).depthFin *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) ≤
      2 * ((11 * Y + 9) / 10) + 2 * (Ck) +
        2 * ∑ i ∈ ((slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter (fun i => ¬ 0 < Internal.depPre eventsC
            i),
            Internal.whistC tailC highC i)
    (keys : Finset ValidatorIndex) :
    ∑ v ∈ keys, Internal.whistC tailC highC v.toNat ≤
      2 * (Sx + (11 * Y + 9) / 10 + Ck) /
        ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 2) := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  have core := whistle_core h fromFin tail high tailC highC endEpochC replayedC pre registry
    registryCharge
  obtain ⟨T1, hT1⟩ : ∃ T, T = (slashedOnC split counted).filter
      (fun i => i < split.validators.data.size) := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T, T = ((slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => isActiveAt counted (getCurrentEpoch counted) i = true) := ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T, T = ((slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true) := ⟨_, rfl⟩
  rw [← hT1, ← hT2, ← hT3] at core
  rw [← hT1] at count slack
  rw [← hT2, ← hT3] at count
  have insideT1 : ∀ i ∈ T1, i < pulled.validators.data.size := fun i member => by
    rw [hT1] at member
    exact Nat.lt_of_lt_of_le (Finset.mem_filter.mp member).2 grows
  have envSum := whistleEnv_sum_le h T1 insideT1
  rw [← hSx] at envSum
  have hW : 30 ≤ (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    h.facts.whistleblower fork
  set W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hWd
  set M := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat with hM
  set t := pinTerms config pulled anc fin with ht
  have add2 : ∀ a b : ℕ, a / W + b / W ≤ (a + b) / W := fun a b =>
    (Nat.le_div_iff_mul_le (by omega)).2 (by
      rw [Nat.add_mul]
      exact Nat.add_le_add (Nat.div_mul_le_self a W) (Nat.div_mul_le_self b W))
  -- the registry keys without a deposit on C's branch pay their bound and their credits
  have x1 : ∑ i ∈ T1, min (whistleRead t pulled anc counted tailC (fromFin.append tail) pre highC
        high eventsC eventsF events eventsP fin i) M ≤
      (∑ i ∈ T1, Internal.whistleEnv t pulled anc fin i) +
        (∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i),
          Internal.whistleSlack t tailC (fromFin.append tail) highC high eventsC eventsF events fin
            i) +
        M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not T1 (fun i => 0 < Internal.depPre eventsC i)]
    have deposited : ∑ i ∈ T1.filter (fun i => 0 < Internal.depPre eventsC i), min (whistleRead t
      pulled anc
        counted tailC (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin
        i) M ≤
          M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card :=
      (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm])
    have quiet : ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), min (whistleRead t
      pulled anc
        counted tailC (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin
        i) M ≤
          (∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), Internal.whistleEnv t pulled
            anc fin i) +
          ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i),
            Internal.whistleSlack t tailC (fromFin.append tail) highC high eventsC eventsF events
              fin i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ =>
        (min_le_left _ _).trans (whistleRead_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    have sub : ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), Internal.whistleEnv t
      pulled anc fin i ≤
        ∑ i ∈ T1, Internal.whistleEnv t pulled anc fin i :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  have x2 : ∑ i ∈ T2, min (createdCeil t tailC highC eventsC i) M ≤ M * T2.card :=
    (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm])
  have x3 : ∑ i ∈ T3, min (Internal.chargeAmt tailC i + whistleExtra t tailC highC eventsC i) M ≤
      M * T3.card :=
    (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm])
  have paid : M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card + M * T2.card +
      M * T3.card ≤ M * (t.depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) := by
    have := Nat.mul_le_mul_left M count
    rwa [Nat.mul_add, Nat.mul_add] at this
  -- the numerator of the three sums, which every set of keys is bounded by over `W`
  obtain ⟨N, hN⟩ : ∃ N, N = (∑ i ∈ T1, Internal.whistleEnv t pulled anc fin i) +
      (∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i),
        Internal.whistleSlack t tailC (fromFin.append tail) highC high eventsC eventsF events fin i)
          +
      M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card + M * T2.card + M * T3.card :=
    ⟨_, rfl⟩
  have bound : ∀ S' : Finset ValidatorIndex, ∑ v ∈ S', Internal.whistC tailC highC v.toNat ≤ N / W
    := by
    intro S'
    refine (core S').trans ?_
    refine (Nat.add_le_add (Nat.add_le_add (sum_div_le T1 _ W) (sum_div_le T2 _ W))
      (sum_div_le T3 _ W)).trans ?_
    refine ((Nat.add_le_add_right (add2 _ _) _).trans (add2 _ _)).trans ?_
    refine Nat.div_le_div_right ?_
    omega
  -- the whistleblower credits of the keys in the numerator are bounded by the base itself
  have within := BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted
  have credits : ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), Internal.whistC tailC
    highC i ≤
      N / W := by
    have small : ∀ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), i < 2 ^ 64 :=
      fun i member => by
        have inT1 := (Finset.mem_filter.mp member).1
        rw [hT1] at inT1
        have inSlashed := (Finset.mem_filter.mp inT1).1
        unfold slashedOnC at inSlashed
        exact Nat.lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp inSlashed).1) within
    have image := bound ((T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i)).image UInt64.ofNat)
    rwa [sum_image_ofNat _ small] at image
  -- `N` is at most the numerator that `otherCredits` pays, with the credits counted twice
  have numerator : N ≤ 2 * (Sx + (11 * Y + 9) / 10 +
      Ck) + 2 * (N / W) := by
    omega
  refine (bound keys).trans ?_
  refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
  have shape : N / W * W ≤ N := Nat.div_mul_le_self N W
  have split2 : N / W * W = N / W * (W - 2) + N / W * 2 := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

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
  have exitLt := exitEpoch_toNat_lt_of_ne_far unset
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

/-- A key whose exit at R is by the finalized epoch is read by `exitBeforeFin`. -/
private theorem exitBeforeFin_of_exit (config : Config) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat) :
    (pinTerms config pulled anc fin).exitBeforeFin i = true := by
  simp only [pinTerms]
  simp [foundPulled, exited]

/-- `bF` of a key that `exitBeforeFin` reads is its finalized effective or rounded balance. -/
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

The key is not one that R slashes: `registry_frozen` bounds those, from the finalized state.

Its balance at a state of C's branch is its finalized balance and its credits since.

Those credits are sync and consolidation credits, which the slack holds with one rounding band. -/
private theorem registry_exited
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
      have replayedF' := replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called h)
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
private theorem sum_unitK (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ) (eventsC events eventsF : List (BalanceEvent preset))
    (S : Finset ValidatorIndex) (cred : ValidatorIndex → ℕ) :
    ∑ v ∈ S, Internal.unitK t tailC high eventsC events eventsF v.toNat (cred v) =
      t.unitGain * (S.filter fun v =>
        0 < Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cred v)).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold Internal.unitK
  split <;> simp_all

/-- The units of the counted keys, at their weights, fit the unit terms of `pinReserve`.

A credited key's unit takes a slot of `creditUnits`, and a seat-only key's takes a seat unit.

A key credited only by a consolidation of X takes its unit from `consolidationsXCount`.

A key slashed only on R's branch takes its unit in `branchR`.

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
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC v.toNat
  have s5 : ∑ v ∈ Internal.K5 counted V,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat
        (Internal.propC tailC highC v.toNat) =
        (pinTerms config pulled anc fin).unitGain * G5.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.propC tailC highC v.toNat
  have s6 : ∑ v ∈ Internal.K6 pulled counted,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * G6.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC v.toNat
  have ssc : ∑ v ∈ Internal.SC pulled counted split,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * Gsc.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC v.toNat
  have scs : ∑ v ∈ Internal.CS counted split,
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF v.toNat =
        (pinTerms config pulled anc fin).unitGain * Gcs.card :=
    sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC v.toNat
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
      rw [Internal.inducedR_of_withdrawn _ _ _ (withdrawnRB_of_le config pulled anc fin found
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

The key's flows also compound, which `keyExtra` charges with its unit and its induced leak.

The start's rounding is `prefix_envelope`'s floor form. -/
private def keyCeiling (anc : BeaconState preset fork)
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
    exact key_of_kept h i _ (Nat.min_le_left _ _) kept
  have hunit : t.unitGain = t.depth * (t.perIncrement *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) := by
    subst ht
    rfl
  have hW : 11 * Internal.slashW t i < 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    subst ht
    have hWdb := slashW_add_downwardBand_le h i
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
  exact ⟨v, rfl, e1, t, replayed1, rfl, prefix_deposits_clean h pre aEarly highC replayed1 v
    (by simpa using (Bool.and_eq_true_iff.mp flag).1)⟩

/-- The credits of C's run before a key's slashing are within the credit terms of `whistleSlack`.

They are the key's block credits from rewards and its consolidation and deposit credits.

They are those up to the step.

The proposer credits are within `propN` of the whole run.

The deposits before the step are those of `depPre`, since the key is unslashed before it.

The consolidation credits are within `consAmt`. -/
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
  have depPreOk := deposits_le_depPre e1 v.toNat clean
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
private theorem creditScan_prefix_le (blockP slotP : BalanceSource → Bool) (v high : ℕ)
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
  have gross := creditScan_prefix_le
    (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i highC pre step
    post
  have deposits := creditScan_prefix_le (fun _ => false) (fun s => decide (s = .deposits)) i highC
    pre step post
  refine ⟨creditScan_prefix_le _ _ i highC pre step post,
    creditScan_prefix_le _ _ i highC pre step post, ?_⟩
  unfold Internal.bandC Internal.grossScan
  split_ifs <;> omega

/-- The sync credits of the events of a prefix of C's run are within those of the whole run.

The replay of the prefix at `highC` is a prefix of the replay of the run. -/
private theorem syncCr_prefix_le {a b : ForkedBeaconState preset}
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
    keyCeiling anc run tailC highC eventsC events eventsF v := by
  have fSyncE : Internal.syncD events v ≤ Internal.syncF events v := by
    rw [syncF_eq]; unfold Internal.syncD; omega
  have fSyncC : (eventsC.map (Internal.syncCredit v)).sum ≤ Internal.syncF eventsC v := by
    rw [syncF_eq]; omega
  unfold keyCeiling Internal.keyExtra
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The rise of a key on the kept branch bounds its effective balance on C's branch, up to flows.

Its balance on C's branch is bounded by `Bc`, and the effective balance by `stay`.

`Bc` adds up R's balance and the leak at the largest effective balance.

It adds the debits and slack on R's runs, and the credits and gains of C's run.

The bound also accounts for flows between states and the bands that pay for rounding.

The cap enters only through `stay` and `cappedY`, which the cap arms prove.

The bound applies to any prefix of C's run.

The start of the effective balance's ceiling is any state's, bounded as `rise_close` reads it.

It concludes with the flows and bands in the form of `keyExtra`, without the credits of `credC`.

`keyCeiling_of_close` gives `keyCeiling` from it, and the credits `Cr` that it holds.

`cappedY` is the premise `capped` of `rise_close`, for a key on a low rate.

It says the effective balance at C is at most the cap that `capFor` reads, and the rounded stake.

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
  have key := key_of_kept h v.toNat D hDle kept
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
    exact leakAt_foldl_le config pulled anc fin (fromFin.append tail) v.toNat notWithdrawn
  have hHeq : H = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      Df * ((11 * q + 9) / 10 + 3 + (pinTerms config pulled anc fin).leak v.toNat) +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) := by
    rw [hH, hq, hDf]
    exact high_eq config pulled anc fin electra v.toNat
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
  have hWdb := slashW_add_downwardBand_le h v.toNat
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
    (fun pre post same => hM ▸ effective_le_foldl_max (fromFin.append tail) v.toNat
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
  have rateLow := keptArm_eq v.toNat kept
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
      (fun pre post cut => hM ▸ effective_le_foldl_max (fromFin.append tail) v.toNat pre post cut)
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
    exact path_le_of_start toC (fromC.append tail) v.toNat _ before envAll z hz
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

It is `key_core_frozen_from` at the end of C's run.

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
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat :=
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
private theorem registry_frozen (h : Setting config checks g split fin pulled anc counted V)
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
  · have bound := short_in_fin h fromC tailC step member i inside leftShort.2.2
      (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC eventsF events fin i) leftShort.1.2
    omega
  have near := h.near
  -- the replays are read at R's epoch
  obtain ⟨replayedF', replayed'⟩ :=
    replays_at_pulled tail high endEpoch replayed fromFin replayedF
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
    syncCr_prefix_le pre step post highC replayedPre replayedC v.toNat
  exact whistle_of_close h _ rfl pre ((pre.snoc step).append post) (fromFin.append tail) highC high
    eventsC eventsPre eventsF events v.toNat
    (Internal.credC pre highC v.toNat + Internal.whistC pre highC v.toNat +
      (eventsPre.map (Internal.syncCredit v.toNat)).sum)
    (balanceAt as v.toNat) core (by omega) p2.1 p1 p2.2.1 p3 p2.2.2 kept

/-- At the finalized state there is no earlier balance path, and the effective balance fits. -/
private theorem finalized_start (h : Setting config checks g split fin pulled anc counted V)
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
private theorem registry_headroom (h : Setting config checks g split fin pulled anc counted V)
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
  have headroom := rise_of_notKept h i notKept
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
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  obtain ⟨shared⟩ := h.toFin
  have capped := Internal.effectiveAt_le_capMax (shared.append (fromFin.append tailC))
    h.genesis h.caps h.early v.toNat
  have headroom := rise_of_notKept h v.toNat notKept
  have countedLe : balanceAt counted v.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := capped
  unfold keyCeiling
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C's branch created beyond the split is bounded by its credits and their gains.

The key's stake is its credits on C's branch.

Its effective balance is within the ceiling of a created key.

Its flows hold the credits, and the key's gain over the depth of the window is the flow gain.

The premises are the rate of the ceiling at the depth of the window.

They are also the charge of the flow gain to the key.

The unit pays the joint floor, and the band is an upward band at least. -/
private theorem created_key_ceiling (h : Setting config checks g split fin pulled anc counted V)
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
  obtain ⟨z, pre, post, -, positive, -, bound⟩ := created_ceiling h tailC highC endEpochC replayedC
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
  have sync := syncF_eq eventsC v.toNat
  have credits : Internal.syncCr eventsC v.toNat = (eventsC.map (Internal.syncCredit v.toNat)).sum
    := rfl
  unfold Internal.keyExtra
  omega

/-- The exit of a key that the finalized state does not hold is not before the finalized epoch.

An exit up to the finalized epoch would be an exit of the finalized registry. -/
private theorem created_exitAfterFin (h : Setting config checks g split fin pulled anc counted V)
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
    (Nat.add_le_add_right (created_exitAfterFin h created w found) _)

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
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF v.toNat := by
  classical
  by_cases absent : split.validators.data.size ≤ v.toNat
  · have activated := Internal.activated_of_quorum h.early voter
    have core := created_key_ceiling (events := events) (eventsF := eventsF) h tail fromFin tailC
      highC endEpochC replayedC activated absent
      (key_of_kept h v.toNat _ (Nat.min_le_left _ _) kept) (Or.inl kept)
      (created_band h fromFin (getCurrentEpoch pulled).toNat (Nat.le_succ _) replayedF tailC highC
        endEpochC replayedC activated absent)
    unfold keyCeiling
    omega
  · -- the key is created on the shared segment, and its envelope starts at its first state
    have splitSize : v.toNat < split.validators.data.size := Nat.lt_of_not_le absent
    obtain ⟨c, toC, fromC, cutC, insideC, -, before, floorStart, -⟩ :=
      created_first_state h fromFin created splitSize
    exact key_core_cap h tail replayed fromFin replayedF tailC highC endEpochC replayedC v
      (Internal.voter_unslashed h v voter) (created_late h created) toC fromC cutC insideC before
      (Or.inr floorStart) kept

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The leak that the counted keys' sync debits on R's branch induce, at their weights.

The keys that are slashed at C and not at the split are counted too, at weight one.

The keys slashed at the split that R's call reads as slashed are counted at weight three.

They are the keys of `Kc` in `bud_sync`.

It fits `syncLeak`, and the leak of one increment for each key slashed on R's branch.

The second bound is read by `flow_whist`, through `whist_units`. -/
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
    replays_at_pulled tail high endEpoch replayed fromFin replayedF
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
          exact envelope_of_clean_fin h fromFin tail replayedF' replayed' v (by omega)
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
        exact envelope_of_clean_fin h fromFin tail replayedF' replayed' v (by omega)
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

The key's flows also compound, which `keyExtra` charges with its unit and its induced leak.

`keyExtra` also holds the key's sync debits on the shared segment. -/
private theorem key_core (h : Setting config checks g split fin pulled anc counted V)
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
    keyCeiling anc (fromFin.append tail) tailC highC eventsC events eventsF i := by
  classical
  -- the replays are read at R's epoch
  obtain ⟨replayedF', replayed'⟩ :=
    replays_at_pulled tail high endEpoch replayed fromFin replayedF
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
        (finalized_start h v.toNat).1 (.inl (finalized_start h v.toNat).2) kept
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
    have core := key_core h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
      replayedC v.toNat (Array.getElem?_eq_some_iff.mp found).1
      (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp member).2.2.1)
    simp only [Internal.eC, Internal.eR]
    push_cast
    unfold keyCeiling at core
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

Each step adds its epoch rewards, which `riseScan` sums once the charge is seen.

It also adds its net block credits and the credits of its slot steps other than the rewards.

The rewards that `riseScan` sums do not fall along the run. -/
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

From `a` the balance rises by the epoch rewards that `riseScan` sums, and by the other credits.

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

They are at most those of `propC`, `whistC` and sync.

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
  have exited := exitEpoch_toNat_lt_of_ne_far set
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
  have propLe := creditScan_prefix_le (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations)) v.toNat highC front step post
  have whistLe := creditScan_prefix_le (fun s => decide (s = .slashings)) (fun _ => false)
    v.toNat highC front step post
  have parts := (Internal.credit_parts_le ((front.snoc step).append post) highC v replayedC).2
  have syncSplit : Internal.syncCr (eventsP ++ eventsY) v.toNat =
      Internal.syncCr eventsP v.toNat + Internal.syncCr eventsY v.toNat := by
    simp only [Internal.syncCr, List.map_append, List.sum_append]
  have syncLe := syncCr_prefix_le front step post highC replayedY replayedC v.toNat
  unfold Internal.whistleSlack Internal.whistleSlackBase
  simp only [Internal.propC, Internal.whistC] at whole propSplit whistSplit parts ⊢
  omega

/-- The effective balance at its slashing of a charged key of the split's registry.

The charge of the key is on C's run, in an epoch after the split's.

The balance at the charge is read as `charge_effective_bound` reads it.

Its bound is that of `registryCharge` in `whistle_core`, without the credits of `pre`. -/
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

Its bound is that of `whistle_core`'s premise `registryCharge`. -/
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
          created_first_state h fromFin beyond inside
        exact registry_frozen h tail high endEpoch replayed fromFin replayedF tailC highC
          endEpochC replayedC step member v.toNat toC fromC cutC insideC before (.inr floorStart)
          unslashed flag
          (fun w found _ => Internal.late_of_exitAfterFin h v.toNat (created_exitAfterFin h beyond)
            w found)
          kept
      · exact registry_headroom (config := config) h tailC step member i kept _
    · have inFin : i < fin.validators.data.size := Nat.lt_of_not_le beyond
      obtain ⟨w, found⟩ : ∃ w, pulled.validators.data[i]? = some w :=
        ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le inside grows)⟩
      by_cases exited : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat
      · by_cases slashedR : (pinTerms config pulled anc fin).slashedRB i = true
        · by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
          · refine registry_frozen h tail high endEpoch replayed fromFin replayedF tailC highC
              endEpochC replayedC step member i Run.nil fromFin (Run.nil_append fromFin) inFin
              (finalized_start h i).1 (.inl (finalized_start h i).2) unslashed flag
              (fun w' found' unslashedR => ?_) kept
            -- R slashes the key, so it is not unslashed there
            rw [Internal.slashedRB_eq] at slashedR
            have := (of_decide_eq_true slashedR).1
            simp [found'] at this
            rw [this] at unslashedR
            exact absurd unslashedR (by decide)
          · exact registry_headroom (config := config) h tailC step member i kept _
        · exact registry_exited h fromFin tail high endEpoch replayedF tailC highC endEpochC
            replayedC step member i inside
            (fun w' found' => by
              obtain rfl := Option.some.inj (found.symm.trans found')
              exact exited) flag slashedR
      · -- A finalized key that exits at or after the finalized epoch.
        by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
        · exact registry_frozen h tail high endEpoch replayed fromFin replayedF tailC highC
            endEpochC replayedC step member i Run.nil fromFin (Run.nil_append fromFin) inFin
            (finalized_start h i).1 (.inl (finalized_start h i).2) unslashed flag
            (fun w' found' _ => Internal.late_of_exitAfterFin h i
              (fun w'' found'' => by
                obtain rfl := Option.some.inj (found.symm.trans found'')
                omega) w' found') kept
        · exact registry_headroom (config := config) h tailC step member i kept _
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
    have := syncF_eq eventsC v.toNat
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

So `credC` is `propC`.

The rest is `key_core`. -/
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
  have exited := exitEpoch_toNat_lt_of_ne_far assigned0
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
  have core := key_core h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
    replayedC v.toNat (Nat.lt_of_lt_of_le insideSplit tail.registryLifecycle.size_le)
    (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp member).1)
  unfold keyCeiling at core
  rw [credEq] at core
  simp only [Internal.eC, Internal.eR]
  omega

/-- The other keys that are previous-epoch-only in C, and their exits.

A key with a departure charge on C's run is at its charge plus its rise after that.

Any other key has its exit assigned before the split, so it is at its balance at R plus its rise.

Both add C's proposer credits and sync seats.

A key with a charge pays no deposit credit after it, so `propC` stands for its credits.

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
    have sync := syncF_eq eventsC v.toNat
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

That gives the rate premise of `created_key_ceiling`. -/
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
  exact created_key_ceiling h tail fromFin tailC highC endEpochC replayedC activated absent
    (key_of_lowGain h lowGain) (Or.inr ⟨notPosition, lowGain⟩)
    (created_band h fromFin high endEpoch replayedF tailC highC endEpochC replayedC activated
      absent)

/-- The units of the active keys of `CS` are held by the units of the keys of `CS`.

Off the high gain rate each active key of `CS` charges one `unitGain` for its stake at the slashing.

Each of them was created by a deposit of C's run, so its flows are positive and its unit is one.

The slot of that unit is the slot of the deposit, which `bud_units` already gives to the key. -/
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
  rw [sum_unitK _ tailC highC eventsC events eventsF _ fun v => Internal.credC tailC highC v.toNat,
    Nat.mul_comm]
  refine Nat.mul_le_mul_left _ (Finset.card_le_card fun v member => ?_)
  obtain ⟨inCS, active⟩ := Finset.mem_filter.mp member
  refine Finset.mem_filter.mpr ⟨inCS, ?_⟩
  obtain ⟨-, absent, -⟩ := Finset.mem_filter.mp inCS
  obtain ⟨w, found, live⟩ := isActiveAt_eq_true_iff.mp active
  have deposit := created_deposit h fromFin replayedF tailC highC endEpochC replayedC
    ⟨w, found, Internal.activation_ne_far_of_active live, activationLe_of_active live⟩ absent
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
    created_deposit h fromFin replayedF tailC (getCurrentEpoch counted).toNat (Nat.le_succ _)
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
  refine deposit_scan_card_le h tailC (getCurrentEpoch counted).toNat _ fun i hi => ?_
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
  rcases Finset.mem_union.mp hv with inK6 | inCS
  · obtain ⟨member, beyond⟩ := Finset.mem_filter.mp inK6
    exact deposit v (Internal.activated_of_activeVoters h.early (Finset.mem_filter.mp member).1)
      (Nat.le_trans grows beyond)
  · obtain ⟨member, active⟩ := Finset.mem_filter.mp inCS
    obtain ⟨w, found, isActive⟩ := isActiveAt_eq_true_iff.mp active
    exact deposit v
      ⟨w, found, Internal.activation_ne_far_of_active isActive, activationLe_of_active isActive⟩
      (Finset.mem_filter.mp member).2.1

/-- The keys of `CS` that are active at C fit the deposit slots that the keys beyond R leave.

At a high gain rate each takes the largest cap, and `creditCap` is the cap of each deposit slot.

The keys of `K6` beyond R's registry take `capUse` of it, so the slots are counted once.

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

`created_deposit` reads the deposit of a created key activated by C. -/
private theorem whist_created (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ i ∈ (slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC) :=
        by
  classical
  intro i member
  obtain ⟨toFin⟩ := h.toFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨inSlashed, outside⟩ := Finset.mem_filter.mp member
  simp only [slashedOnC, Finset.mem_filter, Finset.mem_range] at inSlashed
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
  have replayedF' := replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called h)
    replayedF
  have actLe : counted.validators.data[i].activationEpoch ≤ getCurrentEpoch counted := by
    rw [actEq]
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_trans (UInt64.le_iff_toNat_le.mp activated) epochLe)
  have := created_deposit h fromFin replayedF' tailC highC endEpochC replayedC
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

/-- The units and the induced leak of the registry keys that C slashes fit the base.

The keys are in `SC`, and `bud_units` and `bud_syncLeak` bound `SC` alone at weight one.

A key that R slashes holds a second unit, and `slashedRB_card_le` bounds those keys. -/
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
    (sub : T ⊆ (slashedOnC split counted).filter (fun i => i < split.validators.data.size)) :
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
    simp only [slashedOnC, Finset.mem_filter, Finset.mem_range] at slashedOn
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
  have conv := sum_image_ofNat T small
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

/-- The whistleblower credits of any keys on C's branch fit the base of `otherCredits`.

The base reads each key of R's registry at twice its bound.

It reads each deposited or created key at the largest cap.

`registry` and `registryCharge` are the bounds of the registry keys at their slashing.

The proof reads the base of `otherCredits` off its definition and pays each term of the slack. -/
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
  have count := whist_count h tailC highC endEpochC replayedC
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
  set T1 := (slashedOnC split counted).filter (fun i => i < split.validators.data.size) with hT1
  have subT : T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i) ⊆
      (slashedOnC split counted).filter (fun i => i < split.validators.data.size) := by
    rw [← hT1]
    exact Finset.filter_subset _ _
  have slackT := slack_le h fromFin tail high endEpoch replayed replayedF highLeR tailC highC
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
  exact (flow_whist_of h fromFin tail high tailC highC endEpochC replayedC pre registry
    registryCharge Sx Y ((slots' + L) * inc + F + t.creditUnits + t.syncLeak + e1 + e2) hSx count
    slack keys).trans
    (le_of_eq (by congr 2; omega))

/-- The flow gains of the counted keys, at their weights, fit the low part of `creditGain`.

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
    obtain ⟨onF, onR⟩ := replays_at_pulled tail high endEpoch replayed fromFin replayedF
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
        (flow_sync h tail high replayed fromFin replayedF tailC highC replayedC _))
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
    flow_slash h (Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled counted)
  have weightOther := Internal.weighted_le (fun v : ValidatorIndex => Internal.whistC tailC highC
    v.toNat +
    (Internal.syncCr eventsC v.toNat + Internal.syncD events v.toNat + Internal.syncD eventsF
      v.toNat)) d45 d46 d56
  have weightSlash := Internal.weighted_le (fun v : ValidatorIndex => Internal.slashW t v.toNat) d45
    d46 d56
  have lin := flow_lin t tailC highC eventsC events eventsF (Internal.K4 pulled counted V)
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
    obtain ⟨i, c, found⟩ := flow_pos t tailC highC eventsC events eventsF _ _ _
      (fun i => Internal.credC tailC highC i) (fun i => Internal.propC tailC highC i)
      (fun i => Internal.credC tailC highC i) pos
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (min_le_left _ _)))
      (flow_key h tailC highC eventsC events eventsF i c found)
  have rate : 0 < (∑ v ∈ Internal.K4 pulled counted V, Internal.flowK t tailC highC eventsC events
    eventsF v.toNat) +
      3 * (∑ v ∈ Internal.K5 counted V,
        Internal.flowK t tailC highC eventsC events eventsF v.toNat (Internal.propC tailC highC
          v.toNat)) +
      (∑ v ∈ Internal.K6 pulled counted, Internal.flowK t tailC highC eventsC events eventsF
        v.toNat) →
      2 ≤ t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum /
        WEIGHT_DENOMINATOR.toNat := fun _ => flow_rate h
  have close := flow_close preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
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

In the high regime they are also paid by `capUse`, their share of `creditCap`.

They joined the registry on C's branch, so their stake is the credits that reach them.

The credits compound, which `keyExtra`'s flow gain charges, when the gain rate is low.

Otherwise `capUse` charges each key up to the cap. -/
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

`bud_exitedR` charges it.

Its stake in C is at most its stake at R and its rise.

So is the stake of a key whose exit R reads, which `exiting` and `exitingRise` charge. -/
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
    have := key_core (config := config) h tail high endEpoch replayed fromFin replayedF tailC highC
      endEpochC replayedC v.toNat hin
      (by rw [UInt64.ofNat_toNat]; exact (Finset.mem_filter.mp hv).2.1)
    unfold Internal.eC Internal.eR
    unfold keyCeiling at this
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

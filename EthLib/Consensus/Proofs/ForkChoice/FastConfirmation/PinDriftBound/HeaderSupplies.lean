module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.CreditBudgets

/-! How the pin reserve shares its charges between quorum and whistleblower accounting. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

namespace Internal

/-! ### The supplies of the header terms for the newly slashed and the created slashed keys

The quorum classes and the keys slashed on C can draw on the same reserve terms.

The newly slashed and the created slashed keys join that claim, and the entry is spent once. -/

/-- The rise budget for R's current keys covers both quorum and whistleblower charges.

The quorum charge covers keys active on both branches and counted at C, excluding the voter set.

The whistleblower charge draws on different current keys at R, newly slashed on C's branch. -/
theorem budget_rise (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (stayingKeys pulled counted V), (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        (pinTerms config pulled anc fin).current v.toNat = true,
          (pinTerms config pulled anc fin).rise v.toNat) ≤
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).current i = true,
          (pinTerms config pulled anc fin).rise i := by
  classical
  obtain ⟨dSC, -⟩ := newlySlashed_disjoint h
  have dis : Disjoint (stayingKeys pulled counted V) ((activeNewlySlashed config pulled anc fin
      counted
    split).filter
      fun v => (pinTerms config pulled anc fin).current v.toNat = true) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_left
          (Finset.subset_union_left.trans Finset.subset_union_left) dSC))
  rw [← Finset.sum_union dis]
  refine voters_sum_le (fun i => (pinTerms config pulled anc fin).rise i) fun v hv => ?_
  rcases Finset.mem_union.mp hv with member | member
  · simp only [stayingKeys, Finset.mem_filter] at member
    obtain ⟨w, found, active⟩ := Internal.active_of_activeVoters h.early (s := pulled) member.2.1
    exact Internal.mem_positions_filter config pulled anc fin found
      (isActiveAt_eq_true_iff.mpr ⟨w, found, active⟩)
  · obtain ⟨-, current⟩ := Finset.mem_filter.mp member
    obtain ⟨w, found, -⟩ := isActiveAt_eq_true_iff.mp
      (show isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true from current)
    exact Internal.mem_positions_filter config pulled anc fin found current

/-- The rise budget for keys joining at R's next epoch covers quorum and whistleblower charges.

The quorum charge covers joining keys that are active and counted at C but inactive at R.

The whistleblower charge draws on different joining keys at R, newly slashed on C's branch. -/
theorem budget_joinRise (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (joinedKeys pulled counted) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) ≤
      (pinTerms config pulled anc fin).joinRise := by
  classical
  obtain ⟨dSC, -⟩ := newlySlashed_disjoint h
  have dis : Disjoint ((joinedKeys pulled counted).filter fun v =>
        isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true)
      ((activeNewlySlashed config pulled anc fin counted split).filter fun v =>
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

/-- Late activations, weight 3 for V keys and for new keys, and for the newly slashed keys.

A newly slashed key outside the tight window pays its stake three times and its rise.

It also pays the reward of what its finalized balance exceeds them by, rounded up.

In the tight window the charge for late activations is zero, including over newly slashed keys.
-/
theorem budget_late (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ v ∈ (countedInactiveVoters counted V) with
          (pinTerms config pulled anc fin).lateB v.toNat = true,
        pulledBalance pulled v) +
      (∑ v ∈ (joinedKeys pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat = true,
        (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).lateB v.toNat = true),
        (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) ≤
      (pinTerms config pulled anc fin).late := by
  classical
  obtain ⟨dSC, dSV⟩ := newlySlashed_disjoint h
  rw [Internal.late_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · rw [ite_eq_left tight]
    have baseTight : 3 * (∑ v ∈ (countedInactiveVoters counted V) with
        (pinTerms config pulled anc fin).lateB v.toNat = true, pulledBalance pulled v) +
        (∑ v ∈ (joinedKeys pulled counted) with (pinTerms config pulled anc fin).lateB v.toNat =
          true,
          (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤ 0 := by
      -- Tight: no key of `V` inactive at C and no joined key is late.
      have fin_le := UInt64.le_iff_toNat_le.mp h.finalized
      have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
      have bound := (Internal.tight_iff config pulled anc fin).mp tight
      have near := h.near
      have lowerEpoch : (getCurrentEpoch pulled).toNat + 1 ≤
          anc.finalizedCheckpoint.epoch.toNat + preset.MAX_SEED_LOOKAHEAD.toNat := by omega
      have none : ∀ v ∈ (countedInactiveVoters counted V) ∪ (joinedKeys pulled counted),
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
      have zeroA : ∑ v ∈ (countedInactiveVoters counted V) with (pinTerms config pulled anc
          fin).lateB
          v.toNat
        = true,
          pulledBalance pulled v = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have := none v (Finset.mem_union_left _ (Finset.mem_filter.mp hv).1)
        simp [(Finset.mem_filter.mp hv).2] at this
      have zeroB : ∑ v ∈ (joinedKeys pulled counted) with
          (pinTerms config pulled anc fin).lateB v.toNat = true,
            (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have := none v (Finset.mem_union_right _ (Finset.mem_filter.mp hv).1)
        simp [(Finset.mem_filter.mp hv).2] at this
      rw [zeroA, zeroB]
    have empty : ∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).lateB v.toNat = true),
        (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
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
    set A := (countedInactiveVoters counted V).filter fun v => (pinTerms config pulled anc
        fin).lateB
        v.toNat
      = true
      with hA
    set B := (joinedKeys pulled counted).filter
      fun v => (pinTerms config pulled anc fin).lateB v.toNat = true with hB
    set C := (activeNewlySlashed config pulled anc fin counted split).filter fun v =>
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
    have growA : 3 * ∑ v ∈ A, pulledBalance pulled v ≤
        ∑ v ∈ A, (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun v _ =>
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    have growB : ∑ v ∈ B, (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise
        v.toNat)
      ≤
        ∑ v ∈ B, (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) :=
      Finset.sum_le_sum fun v _ => Nat.le_add_right _ _
    have joined : ∑ v ∈ A, (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise
        v.toNat
      +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) +
        ∑ v ∈ B, (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)) +
        ∑ v ∈ C, (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
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

/-- Joined and newly slashed keys in R's registry not yet eligible at R: stake and rise.

A newly slashed key also pays the reward of its finalized balance's excess over them, rounded up.

In the tight window the pending-key charge is zero, and the guard excludes every newly slashed key.
-/
theorem budget_pendingR (h : Setting config checks g split fin pulled anc counted V) :
    (∑ v ∈ (joinedKeys pulled counted) with (pinTerms config pulled anc fin).pendingRB v.toNat =
      true,
      (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat)) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).pendingRB v.toNat = true),
        (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) ≤
      (pinTerms config pulled anc fin).pendingR := by
  classical
  obtain ⟨dSC, -⟩ := newlySlashed_disjoint h
  rw [Internal.pendingR_eq]
  by_cases tight : (pinTerms config pulled anc fin).tight = true
  · rw [ite_eq_left tight]
    have baseTight : (∑ v ∈ (joinedKeys pulled counted) with
        (pinTerms config pulled anc fin).pendingRB v.toNat = true,
        (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat)) ≤ 0 := by
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
    have empty : ∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).pendingRB v.toNat = true),
        (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
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
    set K := (joinedKeys pulled counted).filter
      fun v => (pinTerms config pulled anc fin).pendingRB v.toNat = true with hK
    set C := (activeNewlySlashed config pulled anc fin counted split).filter fun v =>
      (pinTerms config pulled anc fin).tight = false ∧
        (pinTerms config pulled anc fin).pendingRB v.toNat = true with hC
    have apart : Disjoint K C :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
          (Finset.disjoint_of_subset_left Finset.subset_union_right
            (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) dSC)))
    have grow : ∑ v ∈ K, (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat) ≤
        ∑ v ∈ K, (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
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

Here withdrawable means by the finalized epoch. -/
theorem activeNewlySlashed_unwithdrawn (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} {s w u : Validator} (foundS : split.validators.data[i]? = some s)
    (foundP : pulled.validators.data[i]? = some w)
    (foundC : counted.validators.data[i]? = some u)
    -- Both records are unslashed before C's slashing, and the key is unslashed at R.
    (cleanS : s.slashed = false) (slashedC : u.slashed = true) (cleanP : w.slashed = false)
    (settled : w.withdrawableEpoch.toNat ≤ anc.finalizedCheckpoint.epoch.toNat) : False := by
  obtain ⟨rf⟩ := h.toFin
  obtain ⟨rs⟩ := h.fromFin
  obtain ⟨tailR⟩ := h.toPulled
  obtain ⟨tailC⟩ := h.toCounted
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  obtain ⟨uAssigned, -⟩ := tailC.newly_slashed_withdrawableEpoch h.caps (Internal.Setting.delay h) i
      s u foundS foundC cleanS slashedC
  -- If the split has no exit for the key, C's slashing assigns one.
  --
  -- A run never charges an exit twice.
  by_cases unset : s.exitEpoch = FAR_FUTURE_EPOCH
  · obtain ⟨c, member, index, -⟩ := tailC.departure_charge_of_assigned i s u foundS foundC unset
      uAssigned
    exact Internal.no_charge_of_settled h tailC (Array.getElem?_eq_some_iff.mp foundS).1 foundP
      settled c
      member index
  -- Otherwise R's withdrawable epoch is the split's, so the key is retired at the split.
  --
  -- A retired key stays unslashed on C's run.
  · have kept := Internal.kept_run (rf.append rs) h.genesis h.fulu tailR h.early
    obtain ⟨-, moved⟩ := kept.withdrawable i s w foundS foundP unset
    have same := congrArg UInt64.toNat (moved.resolve_left (by simp [cleanP]))
    have ordered := UInt64.le_iff_toNat_le.mp
      ((Run.invariant (Genesis.invariant h.genesis) (rf.append rs)).exitsOrdered s
        (Array.mem_of_getElem? foundS))
    have exited : s.exitEpoch.toNat ≤ (getCurrentEpoch split).toNat := by omega
    have withdrawn : s.withdrawableEpoch.toNat ≤ (getCurrentEpoch split).toNat := by omega
    have clean := (Run.retired_validator tailC h.caps i s u
      foundS foundC (UInt64.le_iff_toNat_le.mpr exited) cleanS
      (UInt64.le_iff_toNat_le.mpr withdrawn)).1
    simp [slashedC] at clean

/-- For a newly slashed key active at C, the remaining cases are active, late or pending at R.

This excludes keys charged for a slashing on R's branch or a slashable exit. -/
private theorem activeNewlySlashed_class
    (h : Setting config checks g split fin pulled anc counted V)
    {v : ValidatorIndex} (member : v ∈ activeNewlySlashed config pulled anc fin counted split) :
    isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true ∨
      -- The active case includes R's next epoch.
      isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true ∨
      -- Outside the tight window the key can instead be late or pending.
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
  obtain ⟨finSplit, called, later, near, -, -, succNat, -⟩ := Internal.setting_epochs
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
    -- Outside the tight window, take an exit by R's next epoch due to slashing.
    --
    -- It counts in the branch slashing charge.
    --
    -- An unslashed key with such an exit counts in the slashable-exit charge instead.
    --
    -- Or the key withdraws by the finalized epoch, which C's slashing excludes.
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
        exact activeNewlySlashed_unwithdrawn h foundS found foundU cleanS slashedU cleanW settled
    -- A key that exits after R's next epoch activates after it.
    --
    -- Its eligibility is then late or pending.
    · -- The key activates after R's next epoch.
      have afterA : (getCurrentEpoch pulled).toNat + 1 < w.activationEpoch.toNat := by
        by_contra early
        apply notR1
        rw [succNat]
        exact ⟨by omega, by omega⟩
      exact Internal.late_or_pending h found bound afterA

/-- Charged newly slashed keys are current, upcoming-only, late or pending, and pay that entry. -/
theorem newlySlashed_active_split (h : Setting config checks g split fin pulled anc counted V) :
    ∑ v ∈ activeNewlySlashed config pulled anc fin counted split,
        ((pinTerms config pulled anc fin).rise v.toNat +
          -- Outside the tight window, a late or pending newly slashed key pays its stake and rise.
          --
          -- It pays them in this entry.
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
      -- A key is active at R, or active at the next epoch only.
      --
      -- Otherwise its activation is past the delay, or its eligibility is past the epoch.
      --
      -- In the tight window the last two cases are empty.
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        (pinTerms config pulled anc fin).current v.toNat = true,
          (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        (isActiveAt pulled (getCurrentEpoch pulled) v.toNat = false ∧
          isActiveAt pulled (getCurrentEpoch pulled + 1) v.toNat = true),
        (pinTerms config pulled anc fin).rise v.toNat) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).lateB v.toNat = true),
        (3 * pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) +
      (∑ v ∈ (activeNewlySlashed config pulled anc fin counted split) with
        ((pinTerms config pulled anc fin).tight = false ∧
          (pinTerms config pulled anc fin).pendingRB v.toNat = true),
        (pulledBalance pulled v + (pinTerms config pulled anc fin).rise v.toNat +
          3 * ((balanceAt fin v.toNat - balanceAt pulled v.toNat -
            (pinTerms config pulled anc fin).rise v.toNat +
            ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat))) := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v member => ?_
  have cls := activeNewlySlashed_class h member
  have current : (pinTerms config pulled anc fin).current v.toNat =
      isActiveAt pulled (getCurrentEpoch pulled) v.toNat := rfl
  rw [current]
  unfold pulledBalance
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

/-- The whistleblower reward of newly slashed keys R slashes, at R's effective balance plus rise.

Each key reads the quotient of its balance and rise, and the quotient of an increment rounded up.

The reserve for R's slashed keys covers this reward. -/
def newlySlashedWhistleReward (config : Config)
    (pulled anc fin counted split : BeaconState preset fork) : ℕ :=
  ∑ v ∈ (newlySlashed pulled counted split).filter
      (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
    (max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
        (balanceAt fin v.toNat) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- A key off the kept arm rises by its whole headroom to the largest cap.

Within the withdrawal delay, the kept arm fails only if the gain is too large for the balance bound.

So the rise bound uses the largest cap. -/
theorem rise_of_notKept (h : Setting config checks g split fin pulled anc counted V) (i : ℕ)
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
/-- A key that a run from the finalized state creates has a first state on the run. -/
theorem created_first_state (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    {v : ValidatorIndex} (created : fin.validators.data.size ≤ v.toNat)
    (inside : v.toNat < e.validators.data.size) :
    ∃ (c : BeaconState preset fork) (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
      (fromC : Run config checks ⟨fork, c⟩ ⟨fork, e⟩), toC.append fromC = run ∧
      v.toNat < c.validators.data.size ∧
      -- At that state the key is unslashed.
      (∀ u, c.validators.data[v.toNat]? = some u → u.slashed = false) ∧
      -- Before it the key is absent from the path, so its effective balance is zero.
      (∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p v.toNat = 0) ∧
      -- At that state its effective balance is within the floor of its balance.
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
      -- A state of the run that lacks the key is no later than the first state.
      ∀ (d : BeaconState preset fork) (toD : Run config checks ⟨fork, fin⟩ ⟨fork, d⟩)
        (restD : Run config checks ⟨fork, d⟩ ⟨fork, e⟩), toD.append restD = run →
        ¬ v.toNat < d.validators.data.size →
        (getCurrentEpoch d).toNat ≤ (getCurrentEpoch c).toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  -- A step that appends a key leaves it unassigned.
  --
  -- So the first state is where the key is created.
  --
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
    (toFin.append (pre0.snoc step)) h.genesis h.caps h.aligned
    h.early finite
  obtain ⟨⟨b, foundB, le⟩, -, clean⟩ := unassigned v.toNat vn foundN far
  -- the key is absent at each state of the path before the first state
  have before : ∀ p ∈ (pre0.snoc step).balancePath, p = ⟨fork, ns⟩ ∨ effectiveAt p v.toNat = 0 := by
    intro p member
    obtain ⟨r1, r2, cutP⟩ := Internal.balancePath_endpoint (pre0.snoc step)
      (Run.nil : Run config checks ⟨fork, ns⟩ ⟨fork, ns⟩) (Nat.le_refl _) member
    rcases Run.prefix_snoc r1 r2 pre0 step cutP with ⟨same, -⟩ | ⟨r', -⟩
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
theorem effective_le_foldl_max {x y : ForkedBeaconState preset}
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
theorem slashW_add_downwardBand_le
    (h : Setting config checks g split fin pulled anc counted V) (i : ℕ) :
    Internal.slashW (pinTerms config pulled anc fin) i + preset.downwardBand ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  unfold Internal.slashW; split <;> first | exact h.facts.slashBand | simpa using
    (Internal.PinPresetFacts.below h.facts).le

/-- A replay of a run that ends by R's epoch, read at R's epoch.

The horizon of the replay does not change the events of such a run. -/
theorem replay_at_pulled (pulled : BeaconState preset fork)
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
theorem high_eq (config : Config) (pulled anc fin : BeaconState preset fork)
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

The key is not withdrawable by R's next epoch, so the extra leak counts in full. -/
theorem leakAt_foldl_le (config : Config) (pulled anc fin : BeaconState preset fork)
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

The key is slashed on R's branch. -/
private theorem cut_balance_core (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex)
    -- The slash and the band fit one increment.
    (hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (insideC : v.toNat < c.validators.data.size)
    -- This is the floor of the key's balance from each state after the anchor.
    (floor : ∀ {zs : BeaconState preset fork} (_ : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) {evs : List (BalanceEvent preset)},
      r2.balanceEvents (getCurrentEpoch pulled).toNat = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + Internal.slashW (pinTerms config pulled anc fin)
            v.toNat)
    -- This bounds the anchor by its balance when the anchor is no earlier than the split's epoch.
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
    -- The same effective-balance ceiling holds before the anchor.
    (pathEnv : ∀ p ∈ toC.balancePath, p ≠ ⟨fork, c⟩ → effectiveAt p v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat)
    (notWithdrawn : (pinTerms config pulled anc fin).withdrawnRB v.toNat = false) :
    balanceAt split v.toNat ≤ balanceAt pulled v.toNat +
      (pinTerms config pulled anc fin).rise v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
      -- With a sync debit the rounding of `H` adds a second increment.
      --
      -- Without a sync debit, the effective balance stays within the reserve's ceiling.
      --
      -- It then adds no leak.
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
    Internal.cap_le_cap_of_run h.caps toPulled v.toNat
  -- the largest effective balance on R's run
  obtain ⟨M, hM⟩ : ∃ M, M = ((fromFin.append tail).balancePath.map
      fun z => effectiveAt z v.toNat).foldl max 0 := ⟨_, rfl⟩
  obtain ⟨Df, hDf⟩ : ∃ Df, Df = (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat :=
    ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = Internal.slashW (pinTerms config pulled anc fin) v.toNat := ⟨_, rfl⟩
  -- The floors give a ceiling on the key's balance along the run.
  --
  -- That ceiling bounds the key's effective balance at the split, up to a downward band.
  --
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
      (fun pre post cut => hM ▸ Internal.effective_le_foldl_max (fromFin.append tail) v.toNat pre
          post cut)
      toC fromC cutC insideC
      (fun {_} r1 r2 _ {evs} ev => by
        have ev' := Internal.replay_at_pulled pulled r2 high endEpoch (UInt64.le_refl _) ev
        rw [hWdef]
        exact floor r1 r2 ev') z inFull
    rw [hBc, hDf]
    omega
  have capped : ∀ z ∈ fromC.balancePath, effectiveAt z v.toNat ≤ PinTerms.capAt z v.toNat := by
    intro z member
    obtain ⟨zs, rfl, ⟨r1⟩, -⟩ := Internal.balancePath_state fromC member
    exact Internal.effective_le_cap_at (toFin.append (toC.append r1)) h.genesis h.caps
      v.toNat
  have capCeil : ∀ z ∈ fromC.balancePath,
      PinTerms.capAt z v.toNat ≤ PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset)
        v.toNat := by
    intro z member
    obtain ⟨zs, rfl, -, ⟨r2⟩⟩ := Internal.balancePath_state fromC member
    exact Nat.le_trans (Internal.cap_le_cap_of_run h.caps r2 v.toNat) capSplit
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
      have capAtC := Internal.effective_le_cap_at (toFin.append toC) h.genesis h.caps
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
    exact Internal.high_eq config pulled anc fin electra v.toNat
  obtain ⟨ind, hind⟩ : ∃ ind, ind =
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat := ⟨_, rfl⟩
  have induced : Df * (pinTerms config pulled anc fin).leakAt M v.toNat ≤
      Df * (pinTerms config pulled anc fin).leak v.toNat + ind := by
    rw [hind, ← hdf, hM]
    exact Internal.leakAt_foldl_le config pulled anc fin (fromFin.append tail) v.toNat notWithdrawn
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
    exact Internal.slashW_add_downwardBand_le h v.toNat
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
          have ev' := Internal.replay_at_pulled pulled after high endEpoch (UInt64.le_refl _) ev
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
  · have headroom := Internal.rise_of_notKept h v.toNat kept
    have capped : balanceAt split v.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      Internal.effectiveAt_le_capMax (toFin.append fromFin) h.genesis h.caps v.toNat
    have cappedR : balanceAt pulled v.toNat ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
      Internal.effectiveAt_le_capMax (toFin.append (fromFin.append tail)) h.genesis h.caps
        v.toNat
    omega

/-- A key that the shared run slashes is bounded by its finalized balance or by R's balance.

The reward for slashing a key in the shared segment divides this bound by the reward quotient.

The debits cover rounding when this bound is summed over the keys slashed in that segment. -/
private theorem cut_balance_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (member : v ∈ Internal.cutKeys config pulled anc fin split) :
    balanceAt split v.toNat ≤ max (balanceAt fin v.toNat)
      -- The bound by R's balance reads its rise, one increment and the debits and induced leak.
      (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        -- A second increment pays the rounding of the balance when it has a sync debit.
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
  have hWdb := Internal.slashW_add_downwardBand_le h v.toNat
  have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    have := h.facts.bandLow
    have := h.facts.incrementSize
    omega
  -- A queued partial paid before the finalized state leaves the balance at the finalized one.
  --
  -- Otherwise the rise bound's leak allowance covers penalties and sync debits on R's tail.
  by_cases inFin : v.toNat < fin.validators.data.size
  -- The balance at the split is the key's effective balance at the epoch start.
  --
  -- That holds up to the downward band.
  · by_cases flat : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch fin).toNat
    · have sameE : getCurrentEpoch split = getCurrentEpoch fin :=
        UInt64.toNat_inj.mp (by omega)
      exact le_max_of_le_left
        (run_same_epoch_effective fromFin sameE v.toNat inFin).le
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
    have first := Internal.created_first_state h fromFin (v := v) (by omega) (by
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

Thus a cutoff before the start epoch includes no epoch rewards from the run. -/
private theorem balanceEvents_late {f : Fork} {b : BeaconState preset f}
    {y : ForkedBeaconState preset} (tail : Run config checks ⟨f, b⟩ y)
    (same : getCurrentEpoch y.state = getCurrentEpoch b)
    {high : ℕ} (late : high + 1 < (getCurrentEpoch b).toNat) :
    tail.balanceEvents high = .ok [] := by
  refine Run.induction_of_same_epoch (fun _ r => r.balanceEvents high = .ok []) rfl ?_ ?_ tail
    same
  · intro _ s _ _ _ _ _ pre prior
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
/-- The whistleblower credits of the shared run's last epoch fit the keys that it slashes. -/
private theorem cut_whistle (h : Setting config checks g split fin pulled anc counted V)
    {b : BeaconState preset fork} (toB : Run config checks g ⟨fork, b⟩)
    -- This run goes from `b` to the split, inside the split's epoch.
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    -- A whistleblower credit lands in the proposer's block, so a key of any class can receive it.
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b) (high : ℕ) (keys : Finset ℕ) :
    ∑ i ∈ keys, Internal.whistC pre high i ≤
      -- R's call reads each key slashed along `pre` as slashed.
      --
      -- That holds since its withdrawable epoch is a slashing vector away.
      --
      -- The sum is over keys that are not newly slashed, because they are slashed at the split.
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
  · rw [balanceEvents_late pre sameEpoch late] at replayed
    cases replayed
    simp
  have endEpoch : (getCurrentEpoch split).toNat ≤ high + 1 := by rw [sameEpoch]; omega
  let P : ℕ → Prop := fun j => ((b.validators.data[j]?).map (·.slashed)).getD false = false ∧
    ((split.validators.data[j]?).map (·.slashed)).getD false = true ∧
    (pinTerms config pulled anc fin).slashedRB j = true
  let quotient := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  -- Each key slashed along `pre` pays the quotient of its effective balance at the slashing.
  --
  -- That balance is the one at the split.
  --
  -- It changes only at an epoch update, and `pre` is in one epoch.
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
    have withdrawable := ((rest.append toPulled).newly_slashed_withdrawableEpoch h.caps
        (Internal.Setting.delay h) j u wP foundA foundP clean markedP).2
    have p : P j := by
      refine ⟨?_, by simp [foundS, markedS], ?_⟩
      · cases foundB : b.validators.data[j]? with
        | none => rfl
        | some v =>
          simp [Internal.unslashed_of_run before foundB (fun z read => by simp_all)]
      · exact Internal.slashedRB_of_withdrawable config pulled anc fin foundP markedP (by omega)
    have sameEpochA : getCurrentEpoch split = getCurrentEpoch a.state :=
      UInt64.toNat_inj.mp (by omega)
    have kept := rest.effectiveKept_of_same_epoch sameEpochA j
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
/-- R1 from the count of its rounding bands. -/
private theorem budget_branchR_of (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {events eventsF eventsC eventsP : List (BalanceEvent preset)}
    -- This hypothesis bounds the number of rounding bands drawn from the branch budget.
    --
    -- Newly slashed seat holders weigh one in it, and take seat slots that no class claims.
    (bands : 3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ stayingKeys pulled counted V, Internal.bandR (eventsF ++ events) v.toNat) +
        3 * (∑ v ∈ previousOnlyKeys counted V, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ joinedKeys pulled counted, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split,
          if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
            (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) +
        (∑ v ∈ chargedNewlySlashed pulled counted split tailC,
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
        (∑ v ∈ (stayingKeys pulled counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * (∑ v ∈ (previousOnlyKeys counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        (∑ v ∈ (joinedKeys pulled counted),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * newlySlashedWhistleReward config pulled anc fin counted split +
        (∑ v ∈ newlySlashed pulled counted split, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split,
          if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
            (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) +
        (∑ v ∈ chargedNewlySlashed pulled counted split tailC,
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
  -- The branch's slashed keys cover the slash charges, with each class counted at its own weight.
  --
  -- The sync part of the proposer credit fits the proposer credit of each epoch.
  --
  -- The bound `W` covers both the flag gain and the rounding unit of each slashed key.
  classical
  unfold newlySlashedWhistleReward
  obtain ⟨Wh, W, hW, gainW, floorW⟩ := Internal.branchR_split config pulled anc fin
  obtain ⟨d45, d46, d56, -, -, -⟩ := Internal.classes_disjoint h
  obtain ⟨dSC, -⟩ := newlySlashed_disjoint h
  have slashes := Internal.weighted_le (A := stayingKeys pulled counted V) (B := previousOnlyKeys
      counted
    V)
    (C := joinedKeys pulled counted) (fun v => Internal.slashR (pinTerms config pulled anc fin)
      v.toNat) d45 d46
    d56
  -- A cut key is slashed at the split, so it is in no class and is not newly slashed.
  have dCut : Disjoint (stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
      pulled
    counted ∪
      newlySlashed pulled counted split) (Internal.cutKeys config pulled anc fin split) :=
    (Internal.cut_disjoint h).symm.mono_left fun v member => by
      simp only [Finset.mem_union] at member ⊢
      tauto
  -- Each cut key is read as slashed, so its slash charge is an increment.
  have cutRB : (Internal.cutKeys config pulled anc fin split).filter
      (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true) =
        Internal.cutKeys config pulled anc fin split :=
    Finset.filter_true_of_mem fun v cut => (Finset.mem_filter.mp cut).2.2.1
  -- A newly slashed key that R slashes takes an increment of `branchR`'s slashed keys.
  --
  -- A key of the classes takes one too, and the two sets are disjoint.
  have slashBound := Internal.slashR_le config pulled anc fin
    (stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted ∪
        newlySlashed
      pulled counted split ∪
      Internal.cutKeys config pulled anc fin split)
  rw [Finset.sum_union dCut, Finset.sum_union dSC] at slashBound
  have scFloor := floorW (newlySlashed pulled counted split ∪ Internal.cutKeys config pulled anc fin
    split)
  rw [Finset.filter_union, cutRB, Finset.sum_union (Finset.disjoint_of_subset_left
    (Finset.filter_subset _ _) (Finset.disjoint_union_left.mp dCut).2)] at scFloor
  have scReward : ∑ v ∈ (newlySlashed pulled counted split).filter
        (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
      (max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
          (balanceAt fin v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (∑ v ∈ (newlySlashed pulled counted split).filter
          (fun v => (pinTerms config pulled anc fin).slashedRB v.toNat = true),
        max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
          (balanceAt fin v.toNat) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        ∑ v ∈ newlySlashed pulled counted split, Internal.slashR (pinTerms config pulled anc fin)
          v.toNat := by
    have each : ∀ v ∈ (newlySlashed pulled counted split).filter
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

/-- R's credits to voters since the split count at weight three. -/
theorem budget_branchR (h : Setting config checks g split fin pulled anc counted V)
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
    -- The surplus of the slash charge pays for the gains induced by the slashing.
    3 * ((pinTerms config pulled anc fin).slashedR *
        (2 * (pinTerms config pulled anc fin).depthFin *
          (pinTerms config pulled anc fin).flagRate)) +
      3 * ((pinTerms config pulled anc fin).slashedR *
        (pinTerms config pulled anc fin).slashLeak) +
      -- The branch budget also holds a rounding unit for each key slashed on R's branch.
      3 * ((pinTerms config pulled anc fin).unitGain * (pinTerms config pulled anc fin).slashedR) +
      3 * (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        -- The reserve accounts for sync committee events separately from R's other credits.
        3 * ((pinTerms config pulled anc fin).depth *
          (pinTerms config pulled anc fin).syncProposer) +
        -- The slashing of a key on R's branch is charged here for staying and previous-only keys.
        --
        -- So is a sync debit on R's branch that the balance rise omits.
        --
        -- The staying keys weigh one, and the previous-only keys weigh three.
        (∑ v ∈ (stayingKeys pulled counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        3 * (∑ v ∈ (previousOnlyKeys counted V),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        -- A previous-only key with a whistleblower credit on `pre` is read at the credits of `pre`.
        3 * (∑ v ∈ (previousOnlyKeys counted V), Internal.whistC pre highC v.toNat) +
        3 * (∑ v ∈ chargedNewlySlashed pulled counted split tailC, Internal.whistC pre highC
            v.toNat)
          +
        (∑ v ∈ (joinedKeys pulled counted),
          (Internal.slashR (pinTerms config pulled anc fin) v.toNat + Internal.bandR (eventsF ++
            events) v.toNat)) +
        -- The newly slashed keys that R slashes after the split draw on the same budget.
        --
        -- They weigh three in it.
        --
        -- The reserve includes their whistleblower reward on C's branch.
        3 * newlySlashedWhistleReward config pulled anc fin counted split +
        -- Newly slashed seat holders use unclaimed seat slots in that budget at weight one.
        (∑ v ∈ newlySlashed pulled counted split, Internal.bandR (eventsF ++ events) v.toNat) +
        (∑ v ∈ newlySlashed pulled counted split,
          if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
            (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) +
        (∑ v ∈ chargedNewlySlashed pulled counted split tailC,
          if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
            Internal.syncCr eventsP v.toNat then
            preset.upwardBand else 0) ≤
      (pinTerms config pulled anc fin).branchR +
        -- The cut keys' sync debits and induced leak, paid by `budget_sync` and `budget_syncLeak`.
        3 * (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat)) := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  set q := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hq
  set inc := preset.EFFECTIVE_BALANCE_INCREMENT.toNat with hinc
  -- The bands of `budget_branchR_of` are the seats' bands, within the bound of `roundedKeys`.
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
  have of := budget_branchR_of h tailC highC pre (seats.trans (Nat.mul_le_mul_left 3
    (Nat.mul_le_mul_left _ ?bandsLe)))
  case bandsLe => omega
  -- One `cut_whistle` reads the credits of `pre` to previous-only and charged newly slashed keys.
  obtain ⟨dSC, -⟩ := newlySlashed_disjoint h
  have apart : Disjoint (previousOnlyKeys counted V) (chargedNewlySlashed pulled counted split
      tailC) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _)
      (Finset.disjoint_of_subset_left (fun v member => Finset.mem_union.mpr
        (.inl (Finset.mem_union.mpr (.inr member)))) dSC)
  have whistle := cut_whistle h toB pre sameEpoch highC
    ((previousOnlyKeys counted V ∪ chargedNewlySlashed pulled counted split tailC).image
        UInt64.toNat)
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
          h.caps (Internal.Setting.delay h) finite v.toNat
          (fun u read => by simp [found] at read) (by simp [found, foundN, slashedN])
        simp [found] at recorded
    obtain ⟨wP, foundP, slashedP⟩ :=
      (after.append toPulled).slashedPersistence v.toNat w foundN slashedN
    have withdrawable := ((((Run.nil.snoc step).append after).append toPulled)
      |>.newly_slashed_withdrawableEpoch h.caps
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
theorem syncF_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    Internal.syncF events v = (events.map (Internal.syncCredit v)).sum +
      (events.map (Internal.syncDebit v)).sum := by
  unfold Internal.syncF
  rw [← Internal.sum_syncDebit_eq events v]
  exact congrArg (· + ((events.map (Internal.syncDebit v)).sum)) (Internal.sum_map_sync events
    (Internal.keyCredit v)).symm

/-- The sync movement of keys on a run within a call's reach is within an envelope.

The envelope is the seats' one, read at the pulled state's total. -/
private theorem syncF_run_le (h : Setting config checks g split fin pulled anc counted V)
    (pulledTotal : Gwei) (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (sameEpoch : getCurrentEpoch split = getCurrentEpoch b)
    -- This ties `pre` to the run from the finalized state.
    --
    -- So each step of `pre` has a guarded total.
    (shape : (∃ fromB : Run config checks ⟨fork, fin⟩ ⟨fork, b⟩, fromFin = fromB.append pre) ∨
      ∃ toFinB : Run config checks ⟨fork, b⟩ ⟨fork, fin⟩, pre = toFinB.append fromFin)
    -- The run is the tail from the split, after `pre`.
    --
    -- That run `pre` is the shared run from the start of the split's epoch.
    {e : BeaconState preset fork} (t : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (within : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (highE : ℕ) {evs : List (BalanceEvent preset)}
    (replayed : (pre.append t).balanceEvents highE = .ok evs) (keys : Finset ℕ) :
    ∑ i ∈ keys, Internal.syncF evs i ≤
      ((getCurrentEpoch e).toNat + 1 - (getCurrentEpoch split).toNat) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          Internal.syncSeatEnvelope preset pulledTotal.toNat := by
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitB := congrArg UInt64.toNat sameEpoch
  -- A step before the finalized state is in its epoch, where the active stake is the finalized one.
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
          exact (total_band_of_setting h (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩)
            h.early (by dsimp only; omega) okFin pulledOk).2
        · exact guarded step ((Run.contains_append _ _ _).mpr (.inl inFin)) T read
    · exact guarded step ((Run.contains_append _ _ _).mpr (.inr inTail)) T read
  have moves := (Internal.Run.syncDebits_le (pre.append t) h.fulu h.early highE replayed
    pulledTotal.toNat band keys).2.1
  refine (Finset.sum_le_sum fun i _ => (Internal.syncF_eq evs i).le).trans (moves.trans (le_of_eq
      ?_))
  dsimp only
  rw [sameEpoch]

/-- The sync budget includes the proposer's share at R's total stake.

It is paid for each seat in each slot of an epoch. -/
theorem syncProposer_eq (config : Config) (pulled anc fin : BeaconState preset fork) :
    (pinTerms config pulled anc fin).syncProposer =
      preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
        (PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat *
          PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat)) := rfl

/-- The reserve uses R's total active balance when the read succeeds. -/
theorem getD_total_eq {pulledTotal : Gwei}
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    ((getTotalActiveBalance pulled).toOption.getD 0).toNat = pulledTotal.toNat := by
  rw [pulledOk]
  rfl

/-- The steps of a run from the split keep their total within the band of R's total. -/
theorem step_band_of_tail (h : Setting config checks g split fin pulled anc counted V)
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
theorem pin_epochs (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) :
    ((getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat) +
        ((getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat) =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  simp only at finSplit
  omega

/-- The sync seats, in the third window: the base bound with the shared segment's K debits. -/
theorem budget_sync (h : Setting config checks g split fin pulled anc counted V)
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
        (∑ v ∈ (stayingKeys pulled counted V), Internal.syncD eventsF v.toNat) +
        (∑ v ∈ (stayingKeys pulled counted V), (Internal.syncF events v.toNat + Internal.syncF
          eventsC v.toNat)) +
        -- A previous-only key weighs three.
        (∑ v ∈ (previousOnlyKeys counted V), (Internal.syncD eventsF v.toNat + Internal.syncCr
            eventsP
          v.toNat)) +
        (∑ v ∈ (previousOnlyKeys counted V), (Internal.syncF events v.toNat + Internal.syncF eventsC
          v.toNat)) +
        -- Keys slashed at the split and still counted as slashed by R use the same weight.
        --
        -- Their rewards round up, and the debits cover the rounding.
        (∑ v ∈ Internal.cutKeys config pulled anc fin split,
          (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat))) +
      (∑ v ∈ (joinedKeys pulled counted), Internal.syncD eventsF v.toNat) +
      (∑ v ∈ (joinedKeys pulled counted), (Internal.syncF events v.toNat + Internal.syncF eventsC
        v.toNat)) +
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split, Internal.syncCr eventsC
        v.toNat) +
      Internal.wShare preset fork
        (∑ v ∈ newlySlashed pulled counted split, (Internal.syncD eventsF v.toNat + Internal.syncD
          events v.toNat)) +
      -- The bound also holds the shares of created slashed keys.
      Internal.wShare preset fork (∑ v ∈ createdSlashed counted split, Internal.syncCr eventsC
          v.toNat)
        +
      -- It holds those of the shared segment's exited newly slashed keys too.
      Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split with
        (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.syncCr eventsF
          v.toNat) +
      2 * ∑ v ∈ activeNewlySlashed config pulled anc fin counted split, Internal.syncD eventsF
          v.toNat +
      -- The sync credits of `pre` ride with R's tail.
      --
      -- That holds since `pre` and the tail are one run in the epoch.
      --
      -- A newly slashed key weighs once here, for the split-epoch charge case.
      (∑ v ∈ newlySlashed pulled counted split, Internal.syncCr eventsP v.toNat) ≤
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
  -- The shared segment's debits are one weighted sum over the disjoint classes.
  --
  -- the five sets are pairwise disjoint
  obtain ⟨d45, d46, d56, d1, d15, d16⟩ := Internal.classes_disjoint h
  obtain ⟨dS, dVS⟩ := newlySlashed_disjoint h
  obtain ⟨dCK, dCV⟩ := createdSlashed_disjoint h
  have d2 : Disjoint (V ∪ stayingKeys pulled counted V) (previousOnlyKeys counted V) :=
    Finset.disjoint_union_left.mpr ⟨d15, d45⟩
  have d3 : Disjoint (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V) (joinedKeys
      pulled
    counted) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨d16, d46⟩, d56⟩
  have d4 : Disjoint (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
      pulled
    counted)
      (newlySlashed pulled counted split) := by
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
  have dCS : Disjoint (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
      pulled
    counted ∪
      newlySlashed pulled counted split) (createdSlashed counted split) := by
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
      U = V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled counted
          ∪
        newlySlashed pulled counted split ∪
        createdSlashed counted split :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ValidatorIndex → ℕ, ∀ v, g v =
      Internal.syncF events v.toNat + Internal.syncF eventsC v.toNat := ⟨_, fun _ => rfl⟩
  have sumU : ∑ v ∈ U, g v = ∑ v ∈ V, g v + ∑ v ∈ stayingKeys pulled counted V, g v +
      ∑ v ∈ previousOnlyKeys counted V, g v + ∑ v ∈ joinedKeys pulled counted, g v +
      ∑ v ∈ newlySlashed pulled counted split, g v + ∑ v ∈ createdSlashed counted split, g v := by
    rw [hU, Finset.sum_union dCS, Finset.sum_union d4, Finset.sum_union d3, Finset.sum_union d2,
      Finset.sum_union d1]
  -- the newly slashed keys exited by the finalized epoch hold the shared credits, the rest debits
  set EK := (newlySlashed pulled counted split).filter
    (fun v => (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) with hEK
  set NF := (newlySlashed pulled counted split).filter
    (fun v => ¬ (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true) with hNF
  have dKN : Disjoint (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
      pulled
    counted) NF :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) d4
  have dKE : Disjoint (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
      pulled
    counted) EK :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) d4
  have dNE : Disjoint NF EK := Finset.disjoint_left.mpr fun v inN inE =>
    (Finset.mem_filter.mp inN).2 (Finset.mem_filter.mp inE).2
  have scSplit : ∑ v ∈ newlySlashed pulled counted split, Internal.syncD eventsF v.toNat =
      ∑ v ∈ EK, Internal.syncD eventsF v.toNat + ∑ v ∈ NF, Internal.syncD eventsF v.toNat :=
    (Finset.sum_filter_add_sum_filter_not _ _ fun v : ValidatorIndex => Internal.syncD eventsF
      v.toNat).symm
  have unionD : ∑ v ∈ V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
      pulled
    counted ∪ NF,
      Internal.syncD eventsF v.toNat = ∑ v ∈ V, Internal.syncD eventsF v.toNat +
        ∑ v ∈ stayingKeys pulled counted V, Internal.syncD eventsF v.toNat +
        ∑ v ∈ previousOnlyKeys counted V, Internal.syncD eventsF v.toNat + ∑ v ∈ joinedKeys pulled
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
  have class4 : ∑ v ∈ stayingKeys pulled counted V, (Internal.syncF events v.toNat + Internal.syncF
    eventsC v.toNat) ≤
      ∑ v ∈ stayingKeys pulled counted V, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have class5 : ∑ v ∈ previousOnlyKeys counted V, (Internal.syncF events v.toNat + Internal.syncF
      eventsC
    v.toNat) ≤
      ∑ v ∈ previousOnlyKeys counted V, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have class6 : ∑ v ∈ joinedKeys pulled counted, (Internal.syncF events v.toNat + Internal.syncF
    eventsC v.toNat) ≤
      ∑ v ∈ joinedKeys pulled counted, g v := Finset.sum_le_sum fun v _ => (hg v).ge
  have credits : Internal.wShare preset fork (∑ v ∈ newlySlashed pulled counted split,
    Internal.syncCr eventsC v.toNat) ≤
      ∑ v ∈ newlySlashed pulled counted split, Internal.syncF eventsC v.toNat :=
    (Internal.wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      unfold Internal.syncCr
      rw [Internal.syncF_eq]
      exact Nat.le_add_right _ _)
  have debits : Internal.wShare preset fork
      (∑ v ∈ newlySlashed pulled counted split, (Internal.syncD eventsF v.toNat + Internal.syncD
        events v.toNat)) ≤
      ∑ v ∈ newlySlashed pulled counted split, Internal.syncD eventsF v.toNat +
        ∑ v ∈ newlySlashed pulled counted split, Internal.syncF events v.toNat := by
    rw [← Finset.sum_add_distrib]
    exact (Internal.wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      unfold Internal.syncD
      rw [Internal.syncF_eq]
      omega)
  have creditsF : Internal.wShare preset fork (∑ v ∈ EK, Internal.syncCr eventsF v.toNat) ≤
      ∑ v ∈ EK, Internal.syncCr eventsF v.toNat := Internal.wShare_le h.facts _
  have creditsCS : Internal.wShare preset fork (∑ v ∈ createdSlashed counted split, Internal.syncCr
    eventsC v.toNat) ≤
      ∑ v ∈ createdSlashed counted split, g v :=
    (Internal.wShare_le h.facts _).trans (Finset.sum_le_sum fun v _ => by
      rw [hg]
      unfold Internal.syncCr
      rw [Internal.syncF_eq eventsC]
      omega)
  have shares : ∑ v ∈ newlySlashed pulled counted split, Internal.syncF eventsC v.toNat +
      ∑ v ∈ newlySlashed pulled counted split, Internal.syncF events v.toNat =
      ∑ v ∈ newlySlashed pulled counted split, g v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [hg]; omega
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ v ∈ V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪
    joinedKeys pulled counted ∪ NF,
      Internal.syncD eventsF v.toNat + ∑ v ∈ EK, (Internal.syncCr eventsF v.toNat + Internal.syncD
        eventsF v.toNat) :=
    ⟨_, rfl⟩
  -- the keys that the rise term of `budget_whistle_of` charges are among the newly slashed keys
  have rise3a : ∑ v ∈ activeNewlySlashed config pulled anc fin counted split, Internal.syncD eventsF
    v.toNat ≤
      ∑ v ∈ newlySlashed pulled counted split, Internal.syncD eventsF v.toNat :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- the terms of the statement beyond the old ones: the credits of `pre` and the cut keys' debits
  obtain ⟨extra, hextra⟩ : ∃ extra : ℕ, extra =
      3 * ∑ v ∈ previousOnlyKeys counted V, Internal.syncCr eventsP v.toNat +
      3 * ∑ v ∈ Internal.cutKeys config pulled anc fin split,
        (Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat) +
      ∑ v ∈ newlySlashed pulled counted split, Internal.syncCr eventsP v.toNat := ⟨_, rfl⟩
  have k5split : ∑ v ∈ previousOnlyKeys counted V, (Internal.syncD eventsF v.toNat + Internal.syncCr
    eventsP v.toNat) =
      ∑ v ∈ previousOnlyKeys counted V, Internal.syncD eventsF v.toNat + ∑ v ∈ previousOnlyKeys
          counted V,
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
  have cutD : Disjoint (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys
    pulled counted ∪ NF)
      (Internal.cutKeys config pulled anc fin split) := by
    refine Finset.disjoint_of_subset_left ?_ cutU
    rw [hU]
    intro v member
    simp only [Finset.mem_union] at member ⊢
    rcases member with inK | inNF
    · exact .inl (.inl inK)
    · exact .inl (.inr (Finset.mem_filter.mp inNF).1)
  obtain ⟨PD, hPD⟩ : ∃ PD, PD = (V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪
    joinedKeys pulled counted ∪
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
      (voters := V ∪ stayingKeys pulled counted V ∪ previousOnlyKeys counted V ∪ joinedKeys pulled
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
      obtain ⟨pre, -, -, -, -⟩ :=
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
  have totalEq := Internal.getD_total_eq pulledOk
  have seats : (pinTerms config pulled anc fin).syncSeats =
      3 * (((pinTerms config pulled anc fin).depth +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat) := rfl
  have proposer := Internal.syncProposer_eq config pulled anc fin
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
        ∑ v ∈ stayingKeys pulled counted V, Internal.syncF eventsP v.toNat +
        ∑ v ∈ previousOnlyKeys counted V, Internal.syncF eventsP v.toNat + ∑ v ∈ joinedKeys pulled
          counted, Internal.syncF eventsP v.toNat +
        ∑ v ∈ newlySlashed pulled counted split, Internal.syncF eventsP v.toNat +
        ∑ v ∈ createdSlashed counted split, Internal.syncF eventsP v.toNat := by
      rw [hU, Finset.sum_union dCS, Finset.sum_union d4, Finset.sum_union d3, Finset.sum_union d2,
        Finset.sum_union d1]
    have credit (L : Finset ValidatorIndex) :
        ∑ v ∈ L, Internal.syncCr eventsP v.toNat ≤ ∑ v ∈ L, Internal.syncF eventsP v.toNat :=
      Finset.sum_le_sum fun v _ => by
        unfold Internal.syncCr
        rw [Internal.syncF_eq]
        exact Nat.le_add_right _ _
    have k5 := credit (previousOnlyKeys counted V)
    have sc := credit (newlySlashed pulled counted split)
    have cutTail : ∑ v ∈ Internal.cutKeys config pulled anc fin split, Internal.syncD events v.toNat
      ≤
        ∑ v ∈ Internal.cutKeys config pulled anc fin split, g v :=
      Finset.sum_le_sum fun v _ => by
        rw [hg]
        unfold Internal.syncD
        rw [Internal.syncF_eq]
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

Both the seat rewards and the proposer's share are counted for each epoch of the window. -/
theorem syncCredits_le (h : Setting config checks g split fin pulled anc counted V)
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
    Finset.sum_le_sum fun i _ => (Nat.le_add_right _ _).trans (Internal.syncF_eq eventsC i).ge
  have totalEq := Internal.getD_total_eq pulledOk
  have proposer := Internal.syncProposer_eq config pulled anc fin
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
/-- A run from after the split bounds a key's balance and effective balance by its credits. -/
private theorem ceiling_run (h : Setting config checks g split fin pulled anc counted V)
    {c a : ForkedBeaconState preset} (toC : Run config checks ⟨fork, split⟩ c)
    (tail : Run config checks c a) (aEarly : a.fork < .glamsterdam) (aFork : a.fork ≤ fork)
    (i : ℕ) (inside : i < c.state.validators.data.size) (highC : ℕ)
    (endEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1)
    (near : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (capHigh : ℕ) (capLe : capHigh ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt c i ≤ capHigh) (B : ℕ)
    -- The balance at the start, up to the cap bound, is at most `B`.
    (startBal : min (actualBalanceAt c i) capHigh ≤ B)
    -- The cap bound is at least every cap along the run.
    (capCeil : ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh) :
    -- Then the balance up to the cap bound is at most `B`, the credits and the gains.
    --
    -- The gains are taken at the largest rate.
    (∀ z ∈ tail.balancePath, min (actualBalanceAt z i) capHigh ≤ B +
      ((getCurrentEpoch a.state).toNat - (getCurrentEpoch c.state).toNat) *
        (pinTerms config pulled anc fin).gainRateMax +
      (Internal.netScan i highC tail +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tail))) ∧
    -- The effective balance at the end is at most that of the start, or that bound.
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
theorem earlier_charge (h : Setting config checks g split fin pulled anc counted V)
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
    have same := run_same_epoch_effective rest0
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
    Internal.effective_le_cap_at (shared.append (fromFin.append toCC)) h.genesis h.caps i
  have capCC : PinTerms.capAt cc i ≤ PinTerms.capAt a i :=
    Internal.cap_le_cap_of_run h.caps tail2 i
  have alignedCap : PinTerms.capAt a i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    have := congrArg UInt64.toNat
      (withdrawalMaxEffectiveBalance_aligned (fork := a.fork) h.aligned old)
    simpa [PinTerms.capAt, foundA, UInt64.toNat_mod] using this
  have capCeil := Internal.capCeil_path tail2 h.caps (Nat.le_trans aFork cFork) i
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
      run_same_epoch_effective (Run.nil.snoc step1 : Run config checks s s')
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
        (Internal.capCeil_path pre1 h.caps (Nat.le_trans sFork cFork) i z member) capS)
    -- the run from the switch to the key's state, at its cap
    obtain ⟨-, ceil2⟩ := ceiling_run h (toCC.append (pre1.snoc step1)) post1 aEarly aFork i
      insideS' highC (by omega) near (PinTerms.capAt a i) capEnd alignedCap
      (Nat.le_trans (Internal.effective_le_cap_at (shared.append (fromFin.append
        (toCC.append (pre1.snoc step1)))) h.genesis h.caps i)
        (Internal.cap_le_cap_of_run h.caps post1 i))
      (effectiveAt cc i + Internal.stepCredit (fun _ => true) (fun _ => true) i step1) (by omega)
      (Internal.capCeil_path post1 h.caps (Nat.le_trans aFork
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

end Internal

end Terms

end PinDrift
end EthLib.Consensus.Models.Network

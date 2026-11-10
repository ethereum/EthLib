module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Models.Stake

/-!
# Proofs: total balances as stake of the consensus models

The stake of a validator is its effective balance, and a total balance is the stake of a set.

With aligned effective balances, each stake is a multiple of each divisor of the increment.

The total is never below one increment, which matters only for small totals.

Above one and a half increments of active stake, the test of justification compares stakes.

A supermajority link of the model follows Gasper Definition 4.5.

Gasper asks for more than two thirds of the stake; the beacon chain and the model accept two thirds.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Base.Fork}

/-- The stake of the validator at a position of the registry: its effective balance.

A position outside the registry weighs nothing. -/
def balanceAt (state : BeaconState preset fork) (index : ℕ) : ℕ :=
  (state.validators.data[index]?.map (·.effectiveBalance.toNat)).getD 0

/-- With aligned effective balances, each stake is a multiple of each divisor of the increment. -/
theorem dvd_balanceAt_of_aligned {state : BeaconState preset fork} {divisor : ℕ}
    (aligned : EffectiveBalancesAligned state)
    (divides : divisor ∣ preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (index : ℕ) :
    divisor ∣ balanceAt state index := by
  cases found : state.validators.data[index]? with
  | none => simp [balanceAt, found]
  | some validator =>
    have increments := (aligned validator
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))).1
    rw [← UInt64.toNat_inj, UInt64.toNat_mod] at increments
    simp only [balanceAt, found, Option.map_some, Option.getD_some]
    exact Nat.dvd_trans divides (Nat.dvd_of_mod_eq_zero increments)

/-- The sum of the effective balances at some indices is their stake, read as a set.

An index counts once however often it appears, and an index outside the registry adds nothing. -/
theorem sumMarked_markIndices_eq_stake (state : BeaconState preset fork)
    (indices : List ValidatorIndex) :
    sumMarked state.validators.data (markIndices state.validators.data.size indices) =
      stake (fun index => balanceAt state index.toNat) indices.toFinset := by
  classical
  set n := state.validators.data.size
  rw [sumMarked_eq_sum]
  simp only [getElem?_markIndices]
  have range : ((List.range n).map fun j =>
      if (if j < n then some (indices.any (·.toNat == j)) else none).getD false then
        balanceAt state j
      else 0).sum = ∑ j ∈ Finset.range n,
        if indices.any (·.toNat == j) then balanceAt state j else 0 := by
    rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
      Multiset.sum_coe]
    congr 1
    refine List.map_congr_left fun j member => ?_
    simp [List.mem_range.mp member]
  refine range.trans ?_
  rw [← Finset.sum_filter, stake]
  have inside : ∑ i ∈ indices.toFinset, balanceAt state i.toNat =
      ∑ i ∈ indices.toFinset.filter (·.toNat < n), balanceAt state i.toNat := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split
    · rfl
    · simp [balanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt ‹_›)]
  rw [inside]
  have image : (Finset.range n).filter (fun j => indices.any (·.toNat == j) = true) =
      (indices.toFinset.filter (·.toNat < n)).image (·.toNat) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, List.any_eq_true, beq_iff_eq,
      Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨lt, i, member, rfl⟩
      exact ⟨i, ⟨member, lt⟩, rfl⟩
    · rintro ⟨i, ⟨member, lt⟩, rfl⟩
      exact ⟨lt, i, member, rfl⟩
  rw [image, Finset.sum_image fun a _ b _ same => UInt64.toNat_inj.mp same]

/-- A total balance succeeds exactly when two conditions hold.

Every index names a validator, and the stake of the indices, as a set, is below `2^64`.

It is then that stake, or one increment if the stake is smaller. -/
theorem getTotalBalance_ok_iff_stake {state : BeaconState preset fork}
    {indices : List ValidatorIndex} {total : Gwei} :
    getTotalBalance state indices = .ok total ↔
      (∀ index ∈ indices, index.toNat < state.validators.data.size) ∧
        stake (fun index => balanceAt state index.toNat) indices.toFinset < 2 ^ 64 ∧
        total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (stake (fun index => balanceAt state index.toNat) indices.toFinset) := by
  rw [getTotalBalance_ok_iff, sumMarked_markIndices_eq_stake]
  refine and_congr_right fun _ => and_congr_right fun lt => ?_
  rw [← UInt64.toNat_inj, toNat_max, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt lt]

/-- Three times a part reaches twice a total, each raised to a floor.

That holds exactly when it holds without the floor.

The total must be more than one and a half times the floor. -/
private theorem two_mul_max_le_three_mul_max_iff {floor total part : ℕ}
    (large : 3 * floor < 2 * total) :
    2 * max floor total ≤ 3 * max floor part ↔ 2 * total ≤ 3 * part := by
  simp only [Nat.max_def]
  split_ifs <;> omega

/-- The test of justification compares the stakes of two sets of indices.

The first total balance is that of the active indices, the second that of the attesting ones.

The test computes twice the first and three times the second.

It asks that the first is at most the second.

It answers yes exactly when twice the active stake is at most three times the attesting stake.

The active stake must be more than one and a half increments.

The attesting indices need not be active, so the attesting stake may count inactive validators. -/
theorem justificationTest_iff_stake {state : BeaconState preset fork}
    {active attesting : List ValidatorIndex} {total balance threshold weight : Gwei}
    (totalOk : getTotalBalance state active = .ok total)
    (balanceOk : getTotalBalance state attesting = .ok balance)
    (thresholdOk : mulChecked total 2 = .ok threshold)
    (weightOk : mulChecked balance 3 = .ok weight)
    (large : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (fun index => balanceAt state index.toNat) active.toFinset) :
    threshold ≤ weight ↔
      2 * stake (fun index => balanceAt state index.toNat) active.toFinset ≤
        3 * stake (fun index => balanceAt state index.toNat) attesting.toFinset := by
  obtain ⟨-, -, totalEq⟩ := getTotalBalance_ok_iff_stake.mp totalOk
  obtain ⟨-, -, balanceEq⟩ := getTotalBalance_ok_iff_stake.mp balanceOk
  obtain ⟨-, thresholdEq⟩ := mulChecked_ok_iff.mp thresholdOk
  obtain ⟨-, weightEq⟩ := mulChecked_ok_iff.mp weightOk
  rw [UInt64.le_iff_toNat_le, thresholdEq, weightEq, totalEq, balanceEq]
  simp only [UInt64.reduceToNat]
  rw [Nat.mul_comm _ 2, Nat.mul_comm _ 3]
  exact two_mul_max_le_three_mul_max_iff large

end EthLib.Consensus

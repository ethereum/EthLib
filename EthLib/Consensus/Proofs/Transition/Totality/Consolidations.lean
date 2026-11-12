module

public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.Totality.Bound

/-!
# Proofs: pending consolidations succeed under bounds

Each consolidation debits at most its source balance before it credits the target.

The sum of all balances below `2^64` therefore leaves room for that credit.

This also covers a source and target with the same index.

The queue indices must be in the registry, with one balance per validator.

Room for the next epoch then excludes every error of the pending-consolidation step.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

private theorem balance_le_sum (state : BeaconState preset fork) {i : Nat}
    (inside : i < state.balances.data.size) :
    (state.balances.data[i]).toNat ≤ balanceSum state := by
  apply List.single_le_sum (fun _ _ => Nat.zero_le _)
  exact List.mem_map.mpr ⟨state.balances.data[i], by simp, rfl⟩

private theorem moveBalance_exists_ok (state : BeaconState preset fork)
    (source target : ValidatorIndex) (amount balance : Gwei)
    (sourceRead : getBalance state source = .ok balance) (bounded : amount ≤ balance)
    (targetInside : target.toNat < state.balances.data.size)
    (budget : balanceSum state < 2 ^ 64) :
    ∃ after, (do
      let lowered ← decreaseBalance state source amount
      increaseBalance lowered target amount) = .ok after ∧
      SameSizes state after ∧ after.validators = state.validators ∧
      balanceSum after = balanceSum state := by
  obtain ⟨sourceInside, -⟩ :=
    Array.getElem?_eq_some_iff.mp (getBalance_eq_ok_iff.mp sourceRead)
  let lowered := state.putBalance source.toNat sourceInside
    (saturatingSub state.balances.data[source.toNat] amount)
  have down : decreaseBalance state source amount = .ok lowered :=
    decreaseBalance_eq_ok_iff.mpr ⟨sourceInside, rfl⟩
  have size := sameSizes_decreaseBalance down
  have targetLowered : target.toNat < lowered.balances.data.size := by
    rw [size.2]
    exact targetInside
  have taken := balanceSum_decreaseBalance sourceRead bounded down
  have targetBound := balance_le_sum lowered targetLowered
  -- After the debit, any target balance plus the moved amount fits the original sum.
  have fits : lowered.balances.data[target.toNat].toNat + amount.toNat < 2 ^ 64 := by omega
  let after := lowered.putBalance target.toNat targetLowered
    (lowered.balances.data[target.toNat] + amount)
  have up : increaseBalance lowered target amount = .ok after :=
    increaseBalance_eq_ok_iff.mpr ⟨targetLowered, fits, rfl⟩
  have given := balanceSum_increaseBalance up
  refine ⟨after, ?_, size.trans (sameSizes_increaseBalance up),
    (increaseBalance_validators up).trans (decreaseBalance_validators down), ?_⟩
  · simp only [down, up, bind, Except.bind]
  · omega

private theorem passPendingConsolidations_exists_ok (nextEpoch : Epoch)
    (consolidations : List PendingConsolidation) :
    ∀ (state : BeaconState preset fork), BalancesMatch state →
      balanceSum state < 2 ^ 64 →
      (∀ consolidation ∈ consolidations,
        consolidation.sourceIndex.toNat < state.validators.data.size ∧
          consolidation.targetIndex.toNat < state.validators.data.size) →
      ∃ result, passPendingConsolidations nextEpoch state consolidations = .ok result := by
  induction consolidations with
  | nil => intro state _ _ _; exact ⟨(state, 0), rfl⟩
  | cons consolidation rest ih =>
    intro state matched budget inside
    have indices := inside consolidation List.mem_cons_self
    let source := state.validators.data[consolidation.sourceIndex.toNat]
    have found : getValidator state consolidation.sourceIndex = .ok source := by
      simp [getValidator, Array.getElem?_eq_getElem indices.1, source]
    have restInside : ∀ consolidation ∈ rest,
        consolidation.sourceIndex.toNat < state.validators.data.size ∧
          consolidation.targetIndex.toNat < state.validators.data.size :=
      fun c member => inside c (List.mem_cons_of_mem _ member)
    by_cases slashed : source.slashed = true
    · obtain ⟨result, passed⟩ := ih state matched budget restInside
      refine ⟨(result.1, result.2 + 1), ?_⟩
      simp [passPendingConsolidations, found, slashed, liftAccessor, Except.mapError,
        bind, Except.bind, pure, Except.pure, passed]
    · have notSlashed : source.slashed = false := by simpa using slashed
      by_cases early : nextEpoch < source.withdrawableEpoch
      · exact ⟨(state, 0), by simp [passPendingConsolidations, found, notSlashed,
          early, liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure]⟩
      · have sourceInside : consolidation.sourceIndex.toNat < state.balances.data.size := by
          unfold BalancesMatch at matched
          omega
        let balance := state.balances.data[consolidation.sourceIndex.toNat]
        have read : getBalance state consolidation.sourceIndex = .ok balance := by
          simp [getBalance, Array.getElem?_eq_getElem sourceInside, balance]
        obtain ⟨after, moved, sizes, validators, total⟩ := moveBalance_exists_ok state
          consolidation.sourceIndex consolidation.targetIndex (min balance source.effectiveBalance)
          balance read Std.min_le_left (by unfold BalancesMatch at matched; omega) budget
        obtain ⟨result, passed⟩ := ih after (balancesMatch_of_sameSizes sizes matched)
          (by rwa [total]) (by simpa only [validators] using restInside)
        refine ⟨(result.1, result.2 + 1), ?_⟩
        simp only [passPendingConsolidations, found, liftAccessor, Except.mapError,
          bind, Except.bind, notSlashed, Bool.false_eq_true, ↓reduceIte, early, read]
        cases lowered : decreaseBalance state consolidation.sourceIndex
            (min balance source.effectiveBalance) with
        | error error => simp [lowered, bind, Except.bind] at moved
        | ok lower =>
          have raised : increaseBalance lower consolidation.targetIndex
              (min balance source.effectiveBalance) = .ok after := by
            simpa [lowered, bind, Except.bind] using moved
          simp [raised, passed, pure, Except.pure]

/-- From Electra, pending consolidations succeed under index and balance bounds.

The registry has one balance per validator, and the sum of those balances is below `2^64`.

Both indices of every queued consolidation must be in that registry.

The current epoch plus one must fit in 64 bits. -/
theorem processPendingConsolidations_total (state : BeaconState preset fork)
    (electra : .pectra ≤ fork) (matched : BalancesMatch state)
    (budget : balanceSum state < 2 ^ 64)
    (inside : ∀ consolidation ∈ (state.pendingConsolidations electra).data,
      consolidation.sourceIndex.toNat < state.validators.data.size ∧
        consolidation.targetIndex.toNat < state.validators.data.size)
    (fits : (getCurrentEpoch state).toNat + 1 < 2 ^ 64) :
    ∃ after, processPendingConsolidations state electra = .ok after := by
  have next : addChecked (getCurrentEpoch state) 1 = .ok (getCurrentEpoch state + 1) :=
    addChecked_of_lt (by simpa using fits)
  obtain ⟨⟨after, read⟩, passed⟩ := passPendingConsolidations_exists_ok
    (getCurrentEpoch state + 1) (state.pendingConsolidations electra).data.toList state matched
    budget (by simpa using inside)
  simp only [processPendingConsolidations, next, liftAccessor, liftArith, Except.mapError,
    bind, Except.bind, passed]
  exact ⟨_, rfl⟩

end EthLib.Consensus

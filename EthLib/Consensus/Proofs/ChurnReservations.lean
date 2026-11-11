module

public import EthLib.Consensus.Proofs.Churn

/-!
# Proofs: the balance spent by exit and consolidation reservations

A list of reservations keeps the slot and the validator registry, so its churn stays fixed.

The reserved balance and churn left equal the initial carry plus the churn of added epochs.

Each epoch that the queue moves past adds one full churn.

Thus a list placed by a given epoch takes at most that window's budget, including initial carry.

This concerns queue reservations, not the change of the active set through epoch transitions.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

-- Project the successful state steps to the existing arithmetic queue fold.
private theorem foldlM_queue {σ : Type} {step : σ → Gwei → Except AccessorError σ}
    (queue : σ → Epoch × Gwei) (ready : σ → Prop) {first churn : UInt64}
    (projects : ∀ before amount after, ready before → step before amount = .ok after →
      ready after ∧ churnQueue (queue before).1 first churn (queue before).2 amount =
        .ok (queue after))
    {amounts : List Gwei} {before after : σ} (initial : ready before)
    (computed : amounts.foldlM step before = .ok after) :
    amounts.foldlM (fun q amount => churnQueue q.1 first churn q.2 amount) (queue before) =
      .ok (queue after) := by
  induction amounts generalizing before with
  | nil =>
    simpa only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] using
      congrArg queue (Except.ok.inj computed)
  | cons amount rest ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepOk, restOk⟩ := computed
    obtain ⟨kept, queueOk⟩ := projects before amount middle initial stepOk
    rw [List.foldlM_cons, queueOk]
    exact ih kept restOk

private theorem exitReservations_queue {config : Config} {electra : .pectra ≤ fork}
    {state after : BeaconState preset fork} {amounts : List Gwei} {first churn : UInt64}
    (firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first)
    (churnOk : exitChurnLimit config state = .ok churn)
    (computed : amounts.foldlM (fun s amount =>
      Prod.fst <$> computeExitEpochAndUpdateChurn config s electra amount) state = .ok after) :
    amounts.foldlM (fun q amount => churnQueue q.1 first churn q.2 amount)
      (state.earliestExitEpoch electra, state.exitBalanceToConsume electra) =
        .ok (after.earliestExitEpoch electra, after.exitBalanceToConsume electra) := by
  apply foldlM_queue (fun s => (s.earliestExitEpoch electra, s.exitBalanceToConsume electra))
    (fun s => computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      exitChurnLimit config s = .ok churn) ?_ ⟨firstOk, churnOk⟩ computed
  intro before amount later ready stepped
  obtain ⟨⟨reserved, epoch⟩, reserveOk, rfl⟩ := map_ok_iff.mp stepped
  simp only [computeExitEpochAndUpdateChurn, ready.1, ready.2, bind_ok_iff, liftArith,
    mapError_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at reserveOk
  obtain ⟨⟨queued, left⟩, queueOk, final⟩ := reserveOk
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨ready, queueOk⟩

/-- Exit reservations spend their sum, with one full churn for each later epoch of the queue.

The earliest open epoch at the start must be no earlier than the first permitted epoch. -/
theorem computeExitEpochAndUpdateChurn_foldlM_spend {config : Config}
    {electra : .pectra ≤ fork} {state after : BeaconState preset fork} {amounts : List Gwei}
    {first churn : UInt64}
    (firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first)
    (open_ : first ≤ state.earliestExitEpoch electra)
    (churnOk : exitChurnLimit config state = .ok churn)
    (computed : amounts.foldlM (fun s amount =>
      Prod.fst <$> computeExitEpochAndUpdateChurn config s electra amount) state = .ok after) :
    (after.exitBalanceToConsume electra).toNat + (amounts.map UInt64.toNat).sum =
      (state.exitBalanceToConsume electra).toNat +
        ((after.earliestExitEpoch electra).toNat - (state.earliestExitEpoch electra).toNat) *
          churn.toNat :=
  churnQueue_foldlM_spend open_ (exitReservations_queue firstOk churnOk computed)

/-- Exit reservations placed by an epoch fit the initial carry plus the churn of later epochs. -/
theorem computeExitEpochAndUpdateChurn_foldlM_le {config : Config}
    {electra : .pectra ≤ fork} {state after : BeaconState preset fork} {amounts : List Gwei}
    {first churn horizon : UInt64}
    (firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first)
    (open_ : first ≤ state.earliestExitEpoch electra)
    (churnOk : exitChurnLimit config state = .ok churn)
    (computed : amounts.foldlM (fun s amount =>
      Prod.fst <$> computeExitEpochAndUpdateChurn config s electra amount) state = .ok after)
    (placed : after.earliestExitEpoch electra ≤ horizon) :
    (amounts.map UInt64.toNat).sum ≤ (state.exitBalanceToConsume electra).toNat +
      (horizon.toNat - (state.earliestExitEpoch electra).toNat) * churn.toNat := by
  have budget := computeExitEpochAndUpdateChurn_foldlM_spend firstOk open_ churnOk computed
  have epochs := Nat.sub_le_sub_right (UInt64.le_iff_toNat_le.mp placed)
    (state.earliestExitEpoch electra).toNat
  have allowance := Nat.mul_le_mul_right churn.toNat epochs
  omega

private theorem consolidationReservations_queue {config : Config} {electra : .pectra ≤ fork}
    {state after : BeaconState preset fork} {amounts : List Gwei} {first churn : UInt64}
    (firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first)
    (churnOk : getConsolidationChurnLimit config state = .ok churn)
    (computed : amounts.foldlM (fun s amount =>
      Prod.fst <$> computeConsolidationEpochAndUpdateChurn config s electra amount)
      state = .ok after) :
    amounts.foldlM (fun q amount => churnQueue q.1 first churn q.2 amount)
      (state.earliestConsolidationEpoch electra, state.consolidationBalanceToConsume electra) =
        .ok (after.earliestConsolidationEpoch electra,
          after.consolidationBalanceToConsume electra) := by
  apply foldlM_queue
    (fun s => (s.earliestConsolidationEpoch electra, s.consolidationBalanceToConsume electra))
    (fun s => computeActivationExitEpoch preset (getCurrentEpoch s) = .ok first ∧
      getConsolidationChurnLimit config s = .ok churn) ?_ ⟨firstOk, churnOk⟩ computed
  intro before amount later ready stepped
  obtain ⟨⟨reserved, epoch⟩, reserveOk, rfl⟩ := map_ok_iff.mp stepped
  simp only [computeConsolidationEpochAndUpdateChurn, ready.1, ready.2, bind_ok_iff,
    liftArith, mapError_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at reserveOk
  obtain ⟨⟨queued, left⟩, queueOk, final⟩ := reserveOk
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨ready, queueOk⟩

/-- Consolidation reservations spend their sum, with one full churn per later queue epoch.

The earliest open epoch at the start must be no earlier than the first permitted epoch. -/
theorem computeConsolidationEpochAndUpdateChurn_foldlM_spend {config : Config}
    {electra : .pectra ≤ fork} {state after : BeaconState preset fork} {amounts : List Gwei}
    {first churn : UInt64}
    (firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first)
    (open_ : first ≤ state.earliestConsolidationEpoch electra)
    (churnOk : getConsolidationChurnLimit config state = .ok churn)
    (computed : amounts.foldlM (fun s amount =>
      Prod.fst <$> computeConsolidationEpochAndUpdateChurn config s electra amount)
      state = .ok after) :
    (after.consolidationBalanceToConsume electra).toNat + (amounts.map UInt64.toNat).sum =
      (state.consolidationBalanceToConsume electra).toNat +
        ((after.earliestConsolidationEpoch electra).toNat -
          (state.earliestConsolidationEpoch electra).toNat) * churn.toNat :=
  churnQueue_foldlM_spend open_ (consolidationReservations_queue firstOk churnOk computed)

/-- Consolidations placed by an epoch fit the initial carry plus the churn of later epochs. -/
theorem computeConsolidationEpochAndUpdateChurn_foldlM_le {config : Config}
    {electra : .pectra ≤ fork} {state after : BeaconState preset fork} {amounts : List Gwei}
    {first churn horizon : UInt64}
    (firstOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok first)
    (open_ : first ≤ state.earliestConsolidationEpoch electra)
    (churnOk : getConsolidationChurnLimit config state = .ok churn)
    (computed : amounts.foldlM (fun s amount =>
      Prod.fst <$> computeConsolidationEpochAndUpdateChurn config s electra amount)
      state = .ok after)
    (placed : after.earliestConsolidationEpoch electra ≤ horizon) :
    (amounts.map UInt64.toNat).sum ≤ (state.consolidationBalanceToConsume electra).toNat +
      (horizon.toNat - (state.earliestConsolidationEpoch electra).toNat) * churn.toNat := by
  have budget := computeConsolidationEpochAndUpdateChurn_foldlM_spend firstOk open_ churnOk computed
  have epochs := Nat.sub_le_sub_right (UInt64.le_iff_toNat_le.mp placed)
    (state.earliestConsolidationEpoch electra).toNat
  have allowance := Nat.mul_le_mul_right churn.toNat epochs
  omega

end EthLib.Consensus

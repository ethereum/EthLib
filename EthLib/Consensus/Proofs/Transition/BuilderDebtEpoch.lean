module

public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Transition.BuilderDebt
public import EthLib.Consensus.Proofs.Transition.BuilderPayments

/-!
# Proofs: the epoch step of the builder payments keeps the builder debt invariant

The step pays the payments of the previous epoch that reach the quorum, and drops the others.

The payments of the current epoch then move to the first half of the window.

A paid payment moves from the pending payments to the queued withdrawals, so no debt changes.

A dropped payment lowers the debt of its builder.

The next slot is in the next epoch, so the parent payment moves with the window.

A parent of the current epoch keeps its payment, now in the first half.

A parent of the previous epoch leaves the window.

With a positive quorum its payment, which has no weight, is dropped and not paid.

Its value then moves from the debt of its builder to the value that the late path may queue.

[EIP-7732] adds the builder payments and their epoch step.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

private theorem owedBy_shiftPayments {index : BuilderIndex}
    (payments : BuilderPendingPayments preset) :
    owedBy index ((shiftPayments payments).elements.toList.map (·.withdrawal)) =
      owedBy index ((payments.elements.toList.drop preset.SLOTS_PER_EPOCH.toNat).map
        (·.withdrawal)) := by
  have split : (shiftPayments payments).elements.toList =
      payments.elements.toList.drop preset.SLOTS_PER_EPOCH.toNat ++
        List.replicate preset.SLOTS_PER_EPOCH.toNat BuilderPendingPayment.empty := by
    apply List.ext_getElem (by simp; omega)
    intro position inside _
    simp only [Vector.length_toList] at inside
    rw [Vector.getElem_toList, List.getElem_append]
    split
    · rename_i early
      simp only [List.length_drop, Vector.length_toList] at early
      have := getElem_shiftPayments_early payments
        (by omega : position < preset.SLOTS_PER_EPOCH.toNat)
      simp only [List.getElem_drop, Vector.getElem_toList,
        Nat.add_comm preset.SLOTS_PER_EPOCH.toNat position]
      exact this
    · rename_i late
      simp only [List.length_drop, Vector.length_toList] at late
      simp only [List.getElem_replicate]
      exact getElem_shiftPayments_late payments (by omega) inside
  rw [split, List.map_append, owedBy_append]
  simp [owedBy, BuilderPendingPayment.empty]

private theorem saturatingSub_succ {epoch : UInt64} (noWrap : epoch + 1 ≠ 0) :
    Uint64.saturatingSub (epoch + 1) 1 = epoch := by
  unfold Uint64.saturatingSub
  have := epoch.toNat_lt
  split <;> rename_i order <;> revert order noWrap <;>
    simp only [ne_eq, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
      UInt64.toNat_sub, UInt64.toNat_one, UInt64.toNat_zero] <;> omega

private theorem saturatingSub_ne_succ {epoch : UInt64} (noWrap : epoch + 1 ≠ 0) :
    Uint64.saturatingSub epoch 1 ≠ epoch → Uint64.saturatingSub epoch 1 ≠ epoch + 1 := by
  unfold Uint64.saturatingSub
  have := epoch.toNat_lt
  split <;> rename_i order <;> revert order noWrap <;>
    simp only [ne_eq, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, UInt64.toNat_add,
      UInt64.toNat_sub, UInt64.toNat_one, UInt64.toNat_zero] <;> omega

private theorem ne_add_one (epoch : UInt64) : epoch ≠ epoch + 1 := by
  intro same
  have bound := epoch.toNat_lt
  have value := congrArg UInt64.toNat same
  simp only [UInt64.toNat_add, UInt64.toNat_one] at value
  omega

private theorem processBuilderPendingPayments_of_noWrap (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (holds : BuilderDebtCovered state gloas)
    (computed : processBuilderPendingPayments state gloas = .ok after) {next : Slot}
    (boundary : computeEpochAtSlot preset next = getCurrentEpoch state + 1)
    (noWrap : getCurrentEpoch state + 1 ≠ 0) :
    BuilderDebtCovered { after with slot := next } gloas := by
  obtain ⟨one, small⟩ := positive.slotsPerEpoch_bounds
  obtain ⟨quorum, found, queue, shifted⟩ := processBuilderPendingPayments_spec computed
  have least := getBuilderPaymentQuorumThreshold_pos positive found
  obtain ⟨builders, header, bid⟩ : after.builders = state.builders ∧
      after.latestBlockHeader = state.latestBlockHeader ∧
      after.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
    unfold EthLib.Consensus.processBuilderPendingPayments at computed
    obtain ⟨_, _, rest⟩ := bind_ok_iff.mp computed
    cases rest
    exact ⟨rfl, rfl, rfl⟩
  have movedBuilders : ({ after with slot := next }).builders = state.builders := builders
  have movedBid : ({ after with slot := next }).latestExecutionPayloadBid =
      state.latestExecutionPayloadBid := bid
  have movedHeader : ({ after with slot := next }).latestBlockHeader.slot =
      state.latestBlockHeader.slot := congrArg (·.slot) header
  have movedSlot : ({ after with slot := next }).slot = next := rfl
  have movedPayments : ({ after with slot := next }).builderPendingPayments gloas =
      shiftPayments (state.builderPendingPayments gloas) := shifted
  have movedQueue : (({ after with slot := next }).builderPendingWithdrawals gloas).data.toList =
      (state.builderPendingWithdrawals gloas).data.toList ++
        releasedPayments (state.builderPendingPayments gloas).elements.toList
          preset.SLOTS_PER_EPOCH.toNat quorum := queue
  generalize { after with slot := next } = moved at *
  have early : ∀ j, j < preset.SLOTS_PER_EPOCH.toNat →
      paymentAt moved gloas j = paymentAt state gloas (j + preset.SLOTS_PER_EPOCH.toNat) := by
    intro j inside
    rw [paymentAt_of_lt (by omega), paymentAt_of_lt (by omega)]
    simp only [movedPayments]
    exact getElem_shiftPayments_early _ inside
  have late : ∀ j, preset.SLOTS_PER_EPOCH.toNat ≤ j → j < 2 * preset.SLOTS_PER_EPOCH.toNat →
      paymentAt moved gloas j = .empty := by
    intro j low high
    rw [paymentAt_of_lt high]
    simp only [movedPayments]
    exact getElem_shiftPayments_late _ low high
  have beyond : ∀ j, preset.SLOTS_PER_EPOCH.toNat ≤ j → paymentAt moved gloas j = .empty := by
    intro j low
    by_cases high : j < 2 * preset.SLOTS_PER_EPOCH.toNat
    · exact late j low high
    · simp [paymentAt, Nat.not_lt.mp high]
  have shiftedEmpty : ∀ j, (j < preset.SLOTS_PER_EPOCH.toNat →
      paymentAt state gloas (j + preset.SLOTS_PER_EPOCH.toNat) = .empty) →
      paymentAt moved gloas j = .empty := by
    intro j empty
    by_cases low : j < preset.SLOTS_PER_EPOCH.toNat
    · rw [early j low]
      exact empty low
    · exact beyond j (by omega)
  have balance : ∀ index, builderBalance moved gloas index = builderBalance state gloas index :=
    fun _ => by simp only [builderBalance, movedBuilders]
  have lateEq : latePaymentOpen moved gloas = latePaymentOpen state gloas →
      ∀ index, lateBidValue moved gloas index = lateBidValue state gloas index :=
    fun opened _ => by simp only [lateBidValue, opened, movedBid]
  have totalAfter : ∀ index, pendingBuilderTotal moved gloas index =
      owedBy index (state.builderPendingWithdrawals gloas).data.toList +
        owedBy index (releasedPayments (state.builderPendingPayments gloas).elements.toList
          preset.SLOTS_PER_EPOCH.toNat quorum) +
        owedBy index (((state.builderPendingPayments gloas).elements.toList.drop
          preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) := by
    intro index
    unfold pendingBuilderTotal
    rw [movedQueue, movedPayments, owedBy_append, owedBy_shiftPayments]
  have totalBefore : ∀ index, pendingBuilderTotal state gloas index =
      owedBy index (state.builderPendingWithdrawals gloas).data.toList +
        owedBy index (((state.builderPendingPayments gloas).elements.toList.take
          preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) +
        owedBy index (((state.builderPendingPayments gloas).elements.toList.drop
          preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) := by
    intro index
    unfold pendingBuilderTotal
    have split := congrArg (fun list => owedBy index (list.map (·.withdrawal)))
      (List.take_append_drop preset.SLOTS_PER_EPOCH.toNat
        (state.builderPendingPayments gloas).elements.toList)
    simp only [List.map_append, owedBy_append] at split
    omega
  have releasedLe : ∀ index, owedBy index (releasedPayments
      (state.builderPendingPayments gloas).elements.toList preset.SLOTS_PER_EPOCH.toNat quorum) ≤
      owedBy index (((state.builderPendingPayments gloas).elements.toList.take
        preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) :=
    fun _ => owedBy_filter_le _
  suffices step : (∀ index, pendingBuilderTotal moved gloas index +
      lateBidValue moved gloas index ≤
        pendingBuilderTotal state gloas index + lateBidValue state gloas index) ∧
      ParentPaymentFresh moved gloas ∧ LaterPaymentsEmpty moved gloas by
    refine ⟨fun index => ?_, fun index builder found exited => ?_, step.2.1, step.2.2⟩
    · rw [balance]
      exact Nat.le_trans (step.1 index) (holds.covered index)
    · have := holds.exitedClear index builder (by rwa [movedBuilders] at found) exited
      have := step.1 index
      omega
  suffices step : (∀ index, owedBy index (releasedPayments
      (state.builderPendingPayments gloas).elements.toList preset.SLOTS_PER_EPOCH.toNat quorum) +
        lateBidValue moved gloas index ≤
      owedBy index (((state.builderPendingPayments gloas).elements.toList.take
        preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) + lateBidValue state gloas index) ∧
      ParentPaymentFresh moved gloas ∧ LaterPaymentsEmpty moved gloas by
    refine ⟨fun index => ?_, step.2⟩
    rw [totalAfter, totalBefore]
    have := step.1 index
    omega
  have positionBefore : parentPaymentPosition state =
      if computeEpochAtSlot preset state.latestBlockHeader.slot = getCurrentEpoch state then
        some (preset.SLOTS_PER_EPOCH + state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH)
      else if computeEpochAtSlot preset state.latestBlockHeader.slot =
          Uint64.saturatingSub (getCurrentEpoch state) 1 then
        some (state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH)
      else none := rfl
  have positionAfter : parentPaymentPosition moved =
      if computeEpochAtSlot preset state.latestBlockHeader.slot = getCurrentEpoch state + 1 then
        some (preset.SLOTS_PER_EPOCH + state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH)
      else if computeEpochAtSlot preset state.latestBlockHeader.slot = getCurrentEpoch state then
        some (state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH)
      else none := by
    have current : getCurrentEpoch moved = getCurrentEpoch state + 1 := by
      unfold getCurrentEpoch
      rw [movedSlot]
      exact boundary
    unfold parentPaymentPosition getPreviousEpoch
    rw [current, saturatingSub_succ noWrap, movedHeader]
  have offset : (state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH).toNat <
      preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ (by omega)
  have shiftedPosition : (preset.SLOTS_PER_EPOCH +
      state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH).toNat =
      preset.SLOTS_PER_EPOCH.toNat +
        (state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH).toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  generalize state.latestBlockHeader.slot % preset.SLOTS_PER_EPOCH = k
    at positionBefore positionAfter offset shiftedPosition
  generalize computeEpochAtSlot preset state.latestBlockHeader.slot = parent
    at positionBefore positionAfter
  generalize getCurrentEpoch state = epoch at positionBefore positionAfter noWrap
  by_cases current : parent = epoch
  · -- The parent payment moves from the second half to the first.
    have ahead : parent ≠ epoch + 1 := current ▸ ne_add_one epoch
    rw [ite_eq_left current] at positionBefore
    rw [ite_eq_right ahead, ite_eq_left current] at positionAfter
    have same : paymentAt moved gloas k.toNat =
        paymentAt state gloas (preset.SLOTS_PER_EPOCH + k).toNat := by
      rw [early _ offset, shiftedPosition, Nat.add_comm]
    have opened : latePaymentOpen moved gloas = latePaymentOpen state gloas := by
      simp only [latePaymentOpen, positionBefore, positionAfter, same]
    refine ⟨fun index => ?_, fun position found => ?_, fun j later => ?_⟩
    · rw [lateEq opened]
      have := releasedLe index
      omega
    · rw [positionAfter] at found
      cases found
      simp only [same, latestBidWithdrawal, movedBid]
      exact holds.parentFresh _ positionBefore
    · have after := later k positionAfter
      exact shiftedEmpty j fun _ => holds.laterEmpty _ fun parent found => by
        rw [positionBefore] at found
        cases found
        omega
  by_cases previous : parent = Uint64.saturatingSub epoch 1
  · -- The parent payment leaves the window, and the step drops it.
    have ahead : parent ≠ epoch + 1 :=
      previous ▸ saturatingSub_ne_succ noWrap (previous ▸ current)
    rw [ite_eq_right current, ite_eq_left previous] at positionBefore
    rw [ite_eq_right ahead, ite_eq_right current] at positionAfter
    have opened : latePaymentOpen moved gloas = true := by
      simp only [latePaymentOpen, positionAfter]
    obtain ⟨weightless, amountOrBid⟩ := holds.parentFresh _ positionBefore
    refine ⟨fun index => ?_, fun position found => by simp [positionAfter] at found,
      fun j _ => shiftedEmpty j fun _ => holds.laterEmpty _ fun parent found => ?_⟩
    · have entry : ((state.builderPendingPayments gloas).elements.toList.take
          preset.SLOTS_PER_EPOCH.toNat)[k.toNat]'(by simp; omega) =
          paymentAt state gloas k.toNat := by
        rw [paymentAt_of_lt (by omega)]
        simp
        rfl
      have dropped : owedBy index (releasedPayments
          (state.builderPendingPayments gloas).elements.toList preset.SLOTS_PER_EPOCH.toNat
            quorum) + owedBy index [(((state.builderPendingPayments gloas).elements.toList.take
              preset.SLOTS_PER_EPOCH.toNat)[k.toNat]'(by simp; omega)).withdrawal] ≤
          owedBy index (((state.builderPendingPayments gloas).elements.toList.take
            preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) :=
        owedBy_filter_add_le (by simp; omega) (by
          simp only [entry, weightless]
          simp only [decide_eq_false_iff_not]
          intro reached
          exact absurd (UInt64.lt_of_lt_of_le least reached) (by decide))
      rw [entry] at dropped
      rcases amountOrBid with zero | paid
      · have openedBefore : latePaymentOpen state gloas = true := by
          simp [latePaymentOpen, positionBefore, zero]
        rw [lateEq (opened.trans openedBefore.symm)]
        omega
      · rw [paid] at dropped
        simp only [lateBidValue, opened, movedBid, and_true]
        have single : owedBy index [latestBidWithdrawal state gloas] =
            if (state.latestExecutionPayloadBid gloas).builderIndex = index then
              (state.latestExecutionPayloadBid gloas).value.toNat else 0 := by
          simp [owedBy, latestBidWithdrawal, bidPayment]
        rw [single] at dropped
        split <;> split at dropped <;> omega
    · rw [positionBefore] at found
      cases found
      omega
  · -- The parent payment is outside the window, or enters its second half empty.
    rw [ite_eq_right current, ite_eq_right previous] at positionBefore
    have openedBefore : latePaymentOpen state gloas = true := by
      simp only [latePaymentOpen, positionBefore]
    by_cases ahead : parent = epoch + 1
    · rw [ite_eq_left ahead] at positionAfter
      have empty : paymentAt moved gloas (preset.SLOTS_PER_EPOCH + k).toNat = .empty :=
        late _ (by omega) (by omega)
      have opened : latePaymentOpen moved gloas = latePaymentOpen state gloas := by
        rw [openedBefore]
        simp only [latePaymentOpen, positionAfter, empty]
        rfl
      refine ⟨fun index => ?_, fun position found => ?_, fun j later => ?_⟩
      · rw [lateEq opened]
        have := releasedLe index
        omega
      · rw [positionAfter] at found
        cases found
        rw [empty]
        exact ⟨rfl, Or.inl rfl⟩
      · have after := later _ positionAfter
        exact beyond j (by omega)
    · rw [ite_eq_right ahead, ite_eq_right current] at positionAfter
      have opened : latePaymentOpen moved gloas = latePaymentOpen state gloas := by
        rw [openedBefore]
        simp only [latePaymentOpen, positionAfter]
      refine ⟨fun index => ?_, fun position found => by simp [positionAfter] at found,
        fun j _ => shiftedEmpty j fun _ => holds.laterEmpty _ fun parent found => by
          simp [positionBefore] at found⟩
      rw [lateEq opened]
      have := releasedLe index
      omega

/-- With a positive quorum, the epoch step and the move to the next slot keep the debt invariant.

The next slot follows the slot of the state, and it is the first slot of an epoch. -/
theorem BuilderDebtCovered.processBuilderPendingPayments (positive : preset.PaymentQuorumPositive)
    {gloas : .glamsterdam ≤ fork} (holds : BuilderDebtCovered state gloas)
    (computed : processBuilderPendingPayments state gloas = .ok after) {next : Slot}
    (advance : next.toNat = state.slot.toNat + 1) (first : next % preset.SLOTS_PER_EPOCH = 0) :
    BuilderDebtCovered { after with slot := next } gloas := by
  have pos := positive.slotsPerEpoch_bounds.1
  have divides : preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
    rw [← advance]
    exact Nat.dvd_of_mod_eq_zero (by simpa [UInt64.toNat_mod] using congrArg UInt64.toNat first)
  have quotient : (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 :=
    Nat.succ_div_of_dvd divides
  have small := next.toNat_lt
  have least : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 ≤ next.toNat := by
    rw [advance, ← quotient]
    exact Nat.div_le_self _ _
  have successor : (getCurrentEpoch state + 1).toNat =
      state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_add, UInt64.toNat_div,
      UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (by omega)
  refine processBuilderPendingPayments_of_noWrap positive holds computed ?_ ?_
  · apply UInt64.toNat_inj.mp
    rw [successor, computeEpochAtSlot, UInt64.toNat_div, advance, quotient]
  · intro wraps
    have := congrArg UInt64.toNat wraps
    rw [successor] at this
    simp at this

end EthLib.Consensus

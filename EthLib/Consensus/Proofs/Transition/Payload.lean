module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.Payload

/-!
# Proofs: the bid of a block

After a valid bid, the state keeps the bid.

A self-built bid has no value, and a bid with no value records no payment.

A bid with a value records one payment, at the position of its slot in the next epoch.

That payment pays the bid's value from its builder to the proposer of the slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- A valid bid passes its checks, records its payment, and is kept by the state. -/
theorem processExecutionPayloadBid_ok {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    checkExecutionPayloadBid config checks state gloas signed = .ok () ∧
      ∃ recorded, recordBidPayment state gloas signed.message = .ok recorded ∧
        after = { recorded with latestExecutionPayloadBid := fun _ => signed.message } := by
  obtain ⟨u, checked, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨recorded, record, kept⟩ := bind_ok_iff.mp rest
  exact ⟨checked, recorded, record, (Except.ok.inj kept).symm⟩

/-- After a valid bid, the state keeps the bid. -/
theorem latestExecutionPayloadBid_processExecutionPayloadBid
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    after.latestExecutionPayloadBid gloas = signed.message := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayloadBid_ok computed
  rfl

/-- A self-built bid that passes its checks has no value. -/
theorem value_eq_zero_of_selfBuild {signed : SignedExecutionPayloadBid preset fork}
    (checked : checkExecutionPayloadBid config checks state gloas signed = .ok ())
    (selfBuild : signed.message.builderIndex = BUILDER_INDEX_SELF_BUILD) :
    signed.message.value = 0 := by
  unfold checkExecutionPayloadBid at checked
  obtain ⟨u, first, _⟩ := bind_ok_iff.mp checked
  unfold checkBidBuilder at first
  simp only [selfBuild, ↓reduceIte, ensure_ok_iff] at first
  exact first.1

/-- A bid with no value records no payment. -/
theorem recordBidPayment_of_value_eq_zero {bid : ExecutionPayloadBid preset fork}
    (free : bid.value = 0) : recordBidPayment state gloas bid = .ok state := by
  unfold recordBidPayment
  simp only [free, UInt64.lt_irrefl, ↓reduceIte]
  rfl

/-- A valid self-built bid leaves the pending payments as they were. -/
theorem builderPendingPayments_processExecutionPayloadBid_selfBuild
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after)
    (selfBuild : signed.message.builderIndex = BUILDER_INDEX_SELF_BUILD) :
    after.builderPendingPayments gloas = state.builderPendingPayments gloas := by
  obtain ⟨checked, recorded, record, rfl⟩ := processExecutionPayloadBid_ok computed
  rw [recordBidPayment_of_value_eq_zero (value_eq_zero_of_selfBuild checked selfBuild),
    Except.ok.injEq] at record
  subst record
  rfl

/-- A bid with a value records one payment to the proposer of the slot.

The payment sits at the position of the bid's slot in the second epoch of the list.

Every other field of the state is unchanged. -/
theorem recordBidPayment_of_pos {bid : ExecutionPayloadBid preset fork}
    {recorded : BeaconState preset fork} (paid : 0 < bid.value)
    (record : recordBidPayment state gloas bid = .ok recorded) :
    ∃ proposer, ∃ position : Fin (2 * preset.SLOTS_PER_EPOCH.toNat),
      getBeaconProposerIndex state = .ok proposer ∧
      position.val = preset.SLOTS_PER_EPOCH.toNat +
        (bid.slot % preset.SLOTS_PER_EPOCH).toNat ∧
      recorded = { state with builderPendingPayments := fun _ =>
        (state.builderPendingPayments gloas).set position (bidPayment bid proposer) } := by
  unfold recordBidPayment at record
  simp only [paid, ↓reduceIte] at record
  obtain ⟨proposer, found, rest⟩ := bind_ok_iff.mp record
  obtain ⟨position, placed, kept⟩ := bind_ok_iff.mp rest
  rw [liftAccessor_ok] at found
  unfold bidPaymentPosition at placed
  split at placed
  · cases placed
  cases placed
  exact ⟨proposer, _, found, rfl, (Except.ok.inj kept).symm⟩

/-- The payment of a bid pays its value, from its builder, to the address it names. -/
theorem bidPayment_withdrawal (bid : ExecutionPayloadBid preset fork) (proposer : ValidatorIndex) :
    (bidPayment bid proposer).withdrawal = ⟨bid.feeRecipient, bid.value, bid.builderIndex⟩ ∧
      (bidPayment bid proposer).weight = 0 ∧ (bidPayment bid proposer).proposerIndex = proposer :=
  ⟨rfl, rfl, rfl⟩

end EthLib.Consensus

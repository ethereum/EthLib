module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtBlock
public import EthLib.Consensus.Proofs.Transition.PaymentReleaseWithdrawals

/-!
# Proofs: a block and the bids it pays

From Gloas the builder of a block pays its proposer through a pending payment.

A block may pay one bid, that of its parent, through the payload of the parent.

The payload of the parent and the header of the block form one step.

That step releases at most the payment of the parent, and a payment it releases is closed after it.

The header moves the latest block to the slot of the state, which closes the late path.

No later step of the block releases a payment.

The bid opens only the payment of its own slot, which is closed before the bid.

So a block as a whole releases at most the payment of its parent.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- The slot, the pending payments, the pending withdrawals and the latest bid are kept. -/
private structure PaymentFields (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  payments : after.builderPendingPayments = state.builderPendingPayments
  withdrawals : after.builderPendingWithdrawals = state.builderPendingWithdrawals
  bid : after.latestExecutionPayloadBid = state.latestExecutionPayloadBid

/-- Steps that keep the fields of the payments keep them together. -/
private theorem PaymentFields.trans {first second third : BeaconState preset fork}
    (one : PaymentFields first second) (two : PaymentFields second third) :
    PaymentFields first third :=
  ⟨two.slot.trans one.slot, two.payments.trans one.payments, two.withdrawals.trans one.withdrawals,
    two.bid.trans one.bid⟩

/-- A step that keeps the builder fields keeps the fields of the payments. -/
private theorem PaymentFields.of_frame {first second : BeaconState preset fork}
    (frame : BuilderFrame first second) : PaymentFields first second :=
  ⟨frame.slot, frame.payments, frame.withdrawals, frame.bid⟩

/-- A release closed in the window of its end state stays closed after a later header.

The steps between them keep the fields of the payments.

The header is the one that processing a block applies after those steps. -/
private theorem closed_of_fields {gloas : .glamsterdam ≤ fork}
    {mid parented : BeaconState preset fork} {block : BeaconBlock preset fork}
    {released : List Slot} (release : PaymentRelease state mid gloas released)
    (closedMid : ∀ slot ∈ released, ¬ PaymentInWindow mid gloas slot)
    (kept : PaymentFields mid parented) (headedOk : processBlockHeader parented block = .ok after) :
    ∀ slot ∈ released, ¬ PaymentOpen after gloas slot := by
  have late := processBlockHeader_paymentOpen (gloas := gloas) headedOk
  obtain ⟨_, -, rfl⟩ := processBlockHeader_eq headedOk
  have positions := slotPaymentPosition_congr (state := mid) (after := parented) kept.slot
  have read : ∀ position,
      (paymentAt parented gloas position).withdrawal = (paymentAt mid gloas position).withdrawal :=
    fun position => by simp only [paymentAt, kept.payments]
  have window : ∀ slot, PaymentInWindow parented gloas slot ↔ PaymentInWindow mid gloas slot :=
    fun slot => by simp only [PaymentInWindow, positions, read]
  intro slot member opened
  rcases late slot opened with inside | atState
  · exact closedMid slot member ((window slot).mp inside)
  · have past := release.past slot member
    have forward := release.forward
    rw [atState, kept.slot] at *
    exact absurd (UInt64.lt_of_lt_of_le past forward) (UInt64.lt_irrefl _)

/-- A release, then a step that keeps the payment fields and the latest block header, is a release.
-/
private theorem PaymentRelease.of_fields_after {gloas : .glamsterdam ≤ fork}
    {mid parented : BeaconState preset fork} {released : List Slot}
    (release : PaymentRelease state mid gloas released) (kept : PaymentFields mid parented)
    (header : parented.latestBlockHeader.slot = mid.latestBlockHeader.slot) :
    PaymentRelease state parented gloas released := by
  have positions := slotPaymentPosition_congr (state := mid) (after := parented) kept.slot
  have read : ∀ position,
      (paymentAt parented gloas position).withdrawal = (paymentAt mid gloas position).withdrawal :=
    fun position => by simp only [paymentAt, kept.payments]
  have bid := congrFun kept.bid gloas
  have opens := paymentOpen_congr positions header bid read
  refine ⟨release.nodup, ?_, release.opened, release.past, ?_, ?_, ?_⟩
  · rw [congrFun kept.withdrawals gloas, release.queue]
  · exact fun slot opened => release.noReopen slot ((opens slot).mp opened)
  · intro slot openedLast openedFirst
    rw [openWithdrawal_congr positions bid read slot]
    exact release.stable slot ((opens slot).mp openedLast) openedFirst
  · rw [kept.slot]
    exact release.forward

/-- From Gloas, the parent payload releases at most the parent payment, closed after the header.

The hypotheses are those of the step of the parent payload and the header. -/
private theorem parentPayload_release {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} {parented : BeaconState preset fork}
    (fresh : ParentPaymentFresh state gloas) (bidAt : ValuedBidAtLatestBlock state gloas)
    (parentOk : Consensus.processParentExecutionPayload config checks state gloas block.body =
      .ok parented)
    (headedOk : processBlockHeader parented block = .ok after) :
    ∃ released : List Slot, PaymentRelease state parented gloas released ∧
      (∀ slot ∈ released, ¬ PaymentOpen after gloas slot) ∧
      released.Sublist [state.latestBlockHeader.slot] := by
  have older := latestBlockHeader_slot_lt_of_processBlockHeader parentOk headedOk
  have parentHeader : parented.latestBlockHeader = state.latestBlockHeader :=
    (payloadInputs_processParentExecutionPayload parentOk).latestBlockHeader
  rcases processParentExecutionPayload_ok parentOk with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, parentedEq⟩
  · exact ⟨[], .refl _ gloas, nofun, List.nil_sublist _⟩
  have settledHeader : settled.latestBlockHeader = state.latestBlockHeader := by
    have same := congrArg BeaconState.latestBlockHeader (settleParentPayment_eq settledOk)
    exact same
  obtain ⟨released, release, sub, -, closed⟩ := settleParentPayment_release older fresh bidAt
    settledOk
  have frame := builderFrame_validatorRequests depositsOk withdrawalsOk consolidationsOk
  obtain ⟨slot, payments, withdrawals, bid⟩ := builderRequests_paymentFields buildersOk exitsOk
  have kept : PaymentFields settled parented :=
    ((PaymentFields.of_frame frame).trans ⟨slot, payments, withdrawals, bid⟩).trans
      (by rw [parentedEq]; exact ⟨rfl, rfl, rfl, rfl⟩)
  have closes := closed_of_fields release (fun paid member => by
    rw [List.mem_singleton.mp (sub.subset member)]
    exact closed) kept headedOk
  exact ⟨released, release.of_fields_after kept (by rw [parentHeader, settledHeader]), closes,
    sub⟩

/-- From Gloas, the parent payload and the header of a block release at most the parent payment.

They release the payment of the parent's slot or nothing, and each released payment is closed.

The parent payment, while it is in the window, must have no weight.

It must pay the latest bid or have no amount.

A latest bid with a value must be at the slot of the parent.

Those hypotheses are assumptions, which the builder debt invariant and a later step provide. -/
theorem processParentExecutionPayload_processBlockHeader_paymentStep
    {gloas : .glamsterdam ≤ fork} {block : BeaconBlock preset fork}
    {parented : BeaconState preset fork} (fresh : ParentPaymentFresh state gloas)
    (bidAt : ValuedBidAtLatestBlock state gloas)
    (parentOk : Consensus.processParentExecutionPayload config checks state gloas block.body =
      .ok parented)
    (headedOk : processBlockHeader parented block = .ok after) :
    ∃ released : List Slot, PaymentStep state after gloas released ∧
      released.Sublist [state.latestBlockHeader.slot] := by
  obtain ⟨released, release, closes, sub⟩ := parentPayload_release fresh bidAt parentOk headedOk
  exact ⟨released, .of_release_trans release
    (.of_release (processBlockHeader_release headedOk) nofun) closes, sub⟩

/-- From Gloas, a block releases at most the payment of its parent, at the payload of its parent.

That step queues the withdrawal of the released payment, and nothing else adds to the queue.

The rest of the block releases nothing, and may drop a prefix of the queue.

The released payment is closed after the block.

The preset needs a positive payment quorum and at least two slots in an epoch.

Each registry must hold at most 2^40 entries after the block.

The builder debt invariant must hold before the block.

A latest bid with a value must be at the slot of the latest block. -/
theorem processBlock_paymentRelease (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : BuilderDebtCovered state gloas)
    (bidAt : ValuedBidAtLatestBlock state gloas)
    (validatorsFit : after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    ∃ (parented : BeaconState preset fork) (released : List Slot),
      Consensus.processParentExecutionPayload config checks state gloas block.body = .ok parented ∧
      PaymentRelease state parented gloas released ∧ PaymentStep parented after gloas [] ∧
      (∀ slot ∈ released, ¬ PaymentOpen after gloas slot) ∧
      released.Sublist [state.latestBlockHeader.slot] := by
  obtain ⟨parented, headed, withdrawn, bidded, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, votedFrame, operatedOk, syncedFrame, grows, size⟩ :=
    processBlock_gloas_steps gloas computed
  obtain ⟨released, release, closesHeaded, sub⟩ :=
    parentPayload_release holds.parentFresh bidAt parentOk headedOk
  obtain ⟨settled, placed, -⟩ := holds.headed parentOk headedOk
  have parentInputs := payloadInputs_processParentExecutionPayload parentOk
  have withdrawnInputs := payloadInputs_processWithdrawals withdrawnOk
  have paid := settled.processWithdrawals (Nat.le_trans grows validatorsFit)
    (by rw [size]; exact buildersFit) (getCurrentEpoch_ne_farFuture twoSlots headed) withdrawnOk
  -- The header keeps the slot and the latest bid of the parent payload.
  have headedSlot : headed.slot = state.slot := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact parentInputs.slot
  have headedBid : headed.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact parentInputs.latestExecutionPayloadBid
  have older := latestBlockHeader_slot_lt_of_processBlockHeader parentOk headedOk
  have withdrawnSlot : withdrawn.slot = state.slot := withdrawnInputs.slot.trans headedSlot
  have withdrawnBid : withdrawn.latestExecutionPayloadBid = state.latestExecutionPayloadBid :=
    withdrawnInputs.latestExecutionPayloadBid.trans headedBid
  -- The slot of the state is not open before the bid.
  have fresh : ¬ PaymentOpen withdrawn gloas withdrawn.slot := by
    rintro (⟨position, found, amount⟩ | ⟨-, bidSlot, -, value⟩)
    · have mapped := slotPaymentPosition_map_toNat positive.slotsPerEpoch_bounds withdrawn
        withdrawn.slot
      simp only [↓reduceIte, found, Option.map_some] at mapped
      have empty := paid.laterEmpty position.toNat (Nat.le_of_eq (Option.some.inj mapped).symm)
      rw [empty] at amount
      exact absurd amount (by decide)
    · rw [congrFun withdrawnBid gloas] at bidSlot value
      rw [bidAt value, withdrawnSlot] at bidSlot
      rw [bidSlot] at older
      exact UInt64.lt_irrefl _ older
  have bidHolds := paid.processExecutionPayloadBid positive
    (by rw [withdrawnInputs.latestBlockHeader, withdrawnInputs.slot]; exact placed) biddedOk
  have votedHolds := bidHolds.of_frame votedFrame
  have rest : PaymentStep headed after gloas [] :=
    ((((processWithdrawals_paymentStep withdrawnOk).trans_nil
      (.of_release (processExecutionPayloadBid_release positive fresh biddedOk) nofun)).trans_nil
      (.of_release (.of_frame votedFrame) nofun)).trans_nil
      (.of_release (.of_cancel votedHolds.parentFresh
        (PaymentCancel.processOperations operatedOk)) nofun)).trans_nil
      (.of_release (.of_frame syncedFrame) nofun)
  refine ⟨parented, released, parentOk, release,
    (PaymentStep.of_release (processBlockHeader_release headedOk) nofun).trans_nil rest,
    fun slot member => rest.keepsClosed (closesHeaded slot member) ?_, sub⟩
  rw [headedSlot]
  exact release.past slot member

/-- From Gloas, a block releases at most the payment of its parent, and drops a prefix of the queue.

The preset needs a positive payment quorum and at least two slots in an epoch.

Each registry must hold at most 2^40 entries after the block.

The builder debt invariant must hold before the block.

A latest bid with a value must be at the slot of the latest block. -/
theorem processBlock_paymentStep (positive : preset.PaymentQuorumPositive)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : BuilderDebtCovered state gloas)
    (bidAt : ValuedBidAtLatestBlock state gloas)
    (validatorsFit : after.validators.data.size ≤ 2 ^ 40)
    (buildersFit : (after.builders gloas).data.size ≤ 2 ^ 40)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    ∃ released : List Slot, PaymentStep state after gloas released ∧
      released.Sublist [state.latestBlockHeader.slot] := by
  obtain ⟨parented, released, -, release, step, closes, sub⟩ :=
    processBlock_paymentRelease positive twoSlots holds bidAt validatorsFit buildersFit computed
  exact ⟨released, .of_release_trans release step closes, sub⟩

end EthLib.Consensus

module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtBlock
public import EthLib.Consensus.Proofs.Transition.PaymentReleaseWithdrawals

/-!
# Proofs: a block and the bids it pays

From Gloas the builder of a block pays its proposer through a pending payment.

A block may pay one bid, that of its parent, through the payload of the parent.

The payload of the parent and the header of the block form one step.

That step releases at most the payment of the parent, and that payment is closed after it.

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

/-- A state keeps the fields of the payments of itself. -/
private theorem PaymentFields.refl (state : BeaconState preset fork) : PaymentFields state state :=
  ⟨rfl, rfl, rfl, rfl⟩

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

/-- A builder deposit keeps the fields of the payments. -/
private theorem PaymentFields.of_builderDeposit {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    PaymentFields state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- A builder exit keeps the fields of the payments. -/
private theorem PaymentFields.of_builderExit {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    PaymentFields state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact PaymentFields.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A step that keeps the fields of the payments, after a release, with a header at the slot. -/
private theorem paymentStep_of_fields {gloas : .glamsterdam ≤ fork}
    {mid : BeaconState preset fork} {released : List Slot}
    (release : PaymentRelease state mid gloas released)
    (closedMid : ∀ slot ∈ released, ¬ PaymentInWindow mid gloas slot)
    (kept : PaymentFields mid after) (header : after.latestBlockHeader.slot = state.slot) :
    PaymentStep state after gloas released := by
  have positions := slotPaymentPosition_congr kept.slot
  have read : ∀ position,
      (paymentAt after gloas position).withdrawal = (paymentAt mid gloas position).withdrawal :=
    fun position => by simp only [paymentAt, kept.payments]
  have window : ∀ slot, PaymentInWindow after gloas slot ↔ PaymentInWindow mid gloas slot :=
    fun slot => by simp only [PaymentInWindow, positions, read]
  have late : ∀ slot, PaymentOpen after gloas slot →
      PaymentInWindow after gloas slot ∨ slot = state.slot := by
    rintro slot (inside | ⟨atHeader, -, -, -⟩)
    · exact Or.inl inside
    · exact Or.inr (atHeader.trans header)
  refine ⟨release.nodup, ⟨0, ?_⟩, release.opened, release.past, ?_, ?_, ?_⟩
  · simp [kept.withdrawals, release.queue]
  · intro slot member opened
    rcases late slot opened with inside | atState
    · exact closedMid slot member ((window slot).mp inside)
    · have past := release.past slot member
      rw [atState] at past
      exact absurd past (UInt64.lt_irrefl _)
  · intro slot opened
    rcases late slot opened with inside | atState
    · exact release.noReopen slot (Or.inl ((window slot).mp inside))
    · exact Or.inr (atState ▸ UInt64.le_refl _)
  · rw [kept.slot]
    exact release.forward

/-- From Gloas, the payload of the parent and the header of a block release at most the parent.

They release the payment of the parent's slot or nothing, and each released payment is closed.

The parent payment must have no weight, and pay the latest bid or have no amount.

A latest bid with a value must be at the slot of the parent. -/
theorem processParentHeader_paymentStep {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} {parented : BeaconState preset fork}
    (fresh : ParentPaymentFresh state gloas) (bidAt : ValuedBidAtLatestBlock state gloas)
    (parentOk : Consensus.processParentExecutionPayload config checks state gloas block.body =
      .ok parented)
    (headedOk : processBlockHeader parented block = .ok after) :
    ∃ released : List Slot, PaymentStep state after gloas released ∧
      released.Sublist [state.latestBlockHeader.slot] := by
  have inputs := payloadInputs_processParentExecutionPayload parentOk
  have slot : parented.slot = state.slot := inputs.slot
  have header : parented.latestBlockHeader = state.latestBlockHeader := inputs.latestBlockHeader
  obtain ⟨sameSlot, newer, -⟩ := processBlockHeader_checks headedOk
  have older : state.latestBlockHeader.slot < state.slot := by
    rw [← slot, ← header]
    exact sameSlot ▸ newer
  have atSlot : block.slot = state.slot := sameSlot.trans slot
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
  rcases processParentExecutionPayload_ok parentOk with ⟨-, -, rfl⟩ |
    ⟨-, settled, deposited, withdrawn, consolidated, builderDeposited, exited, bits, settledOk,
      depositsOk, withdrawalsOk, consolidationsOk, buildersOk, exitsOk, -, rfl⟩
  · exact ⟨[], .of_release (processBlockHeader_release headedOk) nofun, List.nil_sublist _⟩
  obtain ⟨released, release, sub, -, closed⟩ := settleParentPayment_release older fresh bidAt
    settledOk
  have frame :=
    (BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processDepositRequest ok)
      depositsOk).trans <|
    (BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    BuilderFrame.foldlM (fun _ _ _ ok => builderFrame_processConsolidationRequest ok)
      consolidationsOk
  have deposited := foldlM_ok_invariant (PaymentFields consolidated)
    (fun _ _ _ before ok => before.trans (.of_builderDeposit ok)) (PaymentFields.refl _) buildersOk
  have exits := foldlM_ok_invariant (PaymentFields builderDeposited)
    (fun _ _ _ before ok => before.trans (.of_builderExit ok)) (PaymentFields.refl _) exitsOk
  have kept := (PaymentFields.of_frame frame).trans (deposited.trans exits)
  refine ⟨released, paymentStep_of_fields release (fun paid member => ?_)
    ⟨kept.slot, kept.payments, kept.withdrawals, kept.bid⟩ atSlot, sub⟩
  rw [List.mem_singleton.mp (sub.subset member)]
  exact closed

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
  obtain ⟨parented, headed, withdrawn, bidded, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, votedFrame, operatedOk, syncedFrame, grows, size⟩ :=
    processBlock_gloas_steps gloas computed
  obtain ⟨released, first, sub⟩ :=
    processParentHeader_paymentStep holds.parentFresh bidAt parentOk headedOk
  obtain ⟨settled, placed, started⟩ := holds.headed parentOk headedOk
  have parentInputs := payloadInputs_processParentExecutionPayload parentOk
  have withdrawnInputs := payloadInputs_processWithdrawals withdrawnOk
  have bidInputs := payloadInputs_processExecutionPayloadBid biddedOk
  have paid := settled.processWithdrawals (Nat.le_trans grows validatorsFit)
    (by rw [size]; exact buildersFit) (getCurrentEpoch_ne_farFuture twoSlots headed) withdrawnOk
  -- The header keeps the slot and the latest bid of the parent payload.
  have headedSlot : headed.slot = state.slot := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact parentInputs.slot
  have headedBid : headed.latestExecutionPayloadBid = state.latestExecutionPayloadBid := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    exact parentInputs.latestExecutionPayloadBid
  have older : state.latestBlockHeader.slot < state.slot := by
    obtain ⟨sameSlot, newer, -⟩ := processBlockHeader_checks headedOk
    rw [← parentInputs.slot, ← parentInputs.latestBlockHeader, ← sameSlot]
    exact newer
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
  exact ⟨released,
    (((((first.trans_nil (processWithdrawals_paymentStep withdrawnOk)).trans_nil
      (.of_release (processExecutionPayloadBid_release positive fresh biddedOk) nofun)).trans_nil
      (.of_release (.of_frame votedFrame) nofun)).trans_nil
      (.of_release (.of_cancel votedHolds.parentFresh
        (PaymentCancel.processOperations operatedOk)) nofun)).trans_nil
      (.of_release (.of_frame syncedFrame) nofun)), sub⟩

end EthLib.Consensus

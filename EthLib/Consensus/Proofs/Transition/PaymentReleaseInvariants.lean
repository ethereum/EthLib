module

public import EthLib.Consensus.Proofs.Transition.BuilderDebtBlock
public import EthLib.Consensus.Proofs.Transition.PaymentRelease

/-!
# Proofs: the facts on the payments that a chain keeps

From Gloas the builder of a block pays its proposer through a pending payment.

The steps that pay a bid assume a few facts on the state, which each step of a chain keeps.

A latest bid with a value is at the slot of the latest block.

The upgrade to Gloas starts with a latest bid of no value.

A slot keeps the latest bid and the slot of the latest block.

A block makes its own bid the latest one, at its own slot.

A payment with weight has an amount.

The upgrade to Gloas starts with no payment.

Only an attestation adds weight to a payment, and only to a payment with an amount.

The epoch step moves the payments of the second half of the window to the first.

In the genesis epoch, the first half of the window is empty.

A block adds a bid only in the second half, and otherwise empties a payment or weighs one.

The last slot of the genesis epoch leaves it.

The upgrade to Heze carries each fact over.

[EIP-7732] adds the builders, their bids and their payments.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-! ## The latest bid -/

/-- The upgrade to Gloas starts with a latest bid of no value. -/
theorem valuedBidAtLatestBlock_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    ValuedBidAtLatestBlock post (by decide) := fun positive =>
  absurd ((upgradeToGloas_builderFields computed).2.2 ▸ positive) (by decide)

/-- The upgrade to Heze keeps the latest bid at the latest block. -/
theorem ValuedBidAtLatestBlock.upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {post : BeaconState preset .hegota} (holds : ValuedBidAtLatestBlock pre (by decide))
    (computed : upgradeToHeze config pre = .ok post) :
    ValuedBidAtLatestBlock post (by decide) := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  exact holds

/-- From Gloas, one slot keeps a latest bid with a value at the slot of the latest block. -/
theorem ValuedBidAtLatestBlock.advanceSlot {gloas : .glamsterdam ≤ fork}
    (holds : ValuedBidAtLatestBlock state gloas)
    (computed : advanceSlot config checks state = .ok after) :
    ValuedBidAtLatestBlock after gloas := by
  obtain ⟨cached, cachedOk, -, -, header, -, bid, -⟩ := advanceSlot_cachedRoots computed
  have frame := builderFrame_processSlot cachedOk
  exact holds.of_fields ((congrArg BeaconBlockHeader.slot header).trans frame.headerSlot)
    (bid.trans frame.bid)

/-- From Gloas, after a block, the latest bid is at the slot of the latest block.

It holds whatever the value of the bid. -/
theorem latestExecutionPayloadBid_slot_processBlock (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    (after.latestExecutionPayloadBid gloas).slot = after.latestBlockHeader.slot := by
  obtain ⟨_, _, _, _, _, -, headedOk, withdrawnOk, biddedOk, -, -, -, -⟩ :=
    processBlock_steps gloas computed
  obtain ⟨-, -, atSlot, -⟩ := checkExecutionPayloadBid_ok_iff.mp
    (processExecutionPayloadBid_ok biddedOk).1
  obtain ⟨blockSlot, -⟩ := processBlockHeader_checks headedOk
  obtain ⟨_, -, header⟩ := latestBlockHeader_processBlock computed
  rw [latestExecutionPayloadBid_processBlock gloas computed, header]
  refine atSlot.trans ?_
  exact ((payloadInputs_processWithdrawals withdrawnOk).slot.trans
    (payloadInputs_processBlockHeader headedOk).slot).trans blockSlot.symm

/-- From Gloas, a block puts the latest bid at the slot of the latest block.

It needs no hypothesis on the state before the block. -/
theorem ValuedBidAtLatestBlock.processBlock (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    ValuedBidAtLatestBlock after gloas :=
  fun _ => latestExecutionPayloadBid_slot_processBlock gloas computed

/-! ## The weights -/

/-- The epoch step of the payments keeps an amount for each payment with weight. -/
private theorem WeightedPaymentsFunded.processBuilderPendingPayments
    {gloas : .glamsterdam ≤ fork} (holds : WeightedPaymentsFunded state gloas)
    (computed : processBuilderPendingPayments state gloas = .ok after) :
    WeightedPaymentsFunded after gloas := by
  obtain ⟨-, -, -, payments⟩ := processBuilderPendingPayments_spec computed
  intro position weighted
  by_cases early : position < preset.SLOTS_PER_EPOCH.toNat
  · rw [paymentAt_shiftPayments_early payments early] at weighted ⊢
    exact holds _ weighted
  · rw [paymentAt_shiftPayments_late payments (Nat.le_of_not_lt early)] at weighted
    exact absurd weighted (UInt64.lt_irrefl 0)

/-- The payment of the parent and its requests keep each payment, or empty it. -/
private theorem paymentAt_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after)
    (position : Nat) :
    paymentAt after gloas position = paymentAt state gloas position ∨
      paymentAt after gloas position = .empty := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settled, _, _, _, _, exited, _, settledOk, depositsOk, withdrawalsOk,
      consolidationsOk, buildersOk, exitsOk, -, rfl⟩
  · exact .inl rfl
  -- The requests keep the payments, and the payment of the parent empties at most one.
  have frame := builderFrame_validatorRequests depositsOk withdrawalsOk consolidationsOk
  have kept := (builderRequests_paymentFields buildersOk exitsOk).2.1.trans frame.payments
  change paymentAt exited gloas position = _ ∨ paymentAt exited gloas position = _
  rw [show paymentAt exited gloas position = paymentAt settled gloas position by
    simp only [paymentAt, kept]]
  exact paymentAt_settleParentPayment settledOk position

/-- Weighing a payment adds weight only to a payment with an amount, and keeps each amount. -/
private theorem WeightedPaymentsFunded.recordPaymentWeight {gloas : .glamsterdam ≤ fork}
    {data : AttestationData} {current : Bool} {before updated : EpochParticipation preset fork}
    {attesters : List ValidatorIndex} (holds : WeightedPaymentsFunded state gloas)
    (computed : recordPaymentWeight state gloas data current before updated attesters = .ok after) :
    WeightedPaymentsFunded after gloas := by
  by_cases zero : (paymentAt state gloas
      (attestationPaymentPosition preset current data.slot)).withdrawal.amount = 0
  · rw [recordPaymentWeight_of_amount_eq_zero computed zero]
    exact holds
  intro position weighted
  rw [paymentAt_recordPaymentWeight_withdrawal computed position]
  by_cases weighed : position = attestationPaymentPosition preset current data.slot
  · rw [weighed]
    exact UInt64.pos_iff_ne_zero.mpr zero
  · rw [paymentAt_recordPaymentWeight_other computed weighed] at weighted
    exact holds position weighted

/-- The operations of a block keep an amount for each payment with weight. -/
private theorem WeightedPaymentsFunded.processOperations {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (holds : WeightedPaymentsFunded state gloas)
    (computed : processOperations config checks state body parentSlot = .ok after) :
    WeightedPaymentsFunded after gloas :=
  processOperations_of_steps (gloas := gloas)
    (fun first second => WeightedPaymentsFunded first gloas → WeightedPaymentsFunded second gloas)
    (fun one two kept => two (one kept)) (fun frame kept => kept.of_frame frame)
    (fun slashed kept => kept.of_writes (paymentWrites_slashValidator slashed))
    (fun weighed kept => kept.recordPaymentWeight weighed) computed holds

/-- The upgrade to Gloas starts with an amount for each payment with weight, as none has weight. -/
theorem weightedPaymentsFunded_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    WeightedPaymentsFunded post (by decide) := fun position weighted => by
  rw [paymentAt_of_replicate (upgradeToGloas_builderFields computed).1] at weighted
  exact absurd weighted (UInt64.lt_irrefl 0)

/-- The upgrade to Heze keeps an amount for each payment with weight. -/
theorem WeightedPaymentsFunded.upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {post : BeaconState preset .hegota} (holds : WeightedPaymentsFunded pre (by decide))
    (computed : upgradeToHeze config pre = .ok post) :
    WeightedPaymentsFunded post (by decide) := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  exact holds

/-- From Gloas, one slot keeps an amount for each payment with weight.

The epoch step moves the second half of the window to the first, and empties the second half. -/
theorem WeightedPaymentsFunded.advanceSlot {gloas : .glamsterdam ≤ fork}
    (holds : WeightedPaymentsFunded state gloas)
    (computed : advanceSlot config checks state = .ok after) :
    WeightedPaymentsFunded after gloas := by
  obtain ⟨next, cached, -, -, cachedFrame, ⟨-, rfl⟩ |
    ⟨-, pending, paid, -, before, paidOk, tail⟩⟩ :=
      advanceSlot_builderSplit (gloas := gloas) computed
  · exact (holds.of_frame cachedFrame :)
  · exact (((holds.of_frame cachedFrame).of_frame before).processBuilderPendingPayments
      paidOk).of_frame tail

/-- From Gloas, a block rewrites the payments up to its operations.

Its operations then run, and its last steps keep the builder fields. -/
theorem processBlock_paymentWrites (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    ∃ voted operated, PaymentWrites state voted gloas ∧
      processOperations config checks voted block.body state.latestBlockHeader.slot =
        .ok operated ∧
      BuilderFrame operated after := by
  obtain ⟨parented, headed, withdrawn, bidded, voted, operated, _, parentOk, headedOk,
    withdrawnOk, biddedOk, votedFrame, operatedOk, syncedFrame, -, -⟩ :=
    processBlock_gloas_steps gloas computed
  have parentWrites : PaymentWrites state parented gloas :=
    ⟨(payloadInputs_processParentExecutionPayload parentOk).slot, fun position =>
      (paymentAt_processParentExecutionPayload parentOk position).imp_right .inl⟩
  have headedWrites : PaymentWrites parented headed gloas := by
    obtain ⟨_, -, rfl⟩ := processBlockHeader_eq headedOk
    exact ⟨rfl, fun _ => .inl rfl⟩
  have withdrawnWrites : PaymentWrites headed withdrawn gloas :=
    ⟨(payloadInputs_processWithdrawals withdrawnOk).slot, fun position =>
      .inl (by simp only [paymentAt, processWithdrawals_payments gloas withdrawnOk])⟩
  have biddedWrites : PaymentWrites withdrawn bidded gloas :=
    ⟨(payloadInputs_processExecutionPayloadBid biddedOk).slot, fun position =>
      (paymentAt_processExecutionPayloadBid biddedOk position).imp_right .inr⟩
  exact ⟨voted, operated, parentWrites.trans <| headedWrites.trans <| withdrawnWrites.trans <|
    biddedWrites.trans (.of_frame votedFrame), operatedOk, syncedFrame⟩

/-- From Gloas, a block keeps an amount for each payment with weight.

The payment of the parent and the slashings empty payments.

The bid records a payment of no weight.

An attestation adds weight only to a payment with an amount, and keeps each amount. -/
theorem WeightedPaymentsFunded.processBlock {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : WeightedPaymentsFunded state gloas)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    WeightedPaymentsFunded after gloas := by
  obtain ⟨_, _, writes, operatedOk, syncedFrame⟩ := processBlock_paymentWrites gloas computed
  exact ((holds.of_writes writes).processOperations operatedOk).of_frame syncedFrame

/-! ## The genesis epoch -/

/-- The upgrade to Gloas starts with no payment, so the first half of the window is empty. -/
theorem genesisFirstHalfEmpty_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    GenesisFirstHalfEmpty post (by decide) := fun _ position _ =>
  paymentAt_of_replicate (upgradeToGloas_builderFields computed).1 position

/-- The upgrade to Heze keeps the first half of the genesis window empty. -/
theorem GenesisFirstHalfEmpty.upgradeToHeze {pre : BeaconState preset .glamsterdam}
    {post : BeaconState preset .hegota} (holds : GenesisFirstHalfEmpty pre (by decide))
    (computed : upgradeToHeze config pre = .ok post) :
    GenesisFirstHalfEmpty post (by decide) := by
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp computed
  exact holds

/-- From Gloas, one slot keeps the first half of the genesis window empty.

A slot inside the genesis epoch keeps the window, and the last one leaves that epoch. -/
theorem GenesisFirstHalfEmpty.advanceSlot {gloas : .glamsterdam ≤ fork}
    (holds : GenesisFirstHalfEmpty state gloas)
    (computed : advanceSlot config checks state = .ok after) :
    GenesisFirstHalfEmpty after gloas := by
  obtain ⟨next, cached, sum, -, cachedFrame, ⟨inside, rfl⟩ |
    ⟨boundary, pending, paid, -, -, -, tail⟩⟩ := advanceSlot_builderSplit (gloas := gloas) computed
  · intro genesis
    refine (holds.of_frame cachedFrame :) (UInt64.toNat_inj.mp ?_)
    have epoch := congrArg UInt64.toNat genesis
    rw [getCurrentEpoch_toNat] at epoch
    rw [getCurrentEpoch_toNat, cachedFrame.slot, ← nextSlot_epoch_of_inside sum inside]
    exact epoch
  · -- The last slot of an epoch leaves the genesis epoch.
    intro genesis
    have epoch := congrArg UInt64.toNat genesis
    rw [getCurrentEpoch_toNat, tail.slot] at epoch
    simp only [GENESIS_EPOCH, UInt64.toNat_zero] at epoch
    exact absurd ((nextSlot_epoch_of_boundary sum boundary).symm.trans epoch)
      (Nat.succ_ne_zero _)

/-- The operations of a block keep the first half of the genesis window empty. -/
private theorem GenesisFirstHalfEmpty.processOperations {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (holds : GenesisFirstHalfEmpty state gloas)
    (computed : processOperations config checks state body parentSlot = .ok after) :
    GenesisFirstHalfEmpty after gloas :=
  processOperations_of_steps (gloas := gloas)
    (fun first second => GenesisFirstHalfEmpty first gloas → GenesisFirstHalfEmpty second gloas)
    (fun one two kept => two (one kept)) (fun frame kept => kept.of_frame frame)
    (fun slashed kept => kept.of_writes (paymentWrites_slashValidator slashed))
    (fun weighed kept genesis position early =>
      paymentAt_recordPaymentWeight_empty weighed (kept (by
        rwa [getCurrentEpoch, congrArg BeaconState.slot (recordPaymentWeight_eq weighed)]
          at genesis) position early))
    computed holds

/-- From Gloas, a block keeps the first half of the genesis window empty.

The bid writes its payment in the second half, and the other steps empty a payment or weigh it.

An attestation adds weight only to a payment with an amount, which an empty payment lacks. -/
theorem GenesisFirstHalfEmpty.processBlock {gloas : .glamsterdam ≤ fork}
    {block : BeaconBlock preset fork} (holds : GenesisFirstHalfEmpty state gloas)
    (computed : Consensus.processBlock config checks engine state block = .ok after) :
    GenesisFirstHalfEmpty after gloas := by
  obtain ⟨_, _, writes, operatedOk, syncedFrame⟩ := processBlock_paymentWrites gloas computed
  exact ((holds.of_writes writes).processOperations operatedOk).of_frame syncedFrame

end EthLib.Consensus

module

public import EthLib.Consensus.Proofs.BuilderApi.GloasBid
public import EthLib.Consensus.Proofs.Transition.Payload

/-!
# Proofs: an accepted Gloas bid records its payment to the expected fee recipient

From Gloas a proposer validates a builder's bid against the fee recipient that it expects.

When a block carries that bid, the bid records a pending payment of its value to that fee recipient.

A bid of no value records no payment.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base

variable {preset : Preset} {fork : Base.Fork} {config config' : Config}
  {checks checks' : SignatureChecks} {state state' post : BeaconState preset fork}
  {gloas : .glamsterdam ≤ fork} {preferences : ProposerPreferences} {parentGasLimit : UInt64}
  {signed : SignedExecutionPayloadBid preset fork} {feeRecipient : ExecutionAddress}

/-- A validated bid of positive value, once processed in a block, records its pending payment.

It pays the bid's value from the bid's builder to the fee recipient that the proposer expected.

No hypothesis relates the state of the validation to the state of the block. -/
theorem pendingPayment_of_validateBid
    (valid : validateBid config checks state gloas preferences parentGasLimit signed feeRecipient =
      .ok true)
    (processed : processExecutionPayloadBid config' checks' state' gloas signed = .ok post)
    (positive : 0 < signed.message.value) :
    ∃ position proposer, bidPaymentPosition preset signed.message.slot = .ok position ∧
      getBeaconProposerIndex state' = .ok proposer ∧
      (post.builderPendingPayments gloas)[position] =
        ⟨0, ⟨feeRecipient, signed.message.value, signed.message.builderIndex⟩, proposer⟩ := by
  obtain ⟨-, recorded, record, rfl⟩ := processExecutionPayloadBid_ok processed
  -- The proposer's check gives only that the bid names the expected fee recipient.
  --
  -- The fee recipient comes from the bid, which both steps read.
  have recipient := (validateBid_ok_true_iff.mp valid).2.2.1
  unfold recordBidPayment at record
  simp only [positive, ↓reduceIte] at record
  -- The payment names the proposer of the slot of the block.
  obtain ⟨proposer, hp, rest⟩ := bind_ok_iff.mp record
  -- The payment sits at the position of the bid's slot in the second half of the list.
  --
  -- That half holds the payments of the current epoch.
  obtain ⟨position, hpos, kept⟩ := bind_ok_iff.mp rest
  have hp' : getBeaconProposerIndex state' = .ok proposer := by
    unfold liftAccessor at hp
    cases h : getBeaconProposerIndex state' <;> simp_all [Except.mapError]
  refine ⟨position, proposer, hpos, hp', ?_⟩
  rw [← Except.ok.inj kept]
  -- The payment has no weight yet.
  simp [bidPayment, recipient]

/-- A bid of no value, once processed in a block, leaves the pending payments as they were. -/
theorem builderPendingPayments_processExecutionPayloadBid_of_value_eq_zero
    (processed : processExecutionPayloadBid config' checks' state' gloas signed = .ok post)
    (free : signed.message.value = 0) :
    post.builderPendingPayments gloas = state'.builderPendingPayments gloas := by
  obtain ⟨-, recorded, record, rfl⟩ := processExecutionPayloadBid_ok processed
  rw [recordBidPayment_of_value_eq_zero free] at record
  rw [← Except.ok.inj record]

end EthLib.Consensus.BuilderApi

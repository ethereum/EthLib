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

The upgrade to Heze carries the fact over.

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
  obtain ⟨_, -, header⟩ := latestBlockHeader_processBlock gloas computed
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

end EthLib.Consensus

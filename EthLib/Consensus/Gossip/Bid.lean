module

public import EthLib.Consensus.Gossip.Payload
public import EthLib.Consensus.Gossip.ProposerPreferences
public import EthLib.Base.GasLimit

/-!
# `Consensus.Gossip.Bid`

From Gloas: gossip validation of the bids of builders.

A builder offers to give the payload of a slot for a value, on top of a parent block and payload.

A node forwards only the best bid for each slot and parent, and one bid of each builder there.

The bid must suit the preferences that the proposer of the slot published.

Those preferences fix the address of the fees and the target of the gas limit.

The bid must also build on the head of the fork choice, or on its parent.

The builder must be active, able to pay the bid, and not about to exit.

Some steps of the rule can fail, such as a root, or an addition out of range.

Such a failure is an error rather than an outcome.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Networking.Gossip

variable {preset : Preset} {fork : Fork}

/-! ## Helpers -/

/-- Whether the clock is in a slot or in the slot before it, with the gossip disparity.

Slot 0 has no slot before it, and that is an error. -/
def Store.isCurrentOrNextSlot (config : Config) (store : Store preset fork) (slot : Slot)
    (currentTimeMs : UInt64) : Except ForkChoiceError Bool := do
  let current ← store.isCurrentSlot config slot currentTimeMs
  let previous ← (subChecked slot 1).mapError .arith
  let next ← store.isCurrentSlot config previous currentTimeMs
  return current || next

/-- Whether a gas limit is the one that moves from the parent's limit toward a target.

A block may change the gas limit by less than a 1024th of the parent's limit.

So the limit is the target when the target is that close, and else the nearest bound.

An upper bound past the 64-bit range is an error. -/
def isGasLimitTargetCompatible (parentGasLimit gasLimit targetGasLimit : UInt64) :
    Except ArithError Bool := do
  let _ ← addChecked parentGasLimit (saturatingSub (parentGasLimit / 1024) 1)
  return gasLimit.toNat == gasLimitToward parentGasLimit.toNat targetGasLimit.toNat

/-- Whether a bid builds on the branch of the head of the fork choice.

A bid on the parent of the head block, and on the payload that the head block builds on, does.

Otherwise the bid must build on the head block itself.

Then its payload must be the head's own payload when a proposer would build on the full head.

Else it must be the payload that the head block builds on. -/
def Store.isBidCompatibleWithHead (config : Config) (store : Store preset fork)
    (gloas : .glamsterdam ≤ fork) (bid : ExecutionPayloadBid preset fork) :
    Except ForkChoiceError Bool := do
  let head ← store.getHead config
  let headBlock ← store.block head.root
  let headBid := (headBlock.body.signedExecutionPayloadBid gloas).message
  let onParentPayload := bid.parentBlockHash == headBid.parentBlockHash
  if bid.parentBlockRoot == headBlock.parentRoot && onParentPayload then return true
  if bid.parentBlockRoot != head.root then return false
  if ← store.shouldBuildOnFull gloas head bid.slot then
    return bid.parentBlockHash == headBid.blockHash
  return onParentPayload

/-- The best value of a valid bid for a slot, a parent payload and a parent block, if any. -/
def Seen.bestExecutionPayloadBidFor (seen : Seen) (key : Slot × Hash32 × Root) : Option Gwei :=
  seen.bestExecutionPayloadBids.lookup key

/-- The gas limit of the payload of a valid envelope, by the hash of the payload, if any. -/
def Seen.executionPayloadGasLimitFor (seen : Seen) (blockHash : Hash32) : Option UInt64 :=
  seen.executionPayloadGasLimits.lookup blockHash

/-- Whether the payload of the parent of a bid asks to exit its builder.

That holds only when the bid builds on the latest payload that the state knows.

That payload is the envelope that the store keeps for the parent block.

A request asks to exit the builder when it names its key and comes from its address.

A missing envelope is an error. -/
def builderMayExit (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (state : BeaconState preset fork) (bid : ExecutionPayloadBid preset fork) (builder : Builder) :
    Except ForkChoiceError Bool := do
  if bid.parentBlockHash != (state.latestExecutionPayloadBid gloas).blockHash then return false
  let some envelope := (store.payloads gloas)[bid.parentBlockRoot]?
    | throw (.payloadNotVerified bid.parentBlockRoot)
  return (envelope.executionRequests.builderExits gloas).data.toList.any fun request =>
    request.pubkey == builder.pubkey && request.sourceAddress == builder.executionAddress

/-- From Heze: whether the bits of a bid cover the timely inclusion lists that the node holds.

The lists are those of the slot before the bid, for the dependent root on the chain of its parent.

The committee of that slot comes from the state of the parent, advanced to the slot of the bid.

A bid at slot 0 has no slot before it, and that is an error.

Before Heze a bid has no such bits, and the check accepts. -/
def bidInclusionListOutcome (store : Store preset fork) (state : BeaconState preset fork)
    (bid : ExecutionPayloadBid preset fork) : Except ForkChoiceError ValidationResult :=
  if heze : .hegota ≤ fork then do
    let previous ← (subChecked bid.slot 1).mapError .arith
    let committee ← (getInclusionListCommittee state previous).mapError .accessor
    let dependentRoot ←
      store.getShufflingDependentRoot bid.parentBlockRoot (computeEpochAtSlot preset previous)
    return ignoreUnless ((store.inclusionLists heze).isInclusive committee previous dependentRoot
      (bid.inclusionListBits heze) true) "bid's inclusion list bits is not inclusive"
  else return .accept

/-! ## The topic -/

/-- From Gloas: the checks of a signed bid on its topic, at a time in ms.

The first valid bid of a builder for a slot, a parent payload and a parent block passes.

A later bid with the same key is ignored, and so is a bid whose value does not beat the best one.

The slot must be the current one or the next, by the clock.

The bid must pay nothing on the execution layer, and must not name its parent payload as its own.

Its blob commitments must be within the limit of its epoch.

Its parent block must be known with its state, and before its slot.

Its slot must be within the lookahead of proposers of that state.

The preferences of the proposer must be known, and the bid must suit them.

The parent payload must be known, and the gas limit must move toward the target of the proposer.

The bid must build on the branch of the head, with the RANDAO mix of the parent state.

That state is advanced to the slot of the bid, and the builder is read there.

It must be an active payload builder, able to pay the value, and not exiting by the parent payload.

From Heze its inclusion list bits must cover the timely lists that the node holds.

Last, the builder must have signed the bid. -/
def validateExecutionPayloadBid (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let bid := signed.message
  (ignoreUnless (!seen.executionPayloadBids.contains
      (bid.slot, bid.parentBlockHash, bid.parentBlockRoot, bid.builderIndex))
    "already seen valid bid for this slot, parent, and builder").andThenM fun _ =>
  (ignoreUnless ((seen.bestExecutionPayloadBidFor
      (bid.slot, bid.parentBlockHash, bid.parentBlockRoot)).all (· < bid.value))
    "bid is not the highest value bid seen for this slot and parent").andThenM fun _ => do
  let timely ← store.isCurrentOrNextSlot config bid.slot currentTimeMs
  (ignoreUnless timely "bid's slot is not the current or next slot").andThenM fun _ =>
  (rejectUnless (bid.executionPayment == 0) "bid's execution payment must be zero").andThenM
    fun _ =>
  (rejectUnless (bid.blockHash != bid.parentBlockHash)
    "bid's block hash equals its parent block hash").andThenM fun _ =>
  let proposalEpoch := computeEpochAtSlot preset bid.slot
  (rejectUnless (bid.blobKzgCommitments.data.size ≤
      (config.getBlobParameters proposalEpoch).maxBlobsPerBlock.toNat)
    "too many blob kzg commitments").andThenM fun _ =>
  match store.blocks[bid.parentBlockRoot]? with
  | none => return .ignore "bid's parent block root is not a known beacon block"
  | some parent =>
  (rejectUnless (parent.slot < bid.slot) "bid's slot is not higher than its parent's slot").andThenM
    fun _ =>
  match store.blockStates[bid.parentBlockRoot]? with
  | none => return .ignore "bid's parent block post-state is unavailable"
  | some state => do
  let lookahead ← (addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD).mapError .arith
  (ignoreUnless (proposalEpoch ≤ lookahead)
    "bid's slot is past the parent's proposer lookahead").andThenM fun _ => do
  let dependentRoot ← store.getShufflingDependentRoot bid.parentBlockRoot proposalEpoch
  match seen.proposerPreferencesFor (bid.slot, dependentRoot) with
  | none => return .ignore "matching proposer preferences have not been seen"
  | some preferences =>
  (ignoreUnless (bid.feeRecipient == preferences.feeRecipient)
    "bid's fee recipient does not match the proposer's preference").andThenM fun _ =>
  match seen.executionPayloadGasLimitFor bid.parentBlockHash with
  | none => return .ignore "bid's parent block hash is not a known execution payload"
  | some parentGasLimit => do
  let compatible ← (isGasLimitTargetCompatible parentGasLimit bid.gasLimit
    preferences.targetGasLimit).mapError .arith
  (ignoreUnless compatible "bid's gas limit is not compatible with the proposer's target").andThenM
    fun _ => do
  let onHead ← store.isBidCompatibleWithHead config gloas bid
  (ignoreUnless onHead "bid is not compatible with the current head branch").andThenM fun _ => do
  let randao ← (getRandaoMix state (getCurrentEpoch state)).mapError .accessor
  (rejectUnless (bid.prevRandao == randao) "bid's previous randao is incorrect").andThenM
    fun _ => do
  let state ← (processSlots config checks state bid.slot).mapError .transition
  match (state.builders gloas).data[bid.builderIndex.toNat]? with
  | none => return .reject "builder index out of range"
  | some builder =>
  (rejectUnless (builder.version == PAYLOAD_BUILDER_VERSION)
    "builder is not a payload builder").andThenM fun _ => do
  let active ← (isActiveBuilder state gloas bid.builderIndex).mapError .accessor
  (rejectUnless active "builder is not active").andThenM fun _ => do
  let covered ← (canBuilderCoverBid state gloas bid.builderIndex bid.value).mapError .accessor
  (ignoreUnless covered "builder cannot cover bid value").andThenM fun _ => do
  let exiting ← builderMayExit store gloas state bid builder
  (ignoreUnless (!exiting) "builder may exit").andThenM fun _ => do
  (← bidInclusionListOutcome store state bid).andThenM fun _ => do
  let valid ←
    (verifyExecutionPayloadBidSignature config checks state gloas signed).mapError .transition
  return rejectUnless valid "invalid bid signature"

/-- The keys after a valid bid: its slot, parents and builder, and its value as the best one. -/
def Seen.recordExecutionPayloadBid (seen : Seen) (signed : SignedExecutionPayloadBid preset fork) :
    Seen :=
  let bid := signed.message
  { seen with
    executionPayloadBids :=
      (bid.slot, bid.parentBlockHash, bid.parentBlockRoot, bid.builderIndex) ::
        seen.executionPayloadBids
    bestExecutionPayloadBids :=
      ((bid.slot, bid.parentBlockHash, bid.parentBlockRoot), bid.value) ::
        seen.bestExecutionPayloadBids }

end EthLib.Consensus

module

public import EthLib.Base.GasLimit
public import EthLib.Consensus.Gossip.Payload
public import EthLib.Consensus.Gossip.ProposerPreferences

/-!
# `Consensus.Gossip.Bid`

From Gloas: gossip validation of the bids of builders.

A builder offers the payload of a slot for a value, on a parent block and a parent payload.

The comments in the body state each check, in order.

A step that fails, such as a root or an addition out of range, is an error rather than an outcome.
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
  -- The clock is in the slot `s`.
  let current ← store.isCurrentSlot config slot currentTimeMs
  -- Or it is in `s - 1`, so that `s` is the next slot.
  let previous ← (subChecked slot 1).mapError .arith
  let next ← store.isCurrentSlot config previous currentTimeMs
  return current || next

/-- Whether a gas limit is the one that moves from the parent's limit toward a target.

A block may change the gas limit by less than a 1024th of the parent's limit.

So the limit is the target when the target is that close, and else the nearest bound.

An upper bound past the 64-bit range is an error. -/
def isGasLimitTargetCompatible (parentGasLimit gasLimit targetGasLimit : UInt64) :
    Except ArithError Bool := do
  -- For the parent's limit `p`, let `d = max(floor(p / 1024) - 1, 0)`; then `p + d < 2^64`.
  let _ ← addChecked parentGasLimit (saturatingSub (parentGasLimit / 1024) 1)
  -- The gas limit is the target clamped to `[p - d, p + d]`.
  --
  -- The comparison runs on natural numbers, which give the 64-bit result once the bound holds.
  return gasLimit.toNat == gasLimitToward parentGasLimit.toNat targetGasLimit.toNat

/-- Whether a bid builds on the branch of the head of the fork choice. -/
def Store.isBidCompatibleWithHead (config : Config) (store : Store preset fork)
    (gloas : .glamsterdam ≤ fork) (bid : ExecutionPayloadBid preset fork) :
    Except ForkChoiceError Bool := do
  -- The head of the fork choice, its block and the bid of that block.
  let head ← store.getHead config
  let headBlock ← store.block head.root
  let headBid := (headBlock.body.signedExecutionPayloadBid gloas).message
  -- The bid builds on the payload that the head block builds on.
  let onParentPayload := bid.parentBlockHash == headBid.parentBlockHash
  -- A bid on the parent of the head block, and on that payload, is on the branch.
  if bid.parentBlockRoot == headBlock.parentRoot && onParentPayload then return true
  -- Otherwise the bid builds on the head block itself.
  if bid.parentBlockRoot != head.root then return false
  -- When a proposer would build on the full head, the bid builds on the payload of the head.
  if ← store.shouldBuildOnFull gloas head bid.slot then
    return bid.parentBlockHash == headBid.blockHash
  -- Else it builds on the payload that the head block builds on.
  return onParentPayload

/-- The best value of a valid bid for a slot, a parent payload and a parent block, if any. -/
def Seen.bestExecutionPayloadBidFor (seen : Seen) (key : Slot × Hash32 × Root) : Option Gwei :=
  seen.bestExecutionPayloadBids.lookup key

/-- The count of valid bids of a builder for a slot, a parent payload and a parent block. -/
def Seen.executionPayloadBidCount (seen : Seen) (key : Slot × Hash32 × Root × BuilderIndex) :
    Nat :=
  seen.executionPayloadBids.count key

/-- From Gloas: how many bids a builder may have forwarded for each slot and parent.

It is the balance that the builder does not owe, in whole ether. -/
def getBuilderBidLimit (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (index : BuilderIndex) : Except AccessorError UInt64 := do
  let builder ← getBuilder state gloas index
  -- Let `p` be what the builder owes.
  let pending ← getPendingBalanceToWithdrawForBuilder state gloas index
  -- `floor(max(b - p, 0) / 10^9)`, for the balance `b` of the builder.
  return saturatingSub builder.balance pending / ETH_TO_GWEI

/-- The gas limit of the payload of a valid envelope, by the hash of the payload, if any. -/
def Seen.executionPayloadGasLimitFor (seen : Seen) (blockHash : Hash32) : Option UInt64 :=
  seen.executionPayloadGasLimits.lookup blockHash

/-- Whether the payload of the parent of a bid asks to exit its builder.

A missing envelope is an error. -/
def builderMayExit (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (state : BeaconState preset fork) (bid : ExecutionPayloadBid preset fork) (builder : Builder) :
    Except ForkChoiceError Bool := do
  -- The check applies only to a bid on the block hash of the latest bid of the state.
  if bid.parentBlockHash != (state.latestExecutionPayloadBid gloas).blockHash then return false
  -- The payload is the envelope that the store keeps for the parent block.
  let some envelope := (store.payloads gloas)[bid.parentBlockRoot]?
    | throw (.payloadNotVerified bid.parentBlockRoot)
  -- An exit request of that envelope names the key of the builder and comes from its address.
  return (envelope.executionRequests.builderExits gloas).data.toList.any fun request =>
    request.pubkey == builder.pubkey && request.sourceAddress == builder.executionAddress

/-- From Heze: whether the bits of a bid cover the timely inclusion lists that the node holds.

A bid at slot 0 has no slot before it, and that is an error. -/
def bidInclusionListOutcome (store : Store preset fork) (state : BeaconState preset fork)
    (bid : ExecutionPayloadBid preset fork) : Except ForkChoiceError ValidationResult :=
  if heze : .hegota ≤ fork then do
    -- The slot `s - 1` before the slot `s` of the bid.
    let previous ← (subChecked bid.slot 1).mapError .arith
    -- The inclusion list committee of `s - 1`, in the given state, advanced to `s` by the caller.
    let committee ← (getInclusionListCommittee state previous).mapError .accessor
    -- The dependent root of the epoch of `s - 1`, on the chain of the parent block.
    let dependentRoot ←
      store.getShufflingDependentRoot bid.parentBlockRoot (computeEpochAtSlot preset previous)
    -- IGNORE unless the bits of the bid set each member whose timely list the node holds.
    --
    -- Those lists are for `s - 1` and that root.
    return ignoreUnless ((store.inclusionLists heze).isInclusive committee previous dependentRoot
      (bid.inclusionListBits heze) true) "bid's inclusion list bits is not inclusive"
  -- Before Heze a bid has no such bits, and the check accepts.
  else return .accept

/-! ## The topic -/

/-- From Gloas: the checks of a signed bid on its topic, at a time in ms.

The parents of a bid are its parent payload, by hash, and its parent block, by root.

The proposer of the slot should still weigh a higher bid past the limit, without forwarding it. -/
def validateExecutionPayloadBid (config : Config) (checks : SignatureChecks) (seen : Seen)
    (store : Store preset fork) (gloas : .glamsterdam ≤ fork)
    (signed : SignedExecutionPayloadBid preset fork) (currentTimeMs : UInt64) :
    Except ForkChoiceError ValidationResult :=
  let bid := signed.message
  -- IGNORE unless its value beats the best value of a valid bid for its slot and its parents.
  --
  -- Only the highest bid for a slot and a parent is forwarded, as EIP-7732 specifies.
  (ignoreUnless ((seen.bestExecutionPayloadBidFor
      (bid.slot, bid.parentBlockHash, bid.parentBlockRoot)).all (· < bid.value))
    "bid is not the highest value bid seen for this slot and parent").andThenM fun _ => do
  -- IGNORE unless the clock is in its slot or in the slot before it.
  let timely ← store.isCurrentOrNextSlot config bid.slot currentTimeMs
  (ignoreUnless timely "bid's slot is not the current or next slot").andThenM fun _ =>
  -- REJECT unless its execution payment is 0.
  --
  -- A bid carries no execution payment, as EIP-7732 specifies.
  (rejectUnless (bid.executionPayment == 0) "bid's execution payment must be zero").andThenM
    fun _ =>
  -- REJECT when its block hash is its parent block hash.
  (rejectUnless (bid.blockHash != bid.parentBlockHash)
    "bid's block hash equals its parent block hash").andThenM fun _ =>
  -- Let `e` be the epoch of the slot of the bid.
  let proposalEpoch := computeEpochAtSlot preset bid.slot
  -- REJECT unless it commits to at most the most blobs per block of the blob schedule at `e`.
  (rejectUnless (bid.blobKzgCommitments.data.size ≤
      (config.getBlobParameters proposalEpoch).maxBlobsPerBlock.toNat)
    "too many blob kzg commitments").andThenM fun _ =>
  -- IGNORE unless the parent block is known.
  match store.blocks[bid.parentBlockRoot]? with
  | none => return .ignore "bid's parent block root is not a known beacon block"
  | some parent =>
  -- REJECT unless the parent block is at an earlier slot than the bid.
  (rejectUnless (parent.slot < bid.slot) "bid's slot is not higher than its parent's slot").andThenM
    fun _ =>
  -- IGNORE unless the parent block has a state, which it has once the node imports it.
  match store.blockStates[bid.parentBlockRoot]? with
  | none => return .ignore "bid's parent block post-state is unavailable"
  | some state => do
  -- IGNORE unless `e` is at most the current epoch of that state plus `MIN_SEED_LOOKAHEAD`.
  let lookahead ← (addChecked (getCurrentEpoch state) preset.MIN_SEED_LOOKAHEAD).mapError .arith
  (ignoreUnless (proposalEpoch ≤ lookahead)
    "bid's slot is past the parent's proposer lookahead").andThenM fun _ => do
  -- IGNORE unless the node holds the preferences of the proposer for the slot.
  --
  -- They are keyed by the dependent root of `e` on the chain of the parent block.
  --
  -- A bid for a slot without the preferences of its proposer is not forwarded, as EIP-7732 says.
  let dependentRoot ← store.getShufflingDependentRoot bid.parentBlockRoot proposalEpoch
  match seen.proposerPreferencesFor (bid.slot, dependentRoot) with
  | none => return .ignore "matching proposer preferences have not been seen"
  | some preferences =>
  -- IGNORE unless the fee recipient of the bid is the one of the preferences.
  (ignoreUnless (bid.feeRecipient == preferences.feeRecipient)
    "bid's fee recipient does not match the proposer's preference").andThenM fun _ =>
  -- IGNORE unless the node holds a valid envelope whose payload has the parent block hash.
  match seen.executionPayloadGasLimitFor bid.parentBlockHash with
  | none => return .ignore "bid's parent block hash is not a known execution payload"
  | some parentGasLimit => do
  -- IGNORE unless the gas limit moves from the limit of that payload toward the target.
  --
  -- The target is the target gas limit of the preferences.
  let compatible ← (isGasLimitTargetCompatible parentGasLimit bid.gasLimit
    preferences.targetGasLimit).mapError .arith
  (ignoreUnless compatible "bid's gas limit is not compatible with the proposer's target").andThenM
    fun _ => do
  -- IGNORE unless the bid builds on the branch of the head of the fork choice.
  let onHead ← store.isBidCompatibleWithHead config gloas bid
  (ignoreUnless onHead "bid is not compatible with the current head branch").andThenM fun _ => do
  -- REJECT unless its RANDAO mix is the mix of the current epoch of the parent state.
  let randao ← (getRandaoMix state (getCurrentEpoch state)).mapError .accessor
  (rejectUnless (bid.prevRandao == randao) "bid's previous randao is incorrect").andThenM
    fun _ => do
  -- The parent state, advanced through the empty slots up to the slot of the bid.
  let state ← (processSlots config checks state bid.slot).mapError .transition
  -- REJECT unless the builder index names a builder of that state.
  match (state.builders gloas).data[bid.builderIndex.toNat]? with
  | none => return .reject "builder index out of range"
  | some builder =>
  -- REJECT unless the builder is a payload builder, of version `PAYLOAD_BUILDER_VERSION`.
  (rejectUnless (builder.version == PAYLOAD_BUILDER_VERSION)
    "builder is not a payload builder").andThenM fun _ => do
  -- REJECT unless the builder is active.
  let active ← (isActiveBuilder state gloas bid.builderIndex).mapError .accessor
  (rejectUnless active "builder is not active").andThenM fun _ => do
  -- IGNORE unless the builder has fewer valid bids for the slot and parents than its limit.
  let limit ← (getBuilderBidLimit state gloas bid.builderIndex).mapError .accessor
  (ignoreUnless (seen.executionPayloadBidCount
      (bid.slot, bid.parentBlockHash, bid.parentBlockRoot, bid.builderIndex) < limit.toNat)
    "builder has reached its bid limit for this slot and parent").andThenM fun _ => do
  -- IGNORE unless the balance of the builder covers the value of the bid.
  let covered ← (canBuilderCoverBid state gloas bid.builderIndex bid.value).mapError .accessor
  (ignoreUnless covered "builder cannot cover bid value").andThenM fun _ => do
  -- IGNORE when the parent payload asks to exit the builder.
  let exiting ← builderMayExit store gloas state bid builder
  (ignoreUnless (!exiting) "builder may exit").andThenM fun _ => do
  -- From Heze, IGNORE unless the inclusion list bits of the bid cover the timely lists.
  (← bidInclusionListOutcome store state bid).andThenM fun _ => do
  -- REJECT unless the builder signed the bid.
  let valid ←
    (verifyExecutionPayloadBidSignature config checks state gloas signed).mapError .transition
  return rejectUnless valid "invalid bid signature"

/-- The keys after a valid bid: one more bid of its builder, and its value as the best one. -/
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

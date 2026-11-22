module

public import EthLib.Consensus.ForkChoice.Store

/-!
# `Consensus.ForkChoice.PayloadVotes`

From Gloas a block and its payload arrive apart.

So the fork choice chooses between two nodes of one block: with its payload, or without it.

The payload committee of a slot votes on each payload twice.

One vote says whether the payload came on time, the other whether its blob data is available.

A side wins a vote when more than half of the committee casts it.

A node trusts these votes only for a payload that it has verified itself.

For a block from the previous slot, the votes decide between the full and the empty node.

For an older block, the weight of the attestations decides.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

/-- The number of votes that a side must exceed to win: half of the payload committee. -/
def ptcThreshold (preset : Preset) : Nat :=
  -- `floor(PTC_SIZE / 2)`, as EIP-7732 specifies for both votes.
  preset.PTC_SIZE.toNat / 2

/-- Whether more than the threshold of the committee cast a given vote.

A member that has not voted counts for neither side. -/
def ptcMajority {n : Nat} (threshold : Nat) (votes : Vector (Option Bool) n) (value : Bool) :
    Bool :=
  -- The number of members that voted the value exceeds the threshold.
  threshold < votes.toList.countP (· == some value)

variable {preset : Preset} {fork : Fork}

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The votes of the payload committee for a block, from one of the two vote maps.

The store must hold them. -/
def ptcVotes (votes : Std.TreeMap Root (Vector (Option Bool) preset.PTC_SIZE.toNat))
    (root : Root) : Except ForkChoiceError (Vector (Option Bool) preset.PTC_SIZE.toNat) :=
  -- The votes that the map holds for the root, and an error if it holds none.
  match votes[root]? with
  | some found => return found
  | none => throw (.unknownPayloadVotes root)

/-- Whether the payload of a block counts as on time, or as late when `timely` is false.

A payload that the store has not verified is late, whatever the committee votes. -/
def payloadTimeliness (gloas : .glamsterdam ≤ fork) (root : Root) (timely : Bool) :
    Except ForkChoiceError Bool := do
  -- The store holds the timeliness votes for the block.
  let votes ← ptcVotes (store.payloadTimelinessVote gloas) root
  -- An unverified payload counts as late, whatever the votes.
  if !store.isPayloadVerified gloas root then return !timely
  -- Else the asked side wins when more than `floor(PTC_SIZE / 2)` members voted it.
  return ptcMajority (ptcThreshold preset) votes timely

/-- Whether the blob data of a block counts as available, or as missing when `available` is false.

The data of a payload that the store has not verified is missing, whatever the committee votes. -/
def payloadDataAvailability (gloas : .glamsterdam ≤ fork) (root : Root) (available : Bool) :
    Except ForkChoiceError Bool := do
  -- The store holds the data availability votes for the block.
  let votes ← ptcVotes (store.payloadDataAvailabilityVote gloas) root
  -- The data of an unverified payload counts as missing, whatever the votes.
  if !store.isPayloadVerified gloas root then return !available
  -- Else the asked side wins when more than `floor(PTC_SIZE / 2)` members voted it.
  return ptcMajority (ptcThreshold preset) votes available

/-- Whether a node is the full or the empty node of a block from the slot before the current one.

The attestations of the current slot have not yet weighed in on that payload. -/
def isPreviousSlotPayloadDecision (node : ForkChoiceNode) : Except ForkChoiceError Bool := do
  -- The block has the slot `s` with `s + 1` the current slot.
  let block ← store.block node.root
  let next ← (addChecked block.slot 1).mapError .arith
  let isPreviousSlot := next == (← store.getCurrentSlot config)
  -- The node is the empty or the full node of the block, not the pending one.
  return isPreviousSlot && (node.payloadStatus == .empty || node.payloadStatus == .full)

/-- Whether a proposer at a slot builds on the full node of its head, rather than the empty one.

The head must be the full or the empty node of its block. -/
def shouldBuildOnFull (gloas : .glamsterdam ≤ fork) (head : ForkChoiceNode) (slot : Slot) :
    Except ForkChoiceError Bool := do
  -- The head is not a pending node.
  if head.payloadStatus = .pending then throw (.pendingNode head.root)
  -- For a block at slot `s` with `s + 1` not the slot given, the status of the head decides.
  let block ← store.block head.root
  if (← (addChecked block.slot 1).mapError .arith) ≠ slot then
    return head.payloadStatus == .full
  -- For a block of the previous slot, an empty head gives the empty node.
  if head.payloadStatus = .empty then return false
  -- A full head needs a payload that the committee does not find late.
  if ← store.payloadTimeliness gloas head.root false then return false
  -- Nor one whose blob data the committee finds missing.
  if ← store.payloadDataAvailability gloas head.root false then return false
  return true

/-- From Heze: whether the payload of a block is verified and satisfied its inclusion lists.

The store must hold the answer for the block, else it is an error. -/
def isPayloadInclusionListSatisfied (heze : .hegota ≤ fork) (root : Root) :
    Except ForkChoiceError Bool := do
  -- The answer that the store recorded for the block.
  let some satisfied := (store.payloadInclusionListSatisfaction heze)[root]?
    | throw (.unknownInclusionListSatisfaction root)
  -- A payload that is not verified does not count as satisfying them.
  if !store.isPayloadVerified (Nat.le_trans (by decide) heze) root then return false
  return satisfied

/-- Whether to extend the payload of a block from the previous slot.

The block must be from the previous slot. -/
def shouldExtendPayload (gloas : .glamsterdam ≤ fork) (root : Root) :
    Except ForkChoiceError Bool := do
  -- The block has the slot `s` with `s + 1` the current slot.
  let block ← store.block root
  let nextSlot ← (addChecked block.slot 1).mapError .arith
  let currentSlot ← store.getCurrentSlot config
  if nextSlot ≠ currentSlot then throw (.notPreviousSlot root block.slot currentSlot)
  -- A payload that the store has not verified is not extended.
  if !store.isPayloadVerified gloas root then return false
  -- From Heze, neither is a payload that did not satisfy its inclusion lists.
  if heze : .hegota ≤ fork then
    if !(← store.isPayloadInclusionListSatisfied heze root) then return false
  let proposerRoot := store.proposerBoostRoot
  -- A payload that the committee finds on time and with its data available is extended.
  let payloadIsTimely ← store.payloadTimeliness gloas root true
  let payloadDataIsAvailable ← store.payloadDataAvailability gloas root true
  if payloadIsTimely && payloadDataIsAvailable then return true
  -- Otherwise it is extended when no block is boosted.
  if proposerRoot = Vector.replicate 32 0 then return true
  -- Or when the boosted block does not build on this block.
  let proposerBlock ← store.block proposerRoot
  if proposerBlock.parentRoot ≠ root then return true
  -- Else it is extended when the boosted block builds on the full node of this block.
  store.isParentNodeFull proposerBlock

/-- The number that breaks a tie between the nodes of one block, the greater winning.

[EIP-7732] decides the payload of the previous slot by this tiebreaker, not by attestation weight.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#fork-choice-changes
-/
def getPayloadStatusTiebreaker (gloas : .glamsterdam ≤ fork) (node : ForkChoiceNode) :
    Except ForkChoiceError UInt8 := do
  -- In a decision on the payload of the previous slot, the empty node gets 1.
  if ← store.isPreviousSlotPayloadDecision config node then
    if node.payloadStatus = .empty then return 1
    -- The full node gets 2 if the payload extends, else 0.
    if ← store.shouldExtendPayload config gloas node.root then return 2
    return 0
  -- Outside such a decision, the number of the payload status.
  else return node.payloadStatus.code

end Store

end EthLib.Consensus

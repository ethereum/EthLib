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
  preset.PTC_SIZE.toNat / 2

/-- Whether more than the threshold of the committee cast a given vote.

A member that has not voted counts for neither side. -/
def ptcMajority {n : Nat} (threshold : Nat) (votes : Vector (Option Bool) n) (value : Bool) :
    Bool :=
  threshold < votes.toList.countP (· == some value)

variable {preset : Preset} {fork : Fork}

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The votes of the payload committee for a block, from one of the two vote maps.

The store must hold them. -/
def ptcVotes (votes : Std.TreeMap Root (Vector (Option Bool) preset.PTC_SIZE.toNat))
    (root : Root) : Except ForkChoiceError (Vector (Option Bool) preset.PTC_SIZE.toNat) :=
  match votes[root]? with
  | some found => return found
  | none => throw (.unknownPayloadVotes root)

/-- Whether the payload of a block counts as on time, or as late when `timely` is false.

A payload that the store has not verified is late, whatever the committee votes. -/
def payloadTimeliness (gloas : .glamsterdam ≤ fork) (root : Root) (timely : Bool) :
    Except ForkChoiceError Bool := do
  let votes ← ptcVotes (store.payloadTimelinessVote gloas) root
  if !store.isPayloadVerified gloas root then return !timely
  return ptcMajority (ptcThreshold preset) votes timely

/-- Whether the blob data of a block counts as available, or as missing when `available` is false.

The data of a payload that the store has not verified is missing, whatever the committee votes. -/
def payloadDataAvailability (gloas : .glamsterdam ≤ fork) (root : Root) (available : Bool) :
    Except ForkChoiceError Bool := do
  let votes ← ptcVotes (store.payloadDataAvailabilityVote gloas) root
  if !store.isPayloadVerified gloas root then return !available
  return ptcMajority (ptcThreshold preset) votes available

/-- Whether a node is the full or the empty node of a block from the slot before the current one.

The attestations of the current slot have not yet weighed in on that payload. -/
def isPreviousSlotPayloadDecision (node : ForkChoiceNode) : Except ForkChoiceError Bool := do
  let block ← store.block node.root
  let next ← (addChecked block.slot 1).mapError .arith
  let isPreviousSlot := next == (← store.getCurrentSlot config)
  return isPreviousSlot && (node.payloadStatus == .empty || node.payloadStatus == .full)

/-- Whether a proposer at a slot builds on the full node of its head, rather than the empty one.

The head must be the full or the empty node of its block.

For a block older than the previous slot, it follows the status of the head.

For a block of the previous slot, a full head also needs a payload neither late nor missing. -/
def shouldBuildOnFull (gloas : .glamsterdam ≤ fork) (head : ForkChoiceNode) (slot : Slot) :
    Except ForkChoiceError Bool := do
  if head.payloadStatus = .pending then throw (.pendingNode head.root)
  let block ← store.block head.root
  if (← (addChecked block.slot 1).mapError .arith) ≠ slot then
    return head.payloadStatus == .full
  if head.payloadStatus = .empty then return false
  if ← store.payloadTimeliness gloas head.root false then return false
  if ← store.payloadDataAvailability gloas head.root false then return false
  return true

/-- Whether to extend the payload of a block from the previous slot.

The block must be from the previous slot.

A payload that the store has not verified is not extended.

It extends a payload that the committee finds on time and with its data available.

Otherwise it extends unless the boosted block builds on this block and chose its empty node. -/
def shouldExtendPayload (gloas : .glamsterdam ≤ fork) (root : Root) :
    Except ForkChoiceError Bool := do
  let block ← store.block root
  if (← (addChecked block.slot 1).mapError .arith) ≠ (← store.getCurrentSlot config) then
    throw (.notPreviousSlot root)
  if !store.isPayloadVerified gloas root then return false
  let proposerRoot := store.proposerBoostRoot
  let payloadIsTimely ← store.payloadTimeliness gloas root true
  let payloadDataIsAvailable ← store.payloadDataAvailability gloas root true
  if payloadIsTimely && payloadDataIsAvailable then return true
  if proposerRoot = Vector.replicate 32 0 then return true
  let proposerBlock ← store.block proposerRoot
  if proposerBlock.parentRoot ≠ root then return true
  store.isParentNodeFull proposerBlock

/-- The number that breaks a tie between the nodes of one block, the greater winning.

Outside a decision on the payload of the previous slot, it is the number of the payload status.

In such a decision the empty node gets 1, and the full node 2 if the payload extends, else 0. -/
def getPayloadStatusTiebreaker (gloas : .glamsterdam ≤ fork) (node : ForkChoiceNode) :
    Except ForkChoiceError UInt8 := do
  if ← store.isPreviousSlotPayloadDecision config node then
    if node.payloadStatus = .empty then return 1
    if ← store.shouldExtendPayload config gloas node.root then return 2
    return 0
  else return node.payloadStatus.code

end Store

end EthLib.Consensus

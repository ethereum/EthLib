module

public import EthLib.Consensus.ForkChoice.PayloadVotes

/-!
# `Consensus.ForkChoice.Head`

The head of the fork choice: LMD-GHOST from the justified checkpoint, over the viable blocks.

The rule is Algorithm 3.1 of Gasper, and the weight is its Definition 3.4.

The source is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3), section 3.2.

The weight of a node is the effective balance of the validators whose latest vote descends from it.

Only the validators active and not slashed in the justified state count, and no equivocator does.

The timely block of the current slot also boosts every node in its chain.

The boost is a fixed share of the weight of one committee.

A leaf is viable when its justified and finalized checkpoints agree with the store.

The rule walks only through nodes with a viable leaf below them.

A tie between two children goes to the greater root, compared as a string of bytes.

From Gloas a block has three nodes: pending, then empty or full.

The pending node has the empty node as a child, and the full node once the payload is verified.

The empty or full node has as children the pending nodes of the blocks that build on it.

The empty and the full node of a block from the previous slot weigh nothing.

So the payload committee and the proposer decide that payload, and not the attestations.

The boost does not apply on a weak parent of the slot before whose proposer equivocated early.

A tie between the two nodes of one block goes to the greater tiebreaker of the payload status.

The head is never a pending node.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- The index and effective balance of each validator active in the epoch of a state.

A slashed validator is left out, and the indices increase. -/
def unslashedActiveBalances (state : BeaconState preset fork) : List (ValidatorIndex × Gwei) :=
  -- Each validator active in the current epoch and not slashed, with its effective balance.
  state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isActiveValidator validator (getCurrentEpoch state) && !validator.slashed then
      some (index.toUInt64, validator.effectiveBalance)
    else none

/-- A share of the weight of one committee, in percent.

A committee weighs the total balance of the unslashed active validators, over the epoch's slots.
-/
def calculateCommitteeFraction (state : BeaconState preset fork) (committeePercent : UInt64) :
    Except ForkChoiceError Gwei := do
  -- The total balance `T` of the unslashed active validators.
  let total ← (getTotalBalance state ((unslashedActiveBalances state).map (·.1))).mapError .accessor
  -- `floor(floor(T / SLOTS_PER_EPOCH) * p / 100)`, for the percent `p`.
  let committeeWeight ← (divChecked total preset.SLOTS_PER_EPOCH).mapError .arith
  return (← (mulChecked committeeWeight committeePercent).mapError .arith) / 100

/-- The boost of a timely block, from the justified state. -/
def computeProposerScore (config : Config) (state : BeaconState preset fork) :
    Except ForkChoiceError Gwei :=
  -- `PROPOSER_SCORE_BOOST` percent of the weight of one committee.
  calculateCommitteeFraction state config.PROPOSER_SCORE_BOOST

/-- A node with its weight and its tiebreaker. -/
abbrev WeightedNode := ForkChoiceNode × Gwei × UInt8

/-- The order of weighted nodes: by weight, then by root as bytes, then by tiebreaker. -/
def compareWeighted : WeightedNode → WeightedNode → Ordering :=
  compareLex (compareOn (·.2.1)) (compareLex (compareOn (·.1.root)) (compareOn (·.2.2)))

instance : Std.TransCmp compareWeighted :=
  inferInstanceAs
    (Std.TransCmp (compareLex (compareOn _) (compareLex (compareOn _) (compareOn _))))

/-- The larger of two weighted nodes.

On equal keys the first one stays. -/
def heavier (a b : WeightedNode) : WeightedNode :=
  -- The second node only when it is strictly larger.
  if compareWeighted a b = .lt then b else a

/-- The node of the largest weighted node of a list, or none when the list is empty. -/
def chooseHeaviest : List WeightedNode → Option ForkChoiceNode
  | [] => none
  -- Gasper, Algorithm 3.1, lines 5 and 6: the arg max by weight, ties broken by the root.
  --
  -- Gasper breaks ties by the hash of the block header; the root as bytes plays that role here.
  --
  -- From Gloas the tiebreaker of the payload status breaks a tie that remains, as EIP-7732 says.
  | first :: rest => some (rest.foldl heavier first).1

/-- The latest votes that count in a state, grouped by the node that each one supports.

Once the tally is built, the count for one node reads only its groups, not the validators.

The groups stop at the first vote whose node cannot be found, and keep its error. -/
structure VoteTally where
  /-- Each supported node and the sum of the balances of its votes, by first vote. -/
  groups : List (ForkChoiceNode × Nat)
  /-- The error of the first vote whose node cannot be found, if there is one. -/
  failure : Option ForkChoiceError

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The state of a checkpoint, or an error when the store holds none. -/
def checkpointState (checkpoint : Checkpoint) : Except ForkChoiceError (BeaconState preset fork) :=
  match store.checkpointStates[checkpoint]? with
  | some state => return state
  | none => throw (.unknownCheckpointState checkpoint)

/-- The state after a known block, or an error when the store holds none. -/
def blockState (root : Root) : Except ForkChoiceError (BeaconState preset fork) :=
  match store.blockStates[root]? with
  | some state => return state
  | none => throw (.unknownBlockState root)

/-- The node that a latest vote supports.

From Gloas the store must hold the block of the vote. -/
def getSupportedNode (message : LatestMessage fork) : Except ForkChoiceError ForkChoiceNode := do
  if gloas : .glamsterdam ≤ fork then
    let block ← store.block message.root
    -- From Gloas a vote from a later slot than its block supports the full or the empty node.
    --
    -- Its payload vote says which, as EIP-7732 specifies.
    if block.slot < message.slot gloas then
      return ⟨message.root, if message.payloadPresent gloas then .full else .empty⟩
    -- A vote from the slot of its block supports the pending node.
    else return ⟨message.root, .pending⟩
  -- Before Gloas the block of the vote, whatever the payload.
  else return ⟨message.root, .pending⟩

/-- The votes that count, grouped by the node that each one supports.

The validators are read in order, and each balance is added to the sum of its supported node.

A new supported node goes on the front of the given list, which is kept in reverse.

A validator without a message is left out, and so is an equivocator.

It gives the sums, and the given nodes in reverse followed by the new nodes by first vote.

It stops at the first vote whose node cannot be found, and gives its error. -/
def groupVotes : List (ValidatorIndex × Gwei) → List ForkChoiceNode →
    Std.TreeMap ForkChoiceNode Nat ForkChoiceNode.compare →
    List ForkChoiceNode × Std.TreeMap ForkChoiceNode Nat ForkChoiceNode.compare ×
      Option ForkChoiceError
  | [], nodes, sums => (nodes.reverse, sums, none)
  | (index, balance) :: rest, nodes, sums =>
    -- A validator without a latest vote is left out.
    match store.latestMessages[index]? with
    | none => groupVotes rest nodes sums
    | some message =>
      -- So is an equivocator.
      if store.equivocatingIndices.contains index then groupVotes rest nodes sums
      else
        match store.getSupportedNode message with
        | .error error => (nodes.reverse, sums, some error)
        -- Its balance joins the sum of the node that its vote supports.
        | .ok node =>
          groupVotes rest (if sums.contains node then nodes else node :: nodes)
            (sums.insert node (sums.getD node 0 + balance.toNat))

/-- The votes that count in a state, from the validators active and not slashed there.

One pass over the validators sums the balances of the votes for each supported node.

No equivocator counts. -/
def tallyVotes (state : BeaconState preset fork) : VoteTally :=
  -- One pass over the unslashed active validators of the state.
  let (nodes, sums, failure) := store.groupVotes (unslashedActiveBalances state) [] ∅
  { groups := nodes.map fun node => (node, sums.getD node 0), failure }

/-- The votes for a node from a tally of the store: the sums of the groups whose node descends.

The groups are checked in order, and the first failed check is the error.

Then comes the error of the first vote whose node cannot be found, if there is one.

A sum that leaves the 64-bit range is an overflow. -/
def scoreFromTally (tally : VoteTally) (node : ForkChoiceNode) : Except ForkChoiceError Gwei := do
  -- Gasper, Definition 3.4: the stake of the latest votes for the node or its descendants.
  let total ← tally.groups.foldlM (init := 0) fun (total : Nat) (supported, weight) => do
    if ← store.isAncestor supported node then return total + weight
    return total
  if let some error := tally.failure then throw error
  if 2 ^ 64 ≤ total then throw (.arith .overflow)
  return total.toUInt64

/-- The votes for a node: the effective balance of the validators that vote in its subtree.

Only the validators active and not slashed in the given state count, and no equivocator does. -/
def getAttestationScore (node : ForkChoiceNode) (state : BeaconState preset fork) :
    Except ForkChoiceError Gwei :=
  -- The tally of the state, read for the node.
  store.scoreFromTally (store.tallyVotes state) node

/-- The votes that count in the justified state, or an error when the store holds no such state.

The head computation builds it once, and every weight it compares reads it. -/
def justifiedTally : Except ForkChoiceError VoteTally :=
  -- The tally of the state of the justified checkpoint.
  return store.tallyVotes (← store.checkpointState store.justifiedCheckpoint)

/-- The boost of a timely block, from the state of the justified checkpoint. -/
def getProposerScore : Except ForkChoiceError Gwei := do
  -- The boost computed on the state of the justified checkpoint.
  computeProposerScore config (← store.checkpointState store.justifiedCheckpoint)

/-- Whether a head holds less weight than a share of a committee.

Its weight counts its votes in the justified state, and every equivocator of its committees. -/
def isHeadWeak (headRoot : Root) : Except ForkChoiceError Bool := do
  -- The threshold is `REORG_HEAD_WEIGHT_THRESHOLD` percent of a committee, in the justified state.
  let justifiedState ← store.checkpointState store.justifiedCheckpoint
  let reorgThreshold ← calculateCommitteeFraction justifiedState config.REORG_HEAD_WEIGHT_THRESHOLD
  let headState ← store.blockState headRoot
  let headBlock ← store.block headRoot
  let epoch := computeEpochAtSlot preset headBlock.slot
  -- The weight of the head starts at the votes for its pending node in the justified state.
  let votes ← store.getAttestationScore ⟨headRoot, .pending⟩ justifiedState
  let mut headWeight : Nat := votes.toNat
  -- It adds the effective balance of each equivocator in the committees of the head's slot.
  --
  -- The committees come from the state after the head, and the balances from the justified state.
  for index in List.range (getCommitteeCountPerSlot headState epoch).toNat do
    let committee ← (getBeaconCommittee headState headBlock.slot index.toUInt64).mapError .accessor
    for validator in committee do
      if store.equivocatingIndices.contains validator then
        let known ← (getValidator justifiedState validator).mapError .accessor
        headWeight := headWeight + known.effectiveBalance.toNat
    if 2 ^ 64 ≤ headWeight then throw (.arith .overflow)
  -- The head is weak when its weight is below the threshold.
  return headWeight < reorgThreshold.toNat

/-- Whether a block of the store arrived before the deadline of the payload committee.

The store must hold that timeliness. -/
def ptcTimely (gloas : .glamsterdam ≤ fork) (root : Root) : Except ForkChoiceError Bool :=
  -- The timeliness that the store recorded for the block.
  match (store.ptcTimeliness gloas)[root]? with
  | some timely => return timely
  | none => throw (.unknownBlockTimeliness root)

/-- Whether the boost applies, from Gloas, as [EIP-7732] specifies.

Every block of the store is tested, so each must have its timeliness.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#fork-choice-changes
-/
def shouldApplyProposerBoost (gloas : .glamsterdam ≤ fork) : Except ForkChoiceError Bool := do
  -- Without a boosted block the boost does not apply; else `s` is the slot of that block.
  if store.proposerBoostRoot = Vector.replicate 32 0 then return false
  let block ← store.block store.proposerBoostRoot
  let parentRoot := block.parentRoot
  let parent ← store.block parentRoot
  let slot := block.slot
  -- A parent older than slot `s - 1` lets the boost apply.
  if (← (addChecked parent.slot 1).mapError .arith) < slot then return true
  -- So does a parent that is not weak.
  if !(← store.isHeadWeak config parentRoot) then return true
  -- A weak parent at `s - 1` lets it apply only when its proposer did not equivocate early.
  --
  -- An early equivocation is another block of that proposer at slot `s - 1`.
  --
  -- It arrived in its slot before the deadline of the payload committee.
  let equivocations ← store.blocks.toList.filterM fun (root, other) => do
    if !(← store.ptcTimely gloas root) || other.proposerIndex ≠ parent.proposerIndex then
      return false
    return (← (addChecked other.slot 1).mapError .arith) = slot && root ≠ parentRoot
  return equivocations.isEmpty

/-- The weight of a node: its votes in the justified state, plus the boost if it applies.

The votes come from the given tally, and the head computation passes the one of the justified state.

Its error, when the store holds no justified state, comes only once the votes are needed. -/
def getWeight (tally : Except ForkChoiceError VoteTally) (node : ForkChoiceNode) :
    Except ForkChoiceError Gwei := do
  -- From Gloas the empty and the full node of a block from the previous slot weigh nothing.
  let decision ← if .glamsterdam ≤ fork then store.isPreviousSlotPayloadDecision config node
    else pure false
  if decision then return 0 else
  -- The votes for the node, Gasper's weight of Definition 3.4.
  let attestationScore ← store.scoreFromTally (← tally) node
  -- The boost needs a boosted block, and from Gloas the consent of its parent.
  let boost ← if gloas : .glamsterdam ≤ fork then store.shouldApplyProposerBoost config gloas
    else pure (store.proposerBoostRoot ≠ Vector.replicate 32 0)
  if !boost then return attestationScore else
  -- It adds to a node from which the boosted block descends.
  let proposerScore ←
    if ← store.isAncestor ⟨store.proposerBoostRoot, .pending⟩ node then
      store.getProposerScore config
    else pure 0
  (addChecked attestationScore proposerScore).mapError .arith

/-- The source that a vote for a block would carry if the block were the head. -/
def getVotingSource (blockRoot : Root) : Except ForkChoiceError Checkpoint := do
  let block ← store.block blockRoot
  let currentEpoch ← store.getCurrentStoreEpoch config
  -- A block of an earlier epoch has its justification pulled up to the end of its epoch.
  if computeEpochAtSlot preset block.slot < currentEpoch then
    match store.unrealizedJustifications[blockRoot]? with
    | some checkpoint => return checkpoint
    | none => throw (.unknownUnrealizedJustification blockRoot)
  -- A block of the current epoch has the current justified checkpoint of its state.
  else
    match store.blockStates[blockRoot]? with
    | some state => return state.currentJustifiedCheckpoint
    | none => throw (.unknownBlockState blockRoot)

/-- The children of a node.

From Gloas the store must hold the block of an empty or full node that has children. -/
def getNodeChildren (node : ForkChoiceNode) : Except ForkChoiceError (List ForkChoiceNode) :=
  -- From Gloas a pending node has the empty node of its block as a child.
  --
  -- It also has the full node when the store has verified the payload.
  if gloas : .glamsterdam ≤ fork ∧ node.payloadStatus = .pending then
    return ⟨node.root, .empty⟩ ::
      if store.isPayloadVerified gloas.1 node.root then [⟨node.root, .full⟩] else []
  else
    -- The known blocks whose parent is the node's block.
    let built := store.blocks.toList.filter fun (_, block) => block.parentRoot = node.root
    -- From Gloas an empty or full node keeps only those that build on its payload status.
    if .glamsterdam ≤ fork ∧ !built.isEmpty then do
      let parent ← store.block node.root
      return built.filterMap fun (root, block) =>
        if parentPayloadStatus block parent = node.payloadStatus then some ⟨root, .pending⟩
        else none
    -- Before Gloas, the pending nodes of those blocks.
    else return built.map fun (root, _) => ⟨root, .pending⟩

/-- A rank that falls from a node to each child in a store that the handlers build.

It counts down the slot of the block, and puts a pending node above the other nodes of its block. -/
def nodeRank (node : ForkChoiceNode) : Nat :=
  -- `2 * (2^64 - s) + 1` for a pending node at slot `s`, `2 * (2^64 - s)` for another, else 0.
  match store.blocks[node.root]? with
  | some block => 2 * (2 ^ 64 - block.slot.toNat) + if node.payloadStatus = .pending then 1 else 0
  | none => 0

/-- Whether a leaf agrees with the justified and finalized checkpoints of the store. -/
def isViableLeaf (node : ForkChoiceNode) : Except ForkChoiceError Bool := do
  let currentEpoch ← store.getCurrentStoreEpoch config
  let votingSource ← store.getVotingSource config node.root
  -- Let `e` be the current epoch and `v` the epoch of the voting source of the leaf.
  --
  -- `v` is the epoch of the justified checkpoint, or `e ≤ v + 2`.
  --
  -- That holds anyway while the justified checkpoint is at the genesis epoch.
  let correctJustified ←
    if store.justifiedCheckpoint.epoch = GENESIS_EPOCH ∨
        votingSource.epoch = store.justifiedCheckpoint.epoch then pure true
    else do
      let bound ← (addChecked votingSource.epoch 2).mapError .arith
      pure (currentEpoch ≤ bound)
  -- Its chain holds the finalized block, or the finalized checkpoint is at the genesis epoch.
  let finalizedCheckpointBlock ← store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch
  let correctFinalized := decide (store.finalizedCheckpoint.epoch = GENESIS_EPOCH) ||
    decide (store.finalizedCheckpoint.root = finalizedCheckpointBlock)
  return correctJustified && correctFinalized

/-- The nodes of the subtree of a node that lead to a viable leaf, the node last.

A child whose rank is not below its parent's is an error, so that the walk ends. -/
def filterNodeTree (node : ForkChoiceNode) : Except ForkChoiceError (List ForkChoiceNode) := do
  let children ← store.getNodeChildren node
  -- A leaf is kept when it is viable.
  if children.isEmpty then
    return if ← store.isViableLeaf config node then [node] else []
  -- An inner node is kept when one of its children leads to a viable leaf.
  let viable ← children.flatMapM fun child =>
    if _lower : store.nodeRank child < store.nodeRank node then filterNodeTree child
    else throw (.parentSlotNotLower child.root)
  return if viable.isEmpty then [] else viable ++ [node]
termination_by store.nodeRank node

/-- The nodes from the justified block that lead to a viable leaf. -/
def getFilteredNodeTree : Except ForkChoiceError (List ForkChoiceNode) :=
  -- From the pending node of the justified block.
  store.filterNodeTree config ⟨store.justifiedCheckpoint.root, .pending⟩

/-- The tiebreaker of a node, from Gloas the one of its payload status.

Before Gloas the order has no tiebreaker, so every node gets 0 and only weight and root count. -/
def tiebreaker (node : ForkChoiceNode) : Except ForkChoiceError UInt8 :=
  if gloas : .glamsterdam ≤ fork then store.getPayloadStatusTiebreaker config gloas node
  else pure 0

/-- A node with its weight from the given tally, and its tiebreaker. -/
def weighNode (tally : Except ForkChoiceError VoteTally) (node : ForkChoiceNode) :
    Except ForkChoiceError WeightedNode :=
  -- The node, its weight and its tiebreaker.
  return (node, ← store.getWeight config tally node, ← store.tiebreaker config node)

/-- The heaviest child of a node among the given nodes, by weight, then root, then tiebreaker.

It is none when the node has no child among them. -/
def heaviestChild (tally : Except ForkChoiceError VoteTally) (nodes : List ForkChoiceNode)
    (node : ForkChoiceNode) : Except ForkChoiceError (Option ForkChoiceNode) := do
  -- The children of the node among the given nodes, weighed, then the heaviest.
  let children := (← store.getNodeChildren node).filter (· ∈ nodes)
  let weighted ← children.mapM (store.weighNode config tally)
  return chooseHeaviest weighted

/-- LMD-GHOST from a node among the given nodes: move to the heaviest child until there is none.

Every weight reads the given tally.

A child whose rank is not below its parent's is an error, so that the walk ends. -/
def getHeadFrom (tally : Except ForkChoiceError VoteTally) (nodes : List ForkChoiceNode)
    (head : ForkChoiceNode) : Except ForkChoiceError ForkChoiceNode := do
  match ← store.heaviestChild config tally nodes head with
  -- Gasper, Algorithm 4.2, line 11: a node with no child among the nodes is the head.
  | none => return head
  -- Line 9: else the walk moves to the heaviest child.
  | some child =>
    if _lower : store.nodeRank child < store.nodeRank head then getHeadFrom tally nodes child
    else throw (.parentSlotNotLower child.root)
termination_by store.nodeRank head

/-- The head of the chain: LMD-GHOST from the justified block, over the viable nodes.

The votes of the justified state are tallied once, for every weight of the walk. -/
def getHead : Except ForkChoiceError ForkChoiceNode := do
  -- The nodes that lead to a viable leaf.
  let nodes ← store.getFilteredNodeTree config
  -- From Gloas, when none is viable, the head is the empty node of the justified block.
  if .glamsterdam ≤ fork ∧ nodes.isEmpty then return ⟨store.justifiedCheckpoint.root, .empty⟩
  -- Else the walk starts at the justified block, over the nodes left, as Gasper, Algorithm 4.2.
  --
  -- Each weight counts every vote, as `w(G, B, M)` does, where Gasper restricts it to `G'`.
  else
    store.getHeadFrom config store.justifiedTally nodes ⟨store.justifiedCheckpoint.root, .pending⟩

end Store

end EthLib.Consensus

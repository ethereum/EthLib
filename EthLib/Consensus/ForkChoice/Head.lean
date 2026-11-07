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
  state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isActiveValidator validator (getCurrentEpoch state) && !validator.slashed then
      some (index.toUInt64, validator.effectiveBalance)
    else none

/-- A share of the weight of one committee, in percent.

A committee weighs the total balance of the unslashed active validators, over the epoch's slots.
-/
def calculateCommitteeFraction (state : BeaconState preset fork) (committeePercent : UInt64) :
    Except ForkChoiceError Gwei := do
  let total ← (getTotalBalance state ((unslashedActiveBalances state).map (·.1))).mapError .accessor
  let committeeWeight ← (divChecked total preset.SLOTS_PER_EPOCH).mapError .arith
  return (← (mulChecked committeeWeight committeePercent).mapError .arith) / 100

/-- The boost of a timely block, from the justified state. -/
def computeProposerScore (config : Config) (state : BeaconState preset fork) :
    Except ForkChoiceError Gwei :=
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
  if compareWeighted a b = .lt then b else a

/-- The node of the largest weighted node of a list, or none when the list is empty. -/
def chooseHeaviest : List WeightedNode → Option ForkChoiceNode
  | [] => none
  | first :: rest => some (rest.foldl heavier first).1

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

Before Gloas it is the block of the vote, whatever the payload.

From Gloas a vote from a later slot than its block also says whether the payload is present.

It then supports the full or the empty node of the block.

A vote from the slot of its block supports the pending node, and the store must hold the block. -/
def getSupportedNode (message : LatestMessage fork) : Except ForkChoiceError ForkChoiceNode := do
  if gloas : .glamsterdam ≤ fork then
    let block ← store.block message.root
    if block.slot < message.slot gloas then
      return ⟨message.root, if message.payloadPresent gloas then .full else .empty⟩
    else return ⟨message.root, .pending⟩
  else return ⟨message.root, .pending⟩

/-- The votes for a node: the effective balance of the validators that vote in its subtree.

Only the validators active and not slashed in the given state count, and no equivocator does. -/
def getAttestationScore (node : ForkChoiceNode) (state : BeaconState preset fork) :
    Except ForkChoiceError Gwei := do
  let total ← (unslashedActiveBalances state).foldlM (init := 0)
      fun (total : Nat) (index, balance) =>
        match store.latestMessages[index]? with
        | none => pure total
        | some message => do
          if store.equivocatingIndices.contains index then return total
          if ← store.isAncestor (← store.getSupportedNode message) node then
            return total + balance.toNat
          return total
  if 2 ^ 64 ≤ total then throw (.arith .overflow)
  return total.toUInt64

/-- The boost of a timely block, from the state of the justified checkpoint. -/
def getProposerScore : Except ForkChoiceError Gwei := do
  computeProposerScore config (← store.checkpointState store.justifiedCheckpoint)

/-- Whether a head holds less weight than a share of a committee.

Its weight counts its votes in the justified state, and every equivocator of its committees. -/
def isHeadWeak (headRoot : Root) : Except ForkChoiceError Bool := do
  let justifiedState ← store.checkpointState store.justifiedCheckpoint
  let reorgThreshold ← calculateCommitteeFraction justifiedState config.REORG_HEAD_WEIGHT_THRESHOLD
  let headState ← store.blockState headRoot
  let headBlock ← store.block headRoot
  let epoch := computeEpochAtSlot preset headBlock.slot
  let votes ← store.getAttestationScore ⟨headRoot, .pending⟩ justifiedState
  let mut headWeight : Nat := votes.toNat
  for index in List.range (getCommitteeCountPerSlot headState epoch).toNat do
    let committee ← (getBeaconCommittee headState headBlock.slot index.toUInt64).mapError .accessor
    for validator in committee do
      if store.equivocatingIndices.contains validator then
        match justifiedState.validators.data[validator.toNat]? with
        | some known => headWeight := headWeight + known.effectiveBalance.toNat
        | none => throw (.accessor (.indexOutOfRange validator))
    if 2 ^ 64 ≤ headWeight then throw (.arith .overflow)
  return headWeight < reorgThreshold.toNat

/-- Whether a block of the store arrived before the deadline of the payload committee.

The store must hold that timeliness. -/
def ptcTimely (gloas : .glamsterdam ≤ fork) (root : Root) : Except ForkChoiceError Bool :=
  match (store.ptcTimeliness gloas)[root]? with
  | some timely => return timely
  | none => throw (.unknownBlockTimeliness root)

/-- Whether the boost applies, from Gloas.

There must be a boosted block.

A parent older than the slot before the boosted block lets the boost apply.

So does a parent that is not weak.

A weak parent of the slot before lets it apply only when its proposer did not equivocate early.

An early equivocation is another block of that proposer at the parent's slot.

It arrived in its slot before the deadline of the payload committee.

Every block of the store is tested, so each must have its timeliness. -/
def shouldApplyProposerBoost (gloas : .glamsterdam ≤ fork) : Except ForkChoiceError Bool := do
  if store.proposerBoostRoot = Vector.replicate 32 0 then return false
  let block ← store.block store.proposerBoostRoot
  let parentRoot := block.parentRoot
  let parent ← store.block parentRoot
  let slot := block.slot
  if (← (addChecked parent.slot 1).mapError .arith) < slot then return true
  if !(← store.isHeadWeak config parentRoot) then return true
  let equivocations ← store.blocks.toList.filterM fun (root, other) => do
    if !(← store.ptcTimely gloas root) || other.proposerIndex ≠ parent.proposerIndex then
      return false
    return (← (addChecked other.slot 1).mapError .arith) = slot && root ≠ parentRoot
  return equivocations.isEmpty

/-- The weight of a node: its votes in the justified state, plus the boost if it applies.

The boost applies when the boosted block descends from the node.

From Gloas the empty and the full node of a block from the previous slot weigh nothing.

From Gloas the boost also needs the consent of the boosted block's parent. -/
def getWeight (node : ForkChoiceNode) : Except ForkChoiceError Gwei := do
  let decision ← if .glamsterdam ≤ fork then store.isPreviousSlotPayloadDecision config node
    else pure false
  if decision then return 0 else
  let state ← store.checkpointState store.justifiedCheckpoint
  let attestationScore ← store.getAttestationScore node state
  let boost ← if gloas : .glamsterdam ≤ fork then store.shouldApplyProposerBoost config gloas
    else pure (store.proposerBoostRoot ≠ Vector.replicate 32 0)
  if !boost then return attestationScore else
  let proposerScore ←
    if ← store.isAncestor ⟨store.proposerBoostRoot, .pending⟩ node then
      store.getProposerScore config
    else pure 0
  (addChecked attestationScore proposerScore).mapError .arith

/-- The source that a vote for a block would carry if the block were the head.

A block of an earlier epoch has its justification pulled up to the end of its epoch. -/
def getVotingSource (blockRoot : Root) : Except ForkChoiceError Checkpoint := do
  let block ← store.block blockRoot
  let currentEpoch ← store.getCurrentStoreEpoch config
  if computeEpochAtSlot preset block.slot < currentEpoch then
    match store.unrealizedJustifications[blockRoot]? with
    | some checkpoint => return checkpoint
    | none => throw (.unknownUnrealizedJustification blockRoot)
  else
    match store.blockStates[blockRoot]? with
    | some state => return state.currentJustifiedCheckpoint
    | none => throw (.unknownBlockState blockRoot)

/-- The children of a node.

Before Gloas they are the pending nodes of the known blocks whose parent is the node's block.

From Gloas a pending node has the empty node of its block as a child.

It also has the full node when the store has verified the payload.

From Gloas an empty or full node keeps only the blocks that build on its payload status.

Their parent is the node's block, so the store must then hold that block. -/
def getNodeChildren (node : ForkChoiceNode) : Except ForkChoiceError (List ForkChoiceNode) :=
  if gloas : .glamsterdam ≤ fork ∧ node.payloadStatus = .pending then
    return ⟨node.root, .empty⟩ ::
      if store.isPayloadVerified gloas.1 node.root then [⟨node.root, .full⟩] else []
  else
    let built := store.blocks.toList.filter fun (_, block) => block.parentRoot = node.root
    if .glamsterdam ≤ fork ∧ !built.isEmpty then do
      let parent ← store.block node.root
      return built.filterMap fun (root, block) =>
        if parentPayloadStatus block parent = node.payloadStatus then some ⟨root, .pending⟩
        else none
    else return built.map fun (root, _) => ⟨root, .pending⟩

/-- A rank that falls from a node to each child in a store that the handlers build.

It counts down the slot of the block, and puts a pending node above the other nodes of its block. -/
def nodeRank (node : ForkChoiceNode) : Nat :=
  match store.blocks[node.root]? with
  | some block => 2 * (2 ^ 64 - block.slot.toNat) + if node.payloadStatus = .pending then 1 else 0
  | none => 0

/-- Whether a leaf agrees with the justified and finalized checkpoints of the store.

Its voting source must be the justified checkpoint, or at most two epochs old.

Its chain must hold the finalized block.

Each holds while its checkpoint is at the genesis epoch. -/
def isViableLeaf (node : ForkChoiceNode) : Except ForkChoiceError Bool := do
  let currentEpoch ← store.getCurrentStoreEpoch config
  let votingSource ← store.getVotingSource config node.root
  let correctJustified ←
    if store.justifiedCheckpoint.epoch = GENESIS_EPOCH ∨
        votingSource.epoch = store.justifiedCheckpoint.epoch then pure true
    else do
      let bound ← (addChecked votingSource.epoch 2).mapError .arith
      pure (currentEpoch ≤ bound)
  let finalizedCheckpointBlock ← store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch
  let correctFinalized := decide (store.finalizedCheckpoint.epoch = GENESIS_EPOCH) ||
    decide (store.finalizedCheckpoint.root = finalizedCheckpointBlock)
  return correctJustified && correctFinalized

/-- The nodes of the subtree of a node that lead to a viable leaf, the node last.

A child whose rank is not below its parent's is an error, so that the walk ends. -/
def filterNodeTree (node : ForkChoiceNode) : Except ForkChoiceError (List ForkChoiceNode) := do
  let children ← store.getNodeChildren node
  if children.isEmpty then
    return if ← store.isViableLeaf config node then [node] else []
  let viable ← children.flatMapM fun child =>
    if _lower : store.nodeRank child < store.nodeRank node then filterNodeTree child
    else throw (.parentSlotNotLower child.root)
  return if viable.isEmpty then [] else viable ++ [node]
termination_by store.nodeRank node

/-- The nodes from the justified block that lead to a viable leaf. -/
def getFilteredNodeTree : Except ForkChoiceError (List ForkChoiceNode) :=
  store.filterNodeTree config ⟨store.justifiedCheckpoint.root, .pending⟩

/-- The tiebreaker of a node, from Gloas the one of its payload status.

Before Gloas the order has no tiebreaker, so every node gets 0 and only weight and root count. -/
def tiebreaker (node : ForkChoiceNode) : Except ForkChoiceError UInt8 :=
  if gloas : .glamsterdam ≤ fork then store.getPayloadStatusTiebreaker config gloas node
  else pure 0

/-- A node with its weight and its tiebreaker. -/
def weighNode (node : ForkChoiceNode) : Except ForkChoiceError WeightedNode :=
  return (node, ← store.getWeight config node, ← store.tiebreaker config node)

/-- The heaviest child of a node among the given nodes, by weight, then root, then tiebreaker.

It is none when the node has no child among them. -/
def heaviestChild (nodes : List ForkChoiceNode) (node : ForkChoiceNode) :
    Except ForkChoiceError (Option ForkChoiceNode) := do
  let children := (← store.getNodeChildren node).filter (· ∈ nodes)
  let weighted ← children.mapM (store.weighNode config)
  return chooseHeaviest weighted

/-- LMD-GHOST from a node among the given nodes: move to the heaviest child until there is none.

A child whose rank is not below its parent's is an error, so that the walk ends. -/
def getHeadFrom (nodes : List ForkChoiceNode) (head : ForkChoiceNode) :
    Except ForkChoiceError ForkChoiceNode := do
  match ← store.heaviestChild config nodes head with
  | none => return head
  | some child =>
    if _lower : store.nodeRank child < store.nodeRank head then getHeadFrom nodes child
    else throw (.parentSlotNotLower child.root)
termination_by store.nodeRank head

/-- The head of the chain: LMD-GHOST from the justified block, over the viable nodes.

From Gloas, when no node is viable, the head is the empty node of the justified block. -/
def getHead : Except ForkChoiceError ForkChoiceNode := do
  let nodes ← store.getFilteredNodeTree config
  if .glamsterdam ≤ fork ∧ nodes.isEmpty then return ⟨store.justifiedCheckpoint.root, .empty⟩
  else store.getHeadFrom config nodes ⟨store.justifiedCheckpoint.root, .pending⟩

end Store

end EthLib.Consensus

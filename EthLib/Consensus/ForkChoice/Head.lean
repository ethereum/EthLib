module

public import EthLib.Consensus.ForkChoice.Store

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

Gloas changes the children of a node, the weight and the head.

Those rules are not yet specified here, so they fail from Gloas on.
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

/-- The order of weighted nodes: by weight, then by root as a string of bytes. -/
def compareWeighted : ForkChoiceNode × Gwei → ForkChoiceNode × Gwei → Ordering :=
  compareLex (compareOn (·.2)) (compareOn (·.1.root))

instance : Std.TransCmp compareWeighted :=
  inferInstanceAs (Std.TransCmp (compareLex (compareOn _) (compareOn _)))

/-- The larger of two weighted nodes.

On equal keys the first one stays. -/
def heavier (a b : ForkChoiceNode × Gwei) : ForkChoiceNode × Gwei :=
  if compareWeighted a b = .lt then b else a

/-- The node of the largest weighted node of a list, or none when the list is empty. -/
def chooseHeaviest : List (ForkChoiceNode × Gwei) → Option ForkChoiceNode
  | [] => none
  | first :: rest => some (rest.foldl heavier first).1

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The state of a checkpoint, or an error when the store holds none. -/
def checkpointState (checkpoint : Checkpoint) : Except ForkChoiceError (BeaconState preset fork) :=
  match store.checkpointStates[checkpoint]? with
  | some state => return state
  | none => throw (.unknownCheckpointState checkpoint)

/-- The node that a latest vote supports: its block, whatever the payload.

From Gloas the payload of the vote matters, and that rule is not yet specified here. -/
def getSupportedNode (_store : Store preset fork) (message : LatestMessage) :
    Except ForkChoiceError ForkChoiceNode := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  return ⟨message.root, .pending⟩

/-- The votes for a node: the balance of the validators whose latest vote descends from it.

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

/-- The weight of a node: its votes in the justified state, plus the boost if it applies.

The boost applies when the boosted block descends from the node.

From Gloas the weight is not yet specified here. -/
def getWeight (node : ForkChoiceNode) : Except ForkChoiceError Gwei := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let state ← store.checkpointState store.justifiedCheckpoint
  let attestationScore ← store.getAttestationScore node state
  if store.proposerBoostRoot = Vector.replicate 32 0 then return attestationScore
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

/-- The children of a node: the known blocks whose parent is the node's block.

From Gloas the children are not yet specified here. -/
def getNodeChildren (node : ForkChoiceNode) : Except ForkChoiceError (List ForkChoiceNode) := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  return store.blocks.toList.filterMap fun (root, block) =>
    if block.parentRoot = node.root then some ⟨root, .pending⟩ else none

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
    else return currentEpoch ≤ (← (addChecked votingSource.epoch 2).mapError .arith)
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

/-- The heaviest child of a node among the given nodes, by weight and then by root.

It is none when the node has no child among them. -/
def heaviestChild (nodes : List ForkChoiceNode) (node : ForkChoiceNode) :
    Except ForkChoiceError (Option ForkChoiceNode) := do
  let children := (← store.getNodeChildren node).filter (· ∈ nodes)
  let weighted ← children.mapM fun child => (child, ·) <$> store.getWeight config child
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

From Gloas the head is not yet specified here. -/
def getHead : Except ForkChoiceError ForkChoiceNode := do
  if .glamsterdam ≤ fork then throw (.forkNotYetSpecified fork)
  let nodes ← store.getFilteredNodeTree config
  store.getHeadFrom config nodes ⟨store.justifiedCheckpoint.root, .pending⟩

end Store

end EthLib.Consensus

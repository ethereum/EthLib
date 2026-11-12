module

public import EthLib.Consensus.ForkChoice.ProposerHead
public import Std.Data.TreeSet

/-!
# `Consensus.ForkChoice.FastConfirmation`

The fast confirmation rule: a block that every honest node keeps in its chain, found within slots.

The rule and its proof are in [arXiv 2405.00549](https://arxiv.org/abs/2405.00549).

It assumes that the attestations of honest validators reach every node by the end of their slot.

It also assumes a static set of validators.

In every range of consecutive committees, at most a share of the stake is Byzantine.

That share is a value of the configuration, a quarter by default.

A block is safe for LMD-GHOST when its votes exceed a threshold.

The threshold counts the largest weight that could still vote, the boost, and the adversary.

It weighs the committees of a range of slots exactly, from the effective balances of their members.

An average weight per slot would not bound a given committee, as [a counterexample][avg] shows.

A block of the previous epoch also needs its justification to stay within reach.

A block of the current epoch also needs the target of the epoch to become justified.

At the start of each slot the handler records the head, then moves the confirmed block forward.

When the assumptions seem broken, it falls back to the finalized block.

The rule names each block by its pending node.

From Gloas a pending node counts the votes for the block whether its payload is present or not.

From Bellatrix the payload of the confirmed block is the safe block of the execution layer.

From Gloas the safe block is the parent payload that the bid of the confirmed block builds on.

[avg]: https://github.com/ethereum/EthLib/issues/1458#issuecomment-6764027413
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Fork}

/-- What the fast confirmation rule tracks besides the store of the fork choice. -/
structure FastConfirmationStore where
  /-- The root of the most recent confirmed block. -/
  confirmedRoot : Root
  /-- A justified checkpoint that every honest node saw at the start of the previous epoch. -/
  previousEpochObservedJustifiedCheckpoint : Checkpoint
  /-- A justified checkpoint that every honest node saw at the start of the current epoch. -/
  currentEpochObservedJustifiedCheckpoint : Checkpoint
  /-- The greatest unrealized justified checkpoint at the start of the last slot of an epoch. -/
  previousEpochGreatestUnrealizedCheckpoint : Checkpoint
  /-- The head at the start of the previous slot. -/
  previousSlotHead : Root
  /-- The head at the start of the current slot. -/
  currentSlotHead : Root
  deriving DecidableEq, Repr

/-- Whether a slot starts an epoch. -/
def isStartSlotAtEpoch (preset : Preset) (slot : Slot) : Except ForkChoiceError Bool :=
  return (← (computeSlotsSinceEpochStart preset slot).mapError .arith) = 0

/-- Whether the slots from a start to an end, both included, hold a whole epoch. -/
def isFullValidatorSetCovered (preset : Preset) (startSlot endSlot : Slot) :
    Except ForkChoiceError Bool := do
  let afterFirst ← (addChecked startSlot preset.SLOTS_PER_EPOCH).mapError .arith
  let lastOfFirst ← (subChecked afterFirst 1).mapError .arith
  let afterEnd ← (addChecked endSlot 1).mapError .arith
  return computeEpochAtSlot preset lastOfFirst < computeEpochAtSlot preset afterEnd

/-- The sum of a weight over a list, which must stay within 64 bits. -/
def sumGwei {α : Type} (items : List α) (weight : α → Except ForkChoiceError Gwei) :
    Except ForkChoiceError Gwei := do
  let total ← items.foldlM (fun sum item => return sum + (← weight item).toNat) 0
  if 2 ^ 64 ≤ total then throw (.arith .overflow)
  return total.toUInt64

/-- The validator at an index of a state, or an error when the index is out of range. -/
def validatorAt (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except ForkChoiceError Validator :=
  match state.validators.data[index.toNat]? with
  | some validator => return validator
  | none => throw (.accessor (.indexOutOfRange index))

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The epoch of a known block. -/
def getBlockEpoch (root : Root) : Except ForkChoiceError Epoch :=
  return computeEpochAtSlot preset (← store.block root).slot

/-- The checkpoint of an epoch in the chain of a block. -/
def getCheckpointForBlock (root : Root) (epoch : Epoch) : Except ForkChoiceError Checkpoint :=
  return ⟨epoch, ← store.getCheckpointBlock root epoch⟩

/-- The target of the current epoch in the chain of the head. -/
def getCurrentTarget (head : Root) : Except ForkChoiceError Checkpoint := do
  store.getCheckpointForBlock head (← store.getCurrentStoreEpoch config)

/-- The roots from a block back to a terminal block, oldest first, without the terminal block.

The list is empty when the terminal block is not in the chain of the block.

A parent at a slot no lower than its child is an error, so that the walk ends. -/
def getAncestorRoots (root terminal : Root) (acc : List Root := []) :
    Except ForkChoiceError (List Root) :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block => do
    let terminalBlock ← store.block terminal
    if block.slot ≤ terminalBlock.slot then return []
    let acc := root :: acc
    if block.parentRoot = terminal then return acc
    match _parentFound : store.blocks[block.parentRoot]? with
    | none => throw (.unknownBlock block.parentRoot)
    | some parent =>
      if _lower : parent.slot < block.slot then getAncestorRoots block.parentRoot terminal acc
      else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- The members of every committee of a slot, shuffled as in the state of the head. -/
def getSlotCommittee (head : Root) (slot : Slot) :
    Except ForkChoiceError (Std.TreeSet ValidatorIndex) := do
  let shufflingSource ← store.blockState head
  let count := getCommitteeCountPerSlot shufflingSource (computeEpochAtSlot preset slot)
  (List.range count.toNat).foldlM (init := ∅) fun participants index => do
    let committee ← (getBeaconCommittee shufflingSource slot index.toUInt64).mapError .accessor
    return committee.foldl (·.insert ·) participants

/-- The members of every committee of the slots from a start to an end, both included. -/
def getCommitteesBetweenSlots (head : Root) (startSlot endSlot : Slot) :
    Except ForkChoiceError (Std.TreeSet ValidatorIndex) := do
  let afterEnd ← (addChecked endSlot 1).mapError .arith
  (List.range (afterEnd.toNat - startSlot.toNat)).foldlM (init := ∅) fun participants offset => do
    let committee ← store.getSlotCommittee head (startSlot + offset.toUInt64)
    return committee.foldl (·.insert ·) participants

/-- The weight of the committees of the slots from a start to an end, both included.

The members of those committees come with it when it reads them.

A range that starts after it ends weighs nothing.

A range with a whole epoch weighs the total active balance of the source of balances.

Otherwise a member of the committees counts once, when it is active in the source of balances.

Its weight is its effective balance there, and the sum is at least one increment. -/
def computeCommitteeWeightAndMembers (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) :
    Except ForkChoiceError (Gwei × Option (Std.TreeSet ValidatorIndex)) := do
  if startSlot > endSlot then return (0, none)
  if ← isFullValidatorSetCovered preset startSlot endSlot then
    return (← (getTotalActiveBalance balanceSource).mapError .accessor, none)
  let participants ← store.getCommitteesBetweenSlots head startSlot endSlot
  let epoch := getCurrentEpoch balanceSource
  let active ← participants.toList.filterM fun index =>
    return isActiveValidator (← validatorAt balanceSource index) epoch
  return (← (getTotalBalance balanceSource active).mapError .accessor, some participants)

/-- The weight of the committees of the slots from a start to an end, both included. -/
def computeCommitteeWeightBetweenSlots (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  return (← store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot).1

/-- The state of the head, with its slots processed to the current epoch if it is older.

The pending deposits of an epoch from Electra check the signatures of new keys with BLS. -/
def getPulledUpHeadState (head : Root) : Except ForkChoiceError (BeaconState preset fork) := do
  let headState ← store.blockState head
  let currentEpoch ← store.getCurrentStoreEpoch config
  if getCurrentEpoch headState < currentEpoch then
    let start ← (computeStartSlotAtEpoch preset currentEpoch).mapError .arith
    (processSlots config .bls headState start).mapError .transition
  else return headState

/-- The votes for any of a list of nodes from the members of the committees of a range of slots.

The list is read as a set, since only membership in it is tested.

A voter counts when it is active and not slashed in the source of balances, and not an equivocator.

A vote from outside the range by a member of it may count too, which keeps the rule safe. -/
def getNodeSupportBetweenSlots (head : Root) (balanceSource : BeaconState preset fork)
    (nodes : List ForkChoiceNode) (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  let participants ← store.getCommitteesBetweenSlots head startSlot endSlot
  let epoch := getCurrentEpoch balanceSource
  let counted ← participants.toList.filterM fun index => do
    let validator ← validatorAt balanceSource index
    return !validator.slashed && isActiveValidator validator epoch
  sumGwei counted fun index => do
    match store.latestMessages[index]? with
    | none => return 0
    | some message =>
      if (← store.getSupportedNode message) ∈ nodes ∧ index ∉ store.equivocatingIndices then
        return (← validatorAt balanceSource index).effectiveBalance
      else return 0

/-- The weight of the equivocators among a set of validators.

An equivocator counts when it is active in the source of balances. -/
def getEquivocationScoreOf (balanceSource : BeaconState preset fork)
    (participants : Std.TreeSet ValidatorIndex) : Except ForkChoiceError Gwei := do
  let epoch := getCurrentEpoch balanceSource
  let equivocators := participants.toList.filter (· ∈ store.equivocatingIndices)
  let active ← equivocators.filterM fun index => do
    return isActiveValidator (← validatorAt balanceSource index) epoch
  sumGwei active fun index => return (← validatorAt balanceSource index).effectiveBalance

/-- The weight of the equivocators among the members of the committees of a range of slots. -/
def getEquivocationScore (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  store.getEquivocationScoreOf balanceSource
    (← store.getCommitteesBetweenSlots head startSlot endSlot)

/-- The largest weight that the adversary can hold in the committees of a range of slots.

It is the Byzantine share of the weight of the committees, less the weight of known equivocators.

The share rounds the weight down to 100 Gwei.

The members of the committees are read once: by the weight when it needs them, else here. -/
def computeAdversarialWeight (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  let (maximumWeight, members) ←
    store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot
  let maxAdversarialWeight ←
    (mulChecked (maximumWeight / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD).mapError .arith
  let participants ← match members with
    | some participants => pure participants
    | none => store.getCommitteesBetweenSlots head startSlot endSlot
  let equivocationScore ← store.getEquivocationScoreOf balanceSource participants
  return saturatingSub maxAdversarialWeight equivocationScore

/-- The largest weight that the adversary can give a block, from its slot to the last slot.

A block of a new epoch counts from the start of its epoch. -/
def getAdversarialWeight (head : Root) (balanceSource : BeaconState preset fork) (root : Root) :
    Except ForkChoiceError Gwei := do
  let currentSlot ← store.getCurrentSlot config
  let block ← store.block root
  let blockEpoch ← store.getBlockEpoch root
  let startSlot ← if blockEpoch > (← store.getBlockEpoch block.parentRoot) then
      (computeStartSlotAtEpoch preset blockEpoch).mapError .arith
    else pure block.slot
  let lastSlot ← (subChecked currentSlot 1).mapError .arith
  store.computeAdversarialWeight config head balanceSource startSlot lastSlot

/-- The votes for the parent of a block from the committees of the empty slots between them.

The adversarial weight of those slots is taken off, since the adversary may move its votes.

A vote from the parent's own slot supports the pending node of the parent, so those votes count.

Before Gloas the pending node is the only node of the parent.

From Gloas the votes for the node of the parent that the block builds on count with them.

That node is the full or the empty one, and it is the ancestor of the block at the parent's slot.

The other of those two nodes is not an ancestor of the block, so the votes for it stay out. -/
def computeEmptySlotSupportDiscount (head : Root) (balanceSource : BeaconState preset fork)
    (root : Root) : Except ForkChoiceError Gwei := do
  let block ← store.block root
  let parentBlock ← store.block block.parentRoot
  let firstEmpty ← (addChecked parentBlock.slot 1).mapError .arith
  if firstEmpty = block.slot then return 0
  let parentPendingNode : ForkChoiceNode := ⟨block.parentRoot, .pending⟩
  let parentNodes ←
    (if .glamsterdam ≤ fork then do
      let parentNode ← store.getAncestor ⟨root, .pending⟩ parentBlock.slot
      pure [parentPendingNode, parentNode]
    else pure [parentPendingNode])
  let lastEmpty ← (subChecked block.slot 1).mapError .arith
  let parentSupport ←
    store.getNodeSupportBetweenSlots head balanceSource parentNodes firstEmpty lastEmpty
  let adversarialWeight ←
    store.computeAdversarialWeight config head balanceSource firstEmpty lastEmpty
  return saturatingSub parentSupport adversarialWeight

/-- The votes that a block needs to be safe for LMD-GHOST.

It starts from the weight of the committees since its parent, plus the boost.

It takes off the votes for the parent from the empty slots before the block, less the adversary.

That discount exceeding the weight of the committees since the parent is an error.

It halves the result.

It adds the weight of the adversary. -/
def computeSafetyThreshold (head : Root) (root : Root) (balanceSource : BeaconState preset fork) :
    Except ForkChoiceError Gwei := do
  let currentSlot ← store.getCurrentSlot config
  let block ← store.block root
  let parentBlock ← store.block block.parentRoot
  let proposerScore ← computeProposerScore config balanceSource
  let maximumSupport ← store.computeCommitteeWeightBetweenSlots head balanceSource
    (← (addChecked parentBlock.slot 1).mapError .arith)
    (← (subChecked currentSlot 1).mapError .arith)
  let supportDiscount ← store.computeEmptySlotSupportDiscount config head balanceSource root
  let adversarialWeight ← store.getAdversarialWeight config head balanceSource root
  if supportDiscount > maximumSupport then throw (.supportDiscountAboveMaximum root)
  let withBoost ← (addChecked maximumSupport proposerScore).mapError .arith
  let doubled ← (mulChecked 2 adversarialWeight).mapError .arith
  let bound ← (addChecked withBoost doubled).mapError .arith
  return (bound - supportDiscount) / 2

/-- Whether a block is safe for LMD-GHOST: its votes exceed its safety threshold.

The votes come from the given tally, which must be the one of the balance source.

Every known block counts as valid here, since the store drops the blocks found invalid. -/
def isOneConfirmed (head : Root) (balanceSource : BeaconState preset fork) (tally : VoteTally)
    (root : Root) : Except ForkChoiceError Bool := do
  let support ← store.scoreFromTally tally ⟨root, .pending⟩
  return support > (← store.computeSafetyThreshold config head root balanceSource)

/-- Whether every block of the confirmed chain is still safe, from the observed justified block.

The chain starts after that block, or at the previous epoch when that block is older.

The votes of the balance source are tallied once, for the whole chain. -/
def isConfirmedChainSafe (fcr : FastConfirmationStore) (head confirmedRoot : Root) :
    Except ForkChoiceError Bool := do
  let observed := fcr.currentEpochObservedJustifiedCheckpoint
  if observed ≠ (← store.getCheckpointForBlock confirmedRoot observed.epoch) then return false
  let currentEpoch ← store.getCurrentStoreEpoch config
  let startRootExclusive ←
    if currentEpoch ≤ (← (addChecked observed.epoch 1).mapError .arith) then pure observed.root
    else do
      let previousEpoch ← (subChecked currentEpoch 1).mapError .arith
      let previousStart ← (computeStartSlotAtEpoch preset previousEpoch).mapError .arith
      let ancestor := (← store.getAncestor ⟨confirmedRoot, .pending⟩ previousStart).root
      if (← (addChecked (← store.getBlockEpoch ancestor) 1).mapError .arith) = currentEpoch then
        pure (← store.block ancestor).parentRoot
      else pure ancestor
  let chainRoots ← store.getAncestorRoots confirmedRoot startRootExclusive
  let source := store.checkpointState fcr.previousEpochObservedJustifiedCheckpoint
  let tally := source.map store.tallyVotes
  chainRoots.allM fun root => do
    store.isOneConfirmed config head (← source) (← tally) root

/-- An estimate of the votes for the target of the current epoch, from the latest messages.

A voter counts when it is active and not slashed in the pulled-up state of the head. -/
def getCurrentTargetScore (head : Root) : Except ForkChoiceError Gwei := do
  let target ← store.getCurrentTarget config head
  let state ← store.getPulledUpHeadState config head
  let counted ← (getActiveValidatorIndices state (getCurrentEpoch state)).filterM fun index =>
    return !(← validatorAt state index).slashed
  sumGwei counted fun index => do
    match store.latestMessages[index]? with
    | none => return 0
    | some message =>
      if index ∈ store.equivocatingIndices then return 0
      let epoch := getLatestMessageEpoch preset message
      if target = (← store.getCheckpointForBlock message.root epoch) then
        return (← validatorAt state index).effectiveBalance
      else return 0

/-- The honest votes that the target of the current epoch will get, at the least.

It counts the votes so far less the adversary, and the honest share of the slots still to come. -/
def computeHonestFfgSupportForCurrentTarget (head : Root) : Except ForkChoiceError Gwei := do
  let currentSlot ← store.getCurrentSlot config
  let currentEpoch := computeEpochAtSlot preset currentSlot
  let balanceSource ← store.getPulledUpHeadState config head
  let totalActiveBalance ← (getTotalActiveBalance balanceSource).mapError .accessor
  let ffgSupportForCheckpoint ← store.getCurrentTargetScore config head
  let epochStart ← (computeStartSlotAtEpoch preset currentEpoch).mapError .arith
  let lastSlot ← (subChecked currentSlot 1).mapError .arith
  let ffgWeightTillNow ←
    store.computeCommitteeWeightBetweenSlots head balanceSource epochStart lastSlot
  let remainingFfgWeight ← (subChecked totalActiveBalance ffgWeightTillNow).mapError .arith
  let honestShare ← (subChecked 100 config.CONFIRMATION_BYZANTINE_THRESHOLD).mapError .arith
  let remainingHonestFfgWeight ←
    (mulChecked (remainingFfgWeight / 100) honestShare).mapError .arith
  let adversarialWeight ←
    store.computeAdversarialWeight config head balanceSource epochStart lastSlot
  let minHonestFfgSupport := saturatingSub ffgSupportForCheckpoint adversarialWeight
  (addChecked minHonestFfgSupport remainingHonestFfgWeight).mapError .arith

/-- Whether no checkpoint that conflicts with the current target can become justified.

Honest votes for the target must exceed a third of the active balance. -/
def willNoConflictingCheckpointBeJustified (head : Root) : Except ForkChoiceError Bool := do
  if (← store.getCurrentTarget config head) = store.unrealizedJustifiedCheckpoint then return true
  let state ← store.getPulledUpHeadState config head
  let totalActiveBalance ← (getTotalActiveBalance state).mapError .accessor
  let honestFfgSupport ← store.computeHonestFfgSupportForCurrentTarget config head
  return totalActiveBalance < (← (mulChecked 3 honestFfgSupport).mapError .arith)

/-- Whether the target of the current epoch will become justified.

Honest votes for the target must reach two thirds of the active balance. -/
def willCurrentTargetBeJustified (head : Root) : Except ForkChoiceError Bool := do
  let state ← store.getPulledUpHeadState config head
  let totalActiveBalance ← (getTotalActiveBalance state).mapError .accessor
  let honestFfgSupport ← store.computeHonestFfgSupportForCurrentTarget config head
  return (← (mulChecked 2 totalActiveBalance).mapError .arith) ≤
    (← (mulChecked 3 honestFfgSupport).mapError .arith)

/-- The tracked heads and checkpoints after a new head at the start of a slot.

Before the last slot of an epoch ends, the greatest unrealized checkpoint is recorded.

At the start of an epoch, the observed justified checkpoints move one epoch on. -/
def updateFastConfirmationVariables (fcr : FastConfirmationStore) (head : Root) :
    Except ForkChoiceError FastConfirmationStore := do
  let mut fcr := { fcr with previousSlotHead := fcr.currentSlotHead, currentSlotHead := head }
  let currentSlot ← store.getCurrentSlot config
  if ← isStartSlotAtEpoch preset (← (addChecked currentSlot 1).mapError .arith) then
    fcr := { fcr with
      previousEpochGreatestUnrealizedCheckpoint := store.unrealizedJustifiedCheckpoint }
  if ← isStartSlotAtEpoch preset currentSlot then
    fcr := { fcr with
      previousEpochObservedJustifiedCheckpoint := fcr.currentEpochObservedJustifiedCheckpoint
      currentEpochObservedJustifiedCheckpoint := fcr.previousEpochGreatestUnrealizedCheckpoint }
  return fcr

/-- The latest confirmed block on the chain of the head, from a confirmed block onwards.

Blocks of the previous epoch are confirmed while each is safe and the old head holds it.

That needs the justification of the previous epoch to stay within reach.

Later blocks are confirmed while each is safe, and a new epoch needs its target justified.

The votes of the observed justified state are tallied once, for both walks. -/
def findLatestConfirmedDescendant (fcr : FastConfirmationStore) (head latestConfirmedRoot : Root) :
    Except ForkChoiceError Root := do
  let currentEpoch ← store.getCurrentStoreEpoch config
  let currentSlot ← store.getCurrentSlot config
  let isEpochStart ← isStartSlotAtEpoch preset currentSlot
  let arith {α : Type} (x : Except ArithError α) : Except ForkChoiceError α := x.mapError .arith
  let recent (epoch : Epoch) (gap : UInt64) : Except ForkChoiceError Bool := do
    return currentEpoch ≤ (← arith (addChecked epoch gap))
  let source := store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint
  let tally := source.map store.tallyVotes
  let mut confirmedRoot := latestConfirmedRoot
  -- The blocks of the previous epoch.
  let previousEpochOk ← do
    if (← arith (addChecked (← store.getBlockEpoch confirmedRoot) 1)) ≠ currentEpoch then
      pure false
    else if !(← recent (← store.getVotingSource config fcr.previousSlotHead).epoch 2) then
      pure false
    else if isEpochStart then pure true
    else if !(← store.willNoConflictingCheckpointBeJustified config head) then pure false
    else if ← recent (← store.unrealizedJustification fcr.previousSlotHead).epoch 1 then pure true
    else recent (← store.unrealizedJustification head).epoch 1
  if previousEpochOk then
    for root in ← store.getAncestorRoots head confirmedRoot do
      if (← store.getBlockEpoch root) = currentEpoch then break
      if !(← store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨root, .pending⟩) then break
      if !(← store.isOneConfirmed config head (← source) (← tally) root) then break
      confirmedRoot := root
  -- The blocks of the current epoch.
  let currentEpochOk ←
    if isEpochStart then pure true else recent (← store.unrealizedJustification head).epoch 1
  if currentEpochOk then
    let mut tentativeRoot := confirmedRoot
    for root in ← store.getAncestorRoots head confirmedRoot do
      if (← store.getBlockEpoch root) > (← store.getBlockEpoch tentativeRoot) then
        if !(← store.willCurrentTargetBeJustified config head) then break
      if !(← store.isOneConfirmed config head (← source) (← tally) root) then break
      tentativeRoot := root
    let accept ← do
      if (← store.getBlockEpoch tentativeRoot) = currentEpoch then pure true
      else if !(← recent (← store.getVotingSource config tentativeRoot).epoch 2) then pure false
      else if isEpochStart then pure true
      else store.willNoConflictingCheckpointBeJustified config head
    if accept then confirmedRoot := tentativeRoot
  return confirmedRoot

/-- The latest confirmed block.

The confirmed block falls back to the finalized one when it is too old.

It also falls back when it is off the chain of the head.

At the start of an epoch, it also falls back when its chain is not safe.

At the start of an epoch, a newer observed justified block of the previous epoch replaces it.

That needs the unrealized justification of the head to be that checkpoint. -/
def getLatestConfirmed (fcr : FastConfirmationStore) (head : Root) :
    Except ForkChoiceError Root := do
  let currentEpoch ← store.getCurrentStoreEpoch config
  let currentSlot ← store.getCurrentSlot config
  let arith {α : Type} (x : Except ArithError α) : Except ForkChoiceError α := x.mapError .arith
  let mut confirmedRoot := fcr.confirmedRoot
  let reset ← do
    if (← arith (addChecked (← store.getBlockEpoch confirmedRoot) 1)) < currentEpoch then
      pure true
    else if !(← store.isAncestor ⟨head, .pending⟩ ⟨confirmedRoot, .pending⟩) then pure true
    else if ← isStartSlotAtEpoch preset currentSlot then
      pure !(← store.isConfirmedChainSafe config fcr head confirmedRoot)
    else pure false
  if reset then confirmedRoot := store.finalizedCheckpoint.root
  let observed := fcr.currentEpochObservedJustifiedCheckpoint
  let isEpochStart ← isStartSlotAtEpoch preset currentSlot
  let observedSlot := (← store.block observed.root).slot
  let observedEpochOk :=
    (← arith (addChecked (computeEpochAtSlot preset observedSlot) 1)) = currentEpoch
  let headJustificationOk := observed = (← store.unrealizedJustification head)
  let confirmedStale := (← store.block confirmedRoot).slot < observedSlot
  if isEpochStart ∧ observedEpochOk ∧ headJustificationOk ∧ confirmedStale then
    confirmedRoot := observed.root
  if currentEpoch ≤ (← arith (addChecked (← store.getBlockEpoch confirmedRoot) 1)) then
    store.findLatestConfirmedDescendant config fcr head confirmedRoot
  else return confirmedRoot

/-- Whether a block is old enough that the checkpoint after it should be finalized by now. -/
def blockShouldBeFinalized (root : Root) : Except ForkChoiceError Bool := do
  let blockSlot := (← store.block root).slot
  let arith {α : Type} (x : Except ArithError α) : Except ForkChoiceError α := x.mapError .arith
  let nextCheckpointEpoch := computeEpochAtSlot preset
    (← arith (do subChecked (← addChecked blockSlot preset.SLOTS_PER_EPOCH) 1))
  let earliestFinalitySlot ←
    arith (do computeStartSlotAtEpoch preset (← addChecked nextCheckpointEpoch 2))
  return earliestFinalitySlot ≤ (← store.getCurrentSlot config)

/-- The confirmed block after a restart: the block confirmed before it, when that is still sound.

That block must be newer than the current confirmed one, and not yet due for finality.

It must also be on the chain of the head. -/
def getRestartResilientConfirmedRoot (fcr : FastConfirmationStore) (head rootBeforeRestart : Root) :
    Except ForkChoiceError Root := do
  if (← store.block rootBeforeRestart).slot ≤ (← store.block fcr.confirmedRoot).slot then
    return fcr.confirmedRoot
  if ← store.blockShouldBeFinalized config rootBeforeRestart then return fcr.confirmedRoot
  if !(← store.isAncestor ⟨head, .pending⟩ ⟨rootBeforeRestart, .pending⟩) then
    return fcr.confirmedRoot
  return rootBeforeRestart

end Store

/-- The fast confirmation store that starts from the finalized checkpoint of a store. -/
def getFastConfirmationStore (store : Store preset fork) : FastConfirmationStore where
  confirmedRoot := store.finalizedCheckpoint.root
  previousEpochObservedJustifiedCheckpoint := store.finalizedCheckpoint
  currentEpochObservedJustifiedCheckpoint := store.finalizedCheckpoint
  previousEpochGreatestUnrealizedCheckpoint := store.finalizedCheckpoint
  previousSlotHead := store.finalizedCheckpoint.root
  currentSlotHead := store.finalizedCheckpoint.root

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The fast confirmation of a slot: record the head, then move the confirmed block.

The store of the fork choice does not change meanwhile, so its head is computed once. -/
def onFastConfirmation (fcr : FastConfirmationStore) :
    Except ForkChoiceError FastConfirmationStore := do
  let head := (← store.getHead config).root
  let fcr ← store.updateFastConfirmationVariables config fcr head
  return { fcr with confirmedRoot := ← store.getLatestConfirmed config fcr head }

/-- From Bellatrix: the hash of the execution block that a block of the store stands for.

Before Gloas it is the block hash of the payload of the block.

From Gloas a block carries a bid instead of a payload.

The hash is then the parent payload that the bid builds on.

It fails when the store does not hold the block. -/
def executionBlockHashAt (root : Root) (bellatrix : .bellatrix ≤ fork) :
    Except ForkChoiceError Hash32 := do
  let block ← store.block root
  if gloas : .glamsterdam ≤ fork then
    return (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash
  else return (block.body.executionPayload ⟨bellatrix, Nat.lt_of_not_le gloas⟩).blockHash

/-- The hash of the execution block that the execution layer takes as safe.

The rule starts at Bellatrix, with the payload of the confirmed block.

From Gloas a block carries a bid instead of a payload.

Only the parent payload that the bid builds on is safe then. -/
def getSafeExecutionBlockHash (fcr : FastConfirmationStore) (bellatrix : .bellatrix ≤ fork) :
    Except ForkChoiceError Hash32 :=
  store.executionBlockHashAt fcr.confirmedRoot bellatrix

/-- The hash of the execution block that the execution layer takes as finalized.

The rule starts at Bellatrix, with the payload of the finalized block.

Before the merge that payload is the default one, whose block hash is zero.

From Gloas only the parent payload that the bid of the finalized block builds on is finalized. -/
def getFinalizedExecutionBlockHash (bellatrix : .bellatrix ≤ fork) :
    Except ForkChoiceError Hash32 :=
  store.executionBlockHashAt store.finalizedCheckpoint.root bellatrix

end Store

end EthLib.Consensus

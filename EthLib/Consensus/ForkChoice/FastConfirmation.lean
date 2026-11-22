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
  -- `s mod SLOTS_PER_EPOCH = 0`, for the slot `s`.
  return (← (computeSlotsSinceEpochStart preset slot).mapError .arith) = 0

/-- Whether the slots from a start to an end, both included, hold a whole epoch. -/
def isFullValidatorSetCovered (preset : Preset) (startSlot endSlot : Slot) :
    Except ForkChoiceError Bool := do
  -- Let `a` be the start, `b` the end and `P = SLOTS_PER_EPOCH`.
  --
  -- The epoch of slot `a + P - 1` is below the epoch of slot `b + 1`.
  let afterFirst ← (addChecked startSlot preset.SLOTS_PER_EPOCH).mapError .arith
  let lastOfFirst ← (subChecked afterFirst 1).mapError .arith
  let afterEnd ← (addChecked endSlot 1).mapError .arith
  return computeEpochAtSlot preset lastOfFirst < computeEpochAtSlot preset afterEnd

/-- The sum of a weight over a list, which must stay within 64 bits. -/
def sumGwei {α : Type} (items : List α) (weight : α → Except ForkChoiceError Gwei) :
    Except ForkChoiceError Gwei := do
  -- The sum is taken in natural numbers, then must be below `2^64`.
  let total ← items.foldlM (fun sum item => return sum + (← weight item).toNat) 0
  if 2 ^ 64 ≤ total then throw (.arith .overflow)
  return total.toUInt64

/-- The validator at an index of a state, or an error when the index is out of range. -/
def validatorAt (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except ForkChoiceError Validator :=
  (getValidator state index).mapError .accessor

namespace Store

variable (config : Config) (store : Store preset fork)

/-- The epoch of a known block. -/
def getBlockEpoch (root : Root) : Except ForkChoiceError Epoch :=
  -- `floor(s / SLOTS_PER_EPOCH)`, for the slot `s` of the block.
  return computeEpochAtSlot preset (← store.block root).slot

/-- The checkpoint of an epoch in the chain of a block. -/
def getCheckpointForBlock (root : Root) (epoch : Epoch) : Except ForkChoiceError Checkpoint :=
  -- The epoch, with the ancestor of the block at the first slot of the epoch.
  return ⟨epoch, ← store.getCheckpointBlock root epoch⟩

/-- The target of the current epoch in the chain of the head. -/
def getCurrentTarget (head : Root) : Except ForkChoiceError Checkpoint := do
  -- The checkpoint of the current epoch of the store, in the chain of the head.
  store.getCheckpointForBlock head (← store.getCurrentStoreEpoch config)

/-- The roots from a block back to a terminal block, oldest first, without the terminal block.

The list is empty when the terminal block is not in the chain of the block.

A parent at a slot no lower than its child is an error, so that the walk ends. -/
def getAncestorRoots (root terminal : Root) (acc : List Root := []) :
    Except ForkChoiceError (List Root) :=
  match _found : store.blocks[root]? with
  | none => throw (.unknownBlock root)
  | some block => do
    -- A block at a slot no later than the terminal block: the terminal is off the chain, so none.
    let terminalBlock ← store.block terminal
    if block.slot ≤ terminalBlock.slot then return []
    -- The block goes in front of the roots found so far.
    let acc := root :: acc
    -- The walk ends when the parent is the terminal block.
    if block.parentRoot = terminal then return acc
    match _parentFound : store.blocks[block.parentRoot]? with
    | none => throw (.unknownBlock block.parentRoot)
    | some parent =>
      -- Else it goes on from the parent.
      if _lower : parent.slot < block.slot then getAncestorRoots block.parentRoot terminal acc
      else throw (.parentSlotNotLower root)
termination_by (store.blocks[root]?.map (·.slot.toNat)).getD 0
decreasing_by
  simp only [_found, _parentFound, Option.map_some, Option.getD_some]
  exact UInt64.lt_iff_toNat_lt.mp _lower

/-- The members of every committee of a slot, shuffled as in the state of the head. -/
def getSlotCommittee (head : Root) (slot : Slot) :
    Except ForkChoiceError (Std.TreeSet ValidatorIndex) := do
  -- The shuffle comes from the state of the head.
  let shufflingSource ← store.blockState head
  -- The union of the committees of index `0` to `c - 1`, for `c` committees per slot.
  let count := getCommitteeCountPerSlot shufflingSource (computeEpochAtSlot preset slot)
  (List.range count.toNat).foldlM (init := ∅) fun participants index => do
    let committee ← (getBeaconCommittee shufflingSource slot index.toUInt64).mapError .accessor
    return committee.foldl (·.insert ·) participants

/-- The members of every committee of the slots from a start to an end, both included. -/
def getCommitteesBetweenSlots (head : Root) (startSlot endSlot : Slot) :
    Except ForkChoiceError (Std.TreeSet ValidatorIndex) := do
  -- The union of the committees of each slot `s` with `a ≤ s ≤ b`, for the bounds `a` and `b`.
  let afterEnd ← (addChecked endSlot 1).mapError .arith
  (List.range (afterEnd.toNat - startSlot.toNat)).foldlM (init := ∅) fun participants offset => do
    let committee ← store.getSlotCommittee head (startSlot + offset.toUInt64)
    return committee.foldl (·.insert ·) participants

/-- The weight of the committees of the slots from a start to an end, both included.

The members of those committees come with it when it reads them. -/
def computeCommitteeWeightAndMembers (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) :
    Except ForkChoiceError (Gwei × Option (Std.TreeSet ValidatorIndex)) := do
  -- A range that starts after it ends weighs nothing.
  if startSlot > endSlot then return (0, none)
  -- A range with a whole epoch weighs the total active balance of the source of balances.
  if ← isFullValidatorSetCovered preset startSlot endSlot then
    return (← (getTotalActiveBalance balanceSource).mapError .accessor, none)
  -- Else each member of the committees counts once.
  let participants ← store.getCommitteesBetweenSlots head startSlot endSlot
  -- It counts when it is active in the current epoch of the source of balances.
  let epoch := getCurrentEpoch balanceSource
  let active ← participants.toList.filterM fun index =>
    return isActiveValidator (← validatorAt balanceSource index) epoch
  -- The total of their effective balances there, at least `EFFECTIVE_BALANCE_INCREMENT`.
  return (← (getTotalBalance balanceSource active).mapError .accessor, some participants)

/-- The weight of the committees of the slots from a start to an end, both included. -/
def computeCommitteeWeightBetweenSlots (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  -- The weight alone, without the members.
  return (← store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot).1

/-- The state of the head, with its slots processed to the current epoch if it is older.

The pending deposits of an epoch from Electra check the signatures of new keys with BLS. -/
def getPulledUpHeadState (head : Root) : Except ForkChoiceError (BeaconState preset fork) := do
  let headState ← store.blockState head
  let currentEpoch ← store.getCurrentStoreEpoch config
  -- A state of an epoch before the current epoch `e` of the store has its slots processed.
  --
  -- They run up to slot `e * SLOTS_PER_EPOCH`.
  if getCurrentEpoch headState < currentEpoch then
    let start ← (computeStartSlotAtEpoch preset currentEpoch).mapError .arith
    (processSlots config .bls headState start).mapError .transition
  -- Else it is the state of the head.
  else return headState

/-- The votes for any of a list of nodes from the members of the committees of a range of slots.

The list is read as a set, since only membership in it is tested.

A voter counts when it is active and not slashed in the source of balances, and not an equivocator.

A vote from outside the range by a member of it may count too, which keeps the rule safe. -/
def getNodeSupportBetweenSlots (head : Root) (balanceSource : BeaconState preset fork)
    (nodes : List ForkChoiceNode) (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  -- The members of the committees of the range.
  let participants ← store.getCommitteesBetweenSlots head startSlot endSlot
  -- Those not slashed and active in the current epoch of the source of balances.
  let epoch := getCurrentEpoch balanceSource
  let counted ← participants.toList.filterM fun index => do
    let validator ← validatorAt balanceSource index
    return !validator.slashed && isActiveValidator validator epoch
  -- The sum of their effective balances, over those whose latest vote supports a listed node.
  sumGwei counted fun index => do
    match store.latestMessages[index]? with
    | none => return 0
    | some message =>
      -- An equivocator adds nothing.
      if (← store.getSupportedNode message) ∈ nodes ∧ index ∉ store.equivocatingIndices then
        return (← validatorAt balanceSource index).effectiveBalance
      else return 0

/-- The weight of the equivocators among a set of validators.

An equivocator counts when it is active in the source of balances. -/
def getEquivocationScoreOf (balanceSource : BeaconState preset fork)
    (participants : Std.TreeSet ValidatorIndex) : Except ForkChoiceError Gwei := do
  -- The equivocators of the set that are active in the current epoch of the source of balances.
  let epoch := getCurrentEpoch balanceSource
  let equivocators := participants.toList.filter (· ∈ store.equivocatingIndices)
  let active ← equivocators.filterM fun index => do
    return isActiveValidator (← validatorAt balanceSource index) epoch
  -- The sum of their effective balances there.
  sumGwei active fun index => return (← validatorAt balanceSource index).effectiveBalance

/-- The weight of the equivocators among the members of the committees of a range of slots. -/
def getEquivocationScore (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  -- The weight of the equivocators among the members of the committees of the range.
  store.getEquivocationScoreOf balanceSource
    (← store.getCommitteesBetweenSlots head startSlot endSlot)

/-- The largest weight that the adversary can hold in the committees of a range of slots.

The members of the committees are read once: by the weight when it needs them, else here. -/
def computeAdversarialWeight (head : Root) (balanceSource : BeaconState preset fork)
    (startSlot endSlot : Slot) : Except ForkChoiceError Gwei := do
  -- Let `W` be the weight of the committees of the range.
  --
  -- Let `β` be `CONFIRMATION_BYZANTINE_THRESHOLD`.
  let (maximumWeight, members) ←
    store.computeCommitteeWeightAndMembers head balanceSource startSlot endSlot
  -- The Byzantine share is `floor(W / 100) * β`.
  let maxAdversarialWeight ←
    (mulChecked (maximumWeight / 100) config.CONFIRMATION_BYZANTINE_THRESHOLD).mapError .arith
  -- The members come from the weight when it read them, so they are read once, the same set.
  let participants ← match members with
    | some participants => pure participants
    | none => store.getCommitteesBetweenSlots head startSlot endSlot
  -- Let `Q` be the weight of the equivocators among them.
  let equivocationScore ← store.getEquivocationScoreOf balanceSource participants
  -- The share less `Q`, or 0 when `Q` is larger.
  return saturatingSub maxAdversarialWeight equivocationScore

/-- The largest weight that the adversary can give a block, from its slot to the last slot. -/
def getAdversarialWeight (head : Root) (balanceSource : BeaconState preset fork) (root : Root) :
    Except ForkChoiceError Gwei := do
  let currentSlot ← store.getCurrentSlot config
  let block ← store.block root
  -- A block of a later epoch `e` than its parent counts from slot `e * SLOTS_PER_EPOCH`.
  let blockEpoch ← store.getBlockEpoch root
  let startSlot ← if blockEpoch > (← store.getBlockEpoch block.parentRoot) then
      (computeStartSlotAtEpoch preset blockEpoch).mapError .arith
    -- Else it counts from its own slot.
    else pure block.slot
  -- The range ends at slot `t - 1`, for the current slot `t`.
  let lastSlot ← (subChecked currentSlot 1).mapError .arith
  -- The adversarial weight of the committees of that range.
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
  -- Let `p` be the slot of the parent and `s` the slot of the block.
  let block ← store.block root
  let parentBlock ← store.block block.parentRoot
  -- With `s = p + 1` there is no empty slot, and the discount is 0.
  let firstEmpty ← (addChecked parentBlock.slot 1).mapError .arith
  if firstEmpty = block.slot then return 0
  -- The nodes of the parent are its pending node.
  let parentPendingNode : ForkChoiceNode := ⟨block.parentRoot, .pending⟩
  let parentNodes ←
    -- From Gloas they also hold the ancestor of the block at slot `p`.
    (if .glamsterdam ≤ fork then do
      let parentNode ← store.getAncestor ⟨root, .pending⟩ parentBlock.slot
      pure [parentPendingNode, parentNode]
    else pure [parentPendingNode])
  -- Let `S` be the votes for those nodes from the committees of slots `p + 1` to `s - 1`.
  let lastEmpty ← (subChecked block.slot 1).mapError .arith
  let parentSupport ←
    store.getNodeSupportBetweenSlots head balanceSource parentNodes firstEmpty lastEmpty
  -- Let `A` be the adversarial weight of the same slots.
  let adversarialWeight ←
    store.computeAdversarialWeight config head balanceSource firstEmpty lastEmpty
  -- The discount is `S - A`, or 0 when `A` is larger.
  return saturatingSub parentSupport adversarialWeight

/-- The votes that a block needs to be safe for LMD-GHOST.

Its discount for empty slots must not exceed the weight of the committees since its parent.

A larger discount is an error. -/
def computeSafetyThreshold (head : Root) (root : Root) (balanceSource : BeaconState preset fork) :
    Except ForkChoiceError Gwei := do
  -- Let `t` be the current slot and `p` the slot of the parent.
  let currentSlot ← store.getCurrentSlot config
  let block ← store.block root
  let parentBlock ← store.block block.parentRoot
  -- Let `B` be the boost, from the source of balances.
  let proposerScore ← computeProposerScore config balanceSource
  -- Let `M` be the weight of the committees of slots `p + 1` to `t - 1`.
  let maximumSupport ← store.computeCommitteeWeightBetweenSlots head balanceSource
    (← (addChecked parentBlock.slot 1).mapError .arith)
    (← (subChecked currentSlot 1).mapError .arith)
  -- Let `D` be the discount for the empty slots before the block.
  let supportDiscount ← store.computeEmptySlotSupportDiscount config head balanceSource root
  -- Let `A` be the adversarial weight that can support the block.
  let adversarialWeight ← store.getAdversarialWeight config head balanceSource root
  -- `D ≤ M`, else an error.
  if supportDiscount > maximumSupport then throw (.supportDiscountAboveMaximum root)
  -- The threshold is `floor((M + B + 2A - D) / 2)`, which is `floor((M + B - D) / 2) + A`.
  let withBoost ← (addChecked maximumSupport proposerScore).mapError .arith
  let doubled ← (mulChecked 2 adversarialWeight).mapError .arith
  let bound ← (addChecked withBoost doubled).mapError .arith
  return (bound - supportDiscount) / 2

/-- Whether a block is safe for LMD-GHOST: its votes exceed its safety threshold.

The votes come from the given tally, which must be the one of the balance source.

Every known block counts as valid here, since the store drops the blocks found invalid. -/
def isOneConfirmed (head : Root) (balanceSource : BeaconState preset fork) (tally : VoteTally)
    (root : Root) : Except ForkChoiceError Bool := do
  -- The votes for the pending node of the block exceed its safety threshold.
  let support ← store.scoreFromTally tally ⟨root, .pending⟩
  return support > (← store.computeSafetyThreshold config head root balanceSource)

/-- Whether every block of the confirmed chain is still safe, from the observed justified block.

The votes of the balance source are tallied once, for the whole chain. -/
def isConfirmedChainSafe (fcr : FastConfirmationStore) (head confirmedRoot : Root) :
    Except ForkChoiceError Bool := do
  -- The observed justified checkpoint of the current epoch is in the chain of the confirmed block.
  let observed := fcr.currentEpochObservedJustifiedCheckpoint
  if observed ≠ (← store.getCheckpointForBlock confirmedRoot observed.epoch) then return false
  -- Let `e` be the current epoch and `j` the epoch of that checkpoint.
  let currentEpoch ← store.getCurrentStoreEpoch config
  let startRootExclusive ←
    -- With `e ≤ j + 1` the chain starts after the block of the checkpoint.
    if currentEpoch ≤ (← (addChecked observed.epoch 1).mapError .arith) then pure observed.root
    else do
      -- Else let `a` be the ancestor of the confirmed block at slot `(e - 1) * SLOTS_PER_EPOCH`.
      let previousEpoch ← (subChecked currentEpoch 1).mapError .arith
      let previousStart ← (computeStartSlotAtEpoch preset previousEpoch).mapError .arith
      let ancestor := (← store.getAncestor ⟨confirmedRoot, .pending⟩ previousStart).root
      -- When `a` is of epoch `e - 1`, the chain starts at `a`, after its parent.
      if (← (addChecked (← store.getBlockEpoch ancestor) 1).mapError .arith) = currentEpoch then
        pure (← store.block ancestor).parentRoot
      -- Else `a` is the last block before epoch `e - 1`, and the chain starts after it.
      else pure ancestor
  let chainRoots ← store.getAncestorRoots confirmedRoot startRootExclusive
  -- The source of balances is the state of the observed justified checkpoint of the previous epoch.
  --
  -- Its votes are tallied once, for every block of the chain.
  let source := store.checkpointState fcr.previousEpochObservedJustifiedCheckpoint
  let tally := source.map store.tallyVotes
  -- Each block of the chain is safe for LMD-GHOST.
  chainRoots.allM fun root => do
    store.isOneConfirmed config head (← source) (← tally) root

/-- An estimate of the votes for the target of the current epoch, from the latest messages. -/
def getCurrentTargetScore (head : Root) : Except ForkChoiceError Gwei := do
  let target ← store.getCurrentTarget config head
  -- The validators active and not slashed in the pulled-up state of the head.
  let state ← store.getPulledUpHeadState config head
  let counted ← (getActiveValidatorIndices state (getCurrentEpoch state)).filterM fun index =>
    return !(← validatorAt state index).slashed
  -- The sum of their effective balances there, over those whose latest vote is for the target.
  sumGwei counted fun index => do
    match store.latestMessages[index]? with
    | none => return 0
    | some message =>
      -- An equivocator adds nothing.
      if index ∈ store.equivocatingIndices then return 0
      -- The vote is for the target when the checkpoint of its block at its epoch is the target.
      let epoch := getLatestMessageEpoch preset message
      if target = (← store.getCheckpointForBlock message.root epoch) then
        return (← validatorAt state index).effectiveBalance
      else return 0

/-- The honest votes that the target of the current epoch will get, at the least. -/
def computeHonestFfgSupportForCurrentTarget (head : Root) : Except ForkChoiceError Gwei := do
  -- Let `t` be the current slot and `e` its epoch.
  let currentSlot ← store.getCurrentSlot config
  let currentEpoch := computeEpochAtSlot preset currentSlot
  -- Let `T` be the total active balance of the pulled-up state of the head.
  let balanceSource ← store.getPulledUpHeadState config head
  let totalActiveBalance ← (getTotalActiveBalance balanceSource).mapError .accessor
  -- Let `S` be the estimate of the votes for the target.
  let ffgSupportForCheckpoint ← store.getCurrentTargetScore config head
  -- Let `W` be the weight of the committees of slots `e * SLOTS_PER_EPOCH` to `t - 1`.
  let epochStart ← (computeStartSlotAtEpoch preset currentEpoch).mapError .arith
  let lastSlot ← (subChecked currentSlot 1).mapError .arith
  let ffgWeightTillNow ←
    store.computeCommitteeWeightBetweenSlots head balanceSource epochStart lastSlot
  -- Let `β` be `CONFIRMATION_BYZANTINE_THRESHOLD`.
  --
  -- The honest share of the slots to come is `floor((T - W) / 100) * (100 - β)`.
  let remainingFfgWeight ← (subChecked totalActiveBalance ffgWeightTillNow).mapError .arith
  let honestShare ← (subChecked 100 config.CONFIRMATION_BYZANTINE_THRESHOLD).mapError .arith
  let remainingHonestFfgWeight ←
    (mulChecked (remainingFfgWeight / 100) honestShare).mapError .arith
  -- Let `A` be the adversarial weight of the same slots as `W`.
  let adversarialWeight ←
    store.computeAdversarialWeight config head balanceSource epochStart lastSlot
  -- The votes so far less the adversary, `S - A` or 0 when `A` is larger.
  let minHonestFfgSupport := saturatingSub ffgSupportForCheckpoint adversarialWeight
  -- The sum of the two.
  (addChecked minHonestFfgSupport remainingHonestFfgWeight).mapError .arith

/-- Whether no checkpoint that conflicts with the current target can become justified. -/
def willNoConflictingCheckpointBeJustified (head : Root) : Except ForkChoiceError Bool := do
  -- When the target is the unrealized justified checkpoint of the store, no other can be justified.
  if (← store.getCurrentTarget config head) = store.unrealizedJustifiedCheckpoint then return true
  -- Let `T` be the total active balance of the pulled-up state of the head.
  let state ← store.getPulledUpHeadState config head
  let totalActiveBalance ← (getTotalActiveBalance state).mapError .accessor
  -- Let `H` be the honest votes for the target, at the least.
  let honestFfgSupport ← store.computeHonestFfgSupportForCurrentTarget config head
  -- `T < 3H`.
  return totalActiveBalance < (← (mulChecked 3 honestFfgSupport).mapError .arith)

/-- Whether the target of the current epoch will become justified. -/
def willCurrentTargetBeJustified (head : Root) : Except ForkChoiceError Bool := do
  -- Let `T` be the total active balance of the pulled-up state of the head.
  let state ← store.getPulledUpHeadState config head
  let totalActiveBalance ← (getTotalActiveBalance state).mapError .accessor
  -- Let `H` be the honest votes for the target, at the least.
  let honestFfgSupport ← store.computeHonestFfgSupportForCurrentTarget config head
  -- `2T ≤ 3H`.
  return (← (mulChecked 2 totalActiveBalance).mapError .arith) ≤
    (← (mulChecked 3 honestFfgSupport).mapError .arith)

/-- The tracked heads and checkpoints after a new head at the start of a slot. -/
def updateFastConfirmationVariables (fcr : FastConfirmationStore) (head : Root) :
    Except ForkChoiceError FastConfirmationStore := do
  -- The head of the current slot becomes that of the previous slot, and the new head comes in.
  let mut fcr := { fcr with previousSlotHead := fcr.currentSlotHead, currentSlotHead := head }
  -- In the last slot of an epoch, the unrealized justified checkpoint of the store is recorded.
  --
  -- That slot `t` is the one where `t + 1` starts an epoch.
  let currentSlot ← store.getCurrentSlot config
  if ← isStartSlotAtEpoch preset (← (addChecked currentSlot 1).mapError .arith) then
    fcr := { fcr with
      previousEpochGreatestUnrealizedCheckpoint := store.unrealizedJustifiedCheckpoint }
  -- At the start of an epoch, the observed justified checkpoints move one epoch on.
  --
  -- The previous one takes the current one, and the current one takes the recorded checkpoint.
  if ← isStartSlotAtEpoch preset currentSlot then
    fcr := { fcr with
      previousEpochObservedJustifiedCheckpoint := fcr.currentEpochObservedJustifiedCheckpoint
      currentEpochObservedJustifiedCheckpoint := fcr.previousEpochGreatestUnrealizedCheckpoint }
  return fcr

/-- The latest confirmed block on the chain of the head, from a confirmed block onwards.

The votes of the observed justified state are tallied once, for both walks. -/
def findLatestConfirmedDescendant (fcr : FastConfirmationStore) (head latestConfirmedRoot : Root) :
    Except ForkChoiceError Root := do
  -- Let `e` be the current epoch.
  let currentEpoch ← store.getCurrentStoreEpoch config
  let currentSlot ← store.getCurrentSlot config
  let isEpochStart ← isStartSlotAtEpoch preset currentSlot
  let arith {α : Type} (x : Except ArithError α) : Except ForkChoiceError α := x.mapError .arith
  -- An epoch `x` is recent within a gap `g` when `e ≤ x + g`.
  let recent (epoch : Epoch) (gap : UInt64) : Except ForkChoiceError Bool := do
    return currentEpoch ≤ (← arith (addChecked epoch gap))
  -- The source of balances is the state of the observed justified checkpoint of the current epoch.
  --
  -- Its votes are tallied once, for both walks.
  let source := store.checkpointState fcr.currentEpochObservedJustifiedCheckpoint
  let tally := source.map store.tallyVotes
  let mut confirmedRoot := latestConfirmedRoot
  -- The blocks of the previous epoch.
  let previousEpochOk ← do
    -- The confirmed block is of epoch `e - 1`.
    if (← arith (addChecked (← store.getBlockEpoch confirmedRoot) 1)) ≠ currentEpoch then
      pure false
    -- The voting source of the head of the previous slot is recent within 2.
    else if !(← recent (← store.getVotingSource config fcr.previousSlotHead).epoch 2) then
      pure false
    -- Then the start of an epoch is enough.
    else if isEpochStart then pure true
    -- Else no checkpoint that conflicts with the current target can become justified.
    else if !(← store.willNoConflictingCheckpointBeJustified config head) then pure false
    -- And the unrealized justification of the head of the previous slot, or of the head, is recent.
    --
    -- Recent means within 1 epoch.
    else if ← recent (← store.unrealizedJustification fcr.previousSlotHead).epoch 1 then pure true
    else recent (← store.unrealizedJustification head).epoch 1
  if previousEpochOk then
    -- The walk goes from the child of the confirmed block towards the head.
    for root in ← store.getAncestorRoots head confirmedRoot do
      -- It stops at the first block of epoch `e`.
      if (← store.getBlockEpoch root) = currentEpoch then break
      -- It stops at a block that the head of the previous slot does not descend from.
      if !(← store.isAncestor ⟨fcr.previousSlotHead, .pending⟩ ⟨root, .pending⟩) then break
      -- It stops at a block that is not safe for LMD-GHOST.
      if !(← store.isOneConfirmed config head (← source) (← tally) root) then break
      -- Else the block is confirmed.
      confirmedRoot := root
  -- The blocks of the current epoch.
  --
  -- They need the start of an epoch, or an unrealized justification of the head recent within 1.
  let currentEpochOk ←
    if isEpochStart then pure true else recent (← store.unrealizedJustification head).epoch 1
  if currentEpochOk then
    let mut tentativeRoot := confirmedRoot
    -- The walk goes from the child of the confirmed block towards the head.
    for root in ← store.getAncestorRoots head confirmedRoot do
      -- A block of a later epoch than the tentative block needs the target of the current epoch.
      --
      -- That target must be predicted to become justified.
      if (← store.getBlockEpoch root) > (← store.getBlockEpoch tentativeRoot) then
        if !(← store.willCurrentTargetBeJustified config head) then break
      -- It stops at a block that is not safe for LMD-GHOST.
      if !(← store.isOneConfirmed config head (← source) (← tally) root) then break
      -- Else the block becomes the tentative block.
      tentativeRoot := root
    -- The tentative block is confirmed when it is of epoch `e`.
    let accept ← do
      if (← store.getBlockEpoch tentativeRoot) = currentEpoch then pure true
      -- Else its voting source is recent within 2.
      else if !(← recent (← store.getVotingSource config tentativeRoot).epoch 2) then pure false
      -- It is also the start of an epoch, or no conflicting checkpoint can become justified.
      else if isEpochStart then pure true
      else store.willNoConflictingCheckpointBeJustified config head
    if accept then confirmedRoot := tentativeRoot
  return confirmedRoot

/-- The latest confirmed block.

When the assumptions of the rule seem broken, it falls back to the finalized block. -/
def getLatestConfirmed (fcr : FastConfirmationStore) (head : Root) :
    Except ForkChoiceError Root := do
  -- Let `e` be the current epoch.
  let currentEpoch ← store.getCurrentStoreEpoch config
  let currentSlot ← store.getCurrentSlot config
  let arith {α : Type} (x : Except ArithError α) : Except ForkChoiceError α := x.mapError .arith
  let mut confirmedRoot := fcr.confirmedRoot
  -- The confirmed block falls back to the finalized block in three cases.
  let reset ← do
    -- Its epoch `x` is too old: `x + 1 < e`.
    if (← arith (addChecked (← store.getBlockEpoch confirmedRoot) 1)) < currentEpoch then
      pure true
    -- It is off the chain of the head.
    else if !(← store.isAncestor ⟨head, .pending⟩ ⟨confirmedRoot, .pending⟩) then pure true
    -- At the start of an epoch, its chain is not safe.
    else if ← isStartSlotAtEpoch preset currentSlot then
      pure !(← store.isConfirmedChainSafe config fcr head confirmedRoot)
    else pure false
  if reset then confirmedRoot := store.finalizedCheckpoint.root
  -- The block of the observed justified checkpoint replaces it when four conditions hold.
  --
  -- It is the start of an epoch.
  --
  -- The block of the checkpoint is of epoch `e - 1`.
  --
  -- The checkpoint is the unrealized justification of the head.
  --
  -- The confirmed block is at a lower slot than the block of the checkpoint.
  let observed := fcr.currentEpochObservedJustifiedCheckpoint
  let isEpochStart ← isStartSlotAtEpoch preset currentSlot
  let observedSlot := (← store.block observed.root).slot
  let observedEpochOk :=
    (← arith (addChecked (computeEpochAtSlot preset observedSlot) 1)) = currentEpoch
  let headJustificationOk := observed = (← store.unrealizedJustification head)
  let confirmedStale := (← store.block confirmedRoot).slot < observedSlot
  if isEpochStart ∧ observedEpochOk ∧ headJustificationOk ∧ confirmedStale then
    confirmedRoot := observed.root
  -- A confirmed block of epoch `x` with `e ≤ x + 1` moves on along the chain of the head.
  --
  -- Else it stays.
  if currentEpoch ≤ (← arith (addChecked (← store.getBlockEpoch confirmedRoot) 1)) then
    store.findLatestConfirmedDescendant config fcr head confirmedRoot
  else return confirmedRoot

/-- Whether a block is old enough that the checkpoint after it should be finalized by now. -/
def blockShouldBeFinalized (root : Root) : Except ForkChoiceError Bool := do
  -- Let `s` be the slot of the block and `P = SLOTS_PER_EPOCH`.
  let blockSlot := (← store.block root).slot
  let arith {α : Type} (x : Except ArithError α) : Except ForkChoiceError α := x.mapError .arith
  -- The next checkpoint is of epoch `n = floor((s + P - 1) / P)`.
  let nextCheckpointEpoch := computeEpochAtSlot preset
    (← arith (do subChecked (← addChecked blockSlot preset.SLOTS_PER_EPOCH) 1))
  -- It can be finalized from slot `(n + 2) * P` on.
  let earliestFinalitySlot ←
    arith (do computeStartSlotAtEpoch preset (← addChecked nextCheckpointEpoch 2))
  -- That slot is at most the current slot.
  return earliestFinalitySlot ≤ (← store.getCurrentSlot config)

/-- The confirmed block after a restart: the block confirmed before it, when that is still sound. -/
def getRestartResilientConfirmedRoot (fcr : FastConfirmationStore) (head rootBeforeRestart : Root) :
    Except ForkChoiceError Root := do
  -- Let `r` be the block confirmed before the restart.
  --
  -- The current confirmed block stays when its slot is at least that of `r`.
  if (← store.block rootBeforeRestart).slot ≤ (← store.block fcr.confirmedRoot).slot then
    return fcr.confirmedRoot
  -- It stays when `r` is old enough to be due for finality.
  if ← store.blockShouldBeFinalized config rootBeforeRestart then return fcr.confirmedRoot
  -- It stays when `r` is off the chain of the head.
  if !(← store.isAncestor ⟨head, .pending⟩ ⟨rootBeforeRestart, .pending⟩) then
    return fcr.confirmedRoot
  -- Else the block confirmed before the restart is the confirmed block.
  return rootBeforeRestart

end Store

/-- The fast confirmation store that starts from the finalized checkpoint of a store. -/
def getFastConfirmationStore (store : Store preset fork) : FastConfirmationStore where
  -- Each field is the finalized checkpoint of the store, or its root.
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
  -- The head, computed once for the whole slot.
  let head := (← store.getHead config).root
  -- The tracked heads and checkpoints move first.
  let fcr ← store.updateFastConfirmationVariables config fcr head
  -- Then the confirmed block becomes the latest confirmed block.
  return { fcr with confirmedRoot := ← store.getLatestConfirmed config fcr head }

/-- From Bellatrix: the hash of the execution block that a block of the store stands for.

It fails when the store does not hold the block. -/
def executionBlockHashAt (root : Root) (bellatrix : .bellatrix ≤ fork) :
    Except ForkChoiceError Hash32 := do
  let block ← store.block root
  -- From Gloas a block carries a bid instead of a payload.
  --
  -- The hash is that of the parent payload that the bid builds on.
  if gloas : .glamsterdam ≤ fork then
    return (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash
  -- Before Gloas it is the block hash of the payload of the block.
  else return (block.body.executionPayload ⟨bellatrix, Nat.lt_of_not_le gloas⟩).blockHash

/-- The hash of the execution block that the execution layer takes as safe.

The rule starts at Bellatrix, with the payload of the confirmed block.

From Gloas a block carries a bid instead of a payload.

Only the parent payload that the bid builds on is safe then. -/
def getSafeExecutionBlockHash (fcr : FastConfirmationStore) (bellatrix : .bellatrix ≤ fork) :
    Except ForkChoiceError Hash32 :=
  -- The execution block that the confirmed block stands for.
  store.executionBlockHashAt fcr.confirmedRoot bellatrix

/-- The hash of the execution block that the execution layer takes as finalized.

The rule starts at Bellatrix, with the payload of the finalized block.

Before the merge that payload is the default one, whose block hash is zero.

From Gloas only the parent payload that the bid of the finalized block builds on is finalized. -/
def getFinalizedExecutionBlockHash (bellatrix : .bellatrix ≤ fork) :
    Except ForkChoiceError Hash32 :=
  -- The execution block that the finalized block stands for.
  store.executionBlockHashAt store.finalizedCheckpoint.root bellatrix

end Store

end EthLib.Consensus

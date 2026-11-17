module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
public import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
public import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
public import EthLib.Consensus.Proofs.ForkChoice.SharedAncestry
public import EthLib.Consensus.Proofs.ForkChoice.Supporters
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.DutySupport
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets
public import EthLib.Consensus.Proofs.Transition.FfgJustification

/-!
# Observations for historical-anchor transport

These predicates state the observations and evidence alternatives of the historical endpoint.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}

/-- The state is held by the store or obtained by processing slots toward a held child. -/
def CountedState (store : Store preset fork) (config : Config)
    (state : BeaconState preset fork) : Prop :=
  ∃ (root : Root) (base : BeaconState preset fork), store.blockStates[root]? = some base ∧
    (state = base ∨ ∃ (checks : SignatureChecks) (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), store.blocks[childRoot]? = some child ∧
      child.parentRoot = root ∧ slot ≤ child.slot ∧
      processSlots config checks base slot = .ok state)

/-- The validators active at the state's current epoch. -/
def activeVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

/-- Stake of the source state that may leave the active set soon.

It counts the active validators whose exit epoch is at most two epochs after the current one.

From Electra, it adds the exit and consolidation churn limits and the balances left to consume.

A churn limit that fails to read counts as 0.

From Electra, it also adds a slack of `2 * MAX_EFFECTIVE_BALANCE_ELECTRA`.

Before Electra, it adds the validator churn limit, at least 1, times `MAX_EFFECTIVE_BALANCE`. -/
def exitReserve (config : Config) (source : BeaconState preset fork) : Nat :=
  stake (fun v => balanceAt source v.toNat)
    {v ∈ activeVoters source | (source.validators.data[v.toNat]?).any fun validator =>
      validator.exitEpoch.toNat ≤ (getCurrentEpoch source).toNat + 2} +
    if electra : .pectra ≤ fork then
      ((exitChurnLimit config source).toOption.getD 0).toNat +
        (source.exitBalanceToConsume electra).toNat +
        ((getConsolidationChurnLimit config source).toOption.getD 0).toNat +
        (source.consolidationBalanceToConsume electra).toNat +
        2 * preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    else max 1 (getValidatorChurnLimit config source).toNat * preset.MAX_EFFECTIVE_BALANCE.toNat

/-- Every block held by the store has a nonzero state root. -/
def HeldStateRootsNonzero (store : Store preset fork) : Prop :=
  ∀ (r : Root) (b : BeaconBlock preset fork), store.blocks[r]? = some b →
    b.stateRoot ≠ Vector.replicate 32 0

variable {e : Execution (honestForkChoice config checks sources anchorState anchorBlock
  assignment genesisTimeMs) J}

/-- Honest duties due by the horizon produce votes that pass their target-state committee check. -/
def ValidatedDutyVotes (last : Nat) : Prop :=
  ∀ v ∈ J, ∀ slot committeeIndex deadline,
    assignment.committee v slot = some committeeIndex →
    IsAttestationDeadline fork config genesisTimeMs slot deadline →
    e.startTime ≤ deadline → deadline ≤ last →
    ∃ n attestation indexed, VoteAt e v slot committeeIndex deadline n attestation indexed ∧
      ∀ withTarget targetState,
        ((e.world n).state v).storeTargetCheckpointState config checks attestation.data.target =
          .ok withTarget →
        withTarget.checkpointState attestation.data.target = .ok targetState →
        checkAttestationCommittees targetState attestation = .ok ()

/-- Honest assignment duties agree with the committee windows read from each eligible head. -/
def AssignmentWindowAgreement (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
    ∀ (head : ForkChoiceNode) current first finish participants,
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).getCurrentSlot config = .ok current → finish < current →
    (∀ headState, ((e.world k).state w).blockState head.root = .ok headState →
      (getCurrentEpoch headState).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 <
        (computeEpochAtSlot preset first).toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) →
    ((e.world k).state w).getCommitteesBetweenSlots head.root first finish = .ok participants →
    ∀ v ∈ J, v ∈ participants ↔ ∃ slot committeeIndex, first ≤ slot ∧ slot ≤ finish ∧
      assignment.committee v slot = some committeeIndex

/-- Each later successful window read also succeeds with the source state's weights and boost.

With positive `SLOTS_PER_EPOCH`, only a member missing from the source, or overflow, breaks it. -/
def SourceWindowReads (call last : Nat) (source : BeaconState preset fork) : Prop :=
  ∀ w ∈ J, ∀ k (head : ForkChoiceNode) state current first finish maximum,
    (e.world call).time ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).getCurrentSlot config = .ok current → finish < current →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state first finish =
      .ok maximum →
    ∃ sourceMaximum sourceScore,
      ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root source first finish =
        .ok sourceMaximum ∧ computeProposerScore config source = .ok sourceScore

/-- Honest stores have current epochs within the approved horizon. -/
def HonestStoreEpochsBounded (horizon : Epoch) (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k epoch, (e.world k).time ≤ last →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon

/-- A vote below a known block, with a slot in the window of the store's head after that block.

The head descends from the block, and the store's epoch is at most two epochs after the block's.

The window ends at the slot before the store's current slot.

The vote has an origin, and the members are the committees of the head state in the window. -/
def VoteInHeadWindow (config : Config) (store : Store preset fork) (parentRoot : Root)
    (parent : BeaconBlock preset fork) (members : Std.TreeSet ValidatorIndex)
    (v : ValidatorIndex) (attestation : Attestation preset fork) : Prop :=
  ∃ (head : ForkChoiceNode) (current first finish : Slot) (epoch : Epoch),
    store.getHead config = .ok head ∧
    store.blocks[parentRoot]? = some parent ∧
    store.isAncestor ⟨head.root, .pending⟩ ⟨parentRoot, .pending⟩ = .ok true ∧
    store.getCurrentSlot config = .ok current ∧
    store.getCurrentStoreEpoch config = .ok epoch ∧
    epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat + 2 ∧
    addChecked parent.slot 1 = .ok first ∧ subChecked current 1 = .ok finish ∧
    store.getCommitteesBetweenSlots head.root first finish = .ok members ∧
    store.VoteOrigin config v attestation ∧
    store.isAncestor ⟨attestation.data.beaconBlockRoot, .pending⟩ ⟨parentRoot, .pending⟩ =
      .ok true ∧
    first ≤ attestation.data.slot ∧ attestation.data.slot ≤ finish

/-- From the first time to the last, each voter below the parent is in each honest head's window. -/
def VotersInHeadWindow (parentRoot : Root) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, first ≤ (e.world k).time → (e.world k).time ≤ last →
    ∀ parent members v attestation,
    VoteInHeadWindow config ((e.world k).state w) parentRoot parent members v attestation →
    v ∈ members

/-- The voters activated at the target of a vote two epochs after the parent are in the window.

Every other voter below the parent lies in the window by a proof. -/
def NewlyActiveVotersInHeadWindow (parentRoot : Root) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, first ≤ (e.world k).time → (e.world k).time ≤ last →
    ∀ parent members v attestation (targetState : BeaconState preset fork) (voter : Validator),
    VoteInHeadWindow config ((e.world k).state w) parentRoot parent members v attestation →
    (computeEpochAtSlot preset parent.slot).toNat + 2 = attestation.data.target.epoch.toNat →
    ((e.world k).state w).checkpointStates[attestation.data.target]? = some targetState →
    targetState.validators.data[v.toNat]? = some voter →
    voter.activationEpoch = attestation.data.target.epoch →
    v ∈ members

/-- Honest stores do not hold the parent of the anchor before the deadline. -/
def AnchorParentAbsent (last : Nat) : Prop :=
  ∀ a ∈ J, ∀ i, (e.world i).time ≤ last →
    ((e.world i).state a).blocks[anchorBlock.parentRoot]? = none

/-- The approved drift bound compares honest finite stakes in source and receiver balances. -/
def WindowMarginDrift (call last : Nat) (source : BeaconState preset fork)
    (shift : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (head : ForkChoiceNode) state score sourceScore first finish maximum sourceMaximum,
    (e.world call).time ≤ (e.world k).time → (e.world k).time ≤ last →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    computeProposerScore config state = .ok score →
    computeProposerScore config source = .ok sourceScore →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root state first finish =
      .ok maximum →
    ((e.world k).state w).computeCommitteeWeightBetweenSlots head.root source first finish =
      .ok sourceMaximum →
    ∀ p q : Finset ValidatorIndex, (∀ v ∈ p, v ∈ J) → (∀ v ∈ q, v ∈ J) →
    let sourceWeight := fun v => if v ∈ ((unslashedActiveBalances source).map (·.1)).toFinset
      then balanceAt source v.toNat else 0
    let receiverWeight := fun v => if v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset
      then balanceAt state v.toNat else 0
    2 * stake sourceWeight p + stake sourceWeight q + maximum.toNat + score.toNat ≤
      2 * stake receiverWeight p + stake receiverWeight q + sourceMaximum.toNat +
        sourceScore.toNat + shift

/-- The active stake of a balance state is bounded by the supplied cap. -/
def ActiveStakeAtMost (cap : Nat) (state : BeaconState preset fork) : Prop :=
  stake (fun v => balanceAt state v.toNat)
    (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset ≤ cap

/-- Every honest checkpoint state read before the deadline has active stake at most the cap. -/
def CheckpointStakeCeiling (cap last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k checkpoint state, (e.world k).time ≤ last →
    ((e.world k).state w).checkpointState checkpoint = .ok state → ActiveStakeAtMost cap state

variable [DecidablePred (· ∈ J)]

/-- Each nonempty window of the head between the two slots has little Byzantine stake.

Its Byzantine stake plus half the exit reserve is within the threshold share of its active stake.

Stakes are the source state's balances of the window's members active at the source. -/
def SourceWindowReserve (store : Store preset fork) (head : Root)
    (source : BeaconState preset fork) (first last : Slot) : Prop :=
  ∀ low high participants, first ≤ low → low ≤ high → high ≤ last →
    store.getCommitteesBetweenSlots head low high = .ok participants →
    100 * stake (fun v => balanceAt source v.toNat)
        {v ∈ Store.activeMembers source participants | v ∉ J} +
      50 * exitReserve config source ≤ config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat *
        stake (fun v => balanceAt source v.toNat) (Store.activeMembers source participants)

/-- Each full epoch in the window omits at most the exit reserve of active source stake. -/
def WindowExitBound (store : Store preset fork) (source : BeaconState preset fork)
    (head : Root) (first last : Slot) : Prop :=
  ∀ epoch epochStart next epochEnd epochMembers,
    computeStartSlotAtEpoch preset epoch = .ok epochStart →
    addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next →
    subChecked next 1 = .ok epochEnd → first ≤ epochStart → epochEnd ≤ last →
    store.getCommitteesBetweenSlots head epochStart epochEnd = .ok epochMembers →
    stake (fun v => balanceAt source v.toNat)
      {v ∈ activeVoters source | v ∉ epochMembers} ≤ exitReserve config source

/-- All honest stores hold only blocks with nonzero state roots through the horizon. -/
def HeldBlockStateRootsNonzero (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last → HeldStateRootsNonzero ((e.world k).state w)

/-- No honest validator has a true slashed flag in a counted state through the horizon. -/
def HonestCountedStatesUnslashed (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k state, (e.world k).time ≤ last →
    CountedState ((e.world k).state w) config state →
    ∀ v ∈ J, (slashedFlagAt state v.toNat).getD false = false

/-- Every up-to-date honest head descends from the root throughout the half-open time interval. -/
def HonestHeadsCover (root : Root) (first last : Nat) : Prop :=
  ∀ earlier, first ≤ earlier → earlier < last → ∀ a ∈ J, ∀ i hd,
    (e.world i).time = earlier →
    UpToDate config checks sources (e.world i).time ((e.world i).view a) ((e.world i).state a) →
    ((e.world i).state a).getHead config = .ok hd →
    ((e.world i).state a).isAncestor hd ⟨root, .pending⟩ = .ok true

/-- Each up-to-date honest head in the interval reads its justified state and its windows.

A window starts at the given slot and ends before the store's current slot. -/
def HonestHeadReads (firstSlot : Slot) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (head : ForkChoiceNode), first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    (∃ state, ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint =
      .ok state) ∧
    ∀ current high, ((e.world k).state w).getCurrentSlot config = .ok current →
      high < current → ∃ participants,
        ((e.world k).state w).getCommitteesBetweenSlots head.root firstSlot high = .ok participants

/-- Each up-to-date honest store has the root in its filtered tree or below its justified block.

The filtered tree grows from the justified block, so either way the root does not conflict with it.

So this assumes that no honest justified checkpoint conflicts with the root over the interval.

That is the checkpoint-consistency half of the safety of the confirmation, assumed, not derived. -/
def RootViable (root : Root) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (nodes : List ForkChoiceNode), first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes

/-- Each up-to-date honest store with an early justified checkpoint has it comparable with the root.

An early checkpoint has an epoch at most the given one.

The justified block descends from the root, or the root descends from the justified block.

This is the checkpoint-consistency half of the root's viability, for early checkpoints only.

While no later checkpoint is justified, every honest store's checkpoint is early.

So over such a stretch this still assumes the whole consistency.

Realized justification at the call's head would discharge it more directly, by a rule change. -/
def EarlyJustifiedConsistent (root : Root) (epoch : Epoch) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).justifiedCheckpoint.epoch ≤ epoch →
    ((e.world k).state w).isAncestor
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true ∨
      ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true

/-- Each up-to-date honest store keeps a root that strictly descends from its justified block.

The root stays in the store's filtered tree.

The filtered tree keeps such a block when a viable leaf descends from it.

So this says that the root keeps a viable leaf, the other half of the root's viability.

Voting sources refreshed after empty epochs would make it more direct, by a rule change. -/
def RootKeepsViableLeaf (root : Root) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (nodes : List ForkChoiceNode), first ≤ (e.world k).time →
    (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getFilteredNodeTree config = .ok nodes →
    ((e.world k).state w).isAncestor ⟨root, .pending⟩
        ⟨((e.world k).state w).justifiedCheckpoint.root, .pending⟩ = .ok true →
    root ≠ ((e.world k).state w).justifiedCheckpoint.root →
    (⟨root, .pending⟩ : ForkChoiceNode) ∈ nodes

/-- Each up-to-date honest store whose justified checkpoint is after an epoch has an honest signer.

An honest validator signed a vote with that checkpoint as its target.

The vote is of a slot before the store's current slot, in a message sent by the store's time.

Byzantine stake below two thirds in each state that counts the votes gives such a signer.

It follows from that bound and the stake floors.

It also needs a positive inclusion delay and two conditions on the anchor. -/
def JustifiedHonestlySigned (epoch : Epoch) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (slot : Slot), first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getCurrentSlot config = .ok slot →
    epoch < ((e.world k).state w).justifiedCheckpoint.epoch →
    ∃ v ∈ J, ∃ i, (e.world i).time ≤ (e.world k).time ∧ ∃ m ∈ (e.world i).sent, ∃ data,
      (v, data) ∈ statements config checks anchorState anchorBlock m ∧
      data.target = ((e.world k).state w).justifiedCheckpoint ∧ data.slot < slot

/-- Byzantine stake is below two thirds of the total in each state that counts later votes.

The total is the active balance of the state's epoch, at least one increment.

The states are those where an up-to-date honest store over the interval counts votes.

Their epoch is after the given one.

The Byzantine stake is that of the quorum voters outside the honest set.

The quorum voters are the unslashed validators active in the state's epoch or the one before. -/
def ByzantineCountedStake (epoch : Epoch) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (state : BeaconState preset fork) (total : Gwei),
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    CountedState ((e.world k).state w) config state → epoch < getCurrentEpoch state →
    getTotalActiveBalance state = .ok total →
    3 * stake (fun v => balanceAt state v.toNat) {v ∈ quorumVoters state | v ∉ J} <
      2 * total.toNat

/-- Each near honest head of the interval omits at most the exit reserve per full window epoch.

A receiver is near when its store epoch is at most two epochs after `parentEpoch`.

The window starts at the given slot and ends at the slot before the store's current slot.

Later receivers are covered by the duty-epoch step, which does not read it. -/
def ReceiverWindowExitsNear (parentEpoch : Epoch) (source : BeaconState preset fork)
    (firstSlot : Slot) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (head : ForkChoiceNode) (current finish : Slot) (receiverEpoch : Epoch),
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getHead config = .ok head →
    ((e.world k).state w).getCurrentSlot config = .ok current → subChecked current 1 = .ok finish →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok receiverEpoch →
    receiverEpoch.toNat ≤ parentEpoch.toNat + 2 →
    WindowExitBound (config := config) ((e.world k).state w) source head.root firstSlot finish

omit [DecidablePred (· ∈ J)] in
open Classical in
/-- The honest duties of one complete epoch outweigh the rest of the stake and the boost.

The epoch starts at the first time or later and ends by the given time.

The stakes are the balances of the state's unslashed active validators. -/
def LateMargin (preset : Preset) (config : Config) (genesisTimeMs : UInt64)
    (assignment : Assignment preset) (J : Set ValidatorIndex) [DecidablePred (· ∈ J)]
    (first time : ℕ) (state : BeaconState preset fork) (boost : ℕ) : Prop :=
  ∃ (epoch : Epoch) (begin next : Slot) (beginTime endTime : UInt64),
    computeStartSlotAtEpoch preset epoch = .ok begin ∧
    addChecked begin preset.SLOTS_PER_EPOCH = .ok next ∧
    computeTimeAtSlotMs config genesisTimeMs begin = .ok beginTime ∧
    computeTimeAtSlotMs config genesisTimeMs next = .ok endTime ∧
    first ≤ beginTime.toNat ∧ endTime.toNat ≤ time ∧
    stake (fun v => balanceAt state v.toNat)
        ((unslashedActiveBalances state).map (·.1)).toFinset + boost <
      2 * stake (fun v => balanceAt state v.toNat)
        {v ∈ ((unslashedActiveBalances state).map (·.1)).toFinset | v ∈ J ∧
          ∃ slot committeeIndex, begin ≤ slot ∧ slot < next ∧
            assignment.committee v slot = some committeeIndex}

/-- Honest stores more than two epochs past the parent's epoch have the late majority.

The majority reads the stakes of the store's justified state and its boost. -/
def LateDutyMajority (parentEpoch : Epoch) (first last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k (epoch : Epoch) (state : BeaconState preset fork),
    first ≤ (e.world k).time → (e.world k).time ≤ last →
    UpToDate config checks sources (e.world k).time ((e.world k).view w) ((e.world k).state w) →
    ((e.world k).state w).getCurrentStoreEpoch config = .ok epoch →
    parentEpoch.toNat + 2 < epoch.toNat →
    ((e.world k).state w).checkpointState ((e.world k).state w).justifiedCheckpoint = .ok state →
    LateMargin preset config genesisTimeMs assignment J first (e.world k).time state
      (((e.world k).state w).boostScore config)

/-- The receiver can relate the root to each earlier finalized checkpoint in its current store. -/
def ReceiverFinalityCovers (w : ValidatorIndex) (k : Nat) (root : Root)
    (block : BeaconBlock preset fork) : Prop :=
  ∀ k' ≤ k,
    UpToDate config checks sources (e.world k').time ((e.world k').view w)
      ((e.world k').state w) →
    (∃ boundary,
      computeStartSlotAtEpoch preset ((e.world k').state w).finalizedCheckpoint.epoch =
        .ok boundary ∧ boundary ≤ block.slot ∧
      ((e.world k).state w).getCheckpointBlock root
        ((e.world k').state w).finalizedCheckpoint.epoch =
          .ok ((e.world k').state w).finalizedCheckpoint.root) ∨
    ((e.world k).state w).isAncestor
      ⟨((e.world k').state w).finalizedCheckpoint.root, .pending⟩ ⟨root, .pending⟩ = .ok true

/-- Every held honest state remains before the next configured fork through the horizon. -/
def HeldStatesBeforeUpgrade (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last → ∀ next ∈ config.nextFork fork,
    ∀ (root : Root) (state : BeaconState preset fork),
    ((e.world k).state w).blockStates[root]? = some state →
    state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat

/-- Every run to a held state meets direct safety's stake floor at the selected epoch horizon. -/
def HeldRunStakeFloor {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩) (horizon : Epoch) (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last → ∀ (root : Root) (state : BeaconState preset fork),
    ((e.world k).state w).blockStates[root]? = some state →
    ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
    DirectSafety.EnoughStake (pre.append tail) horizon.toNat

/-- Eligible held terminal states have more than three halves of one balance increment in stake. -/
def HeldTerminalStakeFloor (horizon : Epoch) (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last → ∀ (root : Root) (state : BeaconState preset fork),
    ((e.world k).state w).blockStates[root]? = some state →
    (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
    GENESIS_EPOCH + 1 < getCurrentEpoch state →
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)

/-- An honest store has two runs from the anchor to held states that give direct-safety evidence.

A terminal view of the first state has the store's earlier finalized checkpoint.

A terminal view of the second state has the store's later justified checkpoint.

The evidence is the direct-safety stake inequality, or hash evidence on the two runs.

It is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, the stake inequality holds with no accountable key. -/
def HistoricalDirectSafetyEvidence {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩) (time : Nat) : Prop :=
  ∃ w ∈ J, ∃ i k, i ≤ k ∧ (e.world k).time ≤ time ∧
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ r : Root, ((e.world i).state w).blockStates[r]? = some stateA) ∧
      (∃ r : Root, ((e.world k).state w).blockStates[r]? = some stateB) ∧
      va.state.finalizedCheckpoint = ((e.world i).state w).finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = ((e.world k).state w).justifiedCheckpoint ∧
      (stake (DirectSafety.effectiveWeight anchorState) (DirectSafety.unslashedKeys anchorState) ≤
        3 * stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.accountableKeys pre left right) +
        2 * max (DirectSafety.derivedDrift
          ((e.world k).state w).justifiedCheckpoint.epoch.toNat left)
          (DirectSafety.derivedDrift ((e.world k).state w).justifiedCheckpoint.epoch.toNat right) ∨
        DirectSafety.HashEvidence ((pre.append left).hashObjects ++ (pre.append right).hashObjects))

end EthLib.Consensus.Models.Network

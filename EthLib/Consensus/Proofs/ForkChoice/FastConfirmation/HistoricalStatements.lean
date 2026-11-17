module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.DutySupport
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Sets

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
def Counts (store : Store preset fork) (config : Config)
    (state : BeaconState preset fork) : Prop :=
  ∃ (root : Root) (base : BeaconState preset fork), store.blockStates[root]? = some base ∧
    (state = base ∨ ∃ (checks : SignatureChecks) (slot : Slot) (childRoot : Root)
      (child : BeaconBlock preset fork), store.blocks[childRoot]? = some child ∧
      child.parentRoot = root ∧ slot ≤ child.slot ∧
      processSlots config checks base slot = .ok state)

/-- The validators active at the state's current epoch. -/
def activeVoters (state : BeaconState preset fork) : Finset ValidatorIndex :=
  (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset

/-- Stake reserved for scheduled exits and the fork's exit and consolidation churn. -/
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

/-- Each later successful window read also succeeds with the source state's weights and boost. -/
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

variable [DecidablePred (· ∈ J)]

/-- At the call time, each nonempty window covers Byzantine stake plus the weighted exit reserve. -/
def SourceWindowReserve (call : Nat) (source : BeaconState preset fork) : Prop :=
  ∀ w ∈ J, ∀ k head first finish participants,
    (e.world k).time = (e.world call).time → first ≤ finish →
    ((e.world k).state w).getCommitteesBetweenSlots head first finish = .ok participants →
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

/-- Selected checkpoints cover earlier finality outside the same-validator justified case. -/
def ResidualFinalizedCheckpointCompatibility (horizon : Epoch) (last : Nat) : Prop :=
  ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
    ∀ checkpoint : Checkpoint, SelectedCheckpoint ((e.world j).state b) checkpoint →
    ¬ (a = b ∧ i ≤ j ∧ checkpoint = ((e.world j).state b).justifiedCheckpoint) →
    ((e.world i).state a).finalizedCheckpoint.epoch ≤ checkpoint.epoch →
    checkpoint.epoch ≤ horizon →
    ((e.world j).state b).getCheckpointBlock checkpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
        .ok ((e.world i).state a).finalizedCheckpoint.root

/-- All honest stores hold only blocks with nonzero state roots through the horizon. -/
def HeldBlockStateRootsNonzero (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k, (e.world k).time ≤ last → HeldStateRootsNonzero ((e.world k).state w)

/-- No honest validator has a true slashed flag in a counted state through the horizon. -/
def HonestCountedStatesUnslashed (last : Nat) : Prop :=
  ∀ w ∈ J, ∀ k state, (e.world k).time ≤ last →
    Counts ((e.world k).state w) config state →
    ∀ v ∈ J, (slashedFlagAt state v.toNat).getD false = false

/-- Every up-to-date honest head descends from the root throughout the half-open time interval. -/
def HonestHeadsCover (root : Root) (first last : Nat) : Prop :=
  ∀ earlier, first ≤ earlier → earlier < last → ∀ a ∈ J, ∀ i hd,
    (e.world i).time = earlier →
    UpToDate config checks sources (e.world i).time ((e.world i).view a) ((e.world i).state a) →
    ((e.world i).state a).getHead config = .ok hd →
    ((e.world i).state a).isAncestor hd ⟨root, .pending⟩ = .ok true

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

/-- Two historical terminal views expose accountable stake loss or direct-safety hash evidence. -/
def HistoricalFinalityEvidence {g : ForkedBeaconState preset}
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

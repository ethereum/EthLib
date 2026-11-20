module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.CheckpointConsistency
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.ForkChoice.JustifiedVotes
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalSigners
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDrift
import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.Transition.FfgJustification

/-!
# The voters of a call pin the justification

The pin of a fast-confirmation call bounds the drift of its quorum.

This file turns that bound into the reader `justifiedPinned_of_setting`.

The reader proves `JustifiedPinned`.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models DirectSafety PinDrift

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
section PinReader

open Serialization.Ssz

variable {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- The finalized checkpoint of the call's target state is on the justified chain of another store.

The caller's store holds the target block's state, and its head leads to that block.

The head reads the store's finalized block, since it is a viable leaf, or the justified block.

So the target block reads that finalized block, and it reads the target state's finalized block.

The other store's justified chain reads the caller's finalized block, as the finality fact gives.

The two stores agree on their blocks, so the earlier read passes to the other store. -/
private theorem pin_finRead {A B : Store preset fork}
    (reachedA : Store.Reachable config anchorState anchorBlock A)
    (reachedB : Store.Reachable config anchorState anchorBlock B)
    (sound : Invariant anchorState)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (params : DirectSafety.Parameters preset) (nonzero : HeldStateRootsNonzero A)
    (unknownParent : A.blocks[anchorBlock.parentRoot]? = none)
    (same : ∀ (r : Root) (b c : BeaconBlock preset fork),
      A.blocks[r]? = some b → B.blocks[r]? = some c → b = c)
    (chain : A.getCheckpointBlock A.justifiedCheckpoint.root A.finalizedCheckpoint.epoch =
      .ok A.finalizedCheckpoint.root)
    (finality : A.finalizedCheckpoint.epoch ≤ B.justifiedCheckpoint.epoch →
      B.getCheckpointBlock B.justifiedCheckpoint.root A.finalizedCheckpoint.epoch =
        .ok A.finalizedCheckpoint.root)
    {head : ForkChoiceNode} (headOk : A.getHead config = .ok head)
    {epoch : Epoch} {target : Checkpoint}
    (epochOk : A.getCurrentStoreEpoch config = .ok epoch)
    (targetOk : A.getCurrentTarget config head.root = .ok target)
    {anc : BeaconState preset fork} (ancOk : A.blockStates[target.root]? = some anc)
    (later : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch)
    (finalizedLe : A.finalizedCheckpoint.epoch ≤ epoch)
    (justifiedLe : A.finalizedCheckpoint.epoch ≤ B.justifiedCheckpoint.epoch) :
    B.getCheckpointBlock B.justifiedCheckpoint.root anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
  obtain ⟨epoch', block, epochOk', targetRead, rfl⟩ := Store.getCurrentTarget_eq_ok_iff.mp targetOk
  obtain rfl : epoch' = epoch := Except.ok.inj (epochOk'.symm.trans epochOk)
  have ancLe : anc.finalizedCheckpoint.epoch ≤ A.finalizedCheckpoint.epoch :=
    ((reachedA.ordered_finalized sound).2) ancOk
  -- The head reads the finalized block, as a viable leaf or as the justified block.
  have headRead : A.getCheckpointBlock head.root A.finalizedCheckpoint.epoch =
      .ok A.finalizedCheckpoint.root := by
    rcases Store.getHead_viable headOk with viable | ⟨-, same⟩
    · exact reachedA.isViableLeaf_finalized (UInt64.le_of_eq anchorSlot) unknownParent viable
    · rw [congrArg ForkChoiceNode.root same]
      exact chain
  -- The target block reads it too, and so it reads the finalized block of the target state.
  have targetFinalized : A.getCheckpointBlock block A.finalizedCheckpoint.epoch =
      .ok A.finalizedCheckpoint.root :=
    (Store.getCheckpointBlock_trans targetRead finalizedLe) ▸ headRead
  -- The block of the target state reads the finalized block of that state.
  obtain ⟨-, -, -, ancReads⟩ :=
    Store.Reachable.finalizedState_of_blockState reachedA sound anchorSlot params nonzero ancOk
  have ancRead := ancReads later
  have middle : A.getCheckpointBlock A.finalizedCheckpoint.root anc.finalizedCheckpoint.epoch =
      .ok anc.finalizedCheckpoint.root := by
    rw [← Store.getCheckpointBlock_trans targetFinalized ancLe]
    exact ancRead
  -- The other store's justified chain reads the caller's finalized block, which it holds.
  have justifiedRead := finality justifiedLe
  obtain ⟨-, finalizedBlock, -, finalizedHeld, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock justifiedRead
  obtain ⟨boundary, checkpointBlock, boundaryOk, checkpointHeld, checkpointLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock ancRead
  have aboveAnchor : anchorBlock.slot ≤ boundary :=
    UInt64.le_trans (reachedA.anchorSlot_le (UInt64.le_of_eq anchorSlot) checkpointHeld)
      checkpointLe
  have received := Store.getCheckpointBlock_of_same_blocks reachedB same boundaryOk aboveAnchor
    ⟨finalizedBlock, finalizedHeld⟩ middle
  rw [Store.getCheckpointBlock_trans justifiedRead ancLe]
  exact received

/-- The a priori guard at a call's finalized state, and a finality lag within the withdrawal delay.

They are the two conditions that the pin's `Setting` assumes of the call's finalized state.

The call's pulled-up state, target state and finalized state are those of an honest store.

The guard is `aprioriGuardAt` at the finalized state, for the call's epoch.

The lag is the call's epoch, plus two, less the finalized state's epoch. -/
def PinGuarded (last : ℕ) : Prop :=
  ∀ u ∈ J, ∀ n (head : Root) (pulled anc fin : BeaconState preset fork) (target : Checkpoint),
    (e.world n).time ≤ last →
    ((e.world n).state u).getPulledUpHeadState config head = .ok pulled →
    ((e.world n).state u).getCurrentTarget config head = .ok target →
    ((e.world n).state u).blockStates[target.root]? = some anc →
    (getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin) →
    (anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState) →
    DirectSafety.Apriori.aprioriGuardAt config ⟨fork, fin⟩ (getCurrentEpoch pulled).toNat ∧
    (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
      config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat

/-- The voters of a call pin the justified checkpoints of the call's epoch.

Take honest voters whose stake exceeds a third of the total plus the margin and the pin reserve.

A justified checkpoint of the call's epoch then has a signer among them, or two stores collide.

The pin bounds the drift of the quorum.

So the quorum voters outside the set hold less than two thirds of the total.

Honest stores agree on their blocks unless two of them collide.

A store's justified chain reads its own finalized block, by `finality`. -/
theorem justifiedPinned_of_setting [DecidablePred (· ∈ J)] {anchor : Store preset fork}
    {g : ForkedBeaconState preset} {horizon anchorEpoch : Epoch} {margin first last : ℕ}
    (bls : checks = .bls)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (slots : 0 < config.SLOT_DURATION_MS) (parameters : DirectSafety.Parameters preset)
    (delay : preset.InclusionDelayPositive)
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    (unslashed : HonestCountedStatesUnslashed (e := e) last)
    (finality : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    (guarded : PinGuarded (e := e) last)
    (preGloas : fork < .glamsterdam) (fusaka : .fusaka ≤ fork)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bands : preset.IncrementWithinUpwardBand) (caps : CapOrder preset)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (long : 1 < preset.SLOTS_PER_EPOCH)
    (facts : PinPresetFacts preset) :
    JustifiedPinned (e := e) anchorEpoch margin first last := by
  subst bls
  obtain ⟨sound, -, -⟩ := DirectSafety.run_justified_separated pre genesis
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat := by
    have := UInt64.lt_iff_toNat_lt.mp long
    simp only [UInt64.toNat_one] at this
    omega
  have heldEarly := Execution.heldStatesBeforeUpgrade_of_bounded (e := e) anchored start
    anchorSlot slots positive forkWindow bounded
  intro u caller n head pulled total epoch voters callTime headRead pulledOk totalOk epochOk
    target anc fin targetOk ancOk finHeld finAnchor votersOk quorum w receiver k slot _ high
    _ slotOk justifiedEpoch afterAnchorEpoch
  obtain agree | collision := Execution.blocksAgree_or_collision (e := e) last
  swap
  · exact .inr collision
  left
  obtain ⟨node, nodeOk, rfl⟩ := headRead
  obtain ⟨anchorRoot, -, -, -, anchorJustified, -⟩ := getForkchoiceStore_anchor anchored
  have anchorEpochEq : getCurrentEpoch anchorState = anchorEpoch := by
    rw [← anchorEpochOk, anchorJustified]
  have later : getCurrentEpoch anchorState <
      ((e.world k).state w).justifiedCheckpoint.epoch := by
    rw [anchorEpochEq, justifiedEpoch]
    exact afterAnchorEpoch
  have reachedA := e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) n u caller
  have reachedB := e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) k w receiver
  have nonzeroA := roots u caller n callTime
  have targetEpoch : target.epoch = epoch := Store.epoch_eq_of_getCurrentTarget epochOk targetOk
  -- The caller's finalized epoch is at most its store's epoch, which is the receiver's justified.
  have finalizedLe : ((e.world n).state u).finalizedCheckpoint.epoch ≤ epoch :=
    UInt64.le_trans (reachedA.reachable.finalized_le_justified sound)
      (reachedA.forwardReachable.justified_epoch_le_current sound slots
        (UInt64.le_of_eq anchorSlot) epochOk).1
  have justifiedLe : ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := justifiedEpoch ▸ finalizedLe
  have ancLe : anc.finalizedCheckpoint.epoch ≤ ((e.world n).state u).finalizedCheckpoint.epoch :=
    ((reachedA.reachable.ordered_finalized sound).2) ancOk
  obtain ⟨-, -, -, ancReads⟩ :=
    Store.Reachable.finalizedState_of_blockState reachedA.reachable sound anchorSlot parameters
      nonzeroA ancOk
  have signed := Execution.justifiedSigned_at (epoch := getCurrentEpoch anchorState) anchored
    start anchorSlot anchorHeader anchorZero slots parameters delay genesis pre roots absent
    heldEarly bounded enough terminal (UInt64.le_refl _) receiver high slotOk later
    (· ∈ voters)
    fun root base state totalC held shape rootRead _ justifiedLe' near inside totalOkC => by
    -- The receiver's chain at the counting root passes the finalized block of the target state.
    have finReadRoot : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
        ((e.world k).state w).getCheckpointBlock root anc.finalizedCheckpoint.epoch =
          .ok anc.finalizedCheckpoint.root := by
      intro laterAnc
      have justifiedRead := pin_finRead reachedA.reachable reachedB.reachable sound
        anchorSlot parameters nonzeroA (absent u caller n callTime)
        (agree u caller w receiver n k callTime high)
        (finality u caller u caller n n callTime callTime
          (reachedA.reachable.finalized_le_justified sound))
        (finality u caller w receiver n k callTime high) nodeOk epochOk targetOk ancOk laterAnc
        finalizedLe justifiedLe
      rw [Store.getCheckpointBlock_trans rootRead (UInt64.le_trans ancLe justifiedLe)]
      exact justifiedRead
    have counts : CountedState ((e.world k).state w) config state :=
      ⟨root, base, held, shape.imp id fun ⟨slot', childRoot, child, found, parent, le, ok⟩ =>
        ⟨.bls, slot', childRoot, child, found, parent, le, ok⟩⟩
    obtain ⟨pulledEpoch, split, ⟨toFin⟩, ⟨fromFin⟩, ⟨toPulled⟩, ⟨toCounted⟩, finalizedS,
        laterS⟩ :=
      setting_runs_of_call anchored start anchorSlot slots positive genesis pre preGloas fusaka
        forkWindow bounded bands caps facts.activation caller callTime pulledOk targetOk
        ancOk finHeld finAnchor ancReads receiver high (agree u caller w receiver n k callTime high)
        held
        (shape.imp id fun ⟨slot', _, _, _, _, _, ok⟩ => ⟨slot', ok⟩) finReadRoot
        (by rw [targetEpoch, ← justifiedEpoch]; exact justifiedLe')
        (UInt64.le_iff_toNat_le.mpr inside)
    have nearPulled : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
      rw [pulledEpoch, targetEpoch]
      rw [justifiedEpoch] at near
      exact near
    have guard := guarded u caller n node.root pulled anc fin target callTime pulledOk targetOk
      ancOk finHeld finAnchor
    have setting : Setting config .bls g split fin pulled anc state voters :=
      ⟨genesis, ⟨toFin⟩, ⟨fromFin⟩, ⟨toPulled⟩, ⟨toCounted⟩, preGloas, fusaka, bands, caps,
        exitWindow, parameters, maxAligned, twoSlots, guard.2, ⟨total, totalOk⟩,
        facts, guard.1, finalizedS, laterS, nearPulled,
        fun v member => ⟨(votersOk v member).2,
          unslashed w receiver k state high counts v (votersOk v member).1⟩⟩
    have pin := PinDrift.le_pinReserve setting totalOkC totalOk
    have splitStake := Finset.sum_filter_add_sum_filter_not (quorumVoters state) (· ∈ voters)
      (fun v => balanceAt state v.toNat)
    unfold Models.stake at pin quorum ⊢
    beta_reduce at pin quorum ⊢
    omega
  obtain ⟨v, voter, i, before, m, sent, data, member, target', slotLt⟩ := signed
  exact ⟨v, voter, i, before, m, sent, data, member, target', slotLt⟩

section Deployed

variable [DecidablePred (· ∈ J)] {anchor : Store preset fork} {g : ForkedBeaconState preset}
  {horizon anchorEpoch : Epoch} {margin first last : ℕ}
  (bls : checks = .bls)
  (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
  (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
  (anchorEpochOk : anchor.justifiedCheckpoint.epoch = anchorEpoch)
  (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
    anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
    anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
    SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
  (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
  (slots : 0 < config.SLOT_DURATION_MS)
  (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
  (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
  (bounded : HonestStoreEpochsBounded (e := e) horizon last)
  (enough : HeldRunStakeFloor (e := e) pre horizon last)
  (terminal : HeldTerminalStakeFloor (e := e) horizon last)
  (unslashed : HonestCountedStatesUnslashed (e := e) last)
  (finality : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
    ((e.world i).state a).finalizedCheckpoint.epoch ≤
      ((e.world j).state b).justifiedCheckpoint.epoch →
    ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
        .ok ((e.world i).state a).finalizedCheckpoint.root)
  (guarded : PinGuarded (e := e) last)
  (preGloas : fork < .glamsterdam) (fusaka : .fusaka ≤ fork)
  (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)

include bls anchored start anchorSlot anchorEpochOk anchorHeader anchorZero slots genesis pre roots
  absent bounded enough terminal unslashed finality guarded preGloas fusaka forkWindow

/-- On the mainnet preset, the voters of a call pin the justified checkpoints of its epoch. -/
theorem justifiedPinned_of_setting.mainnet (mainnet : preset = Preset.mainnet) :
    JustifiedPinned (e := e) anchorEpoch margin first last := by
  subst mainnet
  exact justifiedPinned_of_setting bls anchored start anchorSlot anchorEpochOk anchorHeader
    anchorZero slots ⟨by decide, by decide, by decide⟩ Preset.inclusionDelayPositive_mainnet
    genesis pre roots absent bounded enough terminal unslashed finality guarded preGloas fusaka
    forkWindow Preset.incrementWithinUpwardBand_mainnet CapOrder.mainnet
    Preset.seedLookaheadAtLeastThree_mainnet maxEffectiveBalancesAligned_mainnet (by decide) PinPresetFacts.mainnet

/-- On the minimal preset, the voters of a call pin the justified checkpoints of its epoch. -/
theorem justifiedPinned_of_setting.minimal (minimal : preset = Preset.minimal) :
    JustifiedPinned (e := e) anchorEpoch margin first last := by
  subst minimal
  exact justifiedPinned_of_setting bls anchored start anchorSlot anchorEpochOk anchorHeader
    anchorZero slots ⟨by decide, by decide, by decide⟩ Preset.inclusionDelayPositive_minimal
    genesis pre roots absent bounded enough terminal unslashed finality guarded preGloas fusaka
    forkWindow Preset.incrementWithinUpwardBand_minimal CapOrder.minimal
    Preset.seedLookaheadAtLeastThree_minimal maxEffectiveBalancesAligned_minimal (by decide) PinPresetFacts.minimal

end Deployed

end PinReader

end EthLib.Consensus.Models.Network

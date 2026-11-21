module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.SourceWindowMargin

/-!
# The exits that a near receiver's window can see

A fast confirmation reads its stake from a checkpoint state, the source.

A receiver near the call reads the committees of an epoch at most three epochs after the source.

The stake that leaves the active set by then must fit the near exit reserve of the source.

Every exit is placed at `current + 1 + MAX_SEED_LOOKAHEAD` or later, from the epoch where it starts.

So each state fixes activity up to `current + MAX_SEED_LOOKAHEAD`.

With a lookahead of at least three epochs, every such exit was already scheduled at the source.

A condition on the preset names that lookahead.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- Active stake of the source state already scheduled to exit within three epochs.

It counts the active validators whose exit epoch is at most three epochs after the current one.

Every exit placed at the source or later lands at least `MAX_SEED_LOOKAHEAD + 1` epochs after it.

So when `MAX_SEED_LOOKAHEAD` is at least 3, no other validator leaves by those three epochs. -/
def exitReserveNear (source : BeaconState preset fork) : ℕ :=
  stake (fun v => balanceAt source v.toNat)
    {v ∈ activeVoters source | (source.validators.data[v.toNat]?).any fun validator =>
      validator.exitEpoch.toNat ≤ (getCurrentEpoch source).toNat + 3}

/-- Stake active at the source and inactive at a near epoch of a later state fits the reserve.

The later state keeps the source's activity up to its fixed epoch, as every run does.

The epoch is from the source's epoch to three epochs after it.

A validator active at the source and inactive at that epoch was inactive there in the source too.

So its exit epoch in the source is at most that epoch, which the near exit reserve counts. -/
private theorem exitStake_le_exitReserveNear {post : Fork}
    {source : BeaconState preset fork} {later : BeaconState preset post}
    (preGloas : fork < .glamsterdam) (fixedWindow : preset.SeedLookaheadAtLeastThree)
    (kept : ActiveKept (activityFixedEpoch source) source later)
    {epoch : Epoch} (low : getCurrentEpoch source ≤ epoch)
    (high : epoch.toNat ≤ (getCurrentEpoch source).toNat + 3) :
    stake (fun v => balanceAt source v.toNat)
        {v ∈ activeVoters source | isActiveAt later epoch v.toNat = false} ≤
      exitReserveNear source := by
  apply stake_mono
  intro v member
  rw [Finset.mem_filter] at member ⊢
  obtain ⟨active, absent⟩ := member
  refine ⟨active, ?_⟩
  -- The epoch is within the source's fixed epoch, so the later state reads the source's activity.
  have fixed : epoch ≤ activityFixedEpoch source := by
    rw [UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    have := epoch.toNat_lt
    have : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := fixedWindow
    omega
  rw [kept epoch fixed] at absent
  unfold activeVoters at active
  rw [List.mem_toFinset, mem_getActiveValidatorIndices (source.validators.bound preGloas)] at active
  obtain ⟨validator, found, current⟩ := active
  simp only [isActiveAt, found, Option.map_some, Option.getD_some] at absent
  simp only [found, Option.any_some, decide_eq_true_eq]
  -- Active at the source's epoch and not at the later one: activation is early, so exit is due.
  simp only [isActiveValidator, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at current absent
  rw [UInt64.le_iff_toNat_le] at low
  omega

/-- A head state that keeps the source's fixed activity omits at most the near reserve per epoch.

Each full epoch of the window must lie between the source's epoch and three epochs after it.

The committees of a full epoch hold every validator active in it at the head state.

So each omitted source validator is inactive there, and the near reserve bounds their stake. -/
private theorem windowExitBoundWith_of_activeKept (store : Store preset fork)
    (source : BeaconState preset fork) (head : Root) (first last : Slot)
    {headState : BeaconState preset fork} (preGloas : fork < .glamsterdam)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (fixedWindow : preset.SeedLookaheadAtLeastThree)
    (headOk : store.blockState head = .ok headState)
    (kept : ActiveKept (activityFixedEpoch source) source headState)
    (near : ∀ (epoch : Epoch) (epochStart next epochEnd : Slot),
      computeStartSlotAtEpoch preset epoch = .ok epochStart →
      addChecked epochStart preset.SLOTS_PER_EPOCH = .ok next →
      subChecked next 1 = .ok epochEnd → first ≤ epochStart → epochEnd ≤ last →
      getCurrentEpoch source ≤ epoch ∧ epoch.toNat ≤ (getCurrentEpoch source).toNat + 3) :
    WindowExitBoundWith store source head first last (exitReserveNear source) := by
  intro epoch epochStart next epochEnd members startOk nextOk endOk firstLe lastLe membersOk
  obtain ⟨low, high⟩ := near epoch epochStart next epochEnd startOk nextOk endOk firstLe lastLe
  refine Nat.le_trans (stake_mono ?_)
    (exitStake_le_exitReserveNear preGloas fixedWindow kept low high)
  intro v member
  simp only [Finset.mem_filter] at member ⊢
  refine ⟨member.1, ?_⟩
  cases active : isActiveAt headState epoch v.toNat
  · rfl
  · -- The window's slots cover the whole epoch, so its committees hold the active validator.
    have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
    have nextNat := (addChecked_ok_iff.mp nextOk).2
    have endNat := (subChecked_ok_iff.mp endOk)
    simp only [UInt64.toNat_one] at endNat
    exact absurd (Store.mem_getCommitteesBetweenSlots_of_active (store := store) positive
      membersOk headOk (by omega) (by rw [Nat.succ_mul]; omega)
      (mem_getActiveValidatorIndices_of_isActiveAt active)) member.2

/-- The balance source of a call is a checkpoint on the parent's chain, recent for the parent.

The checkpoint block is the parent's ancestor at the start of the checkpoint's epoch.

The checkpoint's epoch is at most two epochs before the parent's, and not after it.

It is a fact about the call, which the near exit bound of its receivers reads. -/
def SourceOnParentChain (store : Store preset fork) (checkpoint : Checkpoint)
    (parentRoot : Root) (parent : BeaconBlock preset fork) : Prop :=
  checkpoint.epoch.toNat ≤ (computeEpochAtSlot preset parent.slot).toNat ∧
    (computeEpochAtSlot preset parent.slot).toNat ≤ checkpoint.epoch.toNat + 2 ∧
    store.getCheckpointBlock parentRoot checkpoint.epoch = .ok checkpoint.root

/-- A lookahead state from a state at or before a slot is at that slot. -/
private theorem lookaheadState_slot {config : Config} {checks : SignatureChecks}
    {base state : BeaconState preset fork} {start : Slot} (early : base.slot ≤ start)
    (computed : lookaheadState config checks base start = .ok state) : state.slot = start := by
  unfold lookaheadState at computed
  split at computed
  · exact (processSlots_slot (mapError_ok_iff.mp computed)).2
  · rename_i notBelow
    cases computed
    exact UInt64.le_antisymm early (UInt64.not_lt.mp notBelow)

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- The near exit bound of a call, from the call's source on the parent's chain.

Each full epoch of a near receiver's window omits some active source stake.

That omitted stake is at most the near exit reserve.

It needs a seed lookahead of at least three, and a checkpoint at most two epochs before the parent.

The alternative is a block collision between two honest stores by the horizon. -/
theorem Execution.receiverWindowExitsNear_of_sourceOnParentChain
    {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (fixedWindow : preset.SeedLookaheadAtLeastThree)
    (preGloas : fork < .glamsterdam) {time : ℕ} {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ}
    (callerTime : (e.world n).time ≤ time) {checkpoint : Checkpoint}
    {source : BeaconState preset fork} {block parent : BeaconBlock preset fork} {first : Slot}
    (sourceOk : ((e.world n).state u).checkpointState checkpoint = .ok source)
    (parentOk : ((e.world n).state u).block block.parentRoot = .ok parent)
    (firstOk : addChecked parent.slot 1 = .ok first)
    (onChain : SourceOnParentChain ((e.world n).state u) checkpoint block.parentRoot parent)
    (parentCovers : HonestHeadsCover (e := e) block.parentRoot (e.world n).time (time + 1)) :
    ReceiverWindowExitsNearWith (e := e) (computeEpochAtSlot preset parent.slot) source first
        (e.world n).time time (exitReserveNear source) ∨
      HonestCollision (e := e) time := by
  -- The honest stores by the horizon agree on their blocks, or two of them collide.
  rcases e.blocksAgree_or_collision time with agree | collision
  swap
  · exact .inr collision
  left
  intro w receiver k head current finish receiverEpoch lowK highK upToDate headOk currentOk
    finishOk epochOk nearParent
  have reached (a : ValidatorIndex) (honest : a ∈ J) (i : ℕ) :=
    e.reachable (fun a ha => (start a ha) ▸ Store.Reachable.anchor anchored) i a honest
  have forward := e.forwardReachableWith
    (fun a ha => (start a ha) ▸ Store.ForwardReachableWith.anchor anchored) k w receiver
  have same : ∀ (r : Root) left right, ((e.world n).state u).blocks[r]? = some left →
      ((e.world k).state w).blocks[r]? = some right → left = right :=
    agree u caller w receiver n k callerTime highK
  obtain ⟨parentLow, parentHigh, callerRead⟩ := onChain
  have callerParent := Store.block_ok_iff.mp parentOk
  -- The caller's checkpoint block, at or before the first slot of the checkpoint's epoch.
  obtain ⟨boundary, checkpointBlock, boundaryOk, checkpointFound, checkpointLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock callerRead
  have parentEpochNat : (computeEpochAtSlot preset parent.slot).toNat =
      parent.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  have boundaryLe : boundary ≤ parent.slot :=
    computeStartSlotAtEpoch_le_of_epoch_le boundaryOk parentLow
  -- The receiver's head descends from the parent, which the receiver holds as the caller does.
  have descends : ((e.world k).state w).isAncestor head ⟨block.parentRoot, .pending⟩ = .ok true :=
    parentCovers _ lowK (by omega) w receiver k head rfl upToDate headOk
  have receiverParent : ((e.world k).state w).blocks[block.parentRoot]? = some parent := by
    have read := descends
    simp only [Store.isAncestor, bind_ok_iff] at read
    obtain ⟨held, heldOk, -⟩ := read
    have heldFound := Store.block_ok_iff.mp heldOk
    rw [same _ parent held callerParent heldFound]
    exact heldFound
  obtain ⟨headBlock, headFound, parentLeHead⟩ := Store.slot_le_of_isAncestor receiverParent descends
  -- The receiver's head reads the same checkpoint block.
  have aboveAnchor : anchorBlock.slot ≤ boundary :=
    UInt64.le_trans ((reached u caller n).anchorSlot_le (UInt64.le_of_eq anchorSlot)
      checkpointFound) checkpointLe
  have receiverRead := Store.getCheckpointBlock_of_same_blocks (reached w receiver k) same
    boundaryOk aboveAnchor ⟨parent, receiverParent⟩ callerRead
  have headRead := Store.getCheckpointBlock_of_isAncestor receiverParent descends
    boundaryOk boundaryLe receiverRead
  -- The block states of the checkpoint block and of the head.
  obtain ⟨-, receiverCheckpoint, -, receiverCheckpointFound, -, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock headRead
  obtain ⟨base, baseFound, -, -⟩ :=
    (reached w receiver k).blockStatesFromParents receiverCheckpointFound
  obtain ⟨headState, headStateFound, -, -⟩ :=
    (reached w receiver k).blockStatesFromParents headFound
  -- In the receiver's store, the checkpoint block's state runs on to the head's state.
  obtain ⟨boundaryState, boundaryStateOk, run⟩ := forward.relation_of_checkpointPrefix RunKept
    RunKept.refl (fun one two => one.trans two) (fun ok => runKept_stateTransition ok)
    (fun slots bound ok => runKept_of_processSlots_of_stateTransition slots bound ok)
    (UInt64.le_of_eq anchorSlot) headRead headFound boundaryOk
    (UInt64.le_trans boundaryLe parentLeHead) baseFound headStateFound
  -- In the caller's store, the source is the same state processed with the same checks.
  obtain ⟨callerBase, slot, callerBaseFound, slotOk, sourceComputed⟩ :=
    e.checkpointStates_fixedChecks anchored start caller (Store.checkpointState_ok_iff.mp sourceOk)
  rw [boundaryOk, Except.ok.injEq] at slotOk
  subst slot
  have sameBase : callerBase = base :=
    e.blockStates_eq anchored (start u caller) (start w receiver) same
      callerBaseFound baseFound
  subst sameBase
  have sameSource : boundaryState = source :=
    Except.ok.inj (boundaryStateOk.symm.trans sourceComputed)
  subst sameSource
  -- The source is at the first slot of the checkpoint's epoch.
  have baseSlot := (reached u caller n).blockState_slot_eq anchorSlot checkpointFound
    callerBaseFound
  have sourceSlot := lookaheadState_slot (baseSlot ▸ checkpointLe) sourceComputed
  have sourceEpoch : getCurrentEpoch boundaryState = checkpoint.epoch := by
    rw [getCurrentEpoch, sourceSlot]
    exact computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive)
      boundaryOk
  refine windowExitBoundWith_of_activeKept _ boundaryState head.root first finish preGloas
    positive fixedWindow (Store.blockState_ok_iff.mpr headStateFound) run.active ?_
  -- A full epoch of the window is after the parent's epoch and before the receiver's.
  intro epoch epochStart next epochEnd startOk nextOk endOk firstLe lastLe
  have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
  have nextNat := (addChecked_ok_iff.mp nextOk).2
  have endNat := subChecked_ok_iff.mp endOk
  have firstNat := (addChecked_ok_iff.mp firstOk).2
  have finishNat := subChecked_ok_iff.mp finishOk
  simp only [UInt64.toNat_one] at endNat firstNat finishNat
  have firstLe' := UInt64.le_iff_toNat_le.mp firstLe
  have lastLe' := UInt64.le_iff_toNat_le.mp lastLe
  have receiverNat : receiverEpoch.toNat = current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    rw [Store.getCurrentStoreEpoch_eq currentOk epochOk]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  -- The epoch starts after the parent's slot, so it is after the parent's epoch.
  have afterParent : (computeEpochAtSlot preset parent.slot).toNat < epoch.toNat := by
    rw [parentEpochNat]
    apply (Nat.div_lt_iff_lt_mul positive).mpr
    omega
  -- The epoch ends before the receiver's slot, so it is before the receiver's epoch.
  have beforeReceiver : epoch.toNat + 1 ≤ receiverEpoch.toNat := by
    rw [receiverNat]
    apply (Nat.le_div_iff_mul_le positive).mpr
    rw [Nat.succ_mul]
    omega
  rw [sourceEpoch, UInt64.le_iff_toNat_le]
  omega

end EthLib.Consensus.Models.Network

module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalTransport

/-!
# Finalized-prefix family for historical-anchor transport

The finality companion supplies the finalized-prefix family or explicit evidence.

Source surplus reads the family only within one store.

It needs each receiver's own finalized checkpoint on the chain of its own justified checkpoint.
-/

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Honest justified epochs stay within the horizon that bounds the honest store epochs. -/
private theorem Execution.justified_epoch_le_horizon {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) {horizon : Epoch} {last : Nat}
    (bounded : HonestStoreEpochsBounded (e := e) horizon last) :
    ∀ w ∈ J, ∀ k, (e.world k).time ≤ last →
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon := by
  intro w member k time
  have forward := e.forwardReachableWith
    (fun a ha => (anchored a ha) ▸ Store.ForwardReachableWith.anchor anchorStore) k w member
  obtain ⟨current, currentOk, _, _⟩ := forward.forwardReachable.slots_le_current
    slots (UInt64.le_of_eq anchorSlot)
  have epochOk : ((e.world k).state w).getCurrentStoreEpoch config =
      .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  exact UInt64.le_trans
    (forward.forwardReachable.justified_epoch_le_current sound slots
      (UInt64.le_of_eq anchorSlot) epochOk).1
    (bounded w member k _ time epochOk)

/-- Each honest store's justified checkpoint reads back its earlier finalized checkpoints.

Otherwise two runs from the anchor give direct-safety evidence.

That evidence is relative to the anchor, and its drift counts from the anchor.

With enough churn since the anchor, it holds with no accountable key. -/
public theorem Execution.finalizedFamily_or_historical_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS)
    {horizon : Epoch} {last : Nat}
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    {u : ValidatorIndex} (honest : u ∈ J) {n : Nat} (inTime : (e.world n).time ≤ last) :
    (∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ last →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root) ∨
    HistoricalDirectSafetyEvidence (e := e) pre last := by
  exact e.finalized_prefix_or_accountable anchorStore anchored parameters genesis pre
    anchorSlot boundary (e.anchor_stateRoot_nonzero anchorStore anchored roots honest inTime) absent
    (e.justified_epoch_le_horizon anchorStore anchored sound anchorSlot slots bounded) early enough
    terminal

/-- Honest justified checkpoints agree at each epoch up to the horizon, or evidence holds. -/
public theorem Execution.selectedCheckpointsAgree_or_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    {horizon : Epoch} {last : Nat}
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last) :
    SelectedCheckpointsAgree (e := e) horizon last ∨
      -- Otherwise two honest stores hold different justified checkpoints of one epoch.
      --
      -- Runs from the anchor to held states of both have views that hold the two checkpoints.
      --
      -- That evidence is relative to the anchor, and its drift counts from the anchor.
      --
      -- With enough churn since the anchor, it holds with no accountable key.
      CrossStoreJustifiedEvidence (e := e) pre last := by
  classical
  by_cases agree : SelectedCheckpointsAgree (e := e) horizon last
  · exact .inl agree
  simp only [SelectedCheckpointsAgree, not_forall] at agree
  obtain ⟨a, honestA, b, honestB, i, j, timeA, timeB, first, second, selectedFirst,
    selectedSecond, epoch, inHorizon, different⟩ := agree
  have nonzero := e.anchor_stateRoot_nonzero anchorStore anchored roots honestA timeA
  rcases e.justified_eq_or_accountable anchorStore anchored parameters genesis pre
      anchorSlot nonzero absent early enough terminal honestA honestB timeA timeB selectedFirst
      selectedSecond epoch inHorizon with same | evidence
  · exact absurd same different
  · exact .inr ⟨a, honestA, b, honestB, i, j, timeA, timeB, first, second, selectedFirst,
      selectedSecond, epoch, different, evidence⟩

/-- A held state's justified checkpoint reads every honest finalized checkpoint up to its epoch. -/
public theorem Execution.heldFinality_or_evidence {anchor : Store preset fork}
    {horizon : Epoch} {last : Nat} {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS)
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last) :
    -- The held state is held by an honest store at an event by the time.
    --
    -- The finalized checkpoint is that of an honest store at an event by the time.
    --
    -- That store is the same one or another.
    (∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (st : BeaconState preset fork),
      ((e.world j).state b).blockStates[r]? = some st →
      -- The held state's realized justified checkpoint is after the anchor epoch.
      getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root) ∨
    -- Otherwise runs from the anchor to held states of the two stores give direct-safety evidence.
    --
    -- That evidence is relative to the anchor, and its drift counts from the anchor.
    --
    -- With enough churn since the anchor, it holds with no accountable key.
    HeldStateFinalityEvidence (e := e) pre last := by
  classical
  by_cases family : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last →
      (e.world j).time ≤ last →
      ∀ (r : Root) (st : BeaconState preset fork),
      ((e.world j).state b).blockStates[r]? = some st →
      getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root
  · exact .inl family
  push Not at family
  obtain ⟨a, honestA, b, honestB, i, j, timeA, timeB, r, st, held, after, ordered, failed⟩ :=
    family
  -- The held state's justified epoch is at most its previous epoch, so within the horizon.
  have inHorizon : st.currentJustifiedCheckpoint.epoch ≤ horizon := by
    have forward := e.forwardReachableWith
      (fun w hw => (anchored w hw) ▸ Store.ForwardReachableWith.anchor anchorStore) j b honestB
    obtain ⟨current, currentOk, _, _⟩ := forward.forwardReachable.slots_le_current
      slots (UInt64.le_of_eq anchorSlot)
    have epochOk : ((e.world j).state b).getCurrentStoreEpoch config =
        .ok (computeEpochAtSlot preset current) := by
      simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
    exact UInt64.le_trans
      (UInt64.le_trans ((forward.reachable.ordered sound).2 held).settled
        (getPreviousEpoch_le _))
      (UInt64.le_trans (forward.forwardReachable.blockState_epoch_le_current slots
        (UInt64.le_of_eq anchorSlot) epochOk r st held)
        (bounded b honestB j _ timeB epochOk))
  have result := e.held_finalized_read_or_accountable anchorStore anchored parameters genesis pre
    anchorSlot boundary (e.anchor_stateRoot_nonzero anchorStore anchored roots honestA timeA)
    absent early enough terminal honestA honestB timeA timeB held after ordered inHorizon
  exact .inr ⟨a, honestA, b, honestB, i, j, timeA, timeB, result.resolve_left failed⟩

/-- Each honest finalized checkpoint is on every honest justified chain at its epoch or later. -/
public theorem Execution.crossStoreFinality_or_evidence {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS)
    {horizon : Epoch} {last : Nat}
    (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last)
    (absent : AnchorParentAbsent (e := e) last)
    (parameters : DirectSafety.Parameters preset) {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (pre : Run config checks g ⟨fork, anchorState⟩)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last) :
    -- The two stores may be the same or different, at any events by the time.
    (∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root) ∨
    -- Otherwise two runs from the anchor give direct-safety evidence.
    --
    -- The runs end at held states of the two stores.
    --
    -- That evidence is relative to the anchor, and its drift counts from the anchor.
    --
    -- With enough churn since the anchor, it holds with no accountable key.
    CrossStoreDirectSafetyEvidence (e := e) pre last := by
  classical
  by_cases family : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last →
      (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root
  · exact .inl family
  push Not at family
  obtain ⟨a, honestA, b, honestB, i, j, timeA, timeB, ordered, failed⟩ := family
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have result := e.finalized_read_or_accountable anchorStore anchored parameters genesis pre
    anchorSlot boundary (e.anchor_stateRoot_nonzero anchorStore anchored roots honestA timeA)
    absent (e.justified_epoch_le_horizon anchorStore anchored sound anchorSlot slots bounded)
    early enough terminal honestA honestB timeA timeB ordered
  exact .inr ⟨a, honestA, b, honestB, i, j, timeA, timeB, result.resolve_left failed⟩

/-- A block an honest sender holds reaches each up-to-date honest receiver a delay later, by `last`.

The sender reads the receiver's finalized checkpoint at it; the receiver holds it and its state.

It assumes synchrony, delayed admission, block agreement and nonzero held roots.

It also needs the invariant anchor, a nonempty epoch and two epochs of root history. -/
public theorem Execution.carrier_delivered {Δ : ℕ} {anchor : Store preset fork} {last : ℕ}
    (sync : e.Synchronous Δ) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {m k : ℕ}
    (mBound : (e.world m).time ≤ last) (late : (e.world m).time + Δ ≤ (e.world k).time)
    (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {root : Root} {block : BeaconBlock preset fork} {state : BeaconState preset fork}
    (known : ((e.world m).state u).blocks[root]? = some block)
    (stored : ((e.world m).state u).blockStates[root]? = some state)
    (final : ((e.world m).state u).getCheckpointBlock root
      ((e.world k).state w).finalizedCheckpoint.epoch =
        .ok ((e.world k).state w).finalizedCheckpoint.root) :
    ((e.world k).state w).blocks[root]? = some block ∧
      ((e.world k).state w).blockStates[root]? = some state := by
  have reachedW := e.reachable (fun x hx => (start x hx).symm ▸ Store.Reachable.anchor anchored)
    k w receiver
  -- The receiver holds its finalized block, as the anchor state's root is not zero.
  have finalizedKnown := reachedW.finalized_known sound (UInt64.le_of_eq anchorSlot) positive
    window (e.anchor_stateRoot_nonzero anchored start nonzero receiver bounded)
  rcases e.blocks_of_partiallySynchronous_of_anchorSlot sync (fun _ => UInt64.le_of_eq anchorSlot)
      admitted anchored sender receiver (start u sender) (start w receiver)
      (by simpa using late) bounded upToDate finalizedKnown known final with
    ⟨held, -⟩ | ⟨a, ha, b, hb, i, j, hi, hj, _, ⟨r, left, right⟩, found⟩
  · -- The receiver's state for the block is the sender's.
    obtain ⟨post, postFound, -, -⟩ := reachedW.blockStatesFromParents held
    have same := e.blockStates_eq anchored (start u sender) (start w receiver)
      (agree u sender w receiver m k mBound bounded) stored postFound
    subst post
    exact ⟨held, postFound⟩
  · obtain ⟨leftFound, rightFound, different⟩ := Store.findBlockCollision_held found
    exact absurd (agree a ha b hb i j hi hj r left right leftFound rightFound) different

/-- A delay on, an honest receiver's justified epoch is at least an honest sender's finalized epoch.

The receiver is up to date at an event by `last`; honest stores agree on blocks, with nonzero roots.

By `last`, honest justified roots read honest finalized checkpoints at lower or equal epochs.

It assumes synchrony, delayed admission, an invariant anchor, nonempty epochs and root history. -/
public theorem Execution.finalized_epoch_le_justified_of_late {Δ : ℕ} {anchor : Store preset fork}
    {last : ℕ}
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (admitted : BlocksAdmitted e 0 Δ last)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (sound : Invariant anchorState) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (start : ∀ w ∈ J, e.start w = anchor) (nonzero : HeldBlockStateRootsNonzero (e := e) last)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    -- The finalized checkpoint of each receiver must be read at the justified root of each sender.
    (crossFinal : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ last → (e.world j).time ≤ last →
      ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch →
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
          .ok ((e.world i).state a).finalizedCheckpoint.root)
    {u w : ValidatorIndex} (sender : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    (late : (e.world n).time + Δ ≤ (e.world k).time) (bounded : (e.world k).time ≤ last)
    (upToDate : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w)) :
    ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).justifiedCheckpoint.epoch := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachable (fun x hx => (start x hx).symm ▸ Store.ForwardReachable.anchor anchored)
      i v honest
  have reachedU := (forward u sender n).reachable
  have reachedW := (forward w receiver k).reachable
  have nBound : (e.world n).time ≤ last := by omega
  have aligned : anchorBlock.slot ≤ anchorState.slot := UInt64.le_of_eq anchorSlot
  -- The receiver may have finalized the epoch already.
  by_cases covered : ((e.world n).state u).finalizedCheckpoint.epoch ≤
      ((e.world k).state w).finalizedCheckpoint.epoch
  · exact UInt64.le_trans covered (reachedW.finalized_le_justified sound)
  have below := UInt64.not_le.mp covered
  have finalLe := reachedU.finalized_le_justified sound
  have later : getCurrentEpoch anchorState < ((e.world n).state u).justifiedCheckpoint.epoch :=
    UInt64.lt_of_le_of_lt reachedW.anchor_le_finalized (UInt64.lt_of_lt_of_le below finalLe)
  have notZero := anchorState_hash_nonzero anchored start nonzero sender nBound
  -- The sender reads the receiver's finalized checkpoint at its justified root.
  have crossRead := crossFinal w receiver u sender k n bounded nBound
    (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))
  -- A held block that reads the sender's justified checkpoint reaches the receiver.
  have carry {root : Root} {state : BeaconState preset fork} {block : BeaconBlock preset fork}
      (known : ((e.world n).state u).blocks[root]? = some block)
      (stored : ((e.world n).state u).blockStates[root]? = some state)
      (read : ((e.world n).state u).getCheckpointBlock root
        ((e.world n).state u).justifiedCheckpoint.epoch =
          .ok ((e.world n).state u).justifiedCheckpoint.root) :
      ((e.world k).state w).blocks[root]? = some block ∧
        ((e.world k).state w).blockStates[root]? = some state := by
    refine Execution.carrier_delivered sync positive window admitted anchored sound anchorSlot start
      nonzero agree sender receiver nBound late bounded upToDate known stored ?_
    rw [Store.getCheckpointBlock_trans read
      (UInt64.le_of_lt (UInt64.lt_of_lt_of_le below finalLe))]
    exact crossRead
  obtain ⟨currentU, currentUOk⟩ := (forward u sender n).exists_getCurrentSlot slots
  -- The sender's justified checkpoint comes from the anchor, a held state, or its pull-up.
  --
  -- The block of that state reaches the receiver, whose justified epoch is then at least as late.
  rcases (forward u sender n).justified_origins_epoch positive slots currentUOk with
    ⟨root, _, same⟩ | ⟨root, state, stored, same⟩ |
      ⟨root, block, state, pulled, known, stored, run, same, earlier⟩
  · rw [same] at later
    exact (UInt64.lt_irrefl _ later).elim
  · obtain ⟨block, known⟩ := reachedU.known_of_blockState stored
    have read := (reachedU.getCheckpointBlock_of_blockState sound aligned positive window stored
      (.inl (by simp [same])) later).resolve_right notZero
    obtain ⟨_, held⟩ := carry known stored read.1
    rw [same] at finalLe
    exact UInt64.le_trans finalLe (reachedW.justified_le_of_blockState sound held)
  · have read := (reachedU.getCheckpointBlock_of_blockState sound aligned positive window stored
      (.inr ⟨pulled, run, by simp [same]⟩) later).resolve_right notZero
    obtain ⟨blockHeld, stateHeld⟩ := carry known stored read.1
    -- The receiver's clock is at or after the sender's.
    obtain ⟨currentW, currentWOk⟩ := (forward w receiver k).exists_getCurrentSlot slots
    have slotLe := e.currentSlot_le_of_time_le start sender receiver (by omega) upToDate
      currentUOk currentWOk
    have epochLe : computeEpochAtSlot preset currentU ≤ computeEpochAtSlot preset currentW :=
      UInt64.le_iff_toNat_le.mpr (epoch_le_of_slot_le _ _ (UInt64.le_iff_toNat_le.mp slotLe))
    rw [same] at finalLe
    exact UInt64.le_trans finalLe ((forward w receiver k).justified_le_of_pulledUp sound positive
      slots currentWOk blockHeld stateHeld run (UInt64.lt_of_lt_of_le earlier epochLe))

/-- A caller's slot-start finalized root is on each up-to-date honest head, next slot to `last`.

Otherwise two honest stores collide by `last`, or cross-store direct-safety evidence holds.

It assumes the genesis run, preset parameters, synchrony, delayed admission and fitting delays.

It needs held-store and stake bounds, nonzero held roots and the anchor at an epoch start. -/
public theorem Execution.finalized_ancestor_of_heads_or_evidence
    {Δ last : ℕ} {anchor : Store preset fork} {horizon : Epoch} {g : ForkedBeaconState preset}
    (pre : Run config checks g ⟨fork, anchorState⟩) (genesis : Genesis config checks g)
    (parameters : DirectSafety.Parameters preset) (sync : e.Synchronous Δ)
    (admitted : BlocksAdmitted e 0 Δ last) (fits : DelayFits fork config genesisTimeMs Δ)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (slots : 0 < config.SLOT_DURATION_MS) (bounded : HonestStoreEpochsBounded (e := e) horizon last)
    (roots : HeldBlockStateRootsNonzero (e := e) last) (absent : AnchorParentAbsent (e := e) last)
    (early : HeldStatesBeforeUpgrade (e := e) last)
    (enough : HeldRunStakeFloor (e := e) pre horizon last)
    (terminal : HeldTerminalStakeFloor (e := e) horizon last)
    {u w : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) {n k : ℕ}
    {s next : Slot} {begin following : UInt64}
    (beginOk : computeTimeAtSlotMs config genesisTimeMs s = .ok begin)
    (atStart : (e.world n).time = begin.toNat) (nextOk : addChecked s 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following)
    (afterNext : following.toNat ≤ (e.world k).time) (byLast : (e.world k).time ≤ last)
    (ready : UpToDate config checks sources (e.world k).time ((e.world k).view w)
      ((e.world k).state w))
    {head : ForkChoiceNode} (headOk : ((e.world k).state w).getHead config = .ok head) :
    ((e.world k).state w).isAncestor head
        ⟨((e.world n).state u).finalizedCheckpoint.root, .pending⟩ = .ok true ∨
      HonestCollision (e := e) last ∨ CrossStoreDirectSafetyEvidence (e := e) pre last := by
  have sound := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  rcases e.blocksAgree_or_collision last with agree | collision
  swap
  · exact .inr (.inl collision)
  rcases e.crossStoreFinality_or_evidence anchored start anchorSlot boundary slots bounded roots
      absent parameters genesis pre early enough terminal with crossFinal | direct
  swap
  · exact .inr (.inr direct)
  -- The caller is at its slot start, a delay before the next slot's start.
  obtain ⟨due, dueOk⟩ := fits.1
  have fit := fits.2 s next begin due following nextOk beginOk dueOk followingOk
  have late : (e.world n).time + Δ ≤ (e.world k).time := by omega
  have nBound : (e.world n).time ≤ last := by omega
  -- The receiver has justified the caller's finalized epoch.
  have le := Execution.finalized_epoch_le_justified_of_late sync slots positive window admitted
    anchored sound anchorSlot start roots agree crossFinal caller receiver late byLast ready
  -- The receiver reads that finality below its justified root, which its head descends from.
  have read := crossFinal u caller w receiver n k nBound byLast le
  obtain ⟨-, finalBlock, -, finalFound, -, below⟩ := Store.isAncestor_of_getCheckpointBlock read
  have headDescends := Store.isAncestor_getHead headOk
  obtain ⟨justifiedBlock, justifiedFound⟩ := Store.held_of_isAncestor headDescends
  exact .inl (Store.isAncestor_trans justifiedFound finalFound headDescends below)

end EthLib.Consensus.Models.Network

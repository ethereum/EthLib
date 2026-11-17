module

public import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.FfgSlackChain
public import EthLib.Consensus.Proofs.Transition.FfgJustification
public import EthLib.Consensus.Proofs.Transition.ValidatorKeys
public import EthLib.Consensus.Proofs.Transition.TargetSlots
public import EthLib.Consensus.Proofs.ForkChoice.CommitteeAgreement
public import EthLib.Consensus.Proofs.ForkChoice.VoteDelivery

/-!
# Proofs: the votes behind a store's justified checkpoint

A store's justified checkpoint after the anchor was set by one count of votes.

That count ran in a state the store holds, or on the way from such a state to a held child.

The votes it counts were cast by the attestations of held blocks, or are older than the anchor.

The roots that such a state reads in its history are those the store's walk reaches.

That needs the anchor's latest header to be the anchor block's, with a zero state root.

The anchor store checks neither, so the results take it as a hypothesis.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}

/-- The votes cast by the attestations of the held blocks at or below a root.

Each is read in the committees of the held parent state, processed to the block's slot. -/
def Store.votesBelow (store : Store preset fork) (config : Config) (checks : SignatureChecks)
    (root : Root) : Set (ValidatorIndex × AttestationData) :=
  {vote | ∃ (blockRoot : Root) (block : BeaconBlock preset fork)
      (parent advanced : BeaconState preset fork),
    store.blocks[blockRoot]? = some block ∧
    store.isAncestor ⟨root, .pending⟩ ⟨blockRoot, .pending⟩ = .ok true ∧
    store.blockStates[block.parentRoot]? = some parent ∧
    processSlots config checks parent block.slot = .ok advanced ∧
    vote ∈ blockVotes advanced block}

/-- A block descends from each pending node that its parent descends from, in every fork.

The store must hold the block and its parent, the parent at an earlier slot. -/
private theorem Store.isAncestor_pending_of_parent {store : Store preset fork}
    {root ancestor : Root}
    {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot)
    (descends : store.isAncestor ⟨block.parentRoot, .pending⟩ ⟨ancestor, .pending⟩ = .ok true) :
    store.isAncestor ⟨root, .pending⟩ ⟨ancestor, .pending⟩ = .ok true := by
  by_cases gloas : .glamsterdam ≤ fork
  swap
  · exact Store.isAncestor_of_parent (Nat.lt_of_not_le gloas) found parentFound lower descends
  -- The test reads the ancestor's block, so the store holds it.
  cases known : store.block ancestor with
  | error error => simp [Store.isAncestor, known, bind, Except.bind] at descends
  | ok ancestorBlock =>
  obtain ⟨parentBlock, parentKnown, le⟩ :=
    Store.slot_le_of_isAncestor (Store.block_ok_iff.mp known) descends
  rw [parentFound, Option.some.injEq] at parentKnown
  subst parentKnown
  -- The block is above the ancestor's slot, so the walk from it steps to its parent.
  have above : ¬ block.slot ≤ ancestorBlock.slot := fun atMost =>
    UInt64.not_le.mpr lower (UInt64.le_trans atMost le)
  have step := Store.getAncestor_step (node := ⟨root, .pending⟩) found above parentFound lower
  -- From Gloas only the root of the walk counts, and it does not depend on the status.
  have same := Store.getAncestor_root (store := store) ⟨block.parentRoot, .pending⟩
    (parentPayloadStatus block parent) ancestorBlock.slot
  rw [Store.isAncestor_pending gloas] at descends ⊢
  simp only [known, step, bind, Except.bind] at descends ⊢
  cases walk : store.getAncestor ⟨block.parentRoot, .pending⟩ ancestorBlock.slot <;>
    cases other : store.getAncestor ⟨block.parentRoot, parentPayloadStatus block parent⟩
      ancestorBlock.slot <;>
    simp_all [Functor.map, Except.map]

/-- Slots keep the participation backed by a set of votes, and the early justified checkpoints.

An epoch must have a slot, and the buffer of roots must cover two epochs.

There must be more than `MIN_SEED_LOOKAHEAD + 2` epochs of mixes. -/
theorem votedParticipation_processSlots {votes : Set (ValidatorIndex × AttestationData)}
    {state after : BeaconState preset fork} {slot : Slot}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (flags : TargetFlagsVoted votes state) (pending : PendingVoted votes state)
    (early : JustifiedEarly state) (computed : processSlots config checks state slot = .ok after) :
    TargetFlagsVoted votes after ∧ PendingVoted votes after ∧ JustifiedEarly after := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, slots⟩ := computed
  exact ⟨TargetFlagsVoted.of_advanceSlots positive window early flags slots,
    fun before => PendingVoted.of_advanceSlots before apart early pending slots before,
    early.of_advanceSlots slots⟩

/-- The participation of a held state is backed by two kinds of votes.

The first are the anchor's votes for its own epochs or earlier.

The second are the votes of the held blocks at or below the state's root. -/
theorem Store.ForwardReachableWith.held_participation {store : Store preset fork}
    {votes : Set (ValidatorIndex × AttestationData)}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (flags : TargetFlagsVoted votes anchorState) (pending : PendingVoted votes anchorState)
    (early : JustifiedEarly anchorState)
    {root : Root} {base : BeaconState preset fork}
    (held : store.blockStates[root]? = some base) :
    TargetFlagsVoted ({vote | vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
        store.votesBelow config checks root) base ∧
      PendingVoted ({vote | vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
        store.votesBelow config checks root) base ∧
      JustifiedEarly base := by
  have reachable := reached.reachable
  induction hslot : base.slot.toNat using Nat.strong_induction_on generalizing root base with
  | _ n ih =>
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reached.blockStatesFromParents found
  rw [held, Option.some.injEq] at keptFound
  subst keptFound
  by_cases same : block = anchorBlock
  · -- The anchor state is backed by the anchor's votes of its own epochs or earlier.
    rw [isAnchor same]
    obtain ⟨flagsEarlier, pendingEarlier⟩ := flags.earlier pending
    exact ⟨flagsEarlier.mono Set.subset_union_left, pendingEarlier.mono Set.subset_union_left,
      early⟩
  · obtain ⟨parentState, stepChecks, engine, signed, sameChecks, message, parentFound,
      transition⟩ := notAnchor same
    rw [sameChecks] at transition
    obtain ⟨lowerSlot, atBlock⟩ := stateTransition_slot transition
    obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok transition
    rw [message] at slotsOk blockOk lowerSlot atBlock
    -- The parent state is earlier, so its participation is backed below the parent.
    obtain ⟨parentFlags, parentPending, parentEarly⟩ :=
      ih _ (hslot ▸ atBlock ▸ UInt64.lt_iff_toNat_lt.mp lowerSlot) parentFound rfl
    -- The parent block is below the block, so its votes are below the block too.
    obtain ⟨parentBlock, parentKnown⟩ := reachable.known_of_blockState parentFound
    have parentLower : parentBlock.slot < block.slot := UInt64.lt_of_le_of_lt
      (Store.Reachable.slot_le_of_blockState anchorSlot reachable parentKnown parentFound)
      lowerSlot
    have below : {vote : ValidatorIndex × AttestationData |
          vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
        store.votesBelow config checks block.parentRoot ⊆
        {vote | vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
          store.votesBelow config checks root := by
      refine Set.union_subset_union_right _ ?_
      rintro vote ⟨blockRoot, voter, parent, voterAdvanced, voterFound, descends, rest⟩
      exact ⟨blockRoot, voter, parent, voterAdvanced, voterFound,
        Store.isAncestor_pending_of_parent found parentKnown parentLower descends, rest⟩
    -- The block's own votes are below its root, as it descends from itself.
    have own : blockVotes advanced block ⊆
        {vote | vote.2.target.epoch ≤ getCurrentEpoch anchorState} ∪
          store.votesBelow config checks root := fun vote cast =>
      .inr ⟨root, block, parentState, advanced, found, Store.isAncestor_self found,
        parentFound, slotsOk, cast⟩
    -- The slots up to the block keep the parent's backing.
    obtain ⟨advancedFlags, advancedPending, advancedEarly⟩ := votedParticipation_processSlots
      positive window apart (parentFlags.mono below) (parentPending.mono below) parentEarly slotsOk
    -- The block adds only its own votes.
    obtain ⟨blockFlags, blockPending⟩ :=
      votedParticipation_processBlock apart advancedFlags advancedPending own blockOk
    exact ⟨blockFlags, blockPending, advancedEarly.of_frame (frame_processBlock blockOk)⟩

/-- Some count of slot steps, then one more step, is that count plus one of slot steps. -/
private theorem advanceSlots_succ_of_advanceSlot :
    ∀ (count : Nat) {state mid after : BeaconState preset fork},
      advanceSlots config checks count state = .ok mid →
      advanceSlot config checks mid = .ok after →
        advanceSlots config checks (count + 1) state = .ok after
  | 0, _, _, _, computed, step => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp only [advanceSlots, bind_ok_iff]
    exact ⟨_, step, rfl⟩
  | count + 1, _, _, _, computed, step => by
    rw [advanceSlots, bind_ok_iff] at computed ⊢
    obtain ⟨next, nextOk, rest⟩ := computed
    exact ⟨next, nextOk, advanceSlots_succ_of_advanceSlot count rest step⟩

/-- A state some count of slot steps after a base is the base, or the base processed to a slot. -/
private theorem eq_or_processSlots_of_advanceSlots {count : Nat}
    {base state : BeaconState preset fork}
    (computed : advanceSlots config checks count base = .ok state) :
    state = base ∨ ∃ slot, processSlots config checks base slot = .ok state := by
  rcases count with _ | count
  · simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact .inl computed.symm
  · have slotNat := advanceSlots_slot _ computed
    simp only [processSlots, bind_ok_iff, ensure_ok_iff]
    -- The count of slots from the base to the state is the count of steps.
    exact .inr ⟨state.slot, (), UInt64.lt_iff_toNat_lt.mpr (by omega),
      by rwa [show state.slot.toNat - base.slot.toNat = count + 1 by omega]⟩

/-- Slot steps keep the current justified checkpoint, or the last step that changes it is found.

That step starts on a state some steps after the base, at the last slot of an epoch.

It caches that slot, then justification on the cached state sets the final checkpoint.

The cached state still has another checkpoint. -/
private theorem advanceSlots_last_justification {base : BeaconState preset fork} :
    ∀ (count : Nat) {done : Nat} {start final : BeaconState preset fork},
      advanceSlots config checks done base = .ok start →
      advanceSlots config checks count start = .ok final →
      final.currentJustifiedCheckpoint = start.currentJustifiedCheckpoint ∨
      ∃ (state counted pulled : BeaconState preset fork) (steps : Nat),
        advanceSlots config checks steps base = .ok state ∧ state.slot < final.slot ∧
        (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
        processSlot state = .ok counted ∧
        processJustificationAndFinalization counted = .ok pulled ∧
        pulled.currentJustifiedCheckpoint = final.currentJustifiedCheckpoint ∧
        counted.currentJustifiedCheckpoint ≠ final.currentJustifiedCheckpoint
  | 0, _, _, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact .inl (computed ▸ rfl)
  | count + 1, done, start, final, before, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, step, rest⟩ := computed
    -- A later step that changes the checkpoint is the last one.
    rcases advanceSlots_last_justification count
        (advanceSlots_succ_of_advanceSlot done before step) rest with kept | changed
    swap
    · exact .inr changed
    have finalSlot := advanceSlots_slot count rest
    obtain ⟨slot, cached, epoched, slotNat, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok step
    have cachedKeeps := (frame_processSlot cachedOk).currentJustified
    by_cases same : epoched.currentJustifiedCheckpoint = start.currentJustifiedCheckpoint
    · exact .inl (kept.trans same)
    right
    unfold epochIfLast at epochedOk
    split at epochedOk
    · rename_i last
      -- The epoch step is justification, then steps that keep the checkpoint.
      obtain ⟨pulled, pulledOk, frame⟩ := processEpoch_frame epochedOk
      have lastNat := congrArg UInt64.toNat last
      rw [UInt64.toNat_mod, slotNat] at lastNat
      refine ⟨start, cached, pulled, done, before, UInt64.lt_iff_toNat_lt.mpr ?_, lastNat,
        cachedOk, pulledOk, (kept.trans frame.currentJustified).symm, ?_⟩
      · rw [finalSlot]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (by simp only [slotNat]; omega)
      · rw [kept, cachedKeeps]
        exact Ne.symm same
    · -- Without the epoch step, the cached slot keeps the checkpoint.
      simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact absurd cachedKeeps same

/-- A held state's current justified checkpoint after the anchor's epoch was set by one step.

That step is justification on a held state, or the epoch step toward a held child.

The epoch step runs on the cached last slot of an epoch, on the walk from the held state. -/
private theorem Store.ForwardReachableWith.counted_of_blockState {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (sound : Invariant anchorState) {checkpoint : Checkpoint}
    (after : getCurrentEpoch anchorState < checkpoint.epoch) {root : Root}
    {held : BeaconState preset fork} (found : store.blockStates[root]? = some held)
    (same : held.currentJustifiedCheckpoint = checkpoint) :
    ∃ (root : Root) (base counted pulled : BeaconState preset fork),
      store.blockStates[root]? = some base ∧
      (counted = base ∨
        ∃ (state : BeaconState preset fork) (childRoot : Root) (child : BeaconBlock preset fork),
          store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
          state.slot < child.slot ∧
          (state = base ∨ ∃ slot, processSlots config checks base slot = .ok state) ∧
          (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
          processSlot state = .ok counted) ∧
      processJustificationAndFinalization counted = .ok pulled ∧
      pulled.currentJustifiedCheckpoint = checkpoint ∧
      counted.currentJustifiedCheckpoint ≠ checkpoint := by
  induction hslot : held.slot.toNat using Nat.strong_induction_on generalizing root held with
  | _ n ih =>
  obtain ⟨block, blockFound⟩ := reached.reachable.known_of_blockState found
  obtain ⟨kept, keptFound, isAnchor, notAnchor⟩ := reached.blockStatesFromParents blockFound
  rw [found, Option.some.injEq] at keptFound
  subst keptFound
  by_cases anchored : block = anchorBlock
  · -- The anchor state's justified epoch is at most its previous epoch, so not after its epoch.
    have settled : held.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch anchorState := by
      rw [isAnchor anchored]
      exact sound.settled
    rw [same] at settled
    exact absurd (UInt64.le_trans settled (getPreviousEpoch_le _)) (UInt64.not_le.mpr after)
  obtain ⟨parent, _, engine, signed, rfl, message, parentFound, transition⟩ := notAnchor anchored
  obtain ⟨advanced, slotsOk, advancedSlot, -, blockOk, -⟩ := stateTransition_ok transition
  -- The block keeps the checkpoint of the state at its slot.
  have blockKeeps := (frame_processBlock blockOk).currentJustified
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨-, -, advancedOk⟩ := slotsOk
  rcases advanceSlots_last_justification _ (done := 0) rfl advancedOk with kept |
      ⟨state, counted, pulled, steps, reach, below, last, countedOk, pulledOk, pulledSame,
        countedOther⟩
  · -- No slot changes the checkpoint, so the parent state has it, at an earlier slot.
    obtain ⟨lower, atBlock⟩ := stateTransition_slot transition
    rw [← atBlock] at lower
    exact ih _ (hslot ▸ UInt64.lt_iff_toNat_lt.mp lower) parentFound
      (by rw [← kept, ← blockKeeps, same]) rfl
  · refine ⟨block.parentRoot, parent, counted, pulled, parentFound,
      .inr ⟨state, root, block, blockFound, rfl, ?_,
        eq_or_processSlots_of_advanceSlots reach, last, countedOk⟩, pulledOk, ?_, ?_⟩
    · rw [← message, ← advancedSlot]
      exact below
    · rw [pulledSame, ← blockKeeps, same]
    · rw [← same, blockKeeps]
      exact countedOther

/-- The store's justified checkpoint after the anchor's epoch was set anew by one justification.

Either the step ran on a held state, as the store pulls up a tip.

Or it ran in the epoch step of the slots from a held state toward a held child.

That epoch step runs on the cached last slot of an epoch. -/
theorem Store.ForwardReachableWith.justified_counted {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (sound : Invariant anchorState)
    (after : getCurrentEpoch anchorState < store.justifiedCheckpoint.epoch) :
    ∃ (root : Root) (base counted pulled : BeaconState preset fork),
      store.blockStates[root]? = some base ∧
      (counted = base ∨
        ∃ (state : BeaconState preset fork) (childRoot : Root) (child : BeaconBlock preset fork),
          store.blocks[childRoot]? = some child ∧ child.parentRoot = root ∧
          state.slot < child.slot ∧
          (state = base ∨ ∃ slot, processSlots config checks base slot = .ok state) ∧
          (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 ∧
          processSlot state = .ok counted) ∧
      processJustificationAndFinalization counted = .ok pulled ∧
      pulled.currentJustifiedCheckpoint = store.justifiedCheckpoint ∧
      counted.currentJustifiedCheckpoint ≠ store.justifiedCheckpoint := by
  rcases reached.reachable.justified_origins _ (.inl rfl) with ⟨_, -, anchored⟩ |
      ⟨root, state, found, same⟩ | ⟨root, state, pulled, found, pulledOk, same⟩
  · -- The anchor checkpoint is at the anchor's epoch.
    rw [anchored] at after
    exact absurd after (UInt64.lt_irrefl _)
  · exact reached.counted_of_blockState sound after found same.symm
  · by_cases kept : state.currentJustifiedCheckpoint = store.justifiedCheckpoint
    · exact reached.counted_of_blockState sound after found kept
    · exact ⟨root, state, state, pulled, found, .inl rfl, pulledOk, same.symm, kept⟩

/-- Caching a slot keeps the root read at an earlier slot that stays in the buffer of roots.

The cache writes only the position of the state's own slot.

A slot exactly one buffer length earlier shares that position, so it is excluded. -/
private theorem getBlockRootAtSlot_of_processSlot {state counted : BeaconState preset fork}
    {query : Slot} {root : Root}
    (cached : processSlot state = .ok counted)
    (read : getBlockRootAtSlot counted query = .ok root)
    (recent : state.slot.toNat < query.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    getBlockRootAtSlot state query = .ok root := by
  obtain ⟨_, -, written⟩ := processSlot_blockRoots cached
  obtain ⟨before, fits, within, readOk⟩ := getBlockRootAtSlot_ok_iff.mp read
  rw [processSlot_slot cached] at before within
  -- The written position and the read position differ modulo the buffer length.
  have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
      query % preset.SLOTS_PER_HISTORICAL_ROOT := by
    intro same
    have same' := congrArg UInt64.toNat same
    rw [UInt64.toNat_mod, UInt64.toNat_mod] at same'
    exact Nat.mod_ne_of_sub_lt before (by omega) same'
  rw [readCircular_writeCircular_of_ne written other] at readOk
  exact getBlockRootAtSlot_ok_iff.mpr ⟨before, fits, within, readOk⟩

/-- A history root read after empty slots from a held state agrees with the ancestor walk.

The anchor's latest header must be the anchor block's, with a zero state root. -/
private theorem Store.Reachable.processSlots_history_ancestor {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork), store.blocks[r]? = some b →
      b.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {state advanced : BeaconState preset fork} {slot query : Slot}
    (stored : store.blockStates[root]? = some state)
    (computed : processSlots config checks state slot = .ok advanced)
    (read : getBlockRootAtSlot advanced query = .ok readRoot)
    (later : anchorState.slot ≤ query) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ query = .ok readRoot := by
  have lookahead : lookaheadState config checks state slot = .ok advanced := by
    simp [lookaheadState, (processSlots_slot computed).1, computed, Except.mapError]
  by_cases old : query < state.slot
  -- An earlier slot was already in the held state's history.
  · have run := computed
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at run
    obtain ⟨_, -, advancedOk⟩ := run
    exact reachable.blockState_history_ancestor (UInt64.le_of_eq anchorSlot) nonzero stored
      (getBlockRootAtSlot_of_advanceSlots advancedOk read old) later _
  · obtain ⟨block, found⟩ := reachable.known_of_blockState stored
    -- The held state's header is its block's, with a zero state root, anchor included.
    have zero : state.latestBlockHeader.stateRoot = Vector.replicate 32 0 := by
      by_cases same : block = anchorBlock
      · obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
        rw [stored, Option.some.injEq] at postOk
        rw [postOk, anchored same]
        exact anchorZero
      · rw [(reachable.blockState_header found stored same).2.2.choose_spec.2]
    obtain ⟨-, headerSlot, proposer, parent, body⟩ :=
      reachable.blockState_latestBlockHeader anchorSlot anchorHeader found stored
    have stateRooted := reachable.blockState_root found stored
    -- Empty slots fill the zero state root with the block's state root.
    have filled := processSlots_latestBlockHeader_of_zero zero stateRooted
      (nonzero _ _ found) computed
    have cachedRoot := getBlockRootAtSlot_processSlots_header stateRooted (nonzero _ _ found)
      computed read (UInt64.not_lt.mp old)
    -- So the root read is the block's own root, which the store holds.
    have blockHash := (BeaconBlock.hashTreeRoot_header body).trans (reachable.root found)
    simp only [filled, headerSlot, proposer, parent, blockHash, Except.ok.injEq] at cachedRoot
    rw [cachedRoot] at found
    exact reachable.lookahead_history_ancestor_of_held (UInt64.le_of_eq anchorSlot) nonzero
      reachable stored found lookahead read later _

/-- A block root that a counted state reads after the anchor slot is held.

The store's walk from the held root reaches it.

The anchor's latest header must be the anchor block's, with a zero state root.

The post-state of a block has a zero state root in its header.

The anchor store checks neither.

When the count caches a slot, the read slot must stay less than one buffer length behind.

Caching writes the root at the state's slot.

That position is shared with the slot one buffer length earlier. -/
theorem Store.ForwardReachableWith.counted_history {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (nonzero : ∀ (r : Root) (b : BeaconBlock preset fork), store.blocks[r]? = some b →
      b.stateRoot ≠ Vector.replicate 32 0)
    {root readRoot : Root} {base state counted : BeaconState preset fork} {slot : Slot}
    {epoch : Epoch}
    (held : store.blockStates[root]? = some base)
    (advanced : state = base ∨ processSlots config checks base slot = .ok state)
    (cached : counted = base ∨ processSlot state = .ok counted)
    (recent : processSlot state = .ok counted → ∀ start,
      computeStartSlotAtEpoch preset epoch = .ok start →
        state.slot.toNat < start.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (read : getBlockRoot counted epoch = .ok readRoot)
    (afterAnchor : ∀ start, computeStartSlotAtEpoch preset epoch = .ok start →
      anchorState.slot ≤ start) :
    (∃ b, store.blocks[readRoot]? = some b) ∧
      store.getCheckpointBlock root epoch = .ok readRoot := by
  have reachable := reached.reachable
  obtain ⟨start, startOk, startRead⟩ := getBlockRoot_ok_iff.mp read
  have later := afterAnchor start startOk
  have ancestorLe := UInt64.le_of_eq anchorSlot
  -- Every case reduces to the walk from the held root at the start of the epoch.
  have walk : (·.root) <$> store.getAncestor ⟨root, .pending⟩ start = .ok readRoot := by
    rcases cached with rfl | cachedOk
    · exact reachable.blockState_history_ancestor ancestorLe nonzero held startRead later _
    · have stateRead := getBlockRootAtSlot_of_processSlot cachedOk startRead
        (recent cachedOk start startOk)
      rcases advanced with rfl | slotsOk
      · exact reachable.blockState_history_ancestor ancestorLe nonzero held stateRead later _
      · exact reachable.processSlots_history_ancestor anchorSlot anchorHeader anchorZero nonzero
          held slotsOk stateRead later
  cases ancestor : store.getAncestor ⟨root, .pending⟩ start with
  | error error => simp [ancestor, Functor.map, Except.map] at walk
  | ok node =>
    simp only [ancestor, Functor.map, Except.map, Except.ok.injEq] at walk
    obtain ⟨block, found, -⟩ := Store.getAncestor_le ancestor
    refine ⟨⟨block, walk ▸ found⟩, ?_⟩
    simp [Store.getCheckpointBlock, startOk, ancestor, walk, Except.mapError, bind,
      Except.bind, pure, Except.pure]

/-! ## The state of a vote's target, and the vote as a statement -/

/-- Slots keep the public keys as a prefix, the fork versions and the genesis validators root. -/
private def KeysKept (state after : BeaconState preset fork) : Prop :=
  validatorKeys state <+: validatorKeys after ∧ after.forkVersions = state.forkVersions ∧
    after.genesisValidatorsRoot = state.genesisValidatorsRoot

private theorem KeysKept.trans {first second third : BeaconState preset fork}
    (one : KeysKept first second) (two : KeysKept second third) : KeysKept first third :=
  ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.trans one.2.2⟩

/-- A frame keeps the keys, the fork versions and the genesis validators root. -/
private theorem KeysKept.of_frame {state after : BeaconState preset fork}
    (frame : Frame state after) : KeysKept state after :=
  ⟨frame.pubkeysPrefix, frame.forkVersions, frame.genesisValidatorsRoot⟩

/-- Slots keep the keys, the fork versions and the genesis validators root. -/
private theorem keysKept_processSlots {state after : BeaconState preset fork} {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) : KeysKept state after := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, -, advanced⟩ := computed
  -- Each slot keeps the three, by master's facts about one slot.
  have steps : ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after → KeysKept state after := by
    intro count
    induction count with
    | zero =>
      intro state after ok
      simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at ok
      subst ok
      exact ⟨List.prefix_refl _, rfl, rfl⟩
    | succ count ih =>
      intro state after ok
      simp only [advanceSlots, bind_ok_iff] at ok
      obtain ⟨next, nextOk, rest⟩ := ok
      obtain ⟨forkVersions, root, -⟩ := advanceSlot_kept nextOk
      exact KeysKept.trans ⟨(keys_advanceSlot nextOk).1, forkVersions, root⟩ (ih rest)
  exact steps _ advanced

/-- A block keeps the keys, the fork versions and the genesis validators root. -/
private theorem keysKept_stateTransition {state after : BeaconState preset fork}
    {checks' : SignatureChecks} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks' engine state signed validateResult = .ok after) :
    KeysKept state after := by
  obtain ⟨advanced, slotsOk, -, -, blockOk, -⟩ := stateTransition_ok computed
  exact (keysKept_processSlots slotsOk).trans (.of_frame (frame_processBlock blockOk))

/-- The state of a vote's target runs to the state before a held block that carries the vote.

The target root is the block's ancestor at the start of the target epoch, before the block.

The run keeps the inputs of the committees, the keys, the fork versions and the root. -/
private theorem Store.ForwardReachableWith.target_run {store : Store preset fork}
    (reached : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    {blockRoot targetRoot : Root} {block : BeaconBlock preset fork}
    {parent advanced base : BeaconState preset fork} {epoch : Epoch} {start : Slot}
    {status : PayloadStatus}
    (found : store.blocks[blockRoot]? = some block)
    (parentHeld : store.blockStates[block.parentRoot]? = some parent)
    (slotsOk : processSlots config checks parent block.slot = .ok advanced)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start) (before : start < block.slot)
    (walk : (·.root) <$> store.getAncestor ⟨blockRoot, status⟩ start = .ok targetRoot)
    (baseFound : store.blockStates[targetRoot]? = some base) :
    ∃ boundary, lookaheadState config checks base start = .ok boundary ∧
      RunKept boundary advanced ∧ KeysKept boundary advanced := by
  have reachable := reached.reachable
  -- The parent block is held, below the block.
  obtain ⟨parentBlock, parentFound⟩ := reachable.known_of_blockState parentHeld
  have parentLe := reachable.slot_le_of_blockState anchorSlot parentFound parentHeld
  have parentLt : parent.slot < block.slot := (processSlots_slot slotsOk).1
  have lower : parentBlock.slot < block.slot := UInt64.lt_of_le_of_lt parentLe parentLt
  -- The relation that the run keeps.
  let R := fun (s t : BeaconState preset fork) => RunKept s t ∧ KeysKept s t
  have toAdvanced : R parent advanced :=
    ⟨runKept_processSlots slotsOk, keysKept_processSlots slotsOk⟩
  -- The walk from the block steps to its parent.
  rw [Store.getAncestor_step found (UInt64.not_le.mpr before) parentFound lower,
    Store.getAncestor_root ⟨block.parentRoot, parentPayloadStatus block parentBlock⟩ .pending]
    at walk
  by_cases late : start < parentBlock.slot
  · -- The target is at or below the parent's slot: the checkpoint prefix runs to the parent.
    have target : store.getCheckpointBlock block.parentRoot epoch = .ok targetRoot := by
      simp only [Store.getCheckpointBlock, startOk, Except.mapError, bind, Except.bind]
      exact walk
    obtain ⟨boundary, boundaryOk, toParent⟩ :=
      reached.relation_of_checkpointPrefix (checkpoint := ⟨epoch, targetRoot⟩) R
        (fun s => ⟨RunKept.refl s, ⟨List.prefix_refl _, rfl, rfl⟩⟩)
        (fun one two => ⟨one.1.trans two.1, one.2.trans two.2⟩)
        (fun ok => ⟨runKept_stateTransition ok, keysKept_stateTransition ok⟩)
        (fun midOk atOrAfter ok => relation_of_processSlots_of_stateTransition R
          (fun one two => ⟨one.1.trans two.1, one.2.trans two.2⟩)
          (fun ok => ⟨runKept_processSlots ok, keysKept_processSlots ok⟩)
          (fun ok => ⟨runKept_processBlock ok, .of_frame (frame_processBlock ok)⟩)
          midOk atOrAfter ok)
        anchorSlot target parentFound startOk (UInt64.le_of_lt late) baseFound parentHeld
    exact ⟨boundary, boundaryOk, toParent.1.trans toAdvanced.1, toParent.2.trans toAdvanced.2⟩
  · -- The parent is at or below the start, so it is the target.
    rw [Store.getAncestor_of_le parentFound (UInt64.not_lt.mp late)] at walk
    simp only [Functor.map, Except.map, Except.ok.injEq] at walk
    rw [← walk, parentHeld, Option.some.injEq] at baseFound
    subst baseFound
    unfold lookaheadState
    split
    · -- The slots to the start are the first part of the slots to the block.
      rename_i belowStart
      obtain ⟨mid, midOk, restOk⟩ := processSlots_split belowStart before slotsOk
      refine ⟨mid, by simp [midOk, Except.mapError], runKept_processSlots restOk,
        keysKept_processSlots restOk⟩
    · exact ⟨parent, rfl, toAdvanced⟩

/-- The least inclusion delay of an attestation is at least one slot.

So an attestation in a block is of an earlier slot than the block. -/
structure Preset.InclusionDelayPositive (preset : Preset) : Prop where
  delay : 1 ≤ preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat

/-- The mainnet inclusion delay is positive. -/
theorem Preset.inclusionDelayPositive_mainnet : Preset.mainnet.InclusionDelayPositive := by
  constructor; decide

/-- The minimal inclusion delay is positive. -/
theorem Preset.inclusionDelayPositive_minimal : Preset.minimal.InclusionDelayPositive := by
  constructor; decide

end EthLib.Consensus

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A vote of a held block, for a target the store reaches, is a statement of a sent message.

The block's message is in the store's view, so it was sent.

The store reads the block's attestation in the state of its target, with a valid signature.

The block checked that signature on its own state.

The check reads only the signers' keys, the fork versions and the genesis validators root.

The run from the target state to the block keeps those.

So the vote is a statement of the block in the sense of the network model.

Its slot is before the store's current slot, by the inclusion delay. -/
theorem Execution.exists_sent_of_votesBelow {anchor : Store preset fork}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (delay : preset.InclusionDelayPositive) {w : ValidatorIndex} (honest : w ∈ J) {k : ℕ}
    (absent : ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {vote : ValidatorIndex × AttestationData} {slot : Slot}
    (cast : vote ∈ ((e.world k).state w).votesBelow config checks root)
    (target : ((e.world k).state w).getCheckpointBlock root vote.2.target.epoch =
      .ok vote.2.target.root)
    (slotOk : ((e.world k).state w).getCurrentSlot config = .ok slot) :
    ∃ m ∈ (e.world k).sent, vote ∈ statements config checks anchorState anchorBlock m ∧
      vote.2.slot < slot := by
  have reached := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  have reachable := reached.reachable
  obtain ⟨blockRoot, block, parent, advanced, found, below, parentHeld, slotsOk, attestation,
    included, dataEq, indices, indicesOk, member⟩ := cast
  -- The block is not the anchor, whose parent the store does not hold.
  have notAnchor : block ≠ anchorBlock := by
    rintro rfl
    obtain ⟨_, held⟩ := reachable.known_of_blockState parentHeld
    rw [absent] at held
    cases held
  rcases e.exists_signed_of_blocks found with ⟨initial, -⟩ |
      ⟨signed, pre, post, seen, message, -, preHeld, transitioned, -⟩
  · -- The store at the start holds only the anchor block.
    obtain ⟨anchorRoot, -, blocks, -⟩ := getForkchoiceStore_maps anchored
    rw [start w honest, blocks, Std.TreeMap.getElem?_insert] at initial
    split at initial
    · exact (notAnchor (Option.some.inj initial).symm).elim
    · simp at initial
  rw [parentHeld, Option.some.injEq] at preHeld
  subst preHeld
  obtain ⟨advanced', slotsOk', -, -, blockOk, -⟩ := stateTransition_ok transitioned
  rw [message] at slotsOk' blockOk
  rw [slotsOk, Except.ok.injEq] at slotsOk'
  subst slotsOk'
  -- The block checked the attestation, in a recent epoch and late enough.
  obtain ⟨input, checked, indexed, started, site, indexedOk, valid, recent, epochEq, late⟩ :=
    processBlock_attestation_checked apart blockOk included
  have blockSlot : advanced.slot = block.slot := (processSlots_slot slotsOk).2
  -- The target is the store's walk from the root, at the start of the target epoch.
  have targetCopy := target
  simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq] at targetCopy
  obtain ⟨first, firstOk, node, walk, rooted⟩ := targetCopy
  rw [dataEq] at firstOk rooted
  have firstNat := (computeStartSlotAtEpoch_ok_iff.mp firstOk).2
  have firstLe : first.toNat ≤ attestation.data.slot.toNat := by
    rw [firstNat, epochEq]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  have delayNat := delay.delay
  have before : first < block.slot := UInt64.lt_iff_toNat_lt.mpr (by
    rw [← blockSlot]
    omega)
  -- The walk from the root passes the block, so the target is the block's walk too.
  obtain ⟨reach, reachWalk, reachRoot⟩ := Store.getAncestor_of_isAncestor found below
  rw [Store.getAncestor_trans (UInt64.le_of_lt before) reachWalk] at walk
  have blockWalk : (·.root) <$> ((e.world k).state w).getAncestor
      ⟨blockRoot, reach.payloadStatus⟩ first = .ok attestation.data.target.root := by
    rw [← reachRoot, ← Store.getAncestor_root, walk]
    simp [Functor.map, Except.map, rooted]
  obtain ⟨targetBlock, targetFound, -⟩ := Store.getAncestor_le walk
  rw [rooted] at targetFound
  obtain ⟨base, baseFound, -, -⟩ := reachable.blockStatesFromParents targetFound
  obtain ⟨boundary, boundaryOk, run, keys⟩ := reached.target_run (UInt64.le_of_eq anchorSlot)
    found parentHeld slotsOk firstOk before blockWalk baseFound
  -- The target state reads the same attesters, as the run keeps the committees of the epoch.
  have boundaryLe : first ≤ boundary.slot := by
    unfold lookaheadState at boundaryOk
    split at boundaryOk
    · exact UInt64.le_of_eq (processSlots_slot (mapError_ok_iff.mp boundaryOk)).2.symm
    · simp only [pure, Except.pure, Except.ok.injEq] at boundaryOk
      subst boundaryOk
      exact UInt64.not_lt.mp ‹_›
  have epochNat : (computeEpochAtSlot preset attestation.data.slot).toNat ≤
      (getCurrentEpoch boundary).toNat := by
    rw [← epochEq, getCurrentEpoch_toNat]
    have := UInt64.le_iff_toNat_le.mp boundaryLe
    rw [firstNat] at this
    exact (Nat.le_div_iff_mul_le positive).mpr this
  have recentNat : (getCurrentEpoch advanced).toNat ≤
      (computeEpochAtSlot preset attestation.data.slot).toNat + 1 := by
    rw [← epochEq]
    rcases recent with previous | current
    · rw [previous, getPreviousEpoch_toNat]
      omega
    · rw [current]
      omega
  have epochFits := (computeEpochAtSlot preset attestation.data.slot).toNat_lt
  have attesters := run.getAttestingIndices_eq (attestation := attestation) (by omega)
    (UInt64.le_iff_toNat_le.mpr (by rw [activityFixedEpoch_toNat]; omega)) (by omega)
  have boundaryIndexed : getIndexedAttestation boundary attestation = .ok indexed := by
    rw [← indexedOk]
    simp only [getIndexedAttestation, ← attesters]
  -- The signature checked in the block holds in the target state.
  have frame : Frame advanced checked := (frame_operationsInput started).toFrame.trans site.frame
  obtain ⟨indexed', indexedOk', listed, indexedData, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices (attesters.symm.trans indicesOk)
  have same : indexed' = indexed := Except.ok.inj (indexedOk'.symm.trans boundaryIndexed)
  subst same
  have boundaryValid : isValidIndexedAttestation config checks boundary indexed' = .ok true :=
    isValidIndexedAttestation_of_keys valid (List.prefix_refl _)
      (keys.1.trans frame.pubkeysPrefix) (keys.2.1.symm.trans frame.forkVersions.symm)
      (keys.2.2.symm.trans frame.genesisValidatorsRoot.symm) (fun index inside => by
        rw [listed] at inside
        exact lt_size_of_mem_getActiveValidatorIndices
          (mem_getActiveValidatorIndices_of_getAttestingIndices (attesters.symm.trans indicesOk)
            (by simpa using inside)))
  -- The store reads the attestation in that state.
  have computed : ((e.world k).state w).computeCheckpointState config checks
      attestation.data.target = .ok boundary := by
    unfold Store.computeCheckpointState
    rw [Store.blockState_ok_iff.mpr baseFound]
    simp only [firstOk, Except.mapError, bind, Except.bind]
    exact boundaryOk
  obtain ⟨withTarget, targetState, stored, read⟩ := Store.exists_storeTargetCheckpointState computed
  obtain ⟨base', first', baseFound', firstOk', targetOk⟩ :=
    e.targetState_fixedChecks anchored start honest stored read
  rw [baseFound, Option.some.injEq] at baseFound'
  rw [firstOk, Except.ok.injEq] at firstOk'
  subst baseFound' firstOk'
  rw [boundaryOk, Except.ok.injEq] at targetOk
  subst targetOk
  have reads : ReadsAttestation config checks ((e.world k).state w) attestation indexed' :=
    ⟨withTarget, _, stored, read, boundaryIndexed, boundaryValid⟩
  -- The block's message carries the vote, and the block came before the store's slot.
  refine ⟨.block signed, e.view_subset_sent k w seen, .inl ⟨attestation, message ▸ included,
    _, indexed', reachable, reads, ?_, ?_⟩, ?_⟩
  · rw [listed]
    simpa using member
  · rw [dataEq, indexedData]
  · obtain ⟨current, currentOk, blocks, -⟩ :=
      reached.forwardReachable.slots_le_current slots (UInt64.le_of_eq anchorSlot)
    rw [slotOk, Except.ok.injEq] at currentOk
    subst currentOk
    have := UInt64.le_iff_toNat_le.mp (blocks blockRoot block found)
    rw [dataEq]
    exact UInt64.lt_iff_toNat_lt.mpr (by rw [← blockSlot] at this; omega)

end EthLib.Consensus.Models.Network

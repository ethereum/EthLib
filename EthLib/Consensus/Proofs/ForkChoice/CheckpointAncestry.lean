module

public import EthLib.Consensus.Proofs.DirectSafety.Safety
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
public import EthLib.Consensus.Proofs.ForkChoice.Network

/-!
# Proofs: the ancestry of the checkpoints of a store

A reachable store takes each justified or finalized checkpoint from the anchor or a held state.

The held state gives it directly, or after justification and finalization, as a pull-up.

After the anchor epoch, such a checkpoint names an ancestor of the block of the held state.

It is the latest block of that chain at or before the first slot of the checkpoint's epoch.

The one exception is an anchor state that hashes to the zero root.

The store's finalized checkpoint may be at or before the anchor epoch.

Otherwise it is on its justified chain at the first slot of the finalized epoch.

Failing that, the runs to the two held states of those checkpoints bound the accountable stake.

Or their hashes show a collision or a zero root.

Each viable leaf of the store descends from the finalized block, at every finalized epoch.

[Gasper] §4.1 pairs a block with an epoch.

[Gasper]: https://arxiv.org/abs/2003.03052v3
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-! ## Checkpoint blocks on one chain -/

namespace Store

variable {store : Store preset fork}

/-- A checkpoint block is the root of the chain of a block at the first slot of the epoch. -/
private theorem getCheckpointBlock_ok_iff {root target : Root} {epoch : Epoch} :
    store.getCheckpointBlock root epoch = .ok target ↔ ∃ start,
      computeStartSlotAtEpoch preset epoch = .ok start ∧ store.ancestorRoots root start target := by
  unfold getCheckpointBlock ancestorRoots
  cases computeStartSlotAtEpoch preset epoch with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok start =>
    cases reached : store.getAncestor ⟨root, .pending⟩ start <;>
      simp [reached, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A pending node descends from the pending node of each root on its chain.

Before Gloas the walk keeps the pending status, as each parent is pending then. -/
private theorem isAncestor_of_ancestorRoots (lower : store.ParentsBelow) {root target : Root}
    {slot : Slot} (walk : store.ancestorRoots root slot target) :
    store.isAncestor ⟨root, .pending⟩ ⟨target, .pending⟩ = .ok true := by
  obtain ⟨node, reached, rfl⟩ := walk
  by_cases gloas : .glamsterdam ≤ fork
  · obtain ⟨block, found, le⟩ := getAncestor_le reached
    have stops : store.getAncestor ⟨root, .pending⟩ block.slot = .ok node := by
      rw [getAncestor_trans le reached, getAncestor_of_le found (UInt64.le_refl _)]
    simp [isAncestor_pending gloas, block_ok_iff.mpr found, stops, bind, Except.bind, pure,
      Except.pure]
  · obtain ⟨-, origin, -⟩ := getAncestor_climbs (lower := lower) reached
    obtain ⟨nodeRoot, status⟩ := node
    have pending : status = .pending := by
      rcases origin with same | ⟨_, _, _, _, _, _, parentStatus, _⟩
      · cases same
        rfl
      · exact parentStatus.trans (parentPayloadStatus_of_lt (Nat.lt_of_not_le gloas))
    subst pending
    exact isAncestor_of_getAncestor reached

/-- Two checkpoint blocks of one chain, at ordered epochs, are on one chain themselves.

The earlier block is the ancestor of the later one at the first slot of the earlier epoch. -/
private theorem getCheckpointBlock_of_le (lower : store.ParentsBelow)
    {root early late : Root} {earlyEpoch lateEpoch : Epoch} (ordered : earlyEpoch ≤ lateEpoch)
    (earlyBlock : store.getCheckpointBlock root earlyEpoch = .ok early)
    (lateBlock : store.getCheckpointBlock root lateEpoch = .ok late) :
    store.isAncestor ⟨late, .pending⟩ ⟨early, .pending⟩ = .ok true ∧
      store.getCheckpointBlock late earlyEpoch = .ok early := by
  obtain ⟨startEarly, startedEarly, nodeEarly, walkEarly, rfl⟩ :=
    getCheckpointBlock_ok_iff.mp earlyBlock
  obtain ⟨startLate, startedLate, node, reached, rfl⟩ := getCheckpointBlock_ok_iff.mp lateBlock
  have startLe : startEarly ≤ startLate := by
    rw [computeStartSlotAtEpoch_ok_iff] at startedEarly startedLate
    rw [UInt64.le_iff_toNat_le, startedEarly.2, startedLate.2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp ordered)
  -- The walk to the earlier start can stop at the later block on the way.
  have walk : store.ancestorRoots node.root startEarly nodeEarly.root := by
    have same := getAncestor_root (store := store) node .pending startEarly
    rw [← getAncestor_trans startLe reached, walkEarly] at same
    cases reaching : store.getAncestor ⟨node.root, .pending⟩ startEarly with
    | error e => simp [reaching, Functor.map, Except.map] at same
    | ok other =>
      simp only [reaching, Functor.map, Except.map, Except.ok.injEq] at same
      exact ⟨other, reaching, same.symm⟩
  exact ⟨isAncestor_of_ancestorRoots lower walk,
    getCheckpointBlock_ok_iff.mpr ⟨startEarly, startedEarly, walk⟩⟩

end Store

/-- An epoch after the current epoch of a state starts after the slot of that state. -/
private theorem slot_le_of_getCurrentEpoch_lt {state : BeaconState preset fork} {epoch : Epoch}
    {start : Slot} (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (later : getCurrentEpoch state < epoch)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start) : state.slot ≤ start := by
  have epochLt := UInt64.lt_iff_toNat_lt.mp later
  rw [getCurrentEpoch_toNat] at epochLt
  have next := (Nat.div_lt_iff_lt_mul positive).mp epochLt
  have eq := (mulChecked_ok_iff.mp startOk).2
  exact UInt64.le_iff_toNat_le.mpr (by omega)

/-! ## Runs of the held states -/

/-- A run that extends another hashes the last state of the one it extends. -/
private theorem state_mem_hashObjects_append {config : Config} {checks : SignatureChecks}
    {g x y : ForkedBeaconState preset} (pre : Run config checks g x)
    (tail : Run config checks x y) :
    DirectSafety.HashObject.state x ∈ (pre.append tail).hashObjects :=
  DirectSafety.hashObjects_append_subset pre tail (by
    cases pre with
    | nil => simp [Run.hashObjects]
    | snoc pre step => exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (by simp)))))

/-- Slots of one fork before its next fork extend a run with slot steps.

They add no header. -/
private theorem exists_run_of_advanceSlots {config : Config} {checks : SignatureChecks}
    {g x : ForkedBeaconState preset} {bound : Nat} (pre : Run config checks g x)
    (early : ∀ next ∈ config.nextFork fork,
      bound < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    ∀ (count : Nat) {state after : BeaconState preset fork}
      (tail : Run config checks x ⟨fork, state⟩),
      advanceSlots config checks count state = .ok after → state.slot.toNat + count ≤ bound →
      ∃ next : Run config checks x ⟨fork, after⟩,
        (pre.append next).headers = (pre.append tail).headers
  | 0, state, after, tail, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨tail, rfl⟩
  | count + 1, state, after, tail, computed, within => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, stepOk, rest⟩ := computed
    have slot := advanceSlot_slot stepOk
    have across : advanceSlotAcross config checks ⟨fork, state⟩ = .ok ⟨fork, middle⟩ := by
      rw [advanceSlotAcross_of_before fun next scheduled => by
        have := early next scheduled
        omega, stepOk]
      rfl
    obtain ⟨next, headers⟩ :=
      exists_run_of_advanceSlots pre early count (tail.snoc (.slot across)) rest (by omega)
    exact ⟨next, headers.trans (by simp [Run.append, Run.headers, Step.headers])⟩

/-- Two held blocks whose runs share their headers up to an epoch share its checkpoint block.

The runs extend one run to the anchor, and the epoch starts at or after the anchor block. -/
private theorem getCheckpointBlock_eq_of_checkpointPath {config : Config}
    {checks : SignatureChecks} {store other : Store preset fork}
    {anchorBlock : BeaconBlock preset fork} {g x a b : ForkedBeaconState preset}
    {pre : Run config checks g x} {left : Run config checks x a} {right : Run config checks x b}
    {extraLeft extraRight : List BeaconBlockHeader} {rootLeft rootRight : Root}
    {epoch : Epoch} {start : Slot} {checkpoint : Root}
    (headersLeft : (pre.append left).headers = pre.headers ++ extraLeft)
    (headersRight : (pre.append right).headers = pre.headers ++ extraRight)
    (lastLeft : ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
      store.ancestorRoots rootLeft slot reached ∧
      (((extraLeft.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
          SszType.hashTreeRoot anchorBlock = .ok reached) ∨
        ∃ header, (extraLeft.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
            some header ∧ SszType.hashTreeRoot header = .ok reached))
    (lastRight : ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
      other.ancestorRoots rootRight slot reached ∧
      (((extraRight.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
          SszType.hashTreeRoot anchorBlock = .ok reached) ∨
        ∃ header, (extraRight.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
            some header ∧ SszType.hashTreeRoot header = .ok reached))
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (later : anchorBlock.slot ≤ start)
    (paths : (pre.append left).checkpointPath epoch = (pre.append right).checkpointPath epoch)
    (found : store.getCheckpointBlock rootLeft epoch = .ok checkpoint) :
    other.getCheckpointBlock rootRight epoch = .ok checkpoint := by
  have startEq := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
  -- Past the shared run to the anchor, the two runs have the same headers up to the epoch.
  have same : (extraLeft.filter fun header => header.slot.toNat ≤ start.toNat) =
      extraRight.filter fun header => header.slot.toNat ≤ start.toNat := by
    unfold Run.checkpointPath at paths
    rw [headersLeft, headersRight, List.filter_append, List.filter_append] at paths
    simpa only [startEq] using List.append_cancel_left paths
  obtain ⟨start', startOk', node, walkLeft, rfl⟩ := Store.getCheckpointBlock_ok_iff.mp found
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  obtain ⟨reachedLeft, ⟨node', walkLeft', rfl⟩, casesLeft⟩ := lastLeft start later
  rw [walkLeft, Except.ok.injEq] at walkLeft'
  subst node'
  obtain ⟨reachedRight, walkRight, casesRight⟩ := lastRight start later
  refine Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, ?_⟩
  suffices reachedRight = node.root from this ▸ walkRight
  rw [← same] at casesRight
  rcases casesLeft with ⟨noneLeft, hashLeft⟩ | ⟨header, lastLeft, hashLeft⟩ <;>
    rcases casesRight with ⟨noneRight, hashRight⟩ | ⟨header', lastRight, hashRight⟩
  · exact Except.ok.inj (hashRight.symm.trans hashLeft)
  · rw [noneLeft] at lastRight
    cases lastRight
  · rw [lastLeft] at noneRight
    cases noneRight
  · rw [lastLeft, Option.some.injEq] at lastRight
    subst lastRight
    exact Except.ok.inj (hashRight.symm.trans hashLeft)

/-- A held state follows from the anchor state by a run whose blocks are those of its chain.

Every block of the store was imported with the signature checks of the run.

No upgrade is due at any held slot, so the in-fork transition of the store is a run of steps.

The run adds the headers of the blocks on the chain to the headers of the run to the anchor.

From the slot of the anchor block on, it reaches the last block of the chain at or below the slot.

That block is the anchor block when the chain has no later block at or below the slot. -/
private theorem Store.Reachable.exists_run_of_blockState {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (linked : store.Linked anchorBlock.parentRoot)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    ∃ (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
      (extra : List BeaconBlockHeader),
      (pre.append tail).headers = pre.headers ++ extra ∧
      ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
        store.ancestorRoots root slot reached ∧
        (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
            SszType.hashTreeRoot anchorBlock = .ok reached) ∨
          ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
              some header ∧ SszType.hashTreeRoot header = .ok reached) := by
  obtain ⟨block, found⟩ := reachable.known_of_blockState held
  obtain ⟨post, postOk, anchored, -⟩ := reachable.blockStatesFromParents found
  rw [held, Option.some.injEq] at postOk
  subst post
  by_cases same : block = anchorBlock
  · -- The anchor state ends the run to the anchor, and every later walk stays at its block.
    obtain rfl := anchored same
    subst same
    exact ⟨.nil, [], by simp [Run.append], fun slot later =>
      ⟨root, ⟨_, Store.getAncestor_of_le found later, rfl⟩, .inl ⟨by simp, reachable.root found⟩⟩⟩
  obtain ⟨imports, importsHeld, -, step⟩ := imported found
  rw [held, Option.some.injEq] at importsHeld
  subst imports
  obtain ⟨parent, _, engine, signed, rfl, message, parentHeld, transitioned⟩ := step same
  subst message
  obtain ⟨parentBlock, parentFound, -⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  obtain ⟨tailP, extraP, headersP, lastP⟩ :=
    reachable.exists_run_of_blockState linked imported early pre parentHeld
  have bounds := stateTransition_slot transitioned
  obtain ⟨_, _, _, _, blockOk, _⟩ := stateTransition_ok transitioned
  obtain ⟨bodyRoot, bodyHashed, -⟩ := latestBlockHeader_processBlock blockOk
  have unfolded := transitioned
  simp only [stateTransition, bind_ok_iff] at unfolded
  obtain ⟨advanced, slotsOk, applied⟩ := unfolded
  have advancedSlot := (processSlots_slot slotsOk).2
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨-, -, run⟩ := slotsOk
  have bound : ∀ next ∈ config.nextFork fork,
      signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    fun next scheduled => bounds.2 ▸ early next scheduled held
  -- The slots up to the block extend the run of the parent, and the block step follows.
  obtain ⟨tailA, headersA⟩ := exists_run_of_advanceSlots pre bound _ tailP run
    (by have := UInt64.lt_iff_toNat_lt.mp bounds.1; omega)
  have due : upgradeDue config ⟨fork, advanced⟩ = false :=
    upgradeDue_of_before fun next scheduled => advancedSlot ▸ bound next scheduled
  let header : BeaconBlockHeader := ⟨signed.message.slot, signed.message.proposerIndex,
    signed.message.parentRoot, signed.message.stateRoot, bodyRoot⟩
  have headerOk : DirectSafety.blockHeader signed.message = some header := by
    simp [DirectSafety.blockHeader, bodyHashed, Except.toOption, header]
  have headerRoot : SszType.hashTreeRoot header = .ok root :=
    (BeaconBlock.hashTreeRoot_header bodyHashed).trans (reachable.root found)
  refine ⟨tailA.snoc (.block engine signed due applied), extraP ++ [header], ?_,
    fun slot later => ?_⟩
  · show (pre.append tailA).headers ++ (DirectSafety.blockHeader signed.message).toList = _
    rw [headersA, headersP, headerOk]
    simp
  · by_cases above : signed.message.slot ≤ slot
    · refine ⟨root, ⟨_, Store.getAncestor_of_le found above, rfl⟩, .inr ⟨header, ?_, headerRoot⟩⟩
      have : header.slot.toNat ≤ slot.toNat := UInt64.le_iff_toNat_le.mp above
      simp [List.filter_append, this]
    · obtain ⟨reached, walk, cases⟩ := lastP slot later
      refine ⟨reached, Store.ancestorRoots_of_parent found parentFound lower
        (UInt64.not_le.mp above) walk, ?_⟩
      have : ¬ header.slot.toNat ≤ slot.toNat := fun le =>
        above (UInt64.le_iff_toNat_le.mpr le)
      simpa [List.filter_append, this] using cases
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- A store checkpoint is the anchor checkpoint or a field of a terminal view of a run.

The field is current justification or finality, realized or unrealized in the store.

The run extends the given run to the anchor, with headers describing the held block's chain.

The anchor checkpoint need not be a checkpoint field of the anchor state. -/
theorem Store.Reachable.checkpoint_terminalView {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint)
    (selected : (field = (·.currentJustifiedCheckpoint) ∧
        (checkpoint = store.justifiedCheckpoint ∨
          checkpoint = store.unrealizedJustifiedCheckpoint)) ∨
      (field = (·.finalizedCheckpoint) ∧
        (checkpoint = store.finalizedCheckpoint ∨
          checkpoint = store.unrealizedFinalizedCheckpoint))) :
    (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
      checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
    ∃ (root : Root) (state : BeaconState preset fork)
      (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
      (view : DirectSafety.TerminalView ⟨fork, state⟩),
      store.blockStates[root]? = some state ∧ checkpoint = field view.state ∧
      ∃ extra : List BeaconBlockHeader,
        (pre.append tail).headers = pre.headers ++ extra ∧
        ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
          store.ancestorRoots root slot reached ∧
          (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
              SszType.hashTreeRoot anchorBlock = .ok reached) ∨
            ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
                some header ∧ SszType.hashTreeRoot header = .ok reached) := by
  have origin :
      (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
        checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
      (∃ (root : Root) (state : BeaconState preset fork),
        store.blockStates[root]? = some state ∧ checkpoint = field state) ∨
      ∃ (root : Root) (state pulled : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled := by
    rcases selected with ⟨rfl, selected⟩ | ⟨rfl, selected⟩
    · exact reachable.justified_origins checkpoint selected
    · exact reachable.finalized_origins checkpoint selected
  rcases origin with anchor | origin
  · exact .inl anchor
  · have viewed : ∃ (root : Root) (state : BeaconState preset fork)
        (view : DirectSafety.TerminalView ⟨fork, state⟩),
        store.blockStates[root]? = some state ∧ checkpoint = field view.state := by
      rcases origin with ⟨root, state, held, eq⟩ | ⟨root, state, pulled, held, ok, eq⟩
      · exact ⟨root, state, .realized, held, eq⟩
      · exact ⟨root, state, .pulled pulled ok, held, eq⟩
    obtain ⟨root, state, view, held, eq⟩ := viewed
    obtain ⟨tail, extra, headers, last⟩ := reachable.exists_run_of_blockState
      (reachable.linked_of_unknown anchorSlot unknownParent) imported early pre held
    exact .inr ⟨root, state, tail, view, held, eq, extra, headers, last⟩

/-- One store's finalized checkpoint is early, or on the justified chain of another store.

Otherwise runs to held states of the two stores bound accountable stake, or show hash evidence.

Both stores are reachable from an anchor whose parent neither holds.

The anchor block is at or before the slot of the anchor state, and the preset meets the parameters.

We assume a run from a genesis built from deposits to the anchor state.

We assume that every block of either store was imported with the signature checks of that run.

We assume that no upgrade is due at a held slot, so the stores' transitions are steps of a run.

The first alternative puts the finalized epoch at or before the epoch of the anchor state.

The second puts the finalized checkpoint at the first slot of its epoch on the justified chain.

The third gives the runs from the anchor to the held states of the two fields.

Each field is that of its held state, or of the justification step that fork choice runs on it.

The bound is that of direct accountable safety on the unslashed active stake at the anchor state.

Its drift observes the runs up to one epoch past the justified epoch.

The drift counts from the anchor, so the bound loosens as the justified epoch moves away from it.

We assume a stake floor at the epoch calls of every run from the anchor to a held state.

We assume it too at each held state up to one epoch past the justified epoch, for that step. -/
private theorem Store.Reachable.finalized_ancestor_or_accountable_between {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store earlier : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (reachableEarlier : Store.Reachable config anchorState anchorBlock earlier)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (unknownEarlier : earlier.blocks[anchorBlock.parentRoot]? = none)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (importedEarlier : earlier.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (earlyEarlier : ∀ next ∈ config.nextFork fork,
      ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      earlier.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (ordered : earlier.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch)
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) store.justifiedCheckpoint.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      (getCurrentEpoch state).toNat ≤ store.justifiedCheckpoint.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    earlier.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
    (store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
        ⟨earlier.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock store.justifiedCheckpoint.root
        earlier.finalizedCheckpoint.epoch = .ok earlier.finalizedCheckpoint.root) ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, earlier.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, store.blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = earlier.finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = store.justifiedCheckpoint ∧
      (Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.unslashedKeys anchorState) ≤
        3 * Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.accountableKeys pre left right) +
        2 * max (DirectSafety.derivedDrift store.justifiedCheckpoint.epoch.toNat left)
          (DirectSafety.derivedDrift store.justifiedCheckpoint.epoch.toNat right) ∨
      DirectSafety.HashEvidence ((pre.append left).hashObjects ++
        (pre.append right).hashObjects)) := by
  -- The run from genesis gives the anchor its invariant, and the parameters give the window.
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have lower := reachable.parentsBelow anchorSlot unknownParent
  by_cases atAnchor : earlier.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl atAnchor
  have afterF : getCurrentEpoch anchorState < earlier.finalizedCheckpoint.epoch :=
    UInt64.not_le.mp atAnchor
  have afterJ : getCurrentEpoch anchorState < store.justifiedCheckpoint.epoch :=
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp afterF)
      (UInt64.le_iff_toNat_le.mp ordered))
  -- After the anchor epoch, a field comes from a held state or from the step on it.
  have source {selectedStore : Store preset fork}
      (selectedReachable : Store.Reachable config anchorState anchorBlock selectedStore)
      (unknown : selectedStore.blocks[anchorBlock.parentRoot]? = none)
      (imports : selectedStore.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
      (before : ∀ next ∈ config.nextFork fork,
        ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
        selectedStore.blockStates[root]? = some state →
        state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
      (heldIn : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
        selectedStore.blockStates[root]? = some state →
        earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state)
      (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint)
      (after : getCurrentEpoch anchorState < checkpoint.epoch)
      (selected : (field = (·.currentJustifiedCheckpoint) ∧
          (checkpoint = selectedStore.justifiedCheckpoint ∨
            checkpoint = selectedStore.unrealizedJustifiedCheckpoint)) ∨
        (field = (·.finalizedCheckpoint) ∧
          (checkpoint = selectedStore.finalizedCheckpoint ∨
            checkpoint = selectedStore.unrealizedFinalizedCheckpoint))) :
      ∃ (root : Root) (state : BeaconState preset fork)
        (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
        (view : DirectSafety.TerminalView ⟨fork, state⟩),
        selectedStore.blockStates[root]? = some state ∧ checkpoint = field view.state ∧
        (view.state = state ∨ processJustificationAndFinalization state = .ok view.state) ∧
        view.enough store.justifiedCheckpoint.epoch.toNat ∧
        ∃ extra : List BeaconBlockHeader,
          (pre.append tail).headers = pre.headers ++ extra ∧
          ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
            selectedStore.ancestorRoots root slot reached ∧
            (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
                SszType.hashTreeRoot anchorBlock = .ok reached) ∨
              ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
                  some header ∧ SszType.hashTreeRoot header = .ok reached) := by
    rcases selectedReachable.checkpoint_terminalView anchorSlot unknown imports before pre
        field checkpoint selected with ⟨root, -, rfl⟩ |
      ⟨root, state, tail, view, held, eq, headers⟩
    · exact absurd (UInt64.lt_iff_toNat_lt.mp after) (Nat.lt_irrefl _)
    · cases view with
      | realized => exact ⟨root, state, tail, .realized, held, eq, .inl rfl, trivial, headers⟩
      | pulled pulled ok => exact ⟨root, state, tail, .pulled pulled ok, held, eq, .inr ok,
          (fun horizon later => heldEnough (heldIn held) horizon later), headers⟩
  obtain ⟨rootA, stateA, left, va, heldA, fieldA, selectedA, terminalA,
    extraA, headersA, lastA⟩ :=
    source reachableEarlier unknownEarlier importedEarlier earlyEarlier (fun _ _ h => .inl h)
      (·.finalizedCheckpoint) _ afterF (.inr ⟨rfl, .inl rfl⟩)
  obtain ⟨rootB, stateB, right, vb, heldB, fieldB, selectedB, terminalB,
    extraB, headersB, lastB⟩ :=
    source reachable unknownParent imported early (fun _ _ h => .inr h)
      (·.currentJustifiedCheckpoint) _ afterJ (.inl ⟨rfl, .inl rfl⟩)
  -- Each field of a view is one of the three checkpoints of its held state or of the step on it.
  have member {state : BeaconState preset fork} {view : BeaconState preset fork}
      {checkpoint : Checkpoint}
      (selected : view = state ∨ processJustificationAndFinalization state = .ok view)
      (field : checkpoint = view.currentJustifiedCheckpoint ∨
        checkpoint = view.finalizedCheckpoint) :
      checkpoint ∈ [state.currentJustifiedCheckpoint, state.previousJustifiedCheckpoint,
          state.finalizedCheckpoint] ∨
        ∃ pulled, processJustificationAndFinalization state = .ok pulled ∧
          checkpoint ∈ [pulled.currentJustifiedCheckpoint, pulled.previousJustifiedCheckpoint,
            pulled.finalizedCheckpoint] := by
    rcases selected with rfl | ok
    · exact .inl (by rcases field with rfl | rfl <;> simp)
    · exact .inr ⟨view, ok, by rcases field with rfl | rfl <;> simp⟩
  -- An anchor state that hashes to zero is hash evidence of the run through it.
  have evidence (zero : SszType.hashTreeRoot anchorState = .ok (Vector.replicate 32 0)) :
      DirectSafety.HashEvidence ((pre.append left).hashObjects ++
        (pre.append right).hashObjects) :=
    DirectSafety.hashEvidence_iff.mpr (.inr ⟨_,
      List.mem_append_left _ (state_mem_hashObjects_append pre left),
      by simp [DirectSafety.HashObject.root, zero, Except.toOption]⟩)
  by_cases paths : (pre.append left).checkpointPath earlier.finalizedCheckpoint.epoch =
      (pre.append right).checkpointPath earlier.finalizedCheckpoint.epoch
  · -- Equal paths put the finalized block of the left chain on the justified chain.
    rcases reachableEarlier.getCheckpointBlock_of_blockState sound anchorSlot positive window heldA
        (member selectedA (.inr fieldA)) afterF with ⟨blockA, -⟩ | zero
    · rcases reachable.getCheckpointBlock_of_blockState sound anchorSlot positive window heldB
          (member selectedB (.inl fieldB)) afterJ with ⟨blockB, -⟩ | zero
      · obtain ⟨start, startOk, -⟩ := Store.getCheckpointBlock_ok_iff.mp blockA
        have later : anchorBlock.slot ≤ start :=
          UInt64.le_trans anchorSlot (slot_le_of_getCurrentEpoch_lt positive afterF startOk)
        have blockBF := getCheckpointBlock_eq_of_checkpointPath headersA headersB lastA lastB
          startOk later paths blockA
        exact .inr (.inl (Store.getCheckpointBlock_of_le lower ordered blockBF blockB))
      · exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
          fieldA.symm, fieldB.symm, .inr (evidence zero)⟩)
    · exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
        fieldA.symm, fieldB.symm, .inr (evidence zero)⟩)
  · -- Different paths conflict, and direct accountable safety covers the two views.
    have conflict : DirectSafety.Conflict (pre.append left) (pre.append right)
        va.state.finalizedCheckpoint store.justifiedCheckpoint := by
      rw [← fieldA]
      simpa only [DirectSafety.Conflict, UInt64.min_def, ite_eq_left ordered] using paths
    exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
      fieldA.symm, fieldB.symm, DirectSafety.accountable_safety_justified_terminal pre left right
        va vb parameters genesis store.justifiedCheckpoint (enough (.inl heldA) left)
        (enough (.inr heldB) right) terminalA terminalB (.inr fieldB) (fieldA ▸ ordered) conflict⟩)

/-- The finalized checkpoint of a store is early, or on the chain of its justified checkpoint.

Otherwise two runs to held states of the store bound the accountable stake, or show hash evidence.

The store is reachable from an anchor whose parent it does not hold.

The anchor block is at or before the slot of the anchor state, and the preset meets the parameters.

We assume a run from a genesis built from deposits to the anchor state.

We assume that every block of the store was imported with the signature checks of that run.

We assume that no upgrade is due at a held slot, so the transitions of the store are steps of a run.

The first alternative puts the finalized epoch at or before the epoch of the anchor state.

The second puts the finalized checkpoint at the first slot of its epoch on the justified chain.

The third gives the runs from the anchor to the held states of the two fields.

Each field is that of its held state, or of the justification step that fork choice runs on it.

The bound is that of direct accountable safety on the unslashed active stake at the anchor state.

Its drift observes the runs up to one epoch past the justified epoch.

The drift counts from the anchor, so the bound loosens as the justified epoch moves away from it.

We assume a stake floor at the epoch calls of every run from the anchor to a held state.

We assume it too at each held state up to one epoch past the justified epoch, for that step. -/
theorem Store.Reachable.finalized_ancestor_or_accountable {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) store.justifiedCheckpoint.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      (getCurrentEpoch state).toNat ≤ store.justifiedCheckpoint.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
    (store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
        ⟨store.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock store.justifiedCheckpoint.root
        store.finalizedCheckpoint.epoch = .ok store.finalizedCheckpoint.root) ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, store.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, store.blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = store.finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = store.justifiedCheckpoint ∧
      (Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.unslashedKeys anchorState) ≤
        3 * Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.accountableKeys pre left right) +
        2 * max (DirectSafety.derivedDrift store.justifiedCheckpoint.epoch.toNat left)
          (DirectSafety.derivedDrift store.justifiedCheckpoint.epoch.toNat right) ∨
      DirectSafety.HashEvidence ((pre.append left).hashObjects ++
        (pre.append right).hashObjects)) := by
  exact reachable.finalized_ancestor_or_accountable_between reachable parameters genesis pre
    anchorSlot unknownParent unknownParent imported imported early early
    (Store.Reachable.ordered (DirectSafety.run_justified_separated pre genesis).1 reachable).1.1
    (fun _ _ held => enough (held.elim id id))
    (fun _ _ held => heldEnough (held.elim id id))

/-- In a reachable store, a known block at or below the slot of the anchor block is that block.

Every other known block has a known parent at a lower slot, and none is below the anchor. -/
private theorem Store.Reachable.eq_anchor_of_slot_le {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    {root : Root} {block : BeaconBlock preset fork} (held : store.blocks[root]? = some block)
    (below : block.slot ≤ anchorBlock.slot) : block = anchorBlock := by
  by_contra different
  obtain ⟨_, -, anchorFound⟩ := reachable.anchor_known
  obtain ⟨state, stateHeld, -, provenance⟩ := reachable.blockStatesFromParents held
  obtain ⟨parent, checks, engine, signed, -, message, parentHeld, transition⟩ :=
    provenance different
  obtain ⟨parentBlock, parentFound⟩ := reachable.known_of_blockState parentHeld
  have parentLower := reachable.parentsBelow anchorSlot unknown _ _ _ held parentFound
  have anchorLower := reachable.orphans_le anchorSlot anchorFound unknown parentFound
  have lo := UInt64.le_iff_toNat_le.mp anchorLower
  have hi := UInt64.le_iff_toNat_le.mp below
  have strict := UInt64.lt_iff_toNat_lt.mp parentLower
  omega

theorem Store.Reachable.getCheckpointBlock_anchor {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    {root anchorRoot : Root} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (hashed : SszType.hashTreeRoot anchorBlock = .ok anchorRoot) :
    store.getCheckpointBlock root (getCurrentEpoch anchorState) = .ok anchorRoot := by
  obtain ⟨knownRoot, knownHash, anchorFound⟩ := reachable.anchor_known
  have sameRoot := Except.ok.inj (knownHash.symm.trans hashed)
  subst knownRoot
  have lower := reachable.parentsBelow (UInt64.le_of_eq anchorSlot) unknown
  obtain ⟨node, walk⟩ := Store.getAncestor_ok_of_orphans_le lower
    (fun _ _ held orphan => reachable.orphans_le (UInt64.le_of_eq anchorSlot)
      held orphan anchorFound) (node := ⟨root, .pending⟩) found
  obtain ⟨reached, held, below⟩ := Store.getAncestor_le walk
  have eq := reachable.eq_anchor_of_slot_le (UInt64.le_of_eq anchorSlot) unknown held below
  have rooted : node.root = anchorRoot := by
    have roots := reachable.root held
    rw [eq, hashed, Except.ok.injEq] at roots
    exact roots.symm
  have floor := computeStartSlotAtEpoch_computeEpochAtSlot (preset := preset) anchorState.slot
  have value := (computeStartSlotAtEpoch_ok_iff.mp floor).2
  simp only [computeEpochAtSlot, UInt64.toNat_div] at value
  have rounded := UInt64.le_antisymm
    (UInt64.le_iff_toNat_le.mpr (by rw [value, anchorSlot]; exact Nat.div_mul_le_self _ _))
    (le_computeStartSlotAtEpoch_of_isStartSlotAtEpoch boundary
      (UInt64.le_of_eq anchorSlot) floor)
  rw [rounded] at floor
  exact Store.getCheckpointBlock_ok_iff.mpr ⟨anchorBlock.slot, floor, node, walk, rooted⟩

/-- An ordered earlier finality is on the justified chain, or the two stores give safety evidence.

Both stores start at the same epoch-boundary anchor with a nonzero state root.

The evidence is accountable stake relative to the anchor, or hash evidence of the two runs. -/
theorem Store.Reachable.finalized_prefix_or_accountable {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store earlier : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (reachableEarlier : Store.Reachable config anchorState anchorBlock earlier)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (unknownEarlier : earlier.blocks[anchorBlock.parentRoot]? = none)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (importedEarlier : earlier.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (earlyEarlier : ∀ next ∈ config.nextFork fork,
      ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      earlier.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (ordered : earlier.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch)
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) store.justifiedCheckpoint.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      (getCurrentEpoch state).toNat ≤ store.justifiedCheckpoint.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    store.getCheckpointBlock store.justifiedCheckpoint.root
      earlier.finalizedCheckpoint.epoch = .ok earlier.finalizedCheckpoint.root ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, earlier.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, store.blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = earlier.finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = store.justifiedCheckpoint ∧
      (Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.unslashedKeys anchorState) ≤
        3 * Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.accountableKeys pre left right) +
        2 * max (DirectSafety.derivedDrift store.justifiedCheckpoint.epoch.toNat left)
          (DirectSafety.derivedDrift store.justifiedCheckpoint.epoch.toNat right) ∨
      DirectSafety.HashEvidence ((pre.append left).hashObjects ++
        (pre.append right).hashObjects)) := by
  rcases reachable.finalized_ancestor_or_accountable_between reachableEarlier parameters genesis
      pre (UInt64.le_of_eq anchorSlot) unknownParent unknownEarlier imported importedEarlier
      early earlyEarlier ordered enough heldEnough with atAnchor | ⟨-, read⟩ | evidence
  · have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
    have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
      have := parameters.roots
      omega
    have notZero : SszType.hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0) := by
      rw [reachable.anchorState_root]
      exact fun eq => nonzero (Except.ok.inj eq)
    obtain ⟨epoch, hashed⟩ := reachableEarlier.finalized_eq_anchor_of_epoch_le atAnchor
    have known : store.blocks.contains store.justifiedCheckpoint.root := by
      rcases reachable.checkpoints_known sound (UInt64.le_of_eq anchorSlot) positive window
          (checkpoint := store.justifiedCheckpoint) (by simp) with ⟨-, -, held⟩ |
        ⟨-, held⟩ | zero
      · exact held
      · exact held
      · exact False.elim (notZero zero)
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at known
    obtain ⟨block, found⟩ := Option.isSome_iff_exists.mp known
    exact .inl (epoch ▸ reachable.getCheckpointBlock_anchor anchorSlot boundary unknownParent
      found hashed)
  · exact .inl read
  · exact .inr evidence

/-- A viable leaf of a reachable store descends from the finalized block, genesis epoch included.

Its checkpoint block at the finalized epoch is the finalized block.

The viability check passes at a genesis finalized epoch whatever the root.

Then the finalized checkpoint is the anchor one, and the chain of the leaf ends at the anchor.

The anchor block must not be after the anchor state.

Its parent root must name no known block. -/
theorem Store.Reachable.isViableLeaf_finalized {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    {node : ForkChoiceNode} (viable : store.isViableLeaf config node = .ok true) :
    store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch =
      .ok store.finalizedCheckpoint.root := by
  obtain ⟨checkpointBlock, checkpointOk, genesis | same⟩ :=
    Store.isViableLeaf_checkpointBlock viable
  · obtain ⟨-, hashed⟩ := reachable.finalized_eq_anchor_of_epoch_le
      (UInt64.le_iff_toNat_le.mpr (by simp [genesis, GENESIS_EPOCH]))
    obtain ⟨start, startOk, reachedNode, walk, rfl⟩ :=
      Store.getCheckpointBlock_ok_iff.mp checkpointOk
    -- The walk ends at slot 0, which only the anchor block can hold.
    obtain ⟨reached, held, below⟩ := Store.getAncestor_le walk
    have zero := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
    rw [genesis] at zero
    have atAnchor : reached.slot ≤ anchorBlock.slot := by
      have := UInt64.le_iff_toNat_le.mp below
      exact UInt64.le_iff_toNat_le.mpr (by simp [GENESIS_EPOCH] at zero; omega)
    have roots := reachable.root held
    rw [reachable.eq_anchor_of_slot_le anchorSlot unknownParent held atAnchor, hashed] at roots
    rw [checkpointOk, Except.ok.inj roots]
  · rw [checkpointOk, same]

namespace Models.Network

/-- The earlier finalized checkpoint is on the later justified chain at every honest node.

Otherwise a bounded pair of events gives accountable stake or hash evidence from held states.

The evidence is relative to the anchor.

Three times the accountable stake plus twice the drift covers the unslashed reference stake.

The drift counts from the anchor.

With enough churn since the anchor, the evidence holds with no accountable key. -/
theorem Execution.finalized_prefix_or_accountable {ν κ : Type*} [DecidableEq ν]
    {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {anchor : Store preset fork} {g : ForkedBeaconState preset} {time : ℕ} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor)
    (parameters : DirectSafety.Parameters preset) (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (boundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    (unknown : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
    (bounded : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).justifiedCheckpoint.epoch ≤ horizon)
    (early : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ next ∈ config.nextFork fork, ∀ (root : Root) (state : BeaconState preset fork),
      ((e.world k).state w).blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (enough : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (root : Root) (state : BeaconState preset fork),
      ((e.world k).state w).blockStates[root]? = some state →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
      DirectSafety.EnoughStake (pre.append tail) horizon.toNat)
    (heldEnough : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ∀ (root : Root) (state : BeaconState preset fork),
      ((e.world k).state w).blockStates[root]? = some state →
      (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    (∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root) ∨
    ∃ w ∈ J, ∃ i k, i ≤ k ∧ (e.world k).time ≤ time ∧
      ∃ (stateA stateB : BeaconState preset fork)
        (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
        (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
        (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
        (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
        (∃ rootA : Root, ((e.world i).state w).blockStates[rootA]? = some stateA) ∧
        (∃ rootB : Root, ((e.world k).state w).blockStates[rootB]? = some stateB) ∧
        va.state.finalizedCheckpoint = ((e.world i).state w).finalizedCheckpoint ∧
        vb.state.currentJustifiedCheckpoint = ((e.world k).state w).justifiedCheckpoint ∧
        (Models.stake (DirectSafety.effectiveWeight anchorState)
            (DirectSafety.unslashedKeys anchorState) ≤
          3 * Models.stake (DirectSafety.effectiveWeight anchorState)
            (DirectSafety.accountableKeys pre left right) +
          2 * max
            (DirectSafety.derivedDrift ((e.world k).state w).justifiedCheckpoint.epoch.toNat left)
            (DirectSafety.derivedDrift
              ((e.world k).state w).justifiedCheckpoint.epoch.toNat right) ∨
        DirectSafety.HashEvidence
          ((pre.append left).hashObjects ++ (pre.append right).hashObjects)) := by
  classical
  by_cases family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root
  · exact .inl family
  push Not at family
  obtain ⟨w, honest, i, k, later, inTime, failed⟩ := family
  have earlyTime := (e.monotone_time later).trans inTime
  have forward (n : ℕ) := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) n w honest
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have ordered := UInt64.le_trans (e.checkpointsAdvance_of_le w later).2.epoch_le
    ((forward k).reachable.finalized_le_justified sound)
  have horizonLe := UInt64.le_iff_toNat_le.mp (bounded w honest k inTime)
  have calls ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄
      (held : ((e.world i).state w).blockStates[root]? = some state ∨
        ((e.world k).state w).blockStates[root]? = some state)
      (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) :
      DirectSafety.EnoughStake (pre.append tail)
        ((e.world k).state w).justifiedCheckpoint.epoch.toNat := by
    intro call before
    have upper : (getCurrentEpoch call.cached).toNat ≤ horizon.toNat + 1 := by omega
    rcases held with held | held
    · exact enough w honest i earlyTime root state held tail call upper
    · exact enough w honest k inTime root state held tail call upper
  have terminal ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄
      (held : ((e.world i).state w).blockStates[root]? = some state ∨
        ((e.world k).state w).blockStates[root]? = some state)
      (before : (getCurrentEpoch state).toNat ≤
        ((e.world k).state w).justifiedCheckpoint.epoch.toNat + 1)
      (after : GENESIS_EPOCH + 1 < getCurrentEpoch state) :
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state) := by
    have upper : (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 := by omega
    rcases held with held | held
    · exact heldEnough w honest i earlyTime root state held upper after
    · exact heldEnough w honest k inTime root state held upper after
  have result := (forward k).reachable.finalized_prefix_or_accountable (forward i).reachable
    parameters genesis pre anchorSlot boundary nonzero (unknown w honest k inTime)
    (unknown w honest i earlyTime) (forward k).blockStatesFromParents
    (forward i).blockStatesFromParents (early w honest k inTime)
    (early w honest i earlyTime) ordered calls terminal
  exact .inr ⟨w, honest, i, k, later, inTime, result.resolve_left failed⟩

end Models.Network

end EthLib.Consensus

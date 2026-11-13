module

public import EthLib.Consensus.Proofs.DirectSafety.Safety
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks

/-!
# Proofs: the ancestry of the checkpoints of a store

A reachable store takes each justified or finalized checkpoint from the anchor or a held state.

The held state gives it directly, or after justification and finalization, as a pull-up.

After the anchor epoch, such a checkpoint names an ancestor of the block of the held state.

It is the latest block of that chain at or before the first slot of the checkpoint's epoch.

The one exception is an anchor state that hashes to the zero root.

The store's finalized checkpoint is on its justified chain at the first slot of the finalized epoch.

Otherwise the runs to the two held states of those checkpoints bound the accountable stake.

Or their hashes show a collision or a zero root.

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

/-- Below the slot of a block, the walk from it reaches the roots that its parent's walk reaches. -/
private theorem getAncestor_root_of_parent {root : Root} {slot : Slot}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) (below : slot < block.slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot =
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot := by
  rw [getAncestor_step found (UInt64.not_le.mpr below) parentFound lower]
  exact getAncestor_root _ _ _

/-- A checkpoint block is the root that the walk from a pending node reaches at the epoch start. -/
private theorem getCheckpointBlock_ok_iff {root target : Root} {epoch : Epoch} :
    store.getCheckpointBlock root epoch = .ok target ↔ ∃ start,
      computeStartSlotAtEpoch preset epoch = .ok start ∧
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ start = .ok target := by
  unfold getCheckpointBlock
  cases computeStartSlotAtEpoch preset epoch with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok start =>
    cases store.getAncestor ⟨root, .pending⟩ start <;>
      simp [Except.mapError, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

/-- A pending node descends from the pending node of each root that its walk reaches.

Before Gloas the walk keeps the pending status, as each parent is pending then. -/
private theorem isAncestor_of_getAncestor_root (lower : store.ParentsBelow) {root target : Root}
    {slot : Slot}
    (walk : (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok target) :
    store.isAncestor ⟨root, .pending⟩ ⟨target, .pending⟩ = .ok true := by
  cases reached : store.getAncestor ⟨root, .pending⟩ slot with
  | error e => simp [reached, Functor.map, Except.map] at walk
  | ok node =>
    simp only [reached, Functor.map, Except.map, Except.ok.injEq] at walk
    subst walk
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
  obtain ⟨startEarly, startedEarly, walkEarly⟩ := getCheckpointBlock_ok_iff.mp earlyBlock
  obtain ⟨startLate, startedLate, walkLate⟩ := getCheckpointBlock_ok_iff.mp lateBlock
  have startLe : startEarly ≤ startLate := by
    rw [computeStartSlotAtEpoch_ok_iff] at startedEarly startedLate
    rw [UInt64.le_iff_toNat_le, startedEarly.2, startedLate.2]
    exact Nat.mul_le_mul_right _ (UInt64.le_iff_toNat_le.mp ordered)
  obtain ⟨node, reached, nodeRoot⟩ : ∃ node, store.getAncestor ⟨root, .pending⟩ startLate =
      .ok node ∧ node.root = late := by
    cases reaching : store.getAncestor ⟨root, .pending⟩ startLate <;>
      simp_all [Functor.map, Except.map]
  -- The walk to the earlier start can stop at the later block on the way.
  have walk : (·.root) <$> store.getAncestor ⟨late, .pending⟩ startEarly = .ok early := by
    rw [← nodeRoot, ← getAncestor_root node .pending startEarly,
      ← getAncestor_trans startLe reached]
    exact walkEarly
  exact ⟨isAncestor_of_getAncestor_root lower walk,
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
    DirectSafety.HashObject.state x ∈ (pre.append tail).hashObjects := by
  induction tail with
  | nil =>
    cases pre with
    | nil => simp [Run.append, Run.hashObjects]
    | snoc pre step =>
      exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (by simp))))
  | snoc tail step ih => exact List.mem_append_left _ ih

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
    {checks : SignatureChecks} {store : Store preset fork}
    {anchorBlock : BeaconBlock preset fork} {g x a b : ForkedBeaconState preset}
    {pre : Run config checks g x} {left : Run config checks x a} {right : Run config checks x b}
    {extraLeft extraRight : List BeaconBlockHeader} {rootLeft rootRight : Root}
    {epoch : Epoch} {start : Slot} {checkpoint : Root}
    (headersLeft : (pre.append left).headers = pre.headers ++ extraLeft)
    (headersRight : (pre.append right).headers = pre.headers ++ extraRight)
    (lastLeft : ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
      (·.root) <$> store.getAncestor ⟨rootLeft, .pending⟩ slot = .ok reached ∧
      (((extraLeft.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
          SszType.hashTreeRoot anchorBlock = .ok reached) ∨
        ∃ header, (extraLeft.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
            some header ∧ SszType.hashTreeRoot header = .ok reached))
    (lastRight : ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
      (·.root) <$> store.getAncestor ⟨rootRight, .pending⟩ slot = .ok reached ∧
      (((extraRight.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
          SszType.hashTreeRoot anchorBlock = .ok reached) ∨
        ∃ header, (extraRight.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
            some header ∧ SszType.hashTreeRoot header = .ok reached))
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (later : anchorBlock.slot ≤ start)
    (paths : (pre.append left).checkpointPath epoch = (pre.append right).checkpointPath epoch)
    (found : store.getCheckpointBlock rootLeft epoch = .ok checkpoint) :
    store.getCheckpointBlock rootRight epoch = .ok checkpoint := by
  have startEq := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
  -- Past the shared run to the anchor, the two runs have the same headers up to the epoch.
  have same : (extraLeft.filter fun header => header.slot.toNat ≤ start.toNat) =
      extraRight.filter fun header => header.slot.toNat ≤ start.toNat := by
    unfold Run.checkpointPath at paths
    rw [headersLeft, headersRight, List.filter_append, List.filter_append] at paths
    simpa only [startEq] using List.append_cancel_left paths
  obtain ⟨start', startOk', walkLeft⟩ := Store.getCheckpointBlock_ok_iff.mp found
  rw [startOk, Except.ok.injEq] at startOk'
  subst start'
  obtain ⟨reachedLeft, walkLeft', casesLeft⟩ := lastLeft start later
  rw [walkLeft, Except.ok.injEq] at walkLeft'
  subst reachedLeft
  obtain ⟨reachedRight, walkRight, casesRight⟩ := lastRight start later
  refine Store.getCheckpointBlock_ok_iff.mpr ⟨start, startOk, ?_⟩
  rw [walkRight, Except.ok.injEq]
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

Every block of the store was imported with one set of signature checks.

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
    (imported : ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄
      ⦃state : BeaconState preset fork⦄, store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ (parent : BeaconState preset fork) (engine : ExecutionEngine preset fork)
        (signed : SignedBeaconBlock preset fork), signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
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
        (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok reached ∧
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
    refine ⟨.nil, [], by simp [Run.append], fun slot later =>
      ⟨root, ?_, .inl ⟨by simp, reachable.root found⟩⟩⟩
    rw [Store.getAncestor_of_le found later]
    rfl
  obtain ⟨parent, engine, signed, message, parentHeld, transitioned⟩ :=
    imported found held same
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
    · refine ⟨root, by rw [Store.getAncestor_of_le found above]; rfl, .inr ⟨header, ?_, headerRoot⟩⟩
      have : header.slot.toNat ≤ slot.toNat := UInt64.le_iff_toNat_le.mp above
      simp [List.filter_append, this]
    · rw [Store.getAncestor_root_of_parent found parentFound lower (UInt64.not_le.mp above)]
      obtain ⟨reached, walk, cases⟩ := lastP slot later
      refine ⟨reached, walk, ?_⟩
      have : ¬ header.slot.toNat ≤ slot.toNat := fun le =>
        above (UInt64.le_iff_toNat_le.mpr le)
      simpa [List.filter_append, this] using cases
termination_by state.slot.toNat
decreasing_by
  have bounds := stateTransition_slot transitioned
  rw [bounds.2]
  exact UInt64.lt_iff_toNat_lt.mp bounds.1

/-- The finalized checkpoint of a store is on the chain of its justified checkpoint, or it is early.

Otherwise two runs to held states of the store bound the accountable stake, or show hash evidence.

The store is reachable from an anchor whose parent it does not hold.

A run from a genesis built from deposits reaches the anchor state.

Every block of the store was imported with one set of signature checks.

No upgrade is due at a held slot, so the in-fork transitions of the store are steps of a run.

These hypotheses are sufficient for the proof; they are not claimed to be necessary.

The first alternative puts the finalized epoch at or before the epoch of the anchor state.

The second puts the finalized checkpoint at the first slot of its epoch on the justified chain.

The third gives the runs from the anchor to the held states of the two fields.

Each field is that of its held state, or of the justification step that fork choice runs on it.

The bound is that of direct accountable safety at the anchor state.

Its drift observes the runs up to one epoch past the justified epoch.

The stake floor covers the epoch calls of every run from the anchor to a held state.

It also covers each held state up to one epoch past the justified epoch, for that step. -/
theorem Store.Reachable.finalized_ancestor_or_accountable {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis (config := config) (checks := checks) g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (imported : ∀ ⦃root : Root⦄ ⦃block : BeaconBlock preset fork⦄
      ⦃state : BeaconState preset fork⦄, store.blocks[root]? = some block →
      store.blockStates[root]? = some state → block ≠ anchorBlock →
      ∃ (parent : BeaconState preset fork) (engine : ExecutionEngine preset fork)
        (signed : SignedBeaconBlock preset fork), signed.message = block ∧
        store.blockStates[block.parentRoot]? = some parent ∧
        stateTransition config checks engine parent signed true = .ok state)
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
          (DirectSafety.activeKeys anchorState) ≤
        3 * Models.stake (DirectSafety.effectiveWeight anchorState)
          (DirectSafety.accountableKeys (pre.append left) (pre.append right)
            ⟨fork, anchorState⟩) +
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
  have linked := reachable.linked_of_unknown anchorSlot unknownParent
  have lower := reachable.parentsBelow anchorSlot unknownParent
  have ordered : store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch :=
    (Store.Reachable.ordered sound reachable).1.1
  by_cases atAnchor : store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl atAnchor
  have afterF : getCurrentEpoch anchorState < store.finalizedCheckpoint.epoch :=
    UInt64.not_le.mp atAnchor
  have afterJ : getCurrentEpoch anchorState < store.justifiedCheckpoint.epoch :=
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp afterF)
      (UInt64.le_iff_toNat_le.mp ordered))
  -- After the anchor epoch, a field comes from a held state or from the step on it.
  have source (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint)
      (after : getCurrentEpoch anchorState < checkpoint.epoch)
      (origin : (∃ root, SszType.hashTreeRoot anchorBlock = .ok root ∧
          checkpoint = (⟨getCurrentEpoch anchorState, root⟩ : Checkpoint)) ∨
        (∃ (root : Root) (state : BeaconState preset fork),
          store.blockStates[root]? = some state ∧ checkpoint = field state) ∨
        ∃ (root : Root) (state pulled : BeaconState preset fork),
          store.blockStates[root]? = some state ∧
          processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled) :
      ∃ (root : Root) (state : BeaconState preset fork)
        (view : DirectSafety.TerminalView ⟨fork, state⟩),
        store.blockStates[root]? = some state ∧ checkpoint = field view.state ∧
        (view.state = state ∨ processJustificationAndFinalization state = .ok view.state) ∧
        view.enough store.justifiedCheckpoint.epoch.toNat := by
    rcases origin with ⟨root, -, rfl⟩ | ⟨root, state, held, rfl⟩ |
      ⟨root, state, pulled, held, ok, rfl⟩
    · exact absurd (UInt64.lt_iff_toNat_lt.mp after) (Nat.lt_irrefl _)
    · exact ⟨root, state, .realized, held, rfl, .inl rfl, trivial⟩
    · exact ⟨root, state, .pulled pulled ok, held, rfl, .inr ok,
        fun horizon later => heldEnough held horizon later⟩
  obtain ⟨rootA, stateA, va, heldA, fieldA, selectedA, terminalA⟩ :=
    source (·.finalizedCheckpoint) _ afterF (reachable.finalized_origins _ (.inl rfl))
  obtain ⟨rootB, stateB, vb, heldB, fieldB, selectedB, terminalB⟩ :=
    source (·.currentJustifiedCheckpoint) _ afterJ (reachable.justified_origins _ (.inl rfl))
  -- The runs from the anchor to the two held states.
  obtain ⟨left, extraA, headersA, lastA⟩ :=
    reachable.exists_run_of_blockState linked imported early pre heldA
  obtain ⟨right, extraB, headersB, lastB⟩ :=
    reachable.exists_run_of_blockState linked imported early pre heldB
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
  by_cases paths : (pre.append left).checkpointPath store.finalizedCheckpoint.epoch =
      (pre.append right).checkpointPath store.finalizedCheckpoint.epoch
  · -- Equal paths put the finalized block of the left chain on the justified chain.
    rcases reachable.getCheckpointBlock_of_blockState sound anchorSlot positive window heldA
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
        va vb parameters genesis store.justifiedCheckpoint (enough heldA left)
        (enough heldB right) terminalA terminalB (.inr fieldB) (fieldA ▸ ordered) conflict⟩)

end EthLib.Consensus

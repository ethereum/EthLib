module

public import EthLib.Consensus.Proofs.DirectSafety.Safety
public import EthLib.Consensus.Proofs.ForkChoice.CheckpointBlocks
public import EthLib.Consensus.Proofs.ForkChoice.Network

/-!
# Proofs: the ancestry of the checkpoints of a store

A reachable store takes each justified or finalized checkpoint from the anchor or a held state.

Its finalized checkpoint is at or before the anchor epoch, or on its justified chain.

Otherwise runs to two held states bound the accountable stake, or show hash evidence.

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

/-- Two checkpoint blocks of one chain, at ordered epochs, are on one chain themselves.

The earlier block is the ancestor of the later one at the first slot of the earlier epoch. -/
private theorem getCheckpointBlock_of_le
    {root early late : Root} {earlyEpoch lateEpoch : Epoch} (ordered : earlyEpoch ≤ lateEpoch)
    (earlyBlock : store.getCheckpointBlock root earlyEpoch = .ok early)
    (lateBlock : store.getCheckpointBlock root lateEpoch = .ok late) :
    store.isAncestor ⟨late, .pending⟩ ⟨early, .pending⟩ = .ok true ∧
      store.getCheckpointBlock late earlyEpoch = .ok early := by
  -- The earlier read of the root goes through the later checkpoint.
  have read : store.getCheckpointBlock late earlyEpoch = .ok early :=
    (getCheckpointBlock_trans lateBlock ordered) ▸ earlyBlock
  obtain ⟨_, _, _, _, _, descends⟩ := isAncestor_of_getCheckpointBlock read
  exact ⟨descends, read⟩

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

/-- The headers of two runs in sequence are the headers of each. -/
private theorem Run.headers_append {config : Config} {checks : SignatureChecks}
    {a b c : ForkedBeaconState preset} (pre : Run config checks a b)
    (tail : Run config checks b c) : (pre.append tail).headers = pre.headers ++ tail.headers := by
  induction tail with
  | nil => simp [Run.append, Run.headers]
  | snoc tail step ih => simp [Run.append, Run.headers, ih]

/-- A run with no block step adds no header. -/
private theorem Run.headers_eq_nil {config : Config} {checks : SignatureChecks}
    {a b : ForkedBeaconState preset} (run : Run config checks a b) (none : run.blockCount = 0) :
    run.headers = [] := by
  induction run with
  | nil => rfl
  | snoc pre step ih =>
    cases step with
    | slot ok => simpa [Run.headers, Step.headers] using ih none
    | block => simp [Run.blockCount] at none

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

/-- A block applied to a state extends a run to that state by the block's slots and the block.

No upgrade is due up to the slot of the block, so each of these is a step of the run.

The extended run adds the header of the block, and only that header.

It contains the slot step from each state on the slot walk to the block. -/
private theorem exists_run_of_stateTransition {config : Config} {checks : SignatureChecks}
    {g x : ForkedBeaconState preset} {parent state : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (pre : Run config checks g x) (tailP : Run config checks x ⟨fork, parent⟩)
    (transitioned : stateTransition config checks engine parent signed true = .ok state)
    (early : ∀ next ∈ config.nextFork fork,
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    ∃ tail : Run config checks x ⟨fork, state⟩,
      (pre.append tail).headers =
        (pre.append tailP).headers ++ (DirectSafety.blockHeader signed.message).toList ∧
      ∀ k < signed.message.slot.toNat - parent.slot.toNat, ∀ {mid : BeaconState preset fork},
        advanceSlots config checks k parent = .ok mid →
        ∃ (stepped : ForkedBeaconState preset)
          (across : advanceSlotAcross config checks ⟨fork, mid⟩ = .ok stepped),
          tail.Contains (.slot across) := by
  have bounds := stateTransition_slot transitioned
  -- The slots up to the block extend the run of the parent with no header, and the block follows.
  obtain ⟨advanced, slots, due, applied, none, walk⟩ := run_of_stateTransition transitioned
    fun next scheduled => bounds.2 ▸ early next scheduled
  refine ⟨(tailP.append slots).snoc (.block engine signed due applied), ?_,
    fun k below mid reached => ?_⟩
  · show (pre.append (tailP.append slots)).headers ++
      (DirectSafety.blockHeader signed.message).toList = _
    rw [Run.append_assoc, Run.headers_append, Run.headers_eq_nil slots none, List.append_nil]
  · obtain ⟨stepped, across, member⟩ := walk k below reached
    exact ⟨stepped, across, .earlier ((Run.contains_append tailP slots _).mpr (.inr member)) _⟩

/-- A held state follows from the anchor state by a run, with the store's setting of the checks.

No upgrade is due at any held slot, so the in-fork transition of the store is a run of steps. -/
theorem Store.Reachable.nonempty_run_of_blockState {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) := by
  refine reachable.blockState_induction imported
    (fun _ state => Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩))
    (fun _ _ => ⟨.nil⟩) (fun _ _ _ _ _ _ _ _ held _ ok _ _ transitioned previous => ?_) held
  subst ok
  obtain ⟨tailP⟩ := previous
  obtain ⟨tail, -⟩ := exists_run_of_stateTransition .nil tailP transitioned
    fun next scheduled => early next scheduled held
  exact ⟨tail⟩

/-- A held state follows from the anchor state by a run whose blocks are those of its chain. -/
private theorem Store.Reachable.exists_run_of_blockState {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (linked : store.Linked anchorBlock.parentRoot)
    -- Every block of the store was imported with the signature checks of the run.
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    -- No upgrade is due at any held slot, so the in-fork transition of the store is a run of steps.
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    ∃ (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
      (extra : List BeaconBlockHeader),
      -- The run adds the headers of the blocks on the chain to those of the run to the anchor.
      (pre.append tail).headers = pre.headers ++ extra ∧
      -- Take a slot at or after that of the anchor block.
      --
      -- The run reaches the last block of the chain at or below that slot.
      ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
        store.ancestorRoots root slot reached ∧
        -- That block is the anchor block when the chain has no later block at or below the slot.
        (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
            SszType.hashTreeRoot anchorBlock = .ok reached) ∨
          ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
              some header ∧ SszType.hashTreeRoot header = .ok reached) := by
  refine reachable.blockState_induction imported (fun root state => ∃ (tail : Run config checks
      ⟨fork, anchorState⟩ ⟨fork, state⟩) (extra : List BeaconBlockHeader),
      (pre.append tail).headers = pre.headers ++ extra ∧
      ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
        store.ancestorRoots root slot reached ∧
        (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
            SszType.hashTreeRoot anchorBlock = .ok reached) ∨
          ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
              some header ∧ SszType.hashTreeRoot header = .ok reached))
    (fun root found => ?_) (fun root block parent state _ engine signed found held _ ok message
      parentHeld transitioned previous => ?_) held
  · -- The anchor state ends the run to the anchor, and every later walk stays at its block.
    exact ⟨.nil, [], by simp [Run.append], fun slot later =>
      ⟨root, ⟨_, Store.getAncestor_of_le found later, rfl⟩, .inl ⟨by simp, reachable.root found⟩⟩⟩
  subst ok message
  obtain ⟨parentBlock, parentFound, -⟩ := linked.stateAfter _ _ parentHeld
  have lower := linked.parentsBelow _ _ _ found parentFound
  obtain ⟨tailP, extraP, headersP, lastP⟩ := previous
  obtain ⟨_, _, _, _, blockOk, _⟩ := stateTransition_ok transitioned
  obtain ⟨bodyRoot, bodyHashed, -⟩ := latestBlockHeader_processBlock blockOk
  obtain ⟨tail, headersT, -⟩ :=
    exists_run_of_stateTransition pre tailP transitioned fun next scheduled =>
      early next scheduled held
  let header : BeaconBlockHeader := ⟨signed.message.slot, signed.message.proposerIndex,
    signed.message.parentRoot, signed.message.stateRoot, bodyRoot⟩
  have headerOk : DirectSafety.blockHeader signed.message = some header := by
    simp [DirectSafety.blockHeader, bodyHashed, Except.toOption, header]
  have headerRoot : SszType.hashTreeRoot header = .ok root :=
    (BeaconBlock.hashTreeRoot_header bodyHashed).trans (reachable.root found)
  refine ⟨tail, extraP ++ [header], ?_, fun slot later => ?_⟩
  · rw [headersT, headersP, headerOk]
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
      -- The held state gives the checkpoint in one of two ways.
      rcases origin with ⟨root, state, held, eq⟩ | ⟨root, state, pulled, held, ok, eq⟩
      · -- It gives it directly.
        exact ⟨root, state, .realized, held, eq⟩
      · -- Or it gives it after justification and finalization, as a pull-up.
        exact ⟨root, state, .pulled pulled ok, held, eq⟩
    obtain ⟨root, state, view, held, eq⟩ := viewed
    obtain ⟨tail, extra, headers, last⟩ := reachable.exists_run_of_blockState
      (reachable.linked_of_unknown anchorSlot unknownParent) imported early pre held
    exact .inr ⟨root, state, tail, view, held, eq, extra, headers, last⟩

/-- The keys of the registry of each held state are distinct.

The store imported each block with the signature checks of a run from a genesis built from deposits.

No upgrade is due at a held slot, so the chain of a held state extends that run to the state.

Such a run never gives one key to two validators. -/
theorem Store.ForwardReachableWith.pubkeysDistinct_of_blockState {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset}
    (forward : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩) (genesis : Genesis config checks g)
    {root : Root} {state : BeaconState preset fork}
    (held : store.blockStates[root]? = some state) :
    PubkeysDistinct state := by
  have reachable := forward.reachable
  obtain ⟨tail, -⟩ := reachable.exists_run_of_blockState
    (reachable.linked_of_unknown anchorSlot unknownParent) forward.blockStatesFromParents early
    pre held
  exact (pre.append tail).pubkeysDistinct genesis

/-- With distinct keys, the stake of the active keys is the stake of the active indices.

Each active index names a validator, and no two validators share a key.

So each active key weighs the effective balance of the one validator that has it. -/
theorem stake_activeKeys_eq {fork : Fork} {state : BeaconState preset fork}
    (unique : PubkeysDistinct state) :
    Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state) =
      Models.stake (fun index => balanceAt state index.toNat)
        (getActiveValidatorIndices state (getCurrentEpoch state)).toFinset :=
  DirectSafety.keys_weight state _ unique fun _ member =>
    lt_size_of_mem_getActiveValidatorIndices member

/-- The active indices of a state counted at an epoch boundary carry enough stake. -/
theorem Store.ForwardReachableWith.countedRun_enoughStake {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset} {high : Nat}
    (forward : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (enough : ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
      DirectSafety.EnoughStake (pre.append tail) high)
    (genesis : Genesis config checks g)
    {root childRoot : Root} {base state counted : BeaconState preset fork}
    {child : BeaconBlock preset fork}
    -- The state is on the slot walk from a held state to the slot of a held child block.
    (held : store.blockStates[root]? = some base)
    (childFound : store.blocks[childRoot]? = some child)
    (parent : child.parentRoot = root) (before : state.slot < child.slot)
    (path : state = base ∨ ∃ slot, processSlots config checks base slot = .ok state)
    -- The state is at the last slot of an epoch.
    (boundary : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0)
    -- The state `counted` is the state after caching the slot.
    (countedOk : processSlot state = .ok counted)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch counted)
    (upper : (getCurrentEpoch counted).toNat ≤ high + 1) :
    3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * Models.stake (fun index => balanceAt counted index.toNat)
        (getActiveValidatorIndices counted (getCurrentEpoch counted)).toFinset := by
  have reachable := forward.reachable
  have linked := reachable.linked_of_unknown anchorSlot unknownParent
  have imported := forward.blockStatesFromParents
  -- The child is not the anchor block, whose parent the store does not hold.
  have notAnchor : child ≠ anchorBlock := by
    rintro rfl
    obtain ⟨_, parentFound⟩ := reachable.known_of_blockState held
    rw [← parent, unknownParent] at parentFound
    cases parentFound
  obtain ⟨post, childHeld, -, step⟩ := imported childFound
  obtain ⟨parentState, used, engine, signed, sameChecks, message, parentHeld, transitioned⟩ :=
    step notAnchor
  subst used message
  rw [parent, held, Option.some.injEq] at parentHeld
  subst parentHeld
  obtain ⟨tailP, -⟩ := reachable.exists_run_of_blockState linked imported early pre held
  have bounds := stateTransition_slot transitioned
  have bound : ∀ next ∈ config.nextFork fork,
      signed.message.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    fun next scheduled => bounds.2 ▸ early next scheduled childHeld
  -- The child's state extends the run to the anchor by the slots up to the child and the child.
  obtain ⟨tail, -, slots⟩ :=
    exists_run_of_stateTransition pre tailP transitioned fun next scheduled =>
      early next scheduled childHeld
  -- `state` is on the slot walk from `base` to the block, some count of slots in.
  have onPath : ∃ k, k < signed.message.slot.toNat - base.slot.toNat ∧
      advanceSlots config checks k base = .ok state := by
    have beforeNat := UInt64.lt_iff_toNat_lt.mp before
    rcases path with rfl | ⟨slot, reached⟩
    · exact ⟨0, by omega, rfl⟩
    · have reachedSlot := processSlots_slot reached
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at reached
      obtain ⟨-, -, walk⟩ := reached
      have := UInt64.lt_iff_toNat_lt.mp reachedSlot.1
      have := congrArg UInt64.toNat reachedSlot.2
      rw [← reachedSlot.2] at walk
      exact ⟨_, by omega, walk⟩
  obtain ⟨k, below, reached⟩ := onPath
  -- The slot step from the state is one of the slot steps of that extended run.
  obtain ⟨stepped, across, member⟩ := slots k below reached
  -- No upgrade is due, so the slot step from `state` is the plain slot transition.
  have stateSlot : state.slot.toNat < signed.message.slot.toNat :=
    UInt64.lt_iff_toNat_lt.mp before
  have plain := across
  rw [advanceSlotAcross_of_before fun next scheduled => by
    have := bound next scheduled
    omega] at plain
  cases slotOk : advanceSlot config checks state with
  | error e => simp [slotOk, Except.map] at plain
  | ok slotAfter =>
  obtain ⟨next, cached, epoched, nextSlot, cachedOk, epochOk, -⟩ := advanceSlot_ok slotOk
  rw [countedOk, Except.ok.injEq] at cachedOk
  subst cachedOk
  -- The next slot starts an epoch, so the slot step ran the epoch transition on `counted`.
  --
  -- That transition runs justification on `counted`.
  have starts : next % preset.SLOTS_PER_EPOCH = 0 :=
    UInt64.toNat_inj.mp (by rw [UInt64.toNat_mod, nextSlot]; simpa using boundary)
  simp only [epochIfLast, starts, ↓reduceIte] at epochOk
  obtain ⟨weighed, weighedOk, -⟩ := processEpoch_frame epochOk
  -- So the step is an epoch call of the extended run.
  --
  -- The stake floor at such calls holds at `counted`.
  let call : DirectSafety.EpochCall (pre.append tail) :=
    { before := ⟨fork, state⟩, after := stepped, advanced := across,
      member := (pre.contains_append tail _).mpr (.inr member),
      boundary, cached := counted, weighed, cachedOk := countedOk, weighedOk, later }
  have floor : 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
      2 * Models.stake (DirectSafety.effectiveWeight counted) (DirectSafety.activeKeys counted) :=
    enough childRoot _ childHeld tail call upper
  -- The keys of a run from a genesis built from deposits are distinct.
  --
  -- With distinct keys, the stake of the active keys is that of the active indices.
  have unique := call.pubkeysDistinct genesis
  rwa [stake_activeKeys_eq unique] at floor

/-- After the anchor epoch, a store checkpoint is a field of a terminal view of a held state.

The view is the held state itself, or the justification step that fork choice runs on it.

The run to the held state extends the given run to the anchor.

The step meets the stake floor of the view when the store's held states meet it. -/
private theorem Store.Reachable.terminalView_of_after {config : Config}
    {checks : SignatureChecks} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    {g : ForkedBeaconState preset} {high : Nat}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      (getCurrentEpoch state).toNat ≤ high + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state))
    (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint)
    (after : getCurrentEpoch anchorState < checkpoint.epoch)
    (selected : (field = (·.currentJustifiedCheckpoint) ∧
        (checkpoint = store.justifiedCheckpoint ∨
          checkpoint = store.unrealizedJustifiedCheckpoint)) ∨
      (field = (·.finalizedCheckpoint) ∧
        (checkpoint = store.finalizedCheckpoint ∨
          checkpoint = store.unrealizedFinalizedCheckpoint))) :
    ∃ (root : Root) (state : BeaconState preset fork)
      (tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
      (view : DirectSafety.TerminalView ⟨fork, state⟩),
      store.blockStates[root]? = some state ∧ checkpoint = field view.state ∧
      (view.state = state ∨ processJustificationAndFinalization state = .ok view.state) ∧
      view.enough high ∧
      ∃ extra : List BeaconBlockHeader,
        (pre.append tail).headers = pre.headers ++ extra ∧
        ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
          store.ancestorRoots root slot reached ∧
          (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
              SszType.hashTreeRoot anchorBlock = .ok reached) ∨
            ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
                some header ∧ SszType.hashTreeRoot header = .ok reached) := by
  rcases reachable.checkpoint_terminalView anchorSlot unknown imported early pre
      field checkpoint selected with ⟨root, -, rfl⟩ |
    ⟨root, state, tail, view, held, eq, headers⟩
  · exact absurd (UInt64.lt_iff_toNat_lt.mp after) (Nat.lt_irrefl _)
  · cases view with
    | realized => exact ⟨root, state, tail, .realized, held, eq, .inl rfl, trivial, headers⟩
    | pulled pulled ok => exact ⟨root, state, tail, .pulled pulled ok, held, eq, .inr ok,
        (fun horizon later => heldEnough held horizon later), headers⟩

/-- After the anchor epoch, one store's finalized checkpoint is on a given justified chain.

Otherwise two runs bound the accountable stake, or show hash evidence. -/
private theorem Store.Reachable.finalized_ancestor_or_accountable_of_view {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store earlier : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (reachableEarlier : Store.Reachable config anchorState anchorBlock earlier)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknownEarlier : earlier.blocks[anchorBlock.parentRoot]? = none)
    (importedEarlier : earlier.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (earlyEarlier : ∀ next ∈ config.nextFork fork,
      ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      earlier.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {j : Checkpoint}
    (afterF : getCurrentEpoch anchorState < earlier.finalizedCheckpoint.epoch)
    -- The justified checkpoint `j` is at the finalized epoch or later.
    (ordered : earlier.finalizedCheckpoint.epoch ≤ j.epoch)
    {rootB : Root} {stateB : BeaconState preset fork}
    {right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩}
    {vb : DirectSafety.TerminalView ⟨fork, stateB⟩}
    -- `j` is the current justified field of a terminal view of a held state of another store.
    (heldB : store.blockStates[rootB]? = some stateB)
    (fieldB : j = vb.state.currentJustifiedCheckpoint)
    (selectedB : vb.state = stateB ∨ processJustificationAndFinalization stateB = .ok vb.state)
    (terminalB : vb.enough j.epoch.toNat)
    (pathB : ∃ extra : List BeaconBlockHeader,
      (pre.append right).headers = pre.headers ++ extra ∧
      ∀ slot : Slot, anchorBlock.slot ≤ slot → ∃ reached : Root,
        store.ancestorRoots rootB slot reached ∧
        (((extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? = none ∧
            SszType.hashTreeRoot anchorBlock = .ok reached) ∨
          ∃ header, (extra.filter fun header => header.slot.toNat ≤ slot.toNat).getLast? =
              some header ∧ SszType.hashTreeRoot header = .ok reached))
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) j.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      earlier.blockStates[root]? = some state →
      (getCurrentEpoch state).toNat ≤ j.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    (store.isAncestor ⟨j.root, .pending⟩ ⟨earlier.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock j.root earlier.finalizedCheckpoint.epoch =
        .ok earlier.finalizedCheckpoint.root) ∨
    -- One run goes to the held state of `j`, the other to a held state of the first store.
    ∃ (stateA : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩),
      (∃ rootA : Root, earlier.blockStates[rootA]? = some stateA) ∧
      -- The finalized checkpoint is a field of a terminal view of a held state of the first store.
      va.state.finalizedCheckpoint = earlier.finalizedCheckpoint ∧
      DirectSafety.AccountableOrHashEvidence pre left right j.epoch.toNat := by
  -- The run from genesis gives the anchor its invariant, and the parameters give the window.
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have afterJ : getCurrentEpoch anchorState < j.epoch :=
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp afterF)
      (UInt64.le_iff_toNat_le.mp ordered))
  obtain ⟨extraB, headersB, lastB⟩ := pathB
  obtain ⟨rootA, stateA, left, va, heldA, fieldA, selectedA, terminalA,
    extraA, headersA, lastA⟩ :=
    reachableEarlier.terminalView_of_after anchorSlot unknownEarlier importedEarlier earlyEarlier
      pre heldEnough (·.finalizedCheckpoint) _ afterF (.inr ⟨rfl, .inl rfl⟩)
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
  -- The two runs may take one path to the first slot of the finalized epoch.
  by_cases paths : (pre.append left).checkpointPath earlier.finalizedCheckpoint.epoch =
      (pre.append right).checkpointPath earlier.finalizedCheckpoint.epoch
  · -- Then equal paths put the finalized block of the left chain on the justified chain.
    --
    -- After the anchor epoch, a checkpoint of a held state names an ancestor of its block.
    --
    -- It is the latest block of that chain at or before the first slot of the checkpoint's epoch.
    --
    -- The one exception is an anchor state that hashes to the zero root.
    rcases reachableEarlier.getCheckpointBlock_of_blockState sound anchorSlot positive window heldA
        (member selectedA (.inr fieldA)) afterF with ⟨blockA, -⟩ | zero
    · rcases reachable.getCheckpointBlock_of_blockState sound anchorSlot positive window heldB
          (member selectedB (.inl fieldB)) afterJ with ⟨blockB, -⟩ | zero
      · obtain ⟨start, startOk, -⟩ := Store.getCheckpointBlock_ok_iff.mp blockA
        have later : anchorBlock.slot ≤ start :=
          UInt64.le_trans anchorSlot (slot_le_of_getCurrentEpoch_lt positive afterF startOk)
        have blockBF := getCheckpointBlock_eq_of_checkpointPath headersA headersB lastA lastB
          startOk later paths blockA
        exact .inl (Store.getCheckpointBlock_of_le ordered blockBF blockB)
      · exact .inr ⟨stateA, left, va, ⟨rootA, heldA⟩, fieldA.symm, .inr (evidence zero)⟩
    · exact .inr ⟨stateA, left, va, ⟨rootA, heldA⟩, fieldA.symm, .inr (evidence zero)⟩
  · -- Otherwise the two fields conflict, and direct accountable safety covers the two views.
    --
    -- It bounds the accountable stake.
    have conflict : DirectSafety.Conflict (pre.append left) (pre.append right)
        va.state.finalizedCheckpoint j := by
      rw [← fieldA]
      simpa only [DirectSafety.Conflict, UInt64.min_def, ite_eq_left ordered] using paths
    exact .inr ⟨stateA, left, va, ⟨rootA, heldA⟩, fieldA.symm,
      DirectSafety.accountable_safety_justified_terminal pre left right va vb parameters genesis j
        (enough (.inl heldA) left) (enough (.inr heldB) right) terminalA terminalB (.inr fieldB)
        (fieldA ▸ ordered) conflict⟩


/-- One store's finalized checkpoint is early, or on the justified chain of another store.

Otherwise runs to held states of the two stores bound accountable stake, or show hash evidence.

The bound's drift counts from the anchor, up to one epoch past the justified epoch. -/
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
      DirectSafety.AccountableOrHashEvidence pre left right
        store.justifiedCheckpoint.epoch.toNat := by
  by_cases atAnchor : earlier.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · exact .inl atAnchor
  have afterF : getCurrentEpoch anchorState < earlier.finalizedCheckpoint.epoch :=
    UInt64.not_le.mp atAnchor
  have afterJ : getCurrentEpoch anchorState < store.justifiedCheckpoint.epoch :=
    UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp afterF)
      (UInt64.le_iff_toNat_le.mp ordered))
  -- The justified checkpoint is the field of a view of a held state of the store.
  obtain ⟨rootB, stateB, right, vb, heldB, fieldB, selectedB, terminalB, pathB⟩ :=
    reachable.terminalView_of_after anchorSlot unknownParent imported early pre
      (fun _ _ held => heldEnough (.inr held)) (·.currentJustifiedCheckpoint) _ afterJ
      (.inl ⟨rfl, .inl rfl⟩)
  rcases reachable.finalized_ancestor_or_accountable_of_view reachableEarlier parameters genesis
      pre anchorSlot unknownEarlier importedEarlier earlyEarlier afterF ordered
      heldB fieldB selectedB terminalB pathB enough (fun _ _ held => heldEnough (.inl held)) with
    read | ⟨stateA, left, va, heldA, fieldA, bound⟩
  · exact .inr (.inl read)
  · exact .inr (.inr ⟨stateA, stateB, left, right, va, vb, heldA, ⟨rootB, heldB⟩, fieldA,
      fieldB.symm, bound⟩)

/-- The finalized checkpoint of a store is early, or on the chain of its justified checkpoint.

Otherwise two runs to held states bound the accountable stake, or show hash evidence. -/
theorem Store.Reachable.finalized_ancestor_or_accountable {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} {g : ForkedBeaconState preset}
    -- The store is reachable from an anchor.
    (reachable : Store.Reachable config anchorState anchorBlock store)
    -- The preset meets the parameters.
    (parameters : DirectSafety.Parameters preset)
    -- We assume a run from a genesis built from deposits to the anchor state.
    (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    -- The anchor block is at or before the slot of the anchor state.
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    -- The store does not hold the parent of the anchor.
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    -- We assume that every block of the store was imported with the signature checks of that run.
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    -- We assume that no upgrade is due at a held slot.
    --
    -- So the transitions of the store are steps of a run.
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    -- We assume a stake floor at the epoch calls of every run from the anchor to a held state.
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) store.justifiedCheckpoint.epoch.toNat)
    -- We assume the floor too at each held state up to one epoch past the justified epoch.
    --
    -- The justification step that fork choice runs on such a state needs it.
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      (getCurrentEpoch state).toNat ≤ store.justifiedCheckpoint.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    -- The first alternative puts the finalized epoch at or before the epoch of the anchor state.
    store.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState ∨
    -- The second alternative puts the finalized checkpoint on the justified chain.
    --
    -- It is there at the first slot of its epoch.
    (store.isAncestor ⟨store.justifiedCheckpoint.root, .pending⟩
        ⟨store.finalizedCheckpoint.root, .pending⟩ = .ok true ∧
      store.getCheckpointBlock store.justifiedCheckpoint.root
        store.finalizedCheckpoint.epoch = .ok store.finalizedCheckpoint.root) ∨
    -- The third alternative gives the runs from the anchor to the held states of the two fields.
    --
    -- Each field is that of its held state, or of the justification step run on it by fork choice.
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, store.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, store.blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = store.finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = store.justifiedCheckpoint ∧
      -- The bound is that of direct accountable safety.
      --
      -- It is measured against the unslashed active stake at the anchor state.
      --
      -- Its drift observes the runs up to one epoch past the justified epoch.
      --
      -- The drift counts from the anchor.
      --
      -- So the bound loosens as the justified epoch moves away from the anchor.
      --
      -- Otherwise the hashes of the runs show a collision or a zero root.
      DirectSafety.AccountableOrHashEvidence pre left right
        store.justifiedCheckpoint.epoch.toNat := by
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

/-- One store's finalized checkpoint is on the justified chain of a held state of another store.

Otherwise runs to held states of the two stores give accountable stake or hash evidence. -/
private theorem Store.Reachable.held_finalized_read_or_accountable {config : Config}
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
    {root : Root} {st : BeaconState preset fork} (held : store.blockStates[root]? = some st)
    -- The held state's realized justified checkpoint is after the anchor epoch.
    (after : getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch)
    -- That checkpoint is at the finalized epoch or later.
    (ordered : earlier.finalizedCheckpoint.epoch ≤ st.currentJustifiedCheckpoint.epoch)
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) st.currentJustifiedCheckpoint.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (earlier.blockStates[root]? = some state ∨ store.blockStates[root]? = some state) →
      (getCurrentEpoch state).toNat ≤ st.currentJustifiedCheckpoint.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    store.getCheckpointBlock st.currentJustifiedCheckpoint.root
        earlier.finalizedCheckpoint.epoch = .ok earlier.finalizedCheckpoint.root ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, earlier.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, store.blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = earlier.finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = stateB.currentJustifiedCheckpoint ∧
      earlier.finalizedCheckpoint.epoch ≤ stateB.currentJustifiedCheckpoint.epoch ∧
      store.getCheckpointBlock stateB.currentJustifiedCheckpoint.root
        earlier.finalizedCheckpoint.epoch ≠ .ok earlier.finalizedCheckpoint.root ∧
      DirectSafety.AccountableOrHashEvidence pre left right
        stateB.currentJustifiedCheckpoint.epoch.toNat := by
  by_cases readOk : store.getCheckpointBlock st.currentJustifiedCheckpoint.root
      earlier.finalizedCheckpoint.epoch = .ok earlier.finalizedCheckpoint.root
  · exact .inl readOk
  by_cases atAnchor : earlier.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState
  · -- At or before the anchor epoch, the finalized checkpoint is the anchor's.
    --
    -- The justified root is a known block.
    have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
    have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
    have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
      have := parameters.roots
      omega
    have notZero : SszType.hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0) := by
      rw [reachable.anchorState_root]
      exact fun eq => nonzero (Except.ok.inj eq)
    obtain ⟨epoch, hashed⟩ := reachableEarlier.finalized_eq_anchor_of_epoch_le atAnchor
    rcases reachable.getCheckpointBlock_of_blockState sound (UInt64.le_of_eq anchorSlot) positive
        window held (.inl (by simp)) after with ⟨-, known⟩ | zero
    · rw [Std.TreeMap.contains_eq_isSome_getElem?] at known
      obtain ⟨block, found⟩ := Option.isSome_iff_exists.mp known
      -- Every known block reads the anchor's checkpoint at the anchor epoch.
      exact .inl (epoch ▸ reachable.getCheckpointBlock_anchor anchorSlot boundary unknownParent
        found hashed)
    · exact absurd zero notZero
  · -- After the anchor epoch, the justified side is the held state itself.
    --
    -- The held state is a realized view on its run from the anchor.
    obtain ⟨tail, path⟩ := reachable.exists_run_of_blockState
      (reachable.linked_of_unknown (UInt64.le_of_eq anchorSlot) unknownParent) imported early pre
      held
    rcases reachable.finalized_ancestor_or_accountable_of_view reachableEarlier parameters genesis
        pre (UInt64.le_of_eq anchorSlot) unknownEarlier importedEarlier earlyEarlier
        (UInt64.not_le.mp atAnchor) ordered (vb := .realized) held rfl (.inl rfl) trivial path
        enough (fun _ _ found => heldEnough (.inl found)) with
      ⟨-, read⟩ | ⟨stateA, left, va, heldA, fieldA, bound⟩
    · exact .inl read
    · exact .inr ⟨stateA, st, left, tail, va, .realized, heldA, ⟨root, held⟩, fieldA, rfl,
        ordered, readOk, bound⟩

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
      DirectSafety.AccountableOrHashEvidence pre left right
        store.justifiedCheckpoint.epoch.toNat := by
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

/-- Two stores' justified checkpoints of one epoch are equal, or the two stores give evidence.

Each checkpoint is the justified or unrealized justified checkpoint of its store.

The evidence is runs to held states that bound accountable stake, or hash evidence. -/
theorem Store.Reachable.justified_eq_or_accountable {config : Config}
    {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store other : Store preset fork} {g : ForkedBeaconState preset}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (reachableOther : Store.Reachable config anchorState anchorBlock other)
    (parameters : DirectSafety.Parameters preset)
    (genesis : Genesis config checks g)
    (pre : Run config checks g ⟨fork, anchorState⟩)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    (unknownOther : other.blocks[anchorBlock.parentRoot]? = none)
    (imported : store.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (importedOther : other.BlockStatesFromParents config (· = checks) anchorState anchorBlock)
    (early : ∀ next ∈ config.nextFork fork, ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      store.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (earlyOther : ∀ next ∈ config.nextFork fork,
      ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      other.blockStates[root]? = some state →
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {first second : Checkpoint}
    (selectedFirst : first = store.justifiedCheckpoint ∨
      first = store.unrealizedJustifiedCheckpoint)
    (selectedSecond : second = other.justifiedCheckpoint ∨
      second = other.unrealizedJustifiedCheckpoint)
    (epoch : first.epoch = second.epoch)
    (enough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (store.blockStates[root]? = some state ∨ other.blockStates[root]? = some state) →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) first.epoch.toNat)
    (heldEnough : ∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (store.blockStates[root]? = some state ∨ other.blockStates[root]? = some state) →
      (getCurrentEpoch state).toNat ≤ first.epoch.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) :
    first = second ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, store.blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, other.blockStates[rootB]? = some stateB) ∧
      va.state.currentJustifiedCheckpoint = first ∧
      vb.state.currentJustifiedCheckpoint = second ∧
      DirectSafety.AccountableOrHashEvidence pre left right first.epoch.toNat := by
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by have := parameters.slots; omega
  have window : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    have := parameters.roots
    omega
  have notZero : SszType.hashTreeRoot anchorState ≠ .ok (Vector.replicate 32 0) := by
    rw [reachable.anchorState_root]
    exact fun eq => nonzero (Except.ok.inj eq)
  -- Each checkpoint is the anchor checkpoint at the anchor epoch, or after that epoch.
  have known {selected : Store preset fork}
      (selectedReachable : Store.Reachable config anchorState anchorBlock selected)
      {checkpoint : Checkpoint}
      (member : checkpoint = selected.justifiedCheckpoint ∨
        checkpoint = selected.unrealizedJustifiedCheckpoint) :
      (checkpoint.epoch = getCurrentEpoch anchorState ∧
          SszType.hashTreeRoot anchorBlock = .ok checkpoint.root) ∨
        getCurrentEpoch anchorState < checkpoint.epoch := by
    rcases selectedReachable.checkpoints_known sound (UInt64.le_of_eq anchorSlot) positive window
        (checkpoint := checkpoint) (by rcases member with rfl | rfl <;> simp) with
      ⟨same, hashed, -⟩ | ⟨later, -⟩ | zero
    · exact .inl ⟨same, hashed⟩
    · exact .inr later
    · exact absurd zero notZero
  rcases known reachable selectedFirst with ⟨sameA, hashedA⟩ | afterA <;>
    rcases known reachableOther selectedSecond with ⟨sameB, hashedB⟩ | afterB
  · exact .inl (by
      cases first
      cases second
      simp only at sameA sameB hashedA hashedB
      rw [hashedA, Except.ok.injEq] at hashedB
      rw [sameA, sameB, hashedB])
  · rw [← epoch, sameA] at afterB
    exact absurd afterB (UInt64.lt_irrefl _)
  · rw [epoch, sameB] at afterA
    exact absurd afterA (UInt64.lt_irrefl _)
  -- After the anchor epoch, each checkpoint is a field of a view, and the views agree or conflict.
  obtain ⟨rootA, stateA, left, va, heldA, fieldA, -, terminalA, -⟩ :=
    reachable.terminalView_of_after (UInt64.le_of_eq anchorSlot) unknownParent imported early
      pre (fun _ _ held => heldEnough (.inl held)) (·.currentJustifiedCheckpoint) first afterA
      (.inl ⟨rfl, selectedFirst⟩)
  obtain ⟨rootB, stateB, right, vb, heldB, fieldB, -, terminalB, -⟩ :=
    reachableOther.terminalView_of_after (UInt64.le_of_eq anchorSlot) unknownOther
      importedOther earlyOther pre (fun _ _ held => heldEnough (.inr held))
      (·.currentJustifiedCheckpoint) second afterB (.inl ⟨rfl, selectedSecond⟩)
  -- The anchor state ends before the first slot of the common epoch.
  have starts : anchorState.slot.toNat ≤ first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    have epochLt := UInt64.lt_iff_toNat_lt.mp afterA
    rw [getCurrentEpoch_toNat] at epochLt
    exact Nat.le_of_lt ((Nat.div_lt_iff_lt_mul positive).mp epochLt)
  rcases DirectSafety.accountable_justified_unique_terminal pre left right va vb parameters
      genesis first second (enough (.inl heldA) left) (enough (.inr heldB) right) terminalA
      terminalB (.inr fieldA) (.inr fieldB) epoch starts with
    same | bound
  · exact .inl same
  · exact .inr ⟨stateA, stateB, left, right, va, vb, ⟨rootA, heldA⟩, ⟨rootB, heldB⟩,
      fieldA.symm, fieldB.symm, bound⟩

/-- A viable leaf of a reachable store descends from the finalized block, genesis epoch included.

Its checkpoint block at the finalized epoch is the finalized block. -/
theorem Store.Reachable.isViableLeaf_finalized {config : Config}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    -- The anchor block is not after the anchor state.
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    -- The parent root of the anchor block names no known block.
    (unknownParent : store.blocks[anchorBlock.parentRoot]? = none)
    {node : ForkChoiceNode} (viable : store.isViableLeaf config node = .ok true) :
    store.getCheckpointBlock node.root store.finalizedCheckpoint.epoch =
      .ok store.finalizedCheckpoint.root := by
  obtain ⟨checkpointBlock, checkpointOk, genesis | same⟩ :=
    Store.isViableLeaf_checkpointBlock viable
  · -- The viability check passes at a genesis finalized epoch whatever the root.
    --
    -- Then the finalized checkpoint is the anchor one.
    --
    -- The chain of the leaf ends at the anchor.
    obtain ⟨-, hashed⟩ := reachable.finalized_eq_anchor_of_epoch_le
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

/-- The stake floors of the held states of two honest stores, read at an epoch up to the horizon.

The floors are assumed for every honest store by the time, at the horizon.

At an earlier epoch they are the same floors over fewer epoch calls. -/
private theorem Execution.held_floors {ν κ : Type*} [DecidableEq ν]
    {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : Message preset fork → Set (ν × κ)}
    {sends : ν → ℕ → Set (Message preset fork) → Store preset fork → Message preset fork → Prop}
    {J : Set ν} (e : Execution (forkChoice config checks sources signed sends) J)
    {anchorState : BeaconState preset fork} {g : ForkedBeaconState preset} {time : ℕ}
    {horizon high : Epoch} {pre : Run config checks g ⟨fork, anchorState⟩}
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
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state))
    {a b : ν} (honestA : a ∈ J) (honestB : b ∈ J) {i j : ℕ}
    (timeA : (e.world i).time ≤ time) (timeB : (e.world j).time ≤ time)
    (le : high ≤ horizon) :
    (∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (((e.world i).state a).blockStates[root]? = some state ∨
        ((e.world j).state b).blockStates[root]? = some state) →
      ∀ tail : Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩,
        DirectSafety.EnoughStake (pre.append tail) high.toNat) ∧
    (∀ ⦃root : Root⦄ ⦃state : BeaconState preset fork⦄,
      (((e.world i).state a).blockStates[root]? = some state ∨
        ((e.world j).state b).blockStates[root]? = some state) →
      (getCurrentEpoch state).toNat ≤ high.toNat + 1 →
      GENESIS_EPOCH + 1 < getCurrentEpoch state →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state)) := by
  have below := UInt64.le_iff_toNat_le.mp le
  constructor
  · intro root state held tail call before
    have upper : (getCurrentEpoch call.cached).toNat ≤ horizon.toNat + 1 := by omega
    rcases held with held | held
    · exact enough a honestA i timeA root state held tail call upper
    · exact enough b honestB j timeB root state held tail call upper
  · intro root state held before after
    have upper : (getCurrentEpoch state).toNat ≤ horizon.toNat + 1 := by omega
    rcases held with held | held
    · exact heldEnough a honestA i timeA root state held upper after
    · exact heldEnough b honestB j timeB root state held upper after

/-- One honest node's finalized checkpoint is on another's justified chain, or there is evidence. -/
theorem Execution.finalized_read_or_accountable {ν κ : Type*} [DecidableEq ν]
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
    -- Every honest justified epoch is at most the horizon.
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
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state))
    {a b : ν} (honestA : a ∈ J) (honestB : b ∈ J) {i j : ℕ}
    -- Both nodes are at events by the time.
    (timeA : (e.world i).time ≤ time) (timeB : (e.world j).time ≤ time)
    -- The second node's justified epoch is at or after the first node's finalized epoch.
    (ordered : ((e.world i).state a).finalizedCheckpoint.epoch ≤
      ((e.world j).state b).justifiedCheckpoint.epoch) :
    ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
      .ok ((e.world i).state a).finalizedCheckpoint.root ∨
    ((e.world i).state a).finalizedCheckpoint.epoch ≤
        ((e.world j).state b).justifiedCheckpoint.epoch ∧
      -- Otherwise the second justified root does not read the first finalized root at that epoch.
      ((e.world j).state b).getCheckpointBlock ((e.world j).state b).justifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch ≠
          .ok ((e.world i).state a).finalizedCheckpoint.root ∧
      -- The evidence gives runs from the anchor to held states of the two stores.
      --
      -- It also gives terminal views of those states.
      ∃ (stateA stateB : BeaconState preset fork)
        (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
        (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
        (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
        (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
        (∃ rootA : Root, ((e.world i).state a).blockStates[rootA]? = some stateA) ∧
        (∃ rootB : Root, ((e.world j).state b).blockStates[rootB]? = some stateB) ∧
        -- A view of the first store holds the finalized checkpoint.
        va.state.finalizedCheckpoint = ((e.world i).state a).finalizedCheckpoint ∧
        -- A view of the second store holds the justified checkpoint.
        vb.state.currentJustifiedCheckpoint = ((e.world j).state b).justifiedCheckpoint ∧
        -- The evidence is the direct-safety evidence on those runs.
        --
        -- Its drift counts from the anchor.
        DirectSafety.AccountableOrHashEvidence pre left right
          ((e.world j).state b).justifiedCheckpoint.epoch.toNat := by
  by_cases readOk : ((e.world j).state b).getCheckpointBlock
      ((e.world j).state b).justifiedCheckpoint.root
      ((e.world i).state a).finalizedCheckpoint.epoch =
        .ok ((e.world i).state a).finalizedCheckpoint.root
  · exact .inl readOk
  have forward (n : ℕ) (w : ν) (honest : w ∈ J) := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) n w honest
  obtain ⟨calls, terminal⟩ := e.held_floors enough heldEnough honestA honestB timeA timeB
    (bounded b honestB j timeB)
  rcases (forward j b honestB).reachable.finalized_prefix_or_accountable
      (forward i a honestA).reachable parameters genesis pre anchorSlot boundary nonzero
      (unknown b honestB j timeB) (unknown a honestA i timeA)
      (forward j b honestB).blockStatesFromParents (forward i a honestA).blockStatesFromParents
      (early b honestB j timeB) (early a honestA i timeA) ordered calls terminal with
    read | ⟨stateA, stateB, left, right, va, vb, heldA, heldB, fieldA, fieldB, evidence⟩
  · exact absurd read readOk
  · exact .inr ⟨ordered, readOk, stateA, stateB, left, right, va, vb, heldA, heldB, fieldA, fieldB,
      evidence⟩

/-- The earlier finalized checkpoint is on the later justified chain at every honest node.

Otherwise a bounded pair of events gives accountable stake or hash evidence from held states. -/
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
      ((e.world i).state w).finalizedCheckpoint.epoch ≤
        ((e.world k).state w).justifiedCheckpoint.epoch ∧
      -- At those events the later justified root does not read the earlier finalized root.
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch ≠
          .ok ((e.world i).state w).finalizedCheckpoint.root ∧
      ∃ (stateA stateB : BeaconState preset fork)
        (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
        (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
        (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
        (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
        (∃ rootA : Root, ((e.world i).state w).blockStates[rootA]? = some stateA) ∧
        (∃ rootB : Root, ((e.world k).state w).blockStates[rootB]? = some stateB) ∧
        va.state.finalizedCheckpoint = ((e.world i).state w).finalizedCheckpoint ∧
        vb.state.currentJustifiedCheckpoint = ((e.world k).state w).justifiedCheckpoint ∧
        -- The evidence is relative to the anchor.
        --
        -- Three times the accountable stake plus twice the drift covers the unslashed stake.
        --
        -- That stake is the reference stake.
        --
        -- The drift counts from the anchor.
        --
        -- With enough churn since the anchor, the evidence holds with no accountable key.
        DirectSafety.AccountableOrHashEvidence pre left right
          ((e.world k).state w).justifiedCheckpoint.epoch.toNat := by
  classical
  by_cases family : ∀ w ∈ J, ∀ i k, i ≤ k → (e.world k).time ≤ time →
      ((e.world k).state w).getCheckpointBlock ((e.world k).state w).justifiedCheckpoint.root
        ((e.world i).state w).finalizedCheckpoint.epoch =
          .ok ((e.world i).state w).finalizedCheckpoint.root
  · exact .inl family
  push Not at family
  obtain ⟨w, honest, i, k, later, inTime, failed⟩ := family
  have earlyTime := (e.monotone_time later).trans inTime
  have forward := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  have sound : Invariant anchorState := (DirectSafety.run_justified_separated pre genesis).1
  have ordered := UInt64.le_trans (e.checkpointsAdvance_of_le w later).2.epoch_le
    (forward.reachable.finalized_le_justified sound)
  rcases e.finalized_read_or_accountable anchored start parameters genesis pre anchorSlot boundary
      nonzero unknown bounded early enough heldEnough honest honest earlyTime inTime ordered with
    read | ⟨-, -, evidence⟩
  · exact absurd read failed
  · exact .inr ⟨w, honest, i, k, later, inTime, ordered, failed, evidence⟩

/-- Justified checkpoints of one epoch agree at honest nodes, or two held states give evidence. -/
theorem Execution.justified_eq_or_accountable {ν κ : Type*} [DecidableEq ν]
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
    (nonzero : anchorBlock.stateRoot ≠ Vector.replicate 32 0)
    (unknown : ∀ w ∈ J, ∀ k, (e.world k).time ≤ time →
      ((e.world k).state w).blocks[anchorBlock.parentRoot]? = none)
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
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state))
    {a b : ν} (honestA : a ∈ J) (honestB : b ∈ J) {i j : ℕ}
    (timeA : (e.world i).time ≤ time) (timeB : (e.world j).time ≤ time)
    {first second : Checkpoint}
    -- Each checkpoint is the justified or unrealized justified one of an honest node's store.
    (selectedFirst : first = ((e.world i).state a).justifiedCheckpoint ∨
      first = ((e.world i).state a).unrealizedJustifiedCheckpoint)
    (selectedSecond : second = ((e.world j).state b).justifiedCheckpoint ∨
      second = ((e.world j).state b).unrealizedJustifiedCheckpoint)
    -- The common epoch is at most the horizon of the stake floors.
    (epoch : first.epoch = second.epoch) (inHorizon : first.epoch ≤ horizon) :
    first = second ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, ((e.world i).state a).blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, ((e.world j).state b).blockStates[rootB]? = some stateB) ∧
      va.state.currentJustifiedCheckpoint = first ∧
      vb.state.currentJustifiedCheckpoint = second ∧
      -- The evidence is relative to the anchor.
      --
      -- Three times the accountable stake plus twice the drift covers the unslashed stake.
      --
      -- That stake is the reference stake.
      --
      -- The drift counts from the anchor, up to one epoch past the common epoch.
      DirectSafety.AccountableOrHashEvidence pre left right first.epoch.toNat := by
  have forward (n : ℕ) (w : ν) (honest : w ∈ J) := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) n w honest
  obtain ⟨calls, terminal⟩ := e.held_floors enough heldEnough honestA honestB timeA timeB
    inHorizon
  exact (forward i a honestA).reachable.justified_eq_or_accountable
    (forward j b honestB).reachable parameters genesis pre anchorSlot nonzero
    (unknown a honestA i timeA) (unknown b honestB j timeB)
    (forward i a honestA).blockStatesFromParents (forward j b honestB).blockStatesFromParents
    (early a honestA i timeA) (early b honestB j timeB) selectedFirst selectedSecond epoch
    calls terminal

/-- One honest node's finalized checkpoint is on the justified chain of another's held state.

Otherwise runs from the anchor to held states of the two stores give evidence. -/
theorem Execution.held_finalized_read_or_accountable {ν κ : Type*} [DecidableEq ν]
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
        2 * Models.stake (DirectSafety.effectiveWeight state) (DirectSafety.activeKeys state))
    {a b : ν} (honestA : a ∈ J) (honestB : b ∈ J) {i j : ℕ}
    -- Both nodes are at events by the time.
    (timeA : (e.world i).time ≤ time) (timeB : (e.world j).time ≤ time)
    {root : Root} {st : BeaconState preset fork}
    (held : ((e.world j).state b).blockStates[root]? = some st)
    -- The held state's realized justified checkpoint is after the anchor epoch.
    (after : getCurrentEpoch anchorState < st.currentJustifiedCheckpoint.epoch)
    -- That checkpoint is at the finalized epoch or later.
    (ordered : ((e.world i).state a).finalizedCheckpoint.epoch ≤
      st.currentJustifiedCheckpoint.epoch)
    -- That checkpoint is at most the horizon of the stake floors.
    (inHorizon : st.currentJustifiedCheckpoint.epoch ≤ horizon) :
    ((e.world j).state b).getCheckpointBlock st.currentJustifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch =
      .ok ((e.world i).state a).finalizedCheckpoint.root ∨
    ∃ (stateA stateB : BeaconState preset fork)
      (left : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateA⟩)
      (right : Run config checks ⟨fork, anchorState⟩ ⟨fork, stateB⟩)
      (va : DirectSafety.TerminalView ⟨fork, stateA⟩)
      (vb : DirectSafety.TerminalView ⟨fork, stateB⟩),
      (∃ rootA : Root, ((e.world i).state a).blockStates[rootA]? = some stateA) ∧
      (∃ rootB : Root, ((e.world j).state b).blockStates[rootB]? = some stateB) ∧
      va.state.finalizedCheckpoint = ((e.world i).state a).finalizedCheckpoint ∧
      vb.state.currentJustifiedCheckpoint = stateB.currentJustifiedCheckpoint ∧
      ((e.world i).state a).finalizedCheckpoint.epoch ≤ stateB.currentJustifiedCheckpoint.epoch ∧
      ((e.world j).state b).getCheckpointBlock stateB.currentJustifiedCheckpoint.root
        ((e.world i).state a).finalizedCheckpoint.epoch ≠
          .ok ((e.world i).state a).finalizedCheckpoint.root ∧
      -- Three times the accountable stake plus twice the drift covers the unslashed stake.
      --
      -- That stake is the reference stake.
      --
      -- The drift counts from the anchor, up to one epoch past the held justified epoch.
      DirectSafety.AccountableOrHashEvidence pre left right
        stateB.currentJustifiedCheckpoint.epoch.toNat := by
  have forward (n : ℕ) (w : ν) (honest : w ∈ J) := e.forwardReachableWith
    (fun u hu => (start u hu) ▸ Store.ForwardReachableWith.anchor anchored) n w honest
  obtain ⟨calls, terminal⟩ := e.held_floors enough heldEnough honestA honestB timeA timeB
    inHorizon
  exact (forward j b honestB).reachable.held_finalized_read_or_accountable
    (forward i a honestA).reachable parameters genesis pre anchorSlot boundary nonzero
    (unknown b honestB j timeB) (unknown a honestA i timeA)
    (forward j b honestB).blockStatesFromParents (forward i a honestA).blockStatesFromParents
    (early b honestB j timeB) (early a honestA i timeA) held after ordered calls terminal

end Models.Network

end EthLib.Consensus

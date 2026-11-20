module

public import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Indicators
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.EffectiveFall
import EthLib.Consensus.Proofs.ForkChoice.CheckpointAncestry
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalCoverage
public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.Trace
public import EthLib.Consensus.Proofs.Transition.Upgrade
public import EthLib.Consensus.Proofs.Transition.ValidatorCaps

/-!
# The runs behind the quorum drift of a fast-confirmation call

A call of the fast confirmation rule reads the pulled-up head state of an honest store.

A later state that counts the call's target is on the chain of a block of another honest store.

The drift bound takes runs from one boundary state at the start of the target's epoch.

This file builds those runs from the stores, and so bounds the drift of every call.

The boundary state is right after the epoch transition, so the bands of hysteresis hold there.

At most the target block lies between the boundary state and a middle state at the same slot.

The middle state holds the queue of pending partial withdrawals of the target block.

From the middle state, one run reaches the pulled-up head state and another the later state.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- A run from genesis passes a boundary state at the start of the epoch of its last state.

The boundary state is after the epoch transition and the upgrades of the first slot of that epoch.

Only blocks at that slot lead from the boundary state to the last state.

The bands of hysteresis hold at the boundary state.

Genesis is before Altair and the last state is at Fulu or later, so the run has a slot step.

The epoch transition of that step sets the bands.

An upgrade keeps them, since every effective balance is at most its cap.

A last state at the first slot of an epoch has the boundary state at its own slot.

Any other state is in the epoch of the state before its last step, at the same fork. -/
private theorem run_boundaryEpoch {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset) :
    ∀ {x : ForkedBeaconState preset}, Run config checks g x → x.fork < .glamsterdam →
      .fusaka ≤ x.fork →
      ∃ boundary : BeaconState preset x.fork,
        (x.state.slot % preset.SLOTS_PER_EPOCH = 0 → boundary.slot = x.state.slot) ∧
        getCurrentEpoch boundary = getCurrentEpoch x.state ∧ Hysteresis boundary ∧
        Nonempty (Run config checks g ⟨x.fork, boundary⟩) ∧
        Nonempty (Run config checks ⟨x.fork, boundary⟩ x) := by
  intro x run
  induction run with
  | nil =>
    intro _ fulu
    obtain ⟨_, _, _, initialized⟩ := genesis
    obtain ⟨phase0, -⟩ := initializeBeaconStateFromEth1_ok initialized
    exact absurd (Nat.lt_of_le_of_lt fulu phase0) (by decide)
  | @snoc middle last pre step ih =>
    intro early fulu
    cases step with
    | slot ok =>
      by_cases first : last.state.slot % preset.SLOTS_PER_EPOCH = 0
      · exact ⟨last.state, fun _ => rfl, rfl,
          hysteresis_of_run_slot genesis bands caps activation pre ok early first,
          ⟨pre.snoc (.slot ok)⟩, ⟨.nil⟩⟩
      · have next := (advanceSlotAcross_cases ok).1
        have notFirst : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ middle.state.slot.toNat + 1 := by
          rw [Nat.dvd_iff_mod_eq_zero, ← next]
          intro zero
          exact first (UInt64.toNat_inj.mp (by rw [UInt64.toNat_mod, zero, UInt64.toNat_zero]))
        have same : getCurrentEpoch last.state = getCurrentEpoch middle.state := by
          apply UInt64.toNat_inj.mp
          rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, next, Nat.succ_div]
          simp [notFirst]
        obtain ⟨_, _, -, kept⟩ := advanceSlotAcross_of_same_epoch ok same
        have keptFork : last.fork = middle.fork := by rw [kept]
        obtain ⟨boundary, -, epoch, banded, toBoundary, ⟨rest⟩⟩ :=
          ih (keptFork ▸ early) (keptFork ▸ fulu)
        have extended := rest.snoc (.slot ok)
        have epochLast := epoch.trans same.symm
        subst kept
        exact ⟨boundary, fun atStart => absurd atStart first, epochLast, banded, toBoundary,
          ⟨extended⟩⟩
    | block engine signed due ok =>
      have kept := processBlock_slot (applySignedBlock_ok ok).2.1
      obtain ⟨boundary, atSlot, epoch, banded, first, ⟨rest⟩⟩ := ih early fulu
      exact ⟨boundary, fun atStart => (atSlot (kept ▸ atStart)).trans kept.symm,
        epoch.trans (by simp only [getCurrentEpoch, kept]), banded, first,
        ⟨rest.snoc (.block engine signed due ok)⟩⟩

/-- A run from genesis to a state at the first slot of an epoch passes the boundary state.

The boundary state is at the same slot, after the epoch transition and the upgrades of the slot.

Only blocks at that slot lead from the boundary state to the last state.

The bands of hysteresis hold at the boundary state.

Genesis is before Altair and the last state is at Fulu or later, so the run has a slot step.

The epoch transition of that step sets the bands.

An upgrade keeps them, since every effective balance is at most its cap. -/
private theorem run_boundaryState {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset) :
    ∀ {x : ForkedBeaconState preset}, Run config checks g x → x.fork < .glamsterdam →
      .fusaka ≤ x.fork → x.state.slot % preset.SLOTS_PER_EPOCH = 0 →
      ∃ boundary : BeaconState preset x.fork, boundary.slot = x.state.slot ∧
        Hysteresis boundary ∧ Nonempty (Run config checks g ⟨x.fork, boundary⟩) ∧
        Nonempty (Run config checks ⟨x.fork, boundary⟩ x) := by
  intro x run early fulu atStart
  obtain ⟨boundary, atSlot, -, banded, toBoundary, fromBoundary⟩ :=
    run_boundaryEpoch genesis bands caps activation run early fulu
  exact ⟨boundary, atSlot atStart, banded, toBoundary, fromBoundary⟩

/-! ## Runs along the chains of a store -/

/-- The second state is at the same slot or later, and a run reaches it before the next fork. -/
private def RunsTo (config : Config) (checks : SignatureChecks)
    (first second : BeaconState preset fork) : Prop :=
  first.slot ≤ second.slot ∧
    ((∀ next ∈ config.nextFork fork,
      second.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) →
      Nonempty (Run config checks ⟨fork, first⟩ ⟨fork, second⟩))

private theorem RunsTo.refl (state : BeaconState preset fork) : RunsTo config checks state state :=
  ⟨UInt64.le_refl _, fun _ => ⟨.nil⟩⟩

private theorem RunsTo.trans {first second third : BeaconState preset fork}
    (one : RunsTo config checks first second) (two : RunsTo config checks second third) :
    RunsTo config checks first third := by
  refine ⟨UInt64.le_trans one.1 two.1, fun before => ?_⟩
  have middle : (∀ next ∈ config.nextFork fork,
      second.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) := fun next member =>
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp two.1) (before next member)
  obtain ⟨left⟩ := one.2 middle
  obtain ⟨right⟩ := two.2 before
  exact ⟨left.append right⟩

/-- A block transition is a run. -/
private theorem RunsTo.ofTransition {first second : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (transitioned : Consensus.stateTransition config checks engine first signed true = .ok second) :
    RunsTo config checks first second := by
  obtain ⟨lower, atBlock⟩ := stateTransition_slot transitioned
  refine ⟨atBlock ▸ UInt64.le_of_lt lower, fun before => ?_⟩
  obtain ⟨_, slots, due, applied, -⟩ := run_of_stateTransition transitioned (atBlock ▸ before)
  exact ⟨slots.snoc (.block engine signed due applied)⟩

/-- Slots processed up to a slot at or before a block, then the rest of its transition, run. -/
private theorem RunsTo.ofPrefix {first middle second : BeaconState preset fork} {slot : Slot}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    (prefixOk : processSlots config checks first slot = .ok middle)
    (atMost : slot ≤ signed.message.slot)
    (transitioned : Consensus.stateTransition config checks engine first signed true = .ok second) :
    RunsTo config checks middle second := by
  have middleSlot := (processSlots_slot prefixOk).2
  have secondSlot := (stateTransition_slot transitioned).2
  refine ⟨by rw [middleSlot, secondSlot]; exact atMost, fun before => ?_⟩
  rw [secondSlot] at before
  simp only [Consensus.stateTransition, bind_ok_iff] at transitioned
  obtain ⟨advanced, slotsOk, applied⟩ := transitioned
  have advancedSlot := (processSlots_slot slotsOk).2
  have due : upgradeDue config ⟨fork, advanced⟩ = false :=
    upgradeDue_of_before fun next scheduled => advancedSlot ▸ before next scheduled
  -- The slots after the prefix, if any, lead to the state the block applies to.
  obtain ⟨slots⟩ : Nonempty (Run config checks ⟨fork, middle⟩ ⟨fork, advanced⟩) := by
    rcases UInt64.lt_or_eq_of_le atMost with lower | same
    · obtain ⟨middle', middleOk, restOk⟩ :=
        processSlots_split (processSlots_slot prefixOk).1 lower slotsOk
      rw [Except.ok.inj (middleOk.symm.trans prefixOk)] at restOk
      exact run_of_processSlots restOk before
    · rw [← same] at slotsOk
      rw [Except.ok.inj (slotsOk.symm.trans prefixOk)]
      exact ⟨.nil⟩
  exact ⟨slots.snoc (.block engine signed due applied)⟩

variable {store : Store preset fork}

/-- A slot of an epoch within the horizon is before the next fork. -/
private theorem beforeFork_of_epoch {horizon : Epoch}
    (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) {slot : Slot}
    (inside : slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ horizon.toNat) :
    (∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) := fun next member =>
  (Nat.div_lt_iff_lt_mul positive).mp (Nat.lt_of_le_of_lt inside (window next member))

/-- A store whose epoch is within the horizon holds states before the next fork.

Its current slot is at or after each held state, and in an epoch within the horizon. -/
private theorem held_beforeFork {horizon : Epoch}
    (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (slots : 0 < config.SLOT_DURATION_MS)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (forward : Store.ForwardReachable config anchorState anchorBlock store)
    (bounded : ∀ epoch, store.getCurrentStoreEpoch config = .ok epoch → epoch ≤ horizon) :
    (∀ epoch, store.getCurrentStoreEpoch config = .ok epoch →
      ∀ slot : Slot, slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ epoch.toNat →
        (∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)) ∧
    ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state →
        (∀ next ∈ config.nextFork fork,
      state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) := by
  obtain ⟨current, currentOk, -, statesLe⟩ :=
    forward.slots_le_current slots (UInt64.le_of_eq anchorSlot)
  have epochOk : store.getCurrentStoreEpoch config = .ok (computeEpochAtSlot preset current) := by
    simp [Store.getCurrentStoreEpoch, currentOk, bind, Except.bind, pure, Except.pure]
  have within := UInt64.le_iff_toNat_le.mp (bounded _ epochOk)
  have currentNat : (computeEpochAtSlot preset current).toNat =
      current.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  refine ⟨fun epoch ok slot inside => ?_, fun root state stored => ?_⟩
  · have := UInt64.le_iff_toNat_le.mp (bounded epoch ok)
    exact beforeFork_of_epoch window positive (by omega)
  · have low := UInt64.le_iff_toNat_le.mp (statesLe root state stored)
    exact beforeFork_of_epoch window positive
      (Nat.le_trans (Nat.div_le_div_right low) (currentNat ▸ within))

/-- Honest stores whose epochs stay within a horizon before the next fork hold states before it.

It discharges the premise that every held honest state is before the next fork. -/
theorem Execution.heldStatesBeforeUpgrade_of_bounded {anchor : Store preset fork}
    {horizon : Epoch} {limit : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit) :
    HeldStatesBeforeUpgrade (e := e) limit := by
  intro w honest k time next member root state stored
  have forward := e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) k w honest
  exact (held_beforeFork forkWindow positive slots anchorSlot forward.forwardReachable
    (fun epoch ok => bounded w honest k epoch time ok)).2 root state stored next member

/-- A slot step run is a run, when the last slot is before the next fork. -/
private theorem RunsTo.ofProcessSlots {first second : BeaconState preset fork} {slot : Slot}
    (processed : processSlots config checks first slot = .ok second) :
    RunsTo config checks first second := by
  obtain ⟨lower, reached⟩ := processSlots_slot processed
  exact ⟨reached ▸ UInt64.le_of_lt lower, fun before =>
    run_of_processSlots processed (reached ▸ before)⟩

/-- A state reached from a held state by processed slots runs on from it. -/
private theorem RunsTo.ofReach {first second : BeaconState preset fork}
    (reach : second = first ∨ ∃ slot, processSlots config checks first slot = .ok second) :
    RunsTo config checks first second := by
  rcases reach with rfl | ⟨_, processed⟩
  · exact RunsTo.refl _
  · exact RunsTo.ofProcessSlots processed

/-- The anchor state runs to each state that an honest store holds, before the next fork. -/
private theorem run_of_held (forward : Store.ForwardReachableWith config checks anchorState
      anchorBlock store)
    (before : ∀ (root : Root) (state : BeaconState preset fork),
      store.blockStates[root]? = some state → (∀ next ∈ config.nextFork fork,
        state.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat))
    {root : Root} {state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some state) :
    Nonempty (Run config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) :=
  forward.reachable.nonempty_run_of_blockState forward.blockStatesFromParents
    (fun next member root state stored => before root state stored next member) stored

/-- A checkpoint read whose block is at or before the start of the epoch names that block. -/
private theorem eq_of_getCheckpointBlock {root checkpoint : Root} {epoch : Epoch} {start : Slot}
    {block : BeaconBlock preset fork}
    (read : store.getCheckpointBlock root epoch = .ok checkpoint)
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    (found : store.blocks[root]? = some block) (atMost : block.slot ≤ start) :
    root = checkpoint := by
  simp only [Store.getCheckpointBlock, bind_ok_iff, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq] at read
  obtain ⟨start', startOk', node, walk, rooted⟩ := read
  rw [startOk, Except.ok.injEq] at startOk'
  subst startOk'
  rw [Store.getAncestor_of_le (node := ⟨root, .pending⟩) found atMost, Except.ok.injEq] at walk
  rw [← rooted, ← walk]

/-- A held state whose chain reads a checkpoint runs on from the checkpoint's state at its start.

The state may also have more slots processed, up to the start or later.

The checkpoint's state at the start of its epoch is the lookahead of the checkpoint block's state.

The lookahead exists: a block of the chain is at the start or later, or the slots reach it. -/
private theorem lookahead_runsTo (anchorSlot : anchorBlock.slot = anchorState.slot)
    (forward : Store.ForwardReachableWith config checks anchorState anchorBlock store)
    {checkpoint : Checkpoint} {start : Slot} {base : BeaconState preset fork}
    (startOk : computeStartSlotAtEpoch preset checkpoint.epoch = .ok start)
    (baseFound : store.blockStates[checkpoint.root]? = some base)
    {root : Root} {rootState state : BeaconState preset fork}
    (stored : store.blockStates[root]? = some rootState)
    (read : store.getCheckpointBlock root checkpoint.epoch = .ok checkpoint.root)
    (reach : state = rootState ∨ ∃ slot, processSlots config checks rootState slot = .ok state)
    (later : start ≤ state.slot) :
    ∃ middle, lookaheadState config checks base start = .ok middle ∧
      RunsTo config checks middle state := by
  obtain ⟨rootBlock, rootFound⟩ := forward.reachable.known_of_blockState stored
  have fromRoot : RunsTo config checks rootState state := RunsTo.ofReach reach
  by_cases far : start ≤ rootBlock.slot
  · obtain ⟨middle, lookOk, toRoot⟩ :=
      forward.relation_of_checkpointPrefix_with (RunsTo config checks) RunsTo.refl
        RunsTo.trans RunsTo.ofTransition RunsTo.ofPrefix (UInt64.le_of_eq anchorSlot) read
        rootFound startOk far baseFound stored
    exact ⟨middle, lookOk, toRoot.trans fromRoot⟩
  · -- A root before the epoch is the checkpoint block, and its state is processed past the start.
    have before := UInt64.not_le.mp far
    obtain rfl : root = checkpoint.root :=
      eq_of_getCheckpointBlock read startOk rootFound (UInt64.le_of_lt before)
    obtain rfl : base = rootState := Option.some.inj (baseFound.symm.trans stored)
    have baseBelow : base.slot < start :=
      (forward.reachable.blockState_slot_eq anchorSlot rootFound stored) ▸ before
    rcases reach with rfl | ⟨slot, processed⟩
    · exact absurd (UInt64.lt_of_lt_of_le baseBelow later) (UInt64.lt_irrefl _)
    · have reached := (processSlots_slot processed).2
      rcases UInt64.lt_or_eq_of_le (reached ▸ later) with lower | same
      · obtain ⟨middle, firstOk, restOk⟩ := processSlots_split baseBelow lower processed
        exact ⟨middle, by simp [lookaheadState, baseBelow, firstOk, Except.mapError],
          RunsTo.ofProcessSlots restOk⟩
      · subst same
        exact ⟨state, by simp [lookaheadState, baseBelow, processed, Except.mapError],
          RunsTo.refl _⟩

/-- The lookahead of a held state to the start of an epoch follows a boundary state there.

The held state is at the start or before it, and a run from the anchor reaches it.

The boundary state is at the start, within the bands of hysteresis, and genesis reaches it.

At most one block, the held state's own when it is at the start, lies between the two.

The lookahead state holds the queue of partial withdrawals of the held state. -/
private theorem boundary_of_lookahead {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (history : Run config checks g ⟨fork, anchorState⟩)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    {start : Slot} {base middle : BeaconState preset fork}
    (atStart : start % preset.SLOTS_PER_EPOCH = 0)
    (startBefore : (∀ next ∈ config.nextFork fork,
      start.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat))
    (baseRun : Run config checks ⟨fork, anchorState⟩ ⟨fork, base⟩) (baseLe : base.slot ≤ start)
    (lookOk : lookaheadState config checks base start = .ok middle) :
    middle.slot = start ∧ ∃ boundary : BeaconState preset fork,
      boundary.slot = start ∧ Hysteresis boundary ∧
      Nonempty (Run config checks g ⟨fork, boundary⟩) ∧
      ∃ edge : Run config checks ⟨fork, boundary⟩ ⟨fork, middle⟩, edge.blockCount ≤ 1 ∧
        ∀ electra : .pectra ≤ fork,
          middle.pendingPartialWithdrawals electra = base.pendingPartialWithdrawals electra := by
  rcases UInt64.lt_or_eq_of_le baseLe with below | same
  · -- Slots reach the start, and the last of them runs the epoch transition.
    have processed : processSlots config checks base start = .ok middle := by
      simp only [lookaheadState, below, ↓reduceIte] at lookOk
      exact mapError_ok_iff.mp lookOk
    have atSlot := (processSlots_slot processed).2
    obtain ⟨slotRun⟩ := run_of_processSlots processed startBefore
    exact ⟨atSlot, middle, atSlot, hysteresis_of_processSlots bands processed atStart,
      ⟨(history.append baseRun).append slotRun⟩, .nil, Nat.zero_le _,
      processSlots_pendingPartialWithdrawals
        (Nat.le_trans (show Fork.altair ≤ Fork.fusaka by decide) fulu) processed⟩
  · -- The held state is at the start, after its own block; the boundary state is before it.
    obtain rfl : base = middle := by
      simpa [lookaheadState, same, UInt64.lt_irrefl, pure, Except.pure] using lookOk
    obtain ⟨boundary, atSlot, banded, first, ⟨edge⟩⟩ :=
      run_boundaryState genesis bands caps activation (history.append baseRun) early fulu
        (show base.slot % preset.SLOTS_PER_EPOCH = 0 from same ▸ atStart)
    have counted := edge.blocks_le_slots (a := start.toNat) (b := start.toNat)
      (by rw [atSlot, same]) (by rw [same])
    exact ⟨same, boundary, atSlot.trans same, banded, first, edge, by omega, fun _ => rfl⟩

/-- A lookahead state is the state itself, or the state with slots processed. -/
private theorem reach_of_lookahead {base middle : BeaconState preset fork} {start : Slot}
    (lookOk : lookaheadState config checks base start = .ok middle) :
    middle = base ∨ ∃ slot, processSlots config checks base slot = .ok middle := by
  unfold lookaheadState at lookOk
  split at lookOk
  · exact .inr ⟨start, mapError_ok_iff.mp lookOk⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at lookOk
    exact .inl lookOk.symm

/-- The runs of a call's own branch, from one state at the start of its target's epoch.

This is the part of `runs_of_call` that reads the call alone, with the middle state named.

The middle state is the lookahead of the target block's state to the start of the epoch.

The slots of epochs up to the target's are before the next fork. -/
private theorem call_runs
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {limit : ℕ} {anchor : Store preset fork} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g : ForkedBeaconState preset} (genesis : Genesis config .bls g)
    (history : Run config .bls g ⟨fork, anchorState⟩) (early : fork < .glamsterdam)
    (fulu : .fusaka ≤ fork) (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (callTime : (e.world n).time ≤ limit)
    {head : Root} {pulled anc : BeaconState preset fork} {target : Checkpoint}
    (pulledOk : ((e.world n).state u).getPulledUpHeadState config head = .ok pulled)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (held : ((e.world n).state u).blockStates[target.root]? = some anc) :
    getCurrentEpoch pulled = target.epoch ∧
      (∀ slot : Slot, slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ target.epoch.toNat →
        (∀ next ∈ config.nextFork fork,
          slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat)) ∧
      ∃ start : Slot, computeStartSlotAtEpoch preset target.epoch = .ok start ∧ anc.slot ≤ start ∧
      ∃ boundary middle : BeaconState preset fork,
        lookaheadState config .bls anc start = .ok middle ∧ middle.slot = start ∧
        boundary.slot = start ∧ Hysteresis boundary ∧
        Nonempty (Run config .bls g ⟨fork, boundary⟩) ∧
        (∀ electra : .pectra ≤ fork,
          middle.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra) ∧
        ∃ (edge : Run config .bls ⟨fork, boundary⟩ ⟨fork, middle⟩)
          (tail : Run config .bls ⟨fork, middle⟩ ⟨fork, pulled⟩),
          edge.blockCount ≤ 1 ∧
          edge.blockCount + tail.blockCount ≤
            pulled.slot.toNat - target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + 1 := by
  have forward := e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) n u caller
  obtain ⟨epochBefore, heldBefore⟩ := held_beforeFork window positive slots anchorSlot
    forward.forwardReachable (fun epoch ok => bounded u caller n epoch callTime ok)
  obtain ⟨epoch, checkpoint, epochOk, checkpointOk, rfl⟩ :=
    Store.getCurrentTarget_eq_ok_iff.mp targetOk
  dsimp only at held ⊢
  obtain ⟨boundary, aBlock, boundaryOk, aFound, aLe, -⟩ :=
    Store.isAncestor_of_getCheckpointBlock checkpointOk
  have boundaryNat := (computeStartSlotAtEpoch_ok_iff.mp boundaryOk).2
  have atStart : boundary % preset.SLOTS_PER_EPOCH = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_mod, boundaryNat, Nat.mul_mod_left, UInt64.toNat_zero]
  have epochAt {s : BeaconState preset fork} (atSlot : s.slot = boundary) :
      getCurrentEpoch s = epoch := by
    simp only [getCurrentEpoch, atSlot]
    exact computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive)
      boundaryOk
  have ancSlot : anc.slot = aBlock.slot :=
    forward.reachable.blockState_slot_eq anchorSlot aFound held
  have ancLe : anc.slot ≤ boundary := ancSlot ▸ aLe
  -- The epoch of the store's clock bounds every slot the call reads.
  obtain ⟨now, nowOk, -, statesLe⟩ := forward.forwardReachable.slots_le_current
    slots (UInt64.le_of_eq anchorSlot)
  have epochNow : epoch.toNat = now.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    have same : epoch = computeEpochAtSlot preset now := by
      refine Except.ok.inj (epochOk.symm.trans ?_)
      simp only [Store.getCurrentStoreEpoch, nowOk, bind, Except.bind, pure, Except.pure]
    rw [same]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
  simp only [Store.getPulledUpHeadState, bind_ok_iff] at pulledOk
  obtain ⟨headState, headOk, current, currentOk, pulledOk⟩ := pulledOk
  have headStored := Store.blockState_ok_iff.mp headOk
  obtain rfl : current = epoch := Except.ok.inj (currentOk.symm.trans epochOk)
  -- The pulled-up head state is the head state, or the target state processed to the start.
  obtain ⟨pulledReach, pulledLater, pulledEpoch⟩ :
      (pulled = headState ∨ ∃ slot, processSlots config .bls headState slot = .ok pulled) ∧
        boundary ≤ pulled.slot ∧ getCurrentEpoch pulled = current := by
    split at pulledOk
    · simp only [bind_ok_iff] at pulledOk
      obtain ⟨boundary', boundaryOk', processed⟩ := pulledOk
      obtain rfl : boundary = boundary' :=
        Except.ok.inj (boundaryOk.symm.trans (mapError_ok_iff.mp boundaryOk'))
      have processed := mapError_ok_iff.mp processed
      have atSlot := (processSlots_slot processed).2
      exact ⟨.inr ⟨boundary, processed⟩, UInt64.le_of_eq atSlot.symm, epochAt atSlot⟩
    · rename_i notOlder
      simp only [pure, Except.pure, Except.ok.injEq] at pulledOk
      subst pulledOk
      have notOlderNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp notOlder)
      rw [getCurrentEpoch_toNat] at notOlderNat
      refine ⟨.inl rfl, ?_, ?_⟩
      · rw [UInt64.le_iff_toNat_le, boundaryNat]
        exact (Nat.le_div_iff_mul_le positive).mp notOlderNat
      · have upper := UInt64.le_iff_toNat_le.mp (statesLe head _ headStored)
        apply UInt64.toNat_inj.mp
        rw [getCurrentEpoch_toNat]
        exact Nat.le_antisymm (epochNow ▸ Nat.div_le_div_right upper) notOlderNat
  obtain ⟨middle, lookOk, toPulled⟩ := lookahead_runsTo anchorSlot forward
    (checkpoint := ⟨current, checkpoint⟩) boundaryOk held headStored checkpointOk pulledReach
    pulledLater
  have epochBoundaryOk : ∀ slot : Slot, slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      current.toNat → (∀ next ∈ config.nextFork fork,
      slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :=
    epochBefore current epochOk
  obtain ⟨tail⟩ := toPulled.2
    (epochBoundaryOk pulled.slot (by rw [← getCurrentEpoch_toNat, pulledEpoch]))
  obtain ⟨ancRun⟩ := run_of_held forward heldBefore held
  have boundaryBefore :=
    epochBoundaryOk boundary (by rw [boundaryNat, Nat.mul_div_cancel _ positive])
  obtain ⟨middleBoundary, start, startSlot, banded, first, edge, single, queue⟩ :=
    boundary_of_lookahead genesis history early fulu bands caps activation atStart
      boundaryBefore ancRun ancLe lookOk
  have counted := (edge.append tail).blocks_le_slots (a := boundary.toNat)
    (b := pulled.slot.toNat) (by rw [startSlot]) (Nat.le_refl _)
  rw [Run.blockCount_append, boundaryNat] at counted
  exact ⟨pulledEpoch, epochBoundaryOk, boundary, boundaryOk, ancLe, start, middle, lookOk,
    middleBoundary, startSlot, banded, first, queue, edge, tail, single, counted⟩

/-- The runs of a call, from one state at the start of its target's epoch.

The call is the pulled-up head state and the current target of an honest store.

The receiver state is on the chain of a block of another honest store.

The checkpoint block of that chain for the target's epoch is the target.

The boundary state is at the start of the target's epoch, and genesis reaches it.

The bands of hysteresis hold at the boundary state.

A middle state at the same slot holds the queue of partial withdrawals of the target block.

The target block itself, when it is at the start of the epoch, is the only block on the way to it.

From the middle state, runs reach the pulled-up head state and the receiver state.

The blocks from the boundary state to the pulled-up head state number at most one per slot.

The spec pulls the head state up with BLS checks, so the stores check signatures with BLS. -/
private theorem runs_of_call
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {limit : ℕ} {anchor : Store preset fork} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g : ForkedBeaconState preset} (genesis : Genesis config .bls g)
    (history : Run config .bls g ⟨fork, anchorState⟩) (early : fork < .glamsterdam)
    (fulu : .fusaka ≤ fork) (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (callTime : (e.world n).time ≤ limit)
    {head : Root} {pulled anc : BeaconState preset fork} {target : Checkpoint}
    (pulledOk : ((e.world n).state u).getPulledUpHeadState config head = .ok pulled)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (held : ((e.world n).state u).blockStates[target.root]? = some anc)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (receiveTime : (e.world k).time ≤ limit)
    {root : Root} {rootState state : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some rootState)
    (read : ((e.world k).state w).getCheckpointBlock root target.epoch = .ok target.root)
    (reach : state = rootState ∨ ∃ slot, processSlots config .bls rootState slot = .ok state)
    (later : target.epoch ≤ getCurrentEpoch state) (inside : getCurrentEpoch state ≤ horizon) :
    getCurrentEpoch pulled = target.epoch ∧
      ∃ boundary middle : BeaconState preset fork,
        getCurrentEpoch boundary = target.epoch ∧ getCurrentEpoch middle = target.epoch ∧
        Hysteresis boundary ∧ Nonempty (Run config .bls g ⟨fork, boundary⟩) ∧
        (∀ electra : .pectra ≤ fork,
          middle.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra) ∧
        ∃ (edge : Run config .bls ⟨fork, boundary⟩ ⟨fork, middle⟩)
          (tail : Run config .bls ⟨fork, middle⟩ ⟨fork, pulled⟩),
          edge.blockCount ≤ 1 ∧
          edge.blockCount + tail.blockCount ≤
            pulled.slot.toNat - target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + 1 ∧
          Nonempty (Run config .bls ⟨fork, middle⟩ ⟨fork, state⟩) := by
  obtain ⟨pulledEpoch, -, start', startOk, -, boundary, middle, lookOk, middleSlot, boundarySlot,
    banded, first, queue, edge, tail, single, counted⟩ :=
    call_runs anchored start anchorSlot slots positive genesis history early fulu window bounded
      bands caps activation caller callTime pulledOk targetOk held
  have startNat := (computeStartSlotAtEpoch_ok_iff.mp startOk).2
  have epochAt {s : BeaconState preset fork} (atSlot : s.slot = start') :
      getCurrentEpoch s = target.epoch := by
    simp only [getCurrentEpoch, atSlot]
    exact computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive) startOk
  -- The receiver holds the same target state, and its state runs on from the middle state.
  have forward := e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
    (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) k w receiver
  obtain ⟨-, aBlockW, -, aFoundW, -, -⟩ := Store.isAncestor_of_getCheckpointBlock read
  obtain ⟨ancW, heldW, -⟩ := forward.reachable.blockStatesFromParents aFoundW
  obtain rfl : anc = ancW := e.blockStates_eq anchored (start u caller)
    (start w receiver) (agree u caller w receiver n k callTime receiveTime) held heldW
  have stateLater : start' ≤ state.slot := by
    have := UInt64.le_iff_toNat_le.mp later
    rw [getCurrentEpoch_toNat] at this
    rw [UInt64.le_iff_toNat_le, startNat]
    exact (Nat.le_div_iff_mul_le positive).mp this
  obtain ⟨middle', lookOk', toState⟩ :=
    lookahead_runsTo anchorSlot forward startOk heldW stored read reach stateLater
  obtain rfl : middle = middle' := Except.ok.inj (lookOk.symm.trans lookOk')
  obtain ⟨toStateRun⟩ := toState.2 (beforeFork_of_epoch window positive
    (by rw [← getCurrentEpoch_toNat]; exact UInt64.le_iff_toNat_le.mp inside))
  exact ⟨pulledEpoch, boundary, middle, epochAt boundarySlot, epochAt middleSlot, banded, first,
    queue, edge, tail, single, counted, ⟨toStateRun⟩⟩

/-! ## Runs of the pin's window -/

/-- The runs of the pin's window, from a split state at the start of the finalized epoch.

The call is the pulled-up head state and the current target of an honest store.

The counting state is on the chain of a block of another honest store.

Once finality has passed the anchor, that chain reads the finalized checkpoint.

It is the one that the target block's state holds.

The split state is the lookahead of the finalized block's state to the start of its epoch.

Before finality has passed the anchor, the split state is the anchor state.

A boundary state of the split's epoch, with the bands of hysteresis, runs to the split state.

From the split state, runs reach the call's middle state and the counting state.

The call's own branch is as `runs_of_call` gives it.

It has a boundary state with the bands at the start of the target's epoch.

At most one block lies between that state and the middle state.

A tail runs from the middle state to the pulled-up state. -/
private theorem runs_of_finalized
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {limit : ℕ} {anchor : Store preset fork} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g : ForkedBeaconState preset} (genesis : Genesis config .bls g)
    (history : Run config .bls g ⟨fork, anchorState⟩) (early : fork < .glamsterdam)
    (fulu : .fusaka ≤ fork) (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (callTime : (e.world n).time ≤ limit)
    {head : Root} {pulled anc fin : BeaconState preset fork} {target : Checkpoint}
    (pulledOk : ((e.world n).state u).getPulledUpHeadState config head = .ok pulled)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (held : ((e.world n).state u).blockStates[target.root]? = some anc)
    (finHeld : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin)
    (finAnchor : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState)
    (ancRead : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).getCheckpointBlock target.root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (receiveTime : (e.world k).time ≤ limit)
    {root : Root} {rootState counted : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some rootState)
    (reach : counted = rootState ∨ ∃ slot, processSlots config .bls rootState slot = .ok counted)
    (finRead : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world k).state w).getCheckpointBlock root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root)
    (later : target.epoch ≤ getCurrentEpoch counted) (inside : getCurrentEpoch counted ≤ horizon) :
    getCurrentEpoch pulled = target.epoch ∧
      ∃ common split : BeaconState preset fork,
        Hysteresis common ∧ Nonempty (Run config .bls g ⟨fork, common⟩) ∧
        Nonempty (Run config .bls ⟨fork, common⟩ ⟨fork, split⟩) ∧
        Nonempty (Run config .bls ⟨fork, fin⟩ ⟨fork, split⟩) ∧
        getCurrentEpoch split = getCurrentEpoch common ∧
        (∀ electra : .pectra ≤ fork,
          split.pendingPartialWithdrawals electra = fin.pendingPartialWithdrawals electra) ∧
        anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split ∧
      ∃ boundaryE middleE : BeaconState preset fork,
        getCurrentEpoch boundaryE = target.epoch ∧ getCurrentEpoch middleE = target.epoch ∧
        Hysteresis boundaryE ∧ Nonempty (Run config .bls g ⟨fork, boundaryE⟩) ∧
        (∀ electra : .pectra ≤ fork,
          middleE.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra) ∧
        ∃ (edgeE : Run config .bls ⟨fork, boundaryE⟩ ⟨fork, middleE⟩)
          (_ : Run config .bls ⟨fork, split⟩ ⟨fork, middleE⟩)
          (tailM : Run config .bls ⟨fork, middleE⟩ ⟨fork, pulled⟩)
          (_ : Run config .bls ⟨fork, split⟩ ⟨fork, counted⟩),
          edgeE.blockCount ≤ 1 ∧
          edgeE.blockCount + tailM.blockCount ≤
            pulled.slot.toNat - target.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + 1 := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
      (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) i v honest
  obtain ⟨-, heldBefore⟩ := held_beforeFork window positive slots anchorSlot
    (forward u caller n).forwardReachable (fun epoch ok => bounded u caller n epoch callTime ok)
  obtain ⟨-, heldBeforeW⟩ := held_beforeFork window positive slots anchorSlot
    (forward w receiver k).forwardReachable
    (fun epoch ok => bounded w receiver k epoch receiveTime ok)
  obtain ⟨pulledEpoch, epochBefore, startE, startEOk, ancLe, boundaryE, middleE, lookE, middleSlot,
    boundarySlot, bandedE, firstE, queueE, edgeE, tailM, single, countedE⟩ :=
    call_runs anchored start anchorSlot slots positive genesis history early fulu window bounded
      bands caps activation caller callTime pulledOk targetOk held
  have startENat := (computeStartSlotAtEpoch_ok_iff.mp startEOk).2
  have epochAt {s : BeaconState preset fork} {epoch : Epoch} {slot : Slot}
      (startOk : computeStartSlotAtEpoch preset epoch = .ok slot) (atSlot : s.slot = slot) :
      getCurrentEpoch s = epoch := by
    simp only [getCurrentEpoch, atSlot]
    exact computeEpochAtSlot_computeStartSlotAtEpoch (UInt64.lt_iff_toNat_lt.mpr positive) startOk
  have middleBefore : (∀ next ∈ config.nextFork fork,
      middleE.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :=
    epochBefore _ (by rw [middleSlot, startENat, Nat.mul_div_cancel _ positive])
  have countedBefore : (∀ next ∈ config.nextFork fork,
      counted.slot.toNat < next.2.toNat * preset.SLOTS_PER_EPOCH.toNat) :=
    beforeFork_of_epoch window positive
      (by rw [← getCurrentEpoch_toNat]; exact UInt64.le_iff_toNat_le.mp inside)
  have countedLater := UInt64.le_iff_toNat_le.mp later
  rw [getCurrentEpoch_toNat] at countedLater
  have ancReach := reach_of_lookahead lookE
  refine ⟨pulledEpoch, ?_⟩
  by_cases guard : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch
  · -- After the anchor: the split is the finalized block's state at the start of its epoch.
    have finStored := finHeld guard
    obtain ⟨startF, fBlock, startFOk, fFound, fLe, -⟩ :=
      Store.isAncestor_of_getCheckpointBlock (ancRead guard)
    have startFNat := (computeStartSlotAtEpoch_ok_iff.mp startFOk).2
    have finSlot : fin.slot = fBlock.slot :=
      (forward u caller n).reachable.blockState_slot_eq anchorSlot fFound finStored
    -- The finalized epoch is at most the target's: the target block's state settled it.
    have ancHolds := ((forward u caller n).reachable.ordered sound).2 held
    have settled := UInt64.le_iff_toNat_le.mp (UInt64.le_trans
      (Store.finalized_le_currentJustified ancHolds.ordered)
      (UInt64.le_trans ancHolds.settled (getPreviousEpoch_le _)))
    have ancEpoch : (getCurrentEpoch anc).toNat ≤ target.epoch.toNat := by
      rw [getCurrentEpoch_toNat]
      have := UInt64.le_iff_toNat_le.mp ancLe
      rw [startENat] at this
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact this)
    have finalizedLe : startF.toNat ≤ startE.toNat := by
      rw [startFNat, startENat]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨split, lookF, toMiddleE⟩ := lookahead_runsTo anchorSlot (forward u caller n)
      startFOk finStored held (ancRead guard) ancReach
      (by rw [middleSlot, UInt64.le_iff_toNat_le]; exact finalizedLe)
    -- The receiver holds the same finalized block's state, and so the same split state.
    obtain ⟨-, fBlockW, -, fFoundW, -, -⟩ := Store.isAncestor_of_getCheckpointBlock
      (finRead guard)
    obtain ⟨finW, finStoredW, -⟩ := (forward w receiver k).reachable.blockStatesFromParents fFoundW
    obtain rfl : fin = finW := e.blockStates_eq anchored (start u caller)
      (start w receiver) (agree u caller w receiver n k callTime receiveTime) finStored finStoredW
    obtain ⟨split', lookF', toCounted⟩ := lookahead_runsTo anchorSlot (forward w receiver k)
      startFOk finStoredW stored (finRead guard) reach
      (by
        rw [UInt64.le_iff_toNat_le, startFNat]
        exact (Nat.le_div_iff_mul_le positive).mp (by omega))
    obtain rfl : split = split' := Except.ok.inj (lookF.symm.trans lookF')
    -- The boundary state of the finalized epoch, before the split state.
    have atStartF : startF % preset.SLOTS_PER_EPOCH = 0 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, startFNat, Nat.mul_mod_left, UInt64.toNat_zero]
    have startFBefore :=
      epochBefore startF (by rw [startFNat, Nat.mul_div_cancel _ positive]; omega)
    obtain ⟨finRun⟩ := run_of_held (forward u caller n) heldBefore finStored
    obtain ⟨splitSlot, common, commonSlot, banded, toCommon, edge, -, queue⟩ :=
      boundary_of_lookahead genesis history early fulu bands caps activation atStartF
        startFBefore finRun (finSlot ▸ fLe) lookF
    obtain ⟨fromFin⟩ := (RunsTo.ofReach (checks := .bls) (reach_of_lookahead lookF)).2
      (splitSlot ▸ startFBefore)
    obtain ⟨toMiddle⟩ := toMiddleE.2 middleBefore
    obtain ⟨tailS⟩ := toCounted.2 countedBefore
    refine ⟨common, split, banded, toCommon, ⟨edge⟩, ⟨fromFin⟩,
      (epochAt startFOk splitSlot).trans (epochAt startFOk commonSlot).symm, queue,
      UInt64.le_of_eq (epochAt startFOk splitSlot).symm, boundaryE, middleE,
      epochAt startEOk boundarySlot, epochAt startEOk middleSlot, bandedE, firstE, queueE, edgeE,
      toMiddle, tailM, tailS, single, countedE⟩
  · -- Before finality passes the anchor: the split is the anchor state itself.
    obtain rfl := finAnchor (UInt64.not_lt.mp guard)
    obtain ⟨common, -, commonEpoch, banded, toCommon, edge⟩ :=
      run_boundaryEpoch genesis bands caps activation history early fulu
    obtain ⟨ancRun⟩ := run_of_held (forward u caller n) heldBefore held
    obtain ⟨ancToMiddle⟩ := (RunsTo.ofReach (checks := .bls) ancReach).2 middleBefore
    obtain ⟨rootRun⟩ := run_of_held (forward w receiver k) heldBeforeW stored
    obtain ⟨rootToCounted⟩ := (RunsTo.ofReach (checks := .bls) reach).2 countedBefore
    exact ⟨common, fin, banded, toCommon, edge, ⟨.nil⟩, commonEpoch.symm, fun _ => rfl,
      UInt64.not_lt.mp guard, boundaryE, middleE, epochAt startEOk boundarySlot,
      epochAt startEOk middleSlot, bandedE, firstE, queueE, edgeE, ancRun.append ancToMiddle,
      tailM, rootRun.append rootToCounted, single, countedE⟩

/-- The runs and epochs of the pin's `Setting`, for one call and one counting state.

The finalized block's state `fin` is reached from genesis, and the split state from `fin`.

From the split state, runs reach the pulled-up head state and the counting state.

The split state is at or after the finalized epoch and at or before the call's epoch. -/
theorem setting_runs_of_call
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {limit : ℕ} {anchor : Store preset fork} {horizon : Epoch}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    {g : ForkedBeaconState preset} (genesis : Genesis config .bls g)
    (history : Run config .bls g ⟨fork, anchorState⟩) (early : fork < .glamsterdam)
    (fulu : .fusaka ≤ fork) (window : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (agree : ∀ a ∈ J, ∀ b ∈ J, ∀ i j, (e.world i).time ≤ limit → (e.world j).time ≤ limit →
      ∀ (r : Root) (left right : BeaconBlock preset fork),
      ((e.world i).state a).blocks[r]? = some left →
      ((e.world j).state b).blocks[r]? = some right → left = right)
    (bands : preset.IncrementWithinUpwardBand)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    (sound : Invariant anchorState)
    {u : ValidatorIndex} (caller : u ∈ J) {n : ℕ} (callTime : (e.world n).time ≤ limit)
    {head : Root} {pulled anc fin : BeaconState preset fork} {target : Checkpoint}
    (pulledOk : ((e.world n).state u).getPulledUpHeadState config head = .ok pulled)
    (targetOk : ((e.world n).state u).getCurrentTarget config head = .ok target)
    (held : ((e.world n).state u).blockStates[target.root]? = some anc)
    (finHeld : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).blockStates[anc.finalizedCheckpoint.root]? = some fin)
    (finAnchor : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch anchorState → fin = anchorState)
    (ancRead : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world n).state u).getCheckpointBlock target.root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root)
    {w : ValidatorIndex} (receiver : w ∈ J) {k : ℕ} (receiveTime : (e.world k).time ≤ limit)
    {root : Root} {rootState counted : BeaconState preset fork}
    (stored : ((e.world k).state w).blockStates[root]? = some rootState)
    (reach : counted = rootState ∨ ∃ slot, processSlots config .bls rootState slot = .ok counted)
    (finRead : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch →
      ((e.world k).state w).getCheckpointBlock root anc.finalizedCheckpoint.epoch =
        .ok anc.finalizedCheckpoint.root)
    (later : target.epoch ≤ getCurrentEpoch counted) (inside : getCurrentEpoch counted ≤ horizon) :
    getCurrentEpoch pulled = target.epoch ∧
      ∃ split : BeaconState preset fork,
        Nonempty (Run config .bls g ⟨fork, fin⟩) ∧
        Nonempty (Run config .bls ⟨fork, fin⟩ ⟨fork, split⟩) ∧
        Nonempty (Run config .bls ⟨fork, split⟩ ⟨fork, pulled⟩) ∧
        Nonempty (Run config .bls ⟨fork, split⟩ ⟨fork, counted⟩) ∧
        anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split ∧
        getCurrentEpoch split ≤ getCurrentEpoch pulled ∧
        getCurrentEpoch pulled ≤ getCurrentEpoch counted := by
  have forward (v : ValidatorIndex) (honest : v ∈ J) (i : ℕ) :=
    e.forwardReachableWith (anchorState := anchorState) (anchorBlock := anchorBlock)
      (fun a member => (start a member) ▸ Store.ForwardReachableWith.anchor anchored) i v honest
  obtain ⟨-, heldBefore⟩ := held_beforeFork window positive slots anchorSlot
    (forward u caller n).forwardReachable (fun epoch ok => bounded u caller n epoch callTime ok)
  obtain ⟨pulledEpoch, common, split, -, -, -, ⟨fromFin⟩, -, -, ancLe, boundaryE, middleE, -, -,
    -, -, -, edgeE, toMiddle, tailM, tailS, -, -⟩ :=
    runs_of_finalized anchored start anchorSlot slots positive genesis history early fulu window
      bounded agree bands caps activation sound caller callTime pulledOk targetOk held
      finHeld finAnchor ancRead receiver receiveTime stored reach finRead later inside
  have toPulled := toMiddle.append tailM
  refine ⟨pulledEpoch, split, ?_, ⟨fromFin⟩, ⟨toPulled⟩, ⟨tailS⟩, ancLe,
    currentEpoch_le_of_chainSteps toPulled.chainSteps, pulledEpoch ▸ later⟩
  by_cases guard : getCurrentEpoch anchorState < anc.finalizedCheckpoint.epoch
  · obtain ⟨finRun⟩ := run_of_held (forward u caller n) heldBefore (finHeld guard)
    exact ⟨history.append finRun⟩
  · obtain rfl := finAnchor (UInt64.not_lt.mp guard)
    exact ⟨history⟩

/-- The quorum of each call of an honest store drifts by at most its reserve, at every receiver.

For each call, the bound holds or two honest stores collide on a root by the time bound.

The bound needs BLS checks, because the spec pulls the head state up with them.

An assumption on the run: its fork is Fulu or later, and before Gloas.

The bounds read the epoch transition of Fulu; earlier and later forks are not covered.

The anchor store comes from a successful read of the fork-choice store of the anchor.

Every honest participant starts at the anchor store.

The anchor block is at the anchor state's slot, and slots last a positive time.

The anchor state is reached by a run with BLS checks from a genesis built from deposits.

An epoch has at least one slot, and the preset keeps the bands of hysteresis.

The withdrawal delay is at least one epoch.

The caps are ordered, and the activation balance is at most the largest before Electra.

The seed lookahead covers at least one epoch, so activity in the next epoch is fixed in the current.

An assumption on the run: the stores stay before the next fork through the horizon.

It keeps every run inside one fork, and says nothing about a run that crosses a fork.

An assumption on the run: every honest store's current epoch stays within the horizon.

It ties the horizon to the time bound, and says nothing about stores past it. -/
theorem Execution.quorumDriftWithin
    {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
      genesisTimeMs) J}
    {anchor : Store preset fork} {g : ForkedBeaconState preset} {horizon : Epoch} {limit : ℕ}
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (start : ∀ w ∈ J, e.start w = anchor) (anchorSlot : anchorBlock.slot = anchorState.slot)
    (slots : 0 < config.SLOT_DURATION_MS) (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (genesis : Genesis config .bls g) (history : Run config .bls g ⟨fork, anchorState⟩)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (bands : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset) :
    QuorumDriftWithin (e := e) horizon limit := by
  intro u caller n head pulled anc target callTime pulledOk targetOk held w receiver k root
    rootState state receiveTime stored read reach later near inside voters total pulledTotal
    voting totalOk pulledTotalOk
  rcases e.blocksAgree_or_collision limit with agree | collision
  swap
  · exact .inr collision
  left
  obtain ⟨pulledEpoch, boundary, middle, boundaryEpoch, middleEpoch, banded, ⟨toBoundary⟩,
    queue, edge, tail, single, counted, ⟨toState⟩⟩ :=
    runs_of_call anchored start anchorSlot slots positive genesis history early fulu
      forkWindow bounded agree bands caps activation caller callTime pulledOk targetOk held
      receiver receiveTime stored read reach later inside
  rw [← pulledEpoch] at counted later near
  exact quorumDrift_le_quorumReserve genesis toBoundary edge tail toState early fulu bands
    withdrawDelay caps maxLookahead banded single counted queue
    (middleEpoch.trans boundaryEpoch.symm) (pulledEpoch.trans boundaryEpoch.symm) later near
    voting totalOk pulledTotalOk

end EthLib.Consensus.Models.Network
